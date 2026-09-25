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
lean_object* l_Lean_Json_getObjValAs_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentSyncKind_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentSyncKind_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentContentChangeEvent_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentContentChangeEvent_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentSyncKind_ctorIdx(uint8_t v_x_1_){
_start:
{
switch(v_x_1_)
{
case 0:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
case 1:
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
default: 
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentSyncKind_ctorIdx___boxed(lean_object* v_x_5_){
_start:
{
uint8_t v_x_boxed_6_; lean_object* v_res_7_; 
v_x_boxed_6_ = lean_unbox(v_x_5_);
v_res_7_ = l_Lean_Lsp_TextDocumentSyncKind_ctorIdx(v_x_boxed_6_);
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
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentSyncKind_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, uint8_t v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_inc(v_k_15_);
return v_k_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentSyncKind_ctorElim___boxed(lean_object* v_motive_16_, lean_object* v_ctorIdx_17_, lean_object* v_t_18_, lean_object* v_h_19_, lean_object* v_k_20_){
_start:
{
uint8_t v_t_boxed_21_; lean_object* v_res_22_; 
v_t_boxed_21_ = lean_unbox(v_t_18_);
v_res_22_ = l_Lean_Lsp_TextDocumentSyncKind_ctorElim(v_motive_16_, v_ctorIdx_17_, v_t_boxed_21_, v_h_19_, v_k_20_);
lean_dec(v_k_20_);
lean_dec(v_ctorIdx_17_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentSyncKind_none_elim___redArg(lean_object* v_none_23_){
_start:
{
lean_inc(v_none_23_);
return v_none_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentSyncKind_none_elim___redArg___boxed(lean_object* v_none_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_Lean_Lsp_TextDocumentSyncKind_none_elim___redArg(v_none_24_);
lean_dec(v_none_24_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentSyncKind_none_elim(lean_object* v_motive_26_, uint8_t v_t_27_, lean_object* v_h_28_, lean_object* v_none_29_){
_start:
{
lean_inc(v_none_29_);
return v_none_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentSyncKind_none_elim___boxed(lean_object* v_motive_30_, lean_object* v_t_31_, lean_object* v_h_32_, lean_object* v_none_33_){
_start:
{
uint8_t v_t_boxed_34_; lean_object* v_res_35_; 
v_t_boxed_34_ = lean_unbox(v_t_31_);
v_res_35_ = l_Lean_Lsp_TextDocumentSyncKind_none_elim(v_motive_30_, v_t_boxed_34_, v_h_32_, v_none_33_);
lean_dec(v_none_33_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentSyncKind_full_elim___redArg(lean_object* v_full_36_){
_start:
{
lean_inc(v_full_36_);
return v_full_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentSyncKind_full_elim___redArg___boxed(lean_object* v_full_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Lean_Lsp_TextDocumentSyncKind_full_elim___redArg(v_full_37_);
lean_dec(v_full_37_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentSyncKind_full_elim(lean_object* v_motive_39_, uint8_t v_t_40_, lean_object* v_h_41_, lean_object* v_full_42_){
_start:
{
lean_inc(v_full_42_);
return v_full_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentSyncKind_full_elim___boxed(lean_object* v_motive_43_, lean_object* v_t_44_, lean_object* v_h_45_, lean_object* v_full_46_){
_start:
{
uint8_t v_t_boxed_47_; lean_object* v_res_48_; 
v_t_boxed_47_ = lean_unbox(v_t_44_);
v_res_48_ = l_Lean_Lsp_TextDocumentSyncKind_full_elim(v_motive_43_, v_t_boxed_47_, v_h_45_, v_full_46_);
lean_dec(v_full_46_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentSyncKind_incremental_elim___redArg(lean_object* v_incremental_49_){
_start:
{
lean_inc(v_incremental_49_);
return v_incremental_49_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentSyncKind_incremental_elim___redArg___boxed(lean_object* v_incremental_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l_Lean_Lsp_TextDocumentSyncKind_incremental_elim___redArg(v_incremental_50_);
lean_dec(v_incremental_50_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentSyncKind_incremental_elim(lean_object* v_motive_52_, uint8_t v_t_53_, lean_object* v_h_54_, lean_object* v_incremental_55_){
_start:
{
lean_inc(v_incremental_55_);
return v_incremental_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentSyncKind_incremental_elim___boxed(lean_object* v_motive_56_, lean_object* v_t_57_, lean_object* v_h_58_, lean_object* v_incremental_59_){
_start:
{
uint8_t v_t_boxed_60_; lean_object* v_res_61_; 
v_t_boxed_60_ = lean_unbox(v_t_57_);
v_res_61_ = l_Lean_Lsp_TextDocumentSyncKind_incremental_elim(v_motive_56_, v_t_boxed_60_, v_h_58_, v_incremental_59_);
lean_dec(v_incremental_59_);
return v_res_61_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0(lean_object* v_j_74_){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = l_Lean_Json_getNat_x3f(v_j_74_);
if (lean_obj_tag(v___x_77_) == 1)
{
lean_object* v_a_78_; lean_object* v___x_79_; uint8_t v___x_80_; 
v_a_78_ = lean_ctor_get(v___x_77_, 0);
lean_inc(v_a_78_);
lean_dec_ref_known(v___x_77_, 1);
v___x_79_ = lean_unsigned_to_nat(0u);
v___x_80_ = lean_nat_dec_eq(v_a_78_, v___x_79_);
if (v___x_80_ == 0)
{
lean_object* v___x_81_; uint8_t v___x_82_; 
v___x_81_ = lean_unsigned_to_nat(1u);
v___x_82_ = lean_nat_dec_eq(v_a_78_, v___x_81_);
if (v___x_82_ == 0)
{
lean_object* v___x_83_; uint8_t v___x_84_; 
v___x_83_ = lean_unsigned_to_nat(2u);
v___x_84_ = lean_nat_dec_eq(v_a_78_, v___x_83_);
lean_dec(v_a_78_);
if (v___x_84_ == 0)
{
goto v___jp_75_;
}
else
{
lean_object* v___x_85_; 
v___x_85_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0___closed__2));
return v___x_85_;
}
}
else
{
lean_object* v___x_86_; 
lean_dec(v_a_78_);
v___x_86_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0___closed__3));
return v___x_86_;
}
}
else
{
lean_object* v___x_87_; 
lean_dec(v_a_78_);
v___x_87_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0___closed__4));
return v___x_87_;
}
}
else
{
lean_dec_ref(v___x_77_);
goto v___jp_75_;
}
v___jp_75_:
{
lean_object* v___x_76_; 
v___x_76_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0___closed__1));
return v___x_76_;
}
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__0(void){
_start:
{
lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_90_ = lean_unsigned_to_nat(0u);
v___x_91_ = l_Lean_JsonNumber_fromNat(v___x_90_);
return v___x_91_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__1(void){
_start:
{
lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_92_ = lean_obj_once(&l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__0, &l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__0_once, _init_l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__0);
v___x_93_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_93_, 0, v___x_92_);
return v___x_93_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__2(void){
_start:
{
lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_94_ = lean_unsigned_to_nat(1u);
v___x_95_ = l_Lean_JsonNumber_fromNat(v___x_94_);
return v___x_95_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__3(void){
_start:
{
lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_96_ = lean_obj_once(&l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__2, &l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__2_once, _init_l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__2);
v___x_97_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_97_, 0, v___x_96_);
return v___x_97_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__4(void){
_start:
{
lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_98_ = lean_unsigned_to_nat(2u);
v___x_99_ = l_Lean_JsonNumber_fromNat(v___x_98_);
return v___x_99_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__5(void){
_start:
{
lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_100_ = lean_obj_once(&l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__4, &l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__4_once, _init_l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__4);
v___x_101_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_101_, 0, v___x_100_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0(uint8_t v_x_102_){
_start:
{
switch(v_x_102_)
{
case 0:
{
lean_object* v___x_103_; 
v___x_103_ = lean_obj_once(&l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__1, &l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__1_once, _init_l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__1);
return v___x_103_;
}
case 1:
{
lean_object* v___x_104_; 
v___x_104_ = lean_obj_once(&l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__3, &l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__3_once, _init_l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__3);
return v___x_104_;
}
default: 
{
lean_object* v___x_105_; 
v___x_105_ = lean_obj_once(&l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__5, &l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__5_once, _init_l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__5);
return v___x_105_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___boxed(lean_object* v_x_106_){
_start:
{
uint8_t v_x_81__boxed_107_; lean_object* v_res_108_; 
v_x_81__boxed_107_ = lean_unbox(v_x_106_);
v_res_108_ = l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0(v_x_81__boxed_107_);
return v_res_108_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson_spec__0(lean_object* v_a_111_, lean_object* v_a_112_){
_start:
{
if (lean_obj_tag(v_a_111_) == 0)
{
lean_object* v___x_113_; 
v___x_113_ = lean_array_to_list(v_a_112_);
return v___x_113_;
}
else
{
lean_object* v_head_114_; lean_object* v_tail_115_; lean_object* v___x_116_; 
v_head_114_ = lean_ctor_get(v_a_111_, 0);
lean_inc(v_head_114_);
v_tail_115_ = lean_ctor_get(v_a_111_, 1);
lean_inc(v_tail_115_);
lean_dec_ref_known(v_a_111_, 2);
v___x_116_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_112_, v_head_114_);
v_a_111_ = v_tail_115_;
v_a_112_ = v___x_116_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson(lean_object* v_x_121_){
_start:
{
lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_122_ = ((lean_object*)(l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__0));
v___x_123_ = l_Lean_Lsp_instToJsonTextDocumentItem_toJson(v_x_121_);
v___x_124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_124_, 0, v___x_122_);
lean_ctor_set(v___x_124_, 1, v___x_123_);
v___x_125_ = lean_box(0);
v___x_126_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_126_, 0, v___x_124_);
lean_ctor_set(v___x_126_, 1, v___x_125_);
v___x_127_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_127_, 0, v___x_126_);
lean_ctor_set(v___x_127_, 1, v___x_125_);
v___x_128_ = ((lean_object*)(l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__1));
v___x_129_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson_spec__0(v___x_127_, v___x_128_);
v___x_130_ = l_Lean_Json_mkObj(v___x_129_);
lean_dec(v___x_129_);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson_spec__0(lean_object* v_j_133_, lean_object* v_k_134_){
_start:
{
lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_135_ = l_Lean_Json_getObjValD(v_j_133_, v_k_134_);
v___x_136_ = l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson(v___x_135_);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson_spec__0___boxed(lean_object* v_j_137_, lean_object* v_k_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson_spec__0(v_j_137_, v_k_138_);
lean_dec_ref(v_k_138_);
return v_res_139_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__4(void){
_start:
{
uint8_t v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_147_ = 1;
v___x_148_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__3));
v___x_149_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_148_, v___x_147_);
return v___x_149_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__6(void){
_start:
{
lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; 
v___x_151_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__5));
v___x_152_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__4);
v___x_153_ = lean_string_append(v___x_152_, v___x_151_);
return v___x_153_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__8(void){
_start:
{
uint8_t v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_156_ = 1;
v___x_157_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__7));
v___x_158_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_157_, v___x_156_);
return v___x_158_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__9(void){
_start:
{
lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_159_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__8);
v___x_160_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__6, &l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__6);
v___x_161_ = lean_string_append(v___x_160_, v___x_159_);
return v___x_161_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__11(void){
_start:
{
lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_163_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__10));
v___x_164_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__9, &l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__9);
v___x_165_ = lean_string_append(v___x_164_, v___x_163_);
return v___x_165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson(lean_object* v_json_166_){
_start:
{
lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_167_ = ((lean_object*)(l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__0));
v___x_168_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson_spec__0(v_json_166_, v___x_167_);
if (lean_obj_tag(v___x_168_) == 0)
{
lean_object* v_a_169_; lean_object* v___x_171_; uint8_t v_isShared_172_; uint8_t v_isSharedCheck_178_; 
v_a_169_ = lean_ctor_get(v___x_168_, 0);
v_isSharedCheck_178_ = !lean_is_exclusive(v___x_168_);
if (v_isSharedCheck_178_ == 0)
{
v___x_171_ = v___x_168_;
v_isShared_172_ = v_isSharedCheck_178_;
goto v_resetjp_170_;
}
else
{
lean_inc(v_a_169_);
lean_dec(v___x_168_);
v___x_171_ = lean_box(0);
v_isShared_172_ = v_isSharedCheck_178_;
goto v_resetjp_170_;
}
v_resetjp_170_:
{
lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_176_; 
v___x_173_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__11, &l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__11);
v___x_174_ = lean_string_append(v___x_173_, v_a_169_);
lean_dec(v_a_169_);
if (v_isShared_172_ == 0)
{
lean_ctor_set(v___x_171_, 0, v___x_174_);
v___x_176_ = v___x_171_;
goto v_reusejp_175_;
}
else
{
lean_object* v_reuseFailAlloc_177_; 
v_reuseFailAlloc_177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_177_, 0, v___x_174_);
v___x_176_ = v_reuseFailAlloc_177_;
goto v_reusejp_175_;
}
v_reusejp_175_:
{
return v___x_176_;
}
}
}
else
{
if (lean_obj_tag(v___x_168_) == 0)
{
lean_object* v_a_179_; lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_186_; 
v_a_179_ = lean_ctor_get(v___x_168_, 0);
v_isSharedCheck_186_ = !lean_is_exclusive(v___x_168_);
if (v_isSharedCheck_186_ == 0)
{
v___x_181_ = v___x_168_;
v_isShared_182_ = v_isSharedCheck_186_;
goto v_resetjp_180_;
}
else
{
lean_inc(v_a_179_);
lean_dec(v___x_168_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_186_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
lean_object* v___x_184_; 
if (v_isShared_182_ == 0)
{
lean_ctor_set_tag(v___x_181_, 0);
v___x_184_ = v___x_181_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_185_; 
v_reuseFailAlloc_185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_185_, 0, v_a_179_);
v___x_184_ = v_reuseFailAlloc_185_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
return v___x_184_;
}
}
}
else
{
lean_object* v_a_187_; lean_object* v___x_189_; uint8_t v_isShared_190_; uint8_t v_isSharedCheck_194_; 
v_a_187_ = lean_ctor_get(v___x_168_, 0);
v_isSharedCheck_194_ = !lean_is_exclusive(v___x_168_);
if (v_isSharedCheck_194_ == 0)
{
v___x_189_ = v___x_168_;
v_isShared_190_ = v_isSharedCheck_194_;
goto v_resetjp_188_;
}
else
{
lean_inc(v_a_187_);
lean_dec(v___x_168_);
v___x_189_ = lean_box(0);
v_isShared_190_ = v_isSharedCheck_194_;
goto v_resetjp_188_;
}
v_resetjp_188_:
{
lean_object* v___x_192_; 
if (v_isShared_190_ == 0)
{
v___x_192_ = v___x_189_;
goto v_reusejp_191_;
}
else
{
lean_object* v_reuseFailAlloc_193_; 
v_reuseFailAlloc_193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_193_, 0, v_a_187_);
v___x_192_ = v_reuseFailAlloc_193_;
goto v_reusejp_191_;
}
v_reusejp_191_:
{
return v___x_192_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__1(lean_object* v_j_197_, lean_object* v_k_198_){
_start:
{
lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_201_ = l_Lean_Json_getObjValD(v_j_197_, v_k_198_);
v___x_202_ = l_Lean_Json_getNat_x3f(v___x_201_);
if (lean_obj_tag(v___x_202_) == 1)
{
lean_object* v_a_203_; lean_object* v___x_204_; uint8_t v___x_205_; 
v_a_203_ = lean_ctor_get(v___x_202_, 0);
lean_inc(v_a_203_);
lean_dec_ref_known(v___x_202_, 1);
v___x_204_ = lean_unsigned_to_nat(0u);
v___x_205_ = lean_nat_dec_eq(v_a_203_, v___x_204_);
if (v___x_205_ == 0)
{
lean_object* v___x_206_; uint8_t v___x_207_; 
v___x_206_ = lean_unsigned_to_nat(1u);
v___x_207_ = lean_nat_dec_eq(v_a_203_, v___x_206_);
if (v___x_207_ == 0)
{
lean_object* v___x_208_; uint8_t v___x_209_; 
v___x_208_ = lean_unsigned_to_nat(2u);
v___x_209_ = lean_nat_dec_eq(v_a_203_, v___x_208_);
lean_dec(v_a_203_);
if (v___x_209_ == 0)
{
goto v___jp_199_;
}
else
{
lean_object* v___x_210_; 
v___x_210_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0___closed__2));
return v___x_210_;
}
}
else
{
lean_object* v___x_211_; 
lean_dec(v_a_203_);
v___x_211_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0___closed__3));
return v___x_211_;
}
}
else
{
lean_object* v___x_212_; 
lean_dec(v_a_203_);
v___x_212_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0___closed__4));
return v___x_212_;
}
}
else
{
lean_dec_ref(v___x_202_);
goto v___jp_199_;
}
v___jp_199_:
{
lean_object* v___x_200_; 
v___x_200_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0___closed__1));
return v___x_200_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__1___boxed(lean_object* v_j_213_, lean_object* v_k_214_){
_start:
{
lean_object* v_res_215_; 
v_res_215_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__1(v_j_213_, v_k_214_);
lean_dec_ref(v_k_214_);
return v_res_215_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0_spec__2_spec__3(size_t v_sz_216_, size_t v_i_217_, lean_object* v_bs_218_){
_start:
{
uint8_t v___x_219_; 
v___x_219_ = lean_usize_dec_lt(v_i_217_, v_sz_216_);
if (v___x_219_ == 0)
{
lean_object* v___x_220_; 
v___x_220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_220_, 0, v_bs_218_);
return v___x_220_;
}
else
{
lean_object* v_v_221_; lean_object* v___x_222_; 
v_v_221_ = lean_array_uget_borrowed(v_bs_218_, v_i_217_);
lean_inc(v_v_221_);
v___x_222_ = l_Lean_Lsp_instFromJsonDocumentFilter_fromJson(v_v_221_);
if (lean_obj_tag(v___x_222_) == 0)
{
lean_object* v_a_223_; lean_object* v___x_225_; uint8_t v_isShared_226_; uint8_t v_isSharedCheck_230_; 
lean_dec_ref(v_bs_218_);
v_a_223_ = lean_ctor_get(v___x_222_, 0);
v_isSharedCheck_230_ = !lean_is_exclusive(v___x_222_);
if (v_isSharedCheck_230_ == 0)
{
v___x_225_ = v___x_222_;
v_isShared_226_ = v_isSharedCheck_230_;
goto v_resetjp_224_;
}
else
{
lean_inc(v_a_223_);
lean_dec(v___x_222_);
v___x_225_ = lean_box(0);
v_isShared_226_ = v_isSharedCheck_230_;
goto v_resetjp_224_;
}
v_resetjp_224_:
{
lean_object* v___x_228_; 
if (v_isShared_226_ == 0)
{
v___x_228_ = v___x_225_;
goto v_reusejp_227_;
}
else
{
lean_object* v_reuseFailAlloc_229_; 
v_reuseFailAlloc_229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_229_, 0, v_a_223_);
v___x_228_ = v_reuseFailAlloc_229_;
goto v_reusejp_227_;
}
v_reusejp_227_:
{
return v___x_228_;
}
}
}
else
{
lean_object* v_a_231_; lean_object* v___x_232_; lean_object* v_bs_x27_233_; size_t v___x_234_; size_t v___x_235_; lean_object* v___x_236_; 
v_a_231_ = lean_ctor_get(v___x_222_, 0);
lean_inc(v_a_231_);
lean_dec_ref_known(v___x_222_, 1);
v___x_232_ = lean_unsigned_to_nat(0u);
v_bs_x27_233_ = lean_array_uset(v_bs_218_, v_i_217_, v___x_232_);
v___x_234_ = ((size_t)1ULL);
v___x_235_ = lean_usize_add(v_i_217_, v___x_234_);
v___x_236_ = lean_array_uset(v_bs_x27_233_, v_i_217_, v_a_231_);
v_i_217_ = v___x_235_;
v_bs_218_ = v___x_236_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_sz_238_, lean_object* v_i_239_, lean_object* v_bs_240_){
_start:
{
size_t v_sz_boxed_241_; size_t v_i_boxed_242_; lean_object* v_res_243_; 
v_sz_boxed_241_ = lean_unbox_usize(v_sz_238_);
lean_dec(v_sz_238_);
v_i_boxed_242_ = lean_unbox_usize(v_i_239_);
lean_dec(v_i_239_);
v_res_243_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0_spec__2_spec__3(v_sz_boxed_241_, v_i_boxed_242_, v_bs_240_);
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0_spec__2(lean_object* v_x_246_){
_start:
{
if (lean_obj_tag(v_x_246_) == 4)
{
lean_object* v_elems_247_; size_t v_sz_248_; size_t v___x_249_; lean_object* v___x_250_; 
v_elems_247_ = lean_ctor_get(v_x_246_, 0);
lean_inc_ref(v_elems_247_);
lean_dec_ref_known(v_x_246_, 1);
v_sz_248_ = lean_array_size(v_elems_247_);
v___x_249_ = ((size_t)0ULL);
v___x_250_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0_spec__2_spec__3(v_sz_248_, v___x_249_, v_elems_247_);
return v___x_250_;
}
else
{
lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; 
v___x_251_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0_spec__2___closed__0));
v___x_252_ = lean_unsigned_to_nat(80u);
v___x_253_ = l_Lean_Json_pretty(v_x_246_, v___x_252_);
v___x_254_ = lean_string_append(v___x_251_, v___x_253_);
lean_dec_ref(v___x_253_);
v___x_255_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0_spec__2___closed__1));
v___x_256_ = lean_string_append(v___x_254_, v___x_255_);
v___x_257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_257_, 0, v___x_256_);
return v___x_257_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0(lean_object* v_x_260_){
_start:
{
if (lean_obj_tag(v_x_260_) == 0)
{
lean_object* v___x_261_; 
v___x_261_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0___closed__0));
return v___x_261_;
}
else
{
lean_object* v___x_262_; 
v___x_262_ = l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0_spec__2(v_x_260_);
if (lean_obj_tag(v___x_262_) == 0)
{
lean_object* v_a_263_; lean_object* v___x_265_; uint8_t v_isShared_266_; uint8_t v_isSharedCheck_270_; 
v_a_263_ = lean_ctor_get(v___x_262_, 0);
v_isSharedCheck_270_ = !lean_is_exclusive(v___x_262_);
if (v_isSharedCheck_270_ == 0)
{
v___x_265_ = v___x_262_;
v_isShared_266_ = v_isSharedCheck_270_;
goto v_resetjp_264_;
}
else
{
lean_inc(v_a_263_);
lean_dec(v___x_262_);
v___x_265_ = lean_box(0);
v_isShared_266_ = v_isSharedCheck_270_;
goto v_resetjp_264_;
}
v_resetjp_264_:
{
lean_object* v___x_268_; 
if (v_isShared_266_ == 0)
{
v___x_268_ = v___x_265_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v_a_263_);
v___x_268_ = v_reuseFailAlloc_269_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
return v___x_268_;
}
}
}
else
{
lean_object* v_a_271_; lean_object* v___x_273_; uint8_t v_isShared_274_; uint8_t v_isSharedCheck_279_; 
v_a_271_ = lean_ctor_get(v___x_262_, 0);
v_isSharedCheck_279_ = !lean_is_exclusive(v___x_262_);
if (v_isSharedCheck_279_ == 0)
{
v___x_273_ = v___x_262_;
v_isShared_274_ = v_isSharedCheck_279_;
goto v_resetjp_272_;
}
else
{
lean_inc(v_a_271_);
lean_dec(v___x_262_);
v___x_273_ = lean_box(0);
v_isShared_274_ = v_isSharedCheck_279_;
goto v_resetjp_272_;
}
v_resetjp_272_:
{
lean_object* v___x_275_; lean_object* v___x_277_; 
v___x_275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_275_, 0, v_a_271_);
if (v_isShared_274_ == 0)
{
lean_ctor_set(v___x_273_, 0, v___x_275_);
v___x_277_ = v___x_273_;
goto v_reusejp_276_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v___x_275_);
v___x_277_ = v_reuseFailAlloc_278_;
goto v_reusejp_276_;
}
v_reusejp_276_:
{
return v___x_277_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0(lean_object* v_j_280_, lean_object* v_k_281_){
_start:
{
lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_282_ = l_Lean_Json_getObjValD(v_j_280_, v_k_281_);
v___x_283_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0(v___x_282_);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0___boxed(lean_object* v_j_284_, lean_object* v_k_285_){
_start:
{
lean_object* v_res_286_; 
v_res_286_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0(v_j_284_, v_k_285_);
lean_dec_ref(v_k_285_);
return v_res_286_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__3(void){
_start:
{
uint8_t v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_293_ = 1;
v___x_294_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__2));
v___x_295_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_294_, v___x_293_);
return v___x_295_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__4(void){
_start:
{
lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_296_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__5));
v___x_297_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__3, &l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__3);
v___x_298_ = lean_string_append(v___x_297_, v___x_296_);
return v___x_298_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__7(void){
_start:
{
uint8_t v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_302_ = 1;
v___x_303_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__6));
v___x_304_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_303_, v___x_302_);
return v___x_304_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__8(void){
_start:
{
lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_305_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__7, &l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__7);
v___x_306_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__4, &l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__4);
v___x_307_ = lean_string_append(v___x_306_, v___x_305_);
return v___x_307_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__9(void){
_start:
{
lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_308_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__10));
v___x_309_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__8, &l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__8);
v___x_310_ = lean_string_append(v___x_309_, v___x_308_);
return v___x_310_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__12(void){
_start:
{
uint8_t v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_314_ = 1;
v___x_315_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__11));
v___x_316_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_315_, v___x_314_);
return v___x_316_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__13(void){
_start:
{
lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_317_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__12, &l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__12);
v___x_318_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__4, &l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__4);
v___x_319_ = lean_string_append(v___x_318_, v___x_317_);
return v___x_319_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__14(void){
_start:
{
lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_320_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__10));
v___x_321_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__13, &l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__13);
v___x_322_ = lean_string_append(v___x_321_, v___x_320_);
return v___x_322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson(lean_object* v_json_323_){
_start:
{
lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_324_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__0));
lean_inc(v_json_323_);
v___x_325_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0(v_json_323_, v___x_324_);
if (lean_obj_tag(v___x_325_) == 0)
{
lean_object* v_a_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_335_; 
lean_dec(v_json_323_);
v_a_326_ = lean_ctor_get(v___x_325_, 0);
v_isSharedCheck_335_ = !lean_is_exclusive(v___x_325_);
if (v_isSharedCheck_335_ == 0)
{
v___x_328_ = v___x_325_;
v_isShared_329_ = v_isSharedCheck_335_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_a_326_);
lean_dec(v___x_325_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_335_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_333_; 
v___x_330_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__9, &l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__9);
v___x_331_ = lean_string_append(v___x_330_, v_a_326_);
lean_dec(v_a_326_);
if (v_isShared_329_ == 0)
{
lean_ctor_set(v___x_328_, 0, v___x_331_);
v___x_333_ = v___x_328_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v___x_331_);
v___x_333_ = v_reuseFailAlloc_334_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
return v___x_333_;
}
}
}
else
{
if (lean_obj_tag(v___x_325_) == 0)
{
lean_object* v_a_336_; lean_object* v___x_338_; uint8_t v_isShared_339_; uint8_t v_isSharedCheck_343_; 
lean_dec(v_json_323_);
v_a_336_ = lean_ctor_get(v___x_325_, 0);
v_isSharedCheck_343_ = !lean_is_exclusive(v___x_325_);
if (v_isSharedCheck_343_ == 0)
{
v___x_338_ = v___x_325_;
v_isShared_339_ = v_isSharedCheck_343_;
goto v_resetjp_337_;
}
else
{
lean_inc(v_a_336_);
lean_dec(v___x_325_);
v___x_338_ = lean_box(0);
v_isShared_339_ = v_isSharedCheck_343_;
goto v_resetjp_337_;
}
v_resetjp_337_:
{
lean_object* v___x_341_; 
if (v_isShared_339_ == 0)
{
lean_ctor_set_tag(v___x_338_, 0);
v___x_341_ = v___x_338_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v_a_336_);
v___x_341_ = v_reuseFailAlloc_342_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
return v___x_341_;
}
}
}
else
{
lean_object* v_a_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
v_a_344_ = lean_ctor_get(v___x_325_, 0);
lean_inc(v_a_344_);
lean_dec_ref_known(v___x_325_, 1);
v___x_345_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__10));
v___x_346_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__1(v_json_323_, v___x_345_);
if (lean_obj_tag(v___x_346_) == 0)
{
lean_object* v_a_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_356_; 
lean_dec(v_a_344_);
v_a_347_ = lean_ctor_get(v___x_346_, 0);
v_isSharedCheck_356_ = !lean_is_exclusive(v___x_346_);
if (v_isSharedCheck_356_ == 0)
{
v___x_349_ = v___x_346_;
v_isShared_350_ = v_isSharedCheck_356_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_a_347_);
lean_dec(v___x_346_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_356_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_354_; 
v___x_351_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__14, &l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__14_once, _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__14);
v___x_352_ = lean_string_append(v___x_351_, v_a_347_);
lean_dec(v_a_347_);
if (v_isShared_350_ == 0)
{
lean_ctor_set(v___x_349_, 0, v___x_352_);
v___x_354_ = v___x_349_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v___x_352_);
v___x_354_ = v_reuseFailAlloc_355_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
return v___x_354_;
}
}
}
else
{
if (lean_obj_tag(v___x_346_) == 0)
{
lean_object* v_a_357_; lean_object* v___x_359_; uint8_t v_isShared_360_; uint8_t v_isSharedCheck_364_; 
lean_dec(v_a_344_);
v_a_357_ = lean_ctor_get(v___x_346_, 0);
v_isSharedCheck_364_ = !lean_is_exclusive(v___x_346_);
if (v_isSharedCheck_364_ == 0)
{
v___x_359_ = v___x_346_;
v_isShared_360_ = v_isSharedCheck_364_;
goto v_resetjp_358_;
}
else
{
lean_inc(v_a_357_);
lean_dec(v___x_346_);
v___x_359_ = lean_box(0);
v_isShared_360_ = v_isSharedCheck_364_;
goto v_resetjp_358_;
}
v_resetjp_358_:
{
lean_object* v___x_362_; 
if (v_isShared_360_ == 0)
{
lean_ctor_set_tag(v___x_359_, 0);
v___x_362_ = v___x_359_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_363_; 
v_reuseFailAlloc_363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_363_, 0, v_a_357_);
v___x_362_ = v_reuseFailAlloc_363_;
goto v_reusejp_361_;
}
v_reusejp_361_:
{
return v___x_362_;
}
}
}
else
{
lean_object* v_a_365_; lean_object* v___x_367_; uint8_t v_isShared_368_; uint8_t v_isSharedCheck_374_; 
v_a_365_ = lean_ctor_get(v___x_346_, 0);
v_isSharedCheck_374_ = !lean_is_exclusive(v___x_346_);
if (v_isSharedCheck_374_ == 0)
{
v___x_367_ = v___x_346_;
v_isShared_368_ = v_isSharedCheck_374_;
goto v_resetjp_366_;
}
else
{
lean_inc(v_a_365_);
lean_dec(v___x_346_);
v___x_367_ = lean_box(0);
v_isShared_368_ = v_isSharedCheck_374_;
goto v_resetjp_366_;
}
v_resetjp_366_:
{
lean_object* v___x_369_; uint8_t v___x_370_; lean_object* v___x_372_; 
v___x_369_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_369_, 0, v_a_344_);
v___x_370_ = lean_unbox(v_a_365_);
lean_dec(v_a_365_);
lean_ctor_set_uint8(v___x_369_, sizeof(void*)*1, v___x_370_);
if (v_isShared_368_ == 0)
{
lean_ctor_set(v___x_367_, 0, v___x_369_);
v___x_372_ = v___x_367_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v___x_369_);
v___x_372_ = v_reuseFailAlloc_373_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
return v___x_372_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentContentChangeEvent_ctorIdx(lean_object* v_x_377_){
_start:
{
if (lean_obj_tag(v_x_377_) == 0)
{
lean_object* v___x_378_; 
v___x_378_ = lean_unsigned_to_nat(0u);
return v___x_378_;
}
else
{
lean_object* v___x_379_; 
v___x_379_ = lean_unsigned_to_nat(1u);
return v___x_379_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentContentChangeEvent_ctorIdx___boxed(lean_object* v_x_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l_Lean_Lsp_TextDocumentContentChangeEvent_ctorIdx(v_x_380_);
lean_dec_ref(v_x_380_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentContentChangeEvent_ctorElim___redArg(lean_object* v_t_382_, lean_object* v_k_383_){
_start:
{
if (lean_obj_tag(v_t_382_) == 0)
{
lean_object* v_range_384_; lean_object* v_text_385_; lean_object* v___x_386_; 
v_range_384_ = lean_ctor_get(v_t_382_, 0);
lean_inc_ref(v_range_384_);
v_text_385_ = lean_ctor_get(v_t_382_, 1);
lean_inc_ref(v_text_385_);
lean_dec_ref_known(v_t_382_, 2);
v___x_386_ = lean_apply_2(v_k_383_, v_range_384_, v_text_385_);
return v___x_386_;
}
else
{
lean_object* v_text_387_; lean_object* v___x_388_; 
v_text_387_ = lean_ctor_get(v_t_382_, 0);
lean_inc_ref(v_text_387_);
lean_dec_ref_known(v_t_382_, 1);
v___x_388_ = lean_apply_1(v_k_383_, v_text_387_);
return v___x_388_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentContentChangeEvent_ctorElim(lean_object* v_motive_389_, lean_object* v_ctorIdx_390_, lean_object* v_t_391_, lean_object* v_h_392_, lean_object* v_k_393_){
_start:
{
lean_object* v___x_394_; 
v___x_394_ = l_Lean_Lsp_TextDocumentContentChangeEvent_ctorElim___redArg(v_t_391_, v_k_393_);
return v___x_394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentContentChangeEvent_ctorElim___boxed(lean_object* v_motive_395_, lean_object* v_ctorIdx_396_, lean_object* v_t_397_, lean_object* v_h_398_, lean_object* v_k_399_){
_start:
{
lean_object* v_res_400_; 
v_res_400_ = l_Lean_Lsp_TextDocumentContentChangeEvent_ctorElim(v_motive_395_, v_ctorIdx_396_, v_t_397_, v_h_398_, v_k_399_);
lean_dec(v_ctorIdx_396_);
return v_res_400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentContentChangeEvent_rangeChange_elim___redArg(lean_object* v_t_401_, lean_object* v_rangeChange_402_){
_start:
{
lean_object* v___x_403_; 
v___x_403_ = l_Lean_Lsp_TextDocumentContentChangeEvent_ctorElim___redArg(v_t_401_, v_rangeChange_402_);
return v___x_403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentContentChangeEvent_rangeChange_elim(lean_object* v_motive_404_, lean_object* v_t_405_, lean_object* v_h_406_, lean_object* v_rangeChange_407_){
_start:
{
lean_object* v___x_408_; 
v___x_408_ = l_Lean_Lsp_TextDocumentContentChangeEvent_ctorElim___redArg(v_t_405_, v_rangeChange_407_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentContentChangeEvent_fullChange_elim___redArg(lean_object* v_t_409_, lean_object* v_fullChange_410_){
_start:
{
lean_object* v___x_411_; 
v___x_411_ = l_Lean_Lsp_TextDocumentContentChangeEvent_ctorElim___redArg(v_t_409_, v_fullChange_410_);
return v___x_411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentContentChangeEvent_fullChange_elim(lean_object* v_motive_412_, lean_object* v_t_413_, lean_object* v_h_414_, lean_object* v_fullChange_415_){
_start:
{
lean_object* v___x_416_; 
v___x_416_ = l_Lean_Lsp_TextDocumentContentChangeEvent_ctorElim___redArg(v_t_413_, v_fullChange_415_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0(lean_object* v___x_419_, lean_object* v___x_420_, lean_object* v_j_421_){
_start:
{
lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_442_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0___closed__1));
lean_inc(v_j_421_);
v___x_443_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_421_, v___x_420_, v___x_442_);
if (lean_obj_tag(v___x_443_) == 0)
{
lean_dec_ref_known(v___x_443_, 1);
goto v___jp_422_;
}
else
{
lean_object* v_a_444_; lean_object* v___x_445_; lean_object* v___x_446_; 
v_a_444_ = lean_ctor_get(v___x_443_, 0);
lean_inc(v_a_444_);
lean_dec_ref_known(v___x_443_, 1);
v___x_445_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0___closed__0));
lean_inc_ref(v___x_419_);
lean_inc(v_j_421_);
v___x_446_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_421_, v___x_419_, v___x_445_);
if (lean_obj_tag(v___x_446_) == 0)
{
lean_dec_ref_known(v___x_446_, 1);
lean_dec(v_a_444_);
goto v___jp_422_;
}
else
{
lean_object* v_a_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_455_; 
lean_dec(v_j_421_);
lean_dec_ref(v___x_419_);
v_a_447_ = lean_ctor_get(v___x_446_, 0);
v_isSharedCheck_455_ = !lean_is_exclusive(v___x_446_);
if (v_isSharedCheck_455_ == 0)
{
v___x_449_ = v___x_446_;
v_isShared_450_ = v_isSharedCheck_455_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_a_447_);
lean_dec(v___x_446_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_455_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v___x_451_; lean_object* v___x_453_; 
v___x_451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_451_, 0, v_a_444_);
lean_ctor_set(v___x_451_, 1, v_a_447_);
if (v_isShared_450_ == 0)
{
lean_ctor_set(v___x_449_, 0, v___x_451_);
v___x_453_ = v___x_449_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v___x_451_);
v___x_453_ = v_reuseFailAlloc_454_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
return v___x_453_;
}
}
}
}
v___jp_422_:
{
lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_423_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0___closed__0));
v___x_424_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_421_, v___x_419_, v___x_423_);
if (lean_obj_tag(v___x_424_) == 0)
{
lean_object* v_a_425_; lean_object* v___x_427_; uint8_t v_isShared_428_; uint8_t v_isSharedCheck_432_; 
v_a_425_ = lean_ctor_get(v___x_424_, 0);
v_isSharedCheck_432_ = !lean_is_exclusive(v___x_424_);
if (v_isSharedCheck_432_ == 0)
{
v___x_427_ = v___x_424_;
v_isShared_428_ = v_isSharedCheck_432_;
goto v_resetjp_426_;
}
else
{
lean_inc(v_a_425_);
lean_dec(v___x_424_);
v___x_427_ = lean_box(0);
v_isShared_428_ = v_isSharedCheck_432_;
goto v_resetjp_426_;
}
v_resetjp_426_:
{
lean_object* v___x_430_; 
if (v_isShared_428_ == 0)
{
v___x_430_ = v___x_427_;
goto v_reusejp_429_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v_a_425_);
v___x_430_ = v_reuseFailAlloc_431_;
goto v_reusejp_429_;
}
v_reusejp_429_:
{
return v___x_430_;
}
}
}
else
{
lean_object* v_a_433_; lean_object* v___x_435_; uint8_t v_isShared_436_; uint8_t v_isSharedCheck_441_; 
v_a_433_ = lean_ctor_get(v___x_424_, 0);
v_isSharedCheck_441_ = !lean_is_exclusive(v___x_424_);
if (v_isSharedCheck_441_ == 0)
{
v___x_435_ = v___x_424_;
v_isShared_436_ = v_isSharedCheck_441_;
goto v_resetjp_434_;
}
else
{
lean_inc(v_a_433_);
lean_dec(v___x_424_);
v___x_435_ = lean_box(0);
v_isShared_436_ = v_isSharedCheck_441_;
goto v_resetjp_434_;
}
v_resetjp_434_:
{
lean_object* v___x_437_; lean_object* v___x_439_; 
v___x_437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_437_, 0, v_a_433_);
if (v_isShared_436_ == 0)
{
lean_ctor_set(v___x_435_, 0, v___x_437_);
v___x_439_ = v___x_435_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v___x_437_);
v___x_439_ = v_reuseFailAlloc_440_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
return v___x_439_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentContentChangeEvent_hasToJson___lam__0(lean_object* v_o_462_){
_start:
{
if (lean_obj_tag(v_o_462_) == 0)
{
lean_object* v_range_463_; lean_object* v_text_464_; lean_object* v___x_466_; uint8_t v_isShared_467_; uint8_t v_isSharedCheck_480_; 
v_range_463_ = lean_ctor_get(v_o_462_, 0);
v_text_464_ = lean_ctor_get(v_o_462_, 1);
v_isSharedCheck_480_ = !lean_is_exclusive(v_o_462_);
if (v_isSharedCheck_480_ == 0)
{
v___x_466_ = v_o_462_;
v_isShared_467_ = v_isSharedCheck_480_;
goto v_resetjp_465_;
}
else
{
lean_inc(v_text_464_);
lean_inc(v_range_463_);
lean_dec(v_o_462_);
v___x_466_ = lean_box(0);
v_isShared_467_ = v_isSharedCheck_480_;
goto v_resetjp_465_;
}
v_resetjp_465_:
{
lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_471_; 
v___x_468_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0___closed__1));
v___x_469_ = l_Lean_Lsp_instToJsonRange_toJson(v_range_463_);
if (v_isShared_467_ == 0)
{
lean_ctor_set(v___x_466_, 1, v___x_469_);
lean_ctor_set(v___x_466_, 0, v___x_468_);
v___x_471_ = v___x_466_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v___x_468_);
lean_ctor_set(v_reuseFailAlloc_479_, 1, v___x_469_);
v___x_471_ = v_reuseFailAlloc_479_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_472_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0___closed__0));
v___x_473_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_473_, 0, v_text_464_);
v___x_474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_474_, 0, v___x_472_);
lean_ctor_set(v___x_474_, 1, v___x_473_);
v___x_475_ = lean_box(0);
v___x_476_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_476_, 0, v___x_474_);
lean_ctor_set(v___x_476_, 1, v___x_475_);
v___x_477_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_477_, 0, v___x_471_);
lean_ctor_set(v___x_477_, 1, v___x_476_);
v___x_478_ = l_Lean_Json_mkObj(v___x_477_);
lean_dec_ref_known(v___x_477_, 2);
return v___x_478_;
}
}
}
else
{
lean_object* v_text_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_493_; 
v_text_481_ = lean_ctor_get(v_o_462_, 0);
v_isSharedCheck_493_ = !lean_is_exclusive(v_o_462_);
if (v_isSharedCheck_493_ == 0)
{
v___x_483_ = v_o_462_;
v_isShared_484_ = v_isSharedCheck_493_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_text_481_);
lean_dec(v_o_462_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_493_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
lean_object* v___x_485_; lean_object* v___x_487_; 
v___x_485_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0___closed__0));
if (v_isShared_484_ == 0)
{
lean_ctor_set_tag(v___x_483_, 3);
v___x_487_ = v___x_483_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v_text_481_);
v___x_487_ = v_reuseFailAlloc_492_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; 
v___x_488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_488_, 0, v___x_485_);
lean_ctor_set(v___x_488_, 1, v___x_487_);
v___x_489_ = lean_box(0);
v___x_490_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_490_, 0, v___x_488_);
lean_ctor_set(v___x_490_, 1, v___x_489_);
v___x_491_ = l_Lean_Json_mkObj(v___x_490_);
lean_dec_ref_known(v___x_490_, 2);
return v___x_491_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonDidChangeTextDocumentParams_toJson_spec__0_spec__0(size_t v_sz_496_, size_t v_i_497_, lean_object* v_bs_498_){
_start:
{
uint8_t v___x_499_; 
v___x_499_ = lean_usize_dec_lt(v_i_497_, v_sz_496_);
if (v___x_499_ == 0)
{
return v_bs_498_;
}
else
{
lean_object* v_v_500_; lean_object* v___x_501_; lean_object* v_bs_x27_502_; lean_object* v___y_504_; 
v_v_500_ = lean_array_uget(v_bs_498_, v_i_497_);
v___x_501_ = lean_unsigned_to_nat(0u);
v_bs_x27_502_ = lean_array_uset(v_bs_498_, v_i_497_, v___x_501_);
if (lean_obj_tag(v_v_500_) == 0)
{
lean_object* v_range_509_; lean_object* v_text_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_526_; 
v_range_509_ = lean_ctor_get(v_v_500_, 0);
v_text_510_ = lean_ctor_get(v_v_500_, 1);
v_isSharedCheck_526_ = !lean_is_exclusive(v_v_500_);
if (v_isSharedCheck_526_ == 0)
{
v___x_512_ = v_v_500_;
v_isShared_513_ = v_isSharedCheck_526_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_text_510_);
lean_inc(v_range_509_);
lean_dec(v_v_500_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_526_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_517_; 
v___x_514_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0___closed__1));
v___x_515_ = l_Lean_Lsp_instToJsonRange_toJson(v_range_509_);
if (v_isShared_513_ == 0)
{
lean_ctor_set(v___x_512_, 1, v___x_515_);
lean_ctor_set(v___x_512_, 0, v___x_514_);
v___x_517_ = v___x_512_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v___x_514_);
lean_ctor_set(v_reuseFailAlloc_525_, 1, v___x_515_);
v___x_517_ = v_reuseFailAlloc_525_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; 
v___x_518_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0___closed__0));
v___x_519_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_519_, 0, v_text_510_);
v___x_520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_520_, 0, v___x_518_);
lean_ctor_set(v___x_520_, 1, v___x_519_);
v___x_521_ = lean_box(0);
v___x_522_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_522_, 0, v___x_520_);
lean_ctor_set(v___x_522_, 1, v___x_521_);
v___x_523_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_523_, 0, v___x_517_);
lean_ctor_set(v___x_523_, 1, v___x_522_);
v___x_524_ = l_Lean_Json_mkObj(v___x_523_);
lean_dec_ref_known(v___x_523_, 2);
v___y_504_ = v___x_524_;
goto v___jp_503_;
}
}
}
else
{
lean_object* v_text_527_; lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_539_; 
v_text_527_ = lean_ctor_get(v_v_500_, 0);
v_isSharedCheck_539_ = !lean_is_exclusive(v_v_500_);
if (v_isSharedCheck_539_ == 0)
{
v___x_529_ = v_v_500_;
v_isShared_530_ = v_isSharedCheck_539_;
goto v_resetjp_528_;
}
else
{
lean_inc(v_text_527_);
lean_dec(v_v_500_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_539_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
lean_object* v___x_531_; lean_object* v___x_533_; 
v___x_531_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0___closed__0));
if (v_isShared_530_ == 0)
{
lean_ctor_set_tag(v___x_529_, 3);
v___x_533_ = v___x_529_;
goto v_reusejp_532_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v_text_527_);
v___x_533_ = v_reuseFailAlloc_538_;
goto v_reusejp_532_;
}
v_reusejp_532_:
{
lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; 
v___x_534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_534_, 0, v___x_531_);
lean_ctor_set(v___x_534_, 1, v___x_533_);
v___x_535_ = lean_box(0);
v___x_536_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_536_, 0, v___x_534_);
lean_ctor_set(v___x_536_, 1, v___x_535_);
v___x_537_ = l_Lean_Json_mkObj(v___x_536_);
lean_dec_ref_known(v___x_536_, 2);
v___y_504_ = v___x_537_;
goto v___jp_503_;
}
}
}
v___jp_503_:
{
size_t v___x_505_; size_t v___x_506_; lean_object* v___x_507_; 
v___x_505_ = ((size_t)1ULL);
v___x_506_ = lean_usize_add(v_i_497_, v___x_505_);
v___x_507_ = lean_array_uset(v_bs_x27_502_, v_i_497_, v___y_504_);
v_i_497_ = v___x_506_;
v_bs_498_ = v___x_507_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonDidChangeTextDocumentParams_toJson_spec__0_spec__0___boxed(lean_object* v_sz_540_, lean_object* v_i_541_, lean_object* v_bs_542_){
_start:
{
size_t v_sz_boxed_543_; size_t v_i_boxed_544_; lean_object* v_res_545_; 
v_sz_boxed_543_ = lean_unbox_usize(v_sz_540_);
lean_dec(v_sz_540_);
v_i_boxed_544_ = lean_unbox_usize(v_i_541_);
lean_dec(v_i_541_);
v_res_545_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonDidChangeTextDocumentParams_toJson_spec__0_spec__0(v_sz_boxed_543_, v_i_boxed_544_, v_bs_542_);
return v_res_545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonDidChangeTextDocumentParams_toJson_spec__0(lean_object* v_a_546_){
_start:
{
size_t v_sz_547_; size_t v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; 
v_sz_547_ = lean_array_size(v_a_546_);
v___x_548_ = ((size_t)0ULL);
v___x_549_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonDidChangeTextDocumentParams_toJson_spec__0_spec__0(v_sz_547_, v___x_548_, v_a_546_);
v___x_550_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_550_, 0, v___x_549_);
return v___x_550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDidChangeTextDocumentParams_toJson(lean_object* v_x_552_){
_start:
{
lean_object* v_textDocument_553_; lean_object* v_contentChanges_554_; lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_574_; 
v_textDocument_553_ = lean_ctor_get(v_x_552_, 0);
v_contentChanges_554_ = lean_ctor_get(v_x_552_, 1);
v_isSharedCheck_574_ = !lean_is_exclusive(v_x_552_);
if (v_isSharedCheck_574_ == 0)
{
v___x_556_ = v_x_552_;
v_isShared_557_ = v_isSharedCheck_574_;
goto v_resetjp_555_;
}
else
{
lean_inc(v_contentChanges_554_);
lean_inc(v_textDocument_553_);
lean_dec(v_x_552_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_574_;
goto v_resetjp_555_;
}
v_resetjp_555_:
{
lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_561_; 
v___x_558_ = ((lean_object*)(l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__0));
v___x_559_ = l_Lean_Lsp_instToJsonVersionedTextDocumentIdentifier_toJson(v_textDocument_553_);
if (v_isShared_557_ == 0)
{
lean_ctor_set(v___x_556_, 1, v___x_559_);
lean_ctor_set(v___x_556_, 0, v___x_558_);
v___x_561_ = v___x_556_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v___x_558_);
lean_ctor_set(v_reuseFailAlloc_573_, 1, v___x_559_);
v___x_561_ = v_reuseFailAlloc_573_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_562_ = lean_box(0);
v___x_563_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_563_, 0, v___x_561_);
lean_ctor_set(v___x_563_, 1, v___x_562_);
v___x_564_ = ((lean_object*)(l_Lean_Lsp_instToJsonDidChangeTextDocumentParams_toJson___closed__0));
v___x_565_ = l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonDidChangeTextDocumentParams_toJson_spec__0(v_contentChanges_554_);
v___x_566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_566_, 0, v___x_564_);
lean_ctor_set(v___x_566_, 1, v___x_565_);
v___x_567_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_567_, 0, v___x_566_);
lean_ctor_set(v___x_567_, 1, v___x_562_);
v___x_568_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_568_, 0, v___x_567_);
lean_ctor_set(v___x_568_, 1, v___x_562_);
v___x_569_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_569_, 0, v___x_563_);
lean_ctor_set(v___x_569_, 1, v___x_568_);
v___x_570_ = ((lean_object*)(l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__1));
v___x_571_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson_spec__0(v___x_569_, v___x_570_);
v___x_572_ = l_Lean_Json_mkObj(v___x_571_);
lean_dec(v___x_571_);
return v___x_572_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__0(lean_object* v_j_577_, lean_object* v_k_578_){
_start:
{
lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_579_ = l_Lean_Json_getObjValD(v_j_577_, v_k_578_);
v___x_580_ = l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson(v___x_579_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__0___boxed(lean_object* v_j_581_, lean_object* v_k_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__0(v_j_581_, v_k_582_);
lean_dec_ref(v_k_582_);
return v_res_583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1_spec__3(lean_object* v_j_584_, lean_object* v_k_585_){
_start:
{
lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_586_ = l_Lean_Json_getObjValD(v_j_584_, v_k_585_);
v___x_587_ = l_Lean_Lsp_instFromJsonRange_fromJson(v___x_586_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1_spec__3___boxed(lean_object* v_j_588_, lean_object* v_k_589_){
_start:
{
lean_object* v_res_590_; 
v_res_590_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1_spec__3(v_j_588_, v_k_589_);
lean_dec_ref(v_k_589_);
return v_res_590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1_spec__2(lean_object* v_j_591_, lean_object* v_k_592_){
_start:
{
lean_object* v___x_593_; lean_object* v___x_594_; 
v___x_593_ = l_Lean_Json_getObjValD(v_j_591_, v_k_592_);
v___x_594_ = l_Lean_Json_getStr_x3f(v___x_593_);
return v___x_594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1_spec__2___boxed(lean_object* v_j_595_, lean_object* v_k_596_){
_start:
{
lean_object* v_res_597_; 
v_res_597_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1_spec__2(v_j_595_, v_k_596_);
lean_dec_ref(v_k_596_);
return v_res_597_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1_spec__4(size_t v_sz_598_, size_t v_i_599_, lean_object* v_bs_600_){
_start:
{
uint8_t v___x_601_; 
v___x_601_ = lean_usize_dec_lt(v_i_599_, v_sz_598_);
if (v___x_601_ == 0)
{
lean_object* v___x_602_; 
v___x_602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_602_, 0, v_bs_600_);
return v___x_602_;
}
else
{
lean_object* v_v_603_; lean_object* v___x_604_; lean_object* v_bs_x27_605_; lean_object* v_a_607_; lean_object* v___x_625_; lean_object* v___x_626_; 
v_v_603_ = lean_array_uget(v_bs_600_, v_i_599_);
v___x_604_ = lean_unsigned_to_nat(0u);
v_bs_x27_605_ = lean_array_uset(v_bs_600_, v_i_599_, v___x_604_);
v___x_625_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0___closed__1));
lean_inc(v_v_603_);
v___x_626_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1_spec__3(v_v_603_, v___x_625_);
if (lean_obj_tag(v___x_626_) == 0)
{
lean_dec_ref_known(v___x_626_, 1);
goto v___jp_612_;
}
else
{
lean_object* v_a_627_; lean_object* v___x_628_; lean_object* v___x_629_; 
v_a_627_ = lean_ctor_get(v___x_626_, 0);
lean_inc(v_a_627_);
lean_dec_ref_known(v___x_626_, 1);
v___x_628_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0___closed__0));
lean_inc(v_v_603_);
v___x_629_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1_spec__2(v_v_603_, v___x_628_);
if (lean_obj_tag(v___x_629_) == 0)
{
lean_dec_ref_known(v___x_629_, 1);
lean_dec(v_a_627_);
goto v___jp_612_;
}
else
{
lean_object* v_a_630_; lean_object* v___x_631_; 
lean_dec(v_v_603_);
v_a_630_ = lean_ctor_get(v___x_629_, 0);
lean_inc(v_a_630_);
lean_dec_ref_known(v___x_629_, 1);
v___x_631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_631_, 0, v_a_627_);
lean_ctor_set(v___x_631_, 1, v_a_630_);
v_a_607_ = v___x_631_;
goto v___jp_606_;
}
}
v___jp_606_:
{
size_t v___x_608_; size_t v___x_609_; lean_object* v___x_610_; 
v___x_608_ = ((size_t)1ULL);
v___x_609_ = lean_usize_add(v_i_599_, v___x_608_);
v___x_610_ = lean_array_uset(v_bs_x27_605_, v_i_599_, v_a_607_);
v_i_599_ = v___x_609_;
v_bs_600_ = v___x_610_;
goto _start;
}
v___jp_612_:
{
lean_object* v___x_613_; lean_object* v___x_614_; 
v___x_613_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0___closed__0));
v___x_614_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1_spec__2(v_v_603_, v___x_613_);
if (lean_obj_tag(v___x_614_) == 0)
{
lean_object* v_a_615_; lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_622_; 
lean_dec_ref(v_bs_x27_605_);
v_a_615_ = lean_ctor_get(v___x_614_, 0);
v_isSharedCheck_622_ = !lean_is_exclusive(v___x_614_);
if (v_isSharedCheck_622_ == 0)
{
v___x_617_ = v___x_614_;
v_isShared_618_ = v_isSharedCheck_622_;
goto v_resetjp_616_;
}
else
{
lean_inc(v_a_615_);
lean_dec(v___x_614_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_622_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
lean_object* v___x_620_; 
if (v_isShared_618_ == 0)
{
v___x_620_ = v___x_617_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v_a_615_);
v___x_620_ = v_reuseFailAlloc_621_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
return v___x_620_;
}
}
}
else
{
lean_object* v_a_623_; lean_object* v___x_624_; 
v_a_623_ = lean_ctor_get(v___x_614_, 0);
lean_inc(v_a_623_);
lean_dec_ref_known(v___x_614_, 1);
v___x_624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_624_, 0, v_a_623_);
v_a_607_ = v___x_624_;
goto v___jp_606_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1_spec__4___boxed(lean_object* v_sz_632_, lean_object* v_i_633_, lean_object* v_bs_634_){
_start:
{
size_t v_sz_boxed_635_; size_t v_i_boxed_636_; lean_object* v_res_637_; 
v_sz_boxed_635_ = lean_unbox_usize(v_sz_632_);
lean_dec(v_sz_632_);
v_i_boxed_636_ = lean_unbox_usize(v_i_633_);
lean_dec(v_i_633_);
v_res_637_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1_spec__4(v_sz_boxed_635_, v_i_boxed_636_, v_bs_634_);
return v_res_637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1(lean_object* v_x_638_){
_start:
{
if (lean_obj_tag(v_x_638_) == 4)
{
lean_object* v_elems_639_; size_t v_sz_640_; size_t v___x_641_; lean_object* v___x_642_; 
v_elems_639_ = lean_ctor_get(v_x_638_, 0);
lean_inc_ref(v_elems_639_);
lean_dec_ref_known(v_x_638_, 1);
v_sz_640_ = lean_array_size(v_elems_639_);
v___x_641_ = ((size_t)0ULL);
v___x_642_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1_spec__4(v_sz_640_, v___x_641_, v_elems_639_);
return v___x_642_;
}
else
{
lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_643_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0_spec__2___closed__0));
v___x_644_ = lean_unsigned_to_nat(80u);
v___x_645_ = l_Lean_Json_pretty(v_x_638_, v___x_644_);
v___x_646_ = lean_string_append(v___x_643_, v___x_645_);
lean_dec_ref(v___x_645_);
v___x_647_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0_spec__2___closed__1));
v___x_648_ = lean_string_append(v___x_646_, v___x_647_);
v___x_649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_649_, 0, v___x_648_);
return v___x_649_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1(lean_object* v_j_650_, lean_object* v_k_651_){
_start:
{
lean_object* v___x_652_; lean_object* v___x_653_; 
v___x_652_ = l_Lean_Json_getObjValD(v_j_650_, v_k_651_);
v___x_653_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1(v___x_652_);
return v___x_653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1___boxed(lean_object* v_j_654_, lean_object* v_k_655_){
_start:
{
lean_object* v_res_656_; 
v_res_656_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1(v_j_654_, v_k_655_);
lean_dec_ref(v_k_655_);
return v_res_656_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__2(void){
_start:
{
uint8_t v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; 
v___x_662_ = 1;
v___x_663_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__1));
v___x_664_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_663_, v___x_662_);
return v___x_664_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__3(void){
_start:
{
lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; 
v___x_665_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__5));
v___x_666_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__2, &l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__2);
v___x_667_ = lean_string_append(v___x_666_, v___x_665_);
return v___x_667_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; 
v___x_668_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__8);
v___x_669_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__3);
v___x_670_ = lean_string_append(v___x_669_, v___x_668_);
return v___x_670_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__5(void){
_start:
{
lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; 
v___x_671_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__10));
v___x_672_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__4);
v___x_673_ = lean_string_append(v___x_672_, v___x_671_);
return v___x_673_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__7(void){
_start:
{
uint8_t v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; 
v___x_676_ = 1;
v___x_677_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__6));
v___x_678_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_677_, v___x_676_);
return v___x_678_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__8(void){
_start:
{
lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_679_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__7);
v___x_680_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__3);
v___x_681_ = lean_string_append(v___x_680_, v___x_679_);
return v___x_681_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__9(void){
_start:
{
lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; 
v___x_682_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__10));
v___x_683_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__8);
v___x_684_ = lean_string_append(v___x_683_, v___x_682_);
return v___x_684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson(lean_object* v_json_685_){
_start:
{
lean_object* v___x_686_; lean_object* v___x_687_; 
v___x_686_ = ((lean_object*)(l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__0));
lean_inc(v_json_685_);
v___x_687_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__0(v_json_685_, v___x_686_);
if (lean_obj_tag(v___x_687_) == 0)
{
lean_object* v_a_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_697_; 
lean_dec(v_json_685_);
v_a_688_ = lean_ctor_get(v___x_687_, 0);
v_isSharedCheck_697_ = !lean_is_exclusive(v___x_687_);
if (v_isSharedCheck_697_ == 0)
{
v___x_690_ = v___x_687_;
v_isShared_691_ = v_isSharedCheck_697_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_a_688_);
lean_dec(v___x_687_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_697_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_695_; 
v___x_692_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__5, &l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__5);
v___x_693_ = lean_string_append(v___x_692_, v_a_688_);
lean_dec(v_a_688_);
if (v_isShared_691_ == 0)
{
lean_ctor_set(v___x_690_, 0, v___x_693_);
v___x_695_ = v___x_690_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v___x_693_);
v___x_695_ = v_reuseFailAlloc_696_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
return v___x_695_;
}
}
}
else
{
if (lean_obj_tag(v___x_687_) == 0)
{
lean_object* v_a_698_; lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_705_; 
lean_dec(v_json_685_);
v_a_698_ = lean_ctor_get(v___x_687_, 0);
v_isSharedCheck_705_ = !lean_is_exclusive(v___x_687_);
if (v_isSharedCheck_705_ == 0)
{
v___x_700_ = v___x_687_;
v_isShared_701_ = v_isSharedCheck_705_;
goto v_resetjp_699_;
}
else
{
lean_inc(v_a_698_);
lean_dec(v___x_687_);
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_705_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
lean_object* v___x_703_; 
if (v_isShared_701_ == 0)
{
lean_ctor_set_tag(v___x_700_, 0);
v___x_703_ = v___x_700_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v_a_698_);
v___x_703_ = v_reuseFailAlloc_704_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
return v___x_703_;
}
}
}
else
{
lean_object* v_a_706_; lean_object* v___x_707_; lean_object* v___x_708_; 
v_a_706_ = lean_ctor_get(v___x_687_, 0);
lean_inc(v_a_706_);
lean_dec_ref_known(v___x_687_, 1);
v___x_707_ = ((lean_object*)(l_Lean_Lsp_instToJsonDidChangeTextDocumentParams_toJson___closed__0));
v___x_708_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1(v_json_685_, v___x_707_);
if (lean_obj_tag(v___x_708_) == 0)
{
lean_object* v_a_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_718_; 
lean_dec(v_a_706_);
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
v___x_713_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__9, &l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__9);
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
lean_dec(v_a_706_);
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
lean_object* v_a_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_735_; 
v_a_727_ = lean_ctor_get(v___x_708_, 0);
v_isSharedCheck_735_ = !lean_is_exclusive(v___x_708_);
if (v_isSharedCheck_735_ == 0)
{
v___x_729_ = v___x_708_;
v_isShared_730_ = v_isSharedCheck_735_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_a_727_);
lean_dec(v___x_708_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_735_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
lean_object* v___x_731_; lean_object* v___x_733_; 
v___x_731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_731_, 0, v_a_706_);
lean_ctor_set(v___x_731_, 1, v_a_727_);
if (v_isShared_730_ == 0)
{
lean_ctor_set(v___x_729_, 0, v___x_731_);
v___x_733_ = v___x_729_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v___x_731_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDidSaveTextDocumentParams_toJson_spec__0(lean_object* v_k_738_, lean_object* v_x_739_){
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
lean_object* v_val_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_751_; 
v_val_741_ = lean_ctor_get(v_x_739_, 0);
v_isSharedCheck_751_ = !lean_is_exclusive(v_x_739_);
if (v_isSharedCheck_751_ == 0)
{
v___x_743_ = v_x_739_;
v_isShared_744_ = v_isSharedCheck_751_;
goto v_resetjp_742_;
}
else
{
lean_inc(v_val_741_);
lean_dec(v_x_739_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_751_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
lean_object* v___x_746_; 
if (v_isShared_744_ == 0)
{
lean_ctor_set_tag(v___x_743_, 3);
v___x_746_ = v___x_743_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v_val_741_);
v___x_746_ = v_reuseFailAlloc_750_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; 
v___x_747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_747_, 0, v_k_738_);
lean_ctor_set(v___x_747_, 1, v___x_746_);
v___x_748_ = lean_box(0);
v___x_749_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_749_, 0, v___x_747_);
lean_ctor_set(v___x_749_, 1, v___x_748_);
return v___x_749_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDidSaveTextDocumentParams_toJson(lean_object* v_x_752_){
_start:
{
lean_object* v_textDocument_753_; lean_object* v_text_x3f_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_772_; 
v_textDocument_753_ = lean_ctor_get(v_x_752_, 0);
v_text_x3f_754_ = lean_ctor_get(v_x_752_, 1);
v_isSharedCheck_772_ = !lean_is_exclusive(v_x_752_);
if (v_isSharedCheck_772_ == 0)
{
v___x_756_ = v_x_752_;
v_isShared_757_ = v_isSharedCheck_772_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_text_x3f_754_);
lean_inc(v_textDocument_753_);
lean_dec(v_x_752_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_772_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_761_; 
v___x_758_ = ((lean_object*)(l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__0));
v___x_759_ = l_Lean_Lsp_instToJsonTextDocumentIdentifier_toJson(v_textDocument_753_);
if (v_isShared_757_ == 0)
{
lean_ctor_set(v___x_756_, 1, v___x_759_);
lean_ctor_set(v___x_756_, 0, v___x_758_);
v___x_761_ = v___x_756_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v___x_758_);
lean_ctor_set(v_reuseFailAlloc_771_, 1, v___x_759_);
v___x_761_ = v_reuseFailAlloc_771_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; 
v___x_762_ = lean_box(0);
v___x_763_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_763_, 0, v___x_761_);
lean_ctor_set(v___x_763_, 1, v___x_762_);
v___x_764_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0___closed__0));
v___x_765_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDidSaveTextDocumentParams_toJson_spec__0(v___x_764_, v_text_x3f_754_);
v___x_766_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_766_, 0, v___x_765_);
lean_ctor_set(v___x_766_, 1, v___x_762_);
v___x_767_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_767_, 0, v___x_763_);
lean_ctor_set(v___x_767_, 1, v___x_766_);
v___x_768_ = ((lean_object*)(l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__1));
v___x_769_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson_spec__0(v___x_767_, v___x_768_);
v___x_770_ = l_Lean_Json_mkObj(v___x_769_);
lean_dec(v___x_769_);
return v___x_770_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson_spec__0(lean_object* v_j_775_, lean_object* v_k_776_){
_start:
{
lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_777_ = l_Lean_Json_getObjValD(v_j_775_, v_k_776_);
v___x_778_ = l_Lean_Lsp_instFromJsonTextDocumentIdentifier_fromJson(v___x_777_);
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson_spec__0___boxed(lean_object* v_j_779_, lean_object* v_k_780_){
_start:
{
lean_object* v_res_781_; 
v_res_781_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson_spec__0(v_j_779_, v_k_780_);
lean_dec_ref(v_k_780_);
return v_res_781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson_spec__1_spec__1(lean_object* v_x_784_){
_start:
{
if (lean_obj_tag(v_x_784_) == 0)
{
lean_object* v___x_785_; 
v___x_785_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson_spec__1_spec__1___closed__0));
return v___x_785_;
}
else
{
lean_object* v___x_786_; 
v___x_786_ = l_Lean_Json_getStr_x3f(v_x_784_);
if (lean_obj_tag(v___x_786_) == 0)
{
lean_object* v_a_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_794_; 
v_a_787_ = lean_ctor_get(v___x_786_, 0);
v_isSharedCheck_794_ = !lean_is_exclusive(v___x_786_);
if (v_isSharedCheck_794_ == 0)
{
v___x_789_ = v___x_786_;
v_isShared_790_ = v_isSharedCheck_794_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_a_787_);
lean_dec(v___x_786_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_794_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
lean_object* v___x_792_; 
if (v_isShared_790_ == 0)
{
v___x_792_ = v___x_789_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v_a_787_);
v___x_792_ = v_reuseFailAlloc_793_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
return v___x_792_;
}
}
}
else
{
lean_object* v_a_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_803_; 
v_a_795_ = lean_ctor_get(v___x_786_, 0);
v_isSharedCheck_803_ = !lean_is_exclusive(v___x_786_);
if (v_isSharedCheck_803_ == 0)
{
v___x_797_ = v___x_786_;
v_isShared_798_ = v_isSharedCheck_803_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_a_795_);
lean_dec(v___x_786_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_803_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
lean_object* v___x_799_; lean_object* v___x_801_; 
v___x_799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_799_, 0, v_a_795_);
if (v_isShared_798_ == 0)
{
lean_ctor_set(v___x_797_, 0, v___x_799_);
v___x_801_ = v___x_797_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v___x_799_);
v___x_801_ = v_reuseFailAlloc_802_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
return v___x_801_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson_spec__1(lean_object* v_j_804_, lean_object* v_k_805_){
_start:
{
lean_object* v___x_806_; lean_object* v___x_807_; 
v___x_806_ = l_Lean_Json_getObjValD(v_j_804_, v_k_805_);
v___x_807_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson_spec__1_spec__1(v___x_806_);
return v___x_807_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson_spec__1___boxed(lean_object* v_j_808_, lean_object* v_k_809_){
_start:
{
lean_object* v_res_810_; 
v_res_810_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson_spec__1(v_j_808_, v_k_809_);
lean_dec_ref(v_k_809_);
return v_res_810_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__2(void){
_start:
{
uint8_t v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; 
v___x_816_ = 1;
v___x_817_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__1));
v___x_818_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_817_, v___x_816_);
return v___x_818_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__3(void){
_start:
{
lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; 
v___x_819_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__5));
v___x_820_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__2, &l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__2);
v___x_821_ = lean_string_append(v___x_820_, v___x_819_);
return v___x_821_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; 
v___x_822_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__8);
v___x_823_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__3);
v___x_824_ = lean_string_append(v___x_823_, v___x_822_);
return v___x_824_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__5(void){
_start:
{
lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; 
v___x_825_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__10));
v___x_826_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__4);
v___x_827_ = lean_string_append(v___x_826_, v___x_825_);
return v___x_827_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__8(void){
_start:
{
uint8_t v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; 
v___x_831_ = 1;
v___x_832_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__7));
v___x_833_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_832_, v___x_831_);
return v___x_833_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__9(void){
_start:
{
lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; 
v___x_834_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__8);
v___x_835_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__3);
v___x_836_ = lean_string_append(v___x_835_, v___x_834_);
return v___x_836_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__10(void){
_start:
{
lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; 
v___x_837_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__10));
v___x_838_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__9, &l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__9);
v___x_839_ = lean_string_append(v___x_838_, v___x_837_);
return v___x_839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson(lean_object* v_json_840_){
_start:
{
lean_object* v___x_841_; lean_object* v___x_842_; 
v___x_841_ = ((lean_object*)(l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__0));
lean_inc(v_json_840_);
v___x_842_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson_spec__0(v_json_840_, v___x_841_);
if (lean_obj_tag(v___x_842_) == 0)
{
lean_object* v_a_843_; lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_852_; 
lean_dec(v_json_840_);
v_a_843_ = lean_ctor_get(v___x_842_, 0);
v_isSharedCheck_852_ = !lean_is_exclusive(v___x_842_);
if (v_isSharedCheck_852_ == 0)
{
v___x_845_ = v___x_842_;
v_isShared_846_ = v_isSharedCheck_852_;
goto v_resetjp_844_;
}
else
{
lean_inc(v_a_843_);
lean_dec(v___x_842_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_852_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_850_; 
v___x_847_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__5, &l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__5);
v___x_848_ = lean_string_append(v___x_847_, v_a_843_);
lean_dec(v_a_843_);
if (v_isShared_846_ == 0)
{
lean_ctor_set(v___x_845_, 0, v___x_848_);
v___x_850_ = v___x_845_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v___x_848_);
v___x_850_ = v_reuseFailAlloc_851_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
return v___x_850_;
}
}
}
else
{
if (lean_obj_tag(v___x_842_) == 0)
{
lean_object* v_a_853_; lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_860_; 
lean_dec(v_json_840_);
v_a_853_ = lean_ctor_get(v___x_842_, 0);
v_isSharedCheck_860_ = !lean_is_exclusive(v___x_842_);
if (v_isSharedCheck_860_ == 0)
{
v___x_855_ = v___x_842_;
v_isShared_856_ = v_isSharedCheck_860_;
goto v_resetjp_854_;
}
else
{
lean_inc(v_a_853_);
lean_dec(v___x_842_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_860_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
lean_object* v___x_858_; 
if (v_isShared_856_ == 0)
{
lean_ctor_set_tag(v___x_855_, 0);
v___x_858_ = v___x_855_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v_a_853_);
v___x_858_ = v_reuseFailAlloc_859_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
return v___x_858_;
}
}
}
else
{
lean_object* v_a_861_; lean_object* v___x_862_; lean_object* v___x_863_; 
v_a_861_ = lean_ctor_get(v___x_842_, 0);
lean_inc(v_a_861_);
lean_dec_ref_known(v___x_842_, 1);
v___x_862_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0___closed__0));
v___x_863_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson_spec__1(v_json_840_, v___x_862_);
if (lean_obj_tag(v___x_863_) == 0)
{
lean_object* v_a_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_873_; 
lean_dec(v_a_861_);
v_a_864_ = lean_ctor_get(v___x_863_, 0);
v_isSharedCheck_873_ = !lean_is_exclusive(v___x_863_);
if (v_isSharedCheck_873_ == 0)
{
v___x_866_ = v___x_863_;
v_isShared_867_ = v_isSharedCheck_873_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_a_864_);
lean_dec(v___x_863_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_873_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_871_; 
v___x_868_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__10, &l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__10);
v___x_869_ = lean_string_append(v___x_868_, v_a_864_);
lean_dec(v_a_864_);
if (v_isShared_867_ == 0)
{
lean_ctor_set(v___x_866_, 0, v___x_869_);
v___x_871_ = v___x_866_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v___x_869_);
v___x_871_ = v_reuseFailAlloc_872_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
return v___x_871_;
}
}
}
else
{
if (lean_obj_tag(v___x_863_) == 0)
{
lean_object* v_a_874_; lean_object* v___x_876_; uint8_t v_isShared_877_; uint8_t v_isSharedCheck_881_; 
lean_dec(v_a_861_);
v_a_874_ = lean_ctor_get(v___x_863_, 0);
v_isSharedCheck_881_ = !lean_is_exclusive(v___x_863_);
if (v_isSharedCheck_881_ == 0)
{
v___x_876_ = v___x_863_;
v_isShared_877_ = v_isSharedCheck_881_;
goto v_resetjp_875_;
}
else
{
lean_inc(v_a_874_);
lean_dec(v___x_863_);
v___x_876_ = lean_box(0);
v_isShared_877_ = v_isSharedCheck_881_;
goto v_resetjp_875_;
}
v_resetjp_875_:
{
lean_object* v___x_879_; 
if (v_isShared_877_ == 0)
{
lean_ctor_set_tag(v___x_876_, 0);
v___x_879_ = v___x_876_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v_a_874_);
v___x_879_ = v_reuseFailAlloc_880_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
return v___x_879_;
}
}
}
else
{
lean_object* v_a_882_; lean_object* v___x_884_; uint8_t v_isShared_885_; uint8_t v_isSharedCheck_890_; 
v_a_882_ = lean_ctor_get(v___x_863_, 0);
v_isSharedCheck_890_ = !lean_is_exclusive(v___x_863_);
if (v_isSharedCheck_890_ == 0)
{
v___x_884_ = v___x_863_;
v_isShared_885_ = v_isSharedCheck_890_;
goto v_resetjp_883_;
}
else
{
lean_inc(v_a_882_);
lean_dec(v___x_863_);
v___x_884_ = lean_box(0);
v_isShared_885_ = v_isSharedCheck_890_;
goto v_resetjp_883_;
}
v_resetjp_883_:
{
lean_object* v___x_886_; lean_object* v___x_888_; 
v___x_886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_886_, 0, v_a_861_);
lean_ctor_set(v___x_886_, 1, v_a_882_);
if (v_isShared_885_ == 0)
{
lean_ctor_set(v___x_884_, 0, v___x_886_);
v___x_888_ = v___x_884_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v___x_886_);
v___x_888_ = v_reuseFailAlloc_889_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
return v___x_888_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonSaveOptions_toJson(uint8_t v_x_894_){
_start:
{
lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; 
v___x_895_ = ((lean_object*)(l_Lean_Lsp_instToJsonSaveOptions_toJson___closed__0));
v___x_896_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_896_, 0, v_x_894_);
v___x_897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_897_, 0, v___x_895_);
lean_ctor_set(v___x_897_, 1, v___x_896_);
v___x_898_ = lean_box(0);
v___x_899_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_899_, 0, v___x_897_);
lean_ctor_set(v___x_899_, 1, v___x_898_);
v___x_900_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_900_, 0, v___x_899_);
lean_ctor_set(v___x_900_, 1, v___x_898_);
v___x_901_ = ((lean_object*)(l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__1));
v___x_902_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson_spec__0(v___x_900_, v___x_901_);
v___x_903_ = l_Lean_Json_mkObj(v___x_902_);
lean_dec(v___x_902_);
return v___x_903_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonSaveOptions_toJson___boxed(lean_object* v_x_904_){
_start:
{
uint8_t v_x_29__boxed_905_; lean_object* v_res_906_; 
v_x_29__boxed_905_ = lean_unbox(v_x_904_);
v_res_906_ = l_Lean_Lsp_instToJsonSaveOptions_toJson(v_x_29__boxed_905_);
return v_res_906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonSaveOptions_fromJson_spec__0(lean_object* v_j_909_, lean_object* v_k_910_){
_start:
{
lean_object* v___x_911_; lean_object* v___x_912_; 
v___x_911_ = l_Lean_Json_getObjValD(v_j_909_, v_k_910_);
v___x_912_ = l_Lean_Json_getBool_x3f(v___x_911_);
lean_dec(v___x_911_);
return v___x_912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonSaveOptions_fromJson_spec__0___boxed(lean_object* v_j_913_, lean_object* v_k_914_){
_start:
{
lean_object* v_res_915_; 
v_res_915_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonSaveOptions_fromJson_spec__0(v_j_913_, v_k_914_);
lean_dec_ref(v_k_914_);
return v_res_915_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__2(void){
_start:
{
uint8_t v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; 
v___x_921_ = 1;
v___x_922_ = ((lean_object*)(l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__1));
v___x_923_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_922_, v___x_921_);
return v___x_923_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__3(void){
_start:
{
lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; 
v___x_924_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__5));
v___x_925_ = lean_obj_once(&l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__2, &l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__2);
v___x_926_ = lean_string_append(v___x_925_, v___x_924_);
return v___x_926_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__5(void){
_start:
{
uint8_t v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; 
v___x_929_ = 1;
v___x_930_ = ((lean_object*)(l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__4));
v___x_931_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_930_, v___x_929_);
return v___x_931_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__6(void){
_start:
{
lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; 
v___x_932_ = lean_obj_once(&l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__5, &l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__5);
v___x_933_ = lean_obj_once(&l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__3, &l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__3);
v___x_934_ = lean_string_append(v___x_933_, v___x_932_);
return v___x_934_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__7(void){
_start:
{
lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; 
v___x_935_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__10));
v___x_936_ = lean_obj_once(&l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__6, &l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__6);
v___x_937_ = lean_string_append(v___x_936_, v___x_935_);
return v___x_937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonSaveOptions_fromJson(lean_object* v_json_938_){
_start:
{
lean_object* v___x_939_; lean_object* v___x_940_; 
v___x_939_ = ((lean_object*)(l_Lean_Lsp_instToJsonSaveOptions_toJson___closed__0));
v___x_940_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonSaveOptions_fromJson_spec__0(v_json_938_, v___x_939_);
if (lean_obj_tag(v___x_940_) == 0)
{
lean_object* v_a_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_950_; 
v_a_941_ = lean_ctor_get(v___x_940_, 0);
v_isSharedCheck_950_ = !lean_is_exclusive(v___x_940_);
if (v_isSharedCheck_950_ == 0)
{
v___x_943_ = v___x_940_;
v_isShared_944_ = v_isSharedCheck_950_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_a_941_);
lean_dec(v___x_940_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_950_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_948_; 
v___x_945_ = lean_obj_once(&l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__7, &l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__7);
v___x_946_ = lean_string_append(v___x_945_, v_a_941_);
lean_dec(v_a_941_);
if (v_isShared_944_ == 0)
{
lean_ctor_set(v___x_943_, 0, v___x_946_);
v___x_948_ = v___x_943_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v___x_946_);
v___x_948_ = v_reuseFailAlloc_949_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
return v___x_948_;
}
}
}
else
{
if (lean_obj_tag(v___x_940_) == 0)
{
lean_object* v_a_951_; lean_object* v___x_953_; uint8_t v_isShared_954_; uint8_t v_isSharedCheck_958_; 
v_a_951_ = lean_ctor_get(v___x_940_, 0);
v_isSharedCheck_958_ = !lean_is_exclusive(v___x_940_);
if (v_isSharedCheck_958_ == 0)
{
v___x_953_ = v___x_940_;
v_isShared_954_ = v_isSharedCheck_958_;
goto v_resetjp_952_;
}
else
{
lean_inc(v_a_951_);
lean_dec(v___x_940_);
v___x_953_ = lean_box(0);
v_isShared_954_ = v_isSharedCheck_958_;
goto v_resetjp_952_;
}
v_resetjp_952_:
{
lean_object* v___x_956_; 
if (v_isShared_954_ == 0)
{
lean_ctor_set_tag(v___x_953_, 0);
v___x_956_ = v___x_953_;
goto v_reusejp_955_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v_a_951_);
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
lean_object* v_a_959_; lean_object* v___x_961_; uint8_t v_isShared_962_; uint8_t v_isSharedCheck_966_; 
v_a_959_ = lean_ctor_get(v___x_940_, 0);
v_isSharedCheck_966_ = !lean_is_exclusive(v___x_940_);
if (v_isSharedCheck_966_ == 0)
{
v___x_961_ = v___x_940_;
v_isShared_962_ = v_isSharedCheck_966_;
goto v_resetjp_960_;
}
else
{
lean_inc(v_a_959_);
lean_dec(v___x_940_);
v___x_961_ = lean_box(0);
v_isShared_962_ = v_isSharedCheck_966_;
goto v_resetjp_960_;
}
v_resetjp_960_:
{
lean_object* v___x_964_; 
if (v_isShared_962_ == 0)
{
v___x_964_ = v___x_961_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(1, 1, 0);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDidCloseTextDocumentParams_toJson(lean_object* v_x_969_){
_start:
{
lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; 
v___x_970_ = ((lean_object*)(l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__0));
v___x_971_ = l_Lean_Lsp_instToJsonTextDocumentIdentifier_toJson(v_x_969_);
v___x_972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_972_, 0, v___x_970_);
lean_ctor_set(v___x_972_, 1, v___x_971_);
v___x_973_ = lean_box(0);
v___x_974_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_974_, 0, v___x_972_);
lean_ctor_set(v___x_974_, 1, v___x_973_);
v___x_975_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_975_, 0, v___x_974_);
lean_ctor_set(v___x_975_, 1, v___x_973_);
v___x_976_ = ((lean_object*)(l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__1));
v___x_977_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson_spec__0(v___x_975_, v___x_976_);
v___x_978_ = l_Lean_Json_mkObj(v___x_977_);
lean_dec(v___x_977_);
return v___x_978_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__2(void){
_start:
{
uint8_t v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; 
v___x_986_ = 1;
v___x_987_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__1));
v___x_988_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_987_, v___x_986_);
return v___x_988_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__3(void){
_start:
{
lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; 
v___x_989_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__5));
v___x_990_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__2, &l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__2);
v___x_991_ = lean_string_append(v___x_990_, v___x_989_);
return v___x_991_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; 
v___x_992_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__8);
v___x_993_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__3);
v___x_994_ = lean_string_append(v___x_993_, v___x_992_);
return v___x_994_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__5(void){
_start:
{
lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; 
v___x_995_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__10));
v___x_996_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__4);
v___x_997_ = lean_string_append(v___x_996_, v___x_995_);
return v___x_997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson(lean_object* v_json_998_){
_start:
{
lean_object* v___x_999_; lean_object* v___x_1000_; 
v___x_999_ = ((lean_object*)(l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__0));
v___x_1000_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson_spec__0(v_json_998_, v___x_999_);
if (lean_obj_tag(v___x_1000_) == 0)
{
lean_object* v_a_1001_; lean_object* v___x_1003_; uint8_t v_isShared_1004_; uint8_t v_isSharedCheck_1010_; 
v_a_1001_ = lean_ctor_get(v___x_1000_, 0);
v_isSharedCheck_1010_ = !lean_is_exclusive(v___x_1000_);
if (v_isSharedCheck_1010_ == 0)
{
v___x_1003_ = v___x_1000_;
v_isShared_1004_ = v_isSharedCheck_1010_;
goto v_resetjp_1002_;
}
else
{
lean_inc(v_a_1001_);
lean_dec(v___x_1000_);
v___x_1003_ = lean_box(0);
v_isShared_1004_ = v_isSharedCheck_1010_;
goto v_resetjp_1002_;
}
v_resetjp_1002_:
{
lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1008_; 
v___x_1005_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__5, &l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__5);
v___x_1006_ = lean_string_append(v___x_1005_, v_a_1001_);
lean_dec(v_a_1001_);
if (v_isShared_1004_ == 0)
{
lean_ctor_set(v___x_1003_, 0, v___x_1006_);
v___x_1008_ = v___x_1003_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v___x_1006_);
v___x_1008_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
return v___x_1008_;
}
}
}
else
{
if (lean_obj_tag(v___x_1000_) == 0)
{
lean_object* v_a_1011_; lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1018_; 
v_a_1011_ = lean_ctor_get(v___x_1000_, 0);
v_isSharedCheck_1018_ = !lean_is_exclusive(v___x_1000_);
if (v_isSharedCheck_1018_ == 0)
{
v___x_1013_ = v___x_1000_;
v_isShared_1014_ = v_isSharedCheck_1018_;
goto v_resetjp_1012_;
}
else
{
lean_inc(v_a_1011_);
lean_dec(v___x_1000_);
v___x_1013_ = lean_box(0);
v_isShared_1014_ = v_isSharedCheck_1018_;
goto v_resetjp_1012_;
}
v_resetjp_1012_:
{
lean_object* v___x_1016_; 
if (v_isShared_1014_ == 0)
{
lean_ctor_set_tag(v___x_1013_, 0);
v___x_1016_ = v___x_1013_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v_a_1011_);
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
lean_object* v_a_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1026_; 
v_a_1019_ = lean_ctor_get(v___x_1000_, 0);
v_isSharedCheck_1026_ = !lean_is_exclusive(v___x_1000_);
if (v_isSharedCheck_1026_ == 0)
{
v___x_1021_ = v___x_1000_;
v_isShared_1022_ = v_isSharedCheck_1026_;
goto v_resetjp_1020_;
}
else
{
lean_inc(v_a_1019_);
lean_dec(v___x_1000_);
v___x_1021_ = lean_box(0);
v_isShared_1022_ = v_isSharedCheck_1026_;
goto v_resetjp_1020_;
}
v_resetjp_1020_:
{
lean_object* v___x_1024_; 
if (v_isShared_1022_ == 0)
{
v___x_1024_ = v___x_1021_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(1, 1, 0);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson_spec__0(lean_object* v_k_1029_, lean_object* v_x_1030_){
_start:
{
if (lean_obj_tag(v_x_1030_) == 0)
{
lean_object* v___x_1031_; 
lean_dec_ref(v_k_1029_);
v___x_1031_ = lean_box(0);
return v___x_1031_;
}
else
{
lean_object* v_val_1032_; uint8_t v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; 
v_val_1032_ = lean_ctor_get(v_x_1030_, 0);
v___x_1033_ = lean_unbox(v_val_1032_);
v___x_1034_ = l_Lean_Lsp_instToJsonSaveOptions_toJson(v___x_1033_);
v___x_1035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1035_, 0, v_k_1029_);
lean_ctor_set(v___x_1035_, 1, v___x_1034_);
v___x_1036_ = lean_box(0);
v___x_1037_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1037_, 0, v___x_1035_);
lean_ctor_set(v___x_1037_, 1, v___x_1036_);
return v___x_1037_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson_spec__0___boxed(lean_object* v_k_1038_, lean_object* v_x_1039_){
_start:
{
lean_object* v_res_1040_; 
v_res_1040_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson_spec__0(v_k_1038_, v_x_1039_);
lean_dec(v_x_1039_);
return v_res_1040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson(lean_object* v_x_1046_){
_start:
{
uint8_t v_openClose_1047_; uint8_t v_change_1048_; uint8_t v_willSave_1049_; uint8_t v_willSaveWaitUntil_1050_; lean_object* v_save_x3f_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___y_1059_; 
v_openClose_1047_ = lean_ctor_get_uint8(v_x_1046_, sizeof(void*)*1);
v_change_1048_ = lean_ctor_get_uint8(v_x_1046_, sizeof(void*)*1 + 1);
v_willSave_1049_ = lean_ctor_get_uint8(v_x_1046_, sizeof(void*)*1 + 2);
v_willSaveWaitUntil_1050_ = lean_ctor_get_uint8(v_x_1046_, sizeof(void*)*1 + 3);
v_save_x3f_1051_ = lean_ctor_get(v_x_1046_, 0);
v___x_1052_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__0));
v___x_1053_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1053_, 0, v_openClose_1047_);
v___x_1054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1052_);
lean_ctor_set(v___x_1054_, 1, v___x_1053_);
v___x_1055_ = lean_box(0);
v___x_1056_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1056_, 0, v___x_1054_);
lean_ctor_set(v___x_1056_, 1, v___x_1055_);
v___x_1057_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__1));
switch(v_change_1048_)
{
case 0:
{
lean_object* v___x_1080_; 
v___x_1080_ = lean_obj_once(&l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__1, &l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__1_once, _init_l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__1);
v___y_1059_ = v___x_1080_;
goto v___jp_1058_;
}
case 1:
{
lean_object* v___x_1081_; 
v___x_1081_ = lean_obj_once(&l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__3, &l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__3_once, _init_l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__3);
v___y_1059_ = v___x_1081_;
goto v___jp_1058_;
}
default: 
{
lean_object* v___x_1082_; 
v___x_1082_ = lean_obj_once(&l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__5, &l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__5_once, _init_l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__5);
v___y_1059_ = v___x_1082_;
goto v___jp_1058_;
}
}
v___jp_1058_:
{
lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; 
lean_inc(v___y_1059_);
v___x_1060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1060_, 0, v___x_1057_);
lean_ctor_set(v___x_1060_, 1, v___y_1059_);
v___x_1061_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1061_, 0, v___x_1060_);
lean_ctor_set(v___x_1061_, 1, v___x_1055_);
v___x_1062_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__2));
v___x_1063_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1063_, 0, v_willSave_1049_);
v___x_1064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1064_, 0, v___x_1062_);
lean_ctor_set(v___x_1064_, 1, v___x_1063_);
v___x_1065_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1065_, 0, v___x_1064_);
lean_ctor_set(v___x_1065_, 1, v___x_1055_);
v___x_1066_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__3));
v___x_1067_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1067_, 0, v_willSaveWaitUntil_1050_);
v___x_1068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1068_, 0, v___x_1066_);
lean_ctor_set(v___x_1068_, 1, v___x_1067_);
v___x_1069_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1069_, 0, v___x_1068_);
lean_ctor_set(v___x_1069_, 1, v___x_1055_);
v___x_1070_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__4));
v___x_1071_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson_spec__0(v___x_1070_, v_save_x3f_1051_);
v___x_1072_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1072_, 0, v___x_1071_);
lean_ctor_set(v___x_1072_, 1, v___x_1055_);
v___x_1073_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1073_, 0, v___x_1069_);
lean_ctor_set(v___x_1073_, 1, v___x_1072_);
v___x_1074_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1074_, 0, v___x_1065_);
lean_ctor_set(v___x_1074_, 1, v___x_1073_);
v___x_1075_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1075_, 0, v___x_1061_);
lean_ctor_set(v___x_1075_, 1, v___x_1074_);
v___x_1076_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1076_, 0, v___x_1056_);
lean_ctor_set(v___x_1076_, 1, v___x_1075_);
v___x_1077_ = ((lean_object*)(l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__1));
v___x_1078_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson_spec__0(v___x_1076_, v___x_1077_);
v___x_1079_ = l_Lean_Json_mkObj(v___x_1078_);
lean_dec(v___x_1078_);
return v___x_1079_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___boxed(lean_object* v_x_1083_){
_start:
{
lean_object* v_res_1084_; 
v_res_1084_ = l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson(v_x_1083_);
lean_dec_ref(v_x_1083_);
return v_res_1084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson_spec__0_spec__0(lean_object* v_x_1089_){
_start:
{
if (lean_obj_tag(v_x_1089_) == 0)
{
lean_object* v___x_1090_; 
v___x_1090_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson_spec__0_spec__0___closed__0));
return v___x_1090_;
}
else
{
lean_object* v___x_1091_; 
v___x_1091_ = l_Lean_Lsp_instFromJsonSaveOptions_fromJson(v_x_1089_);
if (lean_obj_tag(v___x_1091_) == 0)
{
lean_object* v_a_1092_; lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1099_; 
v_a_1092_ = lean_ctor_get(v___x_1091_, 0);
v_isSharedCheck_1099_ = !lean_is_exclusive(v___x_1091_);
if (v_isSharedCheck_1099_ == 0)
{
v___x_1094_ = v___x_1091_;
v_isShared_1095_ = v_isSharedCheck_1099_;
goto v_resetjp_1093_;
}
else
{
lean_inc(v_a_1092_);
lean_dec(v___x_1091_);
v___x_1094_ = lean_box(0);
v_isShared_1095_ = v_isSharedCheck_1099_;
goto v_resetjp_1093_;
}
v_resetjp_1093_:
{
lean_object* v___x_1097_; 
if (v_isShared_1095_ == 0)
{
v___x_1097_ = v___x_1094_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v_a_1092_);
v___x_1097_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
return v___x_1097_;
}
}
}
else
{
lean_object* v_a_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1108_; 
v_a_1100_ = lean_ctor_get(v___x_1091_, 0);
v_isSharedCheck_1108_ = !lean_is_exclusive(v___x_1091_);
if (v_isSharedCheck_1108_ == 0)
{
v___x_1102_ = v___x_1091_;
v_isShared_1103_ = v_isSharedCheck_1108_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_a_1100_);
lean_dec(v___x_1091_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1108_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v___x_1104_; lean_object* v___x_1106_; 
v___x_1104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1104_, 0, v_a_1100_);
if (v_isShared_1103_ == 0)
{
lean_ctor_set(v___x_1102_, 0, v___x_1104_);
v___x_1106_ = v___x_1102_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v___x_1104_);
v___x_1106_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
return v___x_1106_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson_spec__0(lean_object* v_j_1109_, lean_object* v_k_1110_){
_start:
{
lean_object* v___x_1111_; lean_object* v___x_1112_; 
v___x_1111_ = l_Lean_Json_getObjValD(v_j_1109_, v_k_1110_);
v___x_1112_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson_spec__0_spec__0(v___x_1111_);
return v___x_1112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson_spec__0___boxed(lean_object* v_j_1113_, lean_object* v_k_1114_){
_start:
{
lean_object* v_res_1115_; 
v_res_1115_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson_spec__0(v_j_1113_, v_k_1114_);
lean_dec_ref(v_k_1114_);
return v_res_1115_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__2(void){
_start:
{
uint8_t v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; 
v___x_1121_ = 1;
v___x_1122_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__1));
v___x_1123_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1122_, v___x_1121_);
return v___x_1123_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3(void){
_start:
{
lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; 
v___x_1124_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__5));
v___x_1125_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__2, &l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__2);
v___x_1126_ = lean_string_append(v___x_1125_, v___x_1124_);
return v___x_1126_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__5(void){
_start:
{
uint8_t v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; 
v___x_1129_ = 1;
v___x_1130_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__4));
v___x_1131_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1130_, v___x_1129_);
return v___x_1131_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__6(void){
_start:
{
lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; 
v___x_1132_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__5, &l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__5);
v___x_1133_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3, &l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3);
v___x_1134_ = lean_string_append(v___x_1133_, v___x_1132_);
return v___x_1134_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__7(void){
_start:
{
lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; 
v___x_1135_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__10));
v___x_1136_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__6, &l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__6);
v___x_1137_ = lean_string_append(v___x_1136_, v___x_1135_);
return v___x_1137_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__9(void){
_start:
{
uint8_t v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; 
v___x_1140_ = 1;
v___x_1141_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__8));
v___x_1142_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1141_, v___x_1140_);
return v___x_1142_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__10(void){
_start:
{
lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; 
v___x_1143_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__9, &l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__9);
v___x_1144_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3, &l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3);
v___x_1145_ = lean_string_append(v___x_1144_, v___x_1143_);
return v___x_1145_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__11(void){
_start:
{
lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; 
v___x_1146_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__10));
v___x_1147_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__10, &l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__10);
v___x_1148_ = lean_string_append(v___x_1147_, v___x_1146_);
return v___x_1148_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__13(void){
_start:
{
uint8_t v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; 
v___x_1151_ = 1;
v___x_1152_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__12));
v___x_1153_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1152_, v___x_1151_);
return v___x_1153_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__14(void){
_start:
{
lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; 
v___x_1154_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__13, &l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__13);
v___x_1155_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3, &l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3);
v___x_1156_ = lean_string_append(v___x_1155_, v___x_1154_);
return v___x_1156_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__15(void){
_start:
{
lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; 
v___x_1157_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__10));
v___x_1158_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__14, &l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__14_once, _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__14);
v___x_1159_ = lean_string_append(v___x_1158_, v___x_1157_);
return v___x_1159_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__17(void){
_start:
{
uint8_t v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; 
v___x_1162_ = 1;
v___x_1163_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__16));
v___x_1164_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1163_, v___x_1162_);
return v___x_1164_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__18(void){
_start:
{
lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; 
v___x_1165_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__17, &l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__17_once, _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__17);
v___x_1166_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3, &l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3);
v___x_1167_ = lean_string_append(v___x_1166_, v___x_1165_);
return v___x_1167_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__19(void){
_start:
{
lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; 
v___x_1168_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__10));
v___x_1169_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__18, &l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__18_once, _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__18);
v___x_1170_ = lean_string_append(v___x_1169_, v___x_1168_);
return v___x_1170_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__22(void){
_start:
{
uint8_t v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; 
v___x_1174_ = 1;
v___x_1175_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__21));
v___x_1176_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1175_, v___x_1174_);
return v___x_1176_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__23(void){
_start:
{
lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; 
v___x_1177_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__22, &l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__22_once, _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__22);
v___x_1178_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3, &l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3);
v___x_1179_ = lean_string_append(v___x_1178_, v___x_1177_);
return v___x_1179_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__24(void){
_start:
{
lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; 
v___x_1180_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__10));
v___x_1181_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__23, &l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__23_once, _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__23);
v___x_1182_ = lean_string_append(v___x_1181_, v___x_1180_);
return v___x_1182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson(lean_object* v_json_1183_){
_start:
{
lean_object* v___x_1184_; lean_object* v___x_1185_; 
v___x_1184_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__0));
lean_inc(v_json_1183_);
v___x_1185_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonSaveOptions_fromJson_spec__0(v_json_1183_, v___x_1184_);
if (lean_obj_tag(v___x_1185_) == 0)
{
lean_object* v_a_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1195_; 
lean_dec(v_json_1183_);
v_a_1186_ = lean_ctor_get(v___x_1185_, 0);
v_isSharedCheck_1195_ = !lean_is_exclusive(v___x_1185_);
if (v_isSharedCheck_1195_ == 0)
{
v___x_1188_ = v___x_1185_;
v_isShared_1189_ = v_isSharedCheck_1195_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_a_1186_);
lean_dec(v___x_1185_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1195_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1193_; 
v___x_1190_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__7, &l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__7);
v___x_1191_ = lean_string_append(v___x_1190_, v_a_1186_);
lean_dec(v_a_1186_);
if (v_isShared_1189_ == 0)
{
lean_ctor_set(v___x_1188_, 0, v___x_1191_);
v___x_1193_ = v___x_1188_;
goto v_reusejp_1192_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v___x_1191_);
v___x_1193_ = v_reuseFailAlloc_1194_;
goto v_reusejp_1192_;
}
v_reusejp_1192_:
{
return v___x_1193_;
}
}
}
else
{
if (lean_obj_tag(v___x_1185_) == 0)
{
lean_object* v_a_1196_; lean_object* v___x_1198_; uint8_t v_isShared_1199_; uint8_t v_isSharedCheck_1203_; 
lean_dec(v_json_1183_);
v_a_1196_ = lean_ctor_get(v___x_1185_, 0);
v_isSharedCheck_1203_ = !lean_is_exclusive(v___x_1185_);
if (v_isSharedCheck_1203_ == 0)
{
v___x_1198_ = v___x_1185_;
v_isShared_1199_ = v_isSharedCheck_1203_;
goto v_resetjp_1197_;
}
else
{
lean_inc(v_a_1196_);
lean_dec(v___x_1185_);
v___x_1198_ = lean_box(0);
v_isShared_1199_ = v_isSharedCheck_1203_;
goto v_resetjp_1197_;
}
v_resetjp_1197_:
{
lean_object* v___x_1201_; 
if (v_isShared_1199_ == 0)
{
lean_ctor_set_tag(v___x_1198_, 0);
v___x_1201_ = v___x_1198_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v_a_1196_);
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
lean_object* v_a_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; 
v_a_1204_ = lean_ctor_get(v___x_1185_, 0);
lean_inc(v_a_1204_);
lean_dec_ref_known(v___x_1185_, 1);
v___x_1205_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__1));
lean_inc(v_json_1183_);
v___x_1206_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__1(v_json_1183_, v___x_1205_);
if (lean_obj_tag(v___x_1206_) == 0)
{
lean_object* v_a_1207_; lean_object* v___x_1209_; uint8_t v_isShared_1210_; uint8_t v_isSharedCheck_1216_; 
lean_dec(v_a_1204_);
lean_dec(v_json_1183_);
v_a_1207_ = lean_ctor_get(v___x_1206_, 0);
v_isSharedCheck_1216_ = !lean_is_exclusive(v___x_1206_);
if (v_isSharedCheck_1216_ == 0)
{
v___x_1209_ = v___x_1206_;
v_isShared_1210_ = v_isSharedCheck_1216_;
goto v_resetjp_1208_;
}
else
{
lean_inc(v_a_1207_);
lean_dec(v___x_1206_);
v___x_1209_ = lean_box(0);
v_isShared_1210_ = v_isSharedCheck_1216_;
goto v_resetjp_1208_;
}
v_resetjp_1208_:
{
lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1214_; 
v___x_1211_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__11, &l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__11);
v___x_1212_ = lean_string_append(v___x_1211_, v_a_1207_);
lean_dec(v_a_1207_);
if (v_isShared_1210_ == 0)
{
lean_ctor_set(v___x_1209_, 0, v___x_1212_);
v___x_1214_ = v___x_1209_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v___x_1212_);
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
if (lean_obj_tag(v___x_1206_) == 0)
{
lean_object* v_a_1217_; lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1224_; 
lean_dec(v_a_1204_);
lean_dec(v_json_1183_);
v_a_1217_ = lean_ctor_get(v___x_1206_, 0);
v_isSharedCheck_1224_ = !lean_is_exclusive(v___x_1206_);
if (v_isSharedCheck_1224_ == 0)
{
v___x_1219_ = v___x_1206_;
v_isShared_1220_ = v_isSharedCheck_1224_;
goto v_resetjp_1218_;
}
else
{
lean_inc(v_a_1217_);
lean_dec(v___x_1206_);
v___x_1219_ = lean_box(0);
v_isShared_1220_ = v_isSharedCheck_1224_;
goto v_resetjp_1218_;
}
v_resetjp_1218_:
{
lean_object* v___x_1222_; 
if (v_isShared_1220_ == 0)
{
lean_ctor_set_tag(v___x_1219_, 0);
v___x_1222_ = v___x_1219_;
goto v_reusejp_1221_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v_a_1217_);
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
lean_object* v_a_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; 
v_a_1225_ = lean_ctor_get(v___x_1206_, 0);
lean_inc(v_a_1225_);
lean_dec_ref_known(v___x_1206_, 1);
v___x_1226_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__2));
lean_inc(v_json_1183_);
v___x_1227_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonSaveOptions_fromJson_spec__0(v_json_1183_, v___x_1226_);
if (lean_obj_tag(v___x_1227_) == 0)
{
lean_object* v_a_1228_; lean_object* v___x_1230_; uint8_t v_isShared_1231_; uint8_t v_isSharedCheck_1237_; 
lean_dec(v_a_1225_);
lean_dec(v_a_1204_);
lean_dec(v_json_1183_);
v_a_1228_ = lean_ctor_get(v___x_1227_, 0);
v_isSharedCheck_1237_ = !lean_is_exclusive(v___x_1227_);
if (v_isSharedCheck_1237_ == 0)
{
v___x_1230_ = v___x_1227_;
v_isShared_1231_ = v_isSharedCheck_1237_;
goto v_resetjp_1229_;
}
else
{
lean_inc(v_a_1228_);
lean_dec(v___x_1227_);
v___x_1230_ = lean_box(0);
v_isShared_1231_ = v_isSharedCheck_1237_;
goto v_resetjp_1229_;
}
v_resetjp_1229_:
{
lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1235_; 
v___x_1232_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__15, &l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__15_once, _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__15);
v___x_1233_ = lean_string_append(v___x_1232_, v_a_1228_);
lean_dec(v_a_1228_);
if (v_isShared_1231_ == 0)
{
lean_ctor_set(v___x_1230_, 0, v___x_1233_);
v___x_1235_ = v___x_1230_;
goto v_reusejp_1234_;
}
else
{
lean_object* v_reuseFailAlloc_1236_; 
v_reuseFailAlloc_1236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1236_, 0, v___x_1233_);
v___x_1235_ = v_reuseFailAlloc_1236_;
goto v_reusejp_1234_;
}
v_reusejp_1234_:
{
return v___x_1235_;
}
}
}
else
{
if (lean_obj_tag(v___x_1227_) == 0)
{
lean_object* v_a_1238_; lean_object* v___x_1240_; uint8_t v_isShared_1241_; uint8_t v_isSharedCheck_1245_; 
lean_dec(v_a_1225_);
lean_dec(v_a_1204_);
lean_dec(v_json_1183_);
v_a_1238_ = lean_ctor_get(v___x_1227_, 0);
v_isSharedCheck_1245_ = !lean_is_exclusive(v___x_1227_);
if (v_isSharedCheck_1245_ == 0)
{
v___x_1240_ = v___x_1227_;
v_isShared_1241_ = v_isSharedCheck_1245_;
goto v_resetjp_1239_;
}
else
{
lean_inc(v_a_1238_);
lean_dec(v___x_1227_);
v___x_1240_ = lean_box(0);
v_isShared_1241_ = v_isSharedCheck_1245_;
goto v_resetjp_1239_;
}
v_resetjp_1239_:
{
lean_object* v___x_1243_; 
if (v_isShared_1241_ == 0)
{
lean_ctor_set_tag(v___x_1240_, 0);
v___x_1243_ = v___x_1240_;
goto v_reusejp_1242_;
}
else
{
lean_object* v_reuseFailAlloc_1244_; 
v_reuseFailAlloc_1244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1244_, 0, v_a_1238_);
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
lean_object* v_a_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; 
v_a_1246_ = lean_ctor_get(v___x_1227_, 0);
lean_inc(v_a_1246_);
lean_dec_ref_known(v___x_1227_, 1);
v___x_1247_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__3));
lean_inc(v_json_1183_);
v___x_1248_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonSaveOptions_fromJson_spec__0(v_json_1183_, v___x_1247_);
if (lean_obj_tag(v___x_1248_) == 0)
{
lean_object* v_a_1249_; lean_object* v___x_1251_; uint8_t v_isShared_1252_; uint8_t v_isSharedCheck_1258_; 
lean_dec(v_a_1246_);
lean_dec(v_a_1225_);
lean_dec(v_a_1204_);
lean_dec(v_json_1183_);
v_a_1249_ = lean_ctor_get(v___x_1248_, 0);
v_isSharedCheck_1258_ = !lean_is_exclusive(v___x_1248_);
if (v_isSharedCheck_1258_ == 0)
{
v___x_1251_ = v___x_1248_;
v_isShared_1252_ = v_isSharedCheck_1258_;
goto v_resetjp_1250_;
}
else
{
lean_inc(v_a_1249_);
lean_dec(v___x_1248_);
v___x_1251_ = lean_box(0);
v_isShared_1252_ = v_isSharedCheck_1258_;
goto v_resetjp_1250_;
}
v_resetjp_1250_:
{
lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1256_; 
v___x_1253_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__19, &l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__19_once, _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__19);
v___x_1254_ = lean_string_append(v___x_1253_, v_a_1249_);
lean_dec(v_a_1249_);
if (v_isShared_1252_ == 0)
{
lean_ctor_set(v___x_1251_, 0, v___x_1254_);
v___x_1256_ = v___x_1251_;
goto v_reusejp_1255_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v___x_1254_);
v___x_1256_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1255_;
}
v_reusejp_1255_:
{
return v___x_1256_;
}
}
}
else
{
if (lean_obj_tag(v___x_1248_) == 0)
{
lean_object* v_a_1259_; lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1266_; 
lean_dec(v_a_1246_);
lean_dec(v_a_1225_);
lean_dec(v_a_1204_);
lean_dec(v_json_1183_);
v_a_1259_ = lean_ctor_get(v___x_1248_, 0);
v_isSharedCheck_1266_ = !lean_is_exclusive(v___x_1248_);
if (v_isSharedCheck_1266_ == 0)
{
v___x_1261_ = v___x_1248_;
v_isShared_1262_ = v_isSharedCheck_1266_;
goto v_resetjp_1260_;
}
else
{
lean_inc(v_a_1259_);
lean_dec(v___x_1248_);
v___x_1261_ = lean_box(0);
v_isShared_1262_ = v_isSharedCheck_1266_;
goto v_resetjp_1260_;
}
v_resetjp_1260_:
{
lean_object* v___x_1264_; 
if (v_isShared_1262_ == 0)
{
lean_ctor_set_tag(v___x_1261_, 0);
v___x_1264_ = v___x_1261_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v_a_1259_);
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
lean_object* v_a_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; 
v_a_1267_ = lean_ctor_get(v___x_1248_, 0);
lean_inc(v_a_1267_);
lean_dec_ref_known(v___x_1248_, 1);
v___x_1268_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__4));
v___x_1269_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson_spec__0(v_json_1183_, v___x_1268_);
if (lean_obj_tag(v___x_1269_) == 0)
{
lean_object* v_a_1270_; lean_object* v___x_1272_; uint8_t v_isShared_1273_; uint8_t v_isSharedCheck_1279_; 
lean_dec(v_a_1267_);
lean_dec(v_a_1246_);
lean_dec(v_a_1225_);
lean_dec(v_a_1204_);
v_a_1270_ = lean_ctor_get(v___x_1269_, 0);
v_isSharedCheck_1279_ = !lean_is_exclusive(v___x_1269_);
if (v_isSharedCheck_1279_ == 0)
{
v___x_1272_ = v___x_1269_;
v_isShared_1273_ = v_isSharedCheck_1279_;
goto v_resetjp_1271_;
}
else
{
lean_inc(v_a_1270_);
lean_dec(v___x_1269_);
v___x_1272_ = lean_box(0);
v_isShared_1273_ = v_isSharedCheck_1279_;
goto v_resetjp_1271_;
}
v_resetjp_1271_:
{
lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1277_; 
v___x_1274_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__24, &l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__24_once, _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__24);
v___x_1275_ = lean_string_append(v___x_1274_, v_a_1270_);
lean_dec(v_a_1270_);
if (v_isShared_1273_ == 0)
{
lean_ctor_set(v___x_1272_, 0, v___x_1275_);
v___x_1277_ = v___x_1272_;
goto v_reusejp_1276_;
}
else
{
lean_object* v_reuseFailAlloc_1278_; 
v_reuseFailAlloc_1278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1278_, 0, v___x_1275_);
v___x_1277_ = v_reuseFailAlloc_1278_;
goto v_reusejp_1276_;
}
v_reusejp_1276_:
{
return v___x_1277_;
}
}
}
else
{
if (lean_obj_tag(v___x_1269_) == 0)
{
lean_object* v_a_1280_; lean_object* v___x_1282_; uint8_t v_isShared_1283_; uint8_t v_isSharedCheck_1287_; 
lean_dec(v_a_1267_);
lean_dec(v_a_1246_);
lean_dec(v_a_1225_);
lean_dec(v_a_1204_);
v_a_1280_ = lean_ctor_get(v___x_1269_, 0);
v_isSharedCheck_1287_ = !lean_is_exclusive(v___x_1269_);
if (v_isSharedCheck_1287_ == 0)
{
v___x_1282_ = v___x_1269_;
v_isShared_1283_ = v_isSharedCheck_1287_;
goto v_resetjp_1281_;
}
else
{
lean_inc(v_a_1280_);
lean_dec(v___x_1269_);
v___x_1282_ = lean_box(0);
v_isShared_1283_ = v_isSharedCheck_1287_;
goto v_resetjp_1281_;
}
v_resetjp_1281_:
{
lean_object* v___x_1285_; 
if (v_isShared_1283_ == 0)
{
lean_ctor_set_tag(v___x_1282_, 0);
v___x_1285_ = v___x_1282_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v_a_1280_);
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
lean_object* v_a_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1300_; 
v_a_1288_ = lean_ctor_get(v___x_1269_, 0);
v_isSharedCheck_1300_ = !lean_is_exclusive(v___x_1269_);
if (v_isSharedCheck_1300_ == 0)
{
v___x_1290_ = v___x_1269_;
v_isShared_1291_ = v_isSharedCheck_1300_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_a_1288_);
lean_dec(v___x_1269_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1300_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
lean_object* v___x_1292_; uint8_t v___x_1293_; uint8_t v___x_1294_; uint8_t v___x_1295_; uint8_t v___x_1296_; lean_object* v___x_1298_; 
v___x_1292_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v___x_1292_, 0, v_a_1288_);
v___x_1293_ = lean_unbox(v_a_1204_);
lean_dec(v_a_1204_);
lean_ctor_set_uint8(v___x_1292_, sizeof(void*)*1, v___x_1293_);
v___x_1294_ = lean_unbox(v_a_1225_);
lean_dec(v_a_1225_);
lean_ctor_set_uint8(v___x_1292_, sizeof(void*)*1 + 1, v___x_1294_);
v___x_1295_ = lean_unbox(v_a_1246_);
lean_dec(v_a_1246_);
lean_ctor_set_uint8(v___x_1292_, sizeof(void*)*1 + 2, v___x_1295_);
v___x_1296_ = lean_unbox(v_a_1267_);
lean_dec(v_a_1267_);
lean_ctor_set_uint8(v___x_1292_, sizeof(void*)*1 + 3, v___x_1296_);
if (v_isShared_1291_ == 0)
{
lean_ctor_set(v___x_1290_, 0, v___x_1292_);
v___x_1298_ = v___x_1290_;
goto v_reusejp_1297_;
}
else
{
lean_object* v_reuseFailAlloc_1299_; 
v_reuseFailAlloc_1299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1299_, 0, v___x_1292_);
v___x_1298_ = v_reuseFailAlloc_1299_;
goto v_reusejp_1297_;
}
v_reusejp_1297_:
{
return v___x_1298_;
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

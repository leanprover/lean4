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
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
lean_object* l_Lean_Lsp_instFromJsonRange_fromJson(lean_object*);
lean_object* l_Lean_JsonNumber_fromNat(lean_object*);
lean_object* l_Lean_Json_getBool_x3f(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson(lean_object*);
lean_object* l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson(lean_object*);
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
lean_object* l_Lean_Json_getNat_x3f(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Lsp_instFromJsonTextDocumentIdentifier_fromJson(lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Lsp_instFromJsonDocumentFilter_fromJson(lean_object*);
lean_object* l_Lean_Lsp_instToJsonTextDocumentIdentifier_toJson(lean_object*);
lean_object* l_Lean_Lsp_instToJsonTextDocumentItem_toJson(lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentSyncKind_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentSyncKind_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentSyncKind_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentSyncKind_toCtorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0_spec__2_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "expected JSON array, got '"};
static const lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0_spec__2___closed__0 = (const lean_object*)&l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0_spec__2___closed__0_value;
static const lean_string_object l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0_spec__2___closed__1 = (const lean_object*)&l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0_spec__2___closed__1_value;
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0_spec__2(lean_object*);
static const lean_ctor_object l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonDidChangeTextDocumentParams_toJson_spec__0_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonDidChangeTextDocumentParams_toJson_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Lsp_instToJsonDidChangeTextDocumentParams_toJson_spec__0(lean_object*);
static const lean_string_object l_Lean_Lsp_instToJsonDidChangeTextDocumentParams_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "contentChanges"};
static const lean_object* l_Lean_Lsp_instToJsonDidChangeTextDocumentParams_toJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonDidChangeTextDocumentParams_toJson___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDidChangeTextDocumentParams_toJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonDidChangeTextDocumentParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonDidChangeTextDocumentParams_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonDidChangeTextDocumentParams___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonDidChangeTextDocumentParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonDidChangeTextDocumentParams = (const lean_object*)&l_Lean_Lsp_instToJsonDidChangeTextDocumentParams___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1(lean_object*);
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
static const lean_ctor_object l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson_spec__1_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson_spec__1_spec__1___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson_spec__1_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson_spec__1_spec__1(lean_object*);
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
static const lean_ctor_object l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson_spec__0_spec__0___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson_spec__0_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson_spec__0_spec__0(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentSyncKind_toCtorIdx(uint8_t v_x_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = l_Lean_Lsp_TextDocumentSyncKind_ctorIdx(v_x_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentSyncKind_toCtorIdx___boxed(lean_object* v_x_10_){
_start:
{
uint8_t v_x_4__boxed_11_; lean_object* v_res_12_; 
v_x_4__boxed_11_ = lean_unbox(v_x_10_);
v_res_12_ = l_Lean_Lsp_TextDocumentSyncKind_toCtorIdx(v_x_4__boxed_11_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentSyncKind_ctorElim___redArg(lean_object* v_k_13_){
_start:
{
lean_inc(v_k_13_);
return v_k_13_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentSyncKind_ctorElim___redArg___boxed(lean_object* v_k_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = l_Lean_Lsp_TextDocumentSyncKind_ctorElim___redArg(v_k_14_);
lean_dec(v_k_14_);
return v_res_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentSyncKind_ctorElim(lean_object* v_motive_16_, lean_object* v_ctorIdx_17_, uint8_t v_t_18_, lean_object* v_h_19_, lean_object* v_k_20_){
_start:
{
lean_inc(v_k_20_);
return v_k_20_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentSyncKind_ctorElim___boxed(lean_object* v_motive_21_, lean_object* v_ctorIdx_22_, lean_object* v_t_23_, lean_object* v_h_24_, lean_object* v_k_25_){
_start:
{
uint8_t v_t_boxed_26_; lean_object* v_res_27_; 
v_t_boxed_26_ = lean_unbox(v_t_23_);
v_res_27_ = l_Lean_Lsp_TextDocumentSyncKind_ctorElim(v_motive_21_, v_ctorIdx_22_, v_t_boxed_26_, v_h_24_, v_k_25_);
lean_dec(v_k_25_);
lean_dec(v_ctorIdx_22_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentSyncKind_none_elim___redArg(lean_object* v_none_28_){
_start:
{
lean_inc(v_none_28_);
return v_none_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentSyncKind_none_elim___redArg___boxed(lean_object* v_none_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_Lsp_TextDocumentSyncKind_none_elim___redArg(v_none_29_);
lean_dec(v_none_29_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentSyncKind_none_elim(lean_object* v_motive_31_, uint8_t v_t_32_, lean_object* v_h_33_, lean_object* v_none_34_){
_start:
{
lean_inc(v_none_34_);
return v_none_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentSyncKind_none_elim___boxed(lean_object* v_motive_35_, lean_object* v_t_36_, lean_object* v_h_37_, lean_object* v_none_38_){
_start:
{
uint8_t v_t_boxed_39_; lean_object* v_res_40_; 
v_t_boxed_39_ = lean_unbox(v_t_36_);
v_res_40_ = l_Lean_Lsp_TextDocumentSyncKind_none_elim(v_motive_35_, v_t_boxed_39_, v_h_37_, v_none_38_);
lean_dec(v_none_38_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentSyncKind_full_elim___redArg(lean_object* v_full_41_){
_start:
{
lean_inc(v_full_41_);
return v_full_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentSyncKind_full_elim___redArg___boxed(lean_object* v_full_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l_Lean_Lsp_TextDocumentSyncKind_full_elim___redArg(v_full_42_);
lean_dec(v_full_42_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentSyncKind_full_elim(lean_object* v_motive_44_, uint8_t v_t_45_, lean_object* v_h_46_, lean_object* v_full_47_){
_start:
{
lean_inc(v_full_47_);
return v_full_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentSyncKind_full_elim___boxed(lean_object* v_motive_48_, lean_object* v_t_49_, lean_object* v_h_50_, lean_object* v_full_51_){
_start:
{
uint8_t v_t_boxed_52_; lean_object* v_res_53_; 
v_t_boxed_52_ = lean_unbox(v_t_49_);
v_res_53_ = l_Lean_Lsp_TextDocumentSyncKind_full_elim(v_motive_48_, v_t_boxed_52_, v_h_50_, v_full_51_);
lean_dec(v_full_51_);
return v_res_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentSyncKind_incremental_elim___redArg(lean_object* v_incremental_54_){
_start:
{
lean_inc(v_incremental_54_);
return v_incremental_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentSyncKind_incremental_elim___redArg___boxed(lean_object* v_incremental_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_Lean_Lsp_TextDocumentSyncKind_incremental_elim___redArg(v_incremental_55_);
lean_dec(v_incremental_55_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentSyncKind_incremental_elim(lean_object* v_motive_57_, uint8_t v_t_58_, lean_object* v_h_59_, lean_object* v_incremental_60_){
_start:
{
lean_inc(v_incremental_60_);
return v_incremental_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentSyncKind_incremental_elim___boxed(lean_object* v_motive_61_, lean_object* v_t_62_, lean_object* v_h_63_, lean_object* v_incremental_64_){
_start:
{
uint8_t v_t_boxed_65_; lean_object* v_res_66_; 
v_t_boxed_65_ = lean_unbox(v_t_62_);
v_res_66_ = l_Lean_Lsp_TextDocumentSyncKind_incremental_elim(v_motive_61_, v_t_boxed_65_, v_h_63_, v_incremental_64_);
lean_dec(v_incremental_64_);
return v_res_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0(lean_object* v_j_79_){
_start:
{
lean_object* v___x_82_; 
v___x_82_ = l_Lean_Json_getNat_x3f(v_j_79_);
if (lean_obj_tag(v___x_82_) == 1)
{
lean_object* v_a_83_; lean_object* v___x_84_; uint8_t v___x_85_; 
v_a_83_ = lean_ctor_get(v___x_82_, 0);
lean_inc(v_a_83_);
lean_dec_ref(v___x_82_);
v___x_84_ = lean_unsigned_to_nat(0u);
v___x_85_ = lean_nat_dec_eq(v_a_83_, v___x_84_);
if (v___x_85_ == 0)
{
lean_object* v___x_86_; uint8_t v___x_87_; 
v___x_86_ = lean_unsigned_to_nat(1u);
v___x_87_ = lean_nat_dec_eq(v_a_83_, v___x_86_);
if (v___x_87_ == 0)
{
lean_object* v___x_88_; uint8_t v___x_89_; 
v___x_88_ = lean_unsigned_to_nat(2u);
v___x_89_ = lean_nat_dec_eq(v_a_83_, v___x_88_);
lean_dec(v_a_83_);
if (v___x_89_ == 0)
{
goto v___jp_80_;
}
else
{
lean_object* v___x_90_; 
v___x_90_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0___closed__2));
return v___x_90_;
}
}
else
{
lean_object* v___x_91_; 
lean_dec(v_a_83_);
v___x_91_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0___closed__3));
return v___x_91_;
}
}
else
{
lean_object* v___x_92_; 
lean_dec(v_a_83_);
v___x_92_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0___closed__4));
return v___x_92_;
}
}
else
{
lean_dec_ref(v___x_82_);
goto v___jp_80_;
}
v___jp_80_:
{
lean_object* v___x_81_; 
v___x_81_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0___closed__1));
return v___x_81_;
}
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__0(void){
_start:
{
lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_95_ = lean_unsigned_to_nat(0u);
v___x_96_ = l_Lean_JsonNumber_fromNat(v___x_95_);
return v___x_96_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__1(void){
_start:
{
lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_97_ = lean_obj_once(&l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__0, &l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__0_once, _init_l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__0);
v___x_98_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_98_, 0, v___x_97_);
return v___x_98_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__2(void){
_start:
{
lean_object* v___x_99_; lean_object* v___x_100_; 
v___x_99_ = lean_unsigned_to_nat(1u);
v___x_100_ = l_Lean_JsonNumber_fromNat(v___x_99_);
return v___x_100_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__3(void){
_start:
{
lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_101_ = lean_obj_once(&l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__2, &l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__2_once, _init_l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__2);
v___x_102_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_102_, 0, v___x_101_);
return v___x_102_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__4(void){
_start:
{
lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_103_ = lean_unsigned_to_nat(2u);
v___x_104_ = l_Lean_JsonNumber_fromNat(v___x_103_);
return v___x_104_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__5(void){
_start:
{
lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_105_ = lean_obj_once(&l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__4, &l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__4_once, _init_l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__4);
v___x_106_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_106_, 0, v___x_105_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0(uint8_t v_x_107_){
_start:
{
switch(v_x_107_)
{
case 0:
{
lean_object* v___x_108_; 
v___x_108_ = lean_obj_once(&l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__1, &l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__1_once, _init_l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__1);
return v___x_108_;
}
case 1:
{
lean_object* v___x_109_; 
v___x_109_ = lean_obj_once(&l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__3, &l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__3_once, _init_l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__3);
return v___x_109_;
}
default: 
{
lean_object* v___x_110_; 
v___x_110_ = lean_obj_once(&l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__5, &l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__5_once, _init_l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__5);
return v___x_110_;
}
}
}
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
lean_dec_ref(v_a_116_);
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
lean_dec_ref(v___x_207_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0_spec__2_spec__3(size_t v_sz_221_, size_t v_i_222_, lean_object* v_bs_223_){
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
lean_dec_ref(v___x_227_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_sz_243_, lean_object* v_i_244_, lean_object* v_bs_245_){
_start:
{
size_t v_sz_boxed_246_; size_t v_i_boxed_247_; lean_object* v_res_248_; 
v_sz_boxed_246_ = lean_unbox_usize(v_sz_243_);
lean_dec(v_sz_243_);
v_i_boxed_247_ = lean_unbox_usize(v_i_244_);
lean_dec(v_i_244_);
v_res_248_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0_spec__2_spec__3(v_sz_boxed_246_, v_i_boxed_247_, v_bs_245_);
return v_res_248_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0_spec__2(lean_object* v_x_251_){
_start:
{
if (lean_obj_tag(v_x_251_) == 4)
{
lean_object* v_elems_252_; size_t v_sz_253_; size_t v___x_254_; lean_object* v___x_255_; 
v_elems_252_ = lean_ctor_get(v_x_251_, 0);
lean_inc_ref(v_elems_252_);
lean_dec_ref(v_x_251_);
v_sz_253_ = lean_array_size(v_elems_252_);
v___x_254_ = ((size_t)0ULL);
v___x_255_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0_spec__2_spec__3(v_sz_253_, v___x_254_, v_elems_252_);
return v___x_255_;
}
else
{
lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; 
v___x_256_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0_spec__2___closed__0));
v___x_257_ = lean_unsigned_to_nat(80u);
v___x_258_ = l_Lean_Json_pretty(v_x_251_, v___x_257_);
v___x_259_ = lean_string_append(v___x_256_, v___x_258_);
lean_dec_ref(v___x_258_);
v___x_260_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0_spec__2___closed__1));
v___x_261_ = lean_string_append(v___x_259_, v___x_260_);
v___x_262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_262_, 0, v___x_261_);
return v___x_262_;
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0(lean_object* v_x_265_){
_start:
{
if (lean_obj_tag(v_x_265_) == 0)
{
lean_object* v___x_266_; 
v___x_266_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0___closed__0));
return v___x_266_;
}
else
{
lean_object* v___x_267_; 
v___x_267_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0_spec__2(v_x_265_);
if (lean_obj_tag(v___x_267_) == 0)
{
lean_object* v_a_268_; lean_object* v___x_270_; uint8_t v_isShared_271_; uint8_t v_isSharedCheck_275_; 
v_a_268_ = lean_ctor_get(v___x_267_, 0);
v_isSharedCheck_275_ = !lean_is_exclusive(v___x_267_);
if (v_isSharedCheck_275_ == 0)
{
v___x_270_ = v___x_267_;
v_isShared_271_ = v_isSharedCheck_275_;
goto v_resetjp_269_;
}
else
{
lean_inc(v_a_268_);
lean_dec(v___x_267_);
v___x_270_ = lean_box(0);
v_isShared_271_ = v_isSharedCheck_275_;
goto v_resetjp_269_;
}
v_resetjp_269_:
{
lean_object* v___x_273_; 
if (v_isShared_271_ == 0)
{
v___x_273_ = v___x_270_;
goto v_reusejp_272_;
}
else
{
lean_object* v_reuseFailAlloc_274_; 
v_reuseFailAlloc_274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_274_, 0, v_a_268_);
v___x_273_ = v_reuseFailAlloc_274_;
goto v_reusejp_272_;
}
v_reusejp_272_:
{
return v___x_273_;
}
}
}
else
{
lean_object* v_a_276_; lean_object* v___x_278_; uint8_t v_isShared_279_; uint8_t v_isSharedCheck_284_; 
v_a_276_ = lean_ctor_get(v___x_267_, 0);
v_isSharedCheck_284_ = !lean_is_exclusive(v___x_267_);
if (v_isSharedCheck_284_ == 0)
{
v___x_278_ = v___x_267_;
v_isShared_279_ = v_isSharedCheck_284_;
goto v_resetjp_277_;
}
else
{
lean_inc(v_a_276_);
lean_dec(v___x_267_);
v___x_278_ = lean_box(0);
v_isShared_279_ = v_isSharedCheck_284_;
goto v_resetjp_277_;
}
v_resetjp_277_:
{
lean_object* v___x_280_; lean_object* v___x_282_; 
v___x_280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_280_, 0, v_a_276_);
if (v_isShared_279_ == 0)
{
lean_ctor_set(v___x_278_, 0, v___x_280_);
v___x_282_ = v___x_278_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v___x_280_);
v___x_282_ = v_reuseFailAlloc_283_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
return v___x_282_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0(lean_object* v_j_285_, lean_object* v_k_286_){
_start:
{
lean_object* v___x_287_; lean_object* v___x_288_; 
v___x_287_ = l_Lean_Json_getObjValD(v_j_285_, v_k_286_);
v___x_288_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0(v___x_287_);
return v___x_288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0___boxed(lean_object* v_j_289_, lean_object* v_k_290_){
_start:
{
lean_object* v_res_291_; 
v_res_291_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0(v_j_289_, v_k_290_);
lean_dec_ref(v_k_290_);
return v_res_291_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__3(void){
_start:
{
uint8_t v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_298_ = 1;
v___x_299_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__2));
v___x_300_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_299_, v___x_298_);
return v___x_300_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__4(void){
_start:
{
lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_301_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__5));
v___x_302_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__3, &l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__3);
v___x_303_ = lean_string_append(v___x_302_, v___x_301_);
return v___x_303_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__7(void){
_start:
{
uint8_t v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_307_ = 1;
v___x_308_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__6));
v___x_309_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_308_, v___x_307_);
return v___x_309_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__8(void){
_start:
{
lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_310_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__7, &l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__7);
v___x_311_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__4, &l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__4);
v___x_312_ = lean_string_append(v___x_311_, v___x_310_);
return v___x_312_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__9(void){
_start:
{
lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_313_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__10));
v___x_314_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__8, &l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__8);
v___x_315_ = lean_string_append(v___x_314_, v___x_313_);
return v___x_315_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__12(void){
_start:
{
uint8_t v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_319_ = 1;
v___x_320_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__11));
v___x_321_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_320_, v___x_319_);
return v___x_321_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__13(void){
_start:
{
lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_322_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__12, &l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__12);
v___x_323_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__4, &l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__4);
v___x_324_ = lean_string_append(v___x_323_, v___x_322_);
return v___x_324_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__14(void){
_start:
{
lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; 
v___x_325_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__10));
v___x_326_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__13, &l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__13);
v___x_327_ = lean_string_append(v___x_326_, v___x_325_);
return v___x_327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson(lean_object* v_json_328_){
_start:
{
lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_329_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__0));
lean_inc(v_json_328_);
v___x_330_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0(v_json_328_, v___x_329_);
if (lean_obj_tag(v___x_330_) == 0)
{
lean_object* v_a_331_; lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_340_; 
lean_dec(v_json_328_);
v_a_331_ = lean_ctor_get(v___x_330_, 0);
v_isSharedCheck_340_ = !lean_is_exclusive(v___x_330_);
if (v_isSharedCheck_340_ == 0)
{
v___x_333_ = v___x_330_;
v_isShared_334_ = v_isSharedCheck_340_;
goto v_resetjp_332_;
}
else
{
lean_inc(v_a_331_);
lean_dec(v___x_330_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_340_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_338_; 
v___x_335_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__9, &l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__9);
v___x_336_ = lean_string_append(v___x_335_, v_a_331_);
lean_dec(v_a_331_);
if (v_isShared_334_ == 0)
{
lean_ctor_set(v___x_333_, 0, v___x_336_);
v___x_338_ = v___x_333_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v___x_336_);
v___x_338_ = v_reuseFailAlloc_339_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
return v___x_338_;
}
}
}
else
{
if (lean_obj_tag(v___x_330_) == 0)
{
lean_object* v_a_341_; lean_object* v___x_343_; uint8_t v_isShared_344_; uint8_t v_isSharedCheck_348_; 
lean_dec(v_json_328_);
v_a_341_ = lean_ctor_get(v___x_330_, 0);
v_isSharedCheck_348_ = !lean_is_exclusive(v___x_330_);
if (v_isSharedCheck_348_ == 0)
{
v___x_343_ = v___x_330_;
v_isShared_344_ = v_isSharedCheck_348_;
goto v_resetjp_342_;
}
else
{
lean_inc(v_a_341_);
lean_dec(v___x_330_);
v___x_343_ = lean_box(0);
v_isShared_344_ = v_isSharedCheck_348_;
goto v_resetjp_342_;
}
v_resetjp_342_:
{
lean_object* v___x_346_; 
if (v_isShared_344_ == 0)
{
lean_ctor_set_tag(v___x_343_, 0);
v___x_346_ = v___x_343_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v_a_341_);
v___x_346_ = v_reuseFailAlloc_347_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
return v___x_346_;
}
}
}
else
{
lean_object* v_a_349_; lean_object* v___x_350_; lean_object* v___x_351_; 
v_a_349_ = lean_ctor_get(v___x_330_, 0);
lean_inc(v_a_349_);
lean_dec_ref(v___x_330_);
v___x_350_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__10));
v___x_351_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__1(v_json_328_, v___x_350_);
if (lean_obj_tag(v___x_351_) == 0)
{
lean_object* v_a_352_; lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_361_; 
lean_dec(v_a_349_);
v_a_352_ = lean_ctor_get(v___x_351_, 0);
v_isSharedCheck_361_ = !lean_is_exclusive(v___x_351_);
if (v_isSharedCheck_361_ == 0)
{
v___x_354_ = v___x_351_;
v_isShared_355_ = v_isSharedCheck_361_;
goto v_resetjp_353_;
}
else
{
lean_inc(v_a_352_);
lean_dec(v___x_351_);
v___x_354_ = lean_box(0);
v_isShared_355_ = v_isSharedCheck_361_;
goto v_resetjp_353_;
}
v_resetjp_353_:
{
lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_359_; 
v___x_356_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__14, &l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__14_once, _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__14);
v___x_357_ = lean_string_append(v___x_356_, v_a_352_);
lean_dec(v_a_352_);
if (v_isShared_355_ == 0)
{
lean_ctor_set(v___x_354_, 0, v___x_357_);
v___x_359_ = v___x_354_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_360_; 
v_reuseFailAlloc_360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_360_, 0, v___x_357_);
v___x_359_ = v_reuseFailAlloc_360_;
goto v_reusejp_358_;
}
v_reusejp_358_:
{
return v___x_359_;
}
}
}
else
{
if (lean_obj_tag(v___x_351_) == 0)
{
lean_object* v_a_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_369_; 
lean_dec(v_a_349_);
v_a_362_ = lean_ctor_get(v___x_351_, 0);
v_isSharedCheck_369_ = !lean_is_exclusive(v___x_351_);
if (v_isSharedCheck_369_ == 0)
{
v___x_364_ = v___x_351_;
v_isShared_365_ = v_isSharedCheck_369_;
goto v_resetjp_363_;
}
else
{
lean_inc(v_a_362_);
lean_dec(v___x_351_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_369_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
lean_object* v___x_367_; 
if (v_isShared_365_ == 0)
{
lean_ctor_set_tag(v___x_364_, 0);
v___x_367_ = v___x_364_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v_a_362_);
v___x_367_ = v_reuseFailAlloc_368_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
return v___x_367_;
}
}
}
else
{
lean_object* v_a_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_379_; 
v_a_370_ = lean_ctor_get(v___x_351_, 0);
v_isSharedCheck_379_ = !lean_is_exclusive(v___x_351_);
if (v_isSharedCheck_379_ == 0)
{
v___x_372_ = v___x_351_;
v_isShared_373_ = v_isSharedCheck_379_;
goto v_resetjp_371_;
}
else
{
lean_inc(v_a_370_);
lean_dec(v___x_351_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_379_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
lean_object* v___x_374_; uint8_t v___x_375_; lean_object* v___x_377_; 
v___x_374_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_374_, 0, v_a_349_);
v___x_375_ = lean_unbox(v_a_370_);
lean_dec(v_a_370_);
lean_ctor_set_uint8(v___x_374_, sizeof(void*)*1, v___x_375_);
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 0, v___x_374_);
v___x_377_ = v___x_372_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v___x_374_);
v___x_377_ = v_reuseFailAlloc_378_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
return v___x_377_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentContentChangeEvent_ctorIdx(lean_object* v_x_382_){
_start:
{
if (lean_obj_tag(v_x_382_) == 0)
{
lean_object* v___x_383_; 
v___x_383_ = lean_unsigned_to_nat(0u);
return v___x_383_;
}
else
{
lean_object* v___x_384_; 
v___x_384_ = lean_unsigned_to_nat(1u);
return v___x_384_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentContentChangeEvent_ctorIdx___boxed(lean_object* v_x_385_){
_start:
{
lean_object* v_res_386_; 
v_res_386_ = l_Lean_Lsp_TextDocumentContentChangeEvent_ctorIdx(v_x_385_);
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
lean_dec_ref(v_t_387_);
v___x_391_ = lean_apply_2(v_k_388_, v_range_389_, v_text_390_);
return v___x_391_;
}
else
{
lean_object* v_text_392_; lean_object* v___x_393_; 
v_text_392_ = lean_ctor_get(v_t_387_, 0);
lean_inc_ref(v_text_392_);
lean_dec_ref(v_t_387_);
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
lean_dec_ref(v___x_448_);
goto v___jp_427_;
}
else
{
lean_object* v_a_449_; lean_object* v___x_450_; lean_object* v___x_451_; 
v_a_449_ = lean_ctor_get(v___x_448_, 0);
lean_inc(v_a_449_);
lean_dec_ref(v___x_448_);
v___x_450_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0___closed__0));
lean_inc_ref(v___x_424_);
lean_inc(v_j_426_);
v___x_451_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_426_, v___x_424_, v___x_450_);
if (lean_obj_tag(v___x_451_) == 0)
{
lean_dec_ref(v___x_451_);
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
return v___x_496_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonDidChangeTextDocumentParams_toJson_spec__0_spec__0(size_t v_sz_501_, size_t v_i_502_, lean_object* v_bs_503_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonDidChangeTextDocumentParams_toJson_spec__0_spec__0___boxed(lean_object* v_sz_545_, lean_object* v_i_546_, lean_object* v_bs_547_){
_start:
{
size_t v_sz_boxed_548_; size_t v_i_boxed_549_; lean_object* v_res_550_; 
v_sz_boxed_548_ = lean_unbox_usize(v_sz_545_);
lean_dec(v_sz_545_);
v_i_boxed_549_ = lean_unbox_usize(v_i_546_);
lean_dec(v_i_546_);
v_res_550_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonDidChangeTextDocumentParams_toJson_spec__0_spec__0(v_sz_boxed_548_, v_i_boxed_549_, v_bs_547_);
return v_res_550_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Lsp_instToJsonDidChangeTextDocumentParams_toJson_spec__0(lean_object* v_a_551_){
_start:
{
size_t v_sz_552_; size_t v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; 
v_sz_552_ = lean_array_size(v_a_551_);
v___x_553_ = ((size_t)0ULL);
v___x_554_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonDidChangeTextDocumentParams_toJson_spec__0_spec__0(v_sz_552_, v___x_553_, v_a_551_);
v___x_555_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_555_, 0, v___x_554_);
return v___x_555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDidChangeTextDocumentParams_toJson(lean_object* v_x_557_){
_start:
{
lean_object* v_textDocument_558_; lean_object* v_contentChanges_559_; lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_579_; 
v_textDocument_558_ = lean_ctor_get(v_x_557_, 0);
v_contentChanges_559_ = lean_ctor_get(v_x_557_, 1);
v_isSharedCheck_579_ = !lean_is_exclusive(v_x_557_);
if (v_isSharedCheck_579_ == 0)
{
v___x_561_ = v_x_557_;
v_isShared_562_ = v_isSharedCheck_579_;
goto v_resetjp_560_;
}
else
{
lean_inc(v_contentChanges_559_);
lean_inc(v_textDocument_558_);
lean_dec(v_x_557_);
v___x_561_ = lean_box(0);
v_isShared_562_ = v_isSharedCheck_579_;
goto v_resetjp_560_;
}
v_resetjp_560_:
{
lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_566_; 
v___x_563_ = ((lean_object*)(l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__0));
v___x_564_ = l_Lean_Lsp_instToJsonVersionedTextDocumentIdentifier_toJson(v_textDocument_558_);
if (v_isShared_562_ == 0)
{
lean_ctor_set(v___x_561_, 1, v___x_564_);
lean_ctor_set(v___x_561_, 0, v___x_563_);
v___x_566_ = v___x_561_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v___x_563_);
lean_ctor_set(v_reuseFailAlloc_578_, 1, v___x_564_);
v___x_566_ = v_reuseFailAlloc_578_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_567_ = lean_box(0);
v___x_568_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_568_, 0, v___x_566_);
lean_ctor_set(v___x_568_, 1, v___x_567_);
v___x_569_ = ((lean_object*)(l_Lean_Lsp_instToJsonDidChangeTextDocumentParams_toJson___closed__0));
v___x_570_ = l_Array_toJson___at___00Lean_Lsp_instToJsonDidChangeTextDocumentParams_toJson_spec__0(v_contentChanges_559_);
v___x_571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_571_, 0, v___x_569_);
lean_ctor_set(v___x_571_, 1, v___x_570_);
v___x_572_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_572_, 0, v___x_571_);
lean_ctor_set(v___x_572_, 1, v___x_567_);
v___x_573_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_573_, 0, v___x_572_);
lean_ctor_set(v___x_573_, 1, v___x_567_);
v___x_574_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_574_, 0, v___x_568_);
lean_ctor_set(v___x_574_, 1, v___x_573_);
v___x_575_ = ((lean_object*)(l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__1));
v___x_576_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson_spec__0(v___x_574_, v___x_575_);
v___x_577_ = l_Lean_Json_mkObj(v___x_576_);
return v___x_577_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__0(lean_object* v_j_582_, lean_object* v_k_583_){
_start:
{
lean_object* v___x_584_; lean_object* v___x_585_; 
v___x_584_ = l_Lean_Json_getObjValD(v_j_582_, v_k_583_);
v___x_585_ = l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson(v___x_584_);
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__0___boxed(lean_object* v_j_586_, lean_object* v_k_587_){
_start:
{
lean_object* v_res_588_; 
v_res_588_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__0(v_j_586_, v_k_587_);
lean_dec_ref(v_k_587_);
return v_res_588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1_spec__3(lean_object* v_j_589_, lean_object* v_k_590_){
_start:
{
lean_object* v___x_591_; lean_object* v___x_592_; 
v___x_591_ = l_Lean_Json_getObjValD(v_j_589_, v_k_590_);
v___x_592_ = l_Lean_Lsp_instFromJsonRange_fromJson(v___x_591_);
return v___x_592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1_spec__3___boxed(lean_object* v_j_593_, lean_object* v_k_594_){
_start:
{
lean_object* v_res_595_; 
v_res_595_ = l_Lean_Json_getObjValAs_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1_spec__3(v_j_593_, v_k_594_);
lean_dec_ref(v_k_594_);
return v_res_595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1_spec__2(lean_object* v_j_596_, lean_object* v_k_597_){
_start:
{
lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_598_ = l_Lean_Json_getObjValD(v_j_596_, v_k_597_);
v___x_599_ = l_Lean_Json_getStr_x3f(v___x_598_);
return v___x_599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1_spec__2___boxed(lean_object* v_j_600_, lean_object* v_k_601_){
_start:
{
lean_object* v_res_602_; 
v_res_602_ = l_Lean_Json_getObjValAs_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1_spec__2(v_j_600_, v_k_601_);
lean_dec_ref(v_k_601_);
return v_res_602_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1_spec__4(size_t v_sz_603_, size_t v_i_604_, lean_object* v_bs_605_){
_start:
{
uint8_t v___x_606_; 
v___x_606_ = lean_usize_dec_lt(v_i_604_, v_sz_603_);
if (v___x_606_ == 0)
{
lean_object* v___x_607_; 
v___x_607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_607_, 0, v_bs_605_);
return v___x_607_;
}
else
{
lean_object* v_v_608_; lean_object* v___x_609_; lean_object* v_bs_x27_610_; lean_object* v_a_612_; lean_object* v___x_630_; lean_object* v___x_631_; 
v_v_608_ = lean_array_uget(v_bs_605_, v_i_604_);
v___x_609_ = lean_unsigned_to_nat(0u);
v_bs_x27_610_ = lean_array_uset(v_bs_605_, v_i_604_, v___x_609_);
v___x_630_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0___closed__1));
lean_inc(v_v_608_);
v___x_631_ = l_Lean_Json_getObjValAs_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1_spec__3(v_v_608_, v___x_630_);
if (lean_obj_tag(v___x_631_) == 0)
{
lean_dec_ref(v___x_631_);
goto v___jp_617_;
}
else
{
lean_object* v_a_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
v_a_632_ = lean_ctor_get(v___x_631_, 0);
lean_inc(v_a_632_);
lean_dec_ref(v___x_631_);
v___x_633_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0___closed__0));
lean_inc(v_v_608_);
v___x_634_ = l_Lean_Json_getObjValAs_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1_spec__2(v_v_608_, v___x_633_);
if (lean_obj_tag(v___x_634_) == 0)
{
lean_dec_ref(v___x_634_);
lean_dec(v_a_632_);
goto v___jp_617_;
}
else
{
lean_object* v_a_635_; lean_object* v___x_636_; 
lean_dec(v_v_608_);
v_a_635_ = lean_ctor_get(v___x_634_, 0);
lean_inc(v_a_635_);
lean_dec_ref(v___x_634_);
v___x_636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_636_, 0, v_a_632_);
lean_ctor_set(v___x_636_, 1, v_a_635_);
v_a_612_ = v___x_636_;
goto v___jp_611_;
}
}
v___jp_611_:
{
size_t v___x_613_; size_t v___x_614_; lean_object* v___x_615_; 
v___x_613_ = ((size_t)1ULL);
v___x_614_ = lean_usize_add(v_i_604_, v___x_613_);
v___x_615_ = lean_array_uset(v_bs_x27_610_, v_i_604_, v_a_612_);
v_i_604_ = v___x_614_;
v_bs_605_ = v___x_615_;
goto _start;
}
v___jp_617_:
{
lean_object* v___x_618_; lean_object* v___x_619_; 
v___x_618_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0___closed__0));
v___x_619_ = l_Lean_Json_getObjValAs_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1_spec__2(v_v_608_, v___x_618_);
if (lean_obj_tag(v___x_619_) == 0)
{
lean_object* v_a_620_; lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_627_; 
lean_dec_ref(v_bs_x27_610_);
v_a_620_ = lean_ctor_get(v___x_619_, 0);
v_isSharedCheck_627_ = !lean_is_exclusive(v___x_619_);
if (v_isSharedCheck_627_ == 0)
{
v___x_622_ = v___x_619_;
v_isShared_623_ = v_isSharedCheck_627_;
goto v_resetjp_621_;
}
else
{
lean_inc(v_a_620_);
lean_dec(v___x_619_);
v___x_622_ = lean_box(0);
v_isShared_623_ = v_isSharedCheck_627_;
goto v_resetjp_621_;
}
v_resetjp_621_:
{
lean_object* v___x_625_; 
if (v_isShared_623_ == 0)
{
v___x_625_ = v___x_622_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v_a_620_);
v___x_625_ = v_reuseFailAlloc_626_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
return v___x_625_;
}
}
}
else
{
lean_object* v_a_628_; lean_object* v___x_629_; 
v_a_628_ = lean_ctor_get(v___x_619_, 0);
lean_inc(v_a_628_);
lean_dec_ref(v___x_619_);
v___x_629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_629_, 0, v_a_628_);
v_a_612_ = v___x_629_;
goto v___jp_611_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1_spec__4___boxed(lean_object* v_sz_637_, lean_object* v_i_638_, lean_object* v_bs_639_){
_start:
{
size_t v_sz_boxed_640_; size_t v_i_boxed_641_; lean_object* v_res_642_; 
v_sz_boxed_640_ = lean_unbox_usize(v_sz_637_);
lean_dec(v_sz_637_);
v_i_boxed_641_ = lean_unbox_usize(v_i_638_);
lean_dec(v_i_638_);
v_res_642_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1_spec__4(v_sz_boxed_640_, v_i_boxed_641_, v_bs_639_);
return v_res_642_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1(lean_object* v_x_643_){
_start:
{
if (lean_obj_tag(v_x_643_) == 4)
{
lean_object* v_elems_644_; size_t v_sz_645_; size_t v___x_646_; lean_object* v___x_647_; 
v_elems_644_ = lean_ctor_get(v_x_643_, 0);
lean_inc_ref(v_elems_644_);
lean_dec_ref(v_x_643_);
v_sz_645_ = lean_array_size(v_elems_644_);
v___x_646_ = ((size_t)0ULL);
v___x_647_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1_spec__4(v_sz_645_, v___x_646_, v_elems_644_);
return v___x_647_;
}
else
{
lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; 
v___x_648_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0_spec__2___closed__0));
v___x_649_ = lean_unsigned_to_nat(80u);
v___x_650_ = l_Lean_Json_pretty(v_x_643_, v___x_649_);
v___x_651_ = lean_string_append(v___x_648_, v___x_650_);
lean_dec_ref(v___x_650_);
v___x_652_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0_spec__2___closed__1));
v___x_653_ = lean_string_append(v___x_651_, v___x_652_);
v___x_654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_654_, 0, v___x_653_);
return v___x_654_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1(lean_object* v_j_655_, lean_object* v_k_656_){
_start:
{
lean_object* v___x_657_; lean_object* v___x_658_; 
v___x_657_ = l_Lean_Json_getObjValD(v_j_655_, v_k_656_);
v___x_658_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1(v___x_657_);
return v___x_658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1___boxed(lean_object* v_j_659_, lean_object* v_k_660_){
_start:
{
lean_object* v_res_661_; 
v_res_661_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1(v_j_659_, v_k_660_);
lean_dec_ref(v_k_660_);
return v_res_661_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__2(void){
_start:
{
uint8_t v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; 
v___x_667_ = 1;
v___x_668_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__1));
v___x_669_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_668_, v___x_667_);
return v___x_669_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__3(void){
_start:
{
lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; 
v___x_670_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__5));
v___x_671_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__2, &l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__2);
v___x_672_ = lean_string_append(v___x_671_, v___x_670_);
return v___x_672_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; 
v___x_673_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__8);
v___x_674_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__3);
v___x_675_ = lean_string_append(v___x_674_, v___x_673_);
return v___x_675_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__5(void){
_start:
{
lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; 
v___x_676_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__10));
v___x_677_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__4);
v___x_678_ = lean_string_append(v___x_677_, v___x_676_);
return v___x_678_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__7(void){
_start:
{
uint8_t v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; 
v___x_681_ = 1;
v___x_682_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__6));
v___x_683_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_682_, v___x_681_);
return v___x_683_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__8(void){
_start:
{
lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; 
v___x_684_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__7);
v___x_685_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__3);
v___x_686_ = lean_string_append(v___x_685_, v___x_684_);
return v___x_686_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__9(void){
_start:
{
lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_687_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__10));
v___x_688_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__8);
v___x_689_ = lean_string_append(v___x_688_, v___x_687_);
return v___x_689_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson(lean_object* v_json_690_){
_start:
{
lean_object* v___x_691_; lean_object* v___x_692_; 
v___x_691_ = ((lean_object*)(l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__0));
lean_inc(v_json_690_);
v___x_692_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__0(v_json_690_, v___x_691_);
if (lean_obj_tag(v___x_692_) == 0)
{
lean_object* v_a_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_702_; 
lean_dec(v_json_690_);
v_a_693_ = lean_ctor_get(v___x_692_, 0);
v_isSharedCheck_702_ = !lean_is_exclusive(v___x_692_);
if (v_isSharedCheck_702_ == 0)
{
v___x_695_ = v___x_692_;
v_isShared_696_ = v_isSharedCheck_702_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_a_693_);
lean_dec(v___x_692_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_702_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_700_; 
v___x_697_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__5, &l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__5);
v___x_698_ = lean_string_append(v___x_697_, v_a_693_);
lean_dec(v_a_693_);
if (v_isShared_696_ == 0)
{
lean_ctor_set(v___x_695_, 0, v___x_698_);
v___x_700_ = v___x_695_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v___x_698_);
v___x_700_ = v_reuseFailAlloc_701_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
return v___x_700_;
}
}
}
else
{
if (lean_obj_tag(v___x_692_) == 0)
{
lean_object* v_a_703_; lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_710_; 
lean_dec(v_json_690_);
v_a_703_ = lean_ctor_get(v___x_692_, 0);
v_isSharedCheck_710_ = !lean_is_exclusive(v___x_692_);
if (v_isSharedCheck_710_ == 0)
{
v___x_705_ = v___x_692_;
v_isShared_706_ = v_isSharedCheck_710_;
goto v_resetjp_704_;
}
else
{
lean_inc(v_a_703_);
lean_dec(v___x_692_);
v___x_705_ = lean_box(0);
v_isShared_706_ = v_isSharedCheck_710_;
goto v_resetjp_704_;
}
v_resetjp_704_:
{
lean_object* v___x_708_; 
if (v_isShared_706_ == 0)
{
lean_ctor_set_tag(v___x_705_, 0);
v___x_708_ = v___x_705_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v_a_703_);
v___x_708_ = v_reuseFailAlloc_709_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
return v___x_708_;
}
}
}
else
{
lean_object* v_a_711_; lean_object* v___x_712_; lean_object* v___x_713_; 
v_a_711_ = lean_ctor_get(v___x_692_, 0);
lean_inc(v_a_711_);
lean_dec_ref(v___x_692_);
v___x_712_ = ((lean_object*)(l_Lean_Lsp_instToJsonDidChangeTextDocumentParams_toJson___closed__0));
v___x_713_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1(v_json_690_, v___x_712_);
if (lean_obj_tag(v___x_713_) == 0)
{
lean_object* v_a_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_723_; 
lean_dec(v_a_711_);
v_a_714_ = lean_ctor_get(v___x_713_, 0);
v_isSharedCheck_723_ = !lean_is_exclusive(v___x_713_);
if (v_isSharedCheck_723_ == 0)
{
v___x_716_ = v___x_713_;
v_isShared_717_ = v_isSharedCheck_723_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_a_714_);
lean_dec(v___x_713_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_723_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_721_; 
v___x_718_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__9, &l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__9);
v___x_719_ = lean_string_append(v___x_718_, v_a_714_);
lean_dec(v_a_714_);
if (v_isShared_717_ == 0)
{
lean_ctor_set(v___x_716_, 0, v___x_719_);
v___x_721_ = v___x_716_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v___x_719_);
v___x_721_ = v_reuseFailAlloc_722_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
return v___x_721_;
}
}
}
else
{
if (lean_obj_tag(v___x_713_) == 0)
{
lean_object* v_a_724_; lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_731_; 
lean_dec(v_a_711_);
v_a_724_ = lean_ctor_get(v___x_713_, 0);
v_isSharedCheck_731_ = !lean_is_exclusive(v___x_713_);
if (v_isSharedCheck_731_ == 0)
{
v___x_726_ = v___x_713_;
v_isShared_727_ = v_isSharedCheck_731_;
goto v_resetjp_725_;
}
else
{
lean_inc(v_a_724_);
lean_dec(v___x_713_);
v___x_726_ = lean_box(0);
v_isShared_727_ = v_isSharedCheck_731_;
goto v_resetjp_725_;
}
v_resetjp_725_:
{
lean_object* v___x_729_; 
if (v_isShared_727_ == 0)
{
lean_ctor_set_tag(v___x_726_, 0);
v___x_729_ = v___x_726_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v_a_724_);
v___x_729_ = v_reuseFailAlloc_730_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
return v___x_729_;
}
}
}
else
{
lean_object* v_a_732_; lean_object* v___x_734_; uint8_t v_isShared_735_; uint8_t v_isSharedCheck_740_; 
v_a_732_ = lean_ctor_get(v___x_713_, 0);
v_isSharedCheck_740_ = !lean_is_exclusive(v___x_713_);
if (v_isSharedCheck_740_ == 0)
{
v___x_734_ = v___x_713_;
v_isShared_735_ = v_isSharedCheck_740_;
goto v_resetjp_733_;
}
else
{
lean_inc(v_a_732_);
lean_dec(v___x_713_);
v___x_734_ = lean_box(0);
v_isShared_735_ = v_isSharedCheck_740_;
goto v_resetjp_733_;
}
v_resetjp_733_:
{
lean_object* v___x_736_; lean_object* v___x_738_; 
v___x_736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_736_, 0, v_a_711_);
lean_ctor_set(v___x_736_, 1, v_a_732_);
if (v_isShared_735_ == 0)
{
lean_ctor_set(v___x_734_, 0, v___x_736_);
v___x_738_ = v___x_734_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v___x_736_);
v___x_738_ = v_reuseFailAlloc_739_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
return v___x_738_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDidSaveTextDocumentParams_toJson_spec__0(lean_object* v_k_743_, lean_object* v_x_744_){
_start:
{
if (lean_obj_tag(v_x_744_) == 0)
{
lean_object* v___x_745_; 
lean_dec_ref(v_k_743_);
v___x_745_ = lean_box(0);
return v___x_745_;
}
else
{
lean_object* v_val_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_756_; 
v_val_746_ = lean_ctor_get(v_x_744_, 0);
v_isSharedCheck_756_ = !lean_is_exclusive(v_x_744_);
if (v_isSharedCheck_756_ == 0)
{
v___x_748_ = v_x_744_;
v_isShared_749_ = v_isSharedCheck_756_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_val_746_);
lean_dec(v_x_744_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_756_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v___x_751_; 
if (v_isShared_749_ == 0)
{
lean_ctor_set_tag(v___x_748_, 3);
v___x_751_ = v___x_748_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v_val_746_);
v___x_751_ = v_reuseFailAlloc_755_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; 
v___x_752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_752_, 0, v_k_743_);
lean_ctor_set(v___x_752_, 1, v___x_751_);
v___x_753_ = lean_box(0);
v___x_754_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_754_, 0, v___x_752_);
lean_ctor_set(v___x_754_, 1, v___x_753_);
return v___x_754_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDidSaveTextDocumentParams_toJson(lean_object* v_x_757_){
_start:
{
lean_object* v_textDocument_758_; lean_object* v_text_x3f_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_777_; 
v_textDocument_758_ = lean_ctor_get(v_x_757_, 0);
v_text_x3f_759_ = lean_ctor_get(v_x_757_, 1);
v_isSharedCheck_777_ = !lean_is_exclusive(v_x_757_);
if (v_isSharedCheck_777_ == 0)
{
v___x_761_ = v_x_757_;
v_isShared_762_ = v_isSharedCheck_777_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_text_x3f_759_);
lean_inc(v_textDocument_758_);
lean_dec(v_x_757_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_777_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_766_; 
v___x_763_ = ((lean_object*)(l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__0));
v___x_764_ = l_Lean_Lsp_instToJsonTextDocumentIdentifier_toJson(v_textDocument_758_);
if (v_isShared_762_ == 0)
{
lean_ctor_set(v___x_761_, 1, v___x_764_);
lean_ctor_set(v___x_761_, 0, v___x_763_);
v___x_766_ = v___x_761_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v___x_763_);
lean_ctor_set(v_reuseFailAlloc_776_, 1, v___x_764_);
v___x_766_ = v_reuseFailAlloc_776_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; 
v___x_767_ = lean_box(0);
v___x_768_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_768_, 0, v___x_766_);
lean_ctor_set(v___x_768_, 1, v___x_767_);
v___x_769_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0___closed__0));
v___x_770_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDidSaveTextDocumentParams_toJson_spec__0(v___x_769_, v_text_x3f_759_);
v___x_771_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_771_, 0, v___x_770_);
lean_ctor_set(v___x_771_, 1, v___x_767_);
v___x_772_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_772_, 0, v___x_768_);
lean_ctor_set(v___x_772_, 1, v___x_771_);
v___x_773_ = ((lean_object*)(l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__1));
v___x_774_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson_spec__0(v___x_772_, v___x_773_);
v___x_775_ = l_Lean_Json_mkObj(v___x_774_);
return v___x_775_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson_spec__0(lean_object* v_j_780_, lean_object* v_k_781_){
_start:
{
lean_object* v___x_782_; lean_object* v___x_783_; 
v___x_782_ = l_Lean_Json_getObjValD(v_j_780_, v_k_781_);
v___x_783_ = l_Lean_Lsp_instFromJsonTextDocumentIdentifier_fromJson(v___x_782_);
return v___x_783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson_spec__0___boxed(lean_object* v_j_784_, lean_object* v_k_785_){
_start:
{
lean_object* v_res_786_; 
v_res_786_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson_spec__0(v_j_784_, v_k_785_);
lean_dec_ref(v_k_785_);
return v_res_786_;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson_spec__1_spec__1(lean_object* v_x_789_){
_start:
{
if (lean_obj_tag(v_x_789_) == 0)
{
lean_object* v___x_790_; 
v___x_790_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson_spec__1_spec__1___closed__0));
return v___x_790_;
}
else
{
lean_object* v___x_791_; 
v___x_791_ = l_Lean_Json_getStr_x3f(v_x_789_);
if (lean_obj_tag(v___x_791_) == 0)
{
lean_object* v_a_792_; lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_799_; 
v_a_792_ = lean_ctor_get(v___x_791_, 0);
v_isSharedCheck_799_ = !lean_is_exclusive(v___x_791_);
if (v_isSharedCheck_799_ == 0)
{
v___x_794_ = v___x_791_;
v_isShared_795_ = v_isSharedCheck_799_;
goto v_resetjp_793_;
}
else
{
lean_inc(v_a_792_);
lean_dec(v___x_791_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_799_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
lean_object* v___x_797_; 
if (v_isShared_795_ == 0)
{
v___x_797_ = v___x_794_;
goto v_reusejp_796_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v_a_792_);
v___x_797_ = v_reuseFailAlloc_798_;
goto v_reusejp_796_;
}
v_reusejp_796_:
{
return v___x_797_;
}
}
}
else
{
lean_object* v_a_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_808_; 
v_a_800_ = lean_ctor_get(v___x_791_, 0);
v_isSharedCheck_808_ = !lean_is_exclusive(v___x_791_);
if (v_isSharedCheck_808_ == 0)
{
v___x_802_ = v___x_791_;
v_isShared_803_ = v_isSharedCheck_808_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_a_800_);
lean_dec(v___x_791_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_808_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
lean_object* v___x_804_; lean_object* v___x_806_; 
v___x_804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_804_, 0, v_a_800_);
if (v_isShared_803_ == 0)
{
lean_ctor_set(v___x_802_, 0, v___x_804_);
v___x_806_ = v___x_802_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v___x_804_);
v___x_806_ = v_reuseFailAlloc_807_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
return v___x_806_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson_spec__1(lean_object* v_j_809_, lean_object* v_k_810_){
_start:
{
lean_object* v___x_811_; lean_object* v___x_812_; 
v___x_811_ = l_Lean_Json_getObjValD(v_j_809_, v_k_810_);
v___x_812_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson_spec__1_spec__1(v___x_811_);
return v___x_812_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson_spec__1___boxed(lean_object* v_j_813_, lean_object* v_k_814_){
_start:
{
lean_object* v_res_815_; 
v_res_815_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson_spec__1(v_j_813_, v_k_814_);
lean_dec_ref(v_k_814_);
return v_res_815_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__2(void){
_start:
{
uint8_t v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; 
v___x_821_ = 1;
v___x_822_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__1));
v___x_823_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_822_, v___x_821_);
return v___x_823_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__3(void){
_start:
{
lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; 
v___x_824_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__5));
v___x_825_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__2, &l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__2);
v___x_826_ = lean_string_append(v___x_825_, v___x_824_);
return v___x_826_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; 
v___x_827_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__8);
v___x_828_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__3);
v___x_829_ = lean_string_append(v___x_828_, v___x_827_);
return v___x_829_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__5(void){
_start:
{
lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; 
v___x_830_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__10));
v___x_831_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__4);
v___x_832_ = lean_string_append(v___x_831_, v___x_830_);
return v___x_832_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__8(void){
_start:
{
uint8_t v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; 
v___x_836_ = 1;
v___x_837_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__7));
v___x_838_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_837_, v___x_836_);
return v___x_838_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__9(void){
_start:
{
lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; 
v___x_839_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__8);
v___x_840_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__3);
v___x_841_ = lean_string_append(v___x_840_, v___x_839_);
return v___x_841_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__10(void){
_start:
{
lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; 
v___x_842_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__10));
v___x_843_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__9, &l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__9);
v___x_844_ = lean_string_append(v___x_843_, v___x_842_);
return v___x_844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson(lean_object* v_json_845_){
_start:
{
lean_object* v___x_846_; lean_object* v___x_847_; 
v___x_846_ = ((lean_object*)(l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__0));
lean_inc(v_json_845_);
v___x_847_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson_spec__0(v_json_845_, v___x_846_);
if (lean_obj_tag(v___x_847_) == 0)
{
lean_object* v_a_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_857_; 
lean_dec(v_json_845_);
v_a_848_ = lean_ctor_get(v___x_847_, 0);
v_isSharedCheck_857_ = !lean_is_exclusive(v___x_847_);
if (v_isSharedCheck_857_ == 0)
{
v___x_850_ = v___x_847_;
v_isShared_851_ = v_isSharedCheck_857_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_a_848_);
lean_dec(v___x_847_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_857_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_855_; 
v___x_852_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__5, &l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__5);
v___x_853_ = lean_string_append(v___x_852_, v_a_848_);
lean_dec(v_a_848_);
if (v_isShared_851_ == 0)
{
lean_ctor_set(v___x_850_, 0, v___x_853_);
v___x_855_ = v___x_850_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v___x_853_);
v___x_855_ = v_reuseFailAlloc_856_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
return v___x_855_;
}
}
}
else
{
if (lean_obj_tag(v___x_847_) == 0)
{
lean_object* v_a_858_; lean_object* v___x_860_; uint8_t v_isShared_861_; uint8_t v_isSharedCheck_865_; 
lean_dec(v_json_845_);
v_a_858_ = lean_ctor_get(v___x_847_, 0);
v_isSharedCheck_865_ = !lean_is_exclusive(v___x_847_);
if (v_isSharedCheck_865_ == 0)
{
v___x_860_ = v___x_847_;
v_isShared_861_ = v_isSharedCheck_865_;
goto v_resetjp_859_;
}
else
{
lean_inc(v_a_858_);
lean_dec(v___x_847_);
v___x_860_ = lean_box(0);
v_isShared_861_ = v_isSharedCheck_865_;
goto v_resetjp_859_;
}
v_resetjp_859_:
{
lean_object* v___x_863_; 
if (v_isShared_861_ == 0)
{
lean_ctor_set_tag(v___x_860_, 0);
v___x_863_ = v___x_860_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v_a_858_);
v___x_863_ = v_reuseFailAlloc_864_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
return v___x_863_;
}
}
}
else
{
lean_object* v_a_866_; lean_object* v___x_867_; lean_object* v___x_868_; 
v_a_866_ = lean_ctor_get(v___x_847_, 0);
lean_inc(v_a_866_);
lean_dec_ref(v___x_847_);
v___x_867_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0___closed__0));
v___x_868_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson_spec__1(v_json_845_, v___x_867_);
if (lean_obj_tag(v___x_868_) == 0)
{
lean_object* v_a_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_878_; 
lean_dec(v_a_866_);
v_a_869_ = lean_ctor_get(v___x_868_, 0);
v_isSharedCheck_878_ = !lean_is_exclusive(v___x_868_);
if (v_isSharedCheck_878_ == 0)
{
v___x_871_ = v___x_868_;
v_isShared_872_ = v_isSharedCheck_878_;
goto v_resetjp_870_;
}
else
{
lean_inc(v_a_869_);
lean_dec(v___x_868_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_878_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_876_; 
v___x_873_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__10, &l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__10);
v___x_874_ = lean_string_append(v___x_873_, v_a_869_);
lean_dec(v_a_869_);
if (v_isShared_872_ == 0)
{
lean_ctor_set(v___x_871_, 0, v___x_874_);
v___x_876_ = v___x_871_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v___x_874_);
v___x_876_ = v_reuseFailAlloc_877_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
return v___x_876_;
}
}
}
else
{
if (lean_obj_tag(v___x_868_) == 0)
{
lean_object* v_a_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_886_; 
lean_dec(v_a_866_);
v_a_879_ = lean_ctor_get(v___x_868_, 0);
v_isSharedCheck_886_ = !lean_is_exclusive(v___x_868_);
if (v_isSharedCheck_886_ == 0)
{
v___x_881_ = v___x_868_;
v_isShared_882_ = v_isSharedCheck_886_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_a_879_);
lean_dec(v___x_868_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_886_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
lean_object* v___x_884_; 
if (v_isShared_882_ == 0)
{
lean_ctor_set_tag(v___x_881_, 0);
v___x_884_ = v___x_881_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v_a_879_);
v___x_884_ = v_reuseFailAlloc_885_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
return v___x_884_;
}
}
}
else
{
lean_object* v_a_887_; lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_895_; 
v_a_887_ = lean_ctor_get(v___x_868_, 0);
v_isSharedCheck_895_ = !lean_is_exclusive(v___x_868_);
if (v_isSharedCheck_895_ == 0)
{
v___x_889_ = v___x_868_;
v_isShared_890_ = v_isSharedCheck_895_;
goto v_resetjp_888_;
}
else
{
lean_inc(v_a_887_);
lean_dec(v___x_868_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_895_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
lean_object* v___x_891_; lean_object* v___x_893_; 
v___x_891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_891_, 0, v_a_866_);
lean_ctor_set(v___x_891_, 1, v_a_887_);
if (v_isShared_890_ == 0)
{
lean_ctor_set(v___x_889_, 0, v___x_891_);
v___x_893_ = v___x_889_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v___x_891_);
v___x_893_ = v_reuseFailAlloc_894_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
return v___x_893_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonSaveOptions_toJson(uint8_t v_x_899_){
_start:
{
lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; 
v___x_900_ = ((lean_object*)(l_Lean_Lsp_instToJsonSaveOptions_toJson___closed__0));
v___x_901_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_901_, 0, v_x_899_);
v___x_902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_902_, 0, v___x_900_);
lean_ctor_set(v___x_902_, 1, v___x_901_);
v___x_903_ = lean_box(0);
v___x_904_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_904_, 0, v___x_902_);
lean_ctor_set(v___x_904_, 1, v___x_903_);
v___x_905_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_905_, 0, v___x_904_);
lean_ctor_set(v___x_905_, 1, v___x_903_);
v___x_906_ = ((lean_object*)(l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__1));
v___x_907_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson_spec__0(v___x_905_, v___x_906_);
v___x_908_ = l_Lean_Json_mkObj(v___x_907_);
return v___x_908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonSaveOptions_toJson___boxed(lean_object* v_x_909_){
_start:
{
uint8_t v_x_29__boxed_910_; lean_object* v_res_911_; 
v_x_29__boxed_910_ = lean_unbox(v_x_909_);
v_res_911_ = l_Lean_Lsp_instToJsonSaveOptions_toJson(v_x_29__boxed_910_);
return v_res_911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonSaveOptions_fromJson_spec__0(lean_object* v_j_914_, lean_object* v_k_915_){
_start:
{
lean_object* v___x_916_; lean_object* v___x_917_; 
v___x_916_ = l_Lean_Json_getObjValD(v_j_914_, v_k_915_);
v___x_917_ = l_Lean_Json_getBool_x3f(v___x_916_);
lean_dec(v___x_916_);
return v___x_917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonSaveOptions_fromJson_spec__0___boxed(lean_object* v_j_918_, lean_object* v_k_919_){
_start:
{
lean_object* v_res_920_; 
v_res_920_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonSaveOptions_fromJson_spec__0(v_j_918_, v_k_919_);
lean_dec_ref(v_k_919_);
return v_res_920_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__2(void){
_start:
{
uint8_t v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; 
v___x_926_ = 1;
v___x_927_ = ((lean_object*)(l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__1));
v___x_928_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_927_, v___x_926_);
return v___x_928_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__3(void){
_start:
{
lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; 
v___x_929_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__5));
v___x_930_ = lean_obj_once(&l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__2, &l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__2);
v___x_931_ = lean_string_append(v___x_930_, v___x_929_);
return v___x_931_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__5(void){
_start:
{
uint8_t v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; 
v___x_934_ = 1;
v___x_935_ = ((lean_object*)(l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__4));
v___x_936_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_935_, v___x_934_);
return v___x_936_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__6(void){
_start:
{
lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; 
v___x_937_ = lean_obj_once(&l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__5, &l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__5);
v___x_938_ = lean_obj_once(&l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__3, &l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__3);
v___x_939_ = lean_string_append(v___x_938_, v___x_937_);
return v___x_939_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__7(void){
_start:
{
lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; 
v___x_940_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__10));
v___x_941_ = lean_obj_once(&l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__6, &l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__6);
v___x_942_ = lean_string_append(v___x_941_, v___x_940_);
return v___x_942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonSaveOptions_fromJson(lean_object* v_json_943_){
_start:
{
lean_object* v___x_944_; lean_object* v___x_945_; 
v___x_944_ = ((lean_object*)(l_Lean_Lsp_instToJsonSaveOptions_toJson___closed__0));
v___x_945_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonSaveOptions_fromJson_spec__0(v_json_943_, v___x_944_);
if (lean_obj_tag(v___x_945_) == 0)
{
lean_object* v_a_946_; lean_object* v___x_948_; uint8_t v_isShared_949_; uint8_t v_isSharedCheck_955_; 
v_a_946_ = lean_ctor_get(v___x_945_, 0);
v_isSharedCheck_955_ = !lean_is_exclusive(v___x_945_);
if (v_isSharedCheck_955_ == 0)
{
v___x_948_ = v___x_945_;
v_isShared_949_ = v_isSharedCheck_955_;
goto v_resetjp_947_;
}
else
{
lean_inc(v_a_946_);
lean_dec(v___x_945_);
v___x_948_ = lean_box(0);
v_isShared_949_ = v_isSharedCheck_955_;
goto v_resetjp_947_;
}
v_resetjp_947_:
{
lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_953_; 
v___x_950_ = lean_obj_once(&l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__7, &l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__7);
v___x_951_ = lean_string_append(v___x_950_, v_a_946_);
lean_dec(v_a_946_);
if (v_isShared_949_ == 0)
{
lean_ctor_set(v___x_948_, 0, v___x_951_);
v___x_953_ = v___x_948_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v___x_951_);
v___x_953_ = v_reuseFailAlloc_954_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
return v___x_953_;
}
}
}
else
{
if (lean_obj_tag(v___x_945_) == 0)
{
lean_object* v_a_956_; lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_963_; 
v_a_956_ = lean_ctor_get(v___x_945_, 0);
v_isSharedCheck_963_ = !lean_is_exclusive(v___x_945_);
if (v_isSharedCheck_963_ == 0)
{
v___x_958_ = v___x_945_;
v_isShared_959_ = v_isSharedCheck_963_;
goto v_resetjp_957_;
}
else
{
lean_inc(v_a_956_);
lean_dec(v___x_945_);
v___x_958_ = lean_box(0);
v_isShared_959_ = v_isSharedCheck_963_;
goto v_resetjp_957_;
}
v_resetjp_957_:
{
lean_object* v___x_961_; 
if (v_isShared_959_ == 0)
{
lean_ctor_set_tag(v___x_958_, 0);
v___x_961_ = v___x_958_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v_a_956_);
v___x_961_ = v_reuseFailAlloc_962_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
return v___x_961_;
}
}
}
else
{
lean_object* v_a_964_; lean_object* v___x_966_; uint8_t v_isShared_967_; uint8_t v_isSharedCheck_971_; 
v_a_964_ = lean_ctor_get(v___x_945_, 0);
v_isSharedCheck_971_ = !lean_is_exclusive(v___x_945_);
if (v_isSharedCheck_971_ == 0)
{
v___x_966_ = v___x_945_;
v_isShared_967_ = v_isSharedCheck_971_;
goto v_resetjp_965_;
}
else
{
lean_inc(v_a_964_);
lean_dec(v___x_945_);
v___x_966_ = lean_box(0);
v_isShared_967_ = v_isSharedCheck_971_;
goto v_resetjp_965_;
}
v_resetjp_965_:
{
lean_object* v___x_969_; 
if (v_isShared_967_ == 0)
{
v___x_969_ = v___x_966_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v_a_964_);
v___x_969_ = v_reuseFailAlloc_970_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
return v___x_969_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDidCloseTextDocumentParams_toJson(lean_object* v_x_974_){
_start:
{
lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; 
v___x_975_ = ((lean_object*)(l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__0));
v___x_976_ = l_Lean_Lsp_instToJsonTextDocumentIdentifier_toJson(v_x_974_);
v___x_977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_977_, 0, v___x_975_);
lean_ctor_set(v___x_977_, 1, v___x_976_);
v___x_978_ = lean_box(0);
v___x_979_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_979_, 0, v___x_977_);
lean_ctor_set(v___x_979_, 1, v___x_978_);
v___x_980_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_980_, 0, v___x_979_);
lean_ctor_set(v___x_980_, 1, v___x_978_);
v___x_981_ = ((lean_object*)(l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__1));
v___x_982_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson_spec__0(v___x_980_, v___x_981_);
v___x_983_ = l_Lean_Json_mkObj(v___x_982_);
return v___x_983_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__2(void){
_start:
{
uint8_t v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; 
v___x_991_ = 1;
v___x_992_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__1));
v___x_993_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_992_, v___x_991_);
return v___x_993_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__3(void){
_start:
{
lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; 
v___x_994_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__5));
v___x_995_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__2, &l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__2);
v___x_996_ = lean_string_append(v___x_995_, v___x_994_);
return v___x_996_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; 
v___x_997_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__8);
v___x_998_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__3);
v___x_999_ = lean_string_append(v___x_998_, v___x_997_);
return v___x_999_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__5(void){
_start:
{
lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; 
v___x_1000_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__10));
v___x_1001_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__4);
v___x_1002_ = lean_string_append(v___x_1001_, v___x_1000_);
return v___x_1002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson(lean_object* v_json_1003_){
_start:
{
lean_object* v___x_1004_; lean_object* v___x_1005_; 
v___x_1004_ = ((lean_object*)(l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__0));
v___x_1005_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson_spec__0(v_json_1003_, v___x_1004_);
if (lean_obj_tag(v___x_1005_) == 0)
{
lean_object* v_a_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1015_; 
v_a_1006_ = lean_ctor_get(v___x_1005_, 0);
v_isSharedCheck_1015_ = !lean_is_exclusive(v___x_1005_);
if (v_isSharedCheck_1015_ == 0)
{
v___x_1008_ = v___x_1005_;
v_isShared_1009_ = v_isSharedCheck_1015_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_a_1006_);
lean_dec(v___x_1005_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1015_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1013_; 
v___x_1010_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__5, &l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__5);
v___x_1011_ = lean_string_append(v___x_1010_, v_a_1006_);
lean_dec(v_a_1006_);
if (v_isShared_1009_ == 0)
{
lean_ctor_set(v___x_1008_, 0, v___x_1011_);
v___x_1013_ = v___x_1008_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v___x_1011_);
v___x_1013_ = v_reuseFailAlloc_1014_;
goto v_reusejp_1012_;
}
v_reusejp_1012_:
{
return v___x_1013_;
}
}
}
else
{
if (lean_obj_tag(v___x_1005_) == 0)
{
lean_object* v_a_1016_; lean_object* v___x_1018_; uint8_t v_isShared_1019_; uint8_t v_isSharedCheck_1023_; 
v_a_1016_ = lean_ctor_get(v___x_1005_, 0);
v_isSharedCheck_1023_ = !lean_is_exclusive(v___x_1005_);
if (v_isSharedCheck_1023_ == 0)
{
v___x_1018_ = v___x_1005_;
v_isShared_1019_ = v_isSharedCheck_1023_;
goto v_resetjp_1017_;
}
else
{
lean_inc(v_a_1016_);
lean_dec(v___x_1005_);
v___x_1018_ = lean_box(0);
v_isShared_1019_ = v_isSharedCheck_1023_;
goto v_resetjp_1017_;
}
v_resetjp_1017_:
{
lean_object* v___x_1021_; 
if (v_isShared_1019_ == 0)
{
lean_ctor_set_tag(v___x_1018_, 0);
v___x_1021_ = v___x_1018_;
goto v_reusejp_1020_;
}
else
{
lean_object* v_reuseFailAlloc_1022_; 
v_reuseFailAlloc_1022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1022_, 0, v_a_1016_);
v___x_1021_ = v_reuseFailAlloc_1022_;
goto v_reusejp_1020_;
}
v_reusejp_1020_:
{
return v___x_1021_;
}
}
}
else
{
lean_object* v_a_1024_; lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1031_; 
v_a_1024_ = lean_ctor_get(v___x_1005_, 0);
v_isSharedCheck_1031_ = !lean_is_exclusive(v___x_1005_);
if (v_isSharedCheck_1031_ == 0)
{
v___x_1026_ = v___x_1005_;
v_isShared_1027_ = v_isSharedCheck_1031_;
goto v_resetjp_1025_;
}
else
{
lean_inc(v_a_1024_);
lean_dec(v___x_1005_);
v___x_1026_ = lean_box(0);
v_isShared_1027_ = v_isSharedCheck_1031_;
goto v_resetjp_1025_;
}
v_resetjp_1025_:
{
lean_object* v___x_1029_; 
if (v_isShared_1027_ == 0)
{
v___x_1029_ = v___x_1026_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v_a_1024_);
v___x_1029_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
return v___x_1029_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson_spec__0(lean_object* v_k_1034_, lean_object* v_x_1035_){
_start:
{
if (lean_obj_tag(v_x_1035_) == 0)
{
lean_object* v___x_1036_; 
lean_dec_ref(v_k_1034_);
v___x_1036_ = lean_box(0);
return v___x_1036_;
}
else
{
lean_object* v_val_1037_; uint8_t v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; 
v_val_1037_ = lean_ctor_get(v_x_1035_, 0);
v___x_1038_ = lean_unbox(v_val_1037_);
v___x_1039_ = l_Lean_Lsp_instToJsonSaveOptions_toJson(v___x_1038_);
v___x_1040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1040_, 0, v_k_1034_);
lean_ctor_set(v___x_1040_, 1, v___x_1039_);
v___x_1041_ = lean_box(0);
v___x_1042_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1042_, 0, v___x_1040_);
lean_ctor_set(v___x_1042_, 1, v___x_1041_);
return v___x_1042_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson_spec__0___boxed(lean_object* v_k_1043_, lean_object* v_x_1044_){
_start:
{
lean_object* v_res_1045_; 
v_res_1045_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson_spec__0(v_k_1043_, v_x_1044_);
lean_dec(v_x_1044_);
return v_res_1045_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson(lean_object* v_x_1051_){
_start:
{
uint8_t v_openClose_1052_; uint8_t v_change_1053_; uint8_t v_willSave_1054_; uint8_t v_willSaveWaitUntil_1055_; lean_object* v_save_x3f_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___y_1064_; 
v_openClose_1052_ = lean_ctor_get_uint8(v_x_1051_, sizeof(void*)*1);
v_change_1053_ = lean_ctor_get_uint8(v_x_1051_, sizeof(void*)*1 + 1);
v_willSave_1054_ = lean_ctor_get_uint8(v_x_1051_, sizeof(void*)*1 + 2);
v_willSaveWaitUntil_1055_ = lean_ctor_get_uint8(v_x_1051_, sizeof(void*)*1 + 3);
v_save_x3f_1056_ = lean_ctor_get(v_x_1051_, 0);
v___x_1057_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__0));
v___x_1058_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1058_, 0, v_openClose_1052_);
v___x_1059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1059_, 0, v___x_1057_);
lean_ctor_set(v___x_1059_, 1, v___x_1058_);
v___x_1060_ = lean_box(0);
v___x_1061_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1061_, 0, v___x_1059_);
lean_ctor_set(v___x_1061_, 1, v___x_1060_);
v___x_1062_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__1));
switch(v_change_1053_)
{
case 0:
{
lean_object* v___x_1085_; 
v___x_1085_ = lean_obj_once(&l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__1, &l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__1_once, _init_l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__1);
v___y_1064_ = v___x_1085_;
goto v___jp_1063_;
}
case 1:
{
lean_object* v___x_1086_; 
v___x_1086_ = lean_obj_once(&l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__3, &l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__3_once, _init_l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__3);
v___y_1064_ = v___x_1086_;
goto v___jp_1063_;
}
default: 
{
lean_object* v___x_1087_; 
v___x_1087_ = lean_obj_once(&l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__5, &l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__5_once, _init_l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__5);
v___y_1064_ = v___x_1087_;
goto v___jp_1063_;
}
}
v___jp_1063_:
{
lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; 
v___x_1065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1065_, 0, v___x_1062_);
lean_ctor_set(v___x_1065_, 1, v___y_1064_);
v___x_1066_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1066_, 0, v___x_1065_);
lean_ctor_set(v___x_1066_, 1, v___x_1060_);
v___x_1067_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__2));
v___x_1068_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1068_, 0, v_willSave_1054_);
v___x_1069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1069_, 0, v___x_1067_);
lean_ctor_set(v___x_1069_, 1, v___x_1068_);
v___x_1070_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1069_);
lean_ctor_set(v___x_1070_, 1, v___x_1060_);
v___x_1071_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__3));
v___x_1072_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1072_, 0, v_willSaveWaitUntil_1055_);
v___x_1073_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1073_, 0, v___x_1071_);
lean_ctor_set(v___x_1073_, 1, v___x_1072_);
v___x_1074_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1074_, 0, v___x_1073_);
lean_ctor_set(v___x_1074_, 1, v___x_1060_);
v___x_1075_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__4));
v___x_1076_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson_spec__0(v___x_1075_, v_save_x3f_1056_);
v___x_1077_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1077_, 0, v___x_1076_);
lean_ctor_set(v___x_1077_, 1, v___x_1060_);
v___x_1078_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1078_, 0, v___x_1074_);
lean_ctor_set(v___x_1078_, 1, v___x_1077_);
v___x_1079_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1079_, 0, v___x_1070_);
lean_ctor_set(v___x_1079_, 1, v___x_1078_);
v___x_1080_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1080_, 0, v___x_1066_);
lean_ctor_set(v___x_1080_, 1, v___x_1079_);
v___x_1081_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1081_, 0, v___x_1061_);
lean_ctor_set(v___x_1081_, 1, v___x_1080_);
v___x_1082_ = ((lean_object*)(l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__1));
v___x_1083_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson_spec__0(v___x_1081_, v___x_1082_);
v___x_1084_ = l_Lean_Json_mkObj(v___x_1083_);
return v___x_1084_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___boxed(lean_object* v_x_1088_){
_start:
{
lean_object* v_res_1089_; 
v_res_1089_ = l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson(v_x_1088_);
lean_dec_ref(v_x_1088_);
return v_res_1089_;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson_spec__0_spec__0(lean_object* v_x_1094_){
_start:
{
if (lean_obj_tag(v_x_1094_) == 0)
{
lean_object* v___x_1095_; 
v___x_1095_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson_spec__0_spec__0___closed__0));
return v___x_1095_;
}
else
{
lean_object* v___x_1096_; 
v___x_1096_ = l_Lean_Lsp_instFromJsonSaveOptions_fromJson(v_x_1094_);
if (lean_obj_tag(v___x_1096_) == 0)
{
lean_object* v_a_1097_; lean_object* v___x_1099_; uint8_t v_isShared_1100_; uint8_t v_isSharedCheck_1104_; 
v_a_1097_ = lean_ctor_get(v___x_1096_, 0);
v_isSharedCheck_1104_ = !lean_is_exclusive(v___x_1096_);
if (v_isSharedCheck_1104_ == 0)
{
v___x_1099_ = v___x_1096_;
v_isShared_1100_ = v_isSharedCheck_1104_;
goto v_resetjp_1098_;
}
else
{
lean_inc(v_a_1097_);
lean_dec(v___x_1096_);
v___x_1099_ = lean_box(0);
v_isShared_1100_ = v_isSharedCheck_1104_;
goto v_resetjp_1098_;
}
v_resetjp_1098_:
{
lean_object* v___x_1102_; 
if (v_isShared_1100_ == 0)
{
v___x_1102_ = v___x_1099_;
goto v_reusejp_1101_;
}
else
{
lean_object* v_reuseFailAlloc_1103_; 
v_reuseFailAlloc_1103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1103_, 0, v_a_1097_);
v___x_1102_ = v_reuseFailAlloc_1103_;
goto v_reusejp_1101_;
}
v_reusejp_1101_:
{
return v___x_1102_;
}
}
}
else
{
lean_object* v_a_1105_; lean_object* v___x_1107_; uint8_t v_isShared_1108_; uint8_t v_isSharedCheck_1113_; 
v_a_1105_ = lean_ctor_get(v___x_1096_, 0);
v_isSharedCheck_1113_ = !lean_is_exclusive(v___x_1096_);
if (v_isSharedCheck_1113_ == 0)
{
v___x_1107_ = v___x_1096_;
v_isShared_1108_ = v_isSharedCheck_1113_;
goto v_resetjp_1106_;
}
else
{
lean_inc(v_a_1105_);
lean_dec(v___x_1096_);
v___x_1107_ = lean_box(0);
v_isShared_1108_ = v_isSharedCheck_1113_;
goto v_resetjp_1106_;
}
v_resetjp_1106_:
{
lean_object* v___x_1109_; lean_object* v___x_1111_; 
v___x_1109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1109_, 0, v_a_1105_);
if (v_isShared_1108_ == 0)
{
lean_ctor_set(v___x_1107_, 0, v___x_1109_);
v___x_1111_ = v___x_1107_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v___x_1109_);
v___x_1111_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
return v___x_1111_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson_spec__0(lean_object* v_j_1114_, lean_object* v_k_1115_){
_start:
{
lean_object* v___x_1116_; lean_object* v___x_1117_; 
v___x_1116_ = l_Lean_Json_getObjValD(v_j_1114_, v_k_1115_);
v___x_1117_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson_spec__0_spec__0(v___x_1116_);
return v___x_1117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson_spec__0___boxed(lean_object* v_j_1118_, lean_object* v_k_1119_){
_start:
{
lean_object* v_res_1120_; 
v_res_1120_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson_spec__0(v_j_1118_, v_k_1119_);
lean_dec_ref(v_k_1119_);
return v_res_1120_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__2(void){
_start:
{
uint8_t v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; 
v___x_1126_ = 1;
v___x_1127_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__1));
v___x_1128_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1127_, v___x_1126_);
return v___x_1128_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3(void){
_start:
{
lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; 
v___x_1129_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__5));
v___x_1130_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__2, &l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__2);
v___x_1131_ = lean_string_append(v___x_1130_, v___x_1129_);
return v___x_1131_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__5(void){
_start:
{
uint8_t v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; 
v___x_1134_ = 1;
v___x_1135_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__4));
v___x_1136_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1135_, v___x_1134_);
return v___x_1136_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__6(void){
_start:
{
lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; 
v___x_1137_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__5, &l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__5);
v___x_1138_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3, &l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3);
v___x_1139_ = lean_string_append(v___x_1138_, v___x_1137_);
return v___x_1139_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__7(void){
_start:
{
lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; 
v___x_1140_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__10));
v___x_1141_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__6, &l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__6);
v___x_1142_ = lean_string_append(v___x_1141_, v___x_1140_);
return v___x_1142_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__9(void){
_start:
{
uint8_t v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; 
v___x_1145_ = 1;
v___x_1146_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__8));
v___x_1147_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1146_, v___x_1145_);
return v___x_1147_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__10(void){
_start:
{
lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; 
v___x_1148_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__9, &l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__9);
v___x_1149_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3, &l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3);
v___x_1150_ = lean_string_append(v___x_1149_, v___x_1148_);
return v___x_1150_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__11(void){
_start:
{
lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; 
v___x_1151_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__10));
v___x_1152_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__10, &l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__10);
v___x_1153_ = lean_string_append(v___x_1152_, v___x_1151_);
return v___x_1153_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__13(void){
_start:
{
uint8_t v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; 
v___x_1156_ = 1;
v___x_1157_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__12));
v___x_1158_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1157_, v___x_1156_);
return v___x_1158_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__14(void){
_start:
{
lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; 
v___x_1159_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__13, &l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__13);
v___x_1160_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3, &l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3);
v___x_1161_ = lean_string_append(v___x_1160_, v___x_1159_);
return v___x_1161_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__15(void){
_start:
{
lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; 
v___x_1162_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__10));
v___x_1163_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__14, &l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__14_once, _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__14);
v___x_1164_ = lean_string_append(v___x_1163_, v___x_1162_);
return v___x_1164_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__17(void){
_start:
{
uint8_t v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; 
v___x_1167_ = 1;
v___x_1168_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__16));
v___x_1169_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1168_, v___x_1167_);
return v___x_1169_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__18(void){
_start:
{
lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; 
v___x_1170_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__17, &l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__17_once, _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__17);
v___x_1171_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3, &l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3);
v___x_1172_ = lean_string_append(v___x_1171_, v___x_1170_);
return v___x_1172_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__19(void){
_start:
{
lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; 
v___x_1173_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__10));
v___x_1174_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__18, &l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__18_once, _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__18);
v___x_1175_ = lean_string_append(v___x_1174_, v___x_1173_);
return v___x_1175_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__22(void){
_start:
{
uint8_t v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; 
v___x_1179_ = 1;
v___x_1180_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__21));
v___x_1181_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1180_, v___x_1179_);
return v___x_1181_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__23(void){
_start:
{
lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; 
v___x_1182_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__22, &l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__22_once, _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__22);
v___x_1183_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3, &l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3);
v___x_1184_ = lean_string_append(v___x_1183_, v___x_1182_);
return v___x_1184_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__24(void){
_start:
{
lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; 
v___x_1185_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__10));
v___x_1186_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__23, &l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__23_once, _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__23);
v___x_1187_ = lean_string_append(v___x_1186_, v___x_1185_);
return v___x_1187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson(lean_object* v_json_1188_){
_start:
{
lean_object* v___x_1189_; lean_object* v___x_1190_; 
v___x_1189_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__0));
lean_inc(v_json_1188_);
v___x_1190_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonSaveOptions_fromJson_spec__0(v_json_1188_, v___x_1189_);
if (lean_obj_tag(v___x_1190_) == 0)
{
lean_object* v_a_1191_; lean_object* v___x_1193_; uint8_t v_isShared_1194_; uint8_t v_isSharedCheck_1200_; 
lean_dec(v_json_1188_);
v_a_1191_ = lean_ctor_get(v___x_1190_, 0);
v_isSharedCheck_1200_ = !lean_is_exclusive(v___x_1190_);
if (v_isSharedCheck_1200_ == 0)
{
v___x_1193_ = v___x_1190_;
v_isShared_1194_ = v_isSharedCheck_1200_;
goto v_resetjp_1192_;
}
else
{
lean_inc(v_a_1191_);
lean_dec(v___x_1190_);
v___x_1193_ = lean_box(0);
v_isShared_1194_ = v_isSharedCheck_1200_;
goto v_resetjp_1192_;
}
v_resetjp_1192_:
{
lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1198_; 
v___x_1195_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__7, &l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__7);
v___x_1196_ = lean_string_append(v___x_1195_, v_a_1191_);
lean_dec(v_a_1191_);
if (v_isShared_1194_ == 0)
{
lean_ctor_set(v___x_1193_, 0, v___x_1196_);
v___x_1198_ = v___x_1193_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v___x_1196_);
v___x_1198_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
return v___x_1198_;
}
}
}
else
{
if (lean_obj_tag(v___x_1190_) == 0)
{
lean_object* v_a_1201_; lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1208_; 
lean_dec(v_json_1188_);
v_a_1201_ = lean_ctor_get(v___x_1190_, 0);
v_isSharedCheck_1208_ = !lean_is_exclusive(v___x_1190_);
if (v_isSharedCheck_1208_ == 0)
{
v___x_1203_ = v___x_1190_;
v_isShared_1204_ = v_isSharedCheck_1208_;
goto v_resetjp_1202_;
}
else
{
lean_inc(v_a_1201_);
lean_dec(v___x_1190_);
v___x_1203_ = lean_box(0);
v_isShared_1204_ = v_isSharedCheck_1208_;
goto v_resetjp_1202_;
}
v_resetjp_1202_:
{
lean_object* v___x_1206_; 
if (v_isShared_1204_ == 0)
{
lean_ctor_set_tag(v___x_1203_, 0);
v___x_1206_ = v___x_1203_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v_a_1201_);
v___x_1206_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
return v___x_1206_;
}
}
}
else
{
lean_object* v_a_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; 
v_a_1209_ = lean_ctor_get(v___x_1190_, 0);
lean_inc(v_a_1209_);
lean_dec_ref(v___x_1190_);
v___x_1210_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__1));
lean_inc(v_json_1188_);
v___x_1211_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__1(v_json_1188_, v___x_1210_);
if (lean_obj_tag(v___x_1211_) == 0)
{
lean_object* v_a_1212_; lean_object* v___x_1214_; uint8_t v_isShared_1215_; uint8_t v_isSharedCheck_1221_; 
lean_dec(v_a_1209_);
lean_dec(v_json_1188_);
v_a_1212_ = lean_ctor_get(v___x_1211_, 0);
v_isSharedCheck_1221_ = !lean_is_exclusive(v___x_1211_);
if (v_isSharedCheck_1221_ == 0)
{
v___x_1214_ = v___x_1211_;
v_isShared_1215_ = v_isSharedCheck_1221_;
goto v_resetjp_1213_;
}
else
{
lean_inc(v_a_1212_);
lean_dec(v___x_1211_);
v___x_1214_ = lean_box(0);
v_isShared_1215_ = v_isSharedCheck_1221_;
goto v_resetjp_1213_;
}
v_resetjp_1213_:
{
lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1219_; 
v___x_1216_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__11, &l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__11);
v___x_1217_ = lean_string_append(v___x_1216_, v_a_1212_);
lean_dec(v_a_1212_);
if (v_isShared_1215_ == 0)
{
lean_ctor_set(v___x_1214_, 0, v___x_1217_);
v___x_1219_ = v___x_1214_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v___x_1217_);
v___x_1219_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
return v___x_1219_;
}
}
}
else
{
if (lean_obj_tag(v___x_1211_) == 0)
{
lean_object* v_a_1222_; lean_object* v___x_1224_; uint8_t v_isShared_1225_; uint8_t v_isSharedCheck_1229_; 
lean_dec(v_a_1209_);
lean_dec(v_json_1188_);
v_a_1222_ = lean_ctor_get(v___x_1211_, 0);
v_isSharedCheck_1229_ = !lean_is_exclusive(v___x_1211_);
if (v_isSharedCheck_1229_ == 0)
{
v___x_1224_ = v___x_1211_;
v_isShared_1225_ = v_isSharedCheck_1229_;
goto v_resetjp_1223_;
}
else
{
lean_inc(v_a_1222_);
lean_dec(v___x_1211_);
v___x_1224_ = lean_box(0);
v_isShared_1225_ = v_isSharedCheck_1229_;
goto v_resetjp_1223_;
}
v_resetjp_1223_:
{
lean_object* v___x_1227_; 
if (v_isShared_1225_ == 0)
{
lean_ctor_set_tag(v___x_1224_, 0);
v___x_1227_ = v___x_1224_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v_a_1222_);
v___x_1227_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
return v___x_1227_;
}
}
}
else
{
lean_object* v_a_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; 
v_a_1230_ = lean_ctor_get(v___x_1211_, 0);
lean_inc(v_a_1230_);
lean_dec_ref(v___x_1211_);
v___x_1231_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__2));
lean_inc(v_json_1188_);
v___x_1232_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonSaveOptions_fromJson_spec__0(v_json_1188_, v___x_1231_);
if (lean_obj_tag(v___x_1232_) == 0)
{
lean_object* v_a_1233_; lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1242_; 
lean_dec(v_a_1230_);
lean_dec(v_a_1209_);
lean_dec(v_json_1188_);
v_a_1233_ = lean_ctor_get(v___x_1232_, 0);
v_isSharedCheck_1242_ = !lean_is_exclusive(v___x_1232_);
if (v_isSharedCheck_1242_ == 0)
{
v___x_1235_ = v___x_1232_;
v_isShared_1236_ = v_isSharedCheck_1242_;
goto v_resetjp_1234_;
}
else
{
lean_inc(v_a_1233_);
lean_dec(v___x_1232_);
v___x_1235_ = lean_box(0);
v_isShared_1236_ = v_isSharedCheck_1242_;
goto v_resetjp_1234_;
}
v_resetjp_1234_:
{
lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1240_; 
v___x_1237_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__15, &l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__15_once, _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__15);
v___x_1238_ = lean_string_append(v___x_1237_, v_a_1233_);
lean_dec(v_a_1233_);
if (v_isShared_1236_ == 0)
{
lean_ctor_set(v___x_1235_, 0, v___x_1238_);
v___x_1240_ = v___x_1235_;
goto v_reusejp_1239_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v___x_1238_);
v___x_1240_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1239_;
}
v_reusejp_1239_:
{
return v___x_1240_;
}
}
}
else
{
if (lean_obj_tag(v___x_1232_) == 0)
{
lean_object* v_a_1243_; lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1250_; 
lean_dec(v_a_1230_);
lean_dec(v_a_1209_);
lean_dec(v_json_1188_);
v_a_1243_ = lean_ctor_get(v___x_1232_, 0);
v_isSharedCheck_1250_ = !lean_is_exclusive(v___x_1232_);
if (v_isSharedCheck_1250_ == 0)
{
v___x_1245_ = v___x_1232_;
v_isShared_1246_ = v_isSharedCheck_1250_;
goto v_resetjp_1244_;
}
else
{
lean_inc(v_a_1243_);
lean_dec(v___x_1232_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1250_;
goto v_resetjp_1244_;
}
v_resetjp_1244_:
{
lean_object* v___x_1248_; 
if (v_isShared_1246_ == 0)
{
lean_ctor_set_tag(v___x_1245_, 0);
v___x_1248_ = v___x_1245_;
goto v_reusejp_1247_;
}
else
{
lean_object* v_reuseFailAlloc_1249_; 
v_reuseFailAlloc_1249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1249_, 0, v_a_1243_);
v___x_1248_ = v_reuseFailAlloc_1249_;
goto v_reusejp_1247_;
}
v_reusejp_1247_:
{
return v___x_1248_;
}
}
}
else
{
lean_object* v_a_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; 
v_a_1251_ = lean_ctor_get(v___x_1232_, 0);
lean_inc(v_a_1251_);
lean_dec_ref(v___x_1232_);
v___x_1252_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__3));
lean_inc(v_json_1188_);
v___x_1253_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonSaveOptions_fromJson_spec__0(v_json_1188_, v___x_1252_);
if (lean_obj_tag(v___x_1253_) == 0)
{
lean_object* v_a_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1263_; 
lean_dec(v_a_1251_);
lean_dec(v_a_1230_);
lean_dec(v_a_1209_);
lean_dec(v_json_1188_);
v_a_1254_ = lean_ctor_get(v___x_1253_, 0);
v_isSharedCheck_1263_ = !lean_is_exclusive(v___x_1253_);
if (v_isSharedCheck_1263_ == 0)
{
v___x_1256_ = v___x_1253_;
v_isShared_1257_ = v_isSharedCheck_1263_;
goto v_resetjp_1255_;
}
else
{
lean_inc(v_a_1254_);
lean_dec(v___x_1253_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1263_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1261_; 
v___x_1258_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__19, &l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__19_once, _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__19);
v___x_1259_ = lean_string_append(v___x_1258_, v_a_1254_);
lean_dec(v_a_1254_);
if (v_isShared_1257_ == 0)
{
lean_ctor_set(v___x_1256_, 0, v___x_1259_);
v___x_1261_ = v___x_1256_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v___x_1259_);
v___x_1261_ = v_reuseFailAlloc_1262_;
goto v_reusejp_1260_;
}
v_reusejp_1260_:
{
return v___x_1261_;
}
}
}
else
{
if (lean_obj_tag(v___x_1253_) == 0)
{
lean_object* v_a_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1271_; 
lean_dec(v_a_1251_);
lean_dec(v_a_1230_);
lean_dec(v_a_1209_);
lean_dec(v_json_1188_);
v_a_1264_ = lean_ctor_get(v___x_1253_, 0);
v_isSharedCheck_1271_ = !lean_is_exclusive(v___x_1253_);
if (v_isSharedCheck_1271_ == 0)
{
v___x_1266_ = v___x_1253_;
v_isShared_1267_ = v_isSharedCheck_1271_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_a_1264_);
lean_dec(v___x_1253_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1271_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
lean_object* v___x_1269_; 
if (v_isShared_1267_ == 0)
{
lean_ctor_set_tag(v___x_1266_, 0);
v___x_1269_ = v___x_1266_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v_a_1264_);
v___x_1269_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
return v___x_1269_;
}
}
}
else
{
lean_object* v_a_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; 
v_a_1272_ = lean_ctor_get(v___x_1253_, 0);
lean_inc(v_a_1272_);
lean_dec_ref(v___x_1253_);
v___x_1273_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__4));
v___x_1274_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson_spec__0(v_json_1188_, v___x_1273_);
if (lean_obj_tag(v___x_1274_) == 0)
{
lean_object* v_a_1275_; lean_object* v___x_1277_; uint8_t v_isShared_1278_; uint8_t v_isSharedCheck_1284_; 
lean_dec(v_a_1272_);
lean_dec(v_a_1251_);
lean_dec(v_a_1230_);
lean_dec(v_a_1209_);
v_a_1275_ = lean_ctor_get(v___x_1274_, 0);
v_isSharedCheck_1284_ = !lean_is_exclusive(v___x_1274_);
if (v_isSharedCheck_1284_ == 0)
{
v___x_1277_ = v___x_1274_;
v_isShared_1278_ = v_isSharedCheck_1284_;
goto v_resetjp_1276_;
}
else
{
lean_inc(v_a_1275_);
lean_dec(v___x_1274_);
v___x_1277_ = lean_box(0);
v_isShared_1278_ = v_isSharedCheck_1284_;
goto v_resetjp_1276_;
}
v_resetjp_1276_:
{
lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1282_; 
v___x_1279_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__24, &l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__24_once, _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__24);
v___x_1280_ = lean_string_append(v___x_1279_, v_a_1275_);
lean_dec(v_a_1275_);
if (v_isShared_1278_ == 0)
{
lean_ctor_set(v___x_1277_, 0, v___x_1280_);
v___x_1282_ = v___x_1277_;
goto v_reusejp_1281_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v___x_1280_);
v___x_1282_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1281_;
}
v_reusejp_1281_:
{
return v___x_1282_;
}
}
}
else
{
if (lean_obj_tag(v___x_1274_) == 0)
{
lean_object* v_a_1285_; lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1292_; 
lean_dec(v_a_1272_);
lean_dec(v_a_1251_);
lean_dec(v_a_1230_);
lean_dec(v_a_1209_);
v_a_1285_ = lean_ctor_get(v___x_1274_, 0);
v_isSharedCheck_1292_ = !lean_is_exclusive(v___x_1274_);
if (v_isSharedCheck_1292_ == 0)
{
v___x_1287_ = v___x_1274_;
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
else
{
lean_inc(v_a_1285_);
lean_dec(v___x_1274_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
lean_object* v___x_1290_; 
if (v_isShared_1288_ == 0)
{
lean_ctor_set_tag(v___x_1287_, 0);
v___x_1290_ = v___x_1287_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v_a_1285_);
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
lean_object* v_a_1293_; lean_object* v___x_1295_; uint8_t v_isShared_1296_; uint8_t v_isSharedCheck_1305_; 
v_a_1293_ = lean_ctor_get(v___x_1274_, 0);
v_isSharedCheck_1305_ = !lean_is_exclusive(v___x_1274_);
if (v_isSharedCheck_1305_ == 0)
{
v___x_1295_ = v___x_1274_;
v_isShared_1296_ = v_isSharedCheck_1305_;
goto v_resetjp_1294_;
}
else
{
lean_inc(v_a_1293_);
lean_dec(v___x_1274_);
v___x_1295_ = lean_box(0);
v_isShared_1296_ = v_isSharedCheck_1305_;
goto v_resetjp_1294_;
}
v_resetjp_1294_:
{
lean_object* v___x_1297_; uint8_t v___x_1298_; uint8_t v___x_1299_; uint8_t v___x_1300_; uint8_t v___x_1301_; lean_object* v___x_1303_; 
v___x_1297_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v___x_1297_, 0, v_a_1293_);
v___x_1298_ = lean_unbox(v_a_1209_);
lean_dec(v_a_1209_);
lean_ctor_set_uint8(v___x_1297_, sizeof(void*)*1, v___x_1298_);
v___x_1299_ = lean_unbox(v_a_1230_);
lean_dec(v_a_1230_);
lean_ctor_set_uint8(v___x_1297_, sizeof(void*)*1 + 1, v___x_1299_);
v___x_1300_ = lean_unbox(v_a_1251_);
lean_dec(v_a_1251_);
lean_ctor_set_uint8(v___x_1297_, sizeof(void*)*1 + 2, v___x_1300_);
v___x_1301_ = lean_unbox(v_a_1272_);
lean_dec(v_a_1272_);
lean_ctor_set_uint8(v___x_1297_, sizeof(void*)*1 + 3, v___x_1301_);
if (v_isShared_1296_ == 0)
{
lean_ctor_set(v___x_1295_, 0, v___x_1297_);
v___x_1303_ = v___x_1295_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1304_; 
v_reuseFailAlloc_1304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1304_, 0, v___x_1297_);
v___x_1303_ = v_reuseFailAlloc_1304_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
return v___x_1303_;
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
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_Lsp_TextSync(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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

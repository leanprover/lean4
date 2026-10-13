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
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentSyncKind_ctorIdx___impl(uint8_t v_x_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(v_x_1_);
v___x_3_ = lean_obj_tag_nat(v___x_2_);
lean_dec(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentSyncKind_ctorIdx___impl___boxed(lean_object* v_x_4_){
_start:
{
uint8_t v_x_4__boxed_5_; lean_object* v_res_6_; 
v_x_4__boxed_5_ = lean_unbox(v_x_4_);
v_res_6_ = l_Lean_Lsp_TextDocumentSyncKind_ctorIdx___impl(v_x_4__boxed_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentSyncKind_ctorElim___redArg(lean_object* v_k_7_){
_start:
{
lean_inc(v_k_7_);
return v_k_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentSyncKind_ctorElim___redArg___boxed(lean_object* v_k_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Lean_Lsp_TextDocumentSyncKind_ctorElim___redArg(v_k_8_);
lean_dec(v_k_8_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentSyncKind_ctorElim(lean_object* v_motive_10_, lean_object* v_ctorIdx_11_, uint8_t v_t_12_, lean_object* v_h_13_, lean_object* v_k_14_){
_start:
{
lean_inc(v_k_14_);
return v_k_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentSyncKind_ctorElim___boxed(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, lean_object* v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
uint8_t v_t_boxed_20_; lean_object* v_res_21_; 
v_t_boxed_20_ = lean_unbox(v_t_17_);
v_res_21_ = l_Lean_Lsp_TextDocumentSyncKind_ctorElim(v_motive_15_, v_ctorIdx_16_, v_t_boxed_20_, v_h_18_, v_k_19_);
lean_dec(v_k_19_);
lean_dec(v_ctorIdx_16_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentSyncKind_none_elim___redArg(lean_object* v_none_22_){
_start:
{
lean_inc(v_none_22_);
return v_none_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentSyncKind_none_elim___redArg___boxed(lean_object* v_none_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Lean_Lsp_TextDocumentSyncKind_none_elim___redArg(v_none_23_);
lean_dec(v_none_23_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentSyncKind_none_elim(lean_object* v_motive_25_, uint8_t v_t_26_, lean_object* v_h_27_, lean_object* v_none_28_){
_start:
{
lean_inc(v_none_28_);
return v_none_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentSyncKind_none_elim___boxed(lean_object* v_motive_29_, lean_object* v_t_30_, lean_object* v_h_31_, lean_object* v_none_32_){
_start:
{
uint8_t v_t_boxed_33_; lean_object* v_res_34_; 
v_t_boxed_33_ = lean_unbox(v_t_30_);
v_res_34_ = l_Lean_Lsp_TextDocumentSyncKind_none_elim(v_motive_29_, v_t_boxed_33_, v_h_31_, v_none_32_);
lean_dec(v_none_32_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentSyncKind_full_elim___redArg(lean_object* v_full_35_){
_start:
{
lean_inc(v_full_35_);
return v_full_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentSyncKind_full_elim___redArg___boxed(lean_object* v_full_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Lean_Lsp_TextDocumentSyncKind_full_elim___redArg(v_full_36_);
lean_dec(v_full_36_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentSyncKind_full_elim(lean_object* v_motive_38_, uint8_t v_t_39_, lean_object* v_h_40_, lean_object* v_full_41_){
_start:
{
lean_inc(v_full_41_);
return v_full_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentSyncKind_full_elim___boxed(lean_object* v_motive_42_, lean_object* v_t_43_, lean_object* v_h_44_, lean_object* v_full_45_){
_start:
{
uint8_t v_t_boxed_46_; lean_object* v_res_47_; 
v_t_boxed_46_ = lean_unbox(v_t_43_);
v_res_47_ = l_Lean_Lsp_TextDocumentSyncKind_full_elim(v_motive_42_, v_t_boxed_46_, v_h_44_, v_full_45_);
lean_dec(v_full_45_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentSyncKind_incremental_elim___redArg(lean_object* v_incremental_48_){
_start:
{
lean_inc(v_incremental_48_);
return v_incremental_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentSyncKind_incremental_elim___redArg___boxed(lean_object* v_incremental_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_Lean_Lsp_TextDocumentSyncKind_incremental_elim___redArg(v_incremental_49_);
lean_dec(v_incremental_49_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentSyncKind_incremental_elim(lean_object* v_motive_51_, uint8_t v_t_52_, lean_object* v_h_53_, lean_object* v_incremental_54_){
_start:
{
lean_inc(v_incremental_54_);
return v_incremental_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentSyncKind_incremental_elim___boxed(lean_object* v_motive_55_, lean_object* v_t_56_, lean_object* v_h_57_, lean_object* v_incremental_58_){
_start:
{
uint8_t v_t_boxed_59_; lean_object* v_res_60_; 
v_t_boxed_59_ = lean_unbox(v_t_56_);
v_res_60_ = l_Lean_Lsp_TextDocumentSyncKind_incremental_elim(v_motive_55_, v_t_boxed_59_, v_h_57_, v_incremental_58_);
lean_dec(v_incremental_58_);
return v_res_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0(lean_object* v_j_73_){
_start:
{
lean_object* v___x_76_; 
v___x_76_ = l_Lean_Json_getNat_x3f(v_j_73_);
if (lean_obj_tag(v___x_76_) == 1)
{
lean_object* v_a_77_; lean_object* v___x_78_; uint8_t v___x_79_; 
v_a_77_ = lean_ctor_get(v___x_76_, 0);
lean_inc(v_a_77_);
lean_dec_ref_known(v___x_76_, 1);
v___x_78_ = lean_unsigned_to_nat(0u);
v___x_79_ = lean_nat_dec_eq(v_a_77_, v___x_78_);
if (v___x_79_ == 0)
{
lean_object* v___x_80_; uint8_t v___x_81_; 
v___x_80_ = lean_unsigned_to_nat(1u);
v___x_81_ = lean_nat_dec_eq(v_a_77_, v___x_80_);
if (v___x_81_ == 0)
{
lean_object* v___x_82_; uint8_t v___x_83_; 
v___x_82_ = lean_unsigned_to_nat(2u);
v___x_83_ = lean_nat_dec_eq(v_a_77_, v___x_82_);
lean_dec(v_a_77_);
if (v___x_83_ == 0)
{
goto v___jp_74_;
}
else
{
lean_object* v___x_84_; 
v___x_84_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0___closed__2));
return v___x_84_;
}
}
else
{
lean_object* v___x_85_; 
lean_dec(v_a_77_);
v___x_85_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0___closed__3));
return v___x_85_;
}
}
else
{
lean_object* v___x_86_; 
lean_dec(v_a_77_);
v___x_86_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0___closed__4));
return v___x_86_;
}
}
else
{
lean_dec_ref(v___x_76_);
goto v___jp_74_;
}
v___jp_74_:
{
lean_object* v___x_75_; 
v___x_75_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0___closed__1));
return v___x_75_;
}
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__0(void){
_start:
{
lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_89_ = lean_unsigned_to_nat(0u);
v___x_90_ = l_Lean_JsonNumber_fromNat(v___x_89_);
return v___x_90_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__1(void){
_start:
{
lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_91_ = lean_obj_once(&l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__0, &l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__0_once, _init_l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__0);
v___x_92_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_92_, 0, v___x_91_);
return v___x_92_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__2(void){
_start:
{
lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_93_ = lean_unsigned_to_nat(1u);
v___x_94_ = l_Lean_JsonNumber_fromNat(v___x_93_);
return v___x_94_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__3(void){
_start:
{
lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_95_ = lean_obj_once(&l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__2, &l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__2_once, _init_l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__2);
v___x_96_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_96_, 0, v___x_95_);
return v___x_96_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__4(void){
_start:
{
lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_97_ = lean_unsigned_to_nat(2u);
v___x_98_ = l_Lean_JsonNumber_fromNat(v___x_97_);
return v___x_98_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__5(void){
_start:
{
lean_object* v___x_99_; lean_object* v___x_100_; 
v___x_99_ = lean_obj_once(&l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__4, &l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__4_once, _init_l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__4);
v___x_100_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_100_, 0, v___x_99_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0(uint8_t v_x_101_){
_start:
{
switch(v_x_101_)
{
case 0:
{
lean_object* v___x_102_; 
v___x_102_ = lean_obj_once(&l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__1, &l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__1_once, _init_l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__1);
return v___x_102_;
}
case 1:
{
lean_object* v___x_103_; 
v___x_103_ = lean_obj_once(&l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__3, &l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__3_once, _init_l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__3);
return v___x_103_;
}
default: 
{
lean_object* v___x_104_; 
v___x_104_ = lean_obj_once(&l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__5, &l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__5_once, _init_l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__5);
return v___x_104_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___boxed(lean_object* v_x_105_){
_start:
{
uint8_t v_x_81__boxed_106_; lean_object* v_res_107_; 
v_x_81__boxed_106_ = lean_unbox(v_x_105_);
v_res_107_ = l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0(v_x_81__boxed_106_);
return v_res_107_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson_spec__0(lean_object* v_a_110_, lean_object* v_a_111_){
_start:
{
if (lean_obj_tag(v_a_110_) == 0)
{
lean_object* v___x_112_; 
v___x_112_ = lean_array_to_list(v_a_111_);
return v___x_112_;
}
else
{
lean_object* v_head_113_; lean_object* v_tail_114_; lean_object* v___x_115_; 
v_head_113_ = lean_ctor_get(v_a_110_, 0);
lean_inc(v_head_113_);
v_tail_114_ = lean_ctor_get(v_a_110_, 1);
lean_inc(v_tail_114_);
lean_dec_ref_known(v_a_110_, 2);
v___x_115_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_111_, v_head_113_);
v_a_110_ = v_tail_114_;
v_a_111_ = v___x_115_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson(lean_object* v_x_120_){
_start:
{
lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_121_ = ((lean_object*)(l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__0));
v___x_122_ = l_Lean_Lsp_instToJsonTextDocumentItem_toJson(v_x_120_);
v___x_123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_123_, 0, v___x_121_);
lean_ctor_set(v___x_123_, 1, v___x_122_);
v___x_124_ = lean_box(0);
v___x_125_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_125_, 0, v___x_123_);
lean_ctor_set(v___x_125_, 1, v___x_124_);
v___x_126_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_126_, 0, v___x_125_);
lean_ctor_set(v___x_126_, 1, v___x_124_);
v___x_127_ = ((lean_object*)(l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__1));
v___x_128_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson_spec__0(v___x_126_, v___x_127_);
v___x_129_ = l_Lean_Json_mkObj(v___x_128_);
lean_dec(v___x_128_);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson_spec__0(lean_object* v_j_132_, lean_object* v_k_133_){
_start:
{
lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_134_ = l_Lean_Json_getObjValD(v_j_132_, v_k_133_);
v___x_135_ = l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson(v___x_134_);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson_spec__0___boxed(lean_object* v_j_136_, lean_object* v_k_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson_spec__0(v_j_136_, v_k_137_);
lean_dec_ref(v_k_137_);
return v_res_138_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__4(void){
_start:
{
uint8_t v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_146_ = 1;
v___x_147_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__3));
v___x_148_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_147_, v___x_146_);
return v___x_148_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__6(void){
_start:
{
lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; 
v___x_150_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__5));
v___x_151_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__4);
v___x_152_ = lean_string_append(v___x_151_, v___x_150_);
return v___x_152_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__8(void){
_start:
{
uint8_t v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_155_ = 1;
v___x_156_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__7));
v___x_157_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_156_, v___x_155_);
return v___x_157_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__9(void){
_start:
{
lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_158_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__8);
v___x_159_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__6, &l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__6);
v___x_160_ = lean_string_append(v___x_159_, v___x_158_);
return v___x_160_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__11(void){
_start:
{
lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_162_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__10));
v___x_163_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__9, &l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__9);
v___x_164_ = lean_string_append(v___x_163_, v___x_162_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson(lean_object* v_json_165_){
_start:
{
lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_166_ = ((lean_object*)(l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__0));
v___x_167_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson_spec__0(v_json_165_, v___x_166_);
if (lean_obj_tag(v___x_167_) == 0)
{
lean_object* v_a_168_; lean_object* v___x_170_; uint8_t v_isShared_171_; uint8_t v_isSharedCheck_177_; 
v_a_168_ = lean_ctor_get(v___x_167_, 0);
v_isSharedCheck_177_ = !lean_is_exclusive(v___x_167_);
if (v_isSharedCheck_177_ == 0)
{
v___x_170_ = v___x_167_;
v_isShared_171_ = v_isSharedCheck_177_;
goto v_resetjp_169_;
}
else
{
lean_inc(v_a_168_);
lean_dec(v___x_167_);
v___x_170_ = lean_box(0);
v_isShared_171_ = v_isSharedCheck_177_;
goto v_resetjp_169_;
}
v_resetjp_169_:
{
lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_175_; 
v___x_172_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__11, &l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__11);
v___x_173_ = lean_string_append(v___x_172_, v_a_168_);
lean_dec(v_a_168_);
if (v_isShared_171_ == 0)
{
lean_ctor_set(v___x_170_, 0, v___x_173_);
v___x_175_ = v___x_170_;
goto v_reusejp_174_;
}
else
{
lean_object* v_reuseFailAlloc_176_; 
v_reuseFailAlloc_176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_176_, 0, v___x_173_);
v___x_175_ = v_reuseFailAlloc_176_;
goto v_reusejp_174_;
}
v_reusejp_174_:
{
return v___x_175_;
}
}
}
else
{
if (lean_obj_tag(v___x_167_) == 0)
{
lean_object* v_a_178_; lean_object* v___x_180_; uint8_t v_isShared_181_; uint8_t v_isSharedCheck_185_; 
v_a_178_ = lean_ctor_get(v___x_167_, 0);
v_isSharedCheck_185_ = !lean_is_exclusive(v___x_167_);
if (v_isSharedCheck_185_ == 0)
{
v___x_180_ = v___x_167_;
v_isShared_181_ = v_isSharedCheck_185_;
goto v_resetjp_179_;
}
else
{
lean_inc(v_a_178_);
lean_dec(v___x_167_);
v___x_180_ = lean_box(0);
v_isShared_181_ = v_isSharedCheck_185_;
goto v_resetjp_179_;
}
v_resetjp_179_:
{
lean_object* v___x_183_; 
if (v_isShared_181_ == 0)
{
lean_ctor_set_tag(v___x_180_, 0);
v___x_183_ = v___x_180_;
goto v_reusejp_182_;
}
else
{
lean_object* v_reuseFailAlloc_184_; 
v_reuseFailAlloc_184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_184_, 0, v_a_178_);
v___x_183_ = v_reuseFailAlloc_184_;
goto v_reusejp_182_;
}
v_reusejp_182_:
{
return v___x_183_;
}
}
}
else
{
lean_object* v_a_186_; lean_object* v___x_188_; uint8_t v_isShared_189_; uint8_t v_isSharedCheck_193_; 
v_a_186_ = lean_ctor_get(v___x_167_, 0);
v_isSharedCheck_193_ = !lean_is_exclusive(v___x_167_);
if (v_isSharedCheck_193_ == 0)
{
v___x_188_ = v___x_167_;
v_isShared_189_ = v_isSharedCheck_193_;
goto v_resetjp_187_;
}
else
{
lean_inc(v_a_186_);
lean_dec(v___x_167_);
v___x_188_ = lean_box(0);
v_isShared_189_ = v_isSharedCheck_193_;
goto v_resetjp_187_;
}
v_resetjp_187_:
{
lean_object* v___x_191_; 
if (v_isShared_189_ == 0)
{
v___x_191_ = v___x_188_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_192_; 
v_reuseFailAlloc_192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_192_, 0, v_a_186_);
v___x_191_ = v_reuseFailAlloc_192_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
return v___x_191_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__1(lean_object* v_j_196_, lean_object* v_k_197_){
_start:
{
lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_200_ = l_Lean_Json_getObjValD(v_j_196_, v_k_197_);
v___x_201_ = l_Lean_Json_getNat_x3f(v___x_200_);
if (lean_obj_tag(v___x_201_) == 1)
{
lean_object* v_a_202_; lean_object* v___x_203_; uint8_t v___x_204_; 
v_a_202_ = lean_ctor_get(v___x_201_, 0);
lean_inc(v_a_202_);
lean_dec_ref_known(v___x_201_, 1);
v___x_203_ = lean_unsigned_to_nat(0u);
v___x_204_ = lean_nat_dec_eq(v_a_202_, v___x_203_);
if (v___x_204_ == 0)
{
lean_object* v___x_205_; uint8_t v___x_206_; 
v___x_205_ = lean_unsigned_to_nat(1u);
v___x_206_ = lean_nat_dec_eq(v_a_202_, v___x_205_);
if (v___x_206_ == 0)
{
lean_object* v___x_207_; uint8_t v___x_208_; 
v___x_207_ = lean_unsigned_to_nat(2u);
v___x_208_ = lean_nat_dec_eq(v_a_202_, v___x_207_);
lean_dec(v_a_202_);
if (v___x_208_ == 0)
{
goto v___jp_198_;
}
else
{
lean_object* v___x_209_; 
v___x_209_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0___closed__2));
return v___x_209_;
}
}
else
{
lean_object* v___x_210_; 
lean_dec(v_a_202_);
v___x_210_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0___closed__3));
return v___x_210_;
}
}
else
{
lean_object* v___x_211_; 
lean_dec(v_a_202_);
v___x_211_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0___closed__4));
return v___x_211_;
}
}
else
{
lean_dec_ref(v___x_201_);
goto v___jp_198_;
}
v___jp_198_:
{
lean_object* v___x_199_; 
v___x_199_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0___closed__1));
return v___x_199_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__1___boxed(lean_object* v_j_212_, lean_object* v_k_213_){
_start:
{
lean_object* v_res_214_; 
v_res_214_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__1(v_j_212_, v_k_213_);
lean_dec_ref(v_k_213_);
return v_res_214_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0_spec__2_spec__3(size_t v_sz_215_, size_t v_i_216_, lean_object* v_bs_217_){
_start:
{
uint8_t v___x_218_; 
v___x_218_ = lean_usize_dec_lt(v_i_216_, v_sz_215_);
if (v___x_218_ == 0)
{
lean_object* v___x_219_; 
v___x_219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_219_, 0, v_bs_217_);
return v___x_219_;
}
else
{
lean_object* v_v_220_; lean_object* v___x_221_; 
v_v_220_ = lean_array_uget_borrowed(v_bs_217_, v_i_216_);
lean_inc(v_v_220_);
v___x_221_ = l_Lean_Lsp_instFromJsonDocumentFilter_fromJson(v_v_220_);
if (lean_obj_tag(v___x_221_) == 0)
{
lean_object* v_a_222_; lean_object* v___x_224_; uint8_t v_isShared_225_; uint8_t v_isSharedCheck_229_; 
lean_dec_ref(v_bs_217_);
v_a_222_ = lean_ctor_get(v___x_221_, 0);
v_isSharedCheck_229_ = !lean_is_exclusive(v___x_221_);
if (v_isSharedCheck_229_ == 0)
{
v___x_224_ = v___x_221_;
v_isShared_225_ = v_isSharedCheck_229_;
goto v_resetjp_223_;
}
else
{
lean_inc(v_a_222_);
lean_dec(v___x_221_);
v___x_224_ = lean_box(0);
v_isShared_225_ = v_isSharedCheck_229_;
goto v_resetjp_223_;
}
v_resetjp_223_:
{
lean_object* v___x_227_; 
if (v_isShared_225_ == 0)
{
v___x_227_ = v___x_224_;
goto v_reusejp_226_;
}
else
{
lean_object* v_reuseFailAlloc_228_; 
v_reuseFailAlloc_228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_228_, 0, v_a_222_);
v___x_227_ = v_reuseFailAlloc_228_;
goto v_reusejp_226_;
}
v_reusejp_226_:
{
return v___x_227_;
}
}
}
else
{
lean_object* v_a_230_; lean_object* v___x_231_; lean_object* v_bs_x27_232_; size_t v___x_233_; size_t v___x_234_; lean_object* v___x_235_; 
v_a_230_ = lean_ctor_get(v___x_221_, 0);
lean_inc(v_a_230_);
lean_dec_ref_known(v___x_221_, 1);
v___x_231_ = lean_unsigned_to_nat(0u);
v_bs_x27_232_ = lean_array_uset(v_bs_217_, v_i_216_, v___x_231_);
v___x_233_ = ((size_t)1ULL);
v___x_234_ = lean_usize_add(v_i_216_, v___x_233_);
v___x_235_ = lean_array_uset(v_bs_x27_232_, v_i_216_, v_a_230_);
v_i_216_ = v___x_234_;
v_bs_217_ = v___x_235_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_sz_237_, lean_object* v_i_238_, lean_object* v_bs_239_){
_start:
{
size_t v_sz_boxed_240_; size_t v_i_boxed_241_; lean_object* v_res_242_; 
v_sz_boxed_240_ = lean_unbox_usize(v_sz_237_);
lean_dec(v_sz_237_);
v_i_boxed_241_ = lean_unbox_usize(v_i_238_);
lean_dec(v_i_238_);
v_res_242_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0_spec__2_spec__3(v_sz_boxed_240_, v_i_boxed_241_, v_bs_239_);
return v_res_242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0_spec__2(lean_object* v_x_245_){
_start:
{
if (lean_obj_tag(v_x_245_) == 4)
{
lean_object* v_elems_246_; size_t v_sz_247_; size_t v___x_248_; lean_object* v___x_249_; 
v_elems_246_ = lean_ctor_get(v_x_245_, 0);
lean_inc_ref(v_elems_246_);
lean_dec_ref_known(v_x_245_, 1);
v_sz_247_ = lean_array_size(v_elems_246_);
v___x_248_ = ((size_t)0ULL);
v___x_249_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0_spec__2_spec__3(v_sz_247_, v___x_248_, v_elems_246_);
return v___x_249_;
}
else
{
lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; 
v___x_250_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0_spec__2___closed__0));
v___x_251_ = lean_unsigned_to_nat(80u);
v___x_252_ = l_Lean_Json_pretty(v_x_245_, v___x_251_);
v___x_253_ = lean_string_append(v___x_250_, v___x_252_);
lean_dec_ref(v___x_252_);
v___x_254_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0_spec__2___closed__1));
v___x_255_ = lean_string_append(v___x_253_, v___x_254_);
v___x_256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_256_, 0, v___x_255_);
return v___x_256_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0(lean_object* v_x_259_){
_start:
{
if (lean_obj_tag(v_x_259_) == 0)
{
lean_object* v___x_260_; 
v___x_260_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0___closed__0));
return v___x_260_;
}
else
{
lean_object* v___x_261_; 
v___x_261_ = l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0_spec__2(v_x_259_);
if (lean_obj_tag(v___x_261_) == 0)
{
lean_object* v_a_262_; lean_object* v___x_264_; uint8_t v_isShared_265_; uint8_t v_isSharedCheck_269_; 
v_a_262_ = lean_ctor_get(v___x_261_, 0);
v_isSharedCheck_269_ = !lean_is_exclusive(v___x_261_);
if (v_isSharedCheck_269_ == 0)
{
v___x_264_ = v___x_261_;
v_isShared_265_ = v_isSharedCheck_269_;
goto v_resetjp_263_;
}
else
{
lean_inc(v_a_262_);
lean_dec(v___x_261_);
v___x_264_ = lean_box(0);
v_isShared_265_ = v_isSharedCheck_269_;
goto v_resetjp_263_;
}
v_resetjp_263_:
{
lean_object* v___x_267_; 
if (v_isShared_265_ == 0)
{
v___x_267_ = v___x_264_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v_a_262_);
v___x_267_ = v_reuseFailAlloc_268_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
return v___x_267_;
}
}
}
else
{
lean_object* v_a_270_; lean_object* v___x_272_; uint8_t v_isShared_273_; uint8_t v_isSharedCheck_278_; 
v_a_270_ = lean_ctor_get(v___x_261_, 0);
v_isSharedCheck_278_ = !lean_is_exclusive(v___x_261_);
if (v_isSharedCheck_278_ == 0)
{
v___x_272_ = v___x_261_;
v_isShared_273_ = v_isSharedCheck_278_;
goto v_resetjp_271_;
}
else
{
lean_inc(v_a_270_);
lean_dec(v___x_261_);
v___x_272_ = lean_box(0);
v_isShared_273_ = v_isSharedCheck_278_;
goto v_resetjp_271_;
}
v_resetjp_271_:
{
lean_object* v___x_274_; lean_object* v___x_276_; 
v___x_274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_274_, 0, v_a_270_);
if (v_isShared_273_ == 0)
{
lean_ctor_set(v___x_272_, 0, v___x_274_);
v___x_276_ = v___x_272_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v___x_274_);
v___x_276_ = v_reuseFailAlloc_277_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
return v___x_276_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0(lean_object* v_j_279_, lean_object* v_k_280_){
_start:
{
lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_281_ = l_Lean_Json_getObjValD(v_j_279_, v_k_280_);
v___x_282_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0(v___x_281_);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0___boxed(lean_object* v_j_283_, lean_object* v_k_284_){
_start:
{
lean_object* v_res_285_; 
v_res_285_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0(v_j_283_, v_k_284_);
lean_dec_ref(v_k_284_);
return v_res_285_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__3(void){
_start:
{
uint8_t v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_292_ = 1;
v___x_293_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__2));
v___x_294_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_293_, v___x_292_);
return v___x_294_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__4(void){
_start:
{
lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_295_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__5));
v___x_296_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__3, &l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__3);
v___x_297_ = lean_string_append(v___x_296_, v___x_295_);
return v___x_297_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__7(void){
_start:
{
uint8_t v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_301_ = 1;
v___x_302_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__6));
v___x_303_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_302_, v___x_301_);
return v___x_303_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__8(void){
_start:
{
lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; 
v___x_304_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__7, &l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__7);
v___x_305_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__4, &l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__4);
v___x_306_ = lean_string_append(v___x_305_, v___x_304_);
return v___x_306_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__9(void){
_start:
{
lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_307_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__10));
v___x_308_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__8, &l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__8);
v___x_309_ = lean_string_append(v___x_308_, v___x_307_);
return v___x_309_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__12(void){
_start:
{
uint8_t v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_313_ = 1;
v___x_314_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__11));
v___x_315_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_314_, v___x_313_);
return v___x_315_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__13(void){
_start:
{
lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_316_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__12, &l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__12);
v___x_317_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__4, &l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__4);
v___x_318_ = lean_string_append(v___x_317_, v___x_316_);
return v___x_318_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__14(void){
_start:
{
lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_319_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__10));
v___x_320_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__13, &l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__13);
v___x_321_ = lean_string_append(v___x_320_, v___x_319_);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson(lean_object* v_json_322_){
_start:
{
lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_323_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__0));
lean_inc(v_json_322_);
v___x_324_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0(v_json_322_, v___x_323_);
if (lean_obj_tag(v___x_324_) == 0)
{
lean_object* v_a_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_334_; 
lean_dec(v_json_322_);
v_a_325_ = lean_ctor_get(v___x_324_, 0);
v_isSharedCheck_334_ = !lean_is_exclusive(v___x_324_);
if (v_isSharedCheck_334_ == 0)
{
v___x_327_ = v___x_324_;
v_isShared_328_ = v_isSharedCheck_334_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_a_325_);
lean_dec(v___x_324_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_334_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_332_; 
v___x_329_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__9, &l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__9);
v___x_330_ = lean_string_append(v___x_329_, v_a_325_);
lean_dec(v_a_325_);
if (v_isShared_328_ == 0)
{
lean_ctor_set(v___x_327_, 0, v___x_330_);
v___x_332_ = v___x_327_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v___x_330_);
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
if (lean_obj_tag(v___x_324_) == 0)
{
lean_object* v_a_335_; lean_object* v___x_337_; uint8_t v_isShared_338_; uint8_t v_isSharedCheck_342_; 
lean_dec(v_json_322_);
v_a_335_ = lean_ctor_get(v___x_324_, 0);
v_isSharedCheck_342_ = !lean_is_exclusive(v___x_324_);
if (v_isSharedCheck_342_ == 0)
{
v___x_337_ = v___x_324_;
v_isShared_338_ = v_isSharedCheck_342_;
goto v_resetjp_336_;
}
else
{
lean_inc(v_a_335_);
lean_dec(v___x_324_);
v___x_337_ = lean_box(0);
v_isShared_338_ = v_isSharedCheck_342_;
goto v_resetjp_336_;
}
v_resetjp_336_:
{
lean_object* v___x_340_; 
if (v_isShared_338_ == 0)
{
lean_ctor_set_tag(v___x_337_, 0);
v___x_340_ = v___x_337_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v_a_335_);
v___x_340_ = v_reuseFailAlloc_341_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
return v___x_340_;
}
}
}
else
{
lean_object* v_a_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
v_a_343_ = lean_ctor_get(v___x_324_, 0);
lean_inc(v_a_343_);
lean_dec_ref_known(v___x_324_, 1);
v___x_344_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__10));
v___x_345_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__1(v_json_322_, v___x_344_);
if (lean_obj_tag(v___x_345_) == 0)
{
lean_object* v_a_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_355_; 
lean_dec(v_a_343_);
v_a_346_ = lean_ctor_get(v___x_345_, 0);
v_isSharedCheck_355_ = !lean_is_exclusive(v___x_345_);
if (v_isSharedCheck_355_ == 0)
{
v___x_348_ = v___x_345_;
v_isShared_349_ = v_isSharedCheck_355_;
goto v_resetjp_347_;
}
else
{
lean_inc(v_a_346_);
lean_dec(v___x_345_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_355_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_353_; 
v___x_350_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__14, &l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__14_once, _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__14);
v___x_351_ = lean_string_append(v___x_350_, v_a_346_);
lean_dec(v_a_346_);
if (v_isShared_349_ == 0)
{
lean_ctor_set(v___x_348_, 0, v___x_351_);
v___x_353_ = v___x_348_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v___x_351_);
v___x_353_ = v_reuseFailAlloc_354_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
return v___x_353_;
}
}
}
else
{
if (lean_obj_tag(v___x_345_) == 0)
{
lean_object* v_a_356_; lean_object* v___x_358_; uint8_t v_isShared_359_; uint8_t v_isSharedCheck_363_; 
lean_dec(v_a_343_);
v_a_356_ = lean_ctor_get(v___x_345_, 0);
v_isSharedCheck_363_ = !lean_is_exclusive(v___x_345_);
if (v_isSharedCheck_363_ == 0)
{
v___x_358_ = v___x_345_;
v_isShared_359_ = v_isSharedCheck_363_;
goto v_resetjp_357_;
}
else
{
lean_inc(v_a_356_);
lean_dec(v___x_345_);
v___x_358_ = lean_box(0);
v_isShared_359_ = v_isSharedCheck_363_;
goto v_resetjp_357_;
}
v_resetjp_357_:
{
lean_object* v___x_361_; 
if (v_isShared_359_ == 0)
{
lean_ctor_set_tag(v___x_358_, 0);
v___x_361_ = v___x_358_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v_a_356_);
v___x_361_ = v_reuseFailAlloc_362_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
return v___x_361_;
}
}
}
else
{
lean_object* v_a_364_; lean_object* v___x_366_; uint8_t v_isShared_367_; uint8_t v_isSharedCheck_373_; 
v_a_364_ = lean_ctor_get(v___x_345_, 0);
v_isSharedCheck_373_ = !lean_is_exclusive(v___x_345_);
if (v_isSharedCheck_373_ == 0)
{
v___x_366_ = v___x_345_;
v_isShared_367_ = v_isSharedCheck_373_;
goto v_resetjp_365_;
}
else
{
lean_inc(v_a_364_);
lean_dec(v___x_345_);
v___x_366_ = lean_box(0);
v_isShared_367_ = v_isSharedCheck_373_;
goto v_resetjp_365_;
}
v_resetjp_365_:
{
lean_object* v___x_368_; uint8_t v___x_369_; lean_object* v___x_371_; 
v___x_368_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_368_, 0, v_a_343_);
v___x_369_ = lean_unbox(v_a_364_);
lean_dec(v_a_364_);
lean_ctor_set_uint8(v___x_368_, sizeof(void*)*1, v___x_369_);
if (v_isShared_367_ == 0)
{
lean_ctor_set(v___x_366_, 0, v___x_368_);
v___x_371_ = v___x_366_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v___x_368_);
v___x_371_ = v_reuseFailAlloc_372_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
return v___x_371_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentContentChangeEvent_ctorIdx___impl(lean_object* v_x_376_){
_start:
{
lean_object* v___x_377_; 
v___x_377_ = lean_obj_tag_nat(v_x_376_);
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentContentChangeEvent_ctorIdx___impl___boxed(lean_object* v_x_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l_Lean_Lsp_TextDocumentContentChangeEvent_ctorIdx___impl(v_x_378_);
lean_dec_ref(v_x_378_);
return v_res_379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentContentChangeEvent_ctorElim___redArg(lean_object* v_t_380_, lean_object* v_k_381_){
_start:
{
if (lean_obj_tag(v_t_380_) == 0)
{
lean_object* v_range_382_; lean_object* v_text_383_; lean_object* v___x_384_; 
v_range_382_ = lean_ctor_get(v_t_380_, 0);
lean_inc_ref(v_range_382_);
v_text_383_ = lean_ctor_get(v_t_380_, 1);
lean_inc_ref(v_text_383_);
lean_dec_ref_known(v_t_380_, 2);
v___x_384_ = lean_apply_2(v_k_381_, v_range_382_, v_text_383_);
return v___x_384_;
}
else
{
lean_object* v_text_385_; lean_object* v___x_386_; 
v_text_385_ = lean_ctor_get(v_t_380_, 0);
lean_inc_ref(v_text_385_);
lean_dec_ref_known(v_t_380_, 1);
v___x_386_ = lean_apply_1(v_k_381_, v_text_385_);
return v___x_386_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentContentChangeEvent_ctorElim(lean_object* v_motive_387_, lean_object* v_ctorIdx_388_, lean_object* v_t_389_, lean_object* v_h_390_, lean_object* v_k_391_){
_start:
{
lean_object* v___x_392_; 
v___x_392_ = l_Lean_Lsp_TextDocumentContentChangeEvent_ctorElim___redArg(v_t_389_, v_k_391_);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentContentChangeEvent_ctorElim___boxed(lean_object* v_motive_393_, lean_object* v_ctorIdx_394_, lean_object* v_t_395_, lean_object* v_h_396_, lean_object* v_k_397_){
_start:
{
lean_object* v_res_398_; 
v_res_398_ = l_Lean_Lsp_TextDocumentContentChangeEvent_ctorElim(v_motive_393_, v_ctorIdx_394_, v_t_395_, v_h_396_, v_k_397_);
lean_dec(v_ctorIdx_394_);
return v_res_398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentContentChangeEvent_rangeChange_elim___redArg(lean_object* v_t_399_, lean_object* v_rangeChange_400_){
_start:
{
lean_object* v___x_401_; 
v___x_401_ = l_Lean_Lsp_TextDocumentContentChangeEvent_ctorElim___redArg(v_t_399_, v_rangeChange_400_);
return v___x_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentContentChangeEvent_rangeChange_elim(lean_object* v_motive_402_, lean_object* v_t_403_, lean_object* v_h_404_, lean_object* v_rangeChange_405_){
_start:
{
lean_object* v___x_406_; 
v___x_406_ = l_Lean_Lsp_TextDocumentContentChangeEvent_ctorElim___redArg(v_t_403_, v_rangeChange_405_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentContentChangeEvent_fullChange_elim___redArg(lean_object* v_t_407_, lean_object* v_fullChange_408_){
_start:
{
lean_object* v___x_409_; 
v___x_409_ = l_Lean_Lsp_TextDocumentContentChangeEvent_ctorElim___redArg(v_t_407_, v_fullChange_408_);
return v___x_409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentContentChangeEvent_fullChange_elim(lean_object* v_motive_410_, lean_object* v_t_411_, lean_object* v_h_412_, lean_object* v_fullChange_413_){
_start:
{
lean_object* v___x_414_; 
v___x_414_ = l_Lean_Lsp_TextDocumentContentChangeEvent_ctorElim___redArg(v_t_411_, v_fullChange_413_);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0(lean_object* v___x_417_, lean_object* v___x_418_, lean_object* v_j_419_){
_start:
{
lean_object* v___x_440_; lean_object* v___x_441_; 
v___x_440_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0___closed__1));
lean_inc(v_j_419_);
v___x_441_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_419_, v___x_418_, v___x_440_);
if (lean_obj_tag(v___x_441_) == 0)
{
lean_dec_ref_known(v___x_441_, 1);
goto v___jp_420_;
}
else
{
lean_object* v_a_442_; lean_object* v___x_443_; lean_object* v___x_444_; 
v_a_442_ = lean_ctor_get(v___x_441_, 0);
lean_inc(v_a_442_);
lean_dec_ref_known(v___x_441_, 1);
v___x_443_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0___closed__0));
lean_inc_ref(v___x_417_);
lean_inc(v_j_419_);
v___x_444_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_419_, v___x_417_, v___x_443_);
if (lean_obj_tag(v___x_444_) == 0)
{
lean_dec_ref_known(v___x_444_, 1);
lean_dec(v_a_442_);
goto v___jp_420_;
}
else
{
lean_object* v_a_445_; lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_453_; 
lean_dec(v_j_419_);
lean_dec_ref(v___x_417_);
v_a_445_ = lean_ctor_get(v___x_444_, 0);
v_isSharedCheck_453_ = !lean_is_exclusive(v___x_444_);
if (v_isSharedCheck_453_ == 0)
{
v___x_447_ = v___x_444_;
v_isShared_448_ = v_isSharedCheck_453_;
goto v_resetjp_446_;
}
else
{
lean_inc(v_a_445_);
lean_dec(v___x_444_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_453_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
lean_object* v___x_449_; lean_object* v___x_451_; 
v___x_449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_449_, 0, v_a_442_);
lean_ctor_set(v___x_449_, 1, v_a_445_);
if (v_isShared_448_ == 0)
{
lean_ctor_set(v___x_447_, 0, v___x_449_);
v___x_451_ = v___x_447_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v___x_449_);
v___x_451_ = v_reuseFailAlloc_452_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
return v___x_451_;
}
}
}
}
v___jp_420_:
{
lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_421_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0___closed__0));
v___x_422_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_419_, v___x_417_, v___x_421_);
if (lean_obj_tag(v___x_422_) == 0)
{
lean_object* v_a_423_; lean_object* v___x_425_; uint8_t v_isShared_426_; uint8_t v_isSharedCheck_430_; 
v_a_423_ = lean_ctor_get(v___x_422_, 0);
v_isSharedCheck_430_ = !lean_is_exclusive(v___x_422_);
if (v_isSharedCheck_430_ == 0)
{
v___x_425_ = v___x_422_;
v_isShared_426_ = v_isSharedCheck_430_;
goto v_resetjp_424_;
}
else
{
lean_inc(v_a_423_);
lean_dec(v___x_422_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_430_;
goto v_resetjp_424_;
}
v_resetjp_424_:
{
lean_object* v___x_428_; 
if (v_isShared_426_ == 0)
{
v___x_428_ = v___x_425_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v_a_423_);
v___x_428_ = v_reuseFailAlloc_429_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
return v___x_428_;
}
}
}
else
{
lean_object* v_a_431_; lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_439_; 
v_a_431_ = lean_ctor_get(v___x_422_, 0);
v_isSharedCheck_439_ = !lean_is_exclusive(v___x_422_);
if (v_isSharedCheck_439_ == 0)
{
v___x_433_ = v___x_422_;
v_isShared_434_ = v_isSharedCheck_439_;
goto v_resetjp_432_;
}
else
{
lean_inc(v_a_431_);
lean_dec(v___x_422_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_439_;
goto v_resetjp_432_;
}
v_resetjp_432_:
{
lean_object* v___x_435_; lean_object* v___x_437_; 
v___x_435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_435_, 0, v_a_431_);
if (v_isShared_434_ == 0)
{
lean_ctor_set(v___x_433_, 0, v___x_435_);
v___x_437_ = v___x_433_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v___x_435_);
v___x_437_ = v_reuseFailAlloc_438_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
return v___x_437_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentContentChangeEvent_hasToJson___lam__0(lean_object* v_o_460_){
_start:
{
if (lean_obj_tag(v_o_460_) == 0)
{
lean_object* v_range_461_; lean_object* v_text_462_; lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_478_; 
v_range_461_ = lean_ctor_get(v_o_460_, 0);
v_text_462_ = lean_ctor_get(v_o_460_, 1);
v_isSharedCheck_478_ = !lean_is_exclusive(v_o_460_);
if (v_isSharedCheck_478_ == 0)
{
v___x_464_ = v_o_460_;
v_isShared_465_ = v_isSharedCheck_478_;
goto v_resetjp_463_;
}
else
{
lean_inc(v_text_462_);
lean_inc(v_range_461_);
lean_dec(v_o_460_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_478_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_469_; 
v___x_466_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0___closed__1));
v___x_467_ = l_Lean_Lsp_instToJsonRange_toJson(v_range_461_);
if (v_isShared_465_ == 0)
{
lean_ctor_set(v___x_464_, 1, v___x_467_);
lean_ctor_set(v___x_464_, 0, v___x_466_);
v___x_469_ = v___x_464_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v___x_466_);
lean_ctor_set(v_reuseFailAlloc_477_, 1, v___x_467_);
v___x_469_ = v_reuseFailAlloc_477_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_470_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0___closed__0));
v___x_471_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_471_, 0, v_text_462_);
v___x_472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_472_, 0, v___x_470_);
lean_ctor_set(v___x_472_, 1, v___x_471_);
v___x_473_ = lean_box(0);
v___x_474_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_474_, 0, v___x_472_);
lean_ctor_set(v___x_474_, 1, v___x_473_);
v___x_475_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_475_, 0, v___x_469_);
lean_ctor_set(v___x_475_, 1, v___x_474_);
v___x_476_ = l_Lean_Json_mkObj(v___x_475_);
lean_dec_ref_known(v___x_475_, 2);
return v___x_476_;
}
}
}
else
{
lean_object* v_text_479_; lean_object* v___x_481_; uint8_t v_isShared_482_; uint8_t v_isSharedCheck_491_; 
v_text_479_ = lean_ctor_get(v_o_460_, 0);
v_isSharedCheck_491_ = !lean_is_exclusive(v_o_460_);
if (v_isSharedCheck_491_ == 0)
{
v___x_481_ = v_o_460_;
v_isShared_482_ = v_isSharedCheck_491_;
goto v_resetjp_480_;
}
else
{
lean_inc(v_text_479_);
lean_dec(v_o_460_);
v___x_481_ = lean_box(0);
v_isShared_482_ = v_isSharedCheck_491_;
goto v_resetjp_480_;
}
v_resetjp_480_:
{
lean_object* v___x_483_; lean_object* v___x_485_; 
v___x_483_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0___closed__0));
if (v_isShared_482_ == 0)
{
lean_ctor_set_tag(v___x_481_, 3);
v___x_485_ = v___x_481_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_490_; 
v_reuseFailAlloc_490_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_490_, 0, v_text_479_);
v___x_485_ = v_reuseFailAlloc_490_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_486_, 0, v___x_483_);
lean_ctor_set(v___x_486_, 1, v___x_485_);
v___x_487_ = lean_box(0);
v___x_488_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_488_, 0, v___x_486_);
lean_ctor_set(v___x_488_, 1, v___x_487_);
v___x_489_ = l_Lean_Json_mkObj(v___x_488_);
lean_dec_ref_known(v___x_488_, 2);
return v___x_489_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonDidChangeTextDocumentParams_toJson_spec__0_spec__0(size_t v_sz_494_, size_t v_i_495_, lean_object* v_bs_496_){
_start:
{
uint8_t v___x_497_; 
v___x_497_ = lean_usize_dec_lt(v_i_495_, v_sz_494_);
if (v___x_497_ == 0)
{
return v_bs_496_;
}
else
{
lean_object* v_v_498_; lean_object* v___x_499_; lean_object* v_bs_x27_500_; lean_object* v___y_502_; 
v_v_498_ = lean_array_uget(v_bs_496_, v_i_495_);
v___x_499_ = lean_unsigned_to_nat(0u);
v_bs_x27_500_ = lean_array_uset(v_bs_496_, v_i_495_, v___x_499_);
if (lean_obj_tag(v_v_498_) == 0)
{
lean_object* v_range_507_; lean_object* v_text_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_524_; 
v_range_507_ = lean_ctor_get(v_v_498_, 0);
v_text_508_ = lean_ctor_get(v_v_498_, 1);
v_isSharedCheck_524_ = !lean_is_exclusive(v_v_498_);
if (v_isSharedCheck_524_ == 0)
{
v___x_510_ = v_v_498_;
v_isShared_511_ = v_isSharedCheck_524_;
goto v_resetjp_509_;
}
else
{
lean_inc(v_text_508_);
lean_inc(v_range_507_);
lean_dec(v_v_498_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_524_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_515_; 
v___x_512_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0___closed__1));
v___x_513_ = l_Lean_Lsp_instToJsonRange_toJson(v_range_507_);
if (v_isShared_511_ == 0)
{
lean_ctor_set(v___x_510_, 1, v___x_513_);
lean_ctor_set(v___x_510_, 0, v___x_512_);
v___x_515_ = v___x_510_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v___x_512_);
lean_ctor_set(v_reuseFailAlloc_523_, 1, v___x_513_);
v___x_515_ = v_reuseFailAlloc_523_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; 
v___x_516_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0___closed__0));
v___x_517_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_517_, 0, v_text_508_);
v___x_518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_518_, 0, v___x_516_);
lean_ctor_set(v___x_518_, 1, v___x_517_);
v___x_519_ = lean_box(0);
v___x_520_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_520_, 0, v___x_518_);
lean_ctor_set(v___x_520_, 1, v___x_519_);
v___x_521_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_521_, 0, v___x_515_);
lean_ctor_set(v___x_521_, 1, v___x_520_);
v___x_522_ = l_Lean_Json_mkObj(v___x_521_);
lean_dec_ref_known(v___x_521_, 2);
v___y_502_ = v___x_522_;
goto v___jp_501_;
}
}
}
else
{
lean_object* v_text_525_; lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_537_; 
v_text_525_ = lean_ctor_get(v_v_498_, 0);
v_isSharedCheck_537_ = !lean_is_exclusive(v_v_498_);
if (v_isSharedCheck_537_ == 0)
{
v___x_527_ = v_v_498_;
v_isShared_528_ = v_isSharedCheck_537_;
goto v_resetjp_526_;
}
else
{
lean_inc(v_text_525_);
lean_dec(v_v_498_);
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_537_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
lean_object* v___x_529_; lean_object* v___x_531_; 
v___x_529_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0___closed__0));
if (v_isShared_528_ == 0)
{
lean_ctor_set_tag(v___x_527_, 3);
v___x_531_ = v___x_527_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v_text_525_);
v___x_531_ = v_reuseFailAlloc_536_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_532_, 0, v___x_529_);
lean_ctor_set(v___x_532_, 1, v___x_531_);
v___x_533_ = lean_box(0);
v___x_534_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_534_, 0, v___x_532_);
lean_ctor_set(v___x_534_, 1, v___x_533_);
v___x_535_ = l_Lean_Json_mkObj(v___x_534_);
lean_dec_ref_known(v___x_534_, 2);
v___y_502_ = v___x_535_;
goto v___jp_501_;
}
}
}
v___jp_501_:
{
size_t v___x_503_; size_t v___x_504_; lean_object* v___x_505_; 
v___x_503_ = ((size_t)1ULL);
v___x_504_ = lean_usize_add(v_i_495_, v___x_503_);
v___x_505_ = lean_array_uset(v_bs_x27_500_, v_i_495_, v___y_502_);
v_i_495_ = v___x_504_;
v_bs_496_ = v___x_505_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonDidChangeTextDocumentParams_toJson_spec__0_spec__0___boxed(lean_object* v_sz_538_, lean_object* v_i_539_, lean_object* v_bs_540_){
_start:
{
size_t v_sz_boxed_541_; size_t v_i_boxed_542_; lean_object* v_res_543_; 
v_sz_boxed_541_ = lean_unbox_usize(v_sz_538_);
lean_dec(v_sz_538_);
v_i_boxed_542_ = lean_unbox_usize(v_i_539_);
lean_dec(v_i_539_);
v_res_543_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonDidChangeTextDocumentParams_toJson_spec__0_spec__0(v_sz_boxed_541_, v_i_boxed_542_, v_bs_540_);
return v_res_543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonDidChangeTextDocumentParams_toJson_spec__0(lean_object* v_a_544_){
_start:
{
size_t v_sz_545_; size_t v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; 
v_sz_545_ = lean_array_size(v_a_544_);
v___x_546_ = ((size_t)0ULL);
v___x_547_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonDidChangeTextDocumentParams_toJson_spec__0_spec__0(v_sz_545_, v___x_546_, v_a_544_);
v___x_548_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_548_, 0, v___x_547_);
return v___x_548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDidChangeTextDocumentParams_toJson(lean_object* v_x_550_){
_start:
{
lean_object* v_textDocument_551_; lean_object* v_contentChanges_552_; lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_572_; 
v_textDocument_551_ = lean_ctor_get(v_x_550_, 0);
v_contentChanges_552_ = lean_ctor_get(v_x_550_, 1);
v_isSharedCheck_572_ = !lean_is_exclusive(v_x_550_);
if (v_isSharedCheck_572_ == 0)
{
v___x_554_ = v_x_550_;
v_isShared_555_ = v_isSharedCheck_572_;
goto v_resetjp_553_;
}
else
{
lean_inc(v_contentChanges_552_);
lean_inc(v_textDocument_551_);
lean_dec(v_x_550_);
v___x_554_ = lean_box(0);
v_isShared_555_ = v_isSharedCheck_572_;
goto v_resetjp_553_;
}
v_resetjp_553_:
{
lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_559_; 
v___x_556_ = ((lean_object*)(l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__0));
v___x_557_ = l_Lean_Lsp_instToJsonVersionedTextDocumentIdentifier_toJson(v_textDocument_551_);
if (v_isShared_555_ == 0)
{
lean_ctor_set(v___x_554_, 1, v___x_557_);
lean_ctor_set(v___x_554_, 0, v___x_556_);
v___x_559_ = v___x_554_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v___x_556_);
lean_ctor_set(v_reuseFailAlloc_571_, 1, v___x_557_);
v___x_559_ = v_reuseFailAlloc_571_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; 
v___x_560_ = lean_box(0);
v___x_561_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_561_, 0, v___x_559_);
lean_ctor_set(v___x_561_, 1, v___x_560_);
v___x_562_ = ((lean_object*)(l_Lean_Lsp_instToJsonDidChangeTextDocumentParams_toJson___closed__0));
v___x_563_ = l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonDidChangeTextDocumentParams_toJson_spec__0(v_contentChanges_552_);
v___x_564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_564_, 0, v___x_562_);
lean_ctor_set(v___x_564_, 1, v___x_563_);
v___x_565_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_565_, 0, v___x_564_);
lean_ctor_set(v___x_565_, 1, v___x_560_);
v___x_566_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_566_, 0, v___x_565_);
lean_ctor_set(v___x_566_, 1, v___x_560_);
v___x_567_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_567_, 0, v___x_561_);
lean_ctor_set(v___x_567_, 1, v___x_566_);
v___x_568_ = ((lean_object*)(l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__1));
v___x_569_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson_spec__0(v___x_567_, v___x_568_);
v___x_570_ = l_Lean_Json_mkObj(v___x_569_);
lean_dec(v___x_569_);
return v___x_570_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__0(lean_object* v_j_575_, lean_object* v_k_576_){
_start:
{
lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_577_ = l_Lean_Json_getObjValD(v_j_575_, v_k_576_);
v___x_578_ = l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson(v___x_577_);
return v___x_578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__0___boxed(lean_object* v_j_579_, lean_object* v_k_580_){
_start:
{
lean_object* v_res_581_; 
v_res_581_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__0(v_j_579_, v_k_580_);
lean_dec_ref(v_k_580_);
return v_res_581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1_spec__3(lean_object* v_j_582_, lean_object* v_k_583_){
_start:
{
lean_object* v___x_584_; lean_object* v___x_585_; 
v___x_584_ = l_Lean_Json_getObjValD(v_j_582_, v_k_583_);
v___x_585_ = l_Lean_Lsp_instFromJsonRange_fromJson(v___x_584_);
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1_spec__3___boxed(lean_object* v_j_586_, lean_object* v_k_587_){
_start:
{
lean_object* v_res_588_; 
v_res_588_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1_spec__3(v_j_586_, v_k_587_);
lean_dec_ref(v_k_587_);
return v_res_588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1_spec__2(lean_object* v_j_589_, lean_object* v_k_590_){
_start:
{
lean_object* v___x_591_; lean_object* v___x_592_; 
v___x_591_ = l_Lean_Json_getObjValD(v_j_589_, v_k_590_);
v___x_592_ = l_Lean_Json_getStr_x3f(v___x_591_);
return v___x_592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1_spec__2___boxed(lean_object* v_j_593_, lean_object* v_k_594_){
_start:
{
lean_object* v_res_595_; 
v_res_595_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1_spec__2(v_j_593_, v_k_594_);
lean_dec_ref(v_k_594_);
return v_res_595_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1_spec__4(size_t v_sz_596_, size_t v_i_597_, lean_object* v_bs_598_){
_start:
{
uint8_t v___x_599_; 
v___x_599_ = lean_usize_dec_lt(v_i_597_, v_sz_596_);
if (v___x_599_ == 0)
{
lean_object* v___x_600_; 
v___x_600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_600_, 0, v_bs_598_);
return v___x_600_;
}
else
{
lean_object* v_v_601_; lean_object* v___x_602_; lean_object* v_bs_x27_603_; lean_object* v_a_605_; lean_object* v___x_623_; lean_object* v___x_624_; 
v_v_601_ = lean_array_uget(v_bs_598_, v_i_597_);
v___x_602_ = lean_unsigned_to_nat(0u);
v_bs_x27_603_ = lean_array_uset(v_bs_598_, v_i_597_, v___x_602_);
v___x_623_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0___closed__1));
lean_inc(v_v_601_);
v___x_624_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1_spec__3(v_v_601_, v___x_623_);
if (lean_obj_tag(v___x_624_) == 0)
{
lean_dec_ref_known(v___x_624_, 1);
goto v___jp_610_;
}
else
{
lean_object* v_a_625_; lean_object* v___x_626_; lean_object* v___x_627_; 
v_a_625_ = lean_ctor_get(v___x_624_, 0);
lean_inc(v_a_625_);
lean_dec_ref_known(v___x_624_, 1);
v___x_626_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0___closed__0));
lean_inc(v_v_601_);
v___x_627_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1_spec__2(v_v_601_, v___x_626_);
if (lean_obj_tag(v___x_627_) == 0)
{
lean_dec_ref_known(v___x_627_, 1);
lean_dec(v_a_625_);
goto v___jp_610_;
}
else
{
lean_object* v_a_628_; lean_object* v___x_629_; 
lean_dec(v_v_601_);
v_a_628_ = lean_ctor_get(v___x_627_, 0);
lean_inc(v_a_628_);
lean_dec_ref_known(v___x_627_, 1);
v___x_629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_629_, 0, v_a_625_);
lean_ctor_set(v___x_629_, 1, v_a_628_);
v_a_605_ = v___x_629_;
goto v___jp_604_;
}
}
v___jp_604_:
{
size_t v___x_606_; size_t v___x_607_; lean_object* v___x_608_; 
v___x_606_ = ((size_t)1ULL);
v___x_607_ = lean_usize_add(v_i_597_, v___x_606_);
v___x_608_ = lean_array_uset(v_bs_x27_603_, v_i_597_, v_a_605_);
v_i_597_ = v___x_607_;
v_bs_598_ = v___x_608_;
goto _start;
}
v___jp_610_:
{
lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_611_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0___closed__0));
v___x_612_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1_spec__2(v_v_601_, v___x_611_);
if (lean_obj_tag(v___x_612_) == 0)
{
lean_object* v_a_613_; lean_object* v___x_615_; uint8_t v_isShared_616_; uint8_t v_isSharedCheck_620_; 
lean_dec_ref(v_bs_x27_603_);
v_a_613_ = lean_ctor_get(v___x_612_, 0);
v_isSharedCheck_620_ = !lean_is_exclusive(v___x_612_);
if (v_isSharedCheck_620_ == 0)
{
v___x_615_ = v___x_612_;
v_isShared_616_ = v_isSharedCheck_620_;
goto v_resetjp_614_;
}
else
{
lean_inc(v_a_613_);
lean_dec(v___x_612_);
v___x_615_ = lean_box(0);
v_isShared_616_ = v_isSharedCheck_620_;
goto v_resetjp_614_;
}
v_resetjp_614_:
{
lean_object* v___x_618_; 
if (v_isShared_616_ == 0)
{
v___x_618_ = v___x_615_;
goto v_reusejp_617_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v_a_613_);
v___x_618_ = v_reuseFailAlloc_619_;
goto v_reusejp_617_;
}
v_reusejp_617_:
{
return v___x_618_;
}
}
}
else
{
lean_object* v_a_621_; lean_object* v___x_622_; 
v_a_621_ = lean_ctor_get(v___x_612_, 0);
lean_inc(v_a_621_);
lean_dec_ref_known(v___x_612_, 1);
v___x_622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_622_, 0, v_a_621_);
v_a_605_ = v___x_622_;
goto v___jp_604_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1_spec__4___boxed(lean_object* v_sz_630_, lean_object* v_i_631_, lean_object* v_bs_632_){
_start:
{
size_t v_sz_boxed_633_; size_t v_i_boxed_634_; lean_object* v_res_635_; 
v_sz_boxed_633_ = lean_unbox_usize(v_sz_630_);
lean_dec(v_sz_630_);
v_i_boxed_634_ = lean_unbox_usize(v_i_631_);
lean_dec(v_i_631_);
v_res_635_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1_spec__4(v_sz_boxed_633_, v_i_boxed_634_, v_bs_632_);
return v_res_635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1(lean_object* v_x_636_){
_start:
{
if (lean_obj_tag(v_x_636_) == 4)
{
lean_object* v_elems_637_; size_t v_sz_638_; size_t v___x_639_; lean_object* v___x_640_; 
v_elems_637_ = lean_ctor_get(v_x_636_, 0);
lean_inc_ref(v_elems_637_);
lean_dec_ref_known(v_x_636_, 1);
v_sz_638_ = lean_array_size(v_elems_637_);
v___x_639_ = ((size_t)0ULL);
v___x_640_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1_spec__4(v_sz_638_, v___x_639_, v_elems_637_);
return v___x_640_;
}
else
{
lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_641_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0_spec__2___closed__0));
v___x_642_ = lean_unsigned_to_nat(80u);
v___x_643_ = l_Lean_Json_pretty(v_x_636_, v___x_642_);
v___x_644_ = lean_string_append(v___x_641_, v___x_643_);
lean_dec_ref(v___x_643_);
v___x_645_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0_spec__2___closed__1));
v___x_646_ = lean_string_append(v___x_644_, v___x_645_);
v___x_647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_647_, 0, v___x_646_);
return v___x_647_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1(lean_object* v_j_648_, lean_object* v_k_649_){
_start:
{
lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_650_ = l_Lean_Json_getObjValD(v_j_648_, v_k_649_);
v___x_651_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1(v___x_650_);
return v___x_651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1___boxed(lean_object* v_j_652_, lean_object* v_k_653_){
_start:
{
lean_object* v_res_654_; 
v_res_654_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1(v_j_652_, v_k_653_);
lean_dec_ref(v_k_653_);
return v_res_654_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__2(void){
_start:
{
uint8_t v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; 
v___x_660_ = 1;
v___x_661_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__1));
v___x_662_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_661_, v___x_660_);
return v___x_662_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__3(void){
_start:
{
lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; 
v___x_663_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__5));
v___x_664_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__2, &l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__2);
v___x_665_ = lean_string_append(v___x_664_, v___x_663_);
return v___x_665_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; 
v___x_666_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__8);
v___x_667_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__3);
v___x_668_ = lean_string_append(v___x_667_, v___x_666_);
return v___x_668_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__5(void){
_start:
{
lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_669_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__10));
v___x_670_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__4);
v___x_671_ = lean_string_append(v___x_670_, v___x_669_);
return v___x_671_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__7(void){
_start:
{
uint8_t v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; 
v___x_674_ = 1;
v___x_675_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__6));
v___x_676_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_675_, v___x_674_);
return v___x_676_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__8(void){
_start:
{
lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; 
v___x_677_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__7);
v___x_678_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__3);
v___x_679_ = lean_string_append(v___x_678_, v___x_677_);
return v___x_679_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__9(void){
_start:
{
lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_680_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__10));
v___x_681_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__8);
v___x_682_ = lean_string_append(v___x_681_, v___x_680_);
return v___x_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson(lean_object* v_json_683_){
_start:
{
lean_object* v___x_684_; lean_object* v___x_685_; 
v___x_684_ = ((lean_object*)(l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__0));
lean_inc(v_json_683_);
v___x_685_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__0(v_json_683_, v___x_684_);
if (lean_obj_tag(v___x_685_) == 0)
{
lean_object* v_a_686_; lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_695_; 
lean_dec(v_json_683_);
v_a_686_ = lean_ctor_get(v___x_685_, 0);
v_isSharedCheck_695_ = !lean_is_exclusive(v___x_685_);
if (v_isSharedCheck_695_ == 0)
{
v___x_688_ = v___x_685_;
v_isShared_689_ = v_isSharedCheck_695_;
goto v_resetjp_687_;
}
else
{
lean_inc(v_a_686_);
lean_dec(v___x_685_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_695_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_693_; 
v___x_690_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__5, &l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__5);
v___x_691_ = lean_string_append(v___x_690_, v_a_686_);
lean_dec(v_a_686_);
if (v_isShared_689_ == 0)
{
lean_ctor_set(v___x_688_, 0, v___x_691_);
v___x_693_ = v___x_688_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v___x_691_);
v___x_693_ = v_reuseFailAlloc_694_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
return v___x_693_;
}
}
}
else
{
if (lean_obj_tag(v___x_685_) == 0)
{
lean_object* v_a_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_703_; 
lean_dec(v_json_683_);
v_a_696_ = lean_ctor_get(v___x_685_, 0);
v_isSharedCheck_703_ = !lean_is_exclusive(v___x_685_);
if (v_isSharedCheck_703_ == 0)
{
v___x_698_ = v___x_685_;
v_isShared_699_ = v_isSharedCheck_703_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_a_696_);
lean_dec(v___x_685_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_703_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___x_701_; 
if (v_isShared_699_ == 0)
{
lean_ctor_set_tag(v___x_698_, 0);
v___x_701_ = v___x_698_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v_a_696_);
v___x_701_ = v_reuseFailAlloc_702_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
return v___x_701_;
}
}
}
else
{
lean_object* v_a_704_; lean_object* v___x_705_; lean_object* v___x_706_; 
v_a_704_ = lean_ctor_get(v___x_685_, 0);
lean_inc(v_a_704_);
lean_dec_ref_known(v___x_685_, 1);
v___x_705_ = ((lean_object*)(l_Lean_Lsp_instToJsonDidChangeTextDocumentParams_toJson___closed__0));
v___x_706_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1(v_json_683_, v___x_705_);
if (lean_obj_tag(v___x_706_) == 0)
{
lean_object* v_a_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_716_; 
lean_dec(v_a_704_);
v_a_707_ = lean_ctor_get(v___x_706_, 0);
v_isSharedCheck_716_ = !lean_is_exclusive(v___x_706_);
if (v_isSharedCheck_716_ == 0)
{
v___x_709_ = v___x_706_;
v_isShared_710_ = v_isSharedCheck_716_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_a_707_);
lean_dec(v___x_706_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_716_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_714_; 
v___x_711_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__9, &l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__9);
v___x_712_ = lean_string_append(v___x_711_, v_a_707_);
lean_dec(v_a_707_);
if (v_isShared_710_ == 0)
{
lean_ctor_set(v___x_709_, 0, v___x_712_);
v___x_714_ = v___x_709_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v___x_712_);
v___x_714_ = v_reuseFailAlloc_715_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
return v___x_714_;
}
}
}
else
{
if (lean_obj_tag(v___x_706_) == 0)
{
lean_object* v_a_717_; lean_object* v___x_719_; uint8_t v_isShared_720_; uint8_t v_isSharedCheck_724_; 
lean_dec(v_a_704_);
v_a_717_ = lean_ctor_get(v___x_706_, 0);
v_isSharedCheck_724_ = !lean_is_exclusive(v___x_706_);
if (v_isSharedCheck_724_ == 0)
{
v___x_719_ = v___x_706_;
v_isShared_720_ = v_isSharedCheck_724_;
goto v_resetjp_718_;
}
else
{
lean_inc(v_a_717_);
lean_dec(v___x_706_);
v___x_719_ = lean_box(0);
v_isShared_720_ = v_isSharedCheck_724_;
goto v_resetjp_718_;
}
v_resetjp_718_:
{
lean_object* v___x_722_; 
if (v_isShared_720_ == 0)
{
lean_ctor_set_tag(v___x_719_, 0);
v___x_722_ = v___x_719_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v_a_717_);
v___x_722_ = v_reuseFailAlloc_723_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
return v___x_722_;
}
}
}
else
{
lean_object* v_a_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_733_; 
v_a_725_ = lean_ctor_get(v___x_706_, 0);
v_isSharedCheck_733_ = !lean_is_exclusive(v___x_706_);
if (v_isSharedCheck_733_ == 0)
{
v___x_727_ = v___x_706_;
v_isShared_728_ = v_isSharedCheck_733_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_a_725_);
lean_dec(v___x_706_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_733_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v___x_729_; lean_object* v___x_731_; 
v___x_729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_729_, 0, v_a_704_);
lean_ctor_set(v___x_729_, 1, v_a_725_);
if (v_isShared_728_ == 0)
{
lean_ctor_set(v___x_727_, 0, v___x_729_);
v___x_731_ = v___x_727_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v___x_729_);
v___x_731_ = v_reuseFailAlloc_732_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
return v___x_731_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDidSaveTextDocumentParams_toJson_spec__0(lean_object* v_k_736_, lean_object* v_x_737_){
_start:
{
if (lean_obj_tag(v_x_737_) == 0)
{
lean_object* v___x_738_; 
lean_dec_ref(v_k_736_);
v___x_738_ = lean_box(0);
return v___x_738_;
}
else
{
lean_object* v_val_739_; lean_object* v___x_741_; uint8_t v_isShared_742_; uint8_t v_isSharedCheck_749_; 
v_val_739_ = lean_ctor_get(v_x_737_, 0);
v_isSharedCheck_749_ = !lean_is_exclusive(v_x_737_);
if (v_isSharedCheck_749_ == 0)
{
v___x_741_ = v_x_737_;
v_isShared_742_ = v_isSharedCheck_749_;
goto v_resetjp_740_;
}
else
{
lean_inc(v_val_739_);
lean_dec(v_x_737_);
v___x_741_ = lean_box(0);
v_isShared_742_ = v_isSharedCheck_749_;
goto v_resetjp_740_;
}
v_resetjp_740_:
{
lean_object* v___x_744_; 
if (v_isShared_742_ == 0)
{
lean_ctor_set_tag(v___x_741_, 3);
v___x_744_ = v___x_741_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v_val_739_);
v___x_744_ = v_reuseFailAlloc_748_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; 
v___x_745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_745_, 0, v_k_736_);
lean_ctor_set(v___x_745_, 1, v___x_744_);
v___x_746_ = lean_box(0);
v___x_747_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_747_, 0, v___x_745_);
lean_ctor_set(v___x_747_, 1, v___x_746_);
return v___x_747_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDidSaveTextDocumentParams_toJson(lean_object* v_x_750_){
_start:
{
lean_object* v_textDocument_751_; lean_object* v_text_x3f_752_; lean_object* v___x_754_; uint8_t v_isShared_755_; uint8_t v_isSharedCheck_770_; 
v_textDocument_751_ = lean_ctor_get(v_x_750_, 0);
v_text_x3f_752_ = lean_ctor_get(v_x_750_, 1);
v_isSharedCheck_770_ = !lean_is_exclusive(v_x_750_);
if (v_isSharedCheck_770_ == 0)
{
v___x_754_ = v_x_750_;
v_isShared_755_ = v_isSharedCheck_770_;
goto v_resetjp_753_;
}
else
{
lean_inc(v_text_x3f_752_);
lean_inc(v_textDocument_751_);
lean_dec(v_x_750_);
v___x_754_ = lean_box(0);
v_isShared_755_ = v_isSharedCheck_770_;
goto v_resetjp_753_;
}
v_resetjp_753_:
{
lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_759_; 
v___x_756_ = ((lean_object*)(l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__0));
v___x_757_ = l_Lean_Lsp_instToJsonTextDocumentIdentifier_toJson(v_textDocument_751_);
if (v_isShared_755_ == 0)
{
lean_ctor_set(v___x_754_, 1, v___x_757_);
lean_ctor_set(v___x_754_, 0, v___x_756_);
v___x_759_ = v___x_754_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v___x_756_);
lean_ctor_set(v_reuseFailAlloc_769_, 1, v___x_757_);
v___x_759_ = v_reuseFailAlloc_769_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_760_ = lean_box(0);
v___x_761_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_761_, 0, v___x_759_);
lean_ctor_set(v___x_761_, 1, v___x_760_);
v___x_762_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0___closed__0));
v___x_763_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDidSaveTextDocumentParams_toJson_spec__0(v___x_762_, v_text_x3f_752_);
v___x_764_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_764_, 0, v___x_763_);
lean_ctor_set(v___x_764_, 1, v___x_760_);
v___x_765_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_765_, 0, v___x_761_);
lean_ctor_set(v___x_765_, 1, v___x_764_);
v___x_766_ = ((lean_object*)(l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__1));
v___x_767_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson_spec__0(v___x_765_, v___x_766_);
v___x_768_ = l_Lean_Json_mkObj(v___x_767_);
lean_dec(v___x_767_);
return v___x_768_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson_spec__0(lean_object* v_j_773_, lean_object* v_k_774_){
_start:
{
lean_object* v___x_775_; lean_object* v___x_776_; 
v___x_775_ = l_Lean_Json_getObjValD(v_j_773_, v_k_774_);
v___x_776_ = l_Lean_Lsp_instFromJsonTextDocumentIdentifier_fromJson(v___x_775_);
return v___x_776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson_spec__0___boxed(lean_object* v_j_777_, lean_object* v_k_778_){
_start:
{
lean_object* v_res_779_; 
v_res_779_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson_spec__0(v_j_777_, v_k_778_);
lean_dec_ref(v_k_778_);
return v_res_779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson_spec__1_spec__1(lean_object* v_x_782_){
_start:
{
if (lean_obj_tag(v_x_782_) == 0)
{
lean_object* v___x_783_; 
v___x_783_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson_spec__1_spec__1___closed__0));
return v___x_783_;
}
else
{
lean_object* v___x_784_; 
v___x_784_ = l_Lean_Json_getStr_x3f(v_x_782_);
if (lean_obj_tag(v___x_784_) == 0)
{
lean_object* v_a_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_792_; 
v_a_785_ = lean_ctor_get(v___x_784_, 0);
v_isSharedCheck_792_ = !lean_is_exclusive(v___x_784_);
if (v_isSharedCheck_792_ == 0)
{
v___x_787_ = v___x_784_;
v_isShared_788_ = v_isSharedCheck_792_;
goto v_resetjp_786_;
}
else
{
lean_inc(v_a_785_);
lean_dec(v___x_784_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_792_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
lean_object* v___x_790_; 
if (v_isShared_788_ == 0)
{
v___x_790_ = v___x_787_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v_a_785_);
v___x_790_ = v_reuseFailAlloc_791_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
return v___x_790_;
}
}
}
else
{
lean_object* v_a_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_801_; 
v_a_793_ = lean_ctor_get(v___x_784_, 0);
v_isSharedCheck_801_ = !lean_is_exclusive(v___x_784_);
if (v_isSharedCheck_801_ == 0)
{
v___x_795_ = v___x_784_;
v_isShared_796_ = v_isSharedCheck_801_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_a_793_);
lean_dec(v___x_784_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_801_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v___x_797_; lean_object* v___x_799_; 
v___x_797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_797_, 0, v_a_793_);
if (v_isShared_796_ == 0)
{
lean_ctor_set(v___x_795_, 0, v___x_797_);
v___x_799_ = v___x_795_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v___x_797_);
v___x_799_ = v_reuseFailAlloc_800_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
return v___x_799_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson_spec__1(lean_object* v_j_802_, lean_object* v_k_803_){
_start:
{
lean_object* v___x_804_; lean_object* v___x_805_; 
v___x_804_ = l_Lean_Json_getObjValD(v_j_802_, v_k_803_);
v___x_805_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson_spec__1_spec__1(v___x_804_);
return v___x_805_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson_spec__1___boxed(lean_object* v_j_806_, lean_object* v_k_807_){
_start:
{
lean_object* v_res_808_; 
v_res_808_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson_spec__1(v_j_806_, v_k_807_);
lean_dec_ref(v_k_807_);
return v_res_808_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__2(void){
_start:
{
uint8_t v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; 
v___x_814_ = 1;
v___x_815_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__1));
v___x_816_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_815_, v___x_814_);
return v___x_816_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__3(void){
_start:
{
lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; 
v___x_817_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__5));
v___x_818_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__2, &l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__2);
v___x_819_ = lean_string_append(v___x_818_, v___x_817_);
return v___x_819_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; 
v___x_820_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__8);
v___x_821_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__3);
v___x_822_ = lean_string_append(v___x_821_, v___x_820_);
return v___x_822_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__5(void){
_start:
{
lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; 
v___x_823_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__10));
v___x_824_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__4);
v___x_825_ = lean_string_append(v___x_824_, v___x_823_);
return v___x_825_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__8(void){
_start:
{
uint8_t v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; 
v___x_829_ = 1;
v___x_830_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__7));
v___x_831_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_830_, v___x_829_);
return v___x_831_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__9(void){
_start:
{
lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; 
v___x_832_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__8);
v___x_833_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__3);
v___x_834_ = lean_string_append(v___x_833_, v___x_832_);
return v___x_834_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__10(void){
_start:
{
lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; 
v___x_835_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__10));
v___x_836_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__9, &l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__9);
v___x_837_ = lean_string_append(v___x_836_, v___x_835_);
return v___x_837_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson(lean_object* v_json_838_){
_start:
{
lean_object* v___x_839_; lean_object* v___x_840_; 
v___x_839_ = ((lean_object*)(l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__0));
lean_inc(v_json_838_);
v___x_840_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson_spec__0(v_json_838_, v___x_839_);
if (lean_obj_tag(v___x_840_) == 0)
{
lean_object* v_a_841_; lean_object* v___x_843_; uint8_t v_isShared_844_; uint8_t v_isSharedCheck_850_; 
lean_dec(v_json_838_);
v_a_841_ = lean_ctor_get(v___x_840_, 0);
v_isSharedCheck_850_ = !lean_is_exclusive(v___x_840_);
if (v_isSharedCheck_850_ == 0)
{
v___x_843_ = v___x_840_;
v_isShared_844_ = v_isSharedCheck_850_;
goto v_resetjp_842_;
}
else
{
lean_inc(v_a_841_);
lean_dec(v___x_840_);
v___x_843_ = lean_box(0);
v_isShared_844_ = v_isSharedCheck_850_;
goto v_resetjp_842_;
}
v_resetjp_842_:
{
lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_848_; 
v___x_845_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__5, &l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__5);
v___x_846_ = lean_string_append(v___x_845_, v_a_841_);
lean_dec(v_a_841_);
if (v_isShared_844_ == 0)
{
lean_ctor_set(v___x_843_, 0, v___x_846_);
v___x_848_ = v___x_843_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v___x_846_);
v___x_848_ = v_reuseFailAlloc_849_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
return v___x_848_;
}
}
}
else
{
if (lean_obj_tag(v___x_840_) == 0)
{
lean_object* v_a_851_; lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_858_; 
lean_dec(v_json_838_);
v_a_851_ = lean_ctor_get(v___x_840_, 0);
v_isSharedCheck_858_ = !lean_is_exclusive(v___x_840_);
if (v_isSharedCheck_858_ == 0)
{
v___x_853_ = v___x_840_;
v_isShared_854_ = v_isSharedCheck_858_;
goto v_resetjp_852_;
}
else
{
lean_inc(v_a_851_);
lean_dec(v___x_840_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_858_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
lean_object* v___x_856_; 
if (v_isShared_854_ == 0)
{
lean_ctor_set_tag(v___x_853_, 0);
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
lean_object* v_a_859_; lean_object* v___x_860_; lean_object* v___x_861_; 
v_a_859_ = lean_ctor_get(v___x_840_, 0);
lean_inc(v_a_859_);
lean_dec_ref_known(v___x_840_, 1);
v___x_860_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0___closed__0));
v___x_861_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson_spec__1(v_json_838_, v___x_860_);
if (lean_obj_tag(v___x_861_) == 0)
{
lean_object* v_a_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_871_; 
lean_dec(v_a_859_);
v_a_862_ = lean_ctor_get(v___x_861_, 0);
v_isSharedCheck_871_ = !lean_is_exclusive(v___x_861_);
if (v_isSharedCheck_871_ == 0)
{
v___x_864_ = v___x_861_;
v_isShared_865_ = v_isSharedCheck_871_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_a_862_);
lean_dec(v___x_861_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_871_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_869_; 
v___x_866_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__10, &l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__10);
v___x_867_ = lean_string_append(v___x_866_, v_a_862_);
lean_dec(v_a_862_);
if (v_isShared_865_ == 0)
{
lean_ctor_set(v___x_864_, 0, v___x_867_);
v___x_869_ = v___x_864_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v___x_867_);
v___x_869_ = v_reuseFailAlloc_870_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
return v___x_869_;
}
}
}
else
{
if (lean_obj_tag(v___x_861_) == 0)
{
lean_object* v_a_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_879_; 
lean_dec(v_a_859_);
v_a_872_ = lean_ctor_get(v___x_861_, 0);
v_isSharedCheck_879_ = !lean_is_exclusive(v___x_861_);
if (v_isSharedCheck_879_ == 0)
{
v___x_874_ = v___x_861_;
v_isShared_875_ = v_isSharedCheck_879_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_a_872_);
lean_dec(v___x_861_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_879_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
lean_object* v___x_877_; 
if (v_isShared_875_ == 0)
{
lean_ctor_set_tag(v___x_874_, 0);
v___x_877_ = v___x_874_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v_a_872_);
v___x_877_ = v_reuseFailAlloc_878_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
return v___x_877_;
}
}
}
else
{
lean_object* v_a_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_888_; 
v_a_880_ = lean_ctor_get(v___x_861_, 0);
v_isSharedCheck_888_ = !lean_is_exclusive(v___x_861_);
if (v_isSharedCheck_888_ == 0)
{
v___x_882_ = v___x_861_;
v_isShared_883_ = v_isSharedCheck_888_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_a_880_);
lean_dec(v___x_861_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_888_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
lean_object* v___x_884_; lean_object* v___x_886_; 
v___x_884_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_884_, 0, v_a_859_);
lean_ctor_set(v___x_884_, 1, v_a_880_);
if (v_isShared_883_ == 0)
{
lean_ctor_set(v___x_882_, 0, v___x_884_);
v___x_886_ = v___x_882_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v___x_884_);
v___x_886_ = v_reuseFailAlloc_887_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
return v___x_886_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonSaveOptions_toJson(uint8_t v_x_892_){
_start:
{
lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; 
v___x_893_ = ((lean_object*)(l_Lean_Lsp_instToJsonSaveOptions_toJson___closed__0));
v___x_894_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_894_, 0, v_x_892_);
v___x_895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_895_, 0, v___x_893_);
lean_ctor_set(v___x_895_, 1, v___x_894_);
v___x_896_ = lean_box(0);
v___x_897_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_897_, 0, v___x_895_);
lean_ctor_set(v___x_897_, 1, v___x_896_);
v___x_898_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_898_, 0, v___x_897_);
lean_ctor_set(v___x_898_, 1, v___x_896_);
v___x_899_ = ((lean_object*)(l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__1));
v___x_900_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson_spec__0(v___x_898_, v___x_899_);
v___x_901_ = l_Lean_Json_mkObj(v___x_900_);
lean_dec(v___x_900_);
return v___x_901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonSaveOptions_toJson___boxed(lean_object* v_x_902_){
_start:
{
uint8_t v_x_29__boxed_903_; lean_object* v_res_904_; 
v_x_29__boxed_903_ = lean_unbox(v_x_902_);
v_res_904_ = l_Lean_Lsp_instToJsonSaveOptions_toJson(v_x_29__boxed_903_);
return v_res_904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonSaveOptions_fromJson_spec__0(lean_object* v_j_907_, lean_object* v_k_908_){
_start:
{
lean_object* v___x_909_; lean_object* v___x_910_; 
v___x_909_ = l_Lean_Json_getObjValD(v_j_907_, v_k_908_);
v___x_910_ = l_Lean_Json_getBool_x3f(v___x_909_);
lean_dec(v___x_909_);
return v___x_910_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonSaveOptions_fromJson_spec__0___boxed(lean_object* v_j_911_, lean_object* v_k_912_){
_start:
{
lean_object* v_res_913_; 
v_res_913_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonSaveOptions_fromJson_spec__0(v_j_911_, v_k_912_);
lean_dec_ref(v_k_912_);
return v_res_913_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__2(void){
_start:
{
uint8_t v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_919_ = 1;
v___x_920_ = ((lean_object*)(l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__1));
v___x_921_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_920_, v___x_919_);
return v___x_921_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__3(void){
_start:
{
lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; 
v___x_922_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__5));
v___x_923_ = lean_obj_once(&l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__2, &l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__2);
v___x_924_ = lean_string_append(v___x_923_, v___x_922_);
return v___x_924_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__5(void){
_start:
{
uint8_t v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; 
v___x_927_ = 1;
v___x_928_ = ((lean_object*)(l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__4));
v___x_929_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_928_, v___x_927_);
return v___x_929_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__6(void){
_start:
{
lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; 
v___x_930_ = lean_obj_once(&l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__5, &l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__5);
v___x_931_ = lean_obj_once(&l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__3, &l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__3);
v___x_932_ = lean_string_append(v___x_931_, v___x_930_);
return v___x_932_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__7(void){
_start:
{
lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; 
v___x_933_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__10));
v___x_934_ = lean_obj_once(&l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__6, &l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__6);
v___x_935_ = lean_string_append(v___x_934_, v___x_933_);
return v___x_935_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonSaveOptions_fromJson(lean_object* v_json_936_){
_start:
{
lean_object* v___x_937_; lean_object* v___x_938_; 
v___x_937_ = ((lean_object*)(l_Lean_Lsp_instToJsonSaveOptions_toJson___closed__0));
v___x_938_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonSaveOptions_fromJson_spec__0(v_json_936_, v___x_937_);
if (lean_obj_tag(v___x_938_) == 0)
{
lean_object* v_a_939_; lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_948_; 
v_a_939_ = lean_ctor_get(v___x_938_, 0);
v_isSharedCheck_948_ = !lean_is_exclusive(v___x_938_);
if (v_isSharedCheck_948_ == 0)
{
v___x_941_ = v___x_938_;
v_isShared_942_ = v_isSharedCheck_948_;
goto v_resetjp_940_;
}
else
{
lean_inc(v_a_939_);
lean_dec(v___x_938_);
v___x_941_ = lean_box(0);
v_isShared_942_ = v_isSharedCheck_948_;
goto v_resetjp_940_;
}
v_resetjp_940_:
{
lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_946_; 
v___x_943_ = lean_obj_once(&l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__7, &l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__7);
v___x_944_ = lean_string_append(v___x_943_, v_a_939_);
lean_dec(v_a_939_);
if (v_isShared_942_ == 0)
{
lean_ctor_set(v___x_941_, 0, v___x_944_);
v___x_946_ = v___x_941_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v___x_944_);
v___x_946_ = v_reuseFailAlloc_947_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
return v___x_946_;
}
}
}
else
{
if (lean_obj_tag(v___x_938_) == 0)
{
lean_object* v_a_949_; lean_object* v___x_951_; uint8_t v_isShared_952_; uint8_t v_isSharedCheck_956_; 
v_a_949_ = lean_ctor_get(v___x_938_, 0);
v_isSharedCheck_956_ = !lean_is_exclusive(v___x_938_);
if (v_isSharedCheck_956_ == 0)
{
v___x_951_ = v___x_938_;
v_isShared_952_ = v_isSharedCheck_956_;
goto v_resetjp_950_;
}
else
{
lean_inc(v_a_949_);
lean_dec(v___x_938_);
v___x_951_ = lean_box(0);
v_isShared_952_ = v_isSharedCheck_956_;
goto v_resetjp_950_;
}
v_resetjp_950_:
{
lean_object* v___x_954_; 
if (v_isShared_952_ == 0)
{
lean_ctor_set_tag(v___x_951_, 0);
v___x_954_ = v___x_951_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v_a_949_);
v___x_954_ = v_reuseFailAlloc_955_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
return v___x_954_;
}
}
}
else
{
lean_object* v_a_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_964_; 
v_a_957_ = lean_ctor_get(v___x_938_, 0);
v_isSharedCheck_964_ = !lean_is_exclusive(v___x_938_);
if (v_isSharedCheck_964_ == 0)
{
v___x_959_ = v___x_938_;
v_isShared_960_ = v_isSharedCheck_964_;
goto v_resetjp_958_;
}
else
{
lean_inc(v_a_957_);
lean_dec(v___x_938_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_964_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
lean_object* v___x_962_; 
if (v_isShared_960_ == 0)
{
v___x_962_ = v___x_959_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v_a_957_);
v___x_962_ = v_reuseFailAlloc_963_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
return v___x_962_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDidCloseTextDocumentParams_toJson(lean_object* v_x_967_){
_start:
{
lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; 
v___x_968_ = ((lean_object*)(l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__0));
v___x_969_ = l_Lean_Lsp_instToJsonTextDocumentIdentifier_toJson(v_x_967_);
v___x_970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_970_, 0, v___x_968_);
lean_ctor_set(v___x_970_, 1, v___x_969_);
v___x_971_ = lean_box(0);
v___x_972_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_972_, 0, v___x_970_);
lean_ctor_set(v___x_972_, 1, v___x_971_);
v___x_973_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_973_, 0, v___x_972_);
lean_ctor_set(v___x_973_, 1, v___x_971_);
v___x_974_ = ((lean_object*)(l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__1));
v___x_975_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson_spec__0(v___x_973_, v___x_974_);
v___x_976_ = l_Lean_Json_mkObj(v___x_975_);
lean_dec(v___x_975_);
return v___x_976_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__2(void){
_start:
{
uint8_t v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; 
v___x_984_ = 1;
v___x_985_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__1));
v___x_986_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_985_, v___x_984_);
return v___x_986_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__3(void){
_start:
{
lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; 
v___x_987_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__5));
v___x_988_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__2, &l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__2);
v___x_989_ = lean_string_append(v___x_988_, v___x_987_);
return v___x_989_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; 
v___x_990_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__8);
v___x_991_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__3);
v___x_992_ = lean_string_append(v___x_991_, v___x_990_);
return v___x_992_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__5(void){
_start:
{
lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; 
v___x_993_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__10));
v___x_994_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__4);
v___x_995_ = lean_string_append(v___x_994_, v___x_993_);
return v___x_995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson(lean_object* v_json_996_){
_start:
{
lean_object* v___x_997_; lean_object* v___x_998_; 
v___x_997_ = ((lean_object*)(l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__0));
v___x_998_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson_spec__0(v_json_996_, v___x_997_);
if (lean_obj_tag(v___x_998_) == 0)
{
lean_object* v_a_999_; lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1008_; 
v_a_999_ = lean_ctor_get(v___x_998_, 0);
v_isSharedCheck_1008_ = !lean_is_exclusive(v___x_998_);
if (v_isSharedCheck_1008_ == 0)
{
v___x_1001_ = v___x_998_;
v_isShared_1002_ = v_isSharedCheck_1008_;
goto v_resetjp_1000_;
}
else
{
lean_inc(v_a_999_);
lean_dec(v___x_998_);
v___x_1001_ = lean_box(0);
v_isShared_1002_ = v_isSharedCheck_1008_;
goto v_resetjp_1000_;
}
v_resetjp_1000_:
{
lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1006_; 
v___x_1003_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__5, &l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__5);
v___x_1004_ = lean_string_append(v___x_1003_, v_a_999_);
lean_dec(v_a_999_);
if (v_isShared_1002_ == 0)
{
lean_ctor_set(v___x_1001_, 0, v___x_1004_);
v___x_1006_ = v___x_1001_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v___x_1004_);
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
if (lean_obj_tag(v___x_998_) == 0)
{
lean_object* v_a_1009_; lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1016_; 
v_a_1009_ = lean_ctor_get(v___x_998_, 0);
v_isSharedCheck_1016_ = !lean_is_exclusive(v___x_998_);
if (v_isSharedCheck_1016_ == 0)
{
v___x_1011_ = v___x_998_;
v_isShared_1012_ = v_isSharedCheck_1016_;
goto v_resetjp_1010_;
}
else
{
lean_inc(v_a_1009_);
lean_dec(v___x_998_);
v___x_1011_ = lean_box(0);
v_isShared_1012_ = v_isSharedCheck_1016_;
goto v_resetjp_1010_;
}
v_resetjp_1010_:
{
lean_object* v___x_1014_; 
if (v_isShared_1012_ == 0)
{
lean_ctor_set_tag(v___x_1011_, 0);
v___x_1014_ = v___x_1011_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v_a_1009_);
v___x_1014_ = v_reuseFailAlloc_1015_;
goto v_reusejp_1013_;
}
v_reusejp_1013_:
{
return v___x_1014_;
}
}
}
else
{
lean_object* v_a_1017_; lean_object* v___x_1019_; uint8_t v_isShared_1020_; uint8_t v_isSharedCheck_1024_; 
v_a_1017_ = lean_ctor_get(v___x_998_, 0);
v_isSharedCheck_1024_ = !lean_is_exclusive(v___x_998_);
if (v_isSharedCheck_1024_ == 0)
{
v___x_1019_ = v___x_998_;
v_isShared_1020_ = v_isSharedCheck_1024_;
goto v_resetjp_1018_;
}
else
{
lean_inc(v_a_1017_);
lean_dec(v___x_998_);
v___x_1019_ = lean_box(0);
v_isShared_1020_ = v_isSharedCheck_1024_;
goto v_resetjp_1018_;
}
v_resetjp_1018_:
{
lean_object* v___x_1022_; 
if (v_isShared_1020_ == 0)
{
v___x_1022_ = v___x_1019_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v_a_1017_);
v___x_1022_ = v_reuseFailAlloc_1023_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
return v___x_1022_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson_spec__0(lean_object* v_k_1027_, lean_object* v_x_1028_){
_start:
{
if (lean_obj_tag(v_x_1028_) == 0)
{
lean_object* v___x_1029_; 
lean_dec_ref(v_k_1027_);
v___x_1029_ = lean_box(0);
return v___x_1029_;
}
else
{
lean_object* v_val_1030_; uint8_t v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; 
v_val_1030_ = lean_ctor_get(v_x_1028_, 0);
v___x_1031_ = lean_unbox(v_val_1030_);
v___x_1032_ = l_Lean_Lsp_instToJsonSaveOptions_toJson(v___x_1031_);
v___x_1033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1033_, 0, v_k_1027_);
lean_ctor_set(v___x_1033_, 1, v___x_1032_);
v___x_1034_ = lean_box(0);
v___x_1035_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1035_, 0, v___x_1033_);
lean_ctor_set(v___x_1035_, 1, v___x_1034_);
return v___x_1035_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson_spec__0___boxed(lean_object* v_k_1036_, lean_object* v_x_1037_){
_start:
{
lean_object* v_res_1038_; 
v_res_1038_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson_spec__0(v_k_1036_, v_x_1037_);
lean_dec(v_x_1037_);
return v_res_1038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson(lean_object* v_x_1044_){
_start:
{
uint8_t v_openClose_1045_; uint8_t v_change_1046_; uint8_t v_willSave_1047_; uint8_t v_willSaveWaitUntil_1048_; lean_object* v_save_x3f_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___y_1057_; 
v_openClose_1045_ = lean_ctor_get_uint8(v_x_1044_, sizeof(void*)*1);
v_change_1046_ = lean_ctor_get_uint8(v_x_1044_, sizeof(void*)*1 + 1);
v_willSave_1047_ = lean_ctor_get_uint8(v_x_1044_, sizeof(void*)*1 + 2);
v_willSaveWaitUntil_1048_ = lean_ctor_get_uint8(v_x_1044_, sizeof(void*)*1 + 3);
v_save_x3f_1049_ = lean_ctor_get(v_x_1044_, 0);
v___x_1050_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__0));
v___x_1051_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1051_, 0, v_openClose_1045_);
v___x_1052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1052_, 0, v___x_1050_);
lean_ctor_set(v___x_1052_, 1, v___x_1051_);
v___x_1053_ = lean_box(0);
v___x_1054_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1052_);
lean_ctor_set(v___x_1054_, 1, v___x_1053_);
v___x_1055_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__1));
switch(v_change_1046_)
{
case 0:
{
lean_object* v___x_1078_; 
v___x_1078_ = lean_obj_once(&l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__1, &l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__1_once, _init_l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__1);
v___y_1057_ = v___x_1078_;
goto v___jp_1056_;
}
case 1:
{
lean_object* v___x_1079_; 
v___x_1079_ = lean_obj_once(&l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__3, &l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__3_once, _init_l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__3);
v___y_1057_ = v___x_1079_;
goto v___jp_1056_;
}
default: 
{
lean_object* v___x_1080_; 
v___x_1080_ = lean_obj_once(&l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__5, &l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__5_once, _init_l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__5);
v___y_1057_ = v___x_1080_;
goto v___jp_1056_;
}
}
v___jp_1056_:
{
lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; 
lean_inc(v___y_1057_);
v___x_1058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1058_, 0, v___x_1055_);
lean_ctor_set(v___x_1058_, 1, v___y_1057_);
v___x_1059_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1059_, 0, v___x_1058_);
lean_ctor_set(v___x_1059_, 1, v___x_1053_);
v___x_1060_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__2));
v___x_1061_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1061_, 0, v_willSave_1047_);
v___x_1062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1062_, 0, v___x_1060_);
lean_ctor_set(v___x_1062_, 1, v___x_1061_);
v___x_1063_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1063_, 0, v___x_1062_);
lean_ctor_set(v___x_1063_, 1, v___x_1053_);
v___x_1064_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__3));
v___x_1065_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1065_, 0, v_willSaveWaitUntil_1048_);
v___x_1066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1066_, 0, v___x_1064_);
lean_ctor_set(v___x_1066_, 1, v___x_1065_);
v___x_1067_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1067_, 0, v___x_1066_);
lean_ctor_set(v___x_1067_, 1, v___x_1053_);
v___x_1068_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__4));
v___x_1069_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson_spec__0(v___x_1068_, v_save_x3f_1049_);
v___x_1070_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1069_);
lean_ctor_set(v___x_1070_, 1, v___x_1053_);
v___x_1071_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1071_, 0, v___x_1067_);
lean_ctor_set(v___x_1071_, 1, v___x_1070_);
v___x_1072_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1072_, 0, v___x_1063_);
lean_ctor_set(v___x_1072_, 1, v___x_1071_);
v___x_1073_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1073_, 0, v___x_1059_);
lean_ctor_set(v___x_1073_, 1, v___x_1072_);
v___x_1074_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1074_, 0, v___x_1054_);
lean_ctor_set(v___x_1074_, 1, v___x_1073_);
v___x_1075_ = ((lean_object*)(l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__1));
v___x_1076_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson_spec__0(v___x_1074_, v___x_1075_);
v___x_1077_ = l_Lean_Json_mkObj(v___x_1076_);
lean_dec(v___x_1076_);
return v___x_1077_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___boxed(lean_object* v_x_1081_){
_start:
{
lean_object* v_res_1082_; 
v_res_1082_ = l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson(v_x_1081_);
lean_dec_ref(v_x_1081_);
return v_res_1082_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson_spec__0_spec__0(lean_object* v_x_1087_){
_start:
{
if (lean_obj_tag(v_x_1087_) == 0)
{
lean_object* v___x_1088_; 
v___x_1088_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson_spec__0_spec__0___closed__0));
return v___x_1088_;
}
else
{
lean_object* v___x_1089_; 
v___x_1089_ = l_Lean_Lsp_instFromJsonSaveOptions_fromJson(v_x_1087_);
if (lean_obj_tag(v___x_1089_) == 0)
{
lean_object* v_a_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1097_; 
v_a_1090_ = lean_ctor_get(v___x_1089_, 0);
v_isSharedCheck_1097_ = !lean_is_exclusive(v___x_1089_);
if (v_isSharedCheck_1097_ == 0)
{
v___x_1092_ = v___x_1089_;
v_isShared_1093_ = v_isSharedCheck_1097_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_a_1090_);
lean_dec(v___x_1089_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1097_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v___x_1095_; 
if (v_isShared_1093_ == 0)
{
v___x_1095_ = v___x_1092_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v_a_1090_);
v___x_1095_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
return v___x_1095_;
}
}
}
else
{
lean_object* v_a_1098_; lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1106_; 
v_a_1098_ = lean_ctor_get(v___x_1089_, 0);
v_isSharedCheck_1106_ = !lean_is_exclusive(v___x_1089_);
if (v_isSharedCheck_1106_ == 0)
{
v___x_1100_ = v___x_1089_;
v_isShared_1101_ = v_isSharedCheck_1106_;
goto v_resetjp_1099_;
}
else
{
lean_inc(v_a_1098_);
lean_dec(v___x_1089_);
v___x_1100_ = lean_box(0);
v_isShared_1101_ = v_isSharedCheck_1106_;
goto v_resetjp_1099_;
}
v_resetjp_1099_:
{
lean_object* v___x_1102_; lean_object* v___x_1104_; 
v___x_1102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1102_, 0, v_a_1098_);
if (v_isShared_1101_ == 0)
{
lean_ctor_set(v___x_1100_, 0, v___x_1102_);
v___x_1104_ = v___x_1100_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v___x_1102_);
v___x_1104_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
return v___x_1104_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson_spec__0(lean_object* v_j_1107_, lean_object* v_k_1108_){
_start:
{
lean_object* v___x_1109_; lean_object* v___x_1110_; 
v___x_1109_ = l_Lean_Json_getObjValD(v_j_1107_, v_k_1108_);
v___x_1110_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson_spec__0_spec__0(v___x_1109_);
return v___x_1110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson_spec__0___boxed(lean_object* v_j_1111_, lean_object* v_k_1112_){
_start:
{
lean_object* v_res_1113_; 
v_res_1113_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson_spec__0(v_j_1111_, v_k_1112_);
lean_dec_ref(v_k_1112_);
return v_res_1113_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__2(void){
_start:
{
uint8_t v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; 
v___x_1119_ = 1;
v___x_1120_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__1));
v___x_1121_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1120_, v___x_1119_);
return v___x_1121_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3(void){
_start:
{
lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; 
v___x_1122_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__5));
v___x_1123_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__2, &l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__2);
v___x_1124_ = lean_string_append(v___x_1123_, v___x_1122_);
return v___x_1124_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__5(void){
_start:
{
uint8_t v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; 
v___x_1127_ = 1;
v___x_1128_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__4));
v___x_1129_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1128_, v___x_1127_);
return v___x_1129_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__6(void){
_start:
{
lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; 
v___x_1130_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__5, &l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__5);
v___x_1131_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3, &l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3);
v___x_1132_ = lean_string_append(v___x_1131_, v___x_1130_);
return v___x_1132_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__7(void){
_start:
{
lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; 
v___x_1133_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__10));
v___x_1134_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__6, &l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__6);
v___x_1135_ = lean_string_append(v___x_1134_, v___x_1133_);
return v___x_1135_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__9(void){
_start:
{
uint8_t v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; 
v___x_1138_ = 1;
v___x_1139_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__8));
v___x_1140_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1139_, v___x_1138_);
return v___x_1140_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__10(void){
_start:
{
lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; 
v___x_1141_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__9, &l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__9);
v___x_1142_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3, &l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3);
v___x_1143_ = lean_string_append(v___x_1142_, v___x_1141_);
return v___x_1143_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__11(void){
_start:
{
lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; 
v___x_1144_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__10));
v___x_1145_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__10, &l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__10);
v___x_1146_ = lean_string_append(v___x_1145_, v___x_1144_);
return v___x_1146_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__13(void){
_start:
{
uint8_t v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; 
v___x_1149_ = 1;
v___x_1150_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__12));
v___x_1151_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1150_, v___x_1149_);
return v___x_1151_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__14(void){
_start:
{
lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; 
v___x_1152_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__13, &l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__13);
v___x_1153_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3, &l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3);
v___x_1154_ = lean_string_append(v___x_1153_, v___x_1152_);
return v___x_1154_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__15(void){
_start:
{
lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; 
v___x_1155_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__10));
v___x_1156_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__14, &l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__14_once, _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__14);
v___x_1157_ = lean_string_append(v___x_1156_, v___x_1155_);
return v___x_1157_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__17(void){
_start:
{
uint8_t v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; 
v___x_1160_ = 1;
v___x_1161_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__16));
v___x_1162_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1161_, v___x_1160_);
return v___x_1162_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__18(void){
_start:
{
lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; 
v___x_1163_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__17, &l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__17_once, _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__17);
v___x_1164_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3, &l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3);
v___x_1165_ = lean_string_append(v___x_1164_, v___x_1163_);
return v___x_1165_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__19(void){
_start:
{
lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; 
v___x_1166_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__10));
v___x_1167_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__18, &l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__18_once, _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__18);
v___x_1168_ = lean_string_append(v___x_1167_, v___x_1166_);
return v___x_1168_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__22(void){
_start:
{
uint8_t v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; 
v___x_1172_ = 1;
v___x_1173_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__21));
v___x_1174_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1173_, v___x_1172_);
return v___x_1174_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__23(void){
_start:
{
lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; 
v___x_1175_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__22, &l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__22_once, _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__22);
v___x_1176_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3, &l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3);
v___x_1177_ = lean_string_append(v___x_1176_, v___x_1175_);
return v___x_1177_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__24(void){
_start:
{
lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; 
v___x_1178_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__10));
v___x_1179_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__23, &l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__23_once, _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__23);
v___x_1180_ = lean_string_append(v___x_1179_, v___x_1178_);
return v___x_1180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson(lean_object* v_json_1181_){
_start:
{
lean_object* v___x_1182_; lean_object* v___x_1183_; 
v___x_1182_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__0));
lean_inc(v_json_1181_);
v___x_1183_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonSaveOptions_fromJson_spec__0(v_json_1181_, v___x_1182_);
if (lean_obj_tag(v___x_1183_) == 0)
{
lean_object* v_a_1184_; lean_object* v___x_1186_; uint8_t v_isShared_1187_; uint8_t v_isSharedCheck_1193_; 
lean_dec(v_json_1181_);
v_a_1184_ = lean_ctor_get(v___x_1183_, 0);
v_isSharedCheck_1193_ = !lean_is_exclusive(v___x_1183_);
if (v_isSharedCheck_1193_ == 0)
{
v___x_1186_ = v___x_1183_;
v_isShared_1187_ = v_isSharedCheck_1193_;
goto v_resetjp_1185_;
}
else
{
lean_inc(v_a_1184_);
lean_dec(v___x_1183_);
v___x_1186_ = lean_box(0);
v_isShared_1187_ = v_isSharedCheck_1193_;
goto v_resetjp_1185_;
}
v_resetjp_1185_:
{
lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1191_; 
v___x_1188_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__7, &l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__7);
v___x_1189_ = lean_string_append(v___x_1188_, v_a_1184_);
lean_dec(v_a_1184_);
if (v_isShared_1187_ == 0)
{
lean_ctor_set(v___x_1186_, 0, v___x_1189_);
v___x_1191_ = v___x_1186_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v___x_1189_);
v___x_1191_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
return v___x_1191_;
}
}
}
else
{
if (lean_obj_tag(v___x_1183_) == 0)
{
lean_object* v_a_1194_; lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1201_; 
lean_dec(v_json_1181_);
v_a_1194_ = lean_ctor_get(v___x_1183_, 0);
v_isSharedCheck_1201_ = !lean_is_exclusive(v___x_1183_);
if (v_isSharedCheck_1201_ == 0)
{
v___x_1196_ = v___x_1183_;
v_isShared_1197_ = v_isSharedCheck_1201_;
goto v_resetjp_1195_;
}
else
{
lean_inc(v_a_1194_);
lean_dec(v___x_1183_);
v___x_1196_ = lean_box(0);
v_isShared_1197_ = v_isSharedCheck_1201_;
goto v_resetjp_1195_;
}
v_resetjp_1195_:
{
lean_object* v___x_1199_; 
if (v_isShared_1197_ == 0)
{
lean_ctor_set_tag(v___x_1196_, 0);
v___x_1199_ = v___x_1196_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v_a_1194_);
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
v_a_1202_ = lean_ctor_get(v___x_1183_, 0);
lean_inc(v_a_1202_);
lean_dec_ref_known(v___x_1183_, 1);
v___x_1203_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__1));
lean_inc(v_json_1181_);
v___x_1204_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__1(v_json_1181_, v___x_1203_);
if (lean_obj_tag(v___x_1204_) == 0)
{
lean_object* v_a_1205_; lean_object* v___x_1207_; uint8_t v_isShared_1208_; uint8_t v_isSharedCheck_1214_; 
lean_dec(v_a_1202_);
lean_dec(v_json_1181_);
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
v___x_1209_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__11, &l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__11);
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
if (lean_obj_tag(v___x_1204_) == 0)
{
lean_object* v_a_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1222_; 
lean_dec(v_a_1202_);
lean_dec(v_json_1181_);
v_a_1215_ = lean_ctor_get(v___x_1204_, 0);
v_isSharedCheck_1222_ = !lean_is_exclusive(v___x_1204_);
if (v_isSharedCheck_1222_ == 0)
{
v___x_1217_ = v___x_1204_;
v_isShared_1218_ = v_isSharedCheck_1222_;
goto v_resetjp_1216_;
}
else
{
lean_inc(v_a_1215_);
lean_dec(v___x_1204_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1222_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
lean_object* v___x_1220_; 
if (v_isShared_1218_ == 0)
{
lean_ctor_set_tag(v___x_1217_, 0);
v___x_1220_ = v___x_1217_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v_a_1215_);
v___x_1220_ = v_reuseFailAlloc_1221_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
return v___x_1220_;
}
}
}
else
{
lean_object* v_a_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; 
v_a_1223_ = lean_ctor_get(v___x_1204_, 0);
lean_inc(v_a_1223_);
lean_dec_ref_known(v___x_1204_, 1);
v___x_1224_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__2));
lean_inc(v_json_1181_);
v___x_1225_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonSaveOptions_fromJson_spec__0(v_json_1181_, v___x_1224_);
if (lean_obj_tag(v___x_1225_) == 0)
{
lean_object* v_a_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1235_; 
lean_dec(v_a_1223_);
lean_dec(v_a_1202_);
lean_dec(v_json_1181_);
v_a_1226_ = lean_ctor_get(v___x_1225_, 0);
v_isSharedCheck_1235_ = !lean_is_exclusive(v___x_1225_);
if (v_isSharedCheck_1235_ == 0)
{
v___x_1228_ = v___x_1225_;
v_isShared_1229_ = v_isSharedCheck_1235_;
goto v_resetjp_1227_;
}
else
{
lean_inc(v_a_1226_);
lean_dec(v___x_1225_);
v___x_1228_ = lean_box(0);
v_isShared_1229_ = v_isSharedCheck_1235_;
goto v_resetjp_1227_;
}
v_resetjp_1227_:
{
lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1233_; 
v___x_1230_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__15, &l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__15_once, _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__15);
v___x_1231_ = lean_string_append(v___x_1230_, v_a_1226_);
lean_dec(v_a_1226_);
if (v_isShared_1229_ == 0)
{
lean_ctor_set(v___x_1228_, 0, v___x_1231_);
v___x_1233_ = v___x_1228_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v___x_1231_);
v___x_1233_ = v_reuseFailAlloc_1234_;
goto v_reusejp_1232_;
}
v_reusejp_1232_:
{
return v___x_1233_;
}
}
}
else
{
if (lean_obj_tag(v___x_1225_) == 0)
{
lean_object* v_a_1236_; lean_object* v___x_1238_; uint8_t v_isShared_1239_; uint8_t v_isSharedCheck_1243_; 
lean_dec(v_a_1223_);
lean_dec(v_a_1202_);
lean_dec(v_json_1181_);
v_a_1236_ = lean_ctor_get(v___x_1225_, 0);
v_isSharedCheck_1243_ = !lean_is_exclusive(v___x_1225_);
if (v_isSharedCheck_1243_ == 0)
{
v___x_1238_ = v___x_1225_;
v_isShared_1239_ = v_isSharedCheck_1243_;
goto v_resetjp_1237_;
}
else
{
lean_inc(v_a_1236_);
lean_dec(v___x_1225_);
v___x_1238_ = lean_box(0);
v_isShared_1239_ = v_isSharedCheck_1243_;
goto v_resetjp_1237_;
}
v_resetjp_1237_:
{
lean_object* v___x_1241_; 
if (v_isShared_1239_ == 0)
{
lean_ctor_set_tag(v___x_1238_, 0);
v___x_1241_ = v___x_1238_;
goto v_reusejp_1240_;
}
else
{
lean_object* v_reuseFailAlloc_1242_; 
v_reuseFailAlloc_1242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1242_, 0, v_a_1236_);
v___x_1241_ = v_reuseFailAlloc_1242_;
goto v_reusejp_1240_;
}
v_reusejp_1240_:
{
return v___x_1241_;
}
}
}
else
{
lean_object* v_a_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; 
v_a_1244_ = lean_ctor_get(v___x_1225_, 0);
lean_inc(v_a_1244_);
lean_dec_ref_known(v___x_1225_, 1);
v___x_1245_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__3));
lean_inc(v_json_1181_);
v___x_1246_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonSaveOptions_fromJson_spec__0(v_json_1181_, v___x_1245_);
if (lean_obj_tag(v___x_1246_) == 0)
{
lean_object* v_a_1247_; lean_object* v___x_1249_; uint8_t v_isShared_1250_; uint8_t v_isSharedCheck_1256_; 
lean_dec(v_a_1244_);
lean_dec(v_a_1223_);
lean_dec(v_a_1202_);
lean_dec(v_json_1181_);
v_a_1247_ = lean_ctor_get(v___x_1246_, 0);
v_isSharedCheck_1256_ = !lean_is_exclusive(v___x_1246_);
if (v_isSharedCheck_1256_ == 0)
{
v___x_1249_ = v___x_1246_;
v_isShared_1250_ = v_isSharedCheck_1256_;
goto v_resetjp_1248_;
}
else
{
lean_inc(v_a_1247_);
lean_dec(v___x_1246_);
v___x_1249_ = lean_box(0);
v_isShared_1250_ = v_isSharedCheck_1256_;
goto v_resetjp_1248_;
}
v_resetjp_1248_:
{
lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1254_; 
v___x_1251_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__19, &l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__19_once, _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__19);
v___x_1252_ = lean_string_append(v___x_1251_, v_a_1247_);
lean_dec(v_a_1247_);
if (v_isShared_1250_ == 0)
{
lean_ctor_set(v___x_1249_, 0, v___x_1252_);
v___x_1254_ = v___x_1249_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v___x_1252_);
v___x_1254_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
return v___x_1254_;
}
}
}
else
{
if (lean_obj_tag(v___x_1246_) == 0)
{
lean_object* v_a_1257_; lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1264_; 
lean_dec(v_a_1244_);
lean_dec(v_a_1223_);
lean_dec(v_a_1202_);
lean_dec(v_json_1181_);
v_a_1257_ = lean_ctor_get(v___x_1246_, 0);
v_isSharedCheck_1264_ = !lean_is_exclusive(v___x_1246_);
if (v_isSharedCheck_1264_ == 0)
{
v___x_1259_ = v___x_1246_;
v_isShared_1260_ = v_isSharedCheck_1264_;
goto v_resetjp_1258_;
}
else
{
lean_inc(v_a_1257_);
lean_dec(v___x_1246_);
v___x_1259_ = lean_box(0);
v_isShared_1260_ = v_isSharedCheck_1264_;
goto v_resetjp_1258_;
}
v_resetjp_1258_:
{
lean_object* v___x_1262_; 
if (v_isShared_1260_ == 0)
{
lean_ctor_set_tag(v___x_1259_, 0);
v___x_1262_ = v___x_1259_;
goto v_reusejp_1261_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v_a_1257_);
v___x_1262_ = v_reuseFailAlloc_1263_;
goto v_reusejp_1261_;
}
v_reusejp_1261_:
{
return v___x_1262_;
}
}
}
else
{
lean_object* v_a_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; 
v_a_1265_ = lean_ctor_get(v___x_1246_, 0);
lean_inc(v_a_1265_);
lean_dec_ref_known(v___x_1246_, 1);
v___x_1266_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__4));
v___x_1267_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson_spec__0(v_json_1181_, v___x_1266_);
if (lean_obj_tag(v___x_1267_) == 0)
{
lean_object* v_a_1268_; lean_object* v___x_1270_; uint8_t v_isShared_1271_; uint8_t v_isSharedCheck_1277_; 
lean_dec(v_a_1265_);
lean_dec(v_a_1244_);
lean_dec(v_a_1223_);
lean_dec(v_a_1202_);
v_a_1268_ = lean_ctor_get(v___x_1267_, 0);
v_isSharedCheck_1277_ = !lean_is_exclusive(v___x_1267_);
if (v_isSharedCheck_1277_ == 0)
{
v___x_1270_ = v___x_1267_;
v_isShared_1271_ = v_isSharedCheck_1277_;
goto v_resetjp_1269_;
}
else
{
lean_inc(v_a_1268_);
lean_dec(v___x_1267_);
v___x_1270_ = lean_box(0);
v_isShared_1271_ = v_isSharedCheck_1277_;
goto v_resetjp_1269_;
}
v_resetjp_1269_:
{
lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1275_; 
v___x_1272_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__24, &l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__24_once, _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__24);
v___x_1273_ = lean_string_append(v___x_1272_, v_a_1268_);
lean_dec(v_a_1268_);
if (v_isShared_1271_ == 0)
{
lean_ctor_set(v___x_1270_, 0, v___x_1273_);
v___x_1275_ = v___x_1270_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v___x_1273_);
v___x_1275_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1274_;
}
v_reusejp_1274_:
{
return v___x_1275_;
}
}
}
else
{
if (lean_obj_tag(v___x_1267_) == 0)
{
lean_object* v_a_1278_; lean_object* v___x_1280_; uint8_t v_isShared_1281_; uint8_t v_isSharedCheck_1285_; 
lean_dec(v_a_1265_);
lean_dec(v_a_1244_);
lean_dec(v_a_1223_);
lean_dec(v_a_1202_);
v_a_1278_ = lean_ctor_get(v___x_1267_, 0);
v_isSharedCheck_1285_ = !lean_is_exclusive(v___x_1267_);
if (v_isSharedCheck_1285_ == 0)
{
v___x_1280_ = v___x_1267_;
v_isShared_1281_ = v_isSharedCheck_1285_;
goto v_resetjp_1279_;
}
else
{
lean_inc(v_a_1278_);
lean_dec(v___x_1267_);
v___x_1280_ = lean_box(0);
v_isShared_1281_ = v_isSharedCheck_1285_;
goto v_resetjp_1279_;
}
v_resetjp_1279_:
{
lean_object* v___x_1283_; 
if (v_isShared_1281_ == 0)
{
lean_ctor_set_tag(v___x_1280_, 0);
v___x_1283_ = v___x_1280_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v_a_1278_);
v___x_1283_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
return v___x_1283_;
}
}
}
else
{
lean_object* v_a_1286_; lean_object* v___x_1288_; uint8_t v_isShared_1289_; uint8_t v_isSharedCheck_1298_; 
v_a_1286_ = lean_ctor_get(v___x_1267_, 0);
v_isSharedCheck_1298_ = !lean_is_exclusive(v___x_1267_);
if (v_isSharedCheck_1298_ == 0)
{
v___x_1288_ = v___x_1267_;
v_isShared_1289_ = v_isSharedCheck_1298_;
goto v_resetjp_1287_;
}
else
{
lean_inc(v_a_1286_);
lean_dec(v___x_1267_);
v___x_1288_ = lean_box(0);
v_isShared_1289_ = v_isSharedCheck_1298_;
goto v_resetjp_1287_;
}
v_resetjp_1287_:
{
lean_object* v___x_1290_; uint8_t v___x_1291_; uint8_t v___x_1292_; uint8_t v___x_1293_; uint8_t v___x_1294_; lean_object* v___x_1296_; 
v___x_1290_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v___x_1290_, 0, v_a_1286_);
v___x_1291_ = lean_unbox(v_a_1202_);
lean_dec(v_a_1202_);
lean_ctor_set_uint8(v___x_1290_, sizeof(void*)*1, v___x_1291_);
v___x_1292_ = lean_unbox(v_a_1223_);
lean_dec(v_a_1223_);
lean_ctor_set_uint8(v___x_1290_, sizeof(void*)*1 + 1, v___x_1292_);
v___x_1293_ = lean_unbox(v_a_1244_);
lean_dec(v_a_1244_);
lean_ctor_set_uint8(v___x_1290_, sizeof(void*)*1 + 2, v___x_1293_);
v___x_1294_ = lean_unbox(v_a_1265_);
lean_dec(v_a_1265_);
lean_ctor_set_uint8(v___x_1290_, sizeof(void*)*1 + 3, v___x_1294_);
if (v_isShared_1289_ == 0)
{
lean_ctor_set(v___x_1288_, 0, v___x_1290_);
v___x_1296_ = v___x_1288_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v___x_1290_);
v___x_1296_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
return v___x_1296_;
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

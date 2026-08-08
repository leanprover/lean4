// Lean compiler output
// Module: Lean.Data.Lsp.Extra
// Imports: public import Lean.Data.Lsp.TextSync public import Lean.Server.Rpc.Basic
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Json_getNat_x3f(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_Lean_Json_getBool_x3f(lean_object*);
lean_object* l_Lean_Json_getTag_x3f(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Lsp_instToJsonTextDocumentIdentifier_toJson(lean_object*);
lean_object* l_Lean_Lsp_instToJsonPosition_toJson(lean_object*);
lean_object* lean_uint64_to_nat(uint64_t);
lean_object* l_Lean_bignumToJson(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
lean_object* l_Lean_UInt64_fromJson_x3f(lean_object*);
lean_object* l_Lean_Lsp_instFromJsonRpcWireFormat_fromJson(lean_object*);
lean_object* l_Lean_Lsp_instFromJsonTextDocumentIdentifier_fromJson(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_JsonNumber_fromNat(lean_object*);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Lsp_instFromJsonPosition_fromJson(lean_object*);
lean_object* l_Lean_Lsp_instToJsonRange_toJson(lean_object*);
lean_object* l_Lean_Lsp_instFromJsonRange_fromJson(lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson(lean_object*);
lean_object* l_Lean_Lsp_instToJsonVersionedTextDocumentIdentifier_toJson(lean_object*);
lean_object* l_Lean_Lsp_instToJsonRpcWireFormat_toJson(uint8_t);
lean_object* l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson(lean_object*);
lean_object* l_Lean_Lsp_instToJsonTextDocumentItem_toJson(lean_object*);
lean_object* l_Lean_Name_fromJson_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DependencyBuildMode_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Lsp_DependencyBuildMode_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DependencyBuildMode_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DependencyBuildMode_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DependencyBuildMode_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DependencyBuildMode_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DependencyBuildMode_always_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DependencyBuildMode_always_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DependencyBuildMode_always_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DependencyBuildMode_always_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DependencyBuildMode_once_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DependencyBuildMode_once_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DependencyBuildMode_once_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DependencyBuildMode_once_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DependencyBuildMode_never_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DependencyBuildMode_never_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DependencyBuildMode_never_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DependencyBuildMode_never_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "no inductive tag found"};
static const lean_object* l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__0_value)}};
static const lean_object* l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__1_value;
static const lean_string_object l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "never"};
static const lean_object* l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__2 = (const lean_object*)&l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__2_value;
static const lean_string_object l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "always"};
static const lean_object* l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__3 = (const lean_object*)&l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__3_value;
static const lean_string_object l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "once"};
static const lean_object* l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__4 = (const lean_object*)&l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__4_value;
static const lean_string_object l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "no inductive constructor matched"};
static const lean_object* l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__5 = (const lean_object*)&l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__5_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__5_value)}};
static const lean_object* l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__6 = (const lean_object*)&l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__6_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__7 = (const lean_object*)&l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__7_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__8 = (const lean_object*)&l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__8_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__9 = (const lean_object*)&l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonDependencyBuildMode___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonDependencyBuildMode___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonDependencyBuildMode___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonDependencyBuildMode = (const lean_object*)&l_Lean_Lsp_instFromJsonDependencyBuildMode___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_instToJsonDependencyBuildMode_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__3_value)}};
static const lean_object* l_Lean_Lsp_instToJsonDependencyBuildMode_toJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonDependencyBuildMode_toJson___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_instToJsonDependencyBuildMode_toJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__4_value)}};
static const lean_object* l_Lean_Lsp_instToJsonDependencyBuildMode_toJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instToJsonDependencyBuildMode_toJson___closed__1_value;
static const lean_ctor_object l_Lean_Lsp_instToJsonDependencyBuildMode_toJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__2_value)}};
static const lean_object* l_Lean_Lsp_instToJsonDependencyBuildMode_toJson___closed__2 = (const lean_object*)&l_Lean_Lsp_instToJsonDependencyBuildMode_toJson___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDependencyBuildMode_toJson(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDependencyBuildMode_toJson___boxed(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonDependencyBuildMode___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonDependencyBuildMode_toJson___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonDependencyBuildMode___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonDependencyBuildMode___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonDependencyBuildMode = (const lean_object*)&l_Lean_Lsp_instToJsonDependencyBuildMode___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Lsp_instInhabitedDependencyBuildMode_default;
LEAN_EXPORT uint8_t l_Lean_Lsp_instInhabitedDependencyBuildMode;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson_spec__0___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson_spec__1_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson_spec__1_spec__1___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson_spec__1_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson_spec__1_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson_spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "textDocument"};
static const lean_object* l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__0_value;
static const lean_string_object l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__1_value;
static const lean_string_object l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Lsp"};
static const lean_object* l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__2 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__2_value;
static const lean_string_object l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "LeanDidOpenTextDocumentParams"};
static const lean_object* l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__3 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__3_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__4_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__2_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__4_value_aux_1),((lean_object*)&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__3_value),LEAN_SCALAR_PTR_LITERAL(68, 229, 182, 177, 131, 116, 103, 58)}};
static const lean_object* l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__4 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__4_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__5;
static const lean_string_object l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__7;
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(215, 223, 21, 223, 122, 31, 128, 254)}};
static const lean_object* l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__8 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__8_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__10;
static const lean_string_object l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__12;
static const lean_string_object l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "dependencyBuildMode"};
static const lean_object* l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__13 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__13_value;
static const lean_string_object l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "dependencyBuildMode\?"};
static const lean_object* l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__14 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__14_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__14_value),LEAN_SCALAR_PTR_LITERAL(35, 177, 4, 193, 219, 199, 244, 22)}};
static const lean_object* l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__15 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__15_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__16;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__17;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__18;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(lean_object*, lean_object*);
static const lean_array_object l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams = (const lean_object*)&l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson_spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "uri"};
static const lean_object* l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__0_value;
static const lean_string_object l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "WaitForDiagnosticsParams"};
static const lean_object* l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__1_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__2_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__2_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__2_value_aux_1),((lean_object*)&l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(124, 49, 48, 0, 211, 190, 53, 208)}};
static const lean_object* l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__2 = (const lean_object*)&l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__2_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__3;
static lean_once_cell_t l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__4;
static const lean_ctor_object l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(102, 169, 49, 149, 57, 117, 3, 84)}};
static const lean_object* l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__5 = (const lean_object*)&l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__5_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__6;
static lean_once_cell_t l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__7;
static lean_once_cell_t l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__8;
static const lean_string_object l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "version"};
static const lean_object* l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__9 = (const lean_object*)&l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__9_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__9_value),LEAN_SCALAR_PTR_LITERAL(167, 68, 50, 73, 160, 48, 142, 108)}};
static const lean_object* l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__10 = (const lean_object*)&l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__10_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__11;
static lean_once_cell_t l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__12;
static lean_once_cell_t l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__13;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams = (const lean_object*)&l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonWaitForDiagnosticsParams_toJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonWaitForDiagnosticsParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonWaitForDiagnosticsParams_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonWaitForDiagnosticsParams___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonWaitForDiagnosticsParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonWaitForDiagnosticsParams = (const lean_object*)&l_Lean_Lsp_instToJsonWaitForDiagnosticsParams___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonWaitForDiagnostics___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Lsp_instFromJsonWaitForDiagnostics___lam__0___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonWaitForDiagnostics___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonWaitForDiagnostics___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonWaitForDiagnostics___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonWaitForDiagnostics___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonWaitForDiagnostics___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonWaitForDiagnostics___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonWaitForDiagnostics___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonWaitForDiagnostics = (const lean_object*)&l_Lean_Lsp_instFromJsonWaitForDiagnostics___closed__0_value;
static lean_once_cell_t l_Lean_Lsp_instToJsonWaitForDiagnostics___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instToJsonWaitForDiagnostics___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonWaitForDiagnostics___lam__0(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonWaitForDiagnostics___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonWaitForDiagnostics___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonWaitForDiagnostics___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonWaitForDiagnostics___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonWaitForDiagnostics = (const lean_object*)&l_Lean_Lsp_instToJsonWaitForDiagnostics___closed__0_value;
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForILeansParams_fromJson_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForILeansParams_fromJson_spec__0_spec__0___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForILeansParams_fromJson_spec__0_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForILeansParams_fromJson_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForILeansParams_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForILeansParams_fromJson_spec__0___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForILeansParams_fromJson_spec__1_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForILeansParams_fromJson_spec__1_spec__2___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForILeansParams_fromJson_spec__1_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForILeansParams_fromJson_spec__1_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForILeansParams_fromJson_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForILeansParams_fromJson_spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "WaitForILeansParams"};
static const lean_object* l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__1_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__2_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__1_value_aux_1),((lean_object*)&l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 25, 193, 0, 225, 52, 72, 195)}};
static const lean_object* l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__1_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__2;
static lean_once_cell_t l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__3;
static const lean_string_object l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "uri\?"};
static const lean_object* l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__4 = (const lean_object*)&l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__4_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__4_value),LEAN_SCALAR_PTR_LITERAL(133, 106, 144, 1, 211, 237, 135, 209)}};
static const lean_object* l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__5 = (const lean_object*)&l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__5_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__6;
static lean_once_cell_t l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__7;
static lean_once_cell_t l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__8;
static const lean_string_object l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "version\?"};
static const lean_object* l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__9 = (const lean_object*)&l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__9_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__9_value),LEAN_SCALAR_PTR_LITERAL(251, 148, 229, 74, 154, 149, 54, 79)}};
static const lean_object* l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__10 = (const lean_object*)&l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__10_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__11;
static lean_once_cell_t l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__12;
static lean_once_cell_t l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__13;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonWaitForILeansParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonWaitForILeansParams___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonWaitForILeansParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonWaitForILeansParams = (const lean_object*)&l_Lean_Lsp_instFromJsonWaitForILeansParams___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonWaitForILeansParams_toJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonWaitForILeansParams_toJson_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonWaitForILeansParams_toJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonWaitForILeansParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonWaitForILeansParams_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonWaitForILeansParams___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonWaitForILeansParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonWaitForILeansParams = (const lean_object*)&l_Lean_Lsp_instToJsonWaitForILeansParams___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonWaitForILeans_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Lsp_instFromJsonWaitForILeans_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonWaitForILeans_fromJson___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonWaitForILeans_fromJson(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonWaitForILeans_fromJson___boxed(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonWaitForILeans___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonWaitForILeans_fromJson___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonWaitForILeans___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonWaitForILeans___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonWaitForILeans = (const lean_object*)&l_Lean_Lsp_instFromJsonWaitForILeans___closed__0_value;
static lean_once_cell_t l_Lean_Lsp_instToJsonWaitForILeans_toJson___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instToJsonWaitForILeans_toJson___closed__0;
static lean_once_cell_t l_Lean_Lsp_instToJsonWaitForILeans_toJson___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instToJsonWaitForILeans_toJson___closed__1;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonWaitForILeans_toJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonWaitForILeans___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonWaitForILeans_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonWaitForILeans___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonWaitForILeans___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonWaitForILeans = (const lean_object*)&l_Lean_Lsp_instToJsonWaitForILeans___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanFileProgressKind_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanFileProgressKind_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanFileProgressKind_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanFileProgressKind_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanFileProgressKind_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanFileProgressKind_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanFileProgressKind_processing_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanFileProgressKind_processing_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanFileProgressKind_processing_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanFileProgressKind_processing_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanFileProgressKind_fatalError_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanFileProgressKind_fatalError_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanFileProgressKind_fatalError_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanFileProgressKind_fatalError_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Lsp_instInhabitedLeanFileProgressKind_default;
LEAN_EXPORT uint8_t l_Lean_Lsp_instInhabitedLeanFileProgressKind;
LEAN_EXPORT uint8_t l_Lean_Lsp_instBEqLeanFileProgressKind_beq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqLeanFileProgressKind_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_instBEqLeanFileProgressKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instBEqLeanFileProgressKind_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instBEqLeanFileProgressKind___closed__0 = (const lean_object*)&l_Lean_Lsp_instBEqLeanFileProgressKind___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instBEqLeanFileProgressKind = (const lean_object*)&l_Lean_Lsp_instBEqLeanFileProgressKind___closed__0_value;
static const lean_string_object l_Lean_Lsp_instFromJsonLeanFileProgressKind___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "unknown LeanFileProgressKind '"};
static const lean_object* l_Lean_Lsp_instFromJsonLeanFileProgressKind___lam__0___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanFileProgressKind___lam__0___closed__0_value;
static const lean_string_object l_Lean_Lsp_instFromJsonLeanFileProgressKind___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Lean_Lsp_instFromJsonLeanFileProgressKind___lam__0___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanFileProgressKind___lam__0___closed__1_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanFileProgressKind___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Lsp_instFromJsonLeanFileProgressKind___lam__0___closed__2 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanFileProgressKind___lam__0___closed__2_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanFileProgressKind___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Lsp_instFromJsonLeanFileProgressKind___lam__0___closed__3 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanFileProgressKind___lam__0___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanFileProgressKind___lam__0(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonLeanFileProgressKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonLeanFileProgressKind___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonLeanFileProgressKind___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanFileProgressKind___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonLeanFileProgressKind = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanFileProgressKind___closed__0_value;
static lean_once_cell_t l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__0;
static lean_once_cell_t l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__1;
static lean_once_cell_t l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__2;
static lean_once_cell_t l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonLeanFileProgressKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonLeanFileProgressKind___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonLeanFileProgressKind___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonLeanFileProgressKind = (const lean_object*)&l_Lean_Lsp_instToJsonLeanFileProgressKind___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson_spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "range"};
static const lean_object* l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__0_value;
static const lean_string_object l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "LeanFileProgressProcessingInfo"};
static const lean_object* l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__1_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__2_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__2_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__2_value_aux_1),((lean_object*)&l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(68, 15, 192, 12, 228, 25, 52, 98)}};
static const lean_object* l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__2 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__2_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__3;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__4;
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(113, 10, 234, 83, 106, 95, 218, 176)}};
static const lean_object* l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__5 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__5_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__6;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__7;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__8;
static const lean_string_object l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "kind"};
static const lean_object* l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__9 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__9_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__9_value),LEAN_SCALAR_PTR_LITERAL(90, 186, 66, 236, 16, 221, 215, 158)}};
static const lean_object* l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__10 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__10_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__11;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__12;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__13;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanFileProgressProcessingInfo_toJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonLeanFileProgressProcessingInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonLeanFileProgressProcessingInfo_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonLeanFileProgressProcessingInfo___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonLeanFileProgressProcessingInfo___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonLeanFileProgressProcessingInfo = (const lean_object*)&l_Lean_Lsp_instToJsonLeanFileProgressProcessingInfo___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__1_spec__1_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__1_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "expected JSON array, got '"};
static const lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__1_spec__1___closed__0 = (const lean_object*)&l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__1_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__1_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "LeanFileProgressParams"};
static const lean_object* l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__1_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__2_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__1_value_aux_1),((lean_object*)&l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(26, 45, 76, 213, 123, 38, 90, 250)}};
static const lean_object* l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__1_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__2;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__3;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__4;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__5;
static const lean_string_object l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "processing"};
static const lean_object* l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__6 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__6_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__6_value),LEAN_SCALAR_PTR_LITERAL(149, 182, 20, 229, 69, 242, 87, 150)}};
static const lean_object* l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__7 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__7_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__8;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__9;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__10;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonLeanFileProgressParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonLeanFileProgressParams___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanFileProgressParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonLeanFileProgressParams = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanFileProgressParams___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanFileProgressParams_toJson_spec__0_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanFileProgressParams_toJson_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanFileProgressParams_toJson_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanFileProgressParams_toJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonLeanFileProgressParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonLeanFileProgressParams_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonLeanFileProgressParams___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonLeanFileProgressParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonLeanFileProgressParams = (const lean_object*)&l_Lean_Lsp_instToJsonLeanFileProgressParams___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoalParams_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoalParams_fromJson_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoalParams_fromJson_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoalParams_fromJson_spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "PlainGoalParams"};
static const lean_object* l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__1_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__2_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__1_value_aux_1),((lean_object*)&l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(245, 99, 5, 153, 103, 31, 101, 71)}};
static const lean_object* l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__1_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__2;
static lean_once_cell_t l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__3;
static lean_once_cell_t l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__4;
static lean_once_cell_t l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__5;
static const lean_string_object l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "position"};
static const lean_object* l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__6 = (const lean_object*)&l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__6_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__6_value),LEAN_SCALAR_PTR_LITERAL(91, 172, 67, 66, 136, 94, 119, 158)}};
static const lean_object* l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__7 = (const lean_object*)&l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__7_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__8;
static lean_once_cell_t l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__9;
static lean_once_cell_t l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__10;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonPlainGoalParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonPlainGoalParams___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonPlainGoalParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonPlainGoalParams = (const lean_object*)&l_Lean_Lsp_instFromJsonPlainGoalParams___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonPlainGoalParams_toJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonPlainGoalParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonPlainGoalParams_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonPlainGoalParams___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonPlainGoalParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonPlainGoalParams = (const lean_object*)&l_Lean_Lsp_instToJsonPlainGoalParams___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoal_fromJson_spec__0_spec__0_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoal_fromJson_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoal_fromJson_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoal_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoal_fromJson_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "rendered"};
static const lean_object* l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__0_value;
static const lean_string_object l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "PlainGoal"};
static const lean_object* l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__1_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__2_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__2_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__2_value_aux_1),((lean_object*)&l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(172, 25, 213, 99, 53, 123, 59, 157)}};
static const lean_object* l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__2 = (const lean_object*)&l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__2_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__3;
static lean_once_cell_t l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__4;
static const lean_ctor_object l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(43, 31, 242, 88, 44, 24, 118, 196)}};
static const lean_object* l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__5 = (const lean_object*)&l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__5_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__6;
static lean_once_cell_t l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__7;
static lean_once_cell_t l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__8;
static const lean_string_object l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "goals"};
static const lean_object* l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__9 = (const lean_object*)&l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__9_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__9_value),LEAN_SCALAR_PTR_LITERAL(204, 254, 165, 202, 190, 203, 255, 29)}};
static const lean_object* l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__10 = (const lean_object*)&l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__10_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__11;
static lean_once_cell_t l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__12;
static lean_once_cell_t l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__13;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonPlainGoal_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonPlainGoal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonPlainGoal_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonPlainGoal___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonPlainGoal___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonPlainGoal = (const lean_object*)&l_Lean_Lsp_instFromJsonPlainGoal___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPlainGoal_toJson_spec__0_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPlainGoal_toJson_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonPlainGoal_toJson_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonPlainGoal_toJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonPlainGoal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonPlainGoal_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonPlainGoal___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonPlainGoal___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonPlainGoal = (const lean_object*)&l_Lean_Lsp_instToJsonPlainGoal___closed__0_value;
static const lean_string_object l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "PlainTermGoalParams"};
static const lean_object* l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__1_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__2_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__1_value_aux_1),((lean_object*)&l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(40, 170, 206, 133, 20, 23, 29, 223)}};
static const lean_object* l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__1_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__2;
static lean_once_cell_t l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__3;
static lean_once_cell_t l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__4;
static lean_once_cell_t l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__5;
static lean_once_cell_t l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__6;
static lean_once_cell_t l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__7;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonPlainTermGoalParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonPlainTermGoalParams___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonPlainTermGoalParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonPlainTermGoalParams = (const lean_object*)&l_Lean_Lsp_instFromJsonPlainTermGoalParams___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonPlainTermGoalParams_toJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonPlainTermGoalParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonPlainTermGoalParams_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonPlainTermGoalParams___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonPlainTermGoalParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonPlainTermGoalParams = (const lean_object*)&l_Lean_Lsp_instToJsonPlainTermGoalParams___closed__0_value;
static const lean_string_object l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "goal"};
static const lean_object* l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__0_value;
static const lean_string_object l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "PlainTermGoal"};
static const lean_object* l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__1_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__2_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__2_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__2_value_aux_1),((lean_object*)&l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(233, 174, 90, 221, 19, 29, 108, 39)}};
static const lean_object* l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__2 = (const lean_object*)&l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__2_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__3;
static lean_once_cell_t l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__4;
static const lean_ctor_object l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(42, 195, 11, 21, 122, 139, 251, 141)}};
static const lean_object* l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__5 = (const lean_object*)&l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__5_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__6;
static lean_once_cell_t l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__7;
static lean_once_cell_t l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__8;
static lean_once_cell_t l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__9;
static lean_once_cell_t l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__10;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonPlainTermGoal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonPlainTermGoal___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonPlainTermGoal___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonPlainTermGoal = (const lean_object*)&l_Lean_Lsp_instFromJsonPlainTermGoal___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonPlainTermGoal_toJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonPlainTermGoal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonPlainTermGoal_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonPlainTermGoal___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonPlainTermGoal___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonPlainTermGoal = (const lean_object*)&l_Lean_Lsp_instToJsonPlainTermGoal___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonModuleHierarchyOptions_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Lsp_instFromJsonModuleHierarchyOptions_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonModuleHierarchyOptions_fromJson___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonModuleHierarchyOptions_fromJson(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonModuleHierarchyOptions_fromJson___boxed(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonModuleHierarchyOptions___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonModuleHierarchyOptions_fromJson___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonModuleHierarchyOptions___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonModuleHierarchyOptions___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonModuleHierarchyOptions = (const lean_object*)&l_Lean_Lsp_instFromJsonModuleHierarchyOptions___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonModuleHierarchyOptions_toJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonModuleHierarchyOptions___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonModuleHierarchyOptions_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonModuleHierarchyOptions___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonModuleHierarchyOptions___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonModuleHierarchyOptions = (const lean_object*)&l_Lean_Lsp_instToJsonModuleHierarchyOptions___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonHighlightMatchesOptions_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Lsp_instFromJsonHighlightMatchesOptions_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonHighlightMatchesOptions_fromJson___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonHighlightMatchesOptions_fromJson(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonHighlightMatchesOptions_fromJson___boxed(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonHighlightMatchesOptions___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonHighlightMatchesOptions_fromJson___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonHighlightMatchesOptions___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonHighlightMatchesOptions___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonHighlightMatchesOptions = (const lean_object*)&l_Lean_Lsp_instFromJsonHighlightMatchesOptions___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonHighlightMatchesOptions_toJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonHighlightMatchesOptions___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonHighlightMatchesOptions_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonHighlightMatchesOptions___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonHighlightMatchesOptions___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonHighlightMatchesOptions = (const lean_object*)&l_Lean_Lsp_instToJsonHighlightMatchesOptions___closed__0_value;
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__1_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__1_spec__2___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__1_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__1_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__1___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__0_spec__0___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__0_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__0_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "highlightMatchesProvider"};
static const lean_object* l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__0_value;
static const lean_string_object l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "RpcOptions"};
static const lean_object* l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__1_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__2_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__2_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__2_value_aux_1),((lean_object*)&l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 255, 6, 102, 170, 148, 200, 201)}};
static const lean_object* l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__2 = (const lean_object*)&l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__2_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__3;
static lean_once_cell_t l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__4;
static const lean_string_object l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "highlightMatchesProvider\?"};
static const lean_object* l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__5 = (const lean_object*)&l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__5_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__5_value),LEAN_SCALAR_PTR_LITERAL(38, 29, 162, 199, 252, 108, 15, 67)}};
static const lean_object* l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__6 = (const lean_object*)&l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__6_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__7;
static lean_once_cell_t l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__8;
static lean_once_cell_t l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__9;
static const lean_string_object l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "rpcWireFormat"};
static const lean_object* l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__10 = (const lean_object*)&l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__10_value;
static const lean_string_object l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "rpcWireFormat\?"};
static const lean_object* l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__11 = (const lean_object*)&l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__11_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__11_value),LEAN_SCALAR_PTR_LITERAL(102, 166, 72, 226, 0, 98, 21, 166)}};
static const lean_object* l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__12 = (const lean_object*)&l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__12_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__13;
static lean_once_cell_t l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__14;
static lean_once_cell_t l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__15;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonRpcOptions_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonRpcOptions___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonRpcOptions_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonRpcOptions___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonRpcOptions___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonRpcOptions = (const lean_object*)&l_Lean_Lsp_instFromJsonRpcOptions___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonRpcOptions_toJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonRpcOptions_toJson_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonRpcOptions_toJson_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRpcOptions_toJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonRpcOptions___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonRpcOptions_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonRpcOptions___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonRpcOptions___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonRpcOptions = (const lean_object*)&l_Lean_Lsp_instToJsonRpcOptions___closed__0_value;
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModule_fromJson_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModule_fromJson_spec__0_spec__0___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModule_fromJson_spec__0_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModule_fromJson_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModule_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModule_fromJson_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "name"};
static const lean_object* l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__0_value;
static const lean_string_object l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "LeanModule"};
static const lean_object* l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__1_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__2_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__2_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__2_value_aux_1),((lean_object*)&l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(5, 226, 189, 223, 89, 253, 99, 234)}};
static const lean_object* l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__2 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__2_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__3;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__4;
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(84, 246, 234, 130, 97, 205, 144, 82)}};
static const lean_object* l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__5 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__5_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__6;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__7;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__8;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__9;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__10;
static const lean_string_object l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "data"};
static const lean_object* l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__11 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__11_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanModule_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonLeanModule___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonLeanModule_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonLeanModule___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanModule___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonLeanModule = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanModule___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanModule_toJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanModule_toJson_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanModule_toJson(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanModule_toJson___boxed(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonLeanModule___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonLeanModule_toJson___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonLeanModule___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonLeanModule___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonLeanModule = (const lean_object*)&l_Lean_Lsp_instToJsonLeanModule___closed__0_value;
static const lean_string_object l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "LeanPrepareModuleHierarchyParams"};
static const lean_object* l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__1_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__2_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__1_value_aux_1),((lean_object*)&l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(43, 130, 252, 29, 63, 246, 208, 21)}};
static const lean_object* l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__1_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__2;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__3;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__4;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__5;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanPrepareModuleHierarchyParams_toJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonLeanPrepareModuleHierarchyParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonLeanPrepareModuleHierarchyParams_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonLeanPrepareModuleHierarchyParams___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonLeanPrepareModuleHierarchyParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonLeanPrepareModuleHierarchyParams = (const lean_object*)&l_Lean_Lsp_instToJsonLeanPrepareModuleHierarchyParams___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanImportMetaKind_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanImportMetaKind_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanImportMetaKind_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanImportMetaKind_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanImportMetaKind_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanImportMetaKind_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanImportMetaKind_nonMeta_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanImportMetaKind_nonMeta_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanImportMetaKind_nonMeta_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanImportMetaKind_nonMeta_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanImportMetaKind_meta_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanImportMetaKind_meta_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanImportMetaKind_meta_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanImportMetaKind_meta_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanImportMetaKind_full_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanImportMetaKind_full_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanImportMetaKind_full_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanImportMetaKind_full_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Lsp_instInhabitedLeanImportMetaKind_default;
LEAN_EXPORT uint8_t l_Lean_Lsp_instInhabitedLeanImportMetaKind;
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__0_value)}};
static const lean_object* l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson___closed__0_value;
static const lean_string_object l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "full"};
static const lean_object* l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson___closed__1_value;
static const lean_string_object l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "nonMeta"};
static const lean_object* l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson___closed__2 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson___closed__2_value;
static const lean_string_object l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson___closed__3 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson___closed__3_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__5_value)}};
static const lean_object* l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson___closed__4 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson___closed__4_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson___closed__5 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson___closed__5_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson___closed__6 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson___closed__6_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson___closed__7 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonLeanImportMetaKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonLeanImportMetaKind___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanImportMetaKind___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonLeanImportMetaKind = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanImportMetaKind___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_instToJsonLeanImportMetaKind_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson___closed__2_value)}};
static const lean_object* l_Lean_Lsp_instToJsonLeanImportMetaKind_toJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonLeanImportMetaKind_toJson___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_instToJsonLeanImportMetaKind_toJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson___closed__3_value)}};
static const lean_object* l_Lean_Lsp_instToJsonLeanImportMetaKind_toJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instToJsonLeanImportMetaKind_toJson___closed__1_value;
static const lean_ctor_object l_Lean_Lsp_instToJsonLeanImportMetaKind_toJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson___closed__1_value)}};
static const lean_object* l_Lean_Lsp_instToJsonLeanImportMetaKind_toJson___closed__2 = (const lean_object*)&l_Lean_Lsp_instToJsonLeanImportMetaKind_toJson___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanImportMetaKind_toJson(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanImportMetaKind_toJson___boxed(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonLeanImportMetaKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonLeanImportMetaKind_toJson___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonLeanImportMetaKind___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonLeanImportMetaKind___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonLeanImportMetaKind = (const lean_object*)&l_Lean_Lsp_instToJsonLeanImportMetaKind___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportKind_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportKind_fromJson_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportKind_fromJson_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportKind_fromJson_spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "isPrivate"};
static const lean_object* l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__0_value;
static const lean_string_object l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "LeanImportKind"};
static const lean_object* l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__1_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__2_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__2_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__2_value_aux_1),((lean_object*)&l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(177, 249, 252, 144, 151, 115, 145, 91)}};
static const lean_object* l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__2 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__2_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__3;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__4;
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(92, 167, 107, 177, 104, 44, 74, 9)}};
static const lean_object* l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__5 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__5_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__6;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__7;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__8;
static const lean_string_object l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "isAll"};
static const lean_object* l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__9 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__9_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__9_value),LEAN_SCALAR_PTR_LITERAL(186, 103, 90, 28, 253, 177, 161, 31)}};
static const lean_object* l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__10 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__10_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__11;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__12;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__13;
static const lean_string_object l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "metaKind"};
static const lean_object* l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__14 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__14_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__14_value),LEAN_SCALAR_PTR_LITERAL(84, 247, 21, 161, 252, 107, 127, 31)}};
static const lean_object* l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__15 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__15_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__16;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__17;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__18;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanImportKind_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonLeanImportKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonLeanImportKind_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonLeanImportKind___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanImportKind___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonLeanImportKind = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanImportKind___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanImportKind_toJson(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanImportKind_toJson___boxed(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonLeanImportKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonLeanImportKind_toJson___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonLeanImportKind___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonLeanImportKind___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonLeanImportKind = (const lean_object*)&l_Lean_Lsp_instToJsonLeanImportKind___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImport_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImport_fromJson_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImport_fromJson_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImport_fromJson_spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "module"};
static const lean_object* l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__0_value;
static const lean_string_object l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "LeanImport"};
static const lean_object* l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__1_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__2_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__2_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__2_value_aux_1),((lean_object*)&l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(100, 211, 250, 253, 92, 219, 115, 215)}};
static const lean_object* l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__2 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__2_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__3;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__4;
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(119, 13, 181, 135, 119, 7, 66, 71)}};
static const lean_object* l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__5 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__5_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__6;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__7;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__8;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__9;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__10;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanImport_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonLeanImport___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonLeanImport_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonLeanImport___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanImport___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonLeanImport = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanImport___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanImport_toJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonLeanImport___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonLeanImport_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonLeanImport___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonLeanImport___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonLeanImport = (const lean_object*)&l_Lean_Lsp_instToJsonLeanImport___closed__0_value;
static const lean_string_object l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "LeanModuleHierarchyImportsParams"};
static const lean_object* l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__1_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__2_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__1_value_aux_1),((lean_object*)&l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(17, 35, 67, 120, 117, 216, 54, 148)}};
static const lean_object* l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__1_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__2;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__3;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__4;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__5;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanModuleHierarchyImportsParams_toJson(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanModuleHierarchyImportsParams_toJson___boxed(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonLeanModuleHierarchyImportsParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonLeanModuleHierarchyImportsParams_toJson___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonLeanModuleHierarchyImportsParams___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonLeanModuleHierarchyImportsParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonLeanModuleHierarchyImportsParams = (const lean_object*)&l_Lean_Lsp_instToJsonLeanModuleHierarchyImportsParams___closed__0_value;
static const lean_string_object l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "LeanModuleHierarchyImportedByParams"};
static const lean_object* l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__1_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__2_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__1_value_aux_1),((lean_object*)&l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(30, 78, 155, 173, 168, 91, 80, 184)}};
static const lean_object* l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__1_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__2;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__3;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__4;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__5;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanModuleHierarchyImportedByParams_toJson(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanModuleHierarchyImportedByParams_toJson___boxed(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonLeanModuleHierarchyImportedByParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonLeanModuleHierarchyImportedByParams_toJson___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonLeanModuleHierarchyImportedByParams___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonLeanModuleHierarchyImportedByParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonLeanModuleHierarchyImportedByParams = (const lean_object*)&l_Lean_Lsp_instToJsonLeanModuleHierarchyImportedByParams___closed__0_value;
static const lean_string_object l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "RpcConnectParams"};
static const lean_object* l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__1_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__2_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__1_value_aux_1),((lean_object*)&l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(116, 86, 206, 242, 35, 244, 193, 52)}};
static const lean_object* l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__1_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__2;
static lean_once_cell_t l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__3;
static lean_once_cell_t l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__4;
static lean_once_cell_t l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__5;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonRpcConnectParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonRpcConnectParams___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonRpcConnectParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonRpcConnectParams = (const lean_object*)&l_Lean_Lsp_instFromJsonRpcConnectParams___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRpcConnectParams_toJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonRpcConnectParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonRpcConnectParams_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonRpcConnectParams___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonRpcConnectParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonRpcConnectParams = (const lean_object*)&l_Lean_Lsp_instToJsonRpcConnectParams___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcConnected_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcConnected_fromJson_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "sessionId"};
static const lean_object* l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__0_value;
static const lean_string_object l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "RpcConnected"};
static const lean_object* l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__1_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__2_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__2_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__2_value_aux_1),((lean_object*)&l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(180, 241, 46, 33, 123, 225, 103, 159)}};
static const lean_object* l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__2 = (const lean_object*)&l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__2_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__3;
static lean_once_cell_t l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__4;
static const lean_ctor_object l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(133, 212, 152, 2, 20, 200, 182, 114)}};
static const lean_object* l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__5 = (const lean_object*)&l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__5_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__6;
static lean_once_cell_t l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__7;
static lean_once_cell_t l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__8;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonRpcConnected_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonRpcConnected___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonRpcConnected_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonRpcConnected___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonRpcConnected___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonRpcConnected = (const lean_object*)&l_Lean_Lsp_instFromJsonRpcConnected___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRpcConnected_toJson(uint64_t);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRpcConnected_toJson___boxed(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonRpcConnected___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonRpcConnected_toJson___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonRpcConnected___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonRpcConnected___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonRpcConnected = (const lean_object*)&l_Lean_Lsp_instToJsonRpcConnected___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcCallParams_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcCallParams_fromJson_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcCallParams_fromJson_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcCallParams_fromJson_spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "RpcCallParams"};
static const lean_object* l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__1_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__2_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__1_value_aux_1),((lean_object*)&l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 99, 31, 63, 42, 102, 147, 83)}};
static const lean_object* l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__1_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__2;
static lean_once_cell_t l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__3;
static lean_once_cell_t l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__4;
static lean_once_cell_t l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__5;
static lean_once_cell_t l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__6;
static lean_once_cell_t l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__7;
static lean_once_cell_t l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__8;
static lean_once_cell_t l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__9;
static const lean_string_object l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "method"};
static const lean_object* l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__10 = (const lean_object*)&l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__10_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__10_value),LEAN_SCALAR_PTR_LITERAL(50, 27, 204, 235, 104, 139, 101, 144)}};
static const lean_object* l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__11 = (const lean_object*)&l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__11_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__12;
static lean_once_cell_t l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__13;
static lean_once_cell_t l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__14;
static const lean_string_object l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "params"};
static const lean_object* l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__15 = (const lean_object*)&l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__15_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonRpcCallParams_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonRpcCallParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonRpcCallParams_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonRpcCallParams___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonRpcCallParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonRpcCallParams = (const lean_object*)&l_Lean_Lsp_instFromJsonRpcCallParams___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRpcCallParams_toJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonRpcCallParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonRpcCallParams_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonRpcCallParams___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonRpcCallParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonRpcCallParams = (const lean_object*)&l_Lean_Lsp_instToJsonRpcCallParams___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcReleaseParams_fromJson_spec__0_spec__0_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcReleaseParams_fromJson_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcReleaseParams_fromJson_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcReleaseParams_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcReleaseParams_fromJson_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "RpcReleaseParams"};
static const lean_object* l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__1_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__2_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__1_value_aux_1),((lean_object*)&l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(27, 131, 255, 41, 107, 226, 183, 241)}};
static const lean_object* l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__1_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__2;
static lean_once_cell_t l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__3;
static lean_once_cell_t l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__4;
static lean_once_cell_t l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__5;
static lean_once_cell_t l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__6;
static lean_once_cell_t l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__7;
static const lean_string_object l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "refs"};
static const lean_object* l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__8 = (const lean_object*)&l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__8_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__8_value),LEAN_SCALAR_PTR_LITERAL(173, 130, 53, 180, 102, 237, 222, 187)}};
static const lean_object* l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__9 = (const lean_object*)&l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__9_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__10;
static lean_once_cell_t l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__11;
static lean_once_cell_t l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__12;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonRpcReleaseParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonRpcReleaseParams___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonRpcReleaseParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonRpcReleaseParams = (const lean_object*)&l_Lean_Lsp_instFromJsonRpcReleaseParams___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonRpcReleaseParams_toJson_spec__0_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonRpcReleaseParams_toJson_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonRpcReleaseParams_toJson_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRpcReleaseParams_toJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonRpcReleaseParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonRpcReleaseParams_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonRpcReleaseParams___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonRpcReleaseParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonRpcReleaseParams = (const lean_object*)&l_Lean_Lsp_instToJsonRpcReleaseParams___closed__0_value;
static const lean_string_object l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "RpcKeepAliveParams"};
static const lean_object* l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__1_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__2_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__1_value_aux_1),((lean_object*)&l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(62, 100, 125, 228, 178, 55, 134, 224)}};
static const lean_object* l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__1_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__2;
static lean_once_cell_t l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__3;
static lean_once_cell_t l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__4;
static lean_once_cell_t l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__5;
static lean_once_cell_t l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__6;
static lean_once_cell_t l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__7;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonRpcKeepAliveParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonRpcKeepAliveParams___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonRpcKeepAliveParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonRpcKeepAliveParams = (const lean_object*)&l_Lean_Lsp_instFromJsonRpcKeepAliveParams___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRpcKeepAliveParams_toJson(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRpcKeepAliveParams_toJson___boxed(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonRpcKeepAliveParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonRpcKeepAliveParams_toJson___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonRpcKeepAliveParams___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonRpcKeepAliveParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonRpcKeepAliveParams = (const lean_object*)&l_Lean_Lsp_instToJsonRpcKeepAliveParams___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_instInhabitedLineRange_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Lsp_instInhabitedLineRange_default___closed__0 = (const lean_object*)&l_Lean_Lsp_instInhabitedLineRange_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instInhabitedLineRange_default = (const lean_object*)&l_Lean_Lsp_instInhabitedLineRange_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instInhabitedLineRange = (const lean_object*)&l_Lean_Lsp_instInhabitedLineRange_default___closed__0_value;
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Lsp_instReprLineRange_repr_spec__0(lean_object*);
static const lean_string_object l_Lean_Lsp_instReprLineRange_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Lean_Lsp_instReprLineRange_repr___redArg___closed__0 = (const lean_object*)&l_Lean_Lsp_instReprLineRange_repr___redArg___closed__0_value;
static const lean_string_object l_Lean_Lsp_instReprLineRange_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "start"};
static const lean_object* l_Lean_Lsp_instReprLineRange_repr___redArg___closed__1 = (const lean_object*)&l_Lean_Lsp_instReprLineRange_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Lsp_instReprLineRange_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Lsp_instReprLineRange_repr___redArg___closed__1_value)}};
static const lean_object* l_Lean_Lsp_instReprLineRange_repr___redArg___closed__2 = (const lean_object*)&l_Lean_Lsp_instReprLineRange_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Lsp_instReprLineRange_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instReprLineRange_repr___redArg___closed__2_value)}};
static const lean_object* l_Lean_Lsp_instReprLineRange_repr___redArg___closed__3 = (const lean_object*)&l_Lean_Lsp_instReprLineRange_repr___redArg___closed__3_value;
static const lean_string_object l_Lean_Lsp_instReprLineRange_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lean_Lsp_instReprLineRange_repr___redArg___closed__4 = (const lean_object*)&l_Lean_Lsp_instReprLineRange_repr___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Lsp_instReprLineRange_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Lsp_instReprLineRange_repr___redArg___closed__4_value)}};
static const lean_object* l_Lean_Lsp_instReprLineRange_repr___redArg___closed__5 = (const lean_object*)&l_Lean_Lsp_instReprLineRange_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lean_Lsp_instReprLineRange_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Lsp_instReprLineRange_repr___redArg___closed__3_value),((lean_object*)&l_Lean_Lsp_instReprLineRange_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_Lsp_instReprLineRange_repr___redArg___closed__6 = (const lean_object*)&l_Lean_Lsp_instReprLineRange_repr___redArg___closed__6_value;
static lean_once_cell_t l_Lean_Lsp_instReprLineRange_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instReprLineRange_repr___redArg___closed__7;
static const lean_string_object l_Lean_Lsp_instReprLineRange_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lean_Lsp_instReprLineRange_repr___redArg___closed__8 = (const lean_object*)&l_Lean_Lsp_instReprLineRange_repr___redArg___closed__8_value;
static const lean_ctor_object l_Lean_Lsp_instReprLineRange_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Lsp_instReprLineRange_repr___redArg___closed__8_value)}};
static const lean_object* l_Lean_Lsp_instReprLineRange_repr___redArg___closed__9 = (const lean_object*)&l_Lean_Lsp_instReprLineRange_repr___redArg___closed__9_value;
static const lean_string_object l_Lean_Lsp_instReprLineRange_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "end"};
static const lean_object* l_Lean_Lsp_instReprLineRange_repr___redArg___closed__10 = (const lean_object*)&l_Lean_Lsp_instReprLineRange_repr___redArg___closed__10_value;
static const lean_ctor_object l_Lean_Lsp_instReprLineRange_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Lsp_instReprLineRange_repr___redArg___closed__10_value)}};
static const lean_object* l_Lean_Lsp_instReprLineRange_repr___redArg___closed__11 = (const lean_object*)&l_Lean_Lsp_instReprLineRange_repr___redArg___closed__11_value;
static lean_once_cell_t l_Lean_Lsp_instReprLineRange_repr___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instReprLineRange_repr___redArg___closed__12;
static const lean_string_object l_Lean_Lsp_instReprLineRange_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Lean_Lsp_instReprLineRange_repr___redArg___closed__13 = (const lean_object*)&l_Lean_Lsp_instReprLineRange_repr___redArg___closed__13_value;
static lean_once_cell_t l_Lean_Lsp_instReprLineRange_repr___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instReprLineRange_repr___redArg___closed__14;
static lean_once_cell_t l_Lean_Lsp_instReprLineRange_repr___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instReprLineRange_repr___redArg___closed__15;
static const lean_ctor_object l_Lean_Lsp_instReprLineRange_repr___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Lsp_instReprLineRange_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_Lsp_instReprLineRange_repr___redArg___closed__16 = (const lean_object*)&l_Lean_Lsp_instReprLineRange_repr___redArg___closed__16_value;
static const lean_ctor_object l_Lean_Lsp_instReprLineRange_repr___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Lsp_instReprLineRange_repr___redArg___closed__13_value)}};
static const lean_object* l_Lean_Lsp_instReprLineRange_repr___redArg___closed__17 = (const lean_object*)&l_Lean_Lsp_instReprLineRange_repr___redArg___closed__17_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instReprLineRange_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instReprLineRange_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instReprLineRange_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_instReprLineRange___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instReprLineRange_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instReprLineRange___closed__0 = (const lean_object*)&l_Lean_Lsp_instReprLineRange___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instReprLineRange = (const lean_object*)&l_Lean_Lsp_instReprLineRange___closed__0_value;
static const lean_string_object l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "LineRange"};
static const lean_object* l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__1_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__2_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__1_value_aux_1),((lean_object*)&l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(87, 45, 132, 66, 204, 0, 225, 225)}};
static const lean_object* l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__1_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__2;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__3;
static const lean_ctor_object l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instReprLineRange_repr___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(169, 129, 58, 248, 205, 160, 234, 176)}};
static const lean_object* l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__4 = (const lean_object*)&l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__4_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__5;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__6;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__7;
static const lean_ctor_object l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instReprLineRange_repr___redArg___closed__10_value),LEAN_SCALAR_PTR_LITERAL(199, 114, 144, 235, 25, 156, 115, 98)}};
static const lean_object* l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__8 = (const lean_object*)&l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__8_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__9;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__10;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__11;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLineRange_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonLineRange___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonLineRange_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonLineRange___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonLineRange___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonLineRange = (const lean_object*)&l_Lean_Lsp_instFromJsonLineRange___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLineRange_toJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonLineRange___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonLineRange_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonLineRange___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonLineRange___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonLineRange = (const lean_object*)&l_Lean_Lsp_instToJsonLineRange___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_DependencyBuildMode_ctorIdx(uint8_t v_x_1_){
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
LEAN_EXPORT lean_object* l_Lean_Lsp_DependencyBuildMode_ctorIdx___boxed(lean_object* v_x_5_){
_start:
{
uint8_t v_x_boxed_6_; lean_object* v_res_7_; 
v_x_boxed_6_ = lean_unbox(v_x_5_);
v_res_7_ = l_Lean_Lsp_DependencyBuildMode_ctorIdx(v_x_boxed_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DependencyBuildMode_ctorElim___redArg(lean_object* v_k_8_){
_start:
{
lean_inc(v_k_8_);
return v_k_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DependencyBuildMode_ctorElim___redArg___boxed(lean_object* v_k_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Lean_Lsp_DependencyBuildMode_ctorElim___redArg(v_k_9_);
lean_dec(v_k_9_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DependencyBuildMode_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, uint8_t v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_inc(v_k_15_);
return v_k_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DependencyBuildMode_ctorElim___boxed(lean_object* v_motive_16_, lean_object* v_ctorIdx_17_, lean_object* v_t_18_, lean_object* v_h_19_, lean_object* v_k_20_){
_start:
{
uint8_t v_t_boxed_21_; lean_object* v_res_22_; 
v_t_boxed_21_ = lean_unbox(v_t_18_);
v_res_22_ = l_Lean_Lsp_DependencyBuildMode_ctorElim(v_motive_16_, v_ctorIdx_17_, v_t_boxed_21_, v_h_19_, v_k_20_);
lean_dec(v_k_20_);
lean_dec(v_ctorIdx_17_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DependencyBuildMode_always_elim___redArg(lean_object* v_always_23_){
_start:
{
lean_inc(v_always_23_);
return v_always_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DependencyBuildMode_always_elim___redArg___boxed(lean_object* v_always_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_Lean_Lsp_DependencyBuildMode_always_elim___redArg(v_always_24_);
lean_dec(v_always_24_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DependencyBuildMode_always_elim(lean_object* v_motive_26_, uint8_t v_t_27_, lean_object* v_h_28_, lean_object* v_always_29_){
_start:
{
lean_inc(v_always_29_);
return v_always_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DependencyBuildMode_always_elim___boxed(lean_object* v_motive_30_, lean_object* v_t_31_, lean_object* v_h_32_, lean_object* v_always_33_){
_start:
{
uint8_t v_t_boxed_34_; lean_object* v_res_35_; 
v_t_boxed_34_ = lean_unbox(v_t_31_);
v_res_35_ = l_Lean_Lsp_DependencyBuildMode_always_elim(v_motive_30_, v_t_boxed_34_, v_h_32_, v_always_33_);
lean_dec(v_always_33_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DependencyBuildMode_once_elim___redArg(lean_object* v_once_36_){
_start:
{
lean_inc(v_once_36_);
return v_once_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DependencyBuildMode_once_elim___redArg___boxed(lean_object* v_once_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Lean_Lsp_DependencyBuildMode_once_elim___redArg(v_once_37_);
lean_dec(v_once_37_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DependencyBuildMode_once_elim(lean_object* v_motive_39_, uint8_t v_t_40_, lean_object* v_h_41_, lean_object* v_once_42_){
_start:
{
lean_inc(v_once_42_);
return v_once_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DependencyBuildMode_once_elim___boxed(lean_object* v_motive_43_, lean_object* v_t_44_, lean_object* v_h_45_, lean_object* v_once_46_){
_start:
{
uint8_t v_t_boxed_47_; lean_object* v_res_48_; 
v_t_boxed_47_ = lean_unbox(v_t_44_);
v_res_48_ = l_Lean_Lsp_DependencyBuildMode_once_elim(v_motive_43_, v_t_boxed_47_, v_h_45_, v_once_46_);
lean_dec(v_once_46_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DependencyBuildMode_never_elim___redArg(lean_object* v_never_49_){
_start:
{
lean_inc(v_never_49_);
return v_never_49_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DependencyBuildMode_never_elim___redArg___boxed(lean_object* v_never_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l_Lean_Lsp_DependencyBuildMode_never_elim___redArg(v_never_50_);
lean_dec(v_never_50_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DependencyBuildMode_never_elim(lean_object* v_motive_52_, uint8_t v_t_53_, lean_object* v_h_54_, lean_object* v_never_55_){
_start:
{
lean_inc(v_never_55_);
return v_never_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DependencyBuildMode_never_elim___boxed(lean_object* v_motive_56_, lean_object* v_t_57_, lean_object* v_h_58_, lean_object* v_never_59_){
_start:
{
uint8_t v_t_boxed_60_; lean_object* v_res_61_; 
v_t_boxed_60_ = lean_unbox(v_t_57_);
v_res_61_ = l_Lean_Lsp_DependencyBuildMode_never_elim(v_motive_56_, v_t_boxed_60_, v_h_58_, v_never_59_);
lean_dec(v_never_59_);
return v_res_61_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson(lean_object* v_json_80_){
_start:
{
lean_object* v___x_81_; 
v___x_81_ = l_Lean_Json_getTag_x3f(v_json_80_);
if (lean_obj_tag(v___x_81_) == 0)
{
lean_object* v___x_82_; 
v___x_82_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__1));
return v___x_82_;
}
else
{
lean_object* v_val_83_; lean_object* v___x_84_; uint8_t v___x_85_; 
v_val_83_ = lean_ctor_get(v___x_81_, 0);
lean_inc(v_val_83_);
lean_dec_ref_known(v___x_81_, 1);
v___x_84_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__2));
v___x_85_ = lean_string_dec_eq(v_val_83_, v___x_84_);
if (v___x_85_ == 0)
{
lean_object* v___x_86_; uint8_t v___x_87_; 
v___x_86_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__3));
v___x_87_ = lean_string_dec_eq(v_val_83_, v___x_86_);
if (v___x_87_ == 0)
{
lean_object* v___x_88_; uint8_t v___x_89_; 
v___x_88_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__4));
v___x_89_ = lean_string_dec_eq(v_val_83_, v___x_88_);
lean_dec(v_val_83_);
if (v___x_89_ == 0)
{
lean_object* v___x_90_; 
v___x_90_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__6));
return v___x_90_;
}
else
{
lean_object* v___x_91_; 
v___x_91_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__7));
return v___x_91_;
}
}
else
{
lean_object* v___x_92_; 
lean_dec(v_val_83_);
v___x_92_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__8));
return v___x_92_;
}
}
else
{
lean_object* v___x_93_; 
lean_dec(v_val_83_);
v___x_93_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__9));
return v___x_93_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDependencyBuildMode_toJson(uint8_t v_x_102_){
_start:
{
switch(v_x_102_)
{
case 0:
{
lean_object* v___x_103_; 
v___x_103_ = ((lean_object*)(l_Lean_Lsp_instToJsonDependencyBuildMode_toJson___closed__0));
return v___x_103_;
}
case 1:
{
lean_object* v___x_104_; 
v___x_104_ = ((lean_object*)(l_Lean_Lsp_instToJsonDependencyBuildMode_toJson___closed__1));
return v___x_104_;
}
default: 
{
lean_object* v___x_105_; 
v___x_105_ = ((lean_object*)(l_Lean_Lsp_instToJsonDependencyBuildMode_toJson___closed__2));
return v___x_105_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDependencyBuildMode_toJson___boxed(lean_object* v_x_106_){
_start:
{
uint8_t v_x_64__boxed_107_; lean_object* v_res_108_; 
v_x_64__boxed_107_ = lean_unbox(v_x_106_);
v_res_108_ = l_Lean_Lsp_instToJsonDependencyBuildMode_toJson(v_x_64__boxed_107_);
return v_res_108_;
}
}
static uint8_t _init_l_Lean_Lsp_instInhabitedDependencyBuildMode_default(void){
_start:
{
uint8_t v___x_111_; 
v___x_111_ = 0;
return v___x_111_;
}
}
static uint8_t _init_l_Lean_Lsp_instInhabitedDependencyBuildMode(void){
_start:
{
uint8_t v___x_112_; 
v___x_112_ = 0;
return v___x_112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson_spec__0(lean_object* v_j_113_, lean_object* v_k_114_){
_start:
{
lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_115_ = l_Lean_Json_getObjValD(v_j_113_, v_k_114_);
v___x_116_ = l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson(v___x_115_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson_spec__0___boxed(lean_object* v_j_117_, lean_object* v_k_118_){
_start:
{
lean_object* v_res_119_; 
v_res_119_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson_spec__0(v_j_117_, v_k_118_);
lean_dec_ref(v_k_118_);
return v_res_119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson_spec__1_spec__1(lean_object* v_x_122_){
_start:
{
if (lean_obj_tag(v_x_122_) == 0)
{
lean_object* v___x_123_; 
v___x_123_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson_spec__1_spec__1___closed__0));
return v___x_123_;
}
else
{
lean_object* v___x_124_; 
v___x_124_ = l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson(v_x_122_);
if (lean_obj_tag(v___x_124_) == 0)
{
lean_object* v_a_125_; lean_object* v___x_127_; uint8_t v_isShared_128_; uint8_t v_isSharedCheck_132_; 
v_a_125_ = lean_ctor_get(v___x_124_, 0);
v_isSharedCheck_132_ = !lean_is_exclusive(v___x_124_);
if (v_isSharedCheck_132_ == 0)
{
v___x_127_ = v___x_124_;
v_isShared_128_ = v_isSharedCheck_132_;
goto v_resetjp_126_;
}
else
{
lean_inc(v_a_125_);
lean_dec(v___x_124_);
v___x_127_ = lean_box(0);
v_isShared_128_ = v_isSharedCheck_132_;
goto v_resetjp_126_;
}
v_resetjp_126_:
{
lean_object* v___x_130_; 
if (v_isShared_128_ == 0)
{
v___x_130_ = v___x_127_;
goto v_reusejp_129_;
}
else
{
lean_object* v_reuseFailAlloc_131_; 
v_reuseFailAlloc_131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_131_, 0, v_a_125_);
v___x_130_ = v_reuseFailAlloc_131_;
goto v_reusejp_129_;
}
v_reusejp_129_:
{
return v___x_130_;
}
}
}
else
{
lean_object* v_a_133_; lean_object* v___x_135_; uint8_t v_isShared_136_; uint8_t v_isSharedCheck_141_; 
v_a_133_ = lean_ctor_get(v___x_124_, 0);
v_isSharedCheck_141_ = !lean_is_exclusive(v___x_124_);
if (v_isSharedCheck_141_ == 0)
{
v___x_135_ = v___x_124_;
v_isShared_136_ = v_isSharedCheck_141_;
goto v_resetjp_134_;
}
else
{
lean_inc(v_a_133_);
lean_dec(v___x_124_);
v___x_135_ = lean_box(0);
v_isShared_136_ = v_isSharedCheck_141_;
goto v_resetjp_134_;
}
v_resetjp_134_:
{
lean_object* v___x_137_; lean_object* v___x_139_; 
v___x_137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_137_, 0, v_a_133_);
if (v_isShared_136_ == 0)
{
lean_ctor_set(v___x_135_, 0, v___x_137_);
v___x_139_ = v___x_135_;
goto v_reusejp_138_;
}
else
{
lean_object* v_reuseFailAlloc_140_; 
v_reuseFailAlloc_140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_140_, 0, v___x_137_);
v___x_139_ = v_reuseFailAlloc_140_;
goto v_reusejp_138_;
}
v_reusejp_138_:
{
return v___x_139_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson_spec__1(lean_object* v_j_142_, lean_object* v_k_143_){
_start:
{
lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_144_ = l_Lean_Json_getObjValD(v_j_142_, v_k_143_);
v___x_145_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson_spec__1_spec__1(v___x_144_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson_spec__1___boxed(lean_object* v_j_146_, lean_object* v_k_147_){
_start:
{
lean_object* v_res_148_; 
v_res_148_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson_spec__1(v_j_146_, v_k_147_);
lean_dec_ref(v_k_147_);
return v_res_148_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__5(void){
_start:
{
uint8_t v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_157_ = 1;
v___x_158_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__4));
v___x_159_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_158_, v___x_157_);
return v___x_159_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__7(void){
_start:
{
lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_161_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6));
v___x_162_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__5, &l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__5);
v___x_163_ = lean_string_append(v___x_162_, v___x_161_);
return v___x_163_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9(void){
_start:
{
uint8_t v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_166_ = 1;
v___x_167_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__8));
v___x_168_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_167_, v___x_166_);
return v___x_168_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__10(void){
_start:
{
lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_169_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9, &l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9);
v___x_170_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__7);
v___x_171_ = lean_string_append(v___x_170_, v___x_169_);
return v___x_171_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__12(void){
_start:
{
lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_173_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_174_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__10, &l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__10);
v___x_175_ = lean_string_append(v___x_174_, v___x_173_);
return v___x_175_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__16(void){
_start:
{
uint8_t v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_180_ = 1;
v___x_181_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__15));
v___x_182_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_181_, v___x_180_);
return v___x_182_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__17(void){
_start:
{
lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_183_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__16, &l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__16_once, _init_l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__16);
v___x_184_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__7);
v___x_185_ = lean_string_append(v___x_184_, v___x_183_);
return v___x_185_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__18(void){
_start:
{
lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_186_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_187_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__17, &l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__17_once, _init_l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__17);
v___x_188_ = lean_string_append(v___x_187_, v___x_186_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson(lean_object* v_json_189_){
_start:
{
lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_190_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__0));
lean_inc(v_json_189_);
v___x_191_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson_spec__0(v_json_189_, v___x_190_);
if (lean_obj_tag(v___x_191_) == 0)
{
lean_object* v_a_192_; lean_object* v___x_194_; uint8_t v_isShared_195_; uint8_t v_isSharedCheck_201_; 
lean_dec(v_json_189_);
v_a_192_ = lean_ctor_get(v___x_191_, 0);
v_isSharedCheck_201_ = !lean_is_exclusive(v___x_191_);
if (v_isSharedCheck_201_ == 0)
{
v___x_194_ = v___x_191_;
v_isShared_195_ = v_isSharedCheck_201_;
goto v_resetjp_193_;
}
else
{
lean_inc(v_a_192_);
lean_dec(v___x_191_);
v___x_194_ = lean_box(0);
v_isShared_195_ = v_isSharedCheck_201_;
goto v_resetjp_193_;
}
v_resetjp_193_:
{
lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_199_; 
v___x_196_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__12, &l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__12);
v___x_197_ = lean_string_append(v___x_196_, v_a_192_);
lean_dec(v_a_192_);
if (v_isShared_195_ == 0)
{
lean_ctor_set(v___x_194_, 0, v___x_197_);
v___x_199_ = v___x_194_;
goto v_reusejp_198_;
}
else
{
lean_object* v_reuseFailAlloc_200_; 
v_reuseFailAlloc_200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_200_, 0, v___x_197_);
v___x_199_ = v_reuseFailAlloc_200_;
goto v_reusejp_198_;
}
v_reusejp_198_:
{
return v___x_199_;
}
}
}
else
{
if (lean_obj_tag(v___x_191_) == 0)
{
lean_object* v_a_202_; lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_209_; 
lean_dec(v_json_189_);
v_a_202_ = lean_ctor_get(v___x_191_, 0);
v_isSharedCheck_209_ = !lean_is_exclusive(v___x_191_);
if (v_isSharedCheck_209_ == 0)
{
v___x_204_ = v___x_191_;
v_isShared_205_ = v_isSharedCheck_209_;
goto v_resetjp_203_;
}
else
{
lean_inc(v_a_202_);
lean_dec(v___x_191_);
v___x_204_ = lean_box(0);
v_isShared_205_ = v_isSharedCheck_209_;
goto v_resetjp_203_;
}
v_resetjp_203_:
{
lean_object* v___x_207_; 
if (v_isShared_205_ == 0)
{
lean_ctor_set_tag(v___x_204_, 0);
v___x_207_ = v___x_204_;
goto v_reusejp_206_;
}
else
{
lean_object* v_reuseFailAlloc_208_; 
v_reuseFailAlloc_208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_208_, 0, v_a_202_);
v___x_207_ = v_reuseFailAlloc_208_;
goto v_reusejp_206_;
}
v_reusejp_206_:
{
return v___x_207_;
}
}
}
else
{
lean_object* v_a_210_; lean_object* v___x_211_; lean_object* v___x_212_; 
v_a_210_ = lean_ctor_get(v___x_191_, 0);
lean_inc(v_a_210_);
lean_dec_ref_known(v___x_191_, 1);
v___x_211_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__13));
v___x_212_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson_spec__1(v_json_189_, v___x_211_);
if (lean_obj_tag(v___x_212_) == 0)
{
lean_object* v_a_213_; lean_object* v___x_215_; uint8_t v_isShared_216_; uint8_t v_isSharedCheck_222_; 
lean_dec(v_a_210_);
v_a_213_ = lean_ctor_get(v___x_212_, 0);
v_isSharedCheck_222_ = !lean_is_exclusive(v___x_212_);
if (v_isSharedCheck_222_ == 0)
{
v___x_215_ = v___x_212_;
v_isShared_216_ = v_isSharedCheck_222_;
goto v_resetjp_214_;
}
else
{
lean_inc(v_a_213_);
lean_dec(v___x_212_);
v___x_215_ = lean_box(0);
v_isShared_216_ = v_isSharedCheck_222_;
goto v_resetjp_214_;
}
v_resetjp_214_:
{
lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_220_; 
v___x_217_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__18, &l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__18_once, _init_l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__18);
v___x_218_ = lean_string_append(v___x_217_, v_a_213_);
lean_dec(v_a_213_);
if (v_isShared_216_ == 0)
{
lean_ctor_set(v___x_215_, 0, v___x_218_);
v___x_220_ = v___x_215_;
goto v_reusejp_219_;
}
else
{
lean_object* v_reuseFailAlloc_221_; 
v_reuseFailAlloc_221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_221_, 0, v___x_218_);
v___x_220_ = v_reuseFailAlloc_221_;
goto v_reusejp_219_;
}
v_reusejp_219_:
{
return v___x_220_;
}
}
}
else
{
if (lean_obj_tag(v___x_212_) == 0)
{
lean_object* v_a_223_; lean_object* v___x_225_; uint8_t v_isShared_226_; uint8_t v_isSharedCheck_230_; 
lean_dec(v_a_210_);
v_a_223_ = lean_ctor_get(v___x_212_, 0);
v_isSharedCheck_230_ = !lean_is_exclusive(v___x_212_);
if (v_isSharedCheck_230_ == 0)
{
v___x_225_ = v___x_212_;
v_isShared_226_ = v_isSharedCheck_230_;
goto v_resetjp_224_;
}
else
{
lean_inc(v_a_223_);
lean_dec(v___x_212_);
v___x_225_ = lean_box(0);
v_isShared_226_ = v_isSharedCheck_230_;
goto v_resetjp_224_;
}
v_resetjp_224_:
{
lean_object* v___x_228_; 
if (v_isShared_226_ == 0)
{
lean_ctor_set_tag(v___x_225_, 0);
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
lean_object* v_a_231_; lean_object* v___x_233_; uint8_t v_isShared_234_; uint8_t v_isSharedCheck_239_; 
v_a_231_ = lean_ctor_get(v___x_212_, 0);
v_isSharedCheck_239_ = !lean_is_exclusive(v___x_212_);
if (v_isSharedCheck_239_ == 0)
{
v___x_233_ = v___x_212_;
v_isShared_234_ = v_isSharedCheck_239_;
goto v_resetjp_232_;
}
else
{
lean_inc(v_a_231_);
lean_dec(v___x_212_);
v___x_233_ = lean_box(0);
v_isShared_234_ = v_isSharedCheck_239_;
goto v_resetjp_232_;
}
v_resetjp_232_:
{
lean_object* v___x_235_; lean_object* v___x_237_; 
v___x_235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_235_, 0, v_a_210_);
lean_ctor_set(v___x_235_, 1, v_a_231_);
if (v_isShared_234_ == 0)
{
lean_ctor_set(v___x_233_, 0, v___x_235_);
v___x_237_ = v___x_233_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v___x_235_);
v___x_237_ = v_reuseFailAlloc_238_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
return v___x_237_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__0(lean_object* v_k_242_, lean_object* v_x_243_){
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
lean_object* v_val_245_; uint8_t v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; 
v_val_245_ = lean_ctor_get(v_x_243_, 0);
v___x_246_ = lean_unbox(v_val_245_);
v___x_247_ = l_Lean_Lsp_instToJsonDependencyBuildMode_toJson(v___x_246_);
v___x_248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_248_, 0, v_k_242_);
lean_ctor_set(v___x_248_, 1, v___x_247_);
v___x_249_ = lean_box(0);
v___x_250_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_250_, 0, v___x_248_);
lean_ctor_set(v___x_250_, 1, v___x_249_);
return v___x_250_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__0___boxed(lean_object* v_k_251_, lean_object* v_x_252_){
_start:
{
lean_object* v_res_253_; 
v_res_253_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__0(v_k_251_, v_x_252_);
lean_dec(v_x_252_);
return v_res_253_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(lean_object* v_a_254_, lean_object* v_a_255_){
_start:
{
if (lean_obj_tag(v_a_254_) == 0)
{
lean_object* v___x_256_; 
v___x_256_ = lean_array_to_list(v_a_255_);
return v___x_256_;
}
else
{
lean_object* v_head_257_; lean_object* v_tail_258_; lean_object* v___x_259_; 
v_head_257_ = lean_ctor_get(v_a_254_, 0);
lean_inc(v_head_257_);
v_tail_258_ = lean_ctor_get(v_a_254_, 1);
lean_inc(v_tail_258_);
lean_dec_ref_known(v_a_254_, 2);
v___x_259_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_255_, v_head_257_);
v_a_254_ = v_tail_258_;
v_a_255_ = v___x_259_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson(lean_object* v_x_263_){
_start:
{
lean_object* v_toDidOpenTextDocumentParams_264_; lean_object* v_dependencyBuildMode_x3f_265_; lean_object* v___x_267_; uint8_t v_isShared_268_; uint8_t v_isSharedCheck_283_; 
v_toDidOpenTextDocumentParams_264_ = lean_ctor_get(v_x_263_, 0);
v_dependencyBuildMode_x3f_265_ = lean_ctor_get(v_x_263_, 1);
v_isSharedCheck_283_ = !lean_is_exclusive(v_x_263_);
if (v_isSharedCheck_283_ == 0)
{
v___x_267_ = v_x_263_;
v_isShared_268_ = v_isSharedCheck_283_;
goto v_resetjp_266_;
}
else
{
lean_inc(v_dependencyBuildMode_x3f_265_);
lean_inc(v_toDidOpenTextDocumentParams_264_);
lean_dec(v_x_263_);
v___x_267_ = lean_box(0);
v_isShared_268_ = v_isSharedCheck_283_;
goto v_resetjp_266_;
}
v_resetjp_266_:
{
lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_272_; 
v___x_269_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__0));
v___x_270_ = l_Lean_Lsp_instToJsonTextDocumentItem_toJson(v_toDidOpenTextDocumentParams_264_);
if (v_isShared_268_ == 0)
{
lean_ctor_set(v___x_267_, 1, v___x_270_);
lean_ctor_set(v___x_267_, 0, v___x_269_);
v___x_272_ = v___x_267_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v___x_269_);
lean_ctor_set(v_reuseFailAlloc_282_, 1, v___x_270_);
v___x_272_ = v_reuseFailAlloc_282_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_273_ = lean_box(0);
v___x_274_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_274_, 0, v___x_272_);
lean_ctor_set(v___x_274_, 1, v___x_273_);
v___x_275_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__13));
v___x_276_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__0(v___x_275_, v_dependencyBuildMode_x3f_265_);
lean_dec(v_dependencyBuildMode_x3f_265_);
v___x_277_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_277_, 0, v___x_276_);
lean_ctor_set(v___x_277_, 1, v___x_273_);
v___x_278_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_278_, 0, v___x_274_);
lean_ctor_set(v___x_278_, 1, v___x_277_);
v___x_279_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0));
v___x_280_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_278_, v___x_279_);
v___x_281_ = l_Lean_Json_mkObj(v___x_280_);
lean_dec(v___x_280_);
return v___x_281_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson_spec__0(lean_object* v_j_286_, lean_object* v_k_287_){
_start:
{
lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_288_ = l_Lean_Json_getObjValD(v_j_286_, v_k_287_);
v___x_289_ = l_Lean_Json_getStr_x3f(v___x_288_);
return v___x_289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson_spec__0___boxed(lean_object* v_j_290_, lean_object* v_k_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson_spec__0(v_j_290_, v_k_291_);
lean_dec_ref(v_k_291_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson_spec__1(lean_object* v_j_293_, lean_object* v_k_294_){
_start:
{
lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_295_ = l_Lean_Json_getObjValD(v_j_293_, v_k_294_);
v___x_296_ = l_Lean_Json_getNat_x3f(v___x_295_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson_spec__1___boxed(lean_object* v_j_297_, lean_object* v_k_298_){
_start:
{
lean_object* v_res_299_; 
v_res_299_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson_spec__1(v_j_297_, v_k_298_);
lean_dec_ref(v_k_298_);
return v_res_299_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__3(void){
_start:
{
uint8_t v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_306_ = 1;
v___x_307_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__2));
v___x_308_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_307_, v___x_306_);
return v___x_308_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_309_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6));
v___x_310_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__3);
v___x_311_ = lean_string_append(v___x_310_, v___x_309_);
return v___x_311_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__6(void){
_start:
{
uint8_t v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_314_ = 1;
v___x_315_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__5));
v___x_316_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_315_, v___x_314_);
return v___x_316_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__7(void){
_start:
{
lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_317_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__6, &l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__6);
v___x_318_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__4);
v___x_319_ = lean_string_append(v___x_318_, v___x_317_);
return v___x_319_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__8(void){
_start:
{
lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_320_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_321_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__7);
v___x_322_ = lean_string_append(v___x_321_, v___x_320_);
return v___x_322_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__11(void){
_start:
{
uint8_t v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_326_ = 1;
v___x_327_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__10));
v___x_328_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_327_, v___x_326_);
return v___x_328_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__12(void){
_start:
{
lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_329_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__11, &l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__11);
v___x_330_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__4);
v___x_331_ = lean_string_append(v___x_330_, v___x_329_);
return v___x_331_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__13(void){
_start:
{
lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_332_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_333_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__12, &l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__12);
v___x_334_ = lean_string_append(v___x_333_, v___x_332_);
return v___x_334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson(lean_object* v_json_335_){
_start:
{
lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_336_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__0));
lean_inc(v_json_335_);
v___x_337_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson_spec__0(v_json_335_, v___x_336_);
if (lean_obj_tag(v___x_337_) == 0)
{
lean_object* v_a_338_; lean_object* v___x_340_; uint8_t v_isShared_341_; uint8_t v_isSharedCheck_347_; 
lean_dec(v_json_335_);
v_a_338_ = lean_ctor_get(v___x_337_, 0);
v_isSharedCheck_347_ = !lean_is_exclusive(v___x_337_);
if (v_isSharedCheck_347_ == 0)
{
v___x_340_ = v___x_337_;
v_isShared_341_ = v_isSharedCheck_347_;
goto v_resetjp_339_;
}
else
{
lean_inc(v_a_338_);
lean_dec(v___x_337_);
v___x_340_ = lean_box(0);
v_isShared_341_ = v_isSharedCheck_347_;
goto v_resetjp_339_;
}
v_resetjp_339_:
{
lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_345_; 
v___x_342_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__8);
v___x_343_ = lean_string_append(v___x_342_, v_a_338_);
lean_dec(v_a_338_);
if (v_isShared_341_ == 0)
{
lean_ctor_set(v___x_340_, 0, v___x_343_);
v___x_345_ = v___x_340_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v___x_343_);
v___x_345_ = v_reuseFailAlloc_346_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
return v___x_345_;
}
}
}
else
{
if (lean_obj_tag(v___x_337_) == 0)
{
lean_object* v_a_348_; lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_355_; 
lean_dec(v_json_335_);
v_a_348_ = lean_ctor_get(v___x_337_, 0);
v_isSharedCheck_355_ = !lean_is_exclusive(v___x_337_);
if (v_isSharedCheck_355_ == 0)
{
v___x_350_ = v___x_337_;
v_isShared_351_ = v_isSharedCheck_355_;
goto v_resetjp_349_;
}
else
{
lean_inc(v_a_348_);
lean_dec(v___x_337_);
v___x_350_ = lean_box(0);
v_isShared_351_ = v_isSharedCheck_355_;
goto v_resetjp_349_;
}
v_resetjp_349_:
{
lean_object* v___x_353_; 
if (v_isShared_351_ == 0)
{
lean_ctor_set_tag(v___x_350_, 0);
v___x_353_ = v___x_350_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v_a_348_);
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
lean_object* v_a_356_; lean_object* v___x_357_; lean_object* v___x_358_; 
v_a_356_ = lean_ctor_get(v___x_337_, 0);
lean_inc(v_a_356_);
lean_dec_ref_known(v___x_337_, 1);
v___x_357_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__9));
v___x_358_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson_spec__1(v_json_335_, v___x_357_);
if (lean_obj_tag(v___x_358_) == 0)
{
lean_object* v_a_359_; lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_368_; 
lean_dec(v_a_356_);
v_a_359_ = lean_ctor_get(v___x_358_, 0);
v_isSharedCheck_368_ = !lean_is_exclusive(v___x_358_);
if (v_isSharedCheck_368_ == 0)
{
v___x_361_ = v___x_358_;
v_isShared_362_ = v_isSharedCheck_368_;
goto v_resetjp_360_;
}
else
{
lean_inc(v_a_359_);
lean_dec(v___x_358_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_368_;
goto v_resetjp_360_;
}
v_resetjp_360_:
{
lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_366_; 
v___x_363_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__13, &l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__13);
v___x_364_ = lean_string_append(v___x_363_, v_a_359_);
lean_dec(v_a_359_);
if (v_isShared_362_ == 0)
{
lean_ctor_set(v___x_361_, 0, v___x_364_);
v___x_366_ = v___x_361_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v___x_364_);
v___x_366_ = v_reuseFailAlloc_367_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
return v___x_366_;
}
}
}
else
{
if (lean_obj_tag(v___x_358_) == 0)
{
lean_object* v_a_369_; lean_object* v___x_371_; uint8_t v_isShared_372_; uint8_t v_isSharedCheck_376_; 
lean_dec(v_a_356_);
v_a_369_ = lean_ctor_get(v___x_358_, 0);
v_isSharedCheck_376_ = !lean_is_exclusive(v___x_358_);
if (v_isSharedCheck_376_ == 0)
{
v___x_371_ = v___x_358_;
v_isShared_372_ = v_isSharedCheck_376_;
goto v_resetjp_370_;
}
else
{
lean_inc(v_a_369_);
lean_dec(v___x_358_);
v___x_371_ = lean_box(0);
v_isShared_372_ = v_isSharedCheck_376_;
goto v_resetjp_370_;
}
v_resetjp_370_:
{
lean_object* v___x_374_; 
if (v_isShared_372_ == 0)
{
lean_ctor_set_tag(v___x_371_, 0);
v___x_374_ = v___x_371_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v_a_369_);
v___x_374_ = v_reuseFailAlloc_375_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
return v___x_374_;
}
}
}
else
{
lean_object* v_a_377_; lean_object* v___x_379_; uint8_t v_isShared_380_; uint8_t v_isSharedCheck_385_; 
v_a_377_ = lean_ctor_get(v___x_358_, 0);
v_isSharedCheck_385_ = !lean_is_exclusive(v___x_358_);
if (v_isSharedCheck_385_ == 0)
{
v___x_379_ = v___x_358_;
v_isShared_380_ = v_isSharedCheck_385_;
goto v_resetjp_378_;
}
else
{
lean_inc(v_a_377_);
lean_dec(v___x_358_);
v___x_379_ = lean_box(0);
v_isShared_380_ = v_isSharedCheck_385_;
goto v_resetjp_378_;
}
v_resetjp_378_:
{
lean_object* v___x_381_; lean_object* v___x_383_; 
v___x_381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_381_, 0, v_a_356_);
lean_ctor_set(v___x_381_, 1, v_a_377_);
if (v_isShared_380_ == 0)
{
lean_ctor_set(v___x_379_, 0, v___x_381_);
v___x_383_ = v___x_379_;
goto v_reusejp_382_;
}
else
{
lean_object* v_reuseFailAlloc_384_; 
v_reuseFailAlloc_384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_384_, 0, v___x_381_);
v___x_383_ = v_reuseFailAlloc_384_;
goto v_reusejp_382_;
}
v_reusejp_382_:
{
return v___x_383_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonWaitForDiagnosticsParams_toJson(lean_object* v_x_388_){
_start:
{
lean_object* v_uri_389_; lean_object* v_version_390_; lean_object* v___x_392_; uint8_t v_isShared_393_; uint8_t v_isSharedCheck_411_; 
v_uri_389_ = lean_ctor_get(v_x_388_, 0);
v_version_390_ = lean_ctor_get(v_x_388_, 1);
v_isSharedCheck_411_ = !lean_is_exclusive(v_x_388_);
if (v_isSharedCheck_411_ == 0)
{
v___x_392_ = v_x_388_;
v_isShared_393_ = v_isSharedCheck_411_;
goto v_resetjp_391_;
}
else
{
lean_inc(v_version_390_);
lean_inc(v_uri_389_);
lean_dec(v_x_388_);
v___x_392_ = lean_box(0);
v_isShared_393_ = v_isSharedCheck_411_;
goto v_resetjp_391_;
}
v_resetjp_391_:
{
lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_397_; 
v___x_394_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__0));
v___x_395_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_395_, 0, v_uri_389_);
if (v_isShared_393_ == 0)
{
lean_ctor_set(v___x_392_, 1, v___x_395_);
lean_ctor_set(v___x_392_, 0, v___x_394_);
v___x_397_ = v___x_392_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v___x_394_);
lean_ctor_set(v_reuseFailAlloc_410_, 1, v___x_395_);
v___x_397_ = v_reuseFailAlloc_410_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_398_ = lean_box(0);
v___x_399_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_399_, 0, v___x_397_);
lean_ctor_set(v___x_399_, 1, v___x_398_);
v___x_400_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__9));
v___x_401_ = l_Lean_JsonNumber_fromNat(v_version_390_);
v___x_402_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_402_, 0, v___x_401_);
v___x_403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_403_, 0, v___x_400_);
lean_ctor_set(v___x_403_, 1, v___x_402_);
v___x_404_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_404_, 0, v___x_403_);
lean_ctor_set(v___x_404_, 1, v___x_398_);
v___x_405_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_405_, 0, v___x_404_);
lean_ctor_set(v___x_405_, 1, v___x_398_);
v___x_406_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_406_, 0, v___x_399_);
lean_ctor_set(v___x_406_, 1, v___x_405_);
v___x_407_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0));
v___x_408_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_406_, v___x_407_);
v___x_409_ = l_Lean_Json_mkObj(v___x_408_);
lean_dec(v___x_408_);
return v___x_409_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonWaitForDiagnostics___lam__0(lean_object* v_x_416_){
_start:
{
lean_object* v___x_417_; 
v___x_417_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWaitForDiagnostics___lam__0___closed__0));
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonWaitForDiagnostics___lam__0___boxed(lean_object* v_x_418_){
_start:
{
lean_object* v_res_419_; 
v_res_419_ = l_Lean_Lsp_instFromJsonWaitForDiagnostics___lam__0(v_x_418_);
lean_dec(v_x_418_);
return v_res_419_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonWaitForDiagnostics___lam__0___closed__0(void){
_start:
{
lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_422_ = lean_box(0);
v___x_423_ = l_Lean_Json_mkObj(v___x_422_);
return v___x_423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonWaitForDiagnostics___lam__0(lean_object* v_x_424_){
_start:
{
lean_object* v___x_425_; 
v___x_425_ = lean_obj_once(&l_Lean_Lsp_instToJsonWaitForDiagnostics___lam__0___closed__0, &l_Lean_Lsp_instToJsonWaitForDiagnostics___lam__0___closed__0_once, _init_l_Lean_Lsp_instToJsonWaitForDiagnostics___lam__0___closed__0);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForILeansParams_fromJson_spec__0_spec__0(lean_object* v_x_430_){
_start:
{
if (lean_obj_tag(v_x_430_) == 0)
{
lean_object* v___x_431_; 
v___x_431_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForILeansParams_fromJson_spec__0_spec__0___closed__0));
return v___x_431_;
}
else
{
lean_object* v___x_432_; 
v___x_432_ = l_Lean_Json_getStr_x3f(v_x_430_);
if (lean_obj_tag(v___x_432_) == 0)
{
lean_object* v_a_433_; lean_object* v___x_435_; uint8_t v_isShared_436_; uint8_t v_isSharedCheck_440_; 
v_a_433_ = lean_ctor_get(v___x_432_, 0);
v_isSharedCheck_440_ = !lean_is_exclusive(v___x_432_);
if (v_isSharedCheck_440_ == 0)
{
v___x_435_ = v___x_432_;
v_isShared_436_ = v_isSharedCheck_440_;
goto v_resetjp_434_;
}
else
{
lean_inc(v_a_433_);
lean_dec(v___x_432_);
v___x_435_ = lean_box(0);
v_isShared_436_ = v_isSharedCheck_440_;
goto v_resetjp_434_;
}
v_resetjp_434_:
{
lean_object* v___x_438_; 
if (v_isShared_436_ == 0)
{
v___x_438_ = v___x_435_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v_a_433_);
v___x_438_ = v_reuseFailAlloc_439_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
return v___x_438_;
}
}
}
else
{
lean_object* v_a_441_; lean_object* v___x_443_; uint8_t v_isShared_444_; uint8_t v_isSharedCheck_449_; 
v_a_441_ = lean_ctor_get(v___x_432_, 0);
v_isSharedCheck_449_ = !lean_is_exclusive(v___x_432_);
if (v_isSharedCheck_449_ == 0)
{
v___x_443_ = v___x_432_;
v_isShared_444_ = v_isSharedCheck_449_;
goto v_resetjp_442_;
}
else
{
lean_inc(v_a_441_);
lean_dec(v___x_432_);
v___x_443_ = lean_box(0);
v_isShared_444_ = v_isSharedCheck_449_;
goto v_resetjp_442_;
}
v_resetjp_442_:
{
lean_object* v___x_445_; lean_object* v___x_447_; 
v___x_445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_445_, 0, v_a_441_);
if (v_isShared_444_ == 0)
{
lean_ctor_set(v___x_443_, 0, v___x_445_);
v___x_447_ = v___x_443_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v___x_445_);
v___x_447_ = v_reuseFailAlloc_448_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
return v___x_447_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForILeansParams_fromJson_spec__0(lean_object* v_j_450_, lean_object* v_k_451_){
_start:
{
lean_object* v___x_452_; lean_object* v___x_453_; 
v___x_452_ = l_Lean_Json_getObjValD(v_j_450_, v_k_451_);
v___x_453_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForILeansParams_fromJson_spec__0_spec__0(v___x_452_);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForILeansParams_fromJson_spec__0___boxed(lean_object* v_j_454_, lean_object* v_k_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForILeansParams_fromJson_spec__0(v_j_454_, v_k_455_);
lean_dec_ref(v_k_455_);
return v_res_456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForILeansParams_fromJson_spec__1_spec__2(lean_object* v_x_459_){
_start:
{
if (lean_obj_tag(v_x_459_) == 0)
{
lean_object* v___x_460_; 
v___x_460_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForILeansParams_fromJson_spec__1_spec__2___closed__0));
return v___x_460_;
}
else
{
lean_object* v___x_461_; 
v___x_461_ = l_Lean_Json_getNat_x3f(v_x_459_);
if (lean_obj_tag(v___x_461_) == 0)
{
lean_object* v_a_462_; lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_469_; 
v_a_462_ = lean_ctor_get(v___x_461_, 0);
v_isSharedCheck_469_ = !lean_is_exclusive(v___x_461_);
if (v_isSharedCheck_469_ == 0)
{
v___x_464_ = v___x_461_;
v_isShared_465_ = v_isSharedCheck_469_;
goto v_resetjp_463_;
}
else
{
lean_inc(v_a_462_);
lean_dec(v___x_461_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_469_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
lean_object* v___x_467_; 
if (v_isShared_465_ == 0)
{
v___x_467_ = v___x_464_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v_a_462_);
v___x_467_ = v_reuseFailAlloc_468_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
return v___x_467_;
}
}
}
else
{
lean_object* v_a_470_; lean_object* v___x_472_; uint8_t v_isShared_473_; uint8_t v_isSharedCheck_478_; 
v_a_470_ = lean_ctor_get(v___x_461_, 0);
v_isSharedCheck_478_ = !lean_is_exclusive(v___x_461_);
if (v_isSharedCheck_478_ == 0)
{
v___x_472_ = v___x_461_;
v_isShared_473_ = v_isSharedCheck_478_;
goto v_resetjp_471_;
}
else
{
lean_inc(v_a_470_);
lean_dec(v___x_461_);
v___x_472_ = lean_box(0);
v_isShared_473_ = v_isSharedCheck_478_;
goto v_resetjp_471_;
}
v_resetjp_471_:
{
lean_object* v___x_474_; lean_object* v___x_476_; 
v___x_474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_474_, 0, v_a_470_);
if (v_isShared_473_ == 0)
{
lean_ctor_set(v___x_472_, 0, v___x_474_);
v___x_476_ = v___x_472_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v___x_474_);
v___x_476_ = v_reuseFailAlloc_477_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
return v___x_476_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForILeansParams_fromJson_spec__1(lean_object* v_j_479_, lean_object* v_k_480_){
_start:
{
lean_object* v___x_481_; lean_object* v___x_482_; 
v___x_481_ = l_Lean_Json_getObjValD(v_j_479_, v_k_480_);
v___x_482_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForILeansParams_fromJson_spec__1_spec__2(v___x_481_);
return v___x_482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForILeansParams_fromJson_spec__1___boxed(lean_object* v_j_483_, lean_object* v_k_484_){
_start:
{
lean_object* v_res_485_; 
v_res_485_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForILeansParams_fromJson_spec__1(v_j_483_, v_k_484_);
lean_dec_ref(v_k_484_);
return v_res_485_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__2(void){
_start:
{
uint8_t v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_491_ = 1;
v___x_492_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__1));
v___x_493_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_492_, v___x_491_);
return v___x_493_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__3(void){
_start:
{
lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_494_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6));
v___x_495_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__2, &l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__2);
v___x_496_ = lean_string_append(v___x_495_, v___x_494_);
return v___x_496_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__6(void){
_start:
{
uint8_t v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_500_ = 1;
v___x_501_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__5));
v___x_502_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_501_, v___x_500_);
return v___x_502_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__7(void){
_start:
{
lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; 
v___x_503_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__6, &l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__6);
v___x_504_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__3);
v___x_505_ = lean_string_append(v___x_504_, v___x_503_);
return v___x_505_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__8(void){
_start:
{
lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; 
v___x_506_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_507_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__7);
v___x_508_ = lean_string_append(v___x_507_, v___x_506_);
return v___x_508_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__11(void){
_start:
{
uint8_t v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; 
v___x_512_ = 1;
v___x_513_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__10));
v___x_514_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_513_, v___x_512_);
return v___x_514_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__12(void){
_start:
{
lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; 
v___x_515_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__11, &l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__11);
v___x_516_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__3);
v___x_517_ = lean_string_append(v___x_516_, v___x_515_);
return v___x_517_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__13(void){
_start:
{
lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_518_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_519_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__12, &l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__12);
v___x_520_ = lean_string_append(v___x_519_, v___x_518_);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson(lean_object* v_json_521_){
_start:
{
lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_522_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__0));
lean_inc(v_json_521_);
v___x_523_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForILeansParams_fromJson_spec__0(v_json_521_, v___x_522_);
if (lean_obj_tag(v___x_523_) == 0)
{
lean_object* v_a_524_; lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_533_; 
lean_dec(v_json_521_);
v_a_524_ = lean_ctor_get(v___x_523_, 0);
v_isSharedCheck_533_ = !lean_is_exclusive(v___x_523_);
if (v_isSharedCheck_533_ == 0)
{
v___x_526_ = v___x_523_;
v_isShared_527_ = v_isSharedCheck_533_;
goto v_resetjp_525_;
}
else
{
lean_inc(v_a_524_);
lean_dec(v___x_523_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_533_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_531_; 
v___x_528_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__8);
v___x_529_ = lean_string_append(v___x_528_, v_a_524_);
lean_dec(v_a_524_);
if (v_isShared_527_ == 0)
{
lean_ctor_set(v___x_526_, 0, v___x_529_);
v___x_531_ = v___x_526_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v___x_529_);
v___x_531_ = v_reuseFailAlloc_532_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
return v___x_531_;
}
}
}
else
{
if (lean_obj_tag(v___x_523_) == 0)
{
lean_object* v_a_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_541_; 
lean_dec(v_json_521_);
v_a_534_ = lean_ctor_get(v___x_523_, 0);
v_isSharedCheck_541_ = !lean_is_exclusive(v___x_523_);
if (v_isSharedCheck_541_ == 0)
{
v___x_536_ = v___x_523_;
v_isShared_537_ = v_isSharedCheck_541_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_a_534_);
lean_dec(v___x_523_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_541_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
lean_object* v___x_539_; 
if (v_isShared_537_ == 0)
{
lean_ctor_set_tag(v___x_536_, 0);
v___x_539_ = v___x_536_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v_a_534_);
v___x_539_ = v_reuseFailAlloc_540_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
return v___x_539_;
}
}
}
else
{
lean_object* v_a_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
v_a_542_ = lean_ctor_get(v___x_523_, 0);
lean_inc(v_a_542_);
lean_dec_ref_known(v___x_523_, 1);
v___x_543_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__9));
v___x_544_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForILeansParams_fromJson_spec__1(v_json_521_, v___x_543_);
if (lean_obj_tag(v___x_544_) == 0)
{
lean_object* v_a_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_554_; 
lean_dec(v_a_542_);
v_a_545_ = lean_ctor_get(v___x_544_, 0);
v_isSharedCheck_554_ = !lean_is_exclusive(v___x_544_);
if (v_isSharedCheck_554_ == 0)
{
v___x_547_ = v___x_544_;
v_isShared_548_ = v_isSharedCheck_554_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_a_545_);
lean_dec(v___x_544_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_554_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_552_; 
v___x_549_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__13, &l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__13);
v___x_550_ = lean_string_append(v___x_549_, v_a_545_);
lean_dec(v_a_545_);
if (v_isShared_548_ == 0)
{
lean_ctor_set(v___x_547_, 0, v___x_550_);
v___x_552_ = v___x_547_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v___x_550_);
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
if (lean_obj_tag(v___x_544_) == 0)
{
lean_object* v_a_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_562_; 
lean_dec(v_a_542_);
v_a_555_ = lean_ctor_get(v___x_544_, 0);
v_isSharedCheck_562_ = !lean_is_exclusive(v___x_544_);
if (v_isSharedCheck_562_ == 0)
{
v___x_557_ = v___x_544_;
v_isShared_558_ = v_isSharedCheck_562_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_a_555_);
lean_dec(v___x_544_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_562_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
lean_object* v___x_560_; 
if (v_isShared_558_ == 0)
{
lean_ctor_set_tag(v___x_557_, 0);
v___x_560_ = v___x_557_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_571_; 
v_a_563_ = lean_ctor_get(v___x_544_, 0);
v_isSharedCheck_571_ = !lean_is_exclusive(v___x_544_);
if (v_isSharedCheck_571_ == 0)
{
v___x_565_ = v___x_544_;
v_isShared_566_ = v_isSharedCheck_571_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_a_563_);
lean_dec(v___x_544_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_571_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
lean_object* v___x_567_; lean_object* v___x_569_; 
v___x_567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_567_, 0, v_a_542_);
lean_ctor_set(v___x_567_, 1, v_a_563_);
if (v_isShared_566_ == 0)
{
lean_ctor_set(v___x_565_, 0, v___x_567_);
v___x_569_ = v___x_565_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v___x_567_);
v___x_569_ = v_reuseFailAlloc_570_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
return v___x_569_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonWaitForILeansParams_toJson_spec__0(lean_object* v_k_574_, lean_object* v_x_575_){
_start:
{
if (lean_obj_tag(v_x_575_) == 0)
{
lean_object* v___x_576_; 
lean_dec_ref(v_k_574_);
v___x_576_ = lean_box(0);
return v___x_576_;
}
else
{
lean_object* v_val_577_; lean_object* v___x_579_; uint8_t v_isShared_580_; uint8_t v_isSharedCheck_587_; 
v_val_577_ = lean_ctor_get(v_x_575_, 0);
v_isSharedCheck_587_ = !lean_is_exclusive(v_x_575_);
if (v_isSharedCheck_587_ == 0)
{
v___x_579_ = v_x_575_;
v_isShared_580_ = v_isSharedCheck_587_;
goto v_resetjp_578_;
}
else
{
lean_inc(v_val_577_);
lean_dec(v_x_575_);
v___x_579_ = lean_box(0);
v_isShared_580_ = v_isSharedCheck_587_;
goto v_resetjp_578_;
}
v_resetjp_578_:
{
lean_object* v___x_582_; 
if (v_isShared_580_ == 0)
{
lean_ctor_set_tag(v___x_579_, 3);
v___x_582_ = v___x_579_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v_val_577_);
v___x_582_ = v_reuseFailAlloc_586_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; 
v___x_583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_583_, 0, v_k_574_);
lean_ctor_set(v___x_583_, 1, v___x_582_);
v___x_584_ = lean_box(0);
v___x_585_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_585_, 0, v___x_583_);
lean_ctor_set(v___x_585_, 1, v___x_584_);
return v___x_585_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonWaitForILeansParams_toJson_spec__1(lean_object* v_k_588_, lean_object* v_x_589_){
_start:
{
if (lean_obj_tag(v_x_589_) == 0)
{
lean_object* v___x_590_; 
lean_dec_ref(v_k_588_);
v___x_590_ = lean_box(0);
return v___x_590_;
}
else
{
lean_object* v_val_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_602_; 
v_val_591_ = lean_ctor_get(v_x_589_, 0);
v_isSharedCheck_602_ = !lean_is_exclusive(v_x_589_);
if (v_isSharedCheck_602_ == 0)
{
v___x_593_ = v_x_589_;
v_isShared_594_ = v_isSharedCheck_602_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_val_591_);
lean_dec(v_x_589_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_602_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v___x_595_; lean_object* v___x_597_; 
v___x_595_ = l_Lean_JsonNumber_fromNat(v_val_591_);
if (v_isShared_594_ == 0)
{
lean_ctor_set_tag(v___x_593_, 2);
lean_ctor_set(v___x_593_, 0, v___x_595_);
v___x_597_ = v___x_593_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v___x_595_);
v___x_597_ = v_reuseFailAlloc_601_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; 
v___x_598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_598_, 0, v_k_588_);
lean_ctor_set(v___x_598_, 1, v___x_597_);
v___x_599_ = lean_box(0);
v___x_600_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_600_, 0, v___x_598_);
lean_ctor_set(v___x_600_, 1, v___x_599_);
return v___x_600_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonWaitForILeansParams_toJson(lean_object* v_x_603_){
_start:
{
lean_object* v_uri_x3f_604_; lean_object* v_version_x3f_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_621_; 
v_uri_x3f_604_ = lean_ctor_get(v_x_603_, 0);
v_version_x3f_605_ = lean_ctor_get(v_x_603_, 1);
v_isSharedCheck_621_ = !lean_is_exclusive(v_x_603_);
if (v_isSharedCheck_621_ == 0)
{
v___x_607_ = v_x_603_;
v_isShared_608_ = v_isSharedCheck_621_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_version_x3f_605_);
lean_inc(v_uri_x3f_604_);
lean_dec(v_x_603_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_621_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_615_; 
v___x_609_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__0));
v___x_610_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonWaitForILeansParams_toJson_spec__0(v___x_609_, v_uri_x3f_604_);
v___x_611_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__9));
v___x_612_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonWaitForILeansParams_toJson_spec__1(v___x_611_, v_version_x3f_605_);
v___x_613_ = lean_box(0);
if (v_isShared_608_ == 0)
{
lean_ctor_set_tag(v___x_607_, 1);
lean_ctor_set(v___x_607_, 1, v___x_613_);
lean_ctor_set(v___x_607_, 0, v___x_612_);
v___x_615_ = v___x_607_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v___x_612_);
lean_ctor_set(v_reuseFailAlloc_620_, 1, v___x_613_);
v___x_615_ = v_reuseFailAlloc_620_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; 
v___x_616_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_616_, 0, v___x_610_);
lean_ctor_set(v___x_616_, 1, v___x_615_);
v___x_617_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0));
v___x_618_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_616_, v___x_617_);
v___x_619_ = l_Lean_Json_mkObj(v___x_618_);
lean_dec(v___x_618_);
return v___x_619_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonWaitForILeans_fromJson(lean_object* v_json_626_){
_start:
{
lean_object* v___x_627_; 
v___x_627_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWaitForILeans_fromJson___closed__0));
return v___x_627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonWaitForILeans_fromJson___boxed(lean_object* v_json_628_){
_start:
{
lean_object* v_res_629_; 
v_res_629_ = l_Lean_Lsp_instFromJsonWaitForILeans_fromJson(v_json_628_);
lean_dec(v_json_628_);
return v_res_629_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonWaitForILeans_toJson___closed__0(void){
_start:
{
lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_632_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0));
v___x_633_ = lean_box(0);
v___x_634_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_633_, v___x_632_);
return v___x_634_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonWaitForILeans_toJson___closed__1(void){
_start:
{
lean_object* v___x_635_; lean_object* v___x_636_; 
v___x_635_ = lean_obj_once(&l_Lean_Lsp_instToJsonWaitForILeans_toJson___closed__0, &l_Lean_Lsp_instToJsonWaitForILeans_toJson___closed__0_once, _init_l_Lean_Lsp_instToJsonWaitForILeans_toJson___closed__0);
v___x_636_ = l_Lean_Json_mkObj(v___x_635_);
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonWaitForILeans_toJson(lean_object* v_x_637_){
_start:
{
lean_object* v___x_638_; 
v___x_638_ = lean_obj_once(&l_Lean_Lsp_instToJsonWaitForILeans_toJson___closed__1, &l_Lean_Lsp_instToJsonWaitForILeans_toJson___closed__1_once, _init_l_Lean_Lsp_instToJsonWaitForILeans_toJson___closed__1);
return v___x_638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanFileProgressKind_ctorIdx(uint8_t v_x_641_){
_start:
{
if (v_x_641_ == 0)
{
lean_object* v___x_642_; 
v___x_642_ = lean_unsigned_to_nat(0u);
return v___x_642_;
}
else
{
lean_object* v___x_643_; 
v___x_643_ = lean_unsigned_to_nat(1u);
return v___x_643_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanFileProgressKind_ctorIdx___boxed(lean_object* v_x_644_){
_start:
{
uint8_t v_x_boxed_645_; lean_object* v_res_646_; 
v_x_boxed_645_ = lean_unbox(v_x_644_);
v_res_646_ = l_Lean_Lsp_LeanFileProgressKind_ctorIdx(v_x_boxed_645_);
return v_res_646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanFileProgressKind_ctorElim___redArg(lean_object* v_k_647_){
_start:
{
lean_inc(v_k_647_);
return v_k_647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanFileProgressKind_ctorElim___redArg___boxed(lean_object* v_k_648_){
_start:
{
lean_object* v_res_649_; 
v_res_649_ = l_Lean_Lsp_LeanFileProgressKind_ctorElim___redArg(v_k_648_);
lean_dec(v_k_648_);
return v_res_649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanFileProgressKind_ctorElim(lean_object* v_motive_650_, lean_object* v_ctorIdx_651_, uint8_t v_t_652_, lean_object* v_h_653_, lean_object* v_k_654_){
_start:
{
lean_inc(v_k_654_);
return v_k_654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanFileProgressKind_ctorElim___boxed(lean_object* v_motive_655_, lean_object* v_ctorIdx_656_, lean_object* v_t_657_, lean_object* v_h_658_, lean_object* v_k_659_){
_start:
{
uint8_t v_t_boxed_660_; lean_object* v_res_661_; 
v_t_boxed_660_ = lean_unbox(v_t_657_);
v_res_661_ = l_Lean_Lsp_LeanFileProgressKind_ctorElim(v_motive_655_, v_ctorIdx_656_, v_t_boxed_660_, v_h_658_, v_k_659_);
lean_dec(v_k_659_);
lean_dec(v_ctorIdx_656_);
return v_res_661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanFileProgressKind_processing_elim___redArg(lean_object* v_processing_662_){
_start:
{
lean_inc(v_processing_662_);
return v_processing_662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanFileProgressKind_processing_elim___redArg___boxed(lean_object* v_processing_663_){
_start:
{
lean_object* v_res_664_; 
v_res_664_ = l_Lean_Lsp_LeanFileProgressKind_processing_elim___redArg(v_processing_663_);
lean_dec(v_processing_663_);
return v_res_664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanFileProgressKind_processing_elim(lean_object* v_motive_665_, uint8_t v_t_666_, lean_object* v_h_667_, lean_object* v_processing_668_){
_start:
{
lean_inc(v_processing_668_);
return v_processing_668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanFileProgressKind_processing_elim___boxed(lean_object* v_motive_669_, lean_object* v_t_670_, lean_object* v_h_671_, lean_object* v_processing_672_){
_start:
{
uint8_t v_t_boxed_673_; lean_object* v_res_674_; 
v_t_boxed_673_ = lean_unbox(v_t_670_);
v_res_674_ = l_Lean_Lsp_LeanFileProgressKind_processing_elim(v_motive_669_, v_t_boxed_673_, v_h_671_, v_processing_672_);
lean_dec(v_processing_672_);
return v_res_674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanFileProgressKind_fatalError_elim___redArg(lean_object* v_fatalError_675_){
_start:
{
lean_inc(v_fatalError_675_);
return v_fatalError_675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanFileProgressKind_fatalError_elim___redArg___boxed(lean_object* v_fatalError_676_){
_start:
{
lean_object* v_res_677_; 
v_res_677_ = l_Lean_Lsp_LeanFileProgressKind_fatalError_elim___redArg(v_fatalError_676_);
lean_dec(v_fatalError_676_);
return v_res_677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanFileProgressKind_fatalError_elim(lean_object* v_motive_678_, uint8_t v_t_679_, lean_object* v_h_680_, lean_object* v_fatalError_681_){
_start:
{
lean_inc(v_fatalError_681_);
return v_fatalError_681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanFileProgressKind_fatalError_elim___boxed(lean_object* v_motive_682_, lean_object* v_t_683_, lean_object* v_h_684_, lean_object* v_fatalError_685_){
_start:
{
uint8_t v_t_boxed_686_; lean_object* v_res_687_; 
v_t_boxed_686_ = lean_unbox(v_t_683_);
v_res_687_ = l_Lean_Lsp_LeanFileProgressKind_fatalError_elim(v_motive_682_, v_t_boxed_686_, v_h_684_, v_fatalError_685_);
lean_dec(v_fatalError_685_);
return v_res_687_;
}
}
static uint8_t _init_l_Lean_Lsp_instInhabitedLeanFileProgressKind_default(void){
_start:
{
uint8_t v___x_688_; 
v___x_688_ = 0;
return v___x_688_;
}
}
static uint8_t _init_l_Lean_Lsp_instInhabitedLeanFileProgressKind(void){
_start:
{
uint8_t v___x_689_; 
v___x_689_ = 0;
return v___x_689_;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_instBEqLeanFileProgressKind_beq(uint8_t v_x_690_, uint8_t v_y_691_){
_start:
{
lean_object* v___x_692_; lean_object* v___x_693_; uint8_t v___x_694_; 
v___x_692_ = l_Lean_Lsp_LeanFileProgressKind_ctorIdx(v_x_690_);
v___x_693_ = l_Lean_Lsp_LeanFileProgressKind_ctorIdx(v_y_691_);
v___x_694_ = lean_nat_dec_eq(v___x_692_, v___x_693_);
lean_dec(v___x_693_);
lean_dec(v___x_692_);
return v___x_694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqLeanFileProgressKind_beq___boxed(lean_object* v_x_695_, lean_object* v_y_696_){
_start:
{
uint8_t v_x_17__boxed_697_; uint8_t v_y_18__boxed_698_; uint8_t v_res_699_; lean_object* v_r_700_; 
v_x_17__boxed_697_ = lean_unbox(v_x_695_);
v_y_18__boxed_698_ = lean_unbox(v_y_696_);
v_res_699_ = l_Lean_Lsp_instBEqLeanFileProgressKind_beq(v_x_17__boxed_697_, v_y_18__boxed_698_);
v_r_700_ = lean_box(v_res_699_);
return v_r_700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanFileProgressKind___lam__0(lean_object* v_j_711_){
_start:
{
lean_object* v___x_720_; 
lean_inc(v_j_711_);
v___x_720_ = l_Lean_Json_getNat_x3f(v_j_711_);
if (lean_obj_tag(v___x_720_) == 1)
{
lean_object* v_a_721_; lean_object* v___x_722_; uint8_t v___x_723_; 
v_a_721_ = lean_ctor_get(v___x_720_, 0);
lean_inc(v_a_721_);
lean_dec_ref_known(v___x_720_, 1);
v___x_722_ = lean_unsigned_to_nat(1u);
v___x_723_ = lean_nat_dec_eq(v_a_721_, v___x_722_);
if (v___x_723_ == 0)
{
lean_object* v___x_724_; uint8_t v___x_725_; 
v___x_724_ = lean_unsigned_to_nat(2u);
v___x_725_ = lean_nat_dec_eq(v_a_721_, v___x_724_);
lean_dec(v_a_721_);
if (v___x_725_ == 0)
{
goto v___jp_712_;
}
else
{
lean_object* v___x_726_; 
lean_dec(v_j_711_);
v___x_726_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressKind___lam__0___closed__2));
return v___x_726_;
}
}
else
{
lean_object* v___x_727_; 
lean_dec(v_a_721_);
lean_dec(v_j_711_);
v___x_727_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressKind___lam__0___closed__3));
return v___x_727_;
}
}
else
{
lean_dec_ref(v___x_720_);
goto v___jp_712_;
}
v___jp_712_:
{
lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_713_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressKind___lam__0___closed__0));
v___x_714_ = lean_unsigned_to_nat(80u);
v___x_715_ = l_Lean_Json_pretty(v_j_711_, v___x_714_);
v___x_716_ = lean_string_append(v___x_713_, v___x_715_);
lean_dec_ref(v___x_715_);
v___x_717_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressKind___lam__0___closed__1));
v___x_718_ = lean_string_append(v___x_716_, v___x_717_);
v___x_719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_719_, 0, v___x_718_);
return v___x_719_;
}
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__0(void){
_start:
{
lean_object* v___x_730_; lean_object* v___x_731_; 
v___x_730_ = lean_unsigned_to_nat(1u);
v___x_731_ = l_Lean_JsonNumber_fromNat(v___x_730_);
return v___x_731_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__1(void){
_start:
{
lean_object* v___x_732_; lean_object* v___x_733_; 
v___x_732_ = lean_obj_once(&l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__0, &l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__0_once, _init_l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__0);
v___x_733_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_733_, 0, v___x_732_);
return v___x_733_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__2(void){
_start:
{
lean_object* v___x_734_; lean_object* v___x_735_; 
v___x_734_ = lean_unsigned_to_nat(2u);
v___x_735_ = l_Lean_JsonNumber_fromNat(v___x_734_);
return v___x_735_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__3(void){
_start:
{
lean_object* v___x_736_; lean_object* v___x_737_; 
v___x_736_ = lean_obj_once(&l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__2, &l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__2_once, _init_l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__2);
v___x_737_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_737_, 0, v___x_736_);
return v___x_737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0(uint8_t v_x_738_){
_start:
{
if (v_x_738_ == 0)
{
lean_object* v___x_739_; 
v___x_739_ = lean_obj_once(&l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__1, &l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__1_once, _init_l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__1);
return v___x_739_;
}
else
{
lean_object* v___x_740_; 
v___x_740_ = lean_obj_once(&l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__3, &l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__3_once, _init_l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__3);
return v___x_740_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___boxed(lean_object* v_x_741_){
_start:
{
uint8_t v_x_56__boxed_742_; lean_object* v_res_743_; 
v_x_56__boxed_742_ = lean_unbox(v_x_741_);
v_res_743_ = l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0(v_x_56__boxed_742_);
return v_res_743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson_spec__0(lean_object* v_j_746_, lean_object* v_k_747_){
_start:
{
lean_object* v___x_748_; lean_object* v___x_749_; 
v___x_748_ = l_Lean_Json_getObjValD(v_j_746_, v_k_747_);
v___x_749_ = l_Lean_Lsp_instFromJsonRange_fromJson(v___x_748_);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson_spec__0___boxed(lean_object* v_j_750_, lean_object* v_k_751_){
_start:
{
lean_object* v_res_752_; 
v_res_752_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson_spec__0(v_j_750_, v_k_751_);
lean_dec_ref(v_k_751_);
return v_res_752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson_spec__1(lean_object* v_j_753_, lean_object* v_k_754_){
_start:
{
lean_object* v___x_755_; lean_object* v___x_764_; 
v___x_755_ = l_Lean_Json_getObjValD(v_j_753_, v_k_754_);
lean_inc(v___x_755_);
v___x_764_ = l_Lean_Json_getNat_x3f(v___x_755_);
if (lean_obj_tag(v___x_764_) == 1)
{
lean_object* v_a_765_; lean_object* v___x_766_; uint8_t v___x_767_; 
v_a_765_ = lean_ctor_get(v___x_764_, 0);
lean_inc(v_a_765_);
lean_dec_ref_known(v___x_764_, 1);
v___x_766_ = lean_unsigned_to_nat(1u);
v___x_767_ = lean_nat_dec_eq(v_a_765_, v___x_766_);
if (v___x_767_ == 0)
{
lean_object* v___x_768_; uint8_t v___x_769_; 
v___x_768_ = lean_unsigned_to_nat(2u);
v___x_769_ = lean_nat_dec_eq(v_a_765_, v___x_768_);
lean_dec(v_a_765_);
if (v___x_769_ == 0)
{
goto v___jp_756_;
}
else
{
lean_object* v___x_770_; 
lean_dec(v___x_755_);
v___x_770_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressKind___lam__0___closed__2));
return v___x_770_;
}
}
else
{
lean_object* v___x_771_; 
lean_dec(v_a_765_);
lean_dec(v___x_755_);
v___x_771_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressKind___lam__0___closed__3));
return v___x_771_;
}
}
else
{
lean_dec_ref(v___x_764_);
goto v___jp_756_;
}
v___jp_756_:
{
lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; 
v___x_757_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressKind___lam__0___closed__0));
v___x_758_ = lean_unsigned_to_nat(80u);
v___x_759_ = l_Lean_Json_pretty(v___x_755_, v___x_758_);
v___x_760_ = lean_string_append(v___x_757_, v___x_759_);
lean_dec_ref(v___x_759_);
v___x_761_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressKind___lam__0___closed__1));
v___x_762_ = lean_string_append(v___x_760_, v___x_761_);
v___x_763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_763_, 0, v___x_762_);
return v___x_763_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson_spec__1___boxed(lean_object* v_j_772_, lean_object* v_k_773_){
_start:
{
lean_object* v_res_774_; 
v_res_774_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson_spec__1(v_j_772_, v_k_773_);
lean_dec_ref(v_k_773_);
return v_res_774_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__3(void){
_start:
{
uint8_t v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; 
v___x_781_ = 1;
v___x_782_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__2));
v___x_783_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_782_, v___x_781_);
return v___x_783_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__4(void){
_start:
{
lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; 
v___x_784_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6));
v___x_785_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__3);
v___x_786_ = lean_string_append(v___x_785_, v___x_784_);
return v___x_786_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__6(void){
_start:
{
uint8_t v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; 
v___x_789_ = 1;
v___x_790_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__5));
v___x_791_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_790_, v___x_789_);
return v___x_791_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__7(void){
_start:
{
lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; 
v___x_792_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__6);
v___x_793_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__4);
v___x_794_ = lean_string_append(v___x_793_, v___x_792_);
return v___x_794_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__8(void){
_start:
{
lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; 
v___x_795_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_796_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__7);
v___x_797_ = lean_string_append(v___x_796_, v___x_795_);
return v___x_797_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__11(void){
_start:
{
uint8_t v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; 
v___x_801_ = 1;
v___x_802_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__10));
v___x_803_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_802_, v___x_801_);
return v___x_803_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__12(void){
_start:
{
lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; 
v___x_804_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__11, &l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__11);
v___x_805_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__4);
v___x_806_ = lean_string_append(v___x_805_, v___x_804_);
return v___x_806_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__13(void){
_start:
{
lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; 
v___x_807_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_808_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__12, &l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__12);
v___x_809_ = lean_string_append(v___x_808_, v___x_807_);
return v___x_809_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson(lean_object* v_json_810_){
_start:
{
lean_object* v___x_811_; lean_object* v___x_812_; 
v___x_811_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__0));
lean_inc(v_json_810_);
v___x_812_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson_spec__0(v_json_810_, v___x_811_);
if (lean_obj_tag(v___x_812_) == 0)
{
lean_object* v_a_813_; lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_822_; 
lean_dec(v_json_810_);
v_a_813_ = lean_ctor_get(v___x_812_, 0);
v_isSharedCheck_822_ = !lean_is_exclusive(v___x_812_);
if (v_isSharedCheck_822_ == 0)
{
v___x_815_ = v___x_812_;
v_isShared_816_ = v_isSharedCheck_822_;
goto v_resetjp_814_;
}
else
{
lean_inc(v_a_813_);
lean_dec(v___x_812_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_822_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_820_; 
v___x_817_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__8);
v___x_818_ = lean_string_append(v___x_817_, v_a_813_);
lean_dec(v_a_813_);
if (v_isShared_816_ == 0)
{
lean_ctor_set(v___x_815_, 0, v___x_818_);
v___x_820_ = v___x_815_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v___x_818_);
v___x_820_ = v_reuseFailAlloc_821_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
return v___x_820_;
}
}
}
else
{
if (lean_obj_tag(v___x_812_) == 0)
{
lean_object* v_a_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_830_; 
lean_dec(v_json_810_);
v_a_823_ = lean_ctor_get(v___x_812_, 0);
v_isSharedCheck_830_ = !lean_is_exclusive(v___x_812_);
if (v_isSharedCheck_830_ == 0)
{
v___x_825_ = v___x_812_;
v_isShared_826_ = v_isSharedCheck_830_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_a_823_);
lean_dec(v___x_812_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_830_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
lean_object* v___x_828_; 
if (v_isShared_826_ == 0)
{
lean_ctor_set_tag(v___x_825_, 0);
v___x_828_ = v___x_825_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v_a_823_);
v___x_828_ = v_reuseFailAlloc_829_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
return v___x_828_;
}
}
}
else
{
lean_object* v_a_831_; lean_object* v___x_832_; lean_object* v___x_833_; 
v_a_831_ = lean_ctor_get(v___x_812_, 0);
lean_inc(v_a_831_);
lean_dec_ref_known(v___x_812_, 1);
v___x_832_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__9));
v___x_833_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson_spec__1(v_json_810_, v___x_832_);
if (lean_obj_tag(v___x_833_) == 0)
{
lean_object* v_a_834_; lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_843_; 
lean_dec(v_a_831_);
v_a_834_ = lean_ctor_get(v___x_833_, 0);
v_isSharedCheck_843_ = !lean_is_exclusive(v___x_833_);
if (v_isSharedCheck_843_ == 0)
{
v___x_836_ = v___x_833_;
v_isShared_837_ = v_isSharedCheck_843_;
goto v_resetjp_835_;
}
else
{
lean_inc(v_a_834_);
lean_dec(v___x_833_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_843_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_841_; 
v___x_838_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__13, &l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__13);
v___x_839_ = lean_string_append(v___x_838_, v_a_834_);
lean_dec(v_a_834_);
if (v_isShared_837_ == 0)
{
lean_ctor_set(v___x_836_, 0, v___x_839_);
v___x_841_ = v___x_836_;
goto v_reusejp_840_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v___x_839_);
v___x_841_ = v_reuseFailAlloc_842_;
goto v_reusejp_840_;
}
v_reusejp_840_:
{
return v___x_841_;
}
}
}
else
{
if (lean_obj_tag(v___x_833_) == 0)
{
lean_object* v_a_844_; lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_851_; 
lean_dec(v_a_831_);
v_a_844_ = lean_ctor_get(v___x_833_, 0);
v_isSharedCheck_851_ = !lean_is_exclusive(v___x_833_);
if (v_isSharedCheck_851_ == 0)
{
v___x_846_ = v___x_833_;
v_isShared_847_ = v_isSharedCheck_851_;
goto v_resetjp_845_;
}
else
{
lean_inc(v_a_844_);
lean_dec(v___x_833_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_851_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
lean_object* v___x_849_; 
if (v_isShared_847_ == 0)
{
lean_ctor_set_tag(v___x_846_, 0);
v___x_849_ = v___x_846_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v_a_844_);
v___x_849_ = v_reuseFailAlloc_850_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
return v___x_849_;
}
}
}
else
{
lean_object* v_a_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_861_; 
v_a_852_ = lean_ctor_get(v___x_833_, 0);
v_isSharedCheck_861_ = !lean_is_exclusive(v___x_833_);
if (v_isSharedCheck_861_ == 0)
{
v___x_854_ = v___x_833_;
v_isShared_855_ = v_isSharedCheck_861_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_a_852_);
lean_dec(v___x_833_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_861_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
lean_object* v___x_856_; uint8_t v___x_857_; lean_object* v___x_859_; 
v___x_856_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_856_, 0, v_a_831_);
v___x_857_ = lean_unbox(v_a_852_);
lean_dec(v_a_852_);
lean_ctor_set_uint8(v___x_856_, sizeof(void*)*1, v___x_857_);
if (v_isShared_855_ == 0)
{
lean_ctor_set(v___x_854_, 0, v___x_856_);
v___x_859_ = v___x_854_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v___x_856_);
v___x_859_ = v_reuseFailAlloc_860_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
return v___x_859_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanFileProgressProcessingInfo_toJson(lean_object* v_x_864_){
_start:
{
lean_object* v_range_865_; uint8_t v_kind_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___y_874_; 
v_range_865_ = lean_ctor_get(v_x_864_, 0);
lean_inc_ref(v_range_865_);
v_kind_866_ = lean_ctor_get_uint8(v_x_864_, sizeof(void*)*1);
lean_dec_ref(v_x_864_);
v___x_867_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__0));
v___x_868_ = l_Lean_Lsp_instToJsonRange_toJson(v_range_865_);
v___x_869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_869_, 0, v___x_867_);
lean_ctor_set(v___x_869_, 1, v___x_868_);
v___x_870_ = lean_box(0);
v___x_871_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_871_, 0, v___x_869_);
lean_ctor_set(v___x_871_, 1, v___x_870_);
v___x_872_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__9));
if (v_kind_866_ == 0)
{
lean_object* v___x_882_; 
v___x_882_ = lean_obj_once(&l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__1, &l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__1_once, _init_l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__1);
v___y_874_ = v___x_882_;
goto v___jp_873_;
}
else
{
lean_object* v___x_883_; 
v___x_883_ = lean_obj_once(&l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__3, &l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__3_once, _init_l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__3);
v___y_874_ = v___x_883_;
goto v___jp_873_;
}
v___jp_873_:
{
lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; 
lean_inc(v___y_874_);
v___x_875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_875_, 0, v___x_872_);
lean_ctor_set(v___x_875_, 1, v___y_874_);
v___x_876_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_876_, 0, v___x_875_);
lean_ctor_set(v___x_876_, 1, v___x_870_);
v___x_877_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_877_, 0, v___x_876_);
lean_ctor_set(v___x_877_, 1, v___x_870_);
v___x_878_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_878_, 0, v___x_871_);
lean_ctor_set(v___x_878_, 1, v___x_877_);
v___x_879_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0));
v___x_880_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_878_, v___x_879_);
v___x_881_ = l_Lean_Json_mkObj(v___x_880_);
lean_dec(v___x_880_);
return v___x_881_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__0(lean_object* v_j_886_, lean_object* v_k_887_){
_start:
{
lean_object* v___x_888_; lean_object* v___x_889_; 
v___x_888_ = l_Lean_Json_getObjValD(v_j_886_, v_k_887_);
v___x_889_ = l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson(v___x_888_);
return v___x_889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__0___boxed(lean_object* v_j_890_, lean_object* v_k_891_){
_start:
{
lean_object* v_res_892_; 
v_res_892_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__0(v_j_890_, v_k_891_);
lean_dec_ref(v_k_891_);
return v_res_892_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__1_spec__1_spec__2(size_t v_sz_893_, size_t v_i_894_, lean_object* v_bs_895_){
_start:
{
uint8_t v___x_896_; 
v___x_896_ = lean_usize_dec_lt(v_i_894_, v_sz_893_);
if (v___x_896_ == 0)
{
lean_object* v___x_897_; 
v___x_897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_897_, 0, v_bs_895_);
return v___x_897_;
}
else
{
lean_object* v_v_898_; lean_object* v___x_899_; 
v_v_898_ = lean_array_uget_borrowed(v_bs_895_, v_i_894_);
lean_inc(v_v_898_);
v___x_899_ = l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson(v_v_898_);
if (lean_obj_tag(v___x_899_) == 0)
{
lean_object* v_a_900_; lean_object* v___x_902_; uint8_t v_isShared_903_; uint8_t v_isSharedCheck_907_; 
lean_dec_ref(v_bs_895_);
v_a_900_ = lean_ctor_get(v___x_899_, 0);
v_isSharedCheck_907_ = !lean_is_exclusive(v___x_899_);
if (v_isSharedCheck_907_ == 0)
{
v___x_902_ = v___x_899_;
v_isShared_903_ = v_isSharedCheck_907_;
goto v_resetjp_901_;
}
else
{
lean_inc(v_a_900_);
lean_dec(v___x_899_);
v___x_902_ = lean_box(0);
v_isShared_903_ = v_isSharedCheck_907_;
goto v_resetjp_901_;
}
v_resetjp_901_:
{
lean_object* v___x_905_; 
if (v_isShared_903_ == 0)
{
v___x_905_ = v___x_902_;
goto v_reusejp_904_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v_a_900_);
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
lean_object* v_a_908_; lean_object* v___x_909_; lean_object* v_bs_x27_910_; size_t v___x_911_; size_t v___x_912_; lean_object* v___x_913_; 
v_a_908_ = lean_ctor_get(v___x_899_, 0);
lean_inc(v_a_908_);
lean_dec_ref_known(v___x_899_, 1);
v___x_909_ = lean_unsigned_to_nat(0u);
v_bs_x27_910_ = lean_array_uset(v_bs_895_, v_i_894_, v___x_909_);
v___x_911_ = ((size_t)1ULL);
v___x_912_ = lean_usize_add(v_i_894_, v___x_911_);
v___x_913_ = lean_array_uset(v_bs_x27_910_, v_i_894_, v_a_908_);
v_i_894_ = v___x_912_;
v_bs_895_ = v___x_913_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__1_spec__1_spec__2___boxed(lean_object* v_sz_915_, lean_object* v_i_916_, lean_object* v_bs_917_){
_start:
{
size_t v_sz_boxed_918_; size_t v_i_boxed_919_; lean_object* v_res_920_; 
v_sz_boxed_918_ = lean_unbox_usize(v_sz_915_);
lean_dec(v_sz_915_);
v_i_boxed_919_ = lean_unbox_usize(v_i_916_);
lean_dec(v_i_916_);
v_res_920_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__1_spec__1_spec__2(v_sz_boxed_918_, v_i_boxed_919_, v_bs_917_);
return v_res_920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__1_spec__1(lean_object* v_x_922_){
_start:
{
if (lean_obj_tag(v_x_922_) == 4)
{
lean_object* v_elems_923_; size_t v_sz_924_; size_t v___x_925_; lean_object* v___x_926_; 
v_elems_923_ = lean_ctor_get(v_x_922_, 0);
lean_inc_ref(v_elems_923_);
lean_dec_ref_known(v_x_922_, 1);
v_sz_924_ = lean_array_size(v_elems_923_);
v___x_925_ = ((size_t)0ULL);
v___x_926_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__1_spec__1_spec__2(v_sz_924_, v___x_925_, v_elems_923_);
return v___x_926_;
}
else
{
lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; 
v___x_927_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__1_spec__1___closed__0));
v___x_928_ = lean_unsigned_to_nat(80u);
v___x_929_ = l_Lean_Json_pretty(v_x_922_, v___x_928_);
v___x_930_ = lean_string_append(v___x_927_, v___x_929_);
lean_dec_ref(v___x_929_);
v___x_931_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressKind___lam__0___closed__1));
v___x_932_ = lean_string_append(v___x_930_, v___x_931_);
v___x_933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_933_, 0, v___x_932_);
return v___x_933_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__1(lean_object* v_j_934_, lean_object* v_k_935_){
_start:
{
lean_object* v___x_936_; lean_object* v___x_937_; 
v___x_936_ = l_Lean_Json_getObjValD(v_j_934_, v_k_935_);
v___x_937_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__1_spec__1(v___x_936_);
return v___x_937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__1___boxed(lean_object* v_j_938_, lean_object* v_k_939_){
_start:
{
lean_object* v_res_940_; 
v_res_940_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__1(v_j_938_, v_k_939_);
lean_dec_ref(v_k_939_);
return v_res_940_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__2(void){
_start:
{
uint8_t v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; 
v___x_946_ = 1;
v___x_947_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__1));
v___x_948_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_947_, v___x_946_);
return v___x_948_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__3(void){
_start:
{
lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; 
v___x_949_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6));
v___x_950_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__2, &l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__2);
v___x_951_ = lean_string_append(v___x_950_, v___x_949_);
return v___x_951_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; 
v___x_952_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9, &l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9);
v___x_953_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__3);
v___x_954_ = lean_string_append(v___x_953_, v___x_952_);
return v___x_954_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__5(void){
_start:
{
lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; 
v___x_955_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_956_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__4);
v___x_957_ = lean_string_append(v___x_956_, v___x_955_);
return v___x_957_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__8(void){
_start:
{
uint8_t v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; 
v___x_961_ = 1;
v___x_962_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__7));
v___x_963_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_962_, v___x_961_);
return v___x_963_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__9(void){
_start:
{
lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; 
v___x_964_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__8);
v___x_965_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__3);
v___x_966_ = lean_string_append(v___x_965_, v___x_964_);
return v___x_966_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__10(void){
_start:
{
lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; 
v___x_967_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_968_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__9, &l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__9);
v___x_969_ = lean_string_append(v___x_968_, v___x_967_);
return v___x_969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson(lean_object* v_json_970_){
_start:
{
lean_object* v___x_971_; lean_object* v___x_972_; 
v___x_971_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__0));
lean_inc(v_json_970_);
v___x_972_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__0(v_json_970_, v___x_971_);
if (lean_obj_tag(v___x_972_) == 0)
{
lean_object* v_a_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_982_; 
lean_dec(v_json_970_);
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
v___x_977_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__5, &l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__5);
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
lean_dec(v_json_970_);
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
v___x_992_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__6));
v___x_993_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__1(v_json_970_, v___x_992_);
if (lean_obj_tag(v___x_993_) == 0)
{
lean_object* v_a_994_; lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1003_; 
lean_dec(v_a_991_);
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
v___x_998_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__10, &l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__10);
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
v___x_1016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1016_, 0, v_a_991_);
lean_ctor_set(v___x_1016_, 1, v_a_1012_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanFileProgressParams_toJson_spec__0_spec__0(size_t v_sz_1023_, size_t v_i_1024_, lean_object* v_bs_1025_){
_start:
{
uint8_t v___x_1026_; 
v___x_1026_ = lean_usize_dec_lt(v_i_1024_, v_sz_1023_);
if (v___x_1026_ == 0)
{
return v_bs_1025_;
}
else
{
lean_object* v_v_1027_; lean_object* v___x_1028_; lean_object* v_bs_x27_1029_; lean_object* v___x_1030_; size_t v___x_1031_; size_t v___x_1032_; lean_object* v___x_1033_; 
v_v_1027_ = lean_array_uget(v_bs_1025_, v_i_1024_);
v___x_1028_ = lean_unsigned_to_nat(0u);
v_bs_x27_1029_ = lean_array_uset(v_bs_1025_, v_i_1024_, v___x_1028_);
v___x_1030_ = l_Lean_Lsp_instToJsonLeanFileProgressProcessingInfo_toJson(v_v_1027_);
v___x_1031_ = ((size_t)1ULL);
v___x_1032_ = lean_usize_add(v_i_1024_, v___x_1031_);
v___x_1033_ = lean_array_uset(v_bs_x27_1029_, v_i_1024_, v___x_1030_);
v_i_1024_ = v___x_1032_;
v_bs_1025_ = v___x_1033_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanFileProgressParams_toJson_spec__0_spec__0___boxed(lean_object* v_sz_1035_, lean_object* v_i_1036_, lean_object* v_bs_1037_){
_start:
{
size_t v_sz_boxed_1038_; size_t v_i_boxed_1039_; lean_object* v_res_1040_; 
v_sz_boxed_1038_ = lean_unbox_usize(v_sz_1035_);
lean_dec(v_sz_1035_);
v_i_boxed_1039_ = lean_unbox_usize(v_i_1036_);
lean_dec(v_i_1036_);
v_res_1040_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanFileProgressParams_toJson_spec__0_spec__0(v_sz_boxed_1038_, v_i_boxed_1039_, v_bs_1037_);
return v_res_1040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanFileProgressParams_toJson_spec__0(lean_object* v_a_1041_){
_start:
{
size_t v_sz_1042_; size_t v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; 
v_sz_1042_ = lean_array_size(v_a_1041_);
v___x_1043_ = ((size_t)0ULL);
v___x_1044_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanFileProgressParams_toJson_spec__0_spec__0(v_sz_1042_, v___x_1043_, v_a_1041_);
v___x_1045_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1045_, 0, v___x_1044_);
return v___x_1045_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanFileProgressParams_toJson(lean_object* v_x_1046_){
_start:
{
lean_object* v_textDocument_1047_; lean_object* v_processing_1048_; lean_object* v___x_1050_; uint8_t v_isShared_1051_; uint8_t v_isSharedCheck_1068_; 
v_textDocument_1047_ = lean_ctor_get(v_x_1046_, 0);
v_processing_1048_ = lean_ctor_get(v_x_1046_, 1);
v_isSharedCheck_1068_ = !lean_is_exclusive(v_x_1046_);
if (v_isSharedCheck_1068_ == 0)
{
v___x_1050_ = v_x_1046_;
v_isShared_1051_ = v_isSharedCheck_1068_;
goto v_resetjp_1049_;
}
else
{
lean_inc(v_processing_1048_);
lean_inc(v_textDocument_1047_);
lean_dec(v_x_1046_);
v___x_1050_ = lean_box(0);
v_isShared_1051_ = v_isSharedCheck_1068_;
goto v_resetjp_1049_;
}
v_resetjp_1049_:
{
lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1055_; 
v___x_1052_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__0));
v___x_1053_ = l_Lean_Lsp_instToJsonVersionedTextDocumentIdentifier_toJson(v_textDocument_1047_);
if (v_isShared_1051_ == 0)
{
lean_ctor_set(v___x_1050_, 1, v___x_1053_);
lean_ctor_set(v___x_1050_, 0, v___x_1052_);
v___x_1055_ = v___x_1050_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v___x_1052_);
lean_ctor_set(v_reuseFailAlloc_1067_, 1, v___x_1053_);
v___x_1055_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; 
v___x_1056_ = lean_box(0);
v___x_1057_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1057_, 0, v___x_1055_);
lean_ctor_set(v___x_1057_, 1, v___x_1056_);
v___x_1058_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__6));
v___x_1059_ = l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanFileProgressParams_toJson_spec__0(v_processing_1048_);
v___x_1060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1060_, 0, v___x_1058_);
lean_ctor_set(v___x_1060_, 1, v___x_1059_);
v___x_1061_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1061_, 0, v___x_1060_);
lean_ctor_set(v___x_1061_, 1, v___x_1056_);
v___x_1062_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1062_, 0, v___x_1061_);
lean_ctor_set(v___x_1062_, 1, v___x_1056_);
v___x_1063_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1063_, 0, v___x_1057_);
lean_ctor_set(v___x_1063_, 1, v___x_1062_);
v___x_1064_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0));
v___x_1065_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_1063_, v___x_1064_);
v___x_1066_ = l_Lean_Json_mkObj(v___x_1065_);
lean_dec(v___x_1065_);
return v___x_1066_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoalParams_fromJson_spec__0(lean_object* v_j_1071_, lean_object* v_k_1072_){
_start:
{
lean_object* v___x_1073_; lean_object* v___x_1074_; 
v___x_1073_ = l_Lean_Json_getObjValD(v_j_1071_, v_k_1072_);
v___x_1074_ = l_Lean_Lsp_instFromJsonTextDocumentIdentifier_fromJson(v___x_1073_);
return v___x_1074_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoalParams_fromJson_spec__0___boxed(lean_object* v_j_1075_, lean_object* v_k_1076_){
_start:
{
lean_object* v_res_1077_; 
v_res_1077_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoalParams_fromJson_spec__0(v_j_1075_, v_k_1076_);
lean_dec_ref(v_k_1076_);
return v_res_1077_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoalParams_fromJson_spec__1(lean_object* v_j_1078_, lean_object* v_k_1079_){
_start:
{
lean_object* v___x_1080_; lean_object* v___x_1081_; 
v___x_1080_ = l_Lean_Json_getObjValD(v_j_1078_, v_k_1079_);
v___x_1081_ = l_Lean_Lsp_instFromJsonPosition_fromJson(v___x_1080_);
return v___x_1081_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoalParams_fromJson_spec__1___boxed(lean_object* v_j_1082_, lean_object* v_k_1083_){
_start:
{
lean_object* v_res_1084_; 
v_res_1084_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoalParams_fromJson_spec__1(v_j_1082_, v_k_1083_);
lean_dec_ref(v_k_1083_);
return v_res_1084_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__2(void){
_start:
{
uint8_t v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; 
v___x_1090_ = 1;
v___x_1091_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__1));
v___x_1092_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1091_, v___x_1090_);
return v___x_1092_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__3(void){
_start:
{
lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; 
v___x_1093_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6));
v___x_1094_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__2, &l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__2);
v___x_1095_ = lean_string_append(v___x_1094_, v___x_1093_);
return v___x_1095_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; 
v___x_1096_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9, &l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9);
v___x_1097_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__3);
v___x_1098_ = lean_string_append(v___x_1097_, v___x_1096_);
return v___x_1098_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__5(void){
_start:
{
lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; 
v___x_1099_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_1100_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__4);
v___x_1101_ = lean_string_append(v___x_1100_, v___x_1099_);
return v___x_1101_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__8(void){
_start:
{
uint8_t v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; 
v___x_1105_ = 1;
v___x_1106_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__7));
v___x_1107_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1106_, v___x_1105_);
return v___x_1107_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__9(void){
_start:
{
lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; 
v___x_1108_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__8);
v___x_1109_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__3);
v___x_1110_ = lean_string_append(v___x_1109_, v___x_1108_);
return v___x_1110_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__10(void){
_start:
{
lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; 
v___x_1111_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_1112_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__9, &l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__9);
v___x_1113_ = lean_string_append(v___x_1112_, v___x_1111_);
return v___x_1113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson(lean_object* v_json_1114_){
_start:
{
lean_object* v___x_1115_; lean_object* v___x_1116_; 
v___x_1115_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__0));
lean_inc(v_json_1114_);
v___x_1116_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoalParams_fromJson_spec__0(v_json_1114_, v___x_1115_);
if (lean_obj_tag(v___x_1116_) == 0)
{
lean_object* v_a_1117_; lean_object* v___x_1119_; uint8_t v_isShared_1120_; uint8_t v_isSharedCheck_1126_; 
lean_dec(v_json_1114_);
v_a_1117_ = lean_ctor_get(v___x_1116_, 0);
v_isSharedCheck_1126_ = !lean_is_exclusive(v___x_1116_);
if (v_isSharedCheck_1126_ == 0)
{
v___x_1119_ = v___x_1116_;
v_isShared_1120_ = v_isSharedCheck_1126_;
goto v_resetjp_1118_;
}
else
{
lean_inc(v_a_1117_);
lean_dec(v___x_1116_);
v___x_1119_ = lean_box(0);
v_isShared_1120_ = v_isSharedCheck_1126_;
goto v_resetjp_1118_;
}
v_resetjp_1118_:
{
lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1124_; 
v___x_1121_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__5, &l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__5);
v___x_1122_ = lean_string_append(v___x_1121_, v_a_1117_);
lean_dec(v_a_1117_);
if (v_isShared_1120_ == 0)
{
lean_ctor_set(v___x_1119_, 0, v___x_1122_);
v___x_1124_ = v___x_1119_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v___x_1122_);
v___x_1124_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
return v___x_1124_;
}
}
}
else
{
if (lean_obj_tag(v___x_1116_) == 0)
{
lean_object* v_a_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1134_; 
lean_dec(v_json_1114_);
v_a_1127_ = lean_ctor_get(v___x_1116_, 0);
v_isSharedCheck_1134_ = !lean_is_exclusive(v___x_1116_);
if (v_isSharedCheck_1134_ == 0)
{
v___x_1129_ = v___x_1116_;
v_isShared_1130_ = v_isSharedCheck_1134_;
goto v_resetjp_1128_;
}
else
{
lean_inc(v_a_1127_);
lean_dec(v___x_1116_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1134_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
lean_object* v___x_1132_; 
if (v_isShared_1130_ == 0)
{
lean_ctor_set_tag(v___x_1129_, 0);
v___x_1132_ = v___x_1129_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v_a_1127_);
v___x_1132_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
return v___x_1132_;
}
}
}
else
{
lean_object* v_a_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; 
v_a_1135_ = lean_ctor_get(v___x_1116_, 0);
lean_inc(v_a_1135_);
lean_dec_ref_known(v___x_1116_, 1);
v___x_1136_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__6));
v___x_1137_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoalParams_fromJson_spec__1(v_json_1114_, v___x_1136_);
if (lean_obj_tag(v___x_1137_) == 0)
{
lean_object* v_a_1138_; lean_object* v___x_1140_; uint8_t v_isShared_1141_; uint8_t v_isSharedCheck_1147_; 
lean_dec(v_a_1135_);
v_a_1138_ = lean_ctor_get(v___x_1137_, 0);
v_isSharedCheck_1147_ = !lean_is_exclusive(v___x_1137_);
if (v_isSharedCheck_1147_ == 0)
{
v___x_1140_ = v___x_1137_;
v_isShared_1141_ = v_isSharedCheck_1147_;
goto v_resetjp_1139_;
}
else
{
lean_inc(v_a_1138_);
lean_dec(v___x_1137_);
v___x_1140_ = lean_box(0);
v_isShared_1141_ = v_isSharedCheck_1147_;
goto v_resetjp_1139_;
}
v_resetjp_1139_:
{
lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1145_; 
v___x_1142_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__10, &l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__10);
v___x_1143_ = lean_string_append(v___x_1142_, v_a_1138_);
lean_dec(v_a_1138_);
if (v_isShared_1141_ == 0)
{
lean_ctor_set(v___x_1140_, 0, v___x_1143_);
v___x_1145_ = v___x_1140_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v___x_1143_);
v___x_1145_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
return v___x_1145_;
}
}
}
else
{
if (lean_obj_tag(v___x_1137_) == 0)
{
lean_object* v_a_1148_; lean_object* v___x_1150_; uint8_t v_isShared_1151_; uint8_t v_isSharedCheck_1155_; 
lean_dec(v_a_1135_);
v_a_1148_ = lean_ctor_get(v___x_1137_, 0);
v_isSharedCheck_1155_ = !lean_is_exclusive(v___x_1137_);
if (v_isSharedCheck_1155_ == 0)
{
v___x_1150_ = v___x_1137_;
v_isShared_1151_ = v_isSharedCheck_1155_;
goto v_resetjp_1149_;
}
else
{
lean_inc(v_a_1148_);
lean_dec(v___x_1137_);
v___x_1150_ = lean_box(0);
v_isShared_1151_ = v_isSharedCheck_1155_;
goto v_resetjp_1149_;
}
v_resetjp_1149_:
{
lean_object* v___x_1153_; 
if (v_isShared_1151_ == 0)
{
lean_ctor_set_tag(v___x_1150_, 0);
v___x_1153_ = v___x_1150_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v_a_1148_);
v___x_1153_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
return v___x_1153_;
}
}
}
else
{
lean_object* v_a_1156_; lean_object* v___x_1158_; uint8_t v_isShared_1159_; uint8_t v_isSharedCheck_1164_; 
v_a_1156_ = lean_ctor_get(v___x_1137_, 0);
v_isSharedCheck_1164_ = !lean_is_exclusive(v___x_1137_);
if (v_isSharedCheck_1164_ == 0)
{
v___x_1158_ = v___x_1137_;
v_isShared_1159_ = v_isSharedCheck_1164_;
goto v_resetjp_1157_;
}
else
{
lean_inc(v_a_1156_);
lean_dec(v___x_1137_);
v___x_1158_ = lean_box(0);
v_isShared_1159_ = v_isSharedCheck_1164_;
goto v_resetjp_1157_;
}
v_resetjp_1157_:
{
lean_object* v___x_1160_; lean_object* v___x_1162_; 
v___x_1160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1160_, 0, v_a_1135_);
lean_ctor_set(v___x_1160_, 1, v_a_1156_);
if (v_isShared_1159_ == 0)
{
lean_ctor_set(v___x_1158_, 0, v___x_1160_);
v___x_1162_ = v___x_1158_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v___x_1160_);
v___x_1162_ = v_reuseFailAlloc_1163_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
return v___x_1162_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonPlainGoalParams_toJson(lean_object* v_x_1167_){
_start:
{
lean_object* v_textDocument_1168_; lean_object* v_position_1169_; lean_object* v___x_1171_; uint8_t v_isShared_1172_; uint8_t v_isSharedCheck_1189_; 
v_textDocument_1168_ = lean_ctor_get(v_x_1167_, 0);
v_position_1169_ = lean_ctor_get(v_x_1167_, 1);
v_isSharedCheck_1189_ = !lean_is_exclusive(v_x_1167_);
if (v_isSharedCheck_1189_ == 0)
{
v___x_1171_ = v_x_1167_;
v_isShared_1172_ = v_isSharedCheck_1189_;
goto v_resetjp_1170_;
}
else
{
lean_inc(v_position_1169_);
lean_inc(v_textDocument_1168_);
lean_dec(v_x_1167_);
v___x_1171_ = lean_box(0);
v_isShared_1172_ = v_isSharedCheck_1189_;
goto v_resetjp_1170_;
}
v_resetjp_1170_:
{
lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1176_; 
v___x_1173_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__0));
v___x_1174_ = l_Lean_Lsp_instToJsonTextDocumentIdentifier_toJson(v_textDocument_1168_);
if (v_isShared_1172_ == 0)
{
lean_ctor_set(v___x_1171_, 1, v___x_1174_);
lean_ctor_set(v___x_1171_, 0, v___x_1173_);
v___x_1176_ = v___x_1171_;
goto v_reusejp_1175_;
}
else
{
lean_object* v_reuseFailAlloc_1188_; 
v_reuseFailAlloc_1188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1188_, 0, v___x_1173_);
lean_ctor_set(v_reuseFailAlloc_1188_, 1, v___x_1174_);
v___x_1176_ = v_reuseFailAlloc_1188_;
goto v_reusejp_1175_;
}
v_reusejp_1175_:
{
lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; 
v___x_1177_ = lean_box(0);
v___x_1178_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1178_, 0, v___x_1176_);
lean_ctor_set(v___x_1178_, 1, v___x_1177_);
v___x_1179_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__6));
v___x_1180_ = l_Lean_Lsp_instToJsonPosition_toJson(v_position_1169_);
v___x_1181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1181_, 0, v___x_1179_);
lean_ctor_set(v___x_1181_, 1, v___x_1180_);
v___x_1182_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1182_, 0, v___x_1181_);
lean_ctor_set(v___x_1182_, 1, v___x_1177_);
v___x_1183_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1183_, 0, v___x_1182_);
lean_ctor_set(v___x_1183_, 1, v___x_1177_);
v___x_1184_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1184_, 0, v___x_1178_);
lean_ctor_set(v___x_1184_, 1, v___x_1183_);
v___x_1185_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0));
v___x_1186_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_1184_, v___x_1185_);
v___x_1187_ = l_Lean_Json_mkObj(v___x_1186_);
lean_dec(v___x_1186_);
return v___x_1187_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoal_fromJson_spec__0_spec__0_spec__1(size_t v_sz_1192_, size_t v_i_1193_, lean_object* v_bs_1194_){
_start:
{
uint8_t v___x_1195_; 
v___x_1195_ = lean_usize_dec_lt(v_i_1193_, v_sz_1192_);
if (v___x_1195_ == 0)
{
lean_object* v___x_1196_; 
v___x_1196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1196_, 0, v_bs_1194_);
return v___x_1196_;
}
else
{
lean_object* v_v_1197_; lean_object* v___x_1198_; 
v_v_1197_ = lean_array_uget_borrowed(v_bs_1194_, v_i_1193_);
lean_inc(v_v_1197_);
v___x_1198_ = l_Lean_Json_getStr_x3f(v_v_1197_);
if (lean_obj_tag(v___x_1198_) == 0)
{
lean_object* v_a_1199_; lean_object* v___x_1201_; uint8_t v_isShared_1202_; uint8_t v_isSharedCheck_1206_; 
lean_dec_ref(v_bs_1194_);
v_a_1199_ = lean_ctor_get(v___x_1198_, 0);
v_isSharedCheck_1206_ = !lean_is_exclusive(v___x_1198_);
if (v_isSharedCheck_1206_ == 0)
{
v___x_1201_ = v___x_1198_;
v_isShared_1202_ = v_isSharedCheck_1206_;
goto v_resetjp_1200_;
}
else
{
lean_inc(v_a_1199_);
lean_dec(v___x_1198_);
v___x_1201_ = lean_box(0);
v_isShared_1202_ = v_isSharedCheck_1206_;
goto v_resetjp_1200_;
}
v_resetjp_1200_:
{
lean_object* v___x_1204_; 
if (v_isShared_1202_ == 0)
{
v___x_1204_ = v___x_1201_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v_a_1199_);
v___x_1204_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
return v___x_1204_;
}
}
}
else
{
lean_object* v_a_1207_; lean_object* v___x_1208_; lean_object* v_bs_x27_1209_; size_t v___x_1210_; size_t v___x_1211_; lean_object* v___x_1212_; 
v_a_1207_ = lean_ctor_get(v___x_1198_, 0);
lean_inc(v_a_1207_);
lean_dec_ref_known(v___x_1198_, 1);
v___x_1208_ = lean_unsigned_to_nat(0u);
v_bs_x27_1209_ = lean_array_uset(v_bs_1194_, v_i_1193_, v___x_1208_);
v___x_1210_ = ((size_t)1ULL);
v___x_1211_ = lean_usize_add(v_i_1193_, v___x_1210_);
v___x_1212_ = lean_array_uset(v_bs_x27_1209_, v_i_1193_, v_a_1207_);
v_i_1193_ = v___x_1211_;
v_bs_1194_ = v___x_1212_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoal_fromJson_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_1214_, lean_object* v_i_1215_, lean_object* v_bs_1216_){
_start:
{
size_t v_sz_boxed_1217_; size_t v_i_boxed_1218_; lean_object* v_res_1219_; 
v_sz_boxed_1217_ = lean_unbox_usize(v_sz_1214_);
lean_dec(v_sz_1214_);
v_i_boxed_1218_ = lean_unbox_usize(v_i_1215_);
lean_dec(v_i_1215_);
v_res_1219_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoal_fromJson_spec__0_spec__0_spec__1(v_sz_boxed_1217_, v_i_boxed_1218_, v_bs_1216_);
return v_res_1219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoal_fromJson_spec__0_spec__0(lean_object* v_x_1220_){
_start:
{
if (lean_obj_tag(v_x_1220_) == 4)
{
lean_object* v_elems_1221_; size_t v_sz_1222_; size_t v___x_1223_; lean_object* v___x_1224_; 
v_elems_1221_ = lean_ctor_get(v_x_1220_, 0);
lean_inc_ref(v_elems_1221_);
lean_dec_ref_known(v_x_1220_, 1);
v_sz_1222_ = lean_array_size(v_elems_1221_);
v___x_1223_ = ((size_t)0ULL);
v___x_1224_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoal_fromJson_spec__0_spec__0_spec__1(v_sz_1222_, v___x_1223_, v_elems_1221_);
return v___x_1224_;
}
else
{
lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; 
v___x_1225_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__1_spec__1___closed__0));
v___x_1226_ = lean_unsigned_to_nat(80u);
v___x_1227_ = l_Lean_Json_pretty(v_x_1220_, v___x_1226_);
v___x_1228_ = lean_string_append(v___x_1225_, v___x_1227_);
lean_dec_ref(v___x_1227_);
v___x_1229_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressKind___lam__0___closed__1));
v___x_1230_ = lean_string_append(v___x_1228_, v___x_1229_);
v___x_1231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1231_, 0, v___x_1230_);
return v___x_1231_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoal_fromJson_spec__0(lean_object* v_j_1232_, lean_object* v_k_1233_){
_start:
{
lean_object* v___x_1234_; lean_object* v___x_1235_; 
v___x_1234_ = l_Lean_Json_getObjValD(v_j_1232_, v_k_1233_);
v___x_1235_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoal_fromJson_spec__0_spec__0(v___x_1234_);
return v___x_1235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoal_fromJson_spec__0___boxed(lean_object* v_j_1236_, lean_object* v_k_1237_){
_start:
{
lean_object* v_res_1238_; 
v_res_1238_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoal_fromJson_spec__0(v_j_1236_, v_k_1237_);
lean_dec_ref(v_k_1237_);
return v_res_1238_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__3(void){
_start:
{
uint8_t v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; 
v___x_1245_ = 1;
v___x_1246_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__2));
v___x_1247_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1246_, v___x_1245_);
return v___x_1247_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__4(void){
_start:
{
lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; 
v___x_1248_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6));
v___x_1249_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__3, &l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__3);
v___x_1250_ = lean_string_append(v___x_1249_, v___x_1248_);
return v___x_1250_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__6(void){
_start:
{
uint8_t v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; 
v___x_1253_ = 1;
v___x_1254_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__5));
v___x_1255_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1254_, v___x_1253_);
return v___x_1255_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__7(void){
_start:
{
lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; 
v___x_1256_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__6, &l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__6);
v___x_1257_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__4, &l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__4);
v___x_1258_ = lean_string_append(v___x_1257_, v___x_1256_);
return v___x_1258_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__8(void){
_start:
{
lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; 
v___x_1259_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_1260_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__7, &l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__7);
v___x_1261_ = lean_string_append(v___x_1260_, v___x_1259_);
return v___x_1261_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__11(void){
_start:
{
uint8_t v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; 
v___x_1265_ = 1;
v___x_1266_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__10));
v___x_1267_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1266_, v___x_1265_);
return v___x_1267_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__12(void){
_start:
{
lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; 
v___x_1268_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__11, &l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__11);
v___x_1269_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__4, &l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__4);
v___x_1270_ = lean_string_append(v___x_1269_, v___x_1268_);
return v___x_1270_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__13(void){
_start:
{
lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; 
v___x_1271_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_1272_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__12, &l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__12);
v___x_1273_ = lean_string_append(v___x_1272_, v___x_1271_);
return v___x_1273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonPlainGoal_fromJson(lean_object* v_json_1274_){
_start:
{
lean_object* v___x_1275_; lean_object* v___x_1276_; 
v___x_1275_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__0));
lean_inc(v_json_1274_);
v___x_1276_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson_spec__0(v_json_1274_, v___x_1275_);
if (lean_obj_tag(v___x_1276_) == 0)
{
lean_object* v_a_1277_; lean_object* v___x_1279_; uint8_t v_isShared_1280_; uint8_t v_isSharedCheck_1286_; 
lean_dec(v_json_1274_);
v_a_1277_ = lean_ctor_get(v___x_1276_, 0);
v_isSharedCheck_1286_ = !lean_is_exclusive(v___x_1276_);
if (v_isSharedCheck_1286_ == 0)
{
v___x_1279_ = v___x_1276_;
v_isShared_1280_ = v_isSharedCheck_1286_;
goto v_resetjp_1278_;
}
else
{
lean_inc(v_a_1277_);
lean_dec(v___x_1276_);
v___x_1279_ = lean_box(0);
v_isShared_1280_ = v_isSharedCheck_1286_;
goto v_resetjp_1278_;
}
v_resetjp_1278_:
{
lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1284_; 
v___x_1281_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__8, &l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__8);
v___x_1282_ = lean_string_append(v___x_1281_, v_a_1277_);
lean_dec(v_a_1277_);
if (v_isShared_1280_ == 0)
{
lean_ctor_set(v___x_1279_, 0, v___x_1282_);
v___x_1284_ = v___x_1279_;
goto v_reusejp_1283_;
}
else
{
lean_object* v_reuseFailAlloc_1285_; 
v_reuseFailAlloc_1285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1285_, 0, v___x_1282_);
v___x_1284_ = v_reuseFailAlloc_1285_;
goto v_reusejp_1283_;
}
v_reusejp_1283_:
{
return v___x_1284_;
}
}
}
else
{
if (lean_obj_tag(v___x_1276_) == 0)
{
lean_object* v_a_1287_; lean_object* v___x_1289_; uint8_t v_isShared_1290_; uint8_t v_isSharedCheck_1294_; 
lean_dec(v_json_1274_);
v_a_1287_ = lean_ctor_get(v___x_1276_, 0);
v_isSharedCheck_1294_ = !lean_is_exclusive(v___x_1276_);
if (v_isSharedCheck_1294_ == 0)
{
v___x_1289_ = v___x_1276_;
v_isShared_1290_ = v_isSharedCheck_1294_;
goto v_resetjp_1288_;
}
else
{
lean_inc(v_a_1287_);
lean_dec(v___x_1276_);
v___x_1289_ = lean_box(0);
v_isShared_1290_ = v_isSharedCheck_1294_;
goto v_resetjp_1288_;
}
v_resetjp_1288_:
{
lean_object* v___x_1292_; 
if (v_isShared_1290_ == 0)
{
lean_ctor_set_tag(v___x_1289_, 0);
v___x_1292_ = v___x_1289_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v_a_1287_);
v___x_1292_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
return v___x_1292_;
}
}
}
else
{
lean_object* v_a_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; 
v_a_1295_ = lean_ctor_get(v___x_1276_, 0);
lean_inc(v_a_1295_);
lean_dec_ref_known(v___x_1276_, 1);
v___x_1296_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__9));
v___x_1297_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoal_fromJson_spec__0(v_json_1274_, v___x_1296_);
if (lean_obj_tag(v___x_1297_) == 0)
{
lean_object* v_a_1298_; lean_object* v___x_1300_; uint8_t v_isShared_1301_; uint8_t v_isSharedCheck_1307_; 
lean_dec(v_a_1295_);
v_a_1298_ = lean_ctor_get(v___x_1297_, 0);
v_isSharedCheck_1307_ = !lean_is_exclusive(v___x_1297_);
if (v_isSharedCheck_1307_ == 0)
{
v___x_1300_ = v___x_1297_;
v_isShared_1301_ = v_isSharedCheck_1307_;
goto v_resetjp_1299_;
}
else
{
lean_inc(v_a_1298_);
lean_dec(v___x_1297_);
v___x_1300_ = lean_box(0);
v_isShared_1301_ = v_isSharedCheck_1307_;
goto v_resetjp_1299_;
}
v_resetjp_1299_:
{
lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1305_; 
v___x_1302_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__13, &l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__13);
v___x_1303_ = lean_string_append(v___x_1302_, v_a_1298_);
lean_dec(v_a_1298_);
if (v_isShared_1301_ == 0)
{
lean_ctor_set(v___x_1300_, 0, v___x_1303_);
v___x_1305_ = v___x_1300_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1306_; 
v_reuseFailAlloc_1306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1306_, 0, v___x_1303_);
v___x_1305_ = v_reuseFailAlloc_1306_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
return v___x_1305_;
}
}
}
else
{
if (lean_obj_tag(v___x_1297_) == 0)
{
lean_object* v_a_1308_; lean_object* v___x_1310_; uint8_t v_isShared_1311_; uint8_t v_isSharedCheck_1315_; 
lean_dec(v_a_1295_);
v_a_1308_ = lean_ctor_get(v___x_1297_, 0);
v_isSharedCheck_1315_ = !lean_is_exclusive(v___x_1297_);
if (v_isSharedCheck_1315_ == 0)
{
v___x_1310_ = v___x_1297_;
v_isShared_1311_ = v_isSharedCheck_1315_;
goto v_resetjp_1309_;
}
else
{
lean_inc(v_a_1308_);
lean_dec(v___x_1297_);
v___x_1310_ = lean_box(0);
v_isShared_1311_ = v_isSharedCheck_1315_;
goto v_resetjp_1309_;
}
v_resetjp_1309_:
{
lean_object* v___x_1313_; 
if (v_isShared_1311_ == 0)
{
lean_ctor_set_tag(v___x_1310_, 0);
v___x_1313_ = v___x_1310_;
goto v_reusejp_1312_;
}
else
{
lean_object* v_reuseFailAlloc_1314_; 
v_reuseFailAlloc_1314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1314_, 0, v_a_1308_);
v___x_1313_ = v_reuseFailAlloc_1314_;
goto v_reusejp_1312_;
}
v_reusejp_1312_:
{
return v___x_1313_;
}
}
}
else
{
lean_object* v_a_1316_; lean_object* v___x_1318_; uint8_t v_isShared_1319_; uint8_t v_isSharedCheck_1324_; 
v_a_1316_ = lean_ctor_get(v___x_1297_, 0);
v_isSharedCheck_1324_ = !lean_is_exclusive(v___x_1297_);
if (v_isSharedCheck_1324_ == 0)
{
v___x_1318_ = v___x_1297_;
v_isShared_1319_ = v_isSharedCheck_1324_;
goto v_resetjp_1317_;
}
else
{
lean_inc(v_a_1316_);
lean_dec(v___x_1297_);
v___x_1318_ = lean_box(0);
v_isShared_1319_ = v_isSharedCheck_1324_;
goto v_resetjp_1317_;
}
v_resetjp_1317_:
{
lean_object* v___x_1320_; lean_object* v___x_1322_; 
v___x_1320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1320_, 0, v_a_1295_);
lean_ctor_set(v___x_1320_, 1, v_a_1316_);
if (v_isShared_1319_ == 0)
{
lean_ctor_set(v___x_1318_, 0, v___x_1320_);
v___x_1322_ = v___x_1318_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v___x_1320_);
v___x_1322_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
return v___x_1322_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPlainGoal_toJson_spec__0_spec__0(size_t v_sz_1327_, size_t v_i_1328_, lean_object* v_bs_1329_){
_start:
{
uint8_t v___x_1330_; 
v___x_1330_ = lean_usize_dec_lt(v_i_1328_, v_sz_1327_);
if (v___x_1330_ == 0)
{
return v_bs_1329_;
}
else
{
lean_object* v_v_1331_; lean_object* v___x_1332_; lean_object* v_bs_x27_1333_; lean_object* v___x_1334_; size_t v___x_1335_; size_t v___x_1336_; lean_object* v___x_1337_; 
v_v_1331_ = lean_array_uget(v_bs_1329_, v_i_1328_);
v___x_1332_ = lean_unsigned_to_nat(0u);
v_bs_x27_1333_ = lean_array_uset(v_bs_1329_, v_i_1328_, v___x_1332_);
v___x_1334_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1334_, 0, v_v_1331_);
v___x_1335_ = ((size_t)1ULL);
v___x_1336_ = lean_usize_add(v_i_1328_, v___x_1335_);
v___x_1337_ = lean_array_uset(v_bs_x27_1333_, v_i_1328_, v___x_1334_);
v_i_1328_ = v___x_1336_;
v_bs_1329_ = v___x_1337_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPlainGoal_toJson_spec__0_spec__0___boxed(lean_object* v_sz_1339_, lean_object* v_i_1340_, lean_object* v_bs_1341_){
_start:
{
size_t v_sz_boxed_1342_; size_t v_i_boxed_1343_; lean_object* v_res_1344_; 
v_sz_boxed_1342_ = lean_unbox_usize(v_sz_1339_);
lean_dec(v_sz_1339_);
v_i_boxed_1343_ = lean_unbox_usize(v_i_1340_);
lean_dec(v_i_1340_);
v_res_1344_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPlainGoal_toJson_spec__0_spec__0(v_sz_boxed_1342_, v_i_boxed_1343_, v_bs_1341_);
return v_res_1344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonPlainGoal_toJson_spec__0(lean_object* v_a_1345_){
_start:
{
size_t v_sz_1346_; size_t v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; 
v_sz_1346_ = lean_array_size(v_a_1345_);
v___x_1347_ = ((size_t)0ULL);
v___x_1348_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPlainGoal_toJson_spec__0_spec__0(v_sz_1346_, v___x_1347_, v_a_1345_);
v___x_1349_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1349_, 0, v___x_1348_);
return v___x_1349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonPlainGoal_toJson(lean_object* v_x_1350_){
_start:
{
lean_object* v_rendered_1351_; lean_object* v_goals_1352_; lean_object* v___x_1354_; uint8_t v_isShared_1355_; uint8_t v_isSharedCheck_1372_; 
v_rendered_1351_ = lean_ctor_get(v_x_1350_, 0);
v_goals_1352_ = lean_ctor_get(v_x_1350_, 1);
v_isSharedCheck_1372_ = !lean_is_exclusive(v_x_1350_);
if (v_isSharedCheck_1372_ == 0)
{
v___x_1354_ = v_x_1350_;
v_isShared_1355_ = v_isSharedCheck_1372_;
goto v_resetjp_1353_;
}
else
{
lean_inc(v_goals_1352_);
lean_inc(v_rendered_1351_);
lean_dec(v_x_1350_);
v___x_1354_ = lean_box(0);
v_isShared_1355_ = v_isSharedCheck_1372_;
goto v_resetjp_1353_;
}
v_resetjp_1353_:
{
lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1359_; 
v___x_1356_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__0));
v___x_1357_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1357_, 0, v_rendered_1351_);
if (v_isShared_1355_ == 0)
{
lean_ctor_set(v___x_1354_, 1, v___x_1357_);
lean_ctor_set(v___x_1354_, 0, v___x_1356_);
v___x_1359_ = v___x_1354_;
goto v_reusejp_1358_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v___x_1356_);
lean_ctor_set(v_reuseFailAlloc_1371_, 1, v___x_1357_);
v___x_1359_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1358_;
}
v_reusejp_1358_:
{
lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; 
v___x_1360_ = lean_box(0);
v___x_1361_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1361_, 0, v___x_1359_);
lean_ctor_set(v___x_1361_, 1, v___x_1360_);
v___x_1362_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__9));
v___x_1363_ = l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonPlainGoal_toJson_spec__0(v_goals_1352_);
v___x_1364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1364_, 0, v___x_1362_);
lean_ctor_set(v___x_1364_, 1, v___x_1363_);
v___x_1365_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1365_, 0, v___x_1364_);
lean_ctor_set(v___x_1365_, 1, v___x_1360_);
v___x_1366_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1366_, 0, v___x_1365_);
lean_ctor_set(v___x_1366_, 1, v___x_1360_);
v___x_1367_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1367_, 0, v___x_1361_);
lean_ctor_set(v___x_1367_, 1, v___x_1366_);
v___x_1368_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0));
v___x_1369_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_1367_, v___x_1368_);
v___x_1370_ = l_Lean_Json_mkObj(v___x_1369_);
lean_dec(v___x_1369_);
return v___x_1370_;
}
}
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__2(void){
_start:
{
uint8_t v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; 
v___x_1380_ = 1;
v___x_1381_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__1));
v___x_1382_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1381_, v___x_1380_);
return v___x_1382_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__3(void){
_start:
{
lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; 
v___x_1383_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6));
v___x_1384_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__2, &l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__2);
v___x_1385_ = lean_string_append(v___x_1384_, v___x_1383_);
return v___x_1385_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; 
v___x_1386_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9, &l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9);
v___x_1387_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__3);
v___x_1388_ = lean_string_append(v___x_1387_, v___x_1386_);
return v___x_1388_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__5(void){
_start:
{
lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; 
v___x_1389_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_1390_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__4);
v___x_1391_ = lean_string_append(v___x_1390_, v___x_1389_);
return v___x_1391_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__6(void){
_start:
{
lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; 
v___x_1392_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__8);
v___x_1393_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__3);
v___x_1394_ = lean_string_append(v___x_1393_, v___x_1392_);
return v___x_1394_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__7(void){
_start:
{
lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; 
v___x_1395_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_1396_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__6, &l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__6);
v___x_1397_ = lean_string_append(v___x_1396_, v___x_1395_);
return v___x_1397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson(lean_object* v_json_1398_){
_start:
{
lean_object* v___x_1399_; lean_object* v___x_1400_; 
v___x_1399_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__0));
lean_inc(v_json_1398_);
v___x_1400_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoalParams_fromJson_spec__0(v_json_1398_, v___x_1399_);
if (lean_obj_tag(v___x_1400_) == 0)
{
lean_object* v_a_1401_; lean_object* v___x_1403_; uint8_t v_isShared_1404_; uint8_t v_isSharedCheck_1410_; 
lean_dec(v_json_1398_);
v_a_1401_ = lean_ctor_get(v___x_1400_, 0);
v_isSharedCheck_1410_ = !lean_is_exclusive(v___x_1400_);
if (v_isSharedCheck_1410_ == 0)
{
v___x_1403_ = v___x_1400_;
v_isShared_1404_ = v_isSharedCheck_1410_;
goto v_resetjp_1402_;
}
else
{
lean_inc(v_a_1401_);
lean_dec(v___x_1400_);
v___x_1403_ = lean_box(0);
v_isShared_1404_ = v_isSharedCheck_1410_;
goto v_resetjp_1402_;
}
v_resetjp_1402_:
{
lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1408_; 
v___x_1405_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__5, &l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__5);
v___x_1406_ = lean_string_append(v___x_1405_, v_a_1401_);
lean_dec(v_a_1401_);
if (v_isShared_1404_ == 0)
{
lean_ctor_set(v___x_1403_, 0, v___x_1406_);
v___x_1408_ = v___x_1403_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1409_; 
v_reuseFailAlloc_1409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1409_, 0, v___x_1406_);
v___x_1408_ = v_reuseFailAlloc_1409_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
return v___x_1408_;
}
}
}
else
{
if (lean_obj_tag(v___x_1400_) == 0)
{
lean_object* v_a_1411_; lean_object* v___x_1413_; uint8_t v_isShared_1414_; uint8_t v_isSharedCheck_1418_; 
lean_dec(v_json_1398_);
v_a_1411_ = lean_ctor_get(v___x_1400_, 0);
v_isSharedCheck_1418_ = !lean_is_exclusive(v___x_1400_);
if (v_isSharedCheck_1418_ == 0)
{
v___x_1413_ = v___x_1400_;
v_isShared_1414_ = v_isSharedCheck_1418_;
goto v_resetjp_1412_;
}
else
{
lean_inc(v_a_1411_);
lean_dec(v___x_1400_);
v___x_1413_ = lean_box(0);
v_isShared_1414_ = v_isSharedCheck_1418_;
goto v_resetjp_1412_;
}
v_resetjp_1412_:
{
lean_object* v___x_1416_; 
if (v_isShared_1414_ == 0)
{
lean_ctor_set_tag(v___x_1413_, 0);
v___x_1416_ = v___x_1413_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v_a_1411_);
v___x_1416_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1415_;
}
v_reusejp_1415_:
{
return v___x_1416_;
}
}
}
else
{
lean_object* v_a_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; 
v_a_1419_ = lean_ctor_get(v___x_1400_, 0);
lean_inc(v_a_1419_);
lean_dec_ref_known(v___x_1400_, 1);
v___x_1420_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__6));
v___x_1421_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoalParams_fromJson_spec__1(v_json_1398_, v___x_1420_);
if (lean_obj_tag(v___x_1421_) == 0)
{
lean_object* v_a_1422_; lean_object* v___x_1424_; uint8_t v_isShared_1425_; uint8_t v_isSharedCheck_1431_; 
lean_dec(v_a_1419_);
v_a_1422_ = lean_ctor_get(v___x_1421_, 0);
v_isSharedCheck_1431_ = !lean_is_exclusive(v___x_1421_);
if (v_isSharedCheck_1431_ == 0)
{
v___x_1424_ = v___x_1421_;
v_isShared_1425_ = v_isSharedCheck_1431_;
goto v_resetjp_1423_;
}
else
{
lean_inc(v_a_1422_);
lean_dec(v___x_1421_);
v___x_1424_ = lean_box(0);
v_isShared_1425_ = v_isSharedCheck_1431_;
goto v_resetjp_1423_;
}
v_resetjp_1423_:
{
lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1429_; 
v___x_1426_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__7);
v___x_1427_ = lean_string_append(v___x_1426_, v_a_1422_);
lean_dec(v_a_1422_);
if (v_isShared_1425_ == 0)
{
lean_ctor_set(v___x_1424_, 0, v___x_1427_);
v___x_1429_ = v___x_1424_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1430_; 
v_reuseFailAlloc_1430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1430_, 0, v___x_1427_);
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
if (lean_obj_tag(v___x_1421_) == 0)
{
lean_object* v_a_1432_; lean_object* v___x_1434_; uint8_t v_isShared_1435_; uint8_t v_isSharedCheck_1439_; 
lean_dec(v_a_1419_);
v_a_1432_ = lean_ctor_get(v___x_1421_, 0);
v_isSharedCheck_1439_ = !lean_is_exclusive(v___x_1421_);
if (v_isSharedCheck_1439_ == 0)
{
v___x_1434_ = v___x_1421_;
v_isShared_1435_ = v_isSharedCheck_1439_;
goto v_resetjp_1433_;
}
else
{
lean_inc(v_a_1432_);
lean_dec(v___x_1421_);
v___x_1434_ = lean_box(0);
v_isShared_1435_ = v_isSharedCheck_1439_;
goto v_resetjp_1433_;
}
v_resetjp_1433_:
{
lean_object* v___x_1437_; 
if (v_isShared_1435_ == 0)
{
lean_ctor_set_tag(v___x_1434_, 0);
v___x_1437_ = v___x_1434_;
goto v_reusejp_1436_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v_a_1432_);
v___x_1437_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1436_;
}
v_reusejp_1436_:
{
return v___x_1437_;
}
}
}
else
{
lean_object* v_a_1440_; lean_object* v___x_1442_; uint8_t v_isShared_1443_; uint8_t v_isSharedCheck_1448_; 
v_a_1440_ = lean_ctor_get(v___x_1421_, 0);
v_isSharedCheck_1448_ = !lean_is_exclusive(v___x_1421_);
if (v_isSharedCheck_1448_ == 0)
{
v___x_1442_ = v___x_1421_;
v_isShared_1443_ = v_isSharedCheck_1448_;
goto v_resetjp_1441_;
}
else
{
lean_inc(v_a_1440_);
lean_dec(v___x_1421_);
v___x_1442_ = lean_box(0);
v_isShared_1443_ = v_isSharedCheck_1448_;
goto v_resetjp_1441_;
}
v_resetjp_1441_:
{
lean_object* v___x_1444_; lean_object* v___x_1446_; 
v___x_1444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1444_, 0, v_a_1419_);
lean_ctor_set(v___x_1444_, 1, v_a_1440_);
if (v_isShared_1443_ == 0)
{
lean_ctor_set(v___x_1442_, 0, v___x_1444_);
v___x_1446_ = v___x_1442_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v___x_1444_);
v___x_1446_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
return v___x_1446_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonPlainTermGoalParams_toJson(lean_object* v_x_1451_){
_start:
{
lean_object* v_textDocument_1452_; lean_object* v_position_1453_; lean_object* v___x_1455_; uint8_t v_isShared_1456_; uint8_t v_isSharedCheck_1473_; 
v_textDocument_1452_ = lean_ctor_get(v_x_1451_, 0);
v_position_1453_ = lean_ctor_get(v_x_1451_, 1);
v_isSharedCheck_1473_ = !lean_is_exclusive(v_x_1451_);
if (v_isSharedCheck_1473_ == 0)
{
v___x_1455_ = v_x_1451_;
v_isShared_1456_ = v_isSharedCheck_1473_;
goto v_resetjp_1454_;
}
else
{
lean_inc(v_position_1453_);
lean_inc(v_textDocument_1452_);
lean_dec(v_x_1451_);
v___x_1455_ = lean_box(0);
v_isShared_1456_ = v_isSharedCheck_1473_;
goto v_resetjp_1454_;
}
v_resetjp_1454_:
{
lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1460_; 
v___x_1457_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__0));
v___x_1458_ = l_Lean_Lsp_instToJsonTextDocumentIdentifier_toJson(v_textDocument_1452_);
if (v_isShared_1456_ == 0)
{
lean_ctor_set(v___x_1455_, 1, v___x_1458_);
lean_ctor_set(v___x_1455_, 0, v___x_1457_);
v___x_1460_ = v___x_1455_;
goto v_reusejp_1459_;
}
else
{
lean_object* v_reuseFailAlloc_1472_; 
v_reuseFailAlloc_1472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1472_, 0, v___x_1457_);
lean_ctor_set(v_reuseFailAlloc_1472_, 1, v___x_1458_);
v___x_1460_ = v_reuseFailAlloc_1472_;
goto v_reusejp_1459_;
}
v_reusejp_1459_:
{
lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; 
v___x_1461_ = lean_box(0);
v___x_1462_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1462_, 0, v___x_1460_);
lean_ctor_set(v___x_1462_, 1, v___x_1461_);
v___x_1463_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__6));
v___x_1464_ = l_Lean_Lsp_instToJsonPosition_toJson(v_position_1453_);
v___x_1465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1465_, 0, v___x_1463_);
lean_ctor_set(v___x_1465_, 1, v___x_1464_);
v___x_1466_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1466_, 0, v___x_1465_);
lean_ctor_set(v___x_1466_, 1, v___x_1461_);
v___x_1467_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1467_, 0, v___x_1466_);
lean_ctor_set(v___x_1467_, 1, v___x_1461_);
v___x_1468_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1468_, 0, v___x_1462_);
lean_ctor_set(v___x_1468_, 1, v___x_1467_);
v___x_1469_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0));
v___x_1470_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_1468_, v___x_1469_);
v___x_1471_ = l_Lean_Json_mkObj(v___x_1470_);
lean_dec(v___x_1470_);
return v___x_1471_;
}
}
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__3(void){
_start:
{
uint8_t v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; 
v___x_1482_ = 1;
v___x_1483_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__2));
v___x_1484_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1483_, v___x_1482_);
return v___x_1484_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__4(void){
_start:
{
lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; 
v___x_1485_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6));
v___x_1486_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__3, &l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__3);
v___x_1487_ = lean_string_append(v___x_1486_, v___x_1485_);
return v___x_1487_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__6(void){
_start:
{
uint8_t v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; 
v___x_1490_ = 1;
v___x_1491_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__5));
v___x_1492_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1491_, v___x_1490_);
return v___x_1492_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__7(void){
_start:
{
lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; 
v___x_1493_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__6, &l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__6);
v___x_1494_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__4, &l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__4);
v___x_1495_ = lean_string_append(v___x_1494_, v___x_1493_);
return v___x_1495_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__8(void){
_start:
{
lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; 
v___x_1496_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_1497_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__7, &l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__7);
v___x_1498_ = lean_string_append(v___x_1497_, v___x_1496_);
return v___x_1498_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__9(void){
_start:
{
lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; 
v___x_1499_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__6);
v___x_1500_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__4, &l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__4);
v___x_1501_ = lean_string_append(v___x_1500_, v___x_1499_);
return v___x_1501_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__10(void){
_start:
{
lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; 
v___x_1502_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_1503_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__9, &l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__9);
v___x_1504_ = lean_string_append(v___x_1503_, v___x_1502_);
return v___x_1504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson(lean_object* v_json_1505_){
_start:
{
lean_object* v___x_1506_; lean_object* v___x_1507_; 
v___x_1506_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__0));
lean_inc(v_json_1505_);
v___x_1507_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson_spec__0(v_json_1505_, v___x_1506_);
if (lean_obj_tag(v___x_1507_) == 0)
{
lean_object* v_a_1508_; lean_object* v___x_1510_; uint8_t v_isShared_1511_; uint8_t v_isSharedCheck_1517_; 
lean_dec(v_json_1505_);
v_a_1508_ = lean_ctor_get(v___x_1507_, 0);
v_isSharedCheck_1517_ = !lean_is_exclusive(v___x_1507_);
if (v_isSharedCheck_1517_ == 0)
{
v___x_1510_ = v___x_1507_;
v_isShared_1511_ = v_isSharedCheck_1517_;
goto v_resetjp_1509_;
}
else
{
lean_inc(v_a_1508_);
lean_dec(v___x_1507_);
v___x_1510_ = lean_box(0);
v_isShared_1511_ = v_isSharedCheck_1517_;
goto v_resetjp_1509_;
}
v_resetjp_1509_:
{
lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1515_; 
v___x_1512_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__8, &l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__8);
v___x_1513_ = lean_string_append(v___x_1512_, v_a_1508_);
lean_dec(v_a_1508_);
if (v_isShared_1511_ == 0)
{
lean_ctor_set(v___x_1510_, 0, v___x_1513_);
v___x_1515_ = v___x_1510_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v___x_1513_);
v___x_1515_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
return v___x_1515_;
}
}
}
else
{
if (lean_obj_tag(v___x_1507_) == 0)
{
lean_object* v_a_1518_; lean_object* v___x_1520_; uint8_t v_isShared_1521_; uint8_t v_isSharedCheck_1525_; 
lean_dec(v_json_1505_);
v_a_1518_ = lean_ctor_get(v___x_1507_, 0);
v_isSharedCheck_1525_ = !lean_is_exclusive(v___x_1507_);
if (v_isSharedCheck_1525_ == 0)
{
v___x_1520_ = v___x_1507_;
v_isShared_1521_ = v_isSharedCheck_1525_;
goto v_resetjp_1519_;
}
else
{
lean_inc(v_a_1518_);
lean_dec(v___x_1507_);
v___x_1520_ = lean_box(0);
v_isShared_1521_ = v_isSharedCheck_1525_;
goto v_resetjp_1519_;
}
v_resetjp_1519_:
{
lean_object* v___x_1523_; 
if (v_isShared_1521_ == 0)
{
lean_ctor_set_tag(v___x_1520_, 0);
v___x_1523_ = v___x_1520_;
goto v_reusejp_1522_;
}
else
{
lean_object* v_reuseFailAlloc_1524_; 
v_reuseFailAlloc_1524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1524_, 0, v_a_1518_);
v___x_1523_ = v_reuseFailAlloc_1524_;
goto v_reusejp_1522_;
}
v_reusejp_1522_:
{
return v___x_1523_;
}
}
}
else
{
lean_object* v_a_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; 
v_a_1526_ = lean_ctor_get(v___x_1507_, 0);
lean_inc(v_a_1526_);
lean_dec_ref_known(v___x_1507_, 1);
v___x_1527_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__0));
v___x_1528_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson_spec__0(v_json_1505_, v___x_1527_);
if (lean_obj_tag(v___x_1528_) == 0)
{
lean_object* v_a_1529_; lean_object* v___x_1531_; uint8_t v_isShared_1532_; uint8_t v_isSharedCheck_1538_; 
lean_dec(v_a_1526_);
v_a_1529_ = lean_ctor_get(v___x_1528_, 0);
v_isSharedCheck_1538_ = !lean_is_exclusive(v___x_1528_);
if (v_isSharedCheck_1538_ == 0)
{
v___x_1531_ = v___x_1528_;
v_isShared_1532_ = v_isSharedCheck_1538_;
goto v_resetjp_1530_;
}
else
{
lean_inc(v_a_1529_);
lean_dec(v___x_1528_);
v___x_1531_ = lean_box(0);
v_isShared_1532_ = v_isSharedCheck_1538_;
goto v_resetjp_1530_;
}
v_resetjp_1530_:
{
lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1536_; 
v___x_1533_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__10, &l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__10);
v___x_1534_ = lean_string_append(v___x_1533_, v_a_1529_);
lean_dec(v_a_1529_);
if (v_isShared_1532_ == 0)
{
lean_ctor_set(v___x_1531_, 0, v___x_1534_);
v___x_1536_ = v___x_1531_;
goto v_reusejp_1535_;
}
else
{
lean_object* v_reuseFailAlloc_1537_; 
v_reuseFailAlloc_1537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1537_, 0, v___x_1534_);
v___x_1536_ = v_reuseFailAlloc_1537_;
goto v_reusejp_1535_;
}
v_reusejp_1535_:
{
return v___x_1536_;
}
}
}
else
{
if (lean_obj_tag(v___x_1528_) == 0)
{
lean_object* v_a_1539_; lean_object* v___x_1541_; uint8_t v_isShared_1542_; uint8_t v_isSharedCheck_1546_; 
lean_dec(v_a_1526_);
v_a_1539_ = lean_ctor_get(v___x_1528_, 0);
v_isSharedCheck_1546_ = !lean_is_exclusive(v___x_1528_);
if (v_isSharedCheck_1546_ == 0)
{
v___x_1541_ = v___x_1528_;
v_isShared_1542_ = v_isSharedCheck_1546_;
goto v_resetjp_1540_;
}
else
{
lean_inc(v_a_1539_);
lean_dec(v___x_1528_);
v___x_1541_ = lean_box(0);
v_isShared_1542_ = v_isSharedCheck_1546_;
goto v_resetjp_1540_;
}
v_resetjp_1540_:
{
lean_object* v___x_1544_; 
if (v_isShared_1542_ == 0)
{
lean_ctor_set_tag(v___x_1541_, 0);
v___x_1544_ = v___x_1541_;
goto v_reusejp_1543_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v_a_1539_);
v___x_1544_ = v_reuseFailAlloc_1545_;
goto v_reusejp_1543_;
}
v_reusejp_1543_:
{
return v___x_1544_;
}
}
}
else
{
lean_object* v_a_1547_; lean_object* v___x_1549_; uint8_t v_isShared_1550_; uint8_t v_isSharedCheck_1555_; 
v_a_1547_ = lean_ctor_get(v___x_1528_, 0);
v_isSharedCheck_1555_ = !lean_is_exclusive(v___x_1528_);
if (v_isSharedCheck_1555_ == 0)
{
v___x_1549_ = v___x_1528_;
v_isShared_1550_ = v_isSharedCheck_1555_;
goto v_resetjp_1548_;
}
else
{
lean_inc(v_a_1547_);
lean_dec(v___x_1528_);
v___x_1549_ = lean_box(0);
v_isShared_1550_ = v_isSharedCheck_1555_;
goto v_resetjp_1548_;
}
v_resetjp_1548_:
{
lean_object* v___x_1551_; lean_object* v___x_1553_; 
v___x_1551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1551_, 0, v_a_1526_);
lean_ctor_set(v___x_1551_, 1, v_a_1547_);
if (v_isShared_1550_ == 0)
{
lean_ctor_set(v___x_1549_, 0, v___x_1551_);
v___x_1553_ = v___x_1549_;
goto v_reusejp_1552_;
}
else
{
lean_object* v_reuseFailAlloc_1554_; 
v_reuseFailAlloc_1554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1554_, 0, v___x_1551_);
v___x_1553_ = v_reuseFailAlloc_1554_;
goto v_reusejp_1552_;
}
v_reusejp_1552_:
{
return v___x_1553_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonPlainTermGoal_toJson(lean_object* v_x_1558_){
_start:
{
lean_object* v_goal_1559_; lean_object* v_range_1560_; lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1580_; 
v_goal_1559_ = lean_ctor_get(v_x_1558_, 0);
v_range_1560_ = lean_ctor_get(v_x_1558_, 1);
v_isSharedCheck_1580_ = !lean_is_exclusive(v_x_1558_);
if (v_isSharedCheck_1580_ == 0)
{
v___x_1562_ = v_x_1558_;
v_isShared_1563_ = v_isSharedCheck_1580_;
goto v_resetjp_1561_;
}
else
{
lean_inc(v_range_1560_);
lean_inc(v_goal_1559_);
lean_dec(v_x_1558_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1580_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1567_; 
v___x_1564_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__0));
v___x_1565_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1565_, 0, v_goal_1559_);
if (v_isShared_1563_ == 0)
{
lean_ctor_set(v___x_1562_, 1, v___x_1565_);
lean_ctor_set(v___x_1562_, 0, v___x_1564_);
v___x_1567_ = v___x_1562_;
goto v_reusejp_1566_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v___x_1564_);
lean_ctor_set(v_reuseFailAlloc_1579_, 1, v___x_1565_);
v___x_1567_ = v_reuseFailAlloc_1579_;
goto v_reusejp_1566_;
}
v_reusejp_1566_:
{
lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; 
v___x_1568_ = lean_box(0);
v___x_1569_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1569_, 0, v___x_1567_);
lean_ctor_set(v___x_1569_, 1, v___x_1568_);
v___x_1570_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__0));
v___x_1571_ = l_Lean_Lsp_instToJsonRange_toJson(v_range_1560_);
v___x_1572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1572_, 0, v___x_1570_);
lean_ctor_set(v___x_1572_, 1, v___x_1571_);
v___x_1573_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1573_, 0, v___x_1572_);
lean_ctor_set(v___x_1573_, 1, v___x_1568_);
v___x_1574_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1574_, 0, v___x_1573_);
lean_ctor_set(v___x_1574_, 1, v___x_1568_);
v___x_1575_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1575_, 0, v___x_1569_);
lean_ctor_set(v___x_1575_, 1, v___x_1574_);
v___x_1576_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0));
v___x_1577_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_1575_, v___x_1576_);
v___x_1578_ = l_Lean_Json_mkObj(v___x_1577_);
lean_dec(v___x_1577_);
return v___x_1578_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonModuleHierarchyOptions_fromJson(lean_object* v_json_1585_){
_start:
{
lean_object* v___x_1586_; 
v___x_1586_ = ((lean_object*)(l_Lean_Lsp_instFromJsonModuleHierarchyOptions_fromJson___closed__0));
return v___x_1586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonModuleHierarchyOptions_fromJson___boxed(lean_object* v_json_1587_){
_start:
{
lean_object* v_res_1588_; 
v_res_1588_ = l_Lean_Lsp_instFromJsonModuleHierarchyOptions_fromJson(v_json_1587_);
lean_dec(v_json_1587_);
return v_res_1588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonModuleHierarchyOptions_toJson(lean_object* v_x_1591_){
_start:
{
lean_object* v___x_1592_; 
v___x_1592_ = lean_obj_once(&l_Lean_Lsp_instToJsonWaitForILeans_toJson___closed__1, &l_Lean_Lsp_instToJsonWaitForILeans_toJson___closed__1_once, _init_l_Lean_Lsp_instToJsonWaitForILeans_toJson___closed__1);
return v___x_1592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonHighlightMatchesOptions_fromJson(lean_object* v_json_1597_){
_start:
{
lean_object* v___x_1598_; 
v___x_1598_ = ((lean_object*)(l_Lean_Lsp_instFromJsonHighlightMatchesOptions_fromJson___closed__0));
return v___x_1598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonHighlightMatchesOptions_fromJson___boxed(lean_object* v_json_1599_){
_start:
{
lean_object* v_res_1600_; 
v_res_1600_ = l_Lean_Lsp_instFromJsonHighlightMatchesOptions_fromJson(v_json_1599_);
lean_dec(v_json_1599_);
return v_res_1600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonHighlightMatchesOptions_toJson(lean_object* v_x_1603_){
_start:
{
lean_object* v___x_1604_; 
v___x_1604_ = lean_obj_once(&l_Lean_Lsp_instToJsonWaitForILeans_toJson___closed__1, &l_Lean_Lsp_instToJsonWaitForILeans_toJson___closed__1_once, _init_l_Lean_Lsp_instToJsonWaitForILeans_toJson___closed__1);
return v___x_1604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__1_spec__2(lean_object* v_x_1609_){
_start:
{
if (lean_obj_tag(v_x_1609_) == 0)
{
lean_object* v___x_1610_; 
v___x_1610_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__1_spec__2___closed__0));
return v___x_1610_;
}
else
{
lean_object* v___x_1611_; 
v___x_1611_ = l_Lean_Lsp_instFromJsonRpcWireFormat_fromJson(v_x_1609_);
if (lean_obj_tag(v___x_1611_) == 0)
{
lean_object* v_a_1612_; lean_object* v___x_1614_; uint8_t v_isShared_1615_; uint8_t v_isSharedCheck_1619_; 
v_a_1612_ = lean_ctor_get(v___x_1611_, 0);
v_isSharedCheck_1619_ = !lean_is_exclusive(v___x_1611_);
if (v_isSharedCheck_1619_ == 0)
{
v___x_1614_ = v___x_1611_;
v_isShared_1615_ = v_isSharedCheck_1619_;
goto v_resetjp_1613_;
}
else
{
lean_inc(v_a_1612_);
lean_dec(v___x_1611_);
v___x_1614_ = lean_box(0);
v_isShared_1615_ = v_isSharedCheck_1619_;
goto v_resetjp_1613_;
}
v_resetjp_1613_:
{
lean_object* v___x_1617_; 
if (v_isShared_1615_ == 0)
{
v___x_1617_ = v___x_1614_;
goto v_reusejp_1616_;
}
else
{
lean_object* v_reuseFailAlloc_1618_; 
v_reuseFailAlloc_1618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1618_, 0, v_a_1612_);
v___x_1617_ = v_reuseFailAlloc_1618_;
goto v_reusejp_1616_;
}
v_reusejp_1616_:
{
return v___x_1617_;
}
}
}
else
{
lean_object* v_a_1620_; lean_object* v___x_1622_; uint8_t v_isShared_1623_; uint8_t v_isSharedCheck_1628_; 
v_a_1620_ = lean_ctor_get(v___x_1611_, 0);
v_isSharedCheck_1628_ = !lean_is_exclusive(v___x_1611_);
if (v_isSharedCheck_1628_ == 0)
{
v___x_1622_ = v___x_1611_;
v_isShared_1623_ = v_isSharedCheck_1628_;
goto v_resetjp_1621_;
}
else
{
lean_inc(v_a_1620_);
lean_dec(v___x_1611_);
v___x_1622_ = lean_box(0);
v_isShared_1623_ = v_isSharedCheck_1628_;
goto v_resetjp_1621_;
}
v_resetjp_1621_:
{
lean_object* v___x_1624_; lean_object* v___x_1626_; 
v___x_1624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1624_, 0, v_a_1620_);
if (v_isShared_1623_ == 0)
{
lean_ctor_set(v___x_1622_, 0, v___x_1624_);
v___x_1626_ = v___x_1622_;
goto v_reusejp_1625_;
}
else
{
lean_object* v_reuseFailAlloc_1627_; 
v_reuseFailAlloc_1627_ = lean_alloc_ctor(1, 1, 0);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__1(lean_object* v_j_1629_, lean_object* v_k_1630_){
_start:
{
lean_object* v___x_1631_; lean_object* v___x_1632_; 
v___x_1631_ = l_Lean_Json_getObjValD(v_j_1629_, v_k_1630_);
v___x_1632_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__1_spec__2(v___x_1631_);
return v___x_1632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__1___boxed(lean_object* v_j_1633_, lean_object* v_k_1634_){
_start:
{
lean_object* v_res_1635_; 
v_res_1635_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__1(v_j_1633_, v_k_1634_);
lean_dec_ref(v_k_1634_);
return v_res_1635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__0_spec__0(lean_object* v_x_1638_){
_start:
{
if (lean_obj_tag(v_x_1638_) == 0)
{
lean_object* v___x_1639_; 
v___x_1639_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__0_spec__0___closed__0));
return v___x_1639_;
}
else
{
lean_object* v___x_1640_; lean_object* v_a_1641_; lean_object* v___x_1643_; uint8_t v_isShared_1644_; uint8_t v_isSharedCheck_1649_; 
v___x_1640_ = l_Lean_Lsp_instFromJsonHighlightMatchesOptions_fromJson(v_x_1638_);
v_a_1641_ = lean_ctor_get(v___x_1640_, 0);
v_isSharedCheck_1649_ = !lean_is_exclusive(v___x_1640_);
if (v_isSharedCheck_1649_ == 0)
{
v___x_1643_ = v___x_1640_;
v_isShared_1644_ = v_isSharedCheck_1649_;
goto v_resetjp_1642_;
}
else
{
lean_inc(v_a_1641_);
lean_dec(v___x_1640_);
v___x_1643_ = lean_box(0);
v_isShared_1644_ = v_isSharedCheck_1649_;
goto v_resetjp_1642_;
}
v_resetjp_1642_:
{
lean_object* v___x_1645_; lean_object* v___x_1647_; 
v___x_1645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1645_, 0, v_a_1641_);
if (v_isShared_1644_ == 0)
{
lean_ctor_set(v___x_1643_, 0, v___x_1645_);
v___x_1647_ = v___x_1643_;
goto v_reusejp_1646_;
}
else
{
lean_object* v_reuseFailAlloc_1648_; 
v_reuseFailAlloc_1648_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__0_spec__0___boxed(lean_object* v_x_1650_){
_start:
{
lean_object* v_res_1651_; 
v_res_1651_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__0_spec__0(v_x_1650_);
lean_dec(v_x_1650_);
return v_res_1651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__0(lean_object* v_j_1652_, lean_object* v_k_1653_){
_start:
{
lean_object* v___x_1654_; lean_object* v___x_1655_; 
v___x_1654_ = l_Lean_Json_getObjValD(v_j_1652_, v_k_1653_);
v___x_1655_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__0_spec__0(v___x_1654_);
lean_dec(v___x_1654_);
return v___x_1655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__0___boxed(lean_object* v_j_1656_, lean_object* v_k_1657_){
_start:
{
lean_object* v_res_1658_; 
v_res_1658_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__0(v_j_1656_, v_k_1657_);
lean_dec_ref(v_k_1657_);
return v_res_1658_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__3(void){
_start:
{
uint8_t v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; 
v___x_1665_ = 1;
v___x_1666_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__2));
v___x_1667_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1666_, v___x_1665_);
return v___x_1667_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__4(void){
_start:
{
lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; 
v___x_1668_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6));
v___x_1669_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__3, &l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__3);
v___x_1670_ = lean_string_append(v___x_1669_, v___x_1668_);
return v___x_1670_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__7(void){
_start:
{
uint8_t v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; 
v___x_1674_ = 1;
v___x_1675_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__6));
v___x_1676_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1675_, v___x_1674_);
return v___x_1676_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__8(void){
_start:
{
lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; 
v___x_1677_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__7, &l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__7);
v___x_1678_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__4, &l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__4);
v___x_1679_ = lean_string_append(v___x_1678_, v___x_1677_);
return v___x_1679_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__9(void){
_start:
{
lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; 
v___x_1680_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_1681_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__8, &l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__8);
v___x_1682_ = lean_string_append(v___x_1681_, v___x_1680_);
return v___x_1682_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__13(void){
_start:
{
uint8_t v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; 
v___x_1687_ = 1;
v___x_1688_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__12));
v___x_1689_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1688_, v___x_1687_);
return v___x_1689_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__14(void){
_start:
{
lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; 
v___x_1690_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__13, &l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__13);
v___x_1691_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__4, &l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__4);
v___x_1692_ = lean_string_append(v___x_1691_, v___x_1690_);
return v___x_1692_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__15(void){
_start:
{
lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; 
v___x_1693_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_1694_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__14, &l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__14_once, _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__14);
v___x_1695_ = lean_string_append(v___x_1694_, v___x_1693_);
return v___x_1695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonRpcOptions_fromJson(lean_object* v_json_1696_){
_start:
{
lean_object* v___x_1697_; lean_object* v___x_1698_; 
v___x_1697_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__0));
lean_inc(v_json_1696_);
v___x_1698_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__0(v_json_1696_, v___x_1697_);
if (lean_obj_tag(v___x_1698_) == 0)
{
lean_object* v_a_1699_; lean_object* v___x_1701_; uint8_t v_isShared_1702_; uint8_t v_isSharedCheck_1708_; 
lean_dec(v_json_1696_);
v_a_1699_ = lean_ctor_get(v___x_1698_, 0);
v_isSharedCheck_1708_ = !lean_is_exclusive(v___x_1698_);
if (v_isSharedCheck_1708_ == 0)
{
v___x_1701_ = v___x_1698_;
v_isShared_1702_ = v_isSharedCheck_1708_;
goto v_resetjp_1700_;
}
else
{
lean_inc(v_a_1699_);
lean_dec(v___x_1698_);
v___x_1701_ = lean_box(0);
v_isShared_1702_ = v_isSharedCheck_1708_;
goto v_resetjp_1700_;
}
v_resetjp_1700_:
{
lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1706_; 
v___x_1703_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__9, &l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__9);
v___x_1704_ = lean_string_append(v___x_1703_, v_a_1699_);
lean_dec(v_a_1699_);
if (v_isShared_1702_ == 0)
{
lean_ctor_set(v___x_1701_, 0, v___x_1704_);
v___x_1706_ = v___x_1701_;
goto v_reusejp_1705_;
}
else
{
lean_object* v_reuseFailAlloc_1707_; 
v_reuseFailAlloc_1707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1707_, 0, v___x_1704_);
v___x_1706_ = v_reuseFailAlloc_1707_;
goto v_reusejp_1705_;
}
v_reusejp_1705_:
{
return v___x_1706_;
}
}
}
else
{
if (lean_obj_tag(v___x_1698_) == 0)
{
lean_object* v_a_1709_; lean_object* v___x_1711_; uint8_t v_isShared_1712_; uint8_t v_isSharedCheck_1716_; 
lean_dec(v_json_1696_);
v_a_1709_ = lean_ctor_get(v___x_1698_, 0);
v_isSharedCheck_1716_ = !lean_is_exclusive(v___x_1698_);
if (v_isSharedCheck_1716_ == 0)
{
v___x_1711_ = v___x_1698_;
v_isShared_1712_ = v_isSharedCheck_1716_;
goto v_resetjp_1710_;
}
else
{
lean_inc(v_a_1709_);
lean_dec(v___x_1698_);
v___x_1711_ = lean_box(0);
v_isShared_1712_ = v_isSharedCheck_1716_;
goto v_resetjp_1710_;
}
v_resetjp_1710_:
{
lean_object* v___x_1714_; 
if (v_isShared_1712_ == 0)
{
lean_ctor_set_tag(v___x_1711_, 0);
v___x_1714_ = v___x_1711_;
goto v_reusejp_1713_;
}
else
{
lean_object* v_reuseFailAlloc_1715_; 
v_reuseFailAlloc_1715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1715_, 0, v_a_1709_);
v___x_1714_ = v_reuseFailAlloc_1715_;
goto v_reusejp_1713_;
}
v_reusejp_1713_:
{
return v___x_1714_;
}
}
}
else
{
lean_object* v_a_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; 
v_a_1717_ = lean_ctor_get(v___x_1698_, 0);
lean_inc(v_a_1717_);
lean_dec_ref_known(v___x_1698_, 1);
v___x_1718_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__10));
v___x_1719_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__1(v_json_1696_, v___x_1718_);
if (lean_obj_tag(v___x_1719_) == 0)
{
lean_object* v_a_1720_; lean_object* v___x_1722_; uint8_t v_isShared_1723_; uint8_t v_isSharedCheck_1729_; 
lean_dec(v_a_1717_);
v_a_1720_ = lean_ctor_get(v___x_1719_, 0);
v_isSharedCheck_1729_ = !lean_is_exclusive(v___x_1719_);
if (v_isSharedCheck_1729_ == 0)
{
v___x_1722_ = v___x_1719_;
v_isShared_1723_ = v_isSharedCheck_1729_;
goto v_resetjp_1721_;
}
else
{
lean_inc(v_a_1720_);
lean_dec(v___x_1719_);
v___x_1722_ = lean_box(0);
v_isShared_1723_ = v_isSharedCheck_1729_;
goto v_resetjp_1721_;
}
v_resetjp_1721_:
{
lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1727_; 
v___x_1724_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__15, &l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__15_once, _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__15);
v___x_1725_ = lean_string_append(v___x_1724_, v_a_1720_);
lean_dec(v_a_1720_);
if (v_isShared_1723_ == 0)
{
lean_ctor_set(v___x_1722_, 0, v___x_1725_);
v___x_1727_ = v___x_1722_;
goto v_reusejp_1726_;
}
else
{
lean_object* v_reuseFailAlloc_1728_; 
v_reuseFailAlloc_1728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1728_, 0, v___x_1725_);
v___x_1727_ = v_reuseFailAlloc_1728_;
goto v_reusejp_1726_;
}
v_reusejp_1726_:
{
return v___x_1727_;
}
}
}
else
{
if (lean_obj_tag(v___x_1719_) == 0)
{
lean_object* v_a_1730_; lean_object* v___x_1732_; uint8_t v_isShared_1733_; uint8_t v_isSharedCheck_1737_; 
lean_dec(v_a_1717_);
v_a_1730_ = lean_ctor_get(v___x_1719_, 0);
v_isSharedCheck_1737_ = !lean_is_exclusive(v___x_1719_);
if (v_isSharedCheck_1737_ == 0)
{
v___x_1732_ = v___x_1719_;
v_isShared_1733_ = v_isSharedCheck_1737_;
goto v_resetjp_1731_;
}
else
{
lean_inc(v_a_1730_);
lean_dec(v___x_1719_);
v___x_1732_ = lean_box(0);
v_isShared_1733_ = v_isSharedCheck_1737_;
goto v_resetjp_1731_;
}
v_resetjp_1731_:
{
lean_object* v___x_1735_; 
if (v_isShared_1733_ == 0)
{
lean_ctor_set_tag(v___x_1732_, 0);
v___x_1735_ = v___x_1732_;
goto v_reusejp_1734_;
}
else
{
lean_object* v_reuseFailAlloc_1736_; 
v_reuseFailAlloc_1736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1736_, 0, v_a_1730_);
v___x_1735_ = v_reuseFailAlloc_1736_;
goto v_reusejp_1734_;
}
v_reusejp_1734_:
{
return v___x_1735_;
}
}
}
else
{
lean_object* v_a_1738_; lean_object* v___x_1740_; uint8_t v_isShared_1741_; uint8_t v_isSharedCheck_1746_; 
v_a_1738_ = lean_ctor_get(v___x_1719_, 0);
v_isSharedCheck_1746_ = !lean_is_exclusive(v___x_1719_);
if (v_isSharedCheck_1746_ == 0)
{
v___x_1740_ = v___x_1719_;
v_isShared_1741_ = v_isSharedCheck_1746_;
goto v_resetjp_1739_;
}
else
{
lean_inc(v_a_1738_);
lean_dec(v___x_1719_);
v___x_1740_ = lean_box(0);
v_isShared_1741_ = v_isSharedCheck_1746_;
goto v_resetjp_1739_;
}
v_resetjp_1739_:
{
lean_object* v___x_1742_; lean_object* v___x_1744_; 
v___x_1742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1742_, 0, v_a_1717_);
lean_ctor_set(v___x_1742_, 1, v_a_1738_);
if (v_isShared_1741_ == 0)
{
lean_ctor_set(v___x_1740_, 0, v___x_1742_);
v___x_1744_ = v___x_1740_;
goto v_reusejp_1743_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v___x_1742_);
v___x_1744_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1743_;
}
v_reusejp_1743_:
{
return v___x_1744_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonRpcOptions_toJson_spec__0(lean_object* v_k_1749_, lean_object* v_x_1750_){
_start:
{
if (lean_obj_tag(v_x_1750_) == 0)
{
lean_object* v___x_1751_; 
lean_dec_ref(v_k_1749_);
v___x_1751_ = lean_box(0);
return v___x_1751_;
}
else
{
lean_object* v_val_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; 
v_val_1752_ = lean_ctor_get(v_x_1750_, 0);
lean_inc(v_val_1752_);
lean_dec_ref_known(v_x_1750_, 1);
v___x_1753_ = l_Lean_Lsp_instToJsonHighlightMatchesOptions_toJson(v_val_1752_);
v___x_1754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1754_, 0, v_k_1749_);
lean_ctor_set(v___x_1754_, 1, v___x_1753_);
v___x_1755_ = lean_box(0);
v___x_1756_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1756_, 0, v___x_1754_);
lean_ctor_set(v___x_1756_, 1, v___x_1755_);
return v___x_1756_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonRpcOptions_toJson_spec__1(lean_object* v_k_1757_, lean_object* v_x_1758_){
_start:
{
if (lean_obj_tag(v_x_1758_) == 0)
{
lean_object* v___x_1759_; 
lean_dec_ref(v_k_1757_);
v___x_1759_ = lean_box(0);
return v___x_1759_;
}
else
{
lean_object* v_val_1760_; uint8_t v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; 
v_val_1760_ = lean_ctor_get(v_x_1758_, 0);
v___x_1761_ = lean_unbox(v_val_1760_);
v___x_1762_ = l_Lean_Lsp_instToJsonRpcWireFormat_toJson(v___x_1761_);
v___x_1763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1763_, 0, v_k_1757_);
lean_ctor_set(v___x_1763_, 1, v___x_1762_);
v___x_1764_ = lean_box(0);
v___x_1765_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1765_, 0, v___x_1763_);
lean_ctor_set(v___x_1765_, 1, v___x_1764_);
return v___x_1765_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonRpcOptions_toJson_spec__1___boxed(lean_object* v_k_1766_, lean_object* v_x_1767_){
_start:
{
lean_object* v_res_1768_; 
v_res_1768_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonRpcOptions_toJson_spec__1(v_k_1766_, v_x_1767_);
lean_dec(v_x_1767_);
return v_res_1768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRpcOptions_toJson(lean_object* v_x_1769_){
_start:
{
lean_object* v_highlightMatchesProvider_x3f_1770_; lean_object* v_rpcWireFormat_x3f_1771_; lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1787_; 
v_highlightMatchesProvider_x3f_1770_ = lean_ctor_get(v_x_1769_, 0);
v_rpcWireFormat_x3f_1771_ = lean_ctor_get(v_x_1769_, 1);
v_isSharedCheck_1787_ = !lean_is_exclusive(v_x_1769_);
if (v_isSharedCheck_1787_ == 0)
{
v___x_1773_ = v_x_1769_;
v_isShared_1774_ = v_isSharedCheck_1787_;
goto v_resetjp_1772_;
}
else
{
lean_inc(v_rpcWireFormat_x3f_1771_);
lean_inc(v_highlightMatchesProvider_x3f_1770_);
lean_dec(v_x_1769_);
v___x_1773_ = lean_box(0);
v_isShared_1774_ = v_isSharedCheck_1787_;
goto v_resetjp_1772_;
}
v_resetjp_1772_:
{
lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1781_; 
v___x_1775_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__0));
v___x_1776_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonRpcOptions_toJson_spec__0(v___x_1775_, v_highlightMatchesProvider_x3f_1770_);
v___x_1777_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__10));
v___x_1778_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonRpcOptions_toJson_spec__1(v___x_1777_, v_rpcWireFormat_x3f_1771_);
lean_dec(v_rpcWireFormat_x3f_1771_);
v___x_1779_ = lean_box(0);
if (v_isShared_1774_ == 0)
{
lean_ctor_set_tag(v___x_1773_, 1);
lean_ctor_set(v___x_1773_, 1, v___x_1779_);
lean_ctor_set(v___x_1773_, 0, v___x_1778_);
v___x_1781_ = v___x_1773_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v___x_1778_);
lean_ctor_set(v_reuseFailAlloc_1786_, 1, v___x_1779_);
v___x_1781_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; 
v___x_1782_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1782_, 0, v___x_1776_);
lean_ctor_set(v___x_1782_, 1, v___x_1781_);
v___x_1783_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0));
v___x_1784_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_1782_, v___x_1783_);
v___x_1785_ = l_Lean_Json_mkObj(v___x_1784_);
lean_dec(v___x_1784_);
return v___x_1785_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModule_fromJson_spec__0_spec__0(lean_object* v_x_1792_){
_start:
{
if (lean_obj_tag(v_x_1792_) == 0)
{
lean_object* v___x_1793_; 
v___x_1793_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModule_fromJson_spec__0_spec__0___closed__0));
return v___x_1793_;
}
else
{
lean_object* v___x_1794_; lean_object* v___x_1795_; 
v___x_1794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1794_, 0, v_x_1792_);
v___x_1795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1795_, 0, v___x_1794_);
return v___x_1795_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModule_fromJson_spec__0(lean_object* v_j_1796_, lean_object* v_k_1797_){
_start:
{
lean_object* v___x_1798_; lean_object* v___x_1799_; 
v___x_1798_ = l_Lean_Json_getObjValD(v_j_1796_, v_k_1797_);
v___x_1799_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModule_fromJson_spec__0_spec__0(v___x_1798_);
return v___x_1799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModule_fromJson_spec__0___boxed(lean_object* v_j_1800_, lean_object* v_k_1801_){
_start:
{
lean_object* v_res_1802_; 
v_res_1802_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModule_fromJson_spec__0(v_j_1800_, v_k_1801_);
lean_dec_ref(v_k_1801_);
return v_res_1802_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__3(void){
_start:
{
uint8_t v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; 
v___x_1809_ = 1;
v___x_1810_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__2));
v___x_1811_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1810_, v___x_1809_);
return v___x_1811_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__4(void){
_start:
{
lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; 
v___x_1812_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6));
v___x_1813_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__3);
v___x_1814_ = lean_string_append(v___x_1813_, v___x_1812_);
return v___x_1814_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__6(void){
_start:
{
uint8_t v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; 
v___x_1817_ = 1;
v___x_1818_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__5));
v___x_1819_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1818_, v___x_1817_);
return v___x_1819_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__7(void){
_start:
{
lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; 
v___x_1820_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__6);
v___x_1821_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__4);
v___x_1822_ = lean_string_append(v___x_1821_, v___x_1820_);
return v___x_1822_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__8(void){
_start:
{
lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; 
v___x_1823_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_1824_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__7);
v___x_1825_ = lean_string_append(v___x_1824_, v___x_1823_);
return v___x_1825_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__9(void){
_start:
{
lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; 
v___x_1826_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__6, &l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__6);
v___x_1827_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__4);
v___x_1828_ = lean_string_append(v___x_1827_, v___x_1826_);
return v___x_1828_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__10(void){
_start:
{
lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; 
v___x_1829_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_1830_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__9, &l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__9);
v___x_1831_ = lean_string_append(v___x_1830_, v___x_1829_);
return v___x_1831_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanModule_fromJson(lean_object* v_json_1833_){
_start:
{
lean_object* v___x_1834_; lean_object* v___x_1835_; 
v___x_1834_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__0));
lean_inc(v_json_1833_);
v___x_1835_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson_spec__0(v_json_1833_, v___x_1834_);
if (lean_obj_tag(v___x_1835_) == 0)
{
lean_object* v_a_1836_; lean_object* v___x_1838_; uint8_t v_isShared_1839_; uint8_t v_isSharedCheck_1845_; 
lean_dec(v_json_1833_);
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
v___x_1840_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__8);
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
lean_dec(v_json_1833_);
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
lean_object* v_a_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; 
v_a_1854_ = lean_ctor_get(v___x_1835_, 0);
lean_inc(v_a_1854_);
lean_dec_ref_known(v___x_1835_, 1);
v___x_1855_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__0));
lean_inc(v_json_1833_);
v___x_1856_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson_spec__0(v_json_1833_, v___x_1855_);
if (lean_obj_tag(v___x_1856_) == 0)
{
lean_object* v_a_1857_; lean_object* v___x_1859_; uint8_t v_isShared_1860_; uint8_t v_isSharedCheck_1866_; 
lean_dec(v_a_1854_);
lean_dec(v_json_1833_);
v_a_1857_ = lean_ctor_get(v___x_1856_, 0);
v_isSharedCheck_1866_ = !lean_is_exclusive(v___x_1856_);
if (v_isSharedCheck_1866_ == 0)
{
v___x_1859_ = v___x_1856_;
v_isShared_1860_ = v_isSharedCheck_1866_;
goto v_resetjp_1858_;
}
else
{
lean_inc(v_a_1857_);
lean_dec(v___x_1856_);
v___x_1859_ = lean_box(0);
v_isShared_1860_ = v_isSharedCheck_1866_;
goto v_resetjp_1858_;
}
v_resetjp_1858_:
{
lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1864_; 
v___x_1861_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__10, &l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__10);
v___x_1862_ = lean_string_append(v___x_1861_, v_a_1857_);
lean_dec(v_a_1857_);
if (v_isShared_1860_ == 0)
{
lean_ctor_set(v___x_1859_, 0, v___x_1862_);
v___x_1864_ = v___x_1859_;
goto v_reusejp_1863_;
}
else
{
lean_object* v_reuseFailAlloc_1865_; 
v_reuseFailAlloc_1865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1865_, 0, v___x_1862_);
v___x_1864_ = v_reuseFailAlloc_1865_;
goto v_reusejp_1863_;
}
v_reusejp_1863_:
{
return v___x_1864_;
}
}
}
else
{
if (lean_obj_tag(v___x_1856_) == 0)
{
lean_object* v_a_1867_; lean_object* v___x_1869_; uint8_t v_isShared_1870_; uint8_t v_isSharedCheck_1874_; 
lean_dec(v_a_1854_);
lean_dec(v_json_1833_);
v_a_1867_ = lean_ctor_get(v___x_1856_, 0);
v_isSharedCheck_1874_ = !lean_is_exclusive(v___x_1856_);
if (v_isSharedCheck_1874_ == 0)
{
v___x_1869_ = v___x_1856_;
v_isShared_1870_ = v_isSharedCheck_1874_;
goto v_resetjp_1868_;
}
else
{
lean_inc(v_a_1867_);
lean_dec(v___x_1856_);
v___x_1869_ = lean_box(0);
v_isShared_1870_ = v_isSharedCheck_1874_;
goto v_resetjp_1868_;
}
v_resetjp_1868_:
{
lean_object* v___x_1872_; 
if (v_isShared_1870_ == 0)
{
lean_ctor_set_tag(v___x_1869_, 0);
v___x_1872_ = v___x_1869_;
goto v_reusejp_1871_;
}
else
{
lean_object* v_reuseFailAlloc_1873_; 
v_reuseFailAlloc_1873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1873_, 0, v_a_1867_);
v___x_1872_ = v_reuseFailAlloc_1873_;
goto v_reusejp_1871_;
}
v_reusejp_1871_:
{
return v___x_1872_;
}
}
}
else
{
lean_object* v_a_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v_a_1878_; lean_object* v___x_1880_; uint8_t v_isShared_1881_; uint8_t v_isSharedCheck_1886_; 
v_a_1875_ = lean_ctor_get(v___x_1856_, 0);
lean_inc(v_a_1875_);
lean_dec_ref_known(v___x_1856_, 1);
v___x_1876_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__11));
v___x_1877_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModule_fromJson_spec__0(v_json_1833_, v___x_1876_);
v_a_1878_ = lean_ctor_get(v___x_1877_, 0);
v_isSharedCheck_1886_ = !lean_is_exclusive(v___x_1877_);
if (v_isSharedCheck_1886_ == 0)
{
v___x_1880_ = v___x_1877_;
v_isShared_1881_ = v_isSharedCheck_1886_;
goto v_resetjp_1879_;
}
else
{
lean_inc(v_a_1878_);
lean_dec(v___x_1877_);
v___x_1880_ = lean_box(0);
v_isShared_1881_ = v_isSharedCheck_1886_;
goto v_resetjp_1879_;
}
v_resetjp_1879_:
{
lean_object* v___x_1882_; lean_object* v___x_1884_; 
v___x_1882_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1882_, 0, v_a_1854_);
lean_ctor_set(v___x_1882_, 1, v_a_1875_);
lean_ctor_set(v___x_1882_, 2, v_a_1878_);
if (v_isShared_1881_ == 0)
{
lean_ctor_set(v___x_1880_, 0, v___x_1882_);
v___x_1884_ = v___x_1880_;
goto v_reusejp_1883_;
}
else
{
lean_object* v_reuseFailAlloc_1885_; 
v_reuseFailAlloc_1885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1885_, 0, v___x_1882_);
v___x_1884_ = v_reuseFailAlloc_1885_;
goto v_reusejp_1883_;
}
v_reusejp_1883_:
{
return v___x_1884_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanModule_toJson_spec__0(lean_object* v_k_1889_, lean_object* v_x_1890_){
_start:
{
if (lean_obj_tag(v_x_1890_) == 0)
{
lean_object* v___x_1891_; 
lean_dec_ref(v_k_1889_);
v___x_1891_ = lean_box(0);
return v___x_1891_;
}
else
{
lean_object* v_val_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; 
v_val_1892_ = lean_ctor_get(v_x_1890_, 0);
lean_inc(v_val_1892_);
v___x_1893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1893_, 0, v_k_1889_);
lean_ctor_set(v___x_1893_, 1, v_val_1892_);
v___x_1894_ = lean_box(0);
v___x_1895_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1895_, 0, v___x_1893_);
lean_ctor_set(v___x_1895_, 1, v___x_1894_);
return v___x_1895_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanModule_toJson_spec__0___boxed(lean_object* v_k_1896_, lean_object* v_x_1897_){
_start:
{
lean_object* v_res_1898_; 
v_res_1898_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanModule_toJson_spec__0(v_k_1896_, v_x_1897_);
lean_dec(v_x_1897_);
return v_res_1898_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanModule_toJson(lean_object* v_x_1899_){
_start:
{
lean_object* v_name_1900_; lean_object* v_uri_1901_; lean_object* v_data_x3f_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; 
v_name_1900_ = lean_ctor_get(v_x_1899_, 0);
v_uri_1901_ = lean_ctor_get(v_x_1899_, 1);
v_data_x3f_1902_ = lean_ctor_get(v_x_1899_, 2);
v___x_1903_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__0));
lean_inc_ref(v_name_1900_);
v___x_1904_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1904_, 0, v_name_1900_);
v___x_1905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1905_, 0, v___x_1903_);
lean_ctor_set(v___x_1905_, 1, v___x_1904_);
v___x_1906_ = lean_box(0);
v___x_1907_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1907_, 0, v___x_1905_);
lean_ctor_set(v___x_1907_, 1, v___x_1906_);
v___x_1908_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__0));
lean_inc_ref(v_uri_1901_);
v___x_1909_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1909_, 0, v_uri_1901_);
v___x_1910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1910_, 0, v___x_1908_);
lean_ctor_set(v___x_1910_, 1, v___x_1909_);
v___x_1911_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1911_, 0, v___x_1910_);
lean_ctor_set(v___x_1911_, 1, v___x_1906_);
v___x_1912_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__11));
v___x_1913_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanModule_toJson_spec__0(v___x_1912_, v_data_x3f_1902_);
v___x_1914_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1914_, 0, v___x_1913_);
lean_ctor_set(v___x_1914_, 1, v___x_1906_);
v___x_1915_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1915_, 0, v___x_1911_);
lean_ctor_set(v___x_1915_, 1, v___x_1914_);
v___x_1916_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1916_, 0, v___x_1907_);
lean_ctor_set(v___x_1916_, 1, v___x_1915_);
v___x_1917_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0));
v___x_1918_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_1916_, v___x_1917_);
v___x_1919_ = l_Lean_Json_mkObj(v___x_1918_);
lean_dec(v___x_1918_);
return v___x_1919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanModule_toJson___boxed(lean_object* v_x_1920_){
_start:
{
lean_object* v_res_1921_; 
v_res_1921_ = l_Lean_Lsp_instToJsonLeanModule_toJson(v_x_1920_);
lean_dec_ref(v_x_1920_);
return v_res_1921_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__2(void){
_start:
{
uint8_t v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; 
v___x_1929_ = 1;
v___x_1930_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__1));
v___x_1931_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1930_, v___x_1929_);
return v___x_1931_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__3(void){
_start:
{
lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; 
v___x_1932_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6));
v___x_1933_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__2, &l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__2);
v___x_1934_ = lean_string_append(v___x_1933_, v___x_1932_);
return v___x_1934_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; 
v___x_1935_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9, &l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9);
v___x_1936_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__3);
v___x_1937_ = lean_string_append(v___x_1936_, v___x_1935_);
return v___x_1937_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__5(void){
_start:
{
lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; 
v___x_1938_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_1939_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__4);
v___x_1940_ = lean_string_append(v___x_1939_, v___x_1938_);
return v___x_1940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson(lean_object* v_json_1941_){
_start:
{
lean_object* v___x_1942_; lean_object* v___x_1943_; 
v___x_1942_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__0));
v___x_1943_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoalParams_fromJson_spec__0(v_json_1941_, v___x_1942_);
if (lean_obj_tag(v___x_1943_) == 0)
{
lean_object* v_a_1944_; lean_object* v___x_1946_; uint8_t v_isShared_1947_; uint8_t v_isSharedCheck_1953_; 
v_a_1944_ = lean_ctor_get(v___x_1943_, 0);
v_isSharedCheck_1953_ = !lean_is_exclusive(v___x_1943_);
if (v_isSharedCheck_1953_ == 0)
{
v___x_1946_ = v___x_1943_;
v_isShared_1947_ = v_isSharedCheck_1953_;
goto v_resetjp_1945_;
}
else
{
lean_inc(v_a_1944_);
lean_dec(v___x_1943_);
v___x_1946_ = lean_box(0);
v_isShared_1947_ = v_isSharedCheck_1953_;
goto v_resetjp_1945_;
}
v_resetjp_1945_:
{
lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1951_; 
v___x_1948_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__5, &l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__5);
v___x_1949_ = lean_string_append(v___x_1948_, v_a_1944_);
lean_dec(v_a_1944_);
if (v_isShared_1947_ == 0)
{
lean_ctor_set(v___x_1946_, 0, v___x_1949_);
v___x_1951_ = v___x_1946_;
goto v_reusejp_1950_;
}
else
{
lean_object* v_reuseFailAlloc_1952_; 
v_reuseFailAlloc_1952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1952_, 0, v___x_1949_);
v___x_1951_ = v_reuseFailAlloc_1952_;
goto v_reusejp_1950_;
}
v_reusejp_1950_:
{
return v___x_1951_;
}
}
}
else
{
if (lean_obj_tag(v___x_1943_) == 0)
{
lean_object* v_a_1954_; lean_object* v___x_1956_; uint8_t v_isShared_1957_; uint8_t v_isSharedCheck_1961_; 
v_a_1954_ = lean_ctor_get(v___x_1943_, 0);
v_isSharedCheck_1961_ = !lean_is_exclusive(v___x_1943_);
if (v_isSharedCheck_1961_ == 0)
{
v___x_1956_ = v___x_1943_;
v_isShared_1957_ = v_isSharedCheck_1961_;
goto v_resetjp_1955_;
}
else
{
lean_inc(v_a_1954_);
lean_dec(v___x_1943_);
v___x_1956_ = lean_box(0);
v_isShared_1957_ = v_isSharedCheck_1961_;
goto v_resetjp_1955_;
}
v_resetjp_1955_:
{
lean_object* v___x_1959_; 
if (v_isShared_1957_ == 0)
{
lean_ctor_set_tag(v___x_1956_, 0);
v___x_1959_ = v___x_1956_;
goto v_reusejp_1958_;
}
else
{
lean_object* v_reuseFailAlloc_1960_; 
v_reuseFailAlloc_1960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1960_, 0, v_a_1954_);
v___x_1959_ = v_reuseFailAlloc_1960_;
goto v_reusejp_1958_;
}
v_reusejp_1958_:
{
return v___x_1959_;
}
}
}
else
{
lean_object* v_a_1962_; lean_object* v___x_1964_; uint8_t v_isShared_1965_; uint8_t v_isSharedCheck_1969_; 
v_a_1962_ = lean_ctor_get(v___x_1943_, 0);
v_isSharedCheck_1969_ = !lean_is_exclusive(v___x_1943_);
if (v_isSharedCheck_1969_ == 0)
{
v___x_1964_ = v___x_1943_;
v_isShared_1965_ = v_isSharedCheck_1969_;
goto v_resetjp_1963_;
}
else
{
lean_inc(v_a_1962_);
lean_dec(v___x_1943_);
v___x_1964_ = lean_box(0);
v_isShared_1965_ = v_isSharedCheck_1969_;
goto v_resetjp_1963_;
}
v_resetjp_1963_:
{
lean_object* v___x_1967_; 
if (v_isShared_1965_ == 0)
{
v___x_1967_ = v___x_1964_;
goto v_reusejp_1966_;
}
else
{
lean_object* v_reuseFailAlloc_1968_; 
v_reuseFailAlloc_1968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1968_, 0, v_a_1962_);
v___x_1967_ = v_reuseFailAlloc_1968_;
goto v_reusejp_1966_;
}
v_reusejp_1966_:
{
return v___x_1967_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanPrepareModuleHierarchyParams_toJson(lean_object* v_x_1972_){
_start:
{
lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; 
v___x_1973_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__0));
v___x_1974_ = l_Lean_Lsp_instToJsonTextDocumentIdentifier_toJson(v_x_1972_);
v___x_1975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1975_, 0, v___x_1973_);
lean_ctor_set(v___x_1975_, 1, v___x_1974_);
v___x_1976_ = lean_box(0);
v___x_1977_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1977_, 0, v___x_1975_);
lean_ctor_set(v___x_1977_, 1, v___x_1976_);
v___x_1978_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1978_, 0, v___x_1977_);
lean_ctor_set(v___x_1978_, 1, v___x_1976_);
v___x_1979_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0));
v___x_1980_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_1978_, v___x_1979_);
v___x_1981_ = l_Lean_Json_mkObj(v___x_1980_);
lean_dec(v___x_1980_);
return v___x_1981_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanImportMetaKind_ctorIdx(uint8_t v_x_1984_){
_start:
{
switch(v_x_1984_)
{
case 0:
{
lean_object* v___x_1985_; 
v___x_1985_ = lean_unsigned_to_nat(0u);
return v___x_1985_;
}
case 1:
{
lean_object* v___x_1986_; 
v___x_1986_ = lean_unsigned_to_nat(1u);
return v___x_1986_;
}
default: 
{
lean_object* v___x_1987_; 
v___x_1987_ = lean_unsigned_to_nat(2u);
return v___x_1987_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanImportMetaKind_ctorIdx___boxed(lean_object* v_x_1988_){
_start:
{
uint8_t v_x_boxed_1989_; lean_object* v_res_1990_; 
v_x_boxed_1989_ = lean_unbox(v_x_1988_);
v_res_1990_ = l_Lean_Lsp_LeanImportMetaKind_ctorIdx(v_x_boxed_1989_);
return v_res_1990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanImportMetaKind_ctorElim___redArg(lean_object* v_k_1991_){
_start:
{
lean_inc(v_k_1991_);
return v_k_1991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanImportMetaKind_ctorElim___redArg___boxed(lean_object* v_k_1992_){
_start:
{
lean_object* v_res_1993_; 
v_res_1993_ = l_Lean_Lsp_LeanImportMetaKind_ctorElim___redArg(v_k_1992_);
lean_dec(v_k_1992_);
return v_res_1993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanImportMetaKind_ctorElim(lean_object* v_motive_1994_, lean_object* v_ctorIdx_1995_, uint8_t v_t_1996_, lean_object* v_h_1997_, lean_object* v_k_1998_){
_start:
{
lean_inc(v_k_1998_);
return v_k_1998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanImportMetaKind_ctorElim___boxed(lean_object* v_motive_1999_, lean_object* v_ctorIdx_2000_, lean_object* v_t_2001_, lean_object* v_h_2002_, lean_object* v_k_2003_){
_start:
{
uint8_t v_t_boxed_2004_; lean_object* v_res_2005_; 
v_t_boxed_2004_ = lean_unbox(v_t_2001_);
v_res_2005_ = l_Lean_Lsp_LeanImportMetaKind_ctorElim(v_motive_1999_, v_ctorIdx_2000_, v_t_boxed_2004_, v_h_2002_, v_k_2003_);
lean_dec(v_k_2003_);
lean_dec(v_ctorIdx_2000_);
return v_res_2005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanImportMetaKind_nonMeta_elim___redArg(lean_object* v_nonMeta_2006_){
_start:
{
lean_inc(v_nonMeta_2006_);
return v_nonMeta_2006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanImportMetaKind_nonMeta_elim___redArg___boxed(lean_object* v_nonMeta_2007_){
_start:
{
lean_object* v_res_2008_; 
v_res_2008_ = l_Lean_Lsp_LeanImportMetaKind_nonMeta_elim___redArg(v_nonMeta_2007_);
lean_dec(v_nonMeta_2007_);
return v_res_2008_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanImportMetaKind_nonMeta_elim(lean_object* v_motive_2009_, uint8_t v_t_2010_, lean_object* v_h_2011_, lean_object* v_nonMeta_2012_){
_start:
{
lean_inc(v_nonMeta_2012_);
return v_nonMeta_2012_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanImportMetaKind_nonMeta_elim___boxed(lean_object* v_motive_2013_, lean_object* v_t_2014_, lean_object* v_h_2015_, lean_object* v_nonMeta_2016_){
_start:
{
uint8_t v_t_boxed_2017_; lean_object* v_res_2018_; 
v_t_boxed_2017_ = lean_unbox(v_t_2014_);
v_res_2018_ = l_Lean_Lsp_LeanImportMetaKind_nonMeta_elim(v_motive_2013_, v_t_boxed_2017_, v_h_2015_, v_nonMeta_2016_);
lean_dec(v_nonMeta_2016_);
return v_res_2018_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanImportMetaKind_meta_elim___redArg(lean_object* v_meta_2019_){
_start:
{
lean_inc(v_meta_2019_);
return v_meta_2019_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanImportMetaKind_meta_elim___redArg___boxed(lean_object* v_meta_2020_){
_start:
{
lean_object* v_res_2021_; 
v_res_2021_ = l_Lean_Lsp_LeanImportMetaKind_meta_elim___redArg(v_meta_2020_);
lean_dec(v_meta_2020_);
return v_res_2021_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanImportMetaKind_meta_elim(lean_object* v_motive_2022_, uint8_t v_t_2023_, lean_object* v_h_2024_, lean_object* v_meta_2025_){
_start:
{
lean_inc(v_meta_2025_);
return v_meta_2025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanImportMetaKind_meta_elim___boxed(lean_object* v_motive_2026_, lean_object* v_t_2027_, lean_object* v_h_2028_, lean_object* v_meta_2029_){
_start:
{
uint8_t v_t_boxed_2030_; lean_object* v_res_2031_; 
v_t_boxed_2030_ = lean_unbox(v_t_2027_);
v_res_2031_ = l_Lean_Lsp_LeanImportMetaKind_meta_elim(v_motive_2026_, v_t_boxed_2030_, v_h_2028_, v_meta_2029_);
lean_dec(v_meta_2029_);
return v_res_2031_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanImportMetaKind_full_elim___redArg(lean_object* v_full_2032_){
_start:
{
lean_inc(v_full_2032_);
return v_full_2032_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanImportMetaKind_full_elim___redArg___boxed(lean_object* v_full_2033_){
_start:
{
lean_object* v_res_2034_; 
v_res_2034_ = l_Lean_Lsp_LeanImportMetaKind_full_elim___redArg(v_full_2033_);
lean_dec(v_full_2033_);
return v_res_2034_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanImportMetaKind_full_elim(lean_object* v_motive_2035_, uint8_t v_t_2036_, lean_object* v_h_2037_, lean_object* v_full_2038_){
_start:
{
lean_inc(v_full_2038_);
return v_full_2038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanImportMetaKind_full_elim___boxed(lean_object* v_motive_2039_, lean_object* v_t_2040_, lean_object* v_h_2041_, lean_object* v_full_2042_){
_start:
{
uint8_t v_t_boxed_2043_; lean_object* v_res_2044_; 
v_t_boxed_2043_ = lean_unbox(v_t_2040_);
v_res_2044_ = l_Lean_Lsp_LeanImportMetaKind_full_elim(v_motive_2039_, v_t_boxed_2043_, v_h_2041_, v_full_2042_);
lean_dec(v_full_2042_);
return v_res_2044_;
}
}
static uint8_t _init_l_Lean_Lsp_instInhabitedLeanImportMetaKind_default(void){
_start:
{
uint8_t v___x_2045_; 
v___x_2045_ = 0;
return v___x_2045_;
}
}
static uint8_t _init_l_Lean_Lsp_instInhabitedLeanImportMetaKind(void){
_start:
{
uint8_t v___x_2046_; 
v___x_2046_ = 0;
return v___x_2046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson(lean_object* v_json_2063_){
_start:
{
lean_object* v___x_2064_; 
v___x_2064_ = l_Lean_Json_getTag_x3f(v_json_2063_);
if (lean_obj_tag(v___x_2064_) == 0)
{
lean_object* v___x_2065_; 
v___x_2065_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson___closed__0));
return v___x_2065_;
}
else
{
lean_object* v_val_2066_; lean_object* v___x_2067_; uint8_t v___x_2068_; 
v_val_2066_ = lean_ctor_get(v___x_2064_, 0);
lean_inc(v_val_2066_);
lean_dec_ref_known(v___x_2064_, 1);
v___x_2067_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson___closed__1));
v___x_2068_ = lean_string_dec_eq(v_val_2066_, v___x_2067_);
if (v___x_2068_ == 0)
{
lean_object* v___x_2069_; uint8_t v___x_2070_; 
v___x_2069_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson___closed__2));
v___x_2070_ = lean_string_dec_eq(v_val_2066_, v___x_2069_);
if (v___x_2070_ == 0)
{
lean_object* v___x_2071_; uint8_t v___x_2072_; 
v___x_2071_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson___closed__3));
v___x_2072_ = lean_string_dec_eq(v_val_2066_, v___x_2071_);
lean_dec(v_val_2066_);
if (v___x_2072_ == 0)
{
lean_object* v___x_2073_; 
v___x_2073_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson___closed__4));
return v___x_2073_;
}
else
{
lean_object* v___x_2074_; 
v___x_2074_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson___closed__5));
return v___x_2074_;
}
}
else
{
lean_object* v___x_2075_; 
lean_dec(v_val_2066_);
v___x_2075_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson___closed__6));
return v___x_2075_;
}
}
else
{
lean_object* v___x_2076_; 
lean_dec(v_val_2066_);
v___x_2076_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson___closed__7));
return v___x_2076_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanImportMetaKind_toJson(uint8_t v_x_2085_){
_start:
{
switch(v_x_2085_)
{
case 0:
{
lean_object* v___x_2086_; 
v___x_2086_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanImportMetaKind_toJson___closed__0));
return v___x_2086_;
}
case 1:
{
lean_object* v___x_2087_; 
v___x_2087_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanImportMetaKind_toJson___closed__1));
return v___x_2087_;
}
default: 
{
lean_object* v___x_2088_; 
v___x_2088_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanImportMetaKind_toJson___closed__2));
return v___x_2088_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanImportMetaKind_toJson___boxed(lean_object* v_x_2089_){
_start:
{
uint8_t v_x_64__boxed_2090_; lean_object* v_res_2091_; 
v_x_64__boxed_2090_ = lean_unbox(v_x_2089_);
v_res_2091_ = l_Lean_Lsp_instToJsonLeanImportMetaKind_toJson(v_x_64__boxed_2090_);
return v_res_2091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportKind_fromJson_spec__0(lean_object* v_j_2094_, lean_object* v_k_2095_){
_start:
{
lean_object* v___x_2096_; lean_object* v___x_2097_; 
v___x_2096_ = l_Lean_Json_getObjValD(v_j_2094_, v_k_2095_);
v___x_2097_ = l_Lean_Json_getBool_x3f(v___x_2096_);
lean_dec(v___x_2096_);
return v___x_2097_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportKind_fromJson_spec__0___boxed(lean_object* v_j_2098_, lean_object* v_k_2099_){
_start:
{
lean_object* v_res_2100_; 
v_res_2100_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportKind_fromJson_spec__0(v_j_2098_, v_k_2099_);
lean_dec_ref(v_k_2099_);
return v_res_2100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportKind_fromJson_spec__1(lean_object* v_j_2101_, lean_object* v_k_2102_){
_start:
{
lean_object* v___x_2103_; lean_object* v___x_2104_; 
v___x_2103_ = l_Lean_Json_getObjValD(v_j_2101_, v_k_2102_);
v___x_2104_ = l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson(v___x_2103_);
return v___x_2104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportKind_fromJson_spec__1___boxed(lean_object* v_j_2105_, lean_object* v_k_2106_){
_start:
{
lean_object* v_res_2107_; 
v_res_2107_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportKind_fromJson_spec__1(v_j_2105_, v_k_2106_);
lean_dec_ref(v_k_2106_);
return v_res_2107_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__3(void){
_start:
{
uint8_t v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; 
v___x_2114_ = 1;
v___x_2115_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__2));
v___x_2116_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2115_, v___x_2114_);
return v___x_2116_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__4(void){
_start:
{
lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; 
v___x_2117_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6));
v___x_2118_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__3);
v___x_2119_ = lean_string_append(v___x_2118_, v___x_2117_);
return v___x_2119_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__6(void){
_start:
{
uint8_t v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; 
v___x_2122_ = 1;
v___x_2123_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__5));
v___x_2124_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2123_, v___x_2122_);
return v___x_2124_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__7(void){
_start:
{
lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; 
v___x_2125_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__6);
v___x_2126_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__4);
v___x_2127_ = lean_string_append(v___x_2126_, v___x_2125_);
return v___x_2127_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__8(void){
_start:
{
lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; 
v___x_2128_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_2129_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__7);
v___x_2130_ = lean_string_append(v___x_2129_, v___x_2128_);
return v___x_2130_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__11(void){
_start:
{
uint8_t v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; 
v___x_2134_ = 1;
v___x_2135_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__10));
v___x_2136_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2135_, v___x_2134_);
return v___x_2136_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__12(void){
_start:
{
lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; 
v___x_2137_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__11, &l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__11);
v___x_2138_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__4);
v___x_2139_ = lean_string_append(v___x_2138_, v___x_2137_);
return v___x_2139_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__13(void){
_start:
{
lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; 
v___x_2140_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_2141_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__12, &l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__12);
v___x_2142_ = lean_string_append(v___x_2141_, v___x_2140_);
return v___x_2142_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__16(void){
_start:
{
uint8_t v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; 
v___x_2146_ = 1;
v___x_2147_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__15));
v___x_2148_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2147_, v___x_2146_);
return v___x_2148_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__17(void){
_start:
{
lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; 
v___x_2149_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__16, &l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__16_once, _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__16);
v___x_2150_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__4);
v___x_2151_ = lean_string_append(v___x_2150_, v___x_2149_);
return v___x_2151_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__18(void){
_start:
{
lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; 
v___x_2152_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_2153_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__17, &l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__17_once, _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__17);
v___x_2154_ = lean_string_append(v___x_2153_, v___x_2152_);
return v___x_2154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanImportKind_fromJson(lean_object* v_json_2155_){
_start:
{
lean_object* v___x_2156_; lean_object* v___x_2157_; 
v___x_2156_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__0));
lean_inc(v_json_2155_);
v___x_2157_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportKind_fromJson_spec__0(v_json_2155_, v___x_2156_);
if (lean_obj_tag(v___x_2157_) == 0)
{
lean_object* v_a_2158_; lean_object* v___x_2160_; uint8_t v_isShared_2161_; uint8_t v_isSharedCheck_2167_; 
lean_dec(v_json_2155_);
v_a_2158_ = lean_ctor_get(v___x_2157_, 0);
v_isSharedCheck_2167_ = !lean_is_exclusive(v___x_2157_);
if (v_isSharedCheck_2167_ == 0)
{
v___x_2160_ = v___x_2157_;
v_isShared_2161_ = v_isSharedCheck_2167_;
goto v_resetjp_2159_;
}
else
{
lean_inc(v_a_2158_);
lean_dec(v___x_2157_);
v___x_2160_ = lean_box(0);
v_isShared_2161_ = v_isSharedCheck_2167_;
goto v_resetjp_2159_;
}
v_resetjp_2159_:
{
lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2165_; 
v___x_2162_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__8);
v___x_2163_ = lean_string_append(v___x_2162_, v_a_2158_);
lean_dec(v_a_2158_);
if (v_isShared_2161_ == 0)
{
lean_ctor_set(v___x_2160_, 0, v___x_2163_);
v___x_2165_ = v___x_2160_;
goto v_reusejp_2164_;
}
else
{
lean_object* v_reuseFailAlloc_2166_; 
v_reuseFailAlloc_2166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2166_, 0, v___x_2163_);
v___x_2165_ = v_reuseFailAlloc_2166_;
goto v_reusejp_2164_;
}
v_reusejp_2164_:
{
return v___x_2165_;
}
}
}
else
{
if (lean_obj_tag(v___x_2157_) == 0)
{
lean_object* v_a_2168_; lean_object* v___x_2170_; uint8_t v_isShared_2171_; uint8_t v_isSharedCheck_2175_; 
lean_dec(v_json_2155_);
v_a_2168_ = lean_ctor_get(v___x_2157_, 0);
v_isSharedCheck_2175_ = !lean_is_exclusive(v___x_2157_);
if (v_isSharedCheck_2175_ == 0)
{
v___x_2170_ = v___x_2157_;
v_isShared_2171_ = v_isSharedCheck_2175_;
goto v_resetjp_2169_;
}
else
{
lean_inc(v_a_2168_);
lean_dec(v___x_2157_);
v___x_2170_ = lean_box(0);
v_isShared_2171_ = v_isSharedCheck_2175_;
goto v_resetjp_2169_;
}
v_resetjp_2169_:
{
lean_object* v___x_2173_; 
if (v_isShared_2171_ == 0)
{
lean_ctor_set_tag(v___x_2170_, 0);
v___x_2173_ = v___x_2170_;
goto v_reusejp_2172_;
}
else
{
lean_object* v_reuseFailAlloc_2174_; 
v_reuseFailAlloc_2174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2174_, 0, v_a_2168_);
v___x_2173_ = v_reuseFailAlloc_2174_;
goto v_reusejp_2172_;
}
v_reusejp_2172_:
{
return v___x_2173_;
}
}
}
else
{
lean_object* v_a_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; 
v_a_2176_ = lean_ctor_get(v___x_2157_, 0);
lean_inc(v_a_2176_);
lean_dec_ref_known(v___x_2157_, 1);
v___x_2177_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__9));
lean_inc(v_json_2155_);
v___x_2178_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportKind_fromJson_spec__0(v_json_2155_, v___x_2177_);
if (lean_obj_tag(v___x_2178_) == 0)
{
lean_object* v_a_2179_; lean_object* v___x_2181_; uint8_t v_isShared_2182_; uint8_t v_isSharedCheck_2188_; 
lean_dec(v_a_2176_);
lean_dec(v_json_2155_);
v_a_2179_ = lean_ctor_get(v___x_2178_, 0);
v_isSharedCheck_2188_ = !lean_is_exclusive(v___x_2178_);
if (v_isSharedCheck_2188_ == 0)
{
v___x_2181_ = v___x_2178_;
v_isShared_2182_ = v_isSharedCheck_2188_;
goto v_resetjp_2180_;
}
else
{
lean_inc(v_a_2179_);
lean_dec(v___x_2178_);
v___x_2181_ = lean_box(0);
v_isShared_2182_ = v_isSharedCheck_2188_;
goto v_resetjp_2180_;
}
v_resetjp_2180_:
{
lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2186_; 
v___x_2183_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__13, &l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__13);
v___x_2184_ = lean_string_append(v___x_2183_, v_a_2179_);
lean_dec(v_a_2179_);
if (v_isShared_2182_ == 0)
{
lean_ctor_set(v___x_2181_, 0, v___x_2184_);
v___x_2186_ = v___x_2181_;
goto v_reusejp_2185_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v___x_2184_);
v___x_2186_ = v_reuseFailAlloc_2187_;
goto v_reusejp_2185_;
}
v_reusejp_2185_:
{
return v___x_2186_;
}
}
}
else
{
if (lean_obj_tag(v___x_2178_) == 0)
{
lean_object* v_a_2189_; lean_object* v___x_2191_; uint8_t v_isShared_2192_; uint8_t v_isSharedCheck_2196_; 
lean_dec(v_a_2176_);
lean_dec(v_json_2155_);
v_a_2189_ = lean_ctor_get(v___x_2178_, 0);
v_isSharedCheck_2196_ = !lean_is_exclusive(v___x_2178_);
if (v_isSharedCheck_2196_ == 0)
{
v___x_2191_ = v___x_2178_;
v_isShared_2192_ = v_isSharedCheck_2196_;
goto v_resetjp_2190_;
}
else
{
lean_inc(v_a_2189_);
lean_dec(v___x_2178_);
v___x_2191_ = lean_box(0);
v_isShared_2192_ = v_isSharedCheck_2196_;
goto v_resetjp_2190_;
}
v_resetjp_2190_:
{
lean_object* v___x_2194_; 
if (v_isShared_2192_ == 0)
{
lean_ctor_set_tag(v___x_2191_, 0);
v___x_2194_ = v___x_2191_;
goto v_reusejp_2193_;
}
else
{
lean_object* v_reuseFailAlloc_2195_; 
v_reuseFailAlloc_2195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2195_, 0, v_a_2189_);
v___x_2194_ = v_reuseFailAlloc_2195_;
goto v_reusejp_2193_;
}
v_reusejp_2193_:
{
return v___x_2194_;
}
}
}
else
{
lean_object* v_a_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; 
v_a_2197_ = lean_ctor_get(v___x_2178_, 0);
lean_inc(v_a_2197_);
lean_dec_ref_known(v___x_2178_, 1);
v___x_2198_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__14));
v___x_2199_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportKind_fromJson_spec__1(v_json_2155_, v___x_2198_);
if (lean_obj_tag(v___x_2199_) == 0)
{
lean_object* v_a_2200_; lean_object* v___x_2202_; uint8_t v_isShared_2203_; uint8_t v_isSharedCheck_2209_; 
lean_dec(v_a_2197_);
lean_dec(v_a_2176_);
v_a_2200_ = lean_ctor_get(v___x_2199_, 0);
v_isSharedCheck_2209_ = !lean_is_exclusive(v___x_2199_);
if (v_isSharedCheck_2209_ == 0)
{
v___x_2202_ = v___x_2199_;
v_isShared_2203_ = v_isSharedCheck_2209_;
goto v_resetjp_2201_;
}
else
{
lean_inc(v_a_2200_);
lean_dec(v___x_2199_);
v___x_2202_ = lean_box(0);
v_isShared_2203_ = v_isSharedCheck_2209_;
goto v_resetjp_2201_;
}
v_resetjp_2201_:
{
lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2207_; 
v___x_2204_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__18, &l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__18_once, _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__18);
v___x_2205_ = lean_string_append(v___x_2204_, v_a_2200_);
lean_dec(v_a_2200_);
if (v_isShared_2203_ == 0)
{
lean_ctor_set(v___x_2202_, 0, v___x_2205_);
v___x_2207_ = v___x_2202_;
goto v_reusejp_2206_;
}
else
{
lean_object* v_reuseFailAlloc_2208_; 
v_reuseFailAlloc_2208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2208_, 0, v___x_2205_);
v___x_2207_ = v_reuseFailAlloc_2208_;
goto v_reusejp_2206_;
}
v_reusejp_2206_:
{
return v___x_2207_;
}
}
}
else
{
if (lean_obj_tag(v___x_2199_) == 0)
{
lean_object* v_a_2210_; lean_object* v___x_2212_; uint8_t v_isShared_2213_; uint8_t v_isSharedCheck_2217_; 
lean_dec(v_a_2197_);
lean_dec(v_a_2176_);
v_a_2210_ = lean_ctor_get(v___x_2199_, 0);
v_isSharedCheck_2217_ = !lean_is_exclusive(v___x_2199_);
if (v_isSharedCheck_2217_ == 0)
{
v___x_2212_ = v___x_2199_;
v_isShared_2213_ = v_isSharedCheck_2217_;
goto v_resetjp_2211_;
}
else
{
lean_inc(v_a_2210_);
lean_dec(v___x_2199_);
v___x_2212_ = lean_box(0);
v_isShared_2213_ = v_isSharedCheck_2217_;
goto v_resetjp_2211_;
}
v_resetjp_2211_:
{
lean_object* v___x_2215_; 
if (v_isShared_2213_ == 0)
{
lean_ctor_set_tag(v___x_2212_, 0);
v___x_2215_ = v___x_2212_;
goto v_reusejp_2214_;
}
else
{
lean_object* v_reuseFailAlloc_2216_; 
v_reuseFailAlloc_2216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2216_, 0, v_a_2210_);
v___x_2215_ = v_reuseFailAlloc_2216_;
goto v_reusejp_2214_;
}
v_reusejp_2214_:
{
return v___x_2215_;
}
}
}
else
{
lean_object* v_a_2218_; lean_object* v___x_2220_; uint8_t v_isShared_2221_; uint8_t v_isSharedCheck_2229_; 
v_a_2218_ = lean_ctor_get(v___x_2199_, 0);
v_isSharedCheck_2229_ = !lean_is_exclusive(v___x_2199_);
if (v_isSharedCheck_2229_ == 0)
{
v___x_2220_ = v___x_2199_;
v_isShared_2221_ = v_isSharedCheck_2229_;
goto v_resetjp_2219_;
}
else
{
lean_inc(v_a_2218_);
lean_dec(v___x_2199_);
v___x_2220_ = lean_box(0);
v_isShared_2221_ = v_isSharedCheck_2229_;
goto v_resetjp_2219_;
}
v_resetjp_2219_:
{
lean_object* v___x_2222_; uint8_t v___x_2223_; uint8_t v___x_2224_; uint8_t v___x_2225_; lean_object* v___x_2227_; 
v___x_2222_ = lean_alloc_ctor(0, 0, 3);
v___x_2223_ = lean_unbox(v_a_2176_);
lean_dec(v_a_2176_);
lean_ctor_set_uint8(v___x_2222_, 0, v___x_2223_);
v___x_2224_ = lean_unbox(v_a_2197_);
lean_dec(v_a_2197_);
lean_ctor_set_uint8(v___x_2222_, 1, v___x_2224_);
v___x_2225_ = lean_unbox(v_a_2218_);
lean_dec(v_a_2218_);
lean_ctor_set_uint8(v___x_2222_, 2, v___x_2225_);
if (v_isShared_2221_ == 0)
{
lean_ctor_set(v___x_2220_, 0, v___x_2222_);
v___x_2227_ = v___x_2220_;
goto v_reusejp_2226_;
}
else
{
lean_object* v_reuseFailAlloc_2228_; 
v_reuseFailAlloc_2228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2228_, 0, v___x_2222_);
v___x_2227_ = v_reuseFailAlloc_2228_;
goto v_reusejp_2226_;
}
v_reusejp_2226_:
{
return v___x_2227_;
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
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanImportKind_toJson(lean_object* v_x_2232_){
_start:
{
uint8_t v_isPrivate_2233_; uint8_t v_isAll_2234_; uint8_t v_metaKind_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; 
v_isPrivate_2233_ = lean_ctor_get_uint8(v_x_2232_, 0);
v_isAll_2234_ = lean_ctor_get_uint8(v_x_2232_, 1);
v_metaKind_2235_ = lean_ctor_get_uint8(v_x_2232_, 2);
v___x_2236_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__0));
v___x_2237_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2237_, 0, v_isPrivate_2233_);
v___x_2238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2238_, 0, v___x_2236_);
lean_ctor_set(v___x_2238_, 1, v___x_2237_);
v___x_2239_ = lean_box(0);
v___x_2240_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2240_, 0, v___x_2238_);
lean_ctor_set(v___x_2240_, 1, v___x_2239_);
v___x_2241_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__9));
v___x_2242_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2242_, 0, v_isAll_2234_);
v___x_2243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2243_, 0, v___x_2241_);
lean_ctor_set(v___x_2243_, 1, v___x_2242_);
v___x_2244_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2244_, 0, v___x_2243_);
lean_ctor_set(v___x_2244_, 1, v___x_2239_);
v___x_2245_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__14));
v___x_2246_ = l_Lean_Lsp_instToJsonLeanImportMetaKind_toJson(v_metaKind_2235_);
v___x_2247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2247_, 0, v___x_2245_);
lean_ctor_set(v___x_2247_, 1, v___x_2246_);
v___x_2248_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2248_, 0, v___x_2247_);
lean_ctor_set(v___x_2248_, 1, v___x_2239_);
v___x_2249_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2249_, 0, v___x_2248_);
lean_ctor_set(v___x_2249_, 1, v___x_2239_);
v___x_2250_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2250_, 0, v___x_2244_);
lean_ctor_set(v___x_2250_, 1, v___x_2249_);
v___x_2251_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2251_, 0, v___x_2240_);
lean_ctor_set(v___x_2251_, 1, v___x_2250_);
v___x_2252_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0));
v___x_2253_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_2251_, v___x_2252_);
v___x_2254_ = l_Lean_Json_mkObj(v___x_2253_);
lean_dec(v___x_2253_);
return v___x_2254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanImportKind_toJson___boxed(lean_object* v_x_2255_){
_start:
{
lean_object* v_res_2256_; 
v_res_2256_ = l_Lean_Lsp_instToJsonLeanImportKind_toJson(v_x_2255_);
lean_dec_ref(v_x_2255_);
return v_res_2256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImport_fromJson_spec__0(lean_object* v_j_2259_, lean_object* v_k_2260_){
_start:
{
lean_object* v___x_2261_; lean_object* v___x_2262_; 
v___x_2261_ = l_Lean_Json_getObjValD(v_j_2259_, v_k_2260_);
v___x_2262_ = l_Lean_Lsp_instFromJsonLeanModule_fromJson(v___x_2261_);
return v___x_2262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImport_fromJson_spec__0___boxed(lean_object* v_j_2263_, lean_object* v_k_2264_){
_start:
{
lean_object* v_res_2265_; 
v_res_2265_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImport_fromJson_spec__0(v_j_2263_, v_k_2264_);
lean_dec_ref(v_k_2264_);
return v_res_2265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImport_fromJson_spec__1(lean_object* v_j_2266_, lean_object* v_k_2267_){
_start:
{
lean_object* v___x_2268_; lean_object* v___x_2269_; 
v___x_2268_ = l_Lean_Json_getObjValD(v_j_2266_, v_k_2267_);
v___x_2269_ = l_Lean_Lsp_instFromJsonLeanImportKind_fromJson(v___x_2268_);
return v___x_2269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImport_fromJson_spec__1___boxed(lean_object* v_j_2270_, lean_object* v_k_2271_){
_start:
{
lean_object* v_res_2272_; 
v_res_2272_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImport_fromJson_spec__1(v_j_2270_, v_k_2271_);
lean_dec_ref(v_k_2271_);
return v_res_2272_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__3(void){
_start:
{
uint8_t v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; 
v___x_2279_ = 1;
v___x_2280_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__2));
v___x_2281_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2280_, v___x_2279_);
return v___x_2281_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__4(void){
_start:
{
lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; 
v___x_2282_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6));
v___x_2283_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__3);
v___x_2284_ = lean_string_append(v___x_2283_, v___x_2282_);
return v___x_2284_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__6(void){
_start:
{
uint8_t v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; 
v___x_2287_ = 1;
v___x_2288_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__5));
v___x_2289_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2288_, v___x_2287_);
return v___x_2289_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__7(void){
_start:
{
lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; 
v___x_2290_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__6);
v___x_2291_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__4);
v___x_2292_ = lean_string_append(v___x_2291_, v___x_2290_);
return v___x_2292_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__8(void){
_start:
{
lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; 
v___x_2293_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_2294_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__7);
v___x_2295_ = lean_string_append(v___x_2294_, v___x_2293_);
return v___x_2295_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__9(void){
_start:
{
lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; 
v___x_2296_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__11, &l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__11);
v___x_2297_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__4);
v___x_2298_ = lean_string_append(v___x_2297_, v___x_2296_);
return v___x_2298_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__10(void){
_start:
{
lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; 
v___x_2299_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_2300_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__9, &l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__9);
v___x_2301_ = lean_string_append(v___x_2300_, v___x_2299_);
return v___x_2301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanImport_fromJson(lean_object* v_json_2302_){
_start:
{
lean_object* v___x_2303_; lean_object* v___x_2304_; 
v___x_2303_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__0));
lean_inc(v_json_2302_);
v___x_2304_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImport_fromJson_spec__0(v_json_2302_, v___x_2303_);
if (lean_obj_tag(v___x_2304_) == 0)
{
lean_object* v_a_2305_; lean_object* v___x_2307_; uint8_t v_isShared_2308_; uint8_t v_isSharedCheck_2314_; 
lean_dec(v_json_2302_);
v_a_2305_ = lean_ctor_get(v___x_2304_, 0);
v_isSharedCheck_2314_ = !lean_is_exclusive(v___x_2304_);
if (v_isSharedCheck_2314_ == 0)
{
v___x_2307_ = v___x_2304_;
v_isShared_2308_ = v_isSharedCheck_2314_;
goto v_resetjp_2306_;
}
else
{
lean_inc(v_a_2305_);
lean_dec(v___x_2304_);
v___x_2307_ = lean_box(0);
v_isShared_2308_ = v_isSharedCheck_2314_;
goto v_resetjp_2306_;
}
v_resetjp_2306_:
{
lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2312_; 
v___x_2309_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__8);
v___x_2310_ = lean_string_append(v___x_2309_, v_a_2305_);
lean_dec(v_a_2305_);
if (v_isShared_2308_ == 0)
{
lean_ctor_set(v___x_2307_, 0, v___x_2310_);
v___x_2312_ = v___x_2307_;
goto v_reusejp_2311_;
}
else
{
lean_object* v_reuseFailAlloc_2313_; 
v_reuseFailAlloc_2313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2313_, 0, v___x_2310_);
v___x_2312_ = v_reuseFailAlloc_2313_;
goto v_reusejp_2311_;
}
v_reusejp_2311_:
{
return v___x_2312_;
}
}
}
else
{
if (lean_obj_tag(v___x_2304_) == 0)
{
lean_object* v_a_2315_; lean_object* v___x_2317_; uint8_t v_isShared_2318_; uint8_t v_isSharedCheck_2322_; 
lean_dec(v_json_2302_);
v_a_2315_ = lean_ctor_get(v___x_2304_, 0);
v_isSharedCheck_2322_ = !lean_is_exclusive(v___x_2304_);
if (v_isSharedCheck_2322_ == 0)
{
v___x_2317_ = v___x_2304_;
v_isShared_2318_ = v_isSharedCheck_2322_;
goto v_resetjp_2316_;
}
else
{
lean_inc(v_a_2315_);
lean_dec(v___x_2304_);
v___x_2317_ = lean_box(0);
v_isShared_2318_ = v_isSharedCheck_2322_;
goto v_resetjp_2316_;
}
v_resetjp_2316_:
{
lean_object* v___x_2320_; 
if (v_isShared_2318_ == 0)
{
lean_ctor_set_tag(v___x_2317_, 0);
v___x_2320_ = v___x_2317_;
goto v_reusejp_2319_;
}
else
{
lean_object* v_reuseFailAlloc_2321_; 
v_reuseFailAlloc_2321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2321_, 0, v_a_2315_);
v___x_2320_ = v_reuseFailAlloc_2321_;
goto v_reusejp_2319_;
}
v_reusejp_2319_:
{
return v___x_2320_;
}
}
}
else
{
lean_object* v_a_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; 
v_a_2323_ = lean_ctor_get(v___x_2304_, 0);
lean_inc(v_a_2323_);
lean_dec_ref_known(v___x_2304_, 1);
v___x_2324_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__9));
v___x_2325_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImport_fromJson_spec__1(v_json_2302_, v___x_2324_);
if (lean_obj_tag(v___x_2325_) == 0)
{
lean_object* v_a_2326_; lean_object* v___x_2328_; uint8_t v_isShared_2329_; uint8_t v_isSharedCheck_2335_; 
lean_dec(v_a_2323_);
v_a_2326_ = lean_ctor_get(v___x_2325_, 0);
v_isSharedCheck_2335_ = !lean_is_exclusive(v___x_2325_);
if (v_isSharedCheck_2335_ == 0)
{
v___x_2328_ = v___x_2325_;
v_isShared_2329_ = v_isSharedCheck_2335_;
goto v_resetjp_2327_;
}
else
{
lean_inc(v_a_2326_);
lean_dec(v___x_2325_);
v___x_2328_ = lean_box(0);
v_isShared_2329_ = v_isSharedCheck_2335_;
goto v_resetjp_2327_;
}
v_resetjp_2327_:
{
lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2333_; 
v___x_2330_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__10, &l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__10);
v___x_2331_ = lean_string_append(v___x_2330_, v_a_2326_);
lean_dec(v_a_2326_);
if (v_isShared_2329_ == 0)
{
lean_ctor_set(v___x_2328_, 0, v___x_2331_);
v___x_2333_ = v___x_2328_;
goto v_reusejp_2332_;
}
else
{
lean_object* v_reuseFailAlloc_2334_; 
v_reuseFailAlloc_2334_ = lean_alloc_ctor(0, 1, 0);
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
else
{
if (lean_obj_tag(v___x_2325_) == 0)
{
lean_object* v_a_2336_; lean_object* v___x_2338_; uint8_t v_isShared_2339_; uint8_t v_isSharedCheck_2343_; 
lean_dec(v_a_2323_);
v_a_2336_ = lean_ctor_get(v___x_2325_, 0);
v_isSharedCheck_2343_ = !lean_is_exclusive(v___x_2325_);
if (v_isSharedCheck_2343_ == 0)
{
v___x_2338_ = v___x_2325_;
v_isShared_2339_ = v_isSharedCheck_2343_;
goto v_resetjp_2337_;
}
else
{
lean_inc(v_a_2336_);
lean_dec(v___x_2325_);
v___x_2338_ = lean_box(0);
v_isShared_2339_ = v_isSharedCheck_2343_;
goto v_resetjp_2337_;
}
v_resetjp_2337_:
{
lean_object* v___x_2341_; 
if (v_isShared_2339_ == 0)
{
lean_ctor_set_tag(v___x_2338_, 0);
v___x_2341_ = v___x_2338_;
goto v_reusejp_2340_;
}
else
{
lean_object* v_reuseFailAlloc_2342_; 
v_reuseFailAlloc_2342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2342_, 0, v_a_2336_);
v___x_2341_ = v_reuseFailAlloc_2342_;
goto v_reusejp_2340_;
}
v_reusejp_2340_:
{
return v___x_2341_;
}
}
}
else
{
lean_object* v_a_2344_; lean_object* v___x_2346_; uint8_t v_isShared_2347_; uint8_t v_isSharedCheck_2352_; 
v_a_2344_ = lean_ctor_get(v___x_2325_, 0);
v_isSharedCheck_2352_ = !lean_is_exclusive(v___x_2325_);
if (v_isSharedCheck_2352_ == 0)
{
v___x_2346_ = v___x_2325_;
v_isShared_2347_ = v_isSharedCheck_2352_;
goto v_resetjp_2345_;
}
else
{
lean_inc(v_a_2344_);
lean_dec(v___x_2325_);
v___x_2346_ = lean_box(0);
v_isShared_2347_ = v_isSharedCheck_2352_;
goto v_resetjp_2345_;
}
v_resetjp_2345_:
{
lean_object* v___x_2348_; lean_object* v___x_2350_; 
v___x_2348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2348_, 0, v_a_2323_);
lean_ctor_set(v___x_2348_, 1, v_a_2344_);
if (v_isShared_2347_ == 0)
{
lean_ctor_set(v___x_2346_, 0, v___x_2348_);
v___x_2350_ = v___x_2346_;
goto v_reusejp_2349_;
}
else
{
lean_object* v_reuseFailAlloc_2351_; 
v_reuseFailAlloc_2351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2351_, 0, v___x_2348_);
v___x_2350_ = v_reuseFailAlloc_2351_;
goto v_reusejp_2349_;
}
v_reusejp_2349_:
{
return v___x_2350_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanImport_toJson(lean_object* v_x_2355_){
_start:
{
lean_object* v_module_2356_; lean_object* v_kind_2357_; lean_object* v___x_2359_; uint8_t v_isShared_2360_; uint8_t v_isSharedCheck_2377_; 
v_module_2356_ = lean_ctor_get(v_x_2355_, 0);
v_kind_2357_ = lean_ctor_get(v_x_2355_, 1);
v_isSharedCheck_2377_ = !lean_is_exclusive(v_x_2355_);
if (v_isSharedCheck_2377_ == 0)
{
v___x_2359_ = v_x_2355_;
v_isShared_2360_ = v_isSharedCheck_2377_;
goto v_resetjp_2358_;
}
else
{
lean_inc(v_kind_2357_);
lean_inc(v_module_2356_);
lean_dec(v_x_2355_);
v___x_2359_ = lean_box(0);
v_isShared_2360_ = v_isSharedCheck_2377_;
goto v_resetjp_2358_;
}
v_resetjp_2358_:
{
lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2364_; 
v___x_2361_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__0));
v___x_2362_ = l_Lean_Lsp_instToJsonLeanModule_toJson(v_module_2356_);
lean_dec_ref(v_module_2356_);
if (v_isShared_2360_ == 0)
{
lean_ctor_set(v___x_2359_, 1, v___x_2362_);
lean_ctor_set(v___x_2359_, 0, v___x_2361_);
v___x_2364_ = v___x_2359_;
goto v_reusejp_2363_;
}
else
{
lean_object* v_reuseFailAlloc_2376_; 
v_reuseFailAlloc_2376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2376_, 0, v___x_2361_);
lean_ctor_set(v_reuseFailAlloc_2376_, 1, v___x_2362_);
v___x_2364_ = v_reuseFailAlloc_2376_;
goto v_reusejp_2363_;
}
v_reusejp_2363_:
{
lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; 
v___x_2365_ = lean_box(0);
v___x_2366_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2366_, 0, v___x_2364_);
lean_ctor_set(v___x_2366_, 1, v___x_2365_);
v___x_2367_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__9));
v___x_2368_ = l_Lean_Lsp_instToJsonLeanImportKind_toJson(v_kind_2357_);
lean_dec_ref(v_kind_2357_);
v___x_2369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2369_, 0, v___x_2367_);
lean_ctor_set(v___x_2369_, 1, v___x_2368_);
v___x_2370_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2370_, 0, v___x_2369_);
lean_ctor_set(v___x_2370_, 1, v___x_2365_);
v___x_2371_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2371_, 0, v___x_2370_);
lean_ctor_set(v___x_2371_, 1, v___x_2365_);
v___x_2372_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2372_, 0, v___x_2366_);
lean_ctor_set(v___x_2372_, 1, v___x_2371_);
v___x_2373_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0));
v___x_2374_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_2372_, v___x_2373_);
v___x_2375_ = l_Lean_Json_mkObj(v___x_2374_);
lean_dec(v___x_2374_);
return v___x_2375_;
}
}
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__2(void){
_start:
{
uint8_t v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; 
v___x_2385_ = 1;
v___x_2386_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__1));
v___x_2387_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2386_, v___x_2385_);
return v___x_2387_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__3(void){
_start:
{
lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; 
v___x_2388_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6));
v___x_2389_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__2, &l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__2);
v___x_2390_ = lean_string_append(v___x_2389_, v___x_2388_);
return v___x_2390_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; 
v___x_2391_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__6);
v___x_2392_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__3);
v___x_2393_ = lean_string_append(v___x_2392_, v___x_2391_);
return v___x_2393_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__5(void){
_start:
{
lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; 
v___x_2394_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_2395_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__4);
v___x_2396_ = lean_string_append(v___x_2395_, v___x_2394_);
return v___x_2396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson(lean_object* v_json_2397_){
_start:
{
lean_object* v___x_2398_; lean_object* v___x_2399_; 
v___x_2398_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__0));
v___x_2399_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImport_fromJson_spec__0(v_json_2397_, v___x_2398_);
if (lean_obj_tag(v___x_2399_) == 0)
{
lean_object* v_a_2400_; lean_object* v___x_2402_; uint8_t v_isShared_2403_; uint8_t v_isSharedCheck_2409_; 
v_a_2400_ = lean_ctor_get(v___x_2399_, 0);
v_isSharedCheck_2409_ = !lean_is_exclusive(v___x_2399_);
if (v_isSharedCheck_2409_ == 0)
{
v___x_2402_ = v___x_2399_;
v_isShared_2403_ = v_isSharedCheck_2409_;
goto v_resetjp_2401_;
}
else
{
lean_inc(v_a_2400_);
lean_dec(v___x_2399_);
v___x_2402_ = lean_box(0);
v_isShared_2403_ = v_isSharedCheck_2409_;
goto v_resetjp_2401_;
}
v_resetjp_2401_:
{
lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2407_; 
v___x_2404_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__5, &l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__5);
v___x_2405_ = lean_string_append(v___x_2404_, v_a_2400_);
lean_dec(v_a_2400_);
if (v_isShared_2403_ == 0)
{
lean_ctor_set(v___x_2402_, 0, v___x_2405_);
v___x_2407_ = v___x_2402_;
goto v_reusejp_2406_;
}
else
{
lean_object* v_reuseFailAlloc_2408_; 
v_reuseFailAlloc_2408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2408_, 0, v___x_2405_);
v___x_2407_ = v_reuseFailAlloc_2408_;
goto v_reusejp_2406_;
}
v_reusejp_2406_:
{
return v___x_2407_;
}
}
}
else
{
if (lean_obj_tag(v___x_2399_) == 0)
{
lean_object* v_a_2410_; lean_object* v___x_2412_; uint8_t v_isShared_2413_; uint8_t v_isSharedCheck_2417_; 
v_a_2410_ = lean_ctor_get(v___x_2399_, 0);
v_isSharedCheck_2417_ = !lean_is_exclusive(v___x_2399_);
if (v_isSharedCheck_2417_ == 0)
{
v___x_2412_ = v___x_2399_;
v_isShared_2413_ = v_isSharedCheck_2417_;
goto v_resetjp_2411_;
}
else
{
lean_inc(v_a_2410_);
lean_dec(v___x_2399_);
v___x_2412_ = lean_box(0);
v_isShared_2413_ = v_isSharedCheck_2417_;
goto v_resetjp_2411_;
}
v_resetjp_2411_:
{
lean_object* v___x_2415_; 
if (v_isShared_2413_ == 0)
{
lean_ctor_set_tag(v___x_2412_, 0);
v___x_2415_ = v___x_2412_;
goto v_reusejp_2414_;
}
else
{
lean_object* v_reuseFailAlloc_2416_; 
v_reuseFailAlloc_2416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2416_, 0, v_a_2410_);
v___x_2415_ = v_reuseFailAlloc_2416_;
goto v_reusejp_2414_;
}
v_reusejp_2414_:
{
return v___x_2415_;
}
}
}
else
{
lean_object* v_a_2418_; lean_object* v___x_2420_; uint8_t v_isShared_2421_; uint8_t v_isSharedCheck_2425_; 
v_a_2418_ = lean_ctor_get(v___x_2399_, 0);
v_isSharedCheck_2425_ = !lean_is_exclusive(v___x_2399_);
if (v_isSharedCheck_2425_ == 0)
{
v___x_2420_ = v___x_2399_;
v_isShared_2421_ = v_isSharedCheck_2425_;
goto v_resetjp_2419_;
}
else
{
lean_inc(v_a_2418_);
lean_dec(v___x_2399_);
v___x_2420_ = lean_box(0);
v_isShared_2421_ = v_isSharedCheck_2425_;
goto v_resetjp_2419_;
}
v_resetjp_2419_:
{
lean_object* v___x_2423_; 
if (v_isShared_2421_ == 0)
{
v___x_2423_ = v___x_2420_;
goto v_reusejp_2422_;
}
else
{
lean_object* v_reuseFailAlloc_2424_; 
v_reuseFailAlloc_2424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2424_, 0, v_a_2418_);
v___x_2423_ = v_reuseFailAlloc_2424_;
goto v_reusejp_2422_;
}
v_reusejp_2422_:
{
return v___x_2423_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanModuleHierarchyImportsParams_toJson(lean_object* v_x_2428_){
_start:
{
lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; 
v___x_2429_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__0));
v___x_2430_ = l_Lean_Lsp_instToJsonLeanModule_toJson(v_x_2428_);
v___x_2431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2431_, 0, v___x_2429_);
lean_ctor_set(v___x_2431_, 1, v___x_2430_);
v___x_2432_ = lean_box(0);
v___x_2433_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2433_, 0, v___x_2431_);
lean_ctor_set(v___x_2433_, 1, v___x_2432_);
v___x_2434_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2434_, 0, v___x_2433_);
lean_ctor_set(v___x_2434_, 1, v___x_2432_);
v___x_2435_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0));
v___x_2436_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_2434_, v___x_2435_);
v___x_2437_ = l_Lean_Json_mkObj(v___x_2436_);
lean_dec(v___x_2436_);
return v___x_2437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanModuleHierarchyImportsParams_toJson___boxed(lean_object* v_x_2438_){
_start:
{
lean_object* v_res_2439_; 
v_res_2439_ = l_Lean_Lsp_instToJsonLeanModuleHierarchyImportsParams_toJson(v_x_2438_);
lean_dec_ref(v_x_2438_);
return v_res_2439_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__2(void){
_start:
{
uint8_t v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; 
v___x_2447_ = 1;
v___x_2448_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__1));
v___x_2449_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2448_, v___x_2447_);
return v___x_2449_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__3(void){
_start:
{
lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; 
v___x_2450_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6));
v___x_2451_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__2, &l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__2);
v___x_2452_ = lean_string_append(v___x_2451_, v___x_2450_);
return v___x_2452_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; 
v___x_2453_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__6);
v___x_2454_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__3);
v___x_2455_ = lean_string_append(v___x_2454_, v___x_2453_);
return v___x_2455_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__5(void){
_start:
{
lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; 
v___x_2456_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_2457_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__4);
v___x_2458_ = lean_string_append(v___x_2457_, v___x_2456_);
return v___x_2458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson(lean_object* v_json_2459_){
_start:
{
lean_object* v___x_2460_; lean_object* v___x_2461_; 
v___x_2460_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__0));
v___x_2461_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImport_fromJson_spec__0(v_json_2459_, v___x_2460_);
if (lean_obj_tag(v___x_2461_) == 0)
{
lean_object* v_a_2462_; lean_object* v___x_2464_; uint8_t v_isShared_2465_; uint8_t v_isSharedCheck_2471_; 
v_a_2462_ = lean_ctor_get(v___x_2461_, 0);
v_isSharedCheck_2471_ = !lean_is_exclusive(v___x_2461_);
if (v_isSharedCheck_2471_ == 0)
{
v___x_2464_ = v___x_2461_;
v_isShared_2465_ = v_isSharedCheck_2471_;
goto v_resetjp_2463_;
}
else
{
lean_inc(v_a_2462_);
lean_dec(v___x_2461_);
v___x_2464_ = lean_box(0);
v_isShared_2465_ = v_isSharedCheck_2471_;
goto v_resetjp_2463_;
}
v_resetjp_2463_:
{
lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2469_; 
v___x_2466_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__5, &l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__5);
v___x_2467_ = lean_string_append(v___x_2466_, v_a_2462_);
lean_dec(v_a_2462_);
if (v_isShared_2465_ == 0)
{
lean_ctor_set(v___x_2464_, 0, v___x_2467_);
v___x_2469_ = v___x_2464_;
goto v_reusejp_2468_;
}
else
{
lean_object* v_reuseFailAlloc_2470_; 
v_reuseFailAlloc_2470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2470_, 0, v___x_2467_);
v___x_2469_ = v_reuseFailAlloc_2470_;
goto v_reusejp_2468_;
}
v_reusejp_2468_:
{
return v___x_2469_;
}
}
}
else
{
if (lean_obj_tag(v___x_2461_) == 0)
{
lean_object* v_a_2472_; lean_object* v___x_2474_; uint8_t v_isShared_2475_; uint8_t v_isSharedCheck_2479_; 
v_a_2472_ = lean_ctor_get(v___x_2461_, 0);
v_isSharedCheck_2479_ = !lean_is_exclusive(v___x_2461_);
if (v_isSharedCheck_2479_ == 0)
{
v___x_2474_ = v___x_2461_;
v_isShared_2475_ = v_isSharedCheck_2479_;
goto v_resetjp_2473_;
}
else
{
lean_inc(v_a_2472_);
lean_dec(v___x_2461_);
v___x_2474_ = lean_box(0);
v_isShared_2475_ = v_isSharedCheck_2479_;
goto v_resetjp_2473_;
}
v_resetjp_2473_:
{
lean_object* v___x_2477_; 
if (v_isShared_2475_ == 0)
{
lean_ctor_set_tag(v___x_2474_, 0);
v___x_2477_ = v___x_2474_;
goto v_reusejp_2476_;
}
else
{
lean_object* v_reuseFailAlloc_2478_; 
v_reuseFailAlloc_2478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2478_, 0, v_a_2472_);
v___x_2477_ = v_reuseFailAlloc_2478_;
goto v_reusejp_2476_;
}
v_reusejp_2476_:
{
return v___x_2477_;
}
}
}
else
{
lean_object* v_a_2480_; lean_object* v___x_2482_; uint8_t v_isShared_2483_; uint8_t v_isSharedCheck_2487_; 
v_a_2480_ = lean_ctor_get(v___x_2461_, 0);
v_isSharedCheck_2487_ = !lean_is_exclusive(v___x_2461_);
if (v_isSharedCheck_2487_ == 0)
{
v___x_2482_ = v___x_2461_;
v_isShared_2483_ = v_isSharedCheck_2487_;
goto v_resetjp_2481_;
}
else
{
lean_inc(v_a_2480_);
lean_dec(v___x_2461_);
v___x_2482_ = lean_box(0);
v_isShared_2483_ = v_isSharedCheck_2487_;
goto v_resetjp_2481_;
}
v_resetjp_2481_:
{
lean_object* v___x_2485_; 
if (v_isShared_2483_ == 0)
{
v___x_2485_ = v___x_2482_;
goto v_reusejp_2484_;
}
else
{
lean_object* v_reuseFailAlloc_2486_; 
v_reuseFailAlloc_2486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2486_, 0, v_a_2480_);
v___x_2485_ = v_reuseFailAlloc_2486_;
goto v_reusejp_2484_;
}
v_reusejp_2484_:
{
return v___x_2485_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanModuleHierarchyImportedByParams_toJson(lean_object* v_x_2490_){
_start:
{
lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; 
v___x_2491_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__0));
v___x_2492_ = l_Lean_Lsp_instToJsonLeanModule_toJson(v_x_2490_);
v___x_2493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2493_, 0, v___x_2491_);
lean_ctor_set(v___x_2493_, 1, v___x_2492_);
v___x_2494_ = lean_box(0);
v___x_2495_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2495_, 0, v___x_2493_);
lean_ctor_set(v___x_2495_, 1, v___x_2494_);
v___x_2496_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2496_, 0, v___x_2495_);
lean_ctor_set(v___x_2496_, 1, v___x_2494_);
v___x_2497_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0));
v___x_2498_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_2496_, v___x_2497_);
v___x_2499_ = l_Lean_Json_mkObj(v___x_2498_);
lean_dec(v___x_2498_);
return v___x_2499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanModuleHierarchyImportedByParams_toJson___boxed(lean_object* v_x_2500_){
_start:
{
lean_object* v_res_2501_; 
v_res_2501_ = l_Lean_Lsp_instToJsonLeanModuleHierarchyImportedByParams_toJson(v_x_2500_);
lean_dec_ref(v_x_2500_);
return v_res_2501_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__2(void){
_start:
{
uint8_t v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; 
v___x_2509_ = 1;
v___x_2510_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__1));
v___x_2511_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2510_, v___x_2509_);
return v___x_2511_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__3(void){
_start:
{
lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; 
v___x_2512_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6));
v___x_2513_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__2, &l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__2);
v___x_2514_ = lean_string_append(v___x_2513_, v___x_2512_);
return v___x_2514_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; 
v___x_2515_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__6, &l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__6);
v___x_2516_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__3);
v___x_2517_ = lean_string_append(v___x_2516_, v___x_2515_);
return v___x_2517_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__5(void){
_start:
{
lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; 
v___x_2518_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_2519_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__4);
v___x_2520_ = lean_string_append(v___x_2519_, v___x_2518_);
return v___x_2520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson(lean_object* v_json_2521_){
_start:
{
lean_object* v___x_2522_; lean_object* v___x_2523_; 
v___x_2522_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__0));
v___x_2523_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson_spec__0(v_json_2521_, v___x_2522_);
if (lean_obj_tag(v___x_2523_) == 0)
{
lean_object* v_a_2524_; lean_object* v___x_2526_; uint8_t v_isShared_2527_; uint8_t v_isSharedCheck_2533_; 
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
v___x_2528_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__5, &l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__5);
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
if (lean_obj_tag(v___x_2523_) == 0)
{
lean_object* v_a_2534_; lean_object* v___x_2536_; uint8_t v_isShared_2537_; uint8_t v_isSharedCheck_2541_; 
v_a_2534_ = lean_ctor_get(v___x_2523_, 0);
v_isSharedCheck_2541_ = !lean_is_exclusive(v___x_2523_);
if (v_isSharedCheck_2541_ == 0)
{
v___x_2536_ = v___x_2523_;
v_isShared_2537_ = v_isSharedCheck_2541_;
goto v_resetjp_2535_;
}
else
{
lean_inc(v_a_2534_);
lean_dec(v___x_2523_);
v___x_2536_ = lean_box(0);
v_isShared_2537_ = v_isSharedCheck_2541_;
goto v_resetjp_2535_;
}
v_resetjp_2535_:
{
lean_object* v___x_2539_; 
if (v_isShared_2537_ == 0)
{
lean_ctor_set_tag(v___x_2536_, 0);
v___x_2539_ = v___x_2536_;
goto v_reusejp_2538_;
}
else
{
lean_object* v_reuseFailAlloc_2540_; 
v_reuseFailAlloc_2540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2540_, 0, v_a_2534_);
v___x_2539_ = v_reuseFailAlloc_2540_;
goto v_reusejp_2538_;
}
v_reusejp_2538_:
{
return v___x_2539_;
}
}
}
else
{
lean_object* v_a_2542_; lean_object* v___x_2544_; uint8_t v_isShared_2545_; uint8_t v_isSharedCheck_2549_; 
v_a_2542_ = lean_ctor_get(v___x_2523_, 0);
v_isSharedCheck_2549_ = !lean_is_exclusive(v___x_2523_);
if (v_isSharedCheck_2549_ == 0)
{
v___x_2544_ = v___x_2523_;
v_isShared_2545_ = v_isSharedCheck_2549_;
goto v_resetjp_2543_;
}
else
{
lean_inc(v_a_2542_);
lean_dec(v___x_2523_);
v___x_2544_ = lean_box(0);
v_isShared_2545_ = v_isSharedCheck_2549_;
goto v_resetjp_2543_;
}
v_resetjp_2543_:
{
lean_object* v___x_2547_; 
if (v_isShared_2545_ == 0)
{
v___x_2547_ = v___x_2544_;
goto v_reusejp_2546_;
}
else
{
lean_object* v_reuseFailAlloc_2548_; 
v_reuseFailAlloc_2548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2548_, 0, v_a_2542_);
v___x_2547_ = v_reuseFailAlloc_2548_;
goto v_reusejp_2546_;
}
v_reusejp_2546_:
{
return v___x_2547_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRpcConnectParams_toJson(lean_object* v_x_2552_){
_start:
{
lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; 
v___x_2553_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__0));
v___x_2554_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2554_, 0, v_x_2552_);
v___x_2555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2555_, 0, v___x_2553_);
lean_ctor_set(v___x_2555_, 1, v___x_2554_);
v___x_2556_ = lean_box(0);
v___x_2557_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2557_, 0, v___x_2555_);
lean_ctor_set(v___x_2557_, 1, v___x_2556_);
v___x_2558_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2558_, 0, v___x_2557_);
lean_ctor_set(v___x_2558_, 1, v___x_2556_);
v___x_2559_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0));
v___x_2560_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_2558_, v___x_2559_);
v___x_2561_ = l_Lean_Json_mkObj(v___x_2560_);
lean_dec(v___x_2560_);
return v___x_2561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcConnected_fromJson_spec__0(lean_object* v_j_2564_, lean_object* v_k_2565_){
_start:
{
lean_object* v___x_2566_; lean_object* v___x_2567_; 
v___x_2566_ = l_Lean_Json_getObjValD(v_j_2564_, v_k_2565_);
v___x_2567_ = l_Lean_UInt64_fromJson_x3f(v___x_2566_);
return v___x_2567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcConnected_fromJson_spec__0___boxed(lean_object* v_j_2568_, lean_object* v_k_2569_){
_start:
{
lean_object* v_res_2570_; 
v_res_2570_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcConnected_fromJson_spec__0(v_j_2568_, v_k_2569_);
lean_dec_ref(v_k_2569_);
return v_res_2570_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__3(void){
_start:
{
uint8_t v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; 
v___x_2577_ = 1;
v___x_2578_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__2));
v___x_2579_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2578_, v___x_2577_);
return v___x_2579_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__4(void){
_start:
{
lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; 
v___x_2580_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6));
v___x_2581_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__3, &l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__3);
v___x_2582_ = lean_string_append(v___x_2581_, v___x_2580_);
return v___x_2582_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__6(void){
_start:
{
uint8_t v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; 
v___x_2585_ = 1;
v___x_2586_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__5));
v___x_2587_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2586_, v___x_2585_);
return v___x_2587_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__7(void){
_start:
{
lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; 
v___x_2588_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__6, &l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__6);
v___x_2589_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__4, &l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__4);
v___x_2590_ = lean_string_append(v___x_2589_, v___x_2588_);
return v___x_2590_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__8(void){
_start:
{
lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; 
v___x_2591_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_2592_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__7, &l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__7);
v___x_2593_ = lean_string_append(v___x_2592_, v___x_2591_);
return v___x_2593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonRpcConnected_fromJson(lean_object* v_json_2594_){
_start:
{
lean_object* v___x_2595_; lean_object* v___x_2596_; 
v___x_2595_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__0));
v___x_2596_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcConnected_fromJson_spec__0(v_json_2594_, v___x_2595_);
if (lean_obj_tag(v___x_2596_) == 0)
{
lean_object* v_a_2597_; lean_object* v___x_2599_; uint8_t v_isShared_2600_; uint8_t v_isSharedCheck_2606_; 
v_a_2597_ = lean_ctor_get(v___x_2596_, 0);
v_isSharedCheck_2606_ = !lean_is_exclusive(v___x_2596_);
if (v_isSharedCheck_2606_ == 0)
{
v___x_2599_ = v___x_2596_;
v_isShared_2600_ = v_isSharedCheck_2606_;
goto v_resetjp_2598_;
}
else
{
lean_inc(v_a_2597_);
lean_dec(v___x_2596_);
v___x_2599_ = lean_box(0);
v_isShared_2600_ = v_isSharedCheck_2606_;
goto v_resetjp_2598_;
}
v_resetjp_2598_:
{
lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2604_; 
v___x_2601_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__8, &l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__8);
v___x_2602_ = lean_string_append(v___x_2601_, v_a_2597_);
lean_dec(v_a_2597_);
if (v_isShared_2600_ == 0)
{
lean_ctor_set(v___x_2599_, 0, v___x_2602_);
v___x_2604_ = v___x_2599_;
goto v_reusejp_2603_;
}
else
{
lean_object* v_reuseFailAlloc_2605_; 
v_reuseFailAlloc_2605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2605_, 0, v___x_2602_);
v___x_2604_ = v_reuseFailAlloc_2605_;
goto v_reusejp_2603_;
}
v_reusejp_2603_:
{
return v___x_2604_;
}
}
}
else
{
if (lean_obj_tag(v___x_2596_) == 0)
{
lean_object* v_a_2607_; lean_object* v___x_2609_; uint8_t v_isShared_2610_; uint8_t v_isSharedCheck_2614_; 
v_a_2607_ = lean_ctor_get(v___x_2596_, 0);
v_isSharedCheck_2614_ = !lean_is_exclusive(v___x_2596_);
if (v_isSharedCheck_2614_ == 0)
{
v___x_2609_ = v___x_2596_;
v_isShared_2610_ = v_isSharedCheck_2614_;
goto v_resetjp_2608_;
}
else
{
lean_inc(v_a_2607_);
lean_dec(v___x_2596_);
v___x_2609_ = lean_box(0);
v_isShared_2610_ = v_isSharedCheck_2614_;
goto v_resetjp_2608_;
}
v_resetjp_2608_:
{
lean_object* v___x_2612_; 
if (v_isShared_2610_ == 0)
{
lean_ctor_set_tag(v___x_2609_, 0);
v___x_2612_ = v___x_2609_;
goto v_reusejp_2611_;
}
else
{
lean_object* v_reuseFailAlloc_2613_; 
v_reuseFailAlloc_2613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2613_, 0, v_a_2607_);
v___x_2612_ = v_reuseFailAlloc_2613_;
goto v_reusejp_2611_;
}
v_reusejp_2611_:
{
return v___x_2612_;
}
}
}
else
{
lean_object* v_a_2615_; lean_object* v___x_2617_; uint8_t v_isShared_2618_; uint8_t v_isSharedCheck_2622_; 
v_a_2615_ = lean_ctor_get(v___x_2596_, 0);
v_isSharedCheck_2622_ = !lean_is_exclusive(v___x_2596_);
if (v_isSharedCheck_2622_ == 0)
{
v___x_2617_ = v___x_2596_;
v_isShared_2618_ = v_isSharedCheck_2622_;
goto v_resetjp_2616_;
}
else
{
lean_inc(v_a_2615_);
lean_dec(v___x_2596_);
v___x_2617_ = lean_box(0);
v_isShared_2618_ = v_isSharedCheck_2622_;
goto v_resetjp_2616_;
}
v_resetjp_2616_:
{
lean_object* v___x_2620_; 
if (v_isShared_2618_ == 0)
{
v___x_2620_ = v___x_2617_;
goto v_reusejp_2619_;
}
else
{
lean_object* v_reuseFailAlloc_2621_; 
v_reuseFailAlloc_2621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2621_, 0, v_a_2615_);
v___x_2620_ = v_reuseFailAlloc_2621_;
goto v_reusejp_2619_;
}
v_reusejp_2619_:
{
return v___x_2620_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRpcConnected_toJson(uint64_t v_x_2625_){
_start:
{
lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; 
v___x_2626_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__0));
v___x_2627_ = lean_uint64_to_nat(v_x_2625_);
v___x_2628_ = l_Lean_bignumToJson(v___x_2627_);
v___x_2629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2629_, 0, v___x_2626_);
lean_ctor_set(v___x_2629_, 1, v___x_2628_);
v___x_2630_ = lean_box(0);
v___x_2631_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2631_, 0, v___x_2629_);
lean_ctor_set(v___x_2631_, 1, v___x_2630_);
v___x_2632_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2632_, 0, v___x_2631_);
lean_ctor_set(v___x_2632_, 1, v___x_2630_);
v___x_2633_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0));
v___x_2634_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_2632_, v___x_2633_);
v___x_2635_ = l_Lean_Json_mkObj(v___x_2634_);
lean_dec(v___x_2634_);
return v___x_2635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRpcConnected_toJson___boxed(lean_object* v_x_2636_){
_start:
{
uint64_t v_x_30__boxed_2637_; lean_object* v_res_2638_; 
v_x_30__boxed_2637_ = lean_unbox_uint64(v_x_2636_);
lean_dec_ref(v_x_2636_);
v_res_2638_ = l_Lean_Lsp_instToJsonRpcConnected_toJson(v_x_30__boxed_2637_);
return v_res_2638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcCallParams_fromJson_spec__0(lean_object* v_j_2641_, lean_object* v_k_2642_){
_start:
{
lean_object* v___x_2643_; lean_object* v___x_2644_; 
v___x_2643_ = l_Lean_Json_getObjValD(v_j_2641_, v_k_2642_);
v___x_2644_ = l_Lean_Name_fromJson_x3f(v___x_2643_);
return v___x_2644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcCallParams_fromJson_spec__0___boxed(lean_object* v_j_2645_, lean_object* v_k_2646_){
_start:
{
lean_object* v_res_2647_; 
v_res_2647_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcCallParams_fromJson_spec__0(v_j_2645_, v_k_2646_);
lean_dec_ref(v_k_2646_);
return v_res_2647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcCallParams_fromJson_spec__1(lean_object* v_j_2648_, lean_object* v_k_2649_){
_start:
{
lean_object* v___x_2650_; lean_object* v___x_2651_; 
v___x_2650_ = l_Lean_Json_getObjValD(v_j_2648_, v_k_2649_);
v___x_2651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2651_, 0, v___x_2650_);
return v___x_2651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcCallParams_fromJson_spec__1___boxed(lean_object* v_j_2652_, lean_object* v_k_2653_){
_start:
{
lean_object* v_res_2654_; 
v_res_2654_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcCallParams_fromJson_spec__1(v_j_2652_, v_k_2653_);
lean_dec_ref(v_k_2653_);
return v_res_2654_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__2(void){
_start:
{
uint8_t v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; 
v___x_2660_ = 1;
v___x_2661_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__1));
v___x_2662_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2661_, v___x_2660_);
return v___x_2662_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__3(void){
_start:
{
lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; 
v___x_2663_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6));
v___x_2664_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__2, &l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__2);
v___x_2665_ = lean_string_append(v___x_2664_, v___x_2663_);
return v___x_2665_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; 
v___x_2666_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9, &l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9);
v___x_2667_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__3);
v___x_2668_ = lean_string_append(v___x_2667_, v___x_2666_);
return v___x_2668_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__5(void){
_start:
{
lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; 
v___x_2669_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_2670_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__4);
v___x_2671_ = lean_string_append(v___x_2670_, v___x_2669_);
return v___x_2671_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__6(void){
_start:
{
lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; 
v___x_2672_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__8);
v___x_2673_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__3);
v___x_2674_ = lean_string_append(v___x_2673_, v___x_2672_);
return v___x_2674_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__7(void){
_start:
{
lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; 
v___x_2675_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_2676_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__6, &l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__6);
v___x_2677_ = lean_string_append(v___x_2676_, v___x_2675_);
return v___x_2677_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__8(void){
_start:
{
lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; 
v___x_2678_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__6, &l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__6);
v___x_2679_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__3);
v___x_2680_ = lean_string_append(v___x_2679_, v___x_2678_);
return v___x_2680_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__9(void){
_start:
{
lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; 
v___x_2681_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_2682_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__8);
v___x_2683_ = lean_string_append(v___x_2682_, v___x_2681_);
return v___x_2683_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__12(void){
_start:
{
uint8_t v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; 
v___x_2687_ = 1;
v___x_2688_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__11));
v___x_2689_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2688_, v___x_2687_);
return v___x_2689_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__13(void){
_start:
{
lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; 
v___x_2690_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__12, &l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__12);
v___x_2691_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__3);
v___x_2692_ = lean_string_append(v___x_2691_, v___x_2690_);
return v___x_2692_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__14(void){
_start:
{
lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; 
v___x_2693_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_2694_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__13, &l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__13);
v___x_2695_ = lean_string_append(v___x_2694_, v___x_2693_);
return v___x_2695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonRpcCallParams_fromJson(lean_object* v_json_2697_){
_start:
{
lean_object* v___x_2698_; lean_object* v___x_2699_; 
v___x_2698_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__0));
lean_inc(v_json_2697_);
v___x_2699_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoalParams_fromJson_spec__0(v_json_2697_, v___x_2698_);
if (lean_obj_tag(v___x_2699_) == 0)
{
lean_object* v_a_2700_; lean_object* v___x_2702_; uint8_t v_isShared_2703_; uint8_t v_isSharedCheck_2709_; 
lean_dec(v_json_2697_);
v_a_2700_ = lean_ctor_get(v___x_2699_, 0);
v_isSharedCheck_2709_ = !lean_is_exclusive(v___x_2699_);
if (v_isSharedCheck_2709_ == 0)
{
v___x_2702_ = v___x_2699_;
v_isShared_2703_ = v_isSharedCheck_2709_;
goto v_resetjp_2701_;
}
else
{
lean_inc(v_a_2700_);
lean_dec(v___x_2699_);
v___x_2702_ = lean_box(0);
v_isShared_2703_ = v_isSharedCheck_2709_;
goto v_resetjp_2701_;
}
v_resetjp_2701_:
{
lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2707_; 
v___x_2704_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__5, &l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__5);
v___x_2705_ = lean_string_append(v___x_2704_, v_a_2700_);
lean_dec(v_a_2700_);
if (v_isShared_2703_ == 0)
{
lean_ctor_set(v___x_2702_, 0, v___x_2705_);
v___x_2707_ = v___x_2702_;
goto v_reusejp_2706_;
}
else
{
lean_object* v_reuseFailAlloc_2708_; 
v_reuseFailAlloc_2708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2708_, 0, v___x_2705_);
v___x_2707_ = v_reuseFailAlloc_2708_;
goto v_reusejp_2706_;
}
v_reusejp_2706_:
{
return v___x_2707_;
}
}
}
else
{
if (lean_obj_tag(v___x_2699_) == 0)
{
lean_object* v_a_2710_; lean_object* v___x_2712_; uint8_t v_isShared_2713_; uint8_t v_isSharedCheck_2717_; 
lean_dec(v_json_2697_);
v_a_2710_ = lean_ctor_get(v___x_2699_, 0);
v_isSharedCheck_2717_ = !lean_is_exclusive(v___x_2699_);
if (v_isSharedCheck_2717_ == 0)
{
v___x_2712_ = v___x_2699_;
v_isShared_2713_ = v_isSharedCheck_2717_;
goto v_resetjp_2711_;
}
else
{
lean_inc(v_a_2710_);
lean_dec(v___x_2699_);
v___x_2712_ = lean_box(0);
v_isShared_2713_ = v_isSharedCheck_2717_;
goto v_resetjp_2711_;
}
v_resetjp_2711_:
{
lean_object* v___x_2715_; 
if (v_isShared_2713_ == 0)
{
lean_ctor_set_tag(v___x_2712_, 0);
v___x_2715_ = v___x_2712_;
goto v_reusejp_2714_;
}
else
{
lean_object* v_reuseFailAlloc_2716_; 
v_reuseFailAlloc_2716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2716_, 0, v_a_2710_);
v___x_2715_ = v_reuseFailAlloc_2716_;
goto v_reusejp_2714_;
}
v_reusejp_2714_:
{
return v___x_2715_;
}
}
}
else
{
lean_object* v_a_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; 
v_a_2718_ = lean_ctor_get(v___x_2699_, 0);
lean_inc(v_a_2718_);
lean_dec_ref_known(v___x_2699_, 1);
v___x_2719_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__6));
lean_inc(v_json_2697_);
v___x_2720_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoalParams_fromJson_spec__1(v_json_2697_, v___x_2719_);
if (lean_obj_tag(v___x_2720_) == 0)
{
lean_object* v_a_2721_; lean_object* v___x_2723_; uint8_t v_isShared_2724_; uint8_t v_isSharedCheck_2730_; 
lean_dec(v_a_2718_);
lean_dec(v_json_2697_);
v_a_2721_ = lean_ctor_get(v___x_2720_, 0);
v_isSharedCheck_2730_ = !lean_is_exclusive(v___x_2720_);
if (v_isSharedCheck_2730_ == 0)
{
v___x_2723_ = v___x_2720_;
v_isShared_2724_ = v_isSharedCheck_2730_;
goto v_resetjp_2722_;
}
else
{
lean_inc(v_a_2721_);
lean_dec(v___x_2720_);
v___x_2723_ = lean_box(0);
v_isShared_2724_ = v_isSharedCheck_2730_;
goto v_resetjp_2722_;
}
v_resetjp_2722_:
{
lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2728_; 
v___x_2725_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__7);
v___x_2726_ = lean_string_append(v___x_2725_, v_a_2721_);
lean_dec(v_a_2721_);
if (v_isShared_2724_ == 0)
{
lean_ctor_set(v___x_2723_, 0, v___x_2726_);
v___x_2728_ = v___x_2723_;
goto v_reusejp_2727_;
}
else
{
lean_object* v_reuseFailAlloc_2729_; 
v_reuseFailAlloc_2729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2729_, 0, v___x_2726_);
v___x_2728_ = v_reuseFailAlloc_2729_;
goto v_reusejp_2727_;
}
v_reusejp_2727_:
{
return v___x_2728_;
}
}
}
else
{
if (lean_obj_tag(v___x_2720_) == 0)
{
lean_object* v_a_2731_; lean_object* v___x_2733_; uint8_t v_isShared_2734_; uint8_t v_isSharedCheck_2738_; 
lean_dec(v_a_2718_);
lean_dec(v_json_2697_);
v_a_2731_ = lean_ctor_get(v___x_2720_, 0);
v_isSharedCheck_2738_ = !lean_is_exclusive(v___x_2720_);
if (v_isSharedCheck_2738_ == 0)
{
v___x_2733_ = v___x_2720_;
v_isShared_2734_ = v_isSharedCheck_2738_;
goto v_resetjp_2732_;
}
else
{
lean_inc(v_a_2731_);
lean_dec(v___x_2720_);
v___x_2733_ = lean_box(0);
v_isShared_2734_ = v_isSharedCheck_2738_;
goto v_resetjp_2732_;
}
v_resetjp_2732_:
{
lean_object* v___x_2736_; 
if (v_isShared_2734_ == 0)
{
lean_ctor_set_tag(v___x_2733_, 0);
v___x_2736_ = v___x_2733_;
goto v_reusejp_2735_;
}
else
{
lean_object* v_reuseFailAlloc_2737_; 
v_reuseFailAlloc_2737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2737_, 0, v_a_2731_);
v___x_2736_ = v_reuseFailAlloc_2737_;
goto v_reusejp_2735_;
}
v_reusejp_2735_:
{
return v___x_2736_;
}
}
}
else
{
lean_object* v_a_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; 
v_a_2739_ = lean_ctor_get(v___x_2720_, 0);
lean_inc(v_a_2739_);
lean_dec_ref_known(v___x_2720_, 1);
v___x_2740_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__0));
lean_inc(v_json_2697_);
v___x_2741_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcConnected_fromJson_spec__0(v_json_2697_, v___x_2740_);
if (lean_obj_tag(v___x_2741_) == 0)
{
lean_object* v_a_2742_; lean_object* v___x_2744_; uint8_t v_isShared_2745_; uint8_t v_isSharedCheck_2751_; 
lean_dec(v_a_2739_);
lean_dec(v_a_2718_);
lean_dec(v_json_2697_);
v_a_2742_ = lean_ctor_get(v___x_2741_, 0);
v_isSharedCheck_2751_ = !lean_is_exclusive(v___x_2741_);
if (v_isSharedCheck_2751_ == 0)
{
v___x_2744_ = v___x_2741_;
v_isShared_2745_ = v_isSharedCheck_2751_;
goto v_resetjp_2743_;
}
else
{
lean_inc(v_a_2742_);
lean_dec(v___x_2741_);
v___x_2744_ = lean_box(0);
v_isShared_2745_ = v_isSharedCheck_2751_;
goto v_resetjp_2743_;
}
v_resetjp_2743_:
{
lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2749_; 
v___x_2746_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__9, &l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__9);
v___x_2747_ = lean_string_append(v___x_2746_, v_a_2742_);
lean_dec(v_a_2742_);
if (v_isShared_2745_ == 0)
{
lean_ctor_set(v___x_2744_, 0, v___x_2747_);
v___x_2749_ = v___x_2744_;
goto v_reusejp_2748_;
}
else
{
lean_object* v_reuseFailAlloc_2750_; 
v_reuseFailAlloc_2750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2750_, 0, v___x_2747_);
v___x_2749_ = v_reuseFailAlloc_2750_;
goto v_reusejp_2748_;
}
v_reusejp_2748_:
{
return v___x_2749_;
}
}
}
else
{
if (lean_obj_tag(v___x_2741_) == 0)
{
lean_object* v_a_2752_; lean_object* v___x_2754_; uint8_t v_isShared_2755_; uint8_t v_isSharedCheck_2759_; 
lean_dec(v_a_2739_);
lean_dec(v_a_2718_);
lean_dec(v_json_2697_);
v_a_2752_ = lean_ctor_get(v___x_2741_, 0);
v_isSharedCheck_2759_ = !lean_is_exclusive(v___x_2741_);
if (v_isSharedCheck_2759_ == 0)
{
v___x_2754_ = v___x_2741_;
v_isShared_2755_ = v_isSharedCheck_2759_;
goto v_resetjp_2753_;
}
else
{
lean_inc(v_a_2752_);
lean_dec(v___x_2741_);
v___x_2754_ = lean_box(0);
v_isShared_2755_ = v_isSharedCheck_2759_;
goto v_resetjp_2753_;
}
v_resetjp_2753_:
{
lean_object* v___x_2757_; 
if (v_isShared_2755_ == 0)
{
lean_ctor_set_tag(v___x_2754_, 0);
v___x_2757_ = v___x_2754_;
goto v_reusejp_2756_;
}
else
{
lean_object* v_reuseFailAlloc_2758_; 
v_reuseFailAlloc_2758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2758_, 0, v_a_2752_);
v___x_2757_ = v_reuseFailAlloc_2758_;
goto v_reusejp_2756_;
}
v_reusejp_2756_:
{
return v___x_2757_;
}
}
}
else
{
lean_object* v_a_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; 
v_a_2760_ = lean_ctor_get(v___x_2741_, 0);
lean_inc(v_a_2760_);
lean_dec_ref_known(v___x_2741_, 1);
v___x_2761_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__10));
lean_inc(v_json_2697_);
v___x_2762_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcCallParams_fromJson_spec__0(v_json_2697_, v___x_2761_);
if (lean_obj_tag(v___x_2762_) == 0)
{
lean_object* v_a_2763_; lean_object* v___x_2765_; uint8_t v_isShared_2766_; uint8_t v_isSharedCheck_2772_; 
lean_dec(v_a_2760_);
lean_dec(v_a_2739_);
lean_dec(v_a_2718_);
lean_dec(v_json_2697_);
v_a_2763_ = lean_ctor_get(v___x_2762_, 0);
v_isSharedCheck_2772_ = !lean_is_exclusive(v___x_2762_);
if (v_isSharedCheck_2772_ == 0)
{
v___x_2765_ = v___x_2762_;
v_isShared_2766_ = v_isSharedCheck_2772_;
goto v_resetjp_2764_;
}
else
{
lean_inc(v_a_2763_);
lean_dec(v___x_2762_);
v___x_2765_ = lean_box(0);
v_isShared_2766_ = v_isSharedCheck_2772_;
goto v_resetjp_2764_;
}
v_resetjp_2764_:
{
lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2770_; 
v___x_2767_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__14, &l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__14_once, _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__14);
v___x_2768_ = lean_string_append(v___x_2767_, v_a_2763_);
lean_dec(v_a_2763_);
if (v_isShared_2766_ == 0)
{
lean_ctor_set(v___x_2765_, 0, v___x_2768_);
v___x_2770_ = v___x_2765_;
goto v_reusejp_2769_;
}
else
{
lean_object* v_reuseFailAlloc_2771_; 
v_reuseFailAlloc_2771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2771_, 0, v___x_2768_);
v___x_2770_ = v_reuseFailAlloc_2771_;
goto v_reusejp_2769_;
}
v_reusejp_2769_:
{
return v___x_2770_;
}
}
}
else
{
if (lean_obj_tag(v___x_2762_) == 0)
{
lean_object* v_a_2773_; lean_object* v___x_2775_; uint8_t v_isShared_2776_; uint8_t v_isSharedCheck_2780_; 
lean_dec(v_a_2760_);
lean_dec(v_a_2739_);
lean_dec(v_a_2718_);
lean_dec(v_json_2697_);
v_a_2773_ = lean_ctor_get(v___x_2762_, 0);
v_isSharedCheck_2780_ = !lean_is_exclusive(v___x_2762_);
if (v_isSharedCheck_2780_ == 0)
{
v___x_2775_ = v___x_2762_;
v_isShared_2776_ = v_isSharedCheck_2780_;
goto v_resetjp_2774_;
}
else
{
lean_inc(v_a_2773_);
lean_dec(v___x_2762_);
v___x_2775_ = lean_box(0);
v_isShared_2776_ = v_isSharedCheck_2780_;
goto v_resetjp_2774_;
}
v_resetjp_2774_:
{
lean_object* v___x_2778_; 
if (v_isShared_2776_ == 0)
{
lean_ctor_set_tag(v___x_2775_, 0);
v___x_2778_ = v___x_2775_;
goto v_reusejp_2777_;
}
else
{
lean_object* v_reuseFailAlloc_2779_; 
v_reuseFailAlloc_2779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2779_, 0, v_a_2773_);
v___x_2778_ = v_reuseFailAlloc_2779_;
goto v_reusejp_2777_;
}
v_reusejp_2777_:
{
return v___x_2778_;
}
}
}
else
{
lean_object* v_a_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v_a_2784_; lean_object* v___x_2786_; uint8_t v_isShared_2787_; uint8_t v_isSharedCheck_2794_; 
v_a_2781_ = lean_ctor_get(v___x_2762_, 0);
lean_inc(v_a_2781_);
lean_dec_ref_known(v___x_2762_, 1);
v___x_2782_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__15));
v___x_2783_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcCallParams_fromJson_spec__1(v_json_2697_, v___x_2782_);
v_a_2784_ = lean_ctor_get(v___x_2783_, 0);
v_isSharedCheck_2794_ = !lean_is_exclusive(v___x_2783_);
if (v_isSharedCheck_2794_ == 0)
{
v___x_2786_ = v___x_2783_;
v_isShared_2787_ = v_isSharedCheck_2794_;
goto v_resetjp_2785_;
}
else
{
lean_inc(v_a_2784_);
lean_dec(v___x_2783_);
v___x_2786_ = lean_box(0);
v_isShared_2787_ = v_isSharedCheck_2794_;
goto v_resetjp_2785_;
}
v_resetjp_2785_:
{
lean_object* v___x_2788_; lean_object* v___x_2789_; uint64_t v___x_2790_; lean_object* v___x_2792_; 
v___x_2788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2788_, 0, v_a_2718_);
lean_ctor_set(v___x_2788_, 1, v_a_2739_);
v___x_2789_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_2789_, 0, v___x_2788_);
lean_ctor_set(v___x_2789_, 1, v_a_2781_);
lean_ctor_set(v___x_2789_, 2, v_a_2784_);
v___x_2790_ = lean_unbox_uint64(v_a_2760_);
lean_dec(v_a_2760_);
lean_ctor_set_uint64(v___x_2789_, sizeof(void*)*3, v___x_2790_);
if (v_isShared_2787_ == 0)
{
lean_ctor_set(v___x_2786_, 0, v___x_2789_);
v___x_2792_ = v___x_2786_;
goto v_reusejp_2791_;
}
else
{
lean_object* v_reuseFailAlloc_2793_; 
v_reuseFailAlloc_2793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2793_, 0, v___x_2789_);
v___x_2792_ = v_reuseFailAlloc_2793_;
goto v_reusejp_2791_;
}
v_reusejp_2791_:
{
return v___x_2792_;
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
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRpcCallParams_toJson(lean_object* v_x_2797_){
_start:
{
lean_object* v_toTextDocumentPositionParams_2798_; uint64_t v_sessionId_2799_; lean_object* v_method_2800_; lean_object* v_params_2801_; lean_object* v_textDocument_2802_; lean_object* v_position_2803_; lean_object* v___x_2805_; uint8_t v_isShared_2806_; uint8_t v_isSharedCheck_2840_; 
v_toTextDocumentPositionParams_2798_ = lean_ctor_get(v_x_2797_, 0);
lean_inc_ref(v_toTextDocumentPositionParams_2798_);
v_sessionId_2799_ = lean_ctor_get_uint64(v_x_2797_, sizeof(void*)*3);
v_method_2800_ = lean_ctor_get(v_x_2797_, 1);
lean_inc(v_method_2800_);
v_params_2801_ = lean_ctor_get(v_x_2797_, 2);
lean_inc(v_params_2801_);
lean_dec_ref(v_x_2797_);
v_textDocument_2802_ = lean_ctor_get(v_toTextDocumentPositionParams_2798_, 0);
v_position_2803_ = lean_ctor_get(v_toTextDocumentPositionParams_2798_, 1);
v_isSharedCheck_2840_ = !lean_is_exclusive(v_toTextDocumentPositionParams_2798_);
if (v_isSharedCheck_2840_ == 0)
{
v___x_2805_ = v_toTextDocumentPositionParams_2798_;
v_isShared_2806_ = v_isSharedCheck_2840_;
goto v_resetjp_2804_;
}
else
{
lean_inc(v_position_2803_);
lean_inc(v_textDocument_2802_);
lean_dec(v_toTextDocumentPositionParams_2798_);
v___x_2805_ = lean_box(0);
v_isShared_2806_ = v_isSharedCheck_2840_;
goto v_resetjp_2804_;
}
v_resetjp_2804_:
{
lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2810_; 
v___x_2807_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__0));
v___x_2808_ = l_Lean_Lsp_instToJsonTextDocumentIdentifier_toJson(v_textDocument_2802_);
if (v_isShared_2806_ == 0)
{
lean_ctor_set(v___x_2805_, 1, v___x_2808_);
lean_ctor_set(v___x_2805_, 0, v___x_2807_);
v___x_2810_ = v___x_2805_;
goto v_reusejp_2809_;
}
else
{
lean_object* v_reuseFailAlloc_2839_; 
v_reuseFailAlloc_2839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2839_, 0, v___x_2807_);
lean_ctor_set(v_reuseFailAlloc_2839_, 1, v___x_2808_);
v___x_2810_ = v_reuseFailAlloc_2839_;
goto v_reusejp_2809_;
}
v_reusejp_2809_:
{
lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; uint8_t v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; 
v___x_2811_ = lean_box(0);
v___x_2812_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2812_, 0, v___x_2810_);
lean_ctor_set(v___x_2812_, 1, v___x_2811_);
v___x_2813_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__6));
v___x_2814_ = l_Lean_Lsp_instToJsonPosition_toJson(v_position_2803_);
v___x_2815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2815_, 0, v___x_2813_);
lean_ctor_set(v___x_2815_, 1, v___x_2814_);
v___x_2816_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2816_, 0, v___x_2815_);
lean_ctor_set(v___x_2816_, 1, v___x_2811_);
v___x_2817_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__0));
v___x_2818_ = lean_uint64_to_nat(v_sessionId_2799_);
v___x_2819_ = l_Lean_bignumToJson(v___x_2818_);
v___x_2820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2820_, 0, v___x_2817_);
lean_ctor_set(v___x_2820_, 1, v___x_2819_);
v___x_2821_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2821_, 0, v___x_2820_);
lean_ctor_set(v___x_2821_, 1, v___x_2811_);
v___x_2822_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__10));
v___x_2823_ = 1;
v___x_2824_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_method_2800_, v___x_2823_);
v___x_2825_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2825_, 0, v___x_2824_);
v___x_2826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2826_, 0, v___x_2822_);
lean_ctor_set(v___x_2826_, 1, v___x_2825_);
v___x_2827_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2827_, 0, v___x_2826_);
lean_ctor_set(v___x_2827_, 1, v___x_2811_);
v___x_2828_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__15));
v___x_2829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2829_, 0, v___x_2828_);
lean_ctor_set(v___x_2829_, 1, v_params_2801_);
v___x_2830_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2830_, 0, v___x_2829_);
lean_ctor_set(v___x_2830_, 1, v___x_2811_);
v___x_2831_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2831_, 0, v___x_2830_);
lean_ctor_set(v___x_2831_, 1, v___x_2811_);
v___x_2832_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2832_, 0, v___x_2827_);
lean_ctor_set(v___x_2832_, 1, v___x_2831_);
v___x_2833_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2833_, 0, v___x_2821_);
lean_ctor_set(v___x_2833_, 1, v___x_2832_);
v___x_2834_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2834_, 0, v___x_2816_);
lean_ctor_set(v___x_2834_, 1, v___x_2833_);
v___x_2835_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2835_, 0, v___x_2812_);
lean_ctor_set(v___x_2835_, 1, v___x_2834_);
v___x_2836_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0));
v___x_2837_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_2835_, v___x_2836_);
v___x_2838_ = l_Lean_Json_mkObj(v___x_2837_);
lean_dec(v___x_2837_);
return v___x_2838_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcReleaseParams_fromJson_spec__0_spec__0_spec__1(size_t v_sz_2843_, size_t v_i_2844_, lean_object* v_bs_2845_){
_start:
{
uint8_t v___x_2846_; 
v___x_2846_ = lean_usize_dec_lt(v_i_2844_, v_sz_2843_);
if (v___x_2846_ == 0)
{
lean_object* v___x_2847_; 
v___x_2847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2847_, 0, v_bs_2845_);
return v___x_2847_;
}
else
{
lean_object* v_v_2848_; lean_object* v___x_2849_; lean_object* v_bs_x27_2850_; size_t v___x_2851_; size_t v___x_2852_; lean_object* v___x_2853_; 
v_v_2848_ = lean_array_uget(v_bs_2845_, v_i_2844_);
v___x_2849_ = lean_unsigned_to_nat(0u);
v_bs_x27_2850_ = lean_array_uset(v_bs_2845_, v_i_2844_, v___x_2849_);
v___x_2851_ = ((size_t)1ULL);
v___x_2852_ = lean_usize_add(v_i_2844_, v___x_2851_);
v___x_2853_ = lean_array_uset(v_bs_x27_2850_, v_i_2844_, v_v_2848_);
v_i_2844_ = v___x_2852_;
v_bs_2845_ = v___x_2853_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcReleaseParams_fromJson_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_2855_, lean_object* v_i_2856_, lean_object* v_bs_2857_){
_start:
{
size_t v_sz_boxed_2858_; size_t v_i_boxed_2859_; lean_object* v_res_2860_; 
v_sz_boxed_2858_ = lean_unbox_usize(v_sz_2855_);
lean_dec(v_sz_2855_);
v_i_boxed_2859_ = lean_unbox_usize(v_i_2856_);
lean_dec(v_i_2856_);
v_res_2860_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcReleaseParams_fromJson_spec__0_spec__0_spec__1(v_sz_boxed_2858_, v_i_boxed_2859_, v_bs_2857_);
return v_res_2860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcReleaseParams_fromJson_spec__0_spec__0(lean_object* v_x_2861_){
_start:
{
if (lean_obj_tag(v_x_2861_) == 4)
{
lean_object* v_elems_2862_; size_t v_sz_2863_; size_t v___x_2864_; lean_object* v___x_2865_; 
v_elems_2862_ = lean_ctor_get(v_x_2861_, 0);
lean_inc_ref(v_elems_2862_);
lean_dec_ref_known(v_x_2861_, 1);
v_sz_2863_ = lean_array_size(v_elems_2862_);
v___x_2864_ = ((size_t)0ULL);
v___x_2865_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcReleaseParams_fromJson_spec__0_spec__0_spec__1(v_sz_2863_, v___x_2864_, v_elems_2862_);
return v___x_2865_;
}
else
{
lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; 
v___x_2866_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__1_spec__1___closed__0));
v___x_2867_ = lean_unsigned_to_nat(80u);
v___x_2868_ = l_Lean_Json_pretty(v_x_2861_, v___x_2867_);
v___x_2869_ = lean_string_append(v___x_2866_, v___x_2868_);
lean_dec_ref(v___x_2868_);
v___x_2870_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressKind___lam__0___closed__1));
v___x_2871_ = lean_string_append(v___x_2869_, v___x_2870_);
v___x_2872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2872_, 0, v___x_2871_);
return v___x_2872_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcReleaseParams_fromJson_spec__0(lean_object* v_j_2873_, lean_object* v_k_2874_){
_start:
{
lean_object* v___x_2875_; lean_object* v___x_2876_; 
v___x_2875_ = l_Lean_Json_getObjValD(v_j_2873_, v_k_2874_);
v___x_2876_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcReleaseParams_fromJson_spec__0_spec__0(v___x_2875_);
return v___x_2876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcReleaseParams_fromJson_spec__0___boxed(lean_object* v_j_2877_, lean_object* v_k_2878_){
_start:
{
lean_object* v_res_2879_; 
v_res_2879_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcReleaseParams_fromJson_spec__0(v_j_2877_, v_k_2878_);
lean_dec_ref(v_k_2878_);
return v_res_2879_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__2(void){
_start:
{
uint8_t v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; 
v___x_2885_ = 1;
v___x_2886_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__1));
v___x_2887_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2886_, v___x_2885_);
return v___x_2887_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__3(void){
_start:
{
lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; 
v___x_2888_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6));
v___x_2889_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__2, &l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__2);
v___x_2890_ = lean_string_append(v___x_2889_, v___x_2888_);
return v___x_2890_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; 
v___x_2891_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__6, &l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__6);
v___x_2892_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__3);
v___x_2893_ = lean_string_append(v___x_2892_, v___x_2891_);
return v___x_2893_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__5(void){
_start:
{
lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; 
v___x_2894_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_2895_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__4);
v___x_2896_ = lean_string_append(v___x_2895_, v___x_2894_);
return v___x_2896_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__6(void){
_start:
{
lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; 
v___x_2897_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__6, &l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__6);
v___x_2898_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__3);
v___x_2899_ = lean_string_append(v___x_2898_, v___x_2897_);
return v___x_2899_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__7(void){
_start:
{
lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; 
v___x_2900_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_2901_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__6, &l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__6);
v___x_2902_ = lean_string_append(v___x_2901_, v___x_2900_);
return v___x_2902_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__10(void){
_start:
{
uint8_t v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; 
v___x_2906_ = 1;
v___x_2907_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__9));
v___x_2908_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2907_, v___x_2906_);
return v___x_2908_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__11(void){
_start:
{
lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; 
v___x_2909_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__10, &l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__10);
v___x_2910_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__3);
v___x_2911_ = lean_string_append(v___x_2910_, v___x_2909_);
return v___x_2911_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__12(void){
_start:
{
lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; 
v___x_2912_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_2913_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__11, &l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__11);
v___x_2914_ = lean_string_append(v___x_2913_, v___x_2912_);
return v___x_2914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson(lean_object* v_json_2915_){
_start:
{
lean_object* v___x_2916_; lean_object* v___x_2917_; 
v___x_2916_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__0));
lean_inc(v_json_2915_);
v___x_2917_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson_spec__0(v_json_2915_, v___x_2916_);
if (lean_obj_tag(v___x_2917_) == 0)
{
lean_object* v_a_2918_; lean_object* v___x_2920_; uint8_t v_isShared_2921_; uint8_t v_isSharedCheck_2927_; 
lean_dec(v_json_2915_);
v_a_2918_ = lean_ctor_get(v___x_2917_, 0);
v_isSharedCheck_2927_ = !lean_is_exclusive(v___x_2917_);
if (v_isSharedCheck_2927_ == 0)
{
v___x_2920_ = v___x_2917_;
v_isShared_2921_ = v_isSharedCheck_2927_;
goto v_resetjp_2919_;
}
else
{
lean_inc(v_a_2918_);
lean_dec(v___x_2917_);
v___x_2920_ = lean_box(0);
v_isShared_2921_ = v_isSharedCheck_2927_;
goto v_resetjp_2919_;
}
v_resetjp_2919_:
{
lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2925_; 
v___x_2922_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__5, &l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__5);
v___x_2923_ = lean_string_append(v___x_2922_, v_a_2918_);
lean_dec(v_a_2918_);
if (v_isShared_2921_ == 0)
{
lean_ctor_set(v___x_2920_, 0, v___x_2923_);
v___x_2925_ = v___x_2920_;
goto v_reusejp_2924_;
}
else
{
lean_object* v_reuseFailAlloc_2926_; 
v_reuseFailAlloc_2926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2926_, 0, v___x_2923_);
v___x_2925_ = v_reuseFailAlloc_2926_;
goto v_reusejp_2924_;
}
v_reusejp_2924_:
{
return v___x_2925_;
}
}
}
else
{
if (lean_obj_tag(v___x_2917_) == 0)
{
lean_object* v_a_2928_; lean_object* v___x_2930_; uint8_t v_isShared_2931_; uint8_t v_isSharedCheck_2935_; 
lean_dec(v_json_2915_);
v_a_2928_ = lean_ctor_get(v___x_2917_, 0);
v_isSharedCheck_2935_ = !lean_is_exclusive(v___x_2917_);
if (v_isSharedCheck_2935_ == 0)
{
v___x_2930_ = v___x_2917_;
v_isShared_2931_ = v_isSharedCheck_2935_;
goto v_resetjp_2929_;
}
else
{
lean_inc(v_a_2928_);
lean_dec(v___x_2917_);
v___x_2930_ = lean_box(0);
v_isShared_2931_ = v_isSharedCheck_2935_;
goto v_resetjp_2929_;
}
v_resetjp_2929_:
{
lean_object* v___x_2933_; 
if (v_isShared_2931_ == 0)
{
lean_ctor_set_tag(v___x_2930_, 0);
v___x_2933_ = v___x_2930_;
goto v_reusejp_2932_;
}
else
{
lean_object* v_reuseFailAlloc_2934_; 
v_reuseFailAlloc_2934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2934_, 0, v_a_2928_);
v___x_2933_ = v_reuseFailAlloc_2934_;
goto v_reusejp_2932_;
}
v_reusejp_2932_:
{
return v___x_2933_;
}
}
}
else
{
lean_object* v_a_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; 
v_a_2936_ = lean_ctor_get(v___x_2917_, 0);
lean_inc(v_a_2936_);
lean_dec_ref_known(v___x_2917_, 1);
v___x_2937_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__0));
lean_inc(v_json_2915_);
v___x_2938_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcConnected_fromJson_spec__0(v_json_2915_, v___x_2937_);
if (lean_obj_tag(v___x_2938_) == 0)
{
lean_object* v_a_2939_; lean_object* v___x_2941_; uint8_t v_isShared_2942_; uint8_t v_isSharedCheck_2948_; 
lean_dec(v_a_2936_);
lean_dec(v_json_2915_);
v_a_2939_ = lean_ctor_get(v___x_2938_, 0);
v_isSharedCheck_2948_ = !lean_is_exclusive(v___x_2938_);
if (v_isSharedCheck_2948_ == 0)
{
v___x_2941_ = v___x_2938_;
v_isShared_2942_ = v_isSharedCheck_2948_;
goto v_resetjp_2940_;
}
else
{
lean_inc(v_a_2939_);
lean_dec(v___x_2938_);
v___x_2941_ = lean_box(0);
v_isShared_2942_ = v_isSharedCheck_2948_;
goto v_resetjp_2940_;
}
v_resetjp_2940_:
{
lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2946_; 
v___x_2943_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__7);
v___x_2944_ = lean_string_append(v___x_2943_, v_a_2939_);
lean_dec(v_a_2939_);
if (v_isShared_2942_ == 0)
{
lean_ctor_set(v___x_2941_, 0, v___x_2944_);
v___x_2946_ = v___x_2941_;
goto v_reusejp_2945_;
}
else
{
lean_object* v_reuseFailAlloc_2947_; 
v_reuseFailAlloc_2947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2947_, 0, v___x_2944_);
v___x_2946_ = v_reuseFailAlloc_2947_;
goto v_reusejp_2945_;
}
v_reusejp_2945_:
{
return v___x_2946_;
}
}
}
else
{
if (lean_obj_tag(v___x_2938_) == 0)
{
lean_object* v_a_2949_; lean_object* v___x_2951_; uint8_t v_isShared_2952_; uint8_t v_isSharedCheck_2956_; 
lean_dec(v_a_2936_);
lean_dec(v_json_2915_);
v_a_2949_ = lean_ctor_get(v___x_2938_, 0);
v_isSharedCheck_2956_ = !lean_is_exclusive(v___x_2938_);
if (v_isSharedCheck_2956_ == 0)
{
v___x_2951_ = v___x_2938_;
v_isShared_2952_ = v_isSharedCheck_2956_;
goto v_resetjp_2950_;
}
else
{
lean_inc(v_a_2949_);
lean_dec(v___x_2938_);
v___x_2951_ = lean_box(0);
v_isShared_2952_ = v_isSharedCheck_2956_;
goto v_resetjp_2950_;
}
v_resetjp_2950_:
{
lean_object* v___x_2954_; 
if (v_isShared_2952_ == 0)
{
lean_ctor_set_tag(v___x_2951_, 0);
v___x_2954_ = v___x_2951_;
goto v_reusejp_2953_;
}
else
{
lean_object* v_reuseFailAlloc_2955_; 
v_reuseFailAlloc_2955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2955_, 0, v_a_2949_);
v___x_2954_ = v_reuseFailAlloc_2955_;
goto v_reusejp_2953_;
}
v_reusejp_2953_:
{
return v___x_2954_;
}
}
}
else
{
lean_object* v_a_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; 
v_a_2957_ = lean_ctor_get(v___x_2938_, 0);
lean_inc(v_a_2957_);
lean_dec_ref_known(v___x_2938_, 1);
v___x_2958_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__8));
v___x_2959_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcReleaseParams_fromJson_spec__0(v_json_2915_, v___x_2958_);
if (lean_obj_tag(v___x_2959_) == 0)
{
lean_object* v_a_2960_; lean_object* v___x_2962_; uint8_t v_isShared_2963_; uint8_t v_isSharedCheck_2969_; 
lean_dec(v_a_2957_);
lean_dec(v_a_2936_);
v_a_2960_ = lean_ctor_get(v___x_2959_, 0);
v_isSharedCheck_2969_ = !lean_is_exclusive(v___x_2959_);
if (v_isSharedCheck_2969_ == 0)
{
v___x_2962_ = v___x_2959_;
v_isShared_2963_ = v_isSharedCheck_2969_;
goto v_resetjp_2961_;
}
else
{
lean_inc(v_a_2960_);
lean_dec(v___x_2959_);
v___x_2962_ = lean_box(0);
v_isShared_2963_ = v_isSharedCheck_2969_;
goto v_resetjp_2961_;
}
v_resetjp_2961_:
{
lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2967_; 
v___x_2964_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__12, &l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__12);
v___x_2965_ = lean_string_append(v___x_2964_, v_a_2960_);
lean_dec(v_a_2960_);
if (v_isShared_2963_ == 0)
{
lean_ctor_set(v___x_2962_, 0, v___x_2965_);
v___x_2967_ = v___x_2962_;
goto v_reusejp_2966_;
}
else
{
lean_object* v_reuseFailAlloc_2968_; 
v_reuseFailAlloc_2968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2968_, 0, v___x_2965_);
v___x_2967_ = v_reuseFailAlloc_2968_;
goto v_reusejp_2966_;
}
v_reusejp_2966_:
{
return v___x_2967_;
}
}
}
else
{
if (lean_obj_tag(v___x_2959_) == 0)
{
lean_object* v_a_2970_; lean_object* v___x_2972_; uint8_t v_isShared_2973_; uint8_t v_isSharedCheck_2977_; 
lean_dec(v_a_2957_);
lean_dec(v_a_2936_);
v_a_2970_ = lean_ctor_get(v___x_2959_, 0);
v_isSharedCheck_2977_ = !lean_is_exclusive(v___x_2959_);
if (v_isSharedCheck_2977_ == 0)
{
v___x_2972_ = v___x_2959_;
v_isShared_2973_ = v_isSharedCheck_2977_;
goto v_resetjp_2971_;
}
else
{
lean_inc(v_a_2970_);
lean_dec(v___x_2959_);
v___x_2972_ = lean_box(0);
v_isShared_2973_ = v_isSharedCheck_2977_;
goto v_resetjp_2971_;
}
v_resetjp_2971_:
{
lean_object* v___x_2975_; 
if (v_isShared_2973_ == 0)
{
lean_ctor_set_tag(v___x_2972_, 0);
v___x_2975_ = v___x_2972_;
goto v_reusejp_2974_;
}
else
{
lean_object* v_reuseFailAlloc_2976_; 
v_reuseFailAlloc_2976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2976_, 0, v_a_2970_);
v___x_2975_ = v_reuseFailAlloc_2976_;
goto v_reusejp_2974_;
}
v_reusejp_2974_:
{
return v___x_2975_;
}
}
}
else
{
lean_object* v_a_2978_; lean_object* v___x_2980_; uint8_t v_isShared_2981_; uint8_t v_isSharedCheck_2987_; 
v_a_2978_ = lean_ctor_get(v___x_2959_, 0);
v_isSharedCheck_2987_ = !lean_is_exclusive(v___x_2959_);
if (v_isSharedCheck_2987_ == 0)
{
v___x_2980_ = v___x_2959_;
v_isShared_2981_ = v_isSharedCheck_2987_;
goto v_resetjp_2979_;
}
else
{
lean_inc(v_a_2978_);
lean_dec(v___x_2959_);
v___x_2980_ = lean_box(0);
v_isShared_2981_ = v_isSharedCheck_2987_;
goto v_resetjp_2979_;
}
v_resetjp_2979_:
{
lean_object* v___x_2982_; uint64_t v___x_2983_; lean_object* v___x_2985_; 
v___x_2982_ = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(v___x_2982_, 0, v_a_2936_);
lean_ctor_set(v___x_2982_, 1, v_a_2978_);
v___x_2983_ = lean_unbox_uint64(v_a_2957_);
lean_dec(v_a_2957_);
lean_ctor_set_uint64(v___x_2982_, sizeof(void*)*2, v___x_2983_);
if (v_isShared_2981_ == 0)
{
lean_ctor_set(v___x_2980_, 0, v___x_2982_);
v___x_2985_ = v___x_2980_;
goto v_reusejp_2984_;
}
else
{
lean_object* v_reuseFailAlloc_2986_; 
v_reuseFailAlloc_2986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2986_, 0, v___x_2982_);
v___x_2985_ = v_reuseFailAlloc_2986_;
goto v_reusejp_2984_;
}
v_reusejp_2984_:
{
return v___x_2985_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonRpcReleaseParams_toJson_spec__0_spec__0(size_t v_sz_2990_, size_t v_i_2991_, lean_object* v_bs_2992_){
_start:
{
uint8_t v___x_2993_; 
v___x_2993_ = lean_usize_dec_lt(v_i_2991_, v_sz_2990_);
if (v___x_2993_ == 0)
{
return v_bs_2992_;
}
else
{
lean_object* v_v_2994_; lean_object* v___x_2995_; lean_object* v_bs_x27_2996_; size_t v___x_2997_; size_t v___x_2998_; lean_object* v___x_2999_; 
v_v_2994_ = lean_array_uget(v_bs_2992_, v_i_2991_);
v___x_2995_ = lean_unsigned_to_nat(0u);
v_bs_x27_2996_ = lean_array_uset(v_bs_2992_, v_i_2991_, v___x_2995_);
v___x_2997_ = ((size_t)1ULL);
v___x_2998_ = lean_usize_add(v_i_2991_, v___x_2997_);
v___x_2999_ = lean_array_uset(v_bs_x27_2996_, v_i_2991_, v_v_2994_);
v_i_2991_ = v___x_2998_;
v_bs_2992_ = v___x_2999_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonRpcReleaseParams_toJson_spec__0_spec__0___boxed(lean_object* v_sz_3001_, lean_object* v_i_3002_, lean_object* v_bs_3003_){
_start:
{
size_t v_sz_boxed_3004_; size_t v_i_boxed_3005_; lean_object* v_res_3006_; 
v_sz_boxed_3004_ = lean_unbox_usize(v_sz_3001_);
lean_dec(v_sz_3001_);
v_i_boxed_3005_ = lean_unbox_usize(v_i_3002_);
lean_dec(v_i_3002_);
v_res_3006_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonRpcReleaseParams_toJson_spec__0_spec__0(v_sz_boxed_3004_, v_i_boxed_3005_, v_bs_3003_);
return v_res_3006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonRpcReleaseParams_toJson_spec__0(lean_object* v_a_3007_){
_start:
{
size_t v_sz_3008_; size_t v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; 
v_sz_3008_ = lean_array_size(v_a_3007_);
v___x_3009_ = ((size_t)0ULL);
v___x_3010_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonRpcReleaseParams_toJson_spec__0_spec__0(v_sz_3008_, v___x_3009_, v_a_3007_);
v___x_3011_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3011_, 0, v___x_3010_);
return v___x_3011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRpcReleaseParams_toJson(lean_object* v_x_3012_){
_start:
{
lean_object* v_uri_3013_; uint64_t v_sessionId_3014_; lean_object* v_refs_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; 
v_uri_3013_ = lean_ctor_get(v_x_3012_, 0);
lean_inc_ref(v_uri_3013_);
v_sessionId_3014_ = lean_ctor_get_uint64(v_x_3012_, sizeof(void*)*2);
v_refs_3015_ = lean_ctor_get(v_x_3012_, 1);
lean_inc_ref(v_refs_3015_);
lean_dec_ref(v_x_3012_);
v___x_3016_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__0));
v___x_3017_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3017_, 0, v_uri_3013_);
v___x_3018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3018_, 0, v___x_3016_);
lean_ctor_set(v___x_3018_, 1, v___x_3017_);
v___x_3019_ = lean_box(0);
v___x_3020_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3020_, 0, v___x_3018_);
lean_ctor_set(v___x_3020_, 1, v___x_3019_);
v___x_3021_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__0));
v___x_3022_ = lean_uint64_to_nat(v_sessionId_3014_);
v___x_3023_ = l_Lean_bignumToJson(v___x_3022_);
v___x_3024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3024_, 0, v___x_3021_);
lean_ctor_set(v___x_3024_, 1, v___x_3023_);
v___x_3025_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3025_, 0, v___x_3024_);
lean_ctor_set(v___x_3025_, 1, v___x_3019_);
v___x_3026_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__8));
v___x_3027_ = l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonRpcReleaseParams_toJson_spec__0(v_refs_3015_);
v___x_3028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3028_, 0, v___x_3026_);
lean_ctor_set(v___x_3028_, 1, v___x_3027_);
v___x_3029_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3029_, 0, v___x_3028_);
lean_ctor_set(v___x_3029_, 1, v___x_3019_);
v___x_3030_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3030_, 0, v___x_3029_);
lean_ctor_set(v___x_3030_, 1, v___x_3019_);
v___x_3031_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3031_, 0, v___x_3025_);
lean_ctor_set(v___x_3031_, 1, v___x_3030_);
v___x_3032_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3032_, 0, v___x_3020_);
lean_ctor_set(v___x_3032_, 1, v___x_3031_);
v___x_3033_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0));
v___x_3034_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_3032_, v___x_3033_);
v___x_3035_ = l_Lean_Json_mkObj(v___x_3034_);
lean_dec(v___x_3034_);
return v___x_3035_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__2(void){
_start:
{
uint8_t v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; 
v___x_3043_ = 1;
v___x_3044_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__1));
v___x_3045_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3044_, v___x_3043_);
return v___x_3045_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__3(void){
_start:
{
lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; 
v___x_3046_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6));
v___x_3047_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__2, &l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__2);
v___x_3048_ = lean_string_append(v___x_3047_, v___x_3046_);
return v___x_3048_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; 
v___x_3049_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__6, &l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__6);
v___x_3050_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__3);
v___x_3051_ = lean_string_append(v___x_3050_, v___x_3049_);
return v___x_3051_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__5(void){
_start:
{
lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; 
v___x_3052_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_3053_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__4);
v___x_3054_ = lean_string_append(v___x_3053_, v___x_3052_);
return v___x_3054_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__6(void){
_start:
{
lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; 
v___x_3055_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__6, &l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__6);
v___x_3056_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__3);
v___x_3057_ = lean_string_append(v___x_3056_, v___x_3055_);
return v___x_3057_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__7(void){
_start:
{
lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; 
v___x_3058_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_3059_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__6, &l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__6);
v___x_3060_ = lean_string_append(v___x_3059_, v___x_3058_);
return v___x_3060_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson(lean_object* v_json_3061_){
_start:
{
lean_object* v___x_3062_; lean_object* v___x_3063_; 
v___x_3062_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__0));
lean_inc(v_json_3061_);
v___x_3063_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson_spec__0(v_json_3061_, v___x_3062_);
if (lean_obj_tag(v___x_3063_) == 0)
{
lean_object* v_a_3064_; lean_object* v___x_3066_; uint8_t v_isShared_3067_; uint8_t v_isSharedCheck_3073_; 
lean_dec(v_json_3061_);
v_a_3064_ = lean_ctor_get(v___x_3063_, 0);
v_isSharedCheck_3073_ = !lean_is_exclusive(v___x_3063_);
if (v_isSharedCheck_3073_ == 0)
{
v___x_3066_ = v___x_3063_;
v_isShared_3067_ = v_isSharedCheck_3073_;
goto v_resetjp_3065_;
}
else
{
lean_inc(v_a_3064_);
lean_dec(v___x_3063_);
v___x_3066_ = lean_box(0);
v_isShared_3067_ = v_isSharedCheck_3073_;
goto v_resetjp_3065_;
}
v_resetjp_3065_:
{
lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3071_; 
v___x_3068_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__5, &l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__5);
v___x_3069_ = lean_string_append(v___x_3068_, v_a_3064_);
lean_dec(v_a_3064_);
if (v_isShared_3067_ == 0)
{
lean_ctor_set(v___x_3066_, 0, v___x_3069_);
v___x_3071_ = v___x_3066_;
goto v_reusejp_3070_;
}
else
{
lean_object* v_reuseFailAlloc_3072_; 
v_reuseFailAlloc_3072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3072_, 0, v___x_3069_);
v___x_3071_ = v_reuseFailAlloc_3072_;
goto v_reusejp_3070_;
}
v_reusejp_3070_:
{
return v___x_3071_;
}
}
}
else
{
if (lean_obj_tag(v___x_3063_) == 0)
{
lean_object* v_a_3074_; lean_object* v___x_3076_; uint8_t v_isShared_3077_; uint8_t v_isSharedCheck_3081_; 
lean_dec(v_json_3061_);
v_a_3074_ = lean_ctor_get(v___x_3063_, 0);
v_isSharedCheck_3081_ = !lean_is_exclusive(v___x_3063_);
if (v_isSharedCheck_3081_ == 0)
{
v___x_3076_ = v___x_3063_;
v_isShared_3077_ = v_isSharedCheck_3081_;
goto v_resetjp_3075_;
}
else
{
lean_inc(v_a_3074_);
lean_dec(v___x_3063_);
v___x_3076_ = lean_box(0);
v_isShared_3077_ = v_isSharedCheck_3081_;
goto v_resetjp_3075_;
}
v_resetjp_3075_:
{
lean_object* v___x_3079_; 
if (v_isShared_3077_ == 0)
{
lean_ctor_set_tag(v___x_3076_, 0);
v___x_3079_ = v___x_3076_;
goto v_reusejp_3078_;
}
else
{
lean_object* v_reuseFailAlloc_3080_; 
v_reuseFailAlloc_3080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3080_, 0, v_a_3074_);
v___x_3079_ = v_reuseFailAlloc_3080_;
goto v_reusejp_3078_;
}
v_reusejp_3078_:
{
return v___x_3079_;
}
}
}
else
{
lean_object* v_a_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; 
v_a_3082_ = lean_ctor_get(v___x_3063_, 0);
lean_inc(v_a_3082_);
lean_dec_ref_known(v___x_3063_, 1);
v___x_3083_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__0));
v___x_3084_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcConnected_fromJson_spec__0(v_json_3061_, v___x_3083_);
if (lean_obj_tag(v___x_3084_) == 0)
{
lean_object* v_a_3085_; lean_object* v___x_3087_; uint8_t v_isShared_3088_; uint8_t v_isSharedCheck_3094_; 
lean_dec(v_a_3082_);
v_a_3085_ = lean_ctor_get(v___x_3084_, 0);
v_isSharedCheck_3094_ = !lean_is_exclusive(v___x_3084_);
if (v_isSharedCheck_3094_ == 0)
{
v___x_3087_ = v___x_3084_;
v_isShared_3088_ = v_isSharedCheck_3094_;
goto v_resetjp_3086_;
}
else
{
lean_inc(v_a_3085_);
lean_dec(v___x_3084_);
v___x_3087_ = lean_box(0);
v_isShared_3088_ = v_isSharedCheck_3094_;
goto v_resetjp_3086_;
}
v_resetjp_3086_:
{
lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3092_; 
v___x_3089_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__7);
v___x_3090_ = lean_string_append(v___x_3089_, v_a_3085_);
lean_dec(v_a_3085_);
if (v_isShared_3088_ == 0)
{
lean_ctor_set(v___x_3087_, 0, v___x_3090_);
v___x_3092_ = v___x_3087_;
goto v_reusejp_3091_;
}
else
{
lean_object* v_reuseFailAlloc_3093_; 
v_reuseFailAlloc_3093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3093_, 0, v___x_3090_);
v___x_3092_ = v_reuseFailAlloc_3093_;
goto v_reusejp_3091_;
}
v_reusejp_3091_:
{
return v___x_3092_;
}
}
}
else
{
if (lean_obj_tag(v___x_3084_) == 0)
{
lean_object* v_a_3095_; lean_object* v___x_3097_; uint8_t v_isShared_3098_; uint8_t v_isSharedCheck_3102_; 
lean_dec(v_a_3082_);
v_a_3095_ = lean_ctor_get(v___x_3084_, 0);
v_isSharedCheck_3102_ = !lean_is_exclusive(v___x_3084_);
if (v_isSharedCheck_3102_ == 0)
{
v___x_3097_ = v___x_3084_;
v_isShared_3098_ = v_isSharedCheck_3102_;
goto v_resetjp_3096_;
}
else
{
lean_inc(v_a_3095_);
lean_dec(v___x_3084_);
v___x_3097_ = lean_box(0);
v_isShared_3098_ = v_isSharedCheck_3102_;
goto v_resetjp_3096_;
}
v_resetjp_3096_:
{
lean_object* v___x_3100_; 
if (v_isShared_3098_ == 0)
{
lean_ctor_set_tag(v___x_3097_, 0);
v___x_3100_ = v___x_3097_;
goto v_reusejp_3099_;
}
else
{
lean_object* v_reuseFailAlloc_3101_; 
v_reuseFailAlloc_3101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3101_, 0, v_a_3095_);
v___x_3100_ = v_reuseFailAlloc_3101_;
goto v_reusejp_3099_;
}
v_reusejp_3099_:
{
return v___x_3100_;
}
}
}
else
{
lean_object* v_a_3103_; lean_object* v___x_3105_; uint8_t v_isShared_3106_; uint8_t v_isSharedCheck_3112_; 
v_a_3103_ = lean_ctor_get(v___x_3084_, 0);
v_isSharedCheck_3112_ = !lean_is_exclusive(v___x_3084_);
if (v_isSharedCheck_3112_ == 0)
{
v___x_3105_ = v___x_3084_;
v_isShared_3106_ = v_isSharedCheck_3112_;
goto v_resetjp_3104_;
}
else
{
lean_inc(v_a_3103_);
lean_dec(v___x_3084_);
v___x_3105_ = lean_box(0);
v_isShared_3106_ = v_isSharedCheck_3112_;
goto v_resetjp_3104_;
}
v_resetjp_3104_:
{
lean_object* v___x_3107_; uint64_t v___x_3108_; lean_object* v___x_3110_; 
v___x_3107_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3107_, 0, v_a_3082_);
v___x_3108_ = lean_unbox_uint64(v_a_3103_);
lean_dec(v_a_3103_);
lean_ctor_set_uint64(v___x_3107_, sizeof(void*)*1, v___x_3108_);
if (v_isShared_3106_ == 0)
{
lean_ctor_set(v___x_3105_, 0, v___x_3107_);
v___x_3110_ = v___x_3105_;
goto v_reusejp_3109_;
}
else
{
lean_object* v_reuseFailAlloc_3111_; 
v_reuseFailAlloc_3111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3111_, 0, v___x_3107_);
v___x_3110_ = v_reuseFailAlloc_3111_;
goto v_reusejp_3109_;
}
v_reusejp_3109_:
{
return v___x_3110_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRpcKeepAliveParams_toJson(lean_object* v_x_3115_){
_start:
{
lean_object* v_uri_3116_; uint64_t v_sessionId_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; 
v_uri_3116_ = lean_ctor_get(v_x_3115_, 0);
v_sessionId_3117_ = lean_ctor_get_uint64(v_x_3115_, sizeof(void*)*1);
v___x_3118_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__0));
lean_inc_ref(v_uri_3116_);
v___x_3119_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3119_, 0, v_uri_3116_);
v___x_3120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3120_, 0, v___x_3118_);
lean_ctor_set(v___x_3120_, 1, v___x_3119_);
v___x_3121_ = lean_box(0);
v___x_3122_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3122_, 0, v___x_3120_);
lean_ctor_set(v___x_3122_, 1, v___x_3121_);
v___x_3123_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__0));
v___x_3124_ = lean_uint64_to_nat(v_sessionId_3117_);
v___x_3125_ = l_Lean_bignumToJson(v___x_3124_);
v___x_3126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3126_, 0, v___x_3123_);
lean_ctor_set(v___x_3126_, 1, v___x_3125_);
v___x_3127_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3127_, 0, v___x_3126_);
lean_ctor_set(v___x_3127_, 1, v___x_3121_);
v___x_3128_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3128_, 0, v___x_3127_);
lean_ctor_set(v___x_3128_, 1, v___x_3121_);
v___x_3129_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3129_, 0, v___x_3122_);
lean_ctor_set(v___x_3129_, 1, v___x_3128_);
v___x_3130_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0));
v___x_3131_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_3129_, v___x_3130_);
v___x_3132_ = l_Lean_Json_mkObj(v___x_3131_);
lean_dec(v___x_3131_);
return v___x_3132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRpcKeepAliveParams_toJson___boxed(lean_object* v_x_3133_){
_start:
{
lean_object* v_res_3134_; 
v_res_3134_ = l_Lean_Lsp_instToJsonRpcKeepAliveParams_toJson(v_x_3133_);
lean_dec_ref(v_x_3133_);
return v_res_3134_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Lsp_instReprLineRange_repr_spec__0(lean_object* v_a_3141_){
_start:
{
lean_object* v___x_3142_; 
v___x_3142_ = lean_nat_to_int(v_a_3141_);
return v___x_3142_;
}
}
static lean_object* _init_l_Lean_Lsp_instReprLineRange_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_3156_; lean_object* v___x_3157_; 
v___x_3156_ = lean_unsigned_to_nat(9u);
v___x_3157_ = lean_nat_to_int(v___x_3156_);
return v___x_3157_;
}
}
static lean_object* _init_l_Lean_Lsp_instReprLineRange_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_3164_; lean_object* v___x_3165_; 
v___x_3164_ = lean_unsigned_to_nat(7u);
v___x_3165_ = lean_nat_to_int(v___x_3164_);
return v___x_3165_;
}
}
static lean_object* _init_l_Lean_Lsp_instReprLineRange_repr___redArg___closed__14(void){
_start:
{
lean_object* v___x_3167_; lean_object* v___x_3168_; 
v___x_3167_ = ((lean_object*)(l_Lean_Lsp_instReprLineRange_repr___redArg___closed__0));
v___x_3168_ = lean_string_length(v___x_3167_);
return v___x_3168_;
}
}
static lean_object* _init_l_Lean_Lsp_instReprLineRange_repr___redArg___closed__15(void){
_start:
{
lean_object* v___x_3169_; lean_object* v___x_3170_; 
v___x_3169_ = lean_obj_once(&l_Lean_Lsp_instReprLineRange_repr___redArg___closed__14, &l_Lean_Lsp_instReprLineRange_repr___redArg___closed__14_once, _init_l_Lean_Lsp_instReprLineRange_repr___redArg___closed__14);
v___x_3170_ = lean_nat_to_int(v___x_3169_);
return v___x_3170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instReprLineRange_repr___redArg(lean_object* v_x_3175_){
_start:
{
lean_object* v_start_3176_; lean_object* v_end_3177_; lean_object* v___x_3179_; uint8_t v_isShared_3180_; uint8_t v_isSharedCheck_3212_; 
v_start_3176_ = lean_ctor_get(v_x_3175_, 0);
v_end_3177_ = lean_ctor_get(v_x_3175_, 1);
v_isSharedCheck_3212_ = !lean_is_exclusive(v_x_3175_);
if (v_isSharedCheck_3212_ == 0)
{
v___x_3179_ = v_x_3175_;
v_isShared_3180_ = v_isSharedCheck_3212_;
goto v_resetjp_3178_;
}
else
{
lean_inc(v_end_3177_);
lean_inc(v_start_3176_);
lean_dec(v_x_3175_);
v___x_3179_ = lean_box(0);
v_isShared_3180_ = v_isSharedCheck_3212_;
goto v_resetjp_3178_;
}
v_resetjp_3178_:
{
lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3187_; 
v___x_3181_ = ((lean_object*)(l_Lean_Lsp_instReprLineRange_repr___redArg___closed__5));
v___x_3182_ = ((lean_object*)(l_Lean_Lsp_instReprLineRange_repr___redArg___closed__6));
v___x_3183_ = lean_obj_once(&l_Lean_Lsp_instReprLineRange_repr___redArg___closed__7, &l_Lean_Lsp_instReprLineRange_repr___redArg___closed__7_once, _init_l_Lean_Lsp_instReprLineRange_repr___redArg___closed__7);
v___x_3184_ = l_Nat_reprFast(v_start_3176_);
v___x_3185_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3185_, 0, v___x_3184_);
if (v_isShared_3180_ == 0)
{
lean_ctor_set_tag(v___x_3179_, 4);
lean_ctor_set(v___x_3179_, 1, v___x_3185_);
lean_ctor_set(v___x_3179_, 0, v___x_3183_);
v___x_3187_ = v___x_3179_;
goto v_reusejp_3186_;
}
else
{
lean_object* v_reuseFailAlloc_3211_; 
v_reuseFailAlloc_3211_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3211_, 0, v___x_3183_);
lean_ctor_set(v_reuseFailAlloc_3211_, 1, v___x_3185_);
v___x_3187_ = v_reuseFailAlloc_3211_;
goto v_reusejp_3186_;
}
v_reusejp_3186_:
{
uint8_t v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; 
v___x_3188_ = 0;
v___x_3189_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3189_, 0, v___x_3187_);
lean_ctor_set_uint8(v___x_3189_, sizeof(void*)*1, v___x_3188_);
v___x_3190_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3190_, 0, v___x_3182_);
lean_ctor_set(v___x_3190_, 1, v___x_3189_);
v___x_3191_ = ((lean_object*)(l_Lean_Lsp_instReprLineRange_repr___redArg___closed__9));
v___x_3192_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3192_, 0, v___x_3190_);
lean_ctor_set(v___x_3192_, 1, v___x_3191_);
v___x_3193_ = lean_box(1);
v___x_3194_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3194_, 0, v___x_3192_);
lean_ctor_set(v___x_3194_, 1, v___x_3193_);
v___x_3195_ = ((lean_object*)(l_Lean_Lsp_instReprLineRange_repr___redArg___closed__11));
v___x_3196_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3196_, 0, v___x_3194_);
lean_ctor_set(v___x_3196_, 1, v___x_3195_);
v___x_3197_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3197_, 0, v___x_3196_);
lean_ctor_set(v___x_3197_, 1, v___x_3181_);
v___x_3198_ = lean_obj_once(&l_Lean_Lsp_instReprLineRange_repr___redArg___closed__12, &l_Lean_Lsp_instReprLineRange_repr___redArg___closed__12_once, _init_l_Lean_Lsp_instReprLineRange_repr___redArg___closed__12);
v___x_3199_ = l_Nat_reprFast(v_end_3177_);
v___x_3200_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3200_, 0, v___x_3199_);
v___x_3201_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3201_, 0, v___x_3198_);
lean_ctor_set(v___x_3201_, 1, v___x_3200_);
v___x_3202_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3202_, 0, v___x_3201_);
lean_ctor_set_uint8(v___x_3202_, sizeof(void*)*1, v___x_3188_);
v___x_3203_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3203_, 0, v___x_3197_);
lean_ctor_set(v___x_3203_, 1, v___x_3202_);
v___x_3204_ = lean_obj_once(&l_Lean_Lsp_instReprLineRange_repr___redArg___closed__15, &l_Lean_Lsp_instReprLineRange_repr___redArg___closed__15_once, _init_l_Lean_Lsp_instReprLineRange_repr___redArg___closed__15);
v___x_3205_ = ((lean_object*)(l_Lean_Lsp_instReprLineRange_repr___redArg___closed__16));
v___x_3206_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3206_, 0, v___x_3205_);
lean_ctor_set(v___x_3206_, 1, v___x_3203_);
v___x_3207_ = ((lean_object*)(l_Lean_Lsp_instReprLineRange_repr___redArg___closed__17));
v___x_3208_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3208_, 0, v___x_3206_);
lean_ctor_set(v___x_3208_, 1, v___x_3207_);
v___x_3209_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3209_, 0, v___x_3204_);
lean_ctor_set(v___x_3209_, 1, v___x_3208_);
v___x_3210_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3210_, 0, v___x_3209_);
lean_ctor_set_uint8(v___x_3210_, sizeof(void*)*1, v___x_3188_);
return v___x_3210_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instReprLineRange_repr(lean_object* v_x_3213_, lean_object* v_prec_3214_){
_start:
{
lean_object* v___x_3215_; 
v___x_3215_ = l_Lean_Lsp_instReprLineRange_repr___redArg(v_x_3213_);
return v___x_3215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instReprLineRange_repr___boxed(lean_object* v_x_3216_, lean_object* v_prec_3217_){
_start:
{
lean_object* v_res_3218_; 
v_res_3218_ = l_Lean_Lsp_instReprLineRange_repr(v_x_3216_, v_prec_3217_);
lean_dec(v_prec_3217_);
return v_res_3218_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__2(void){
_start:
{
uint8_t v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; 
v___x_3226_ = 1;
v___x_3227_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__1));
v___x_3228_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3227_, v___x_3226_);
return v___x_3228_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__3(void){
_start:
{
lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; 
v___x_3229_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6));
v___x_3230_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__2, &l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__2);
v___x_3231_ = lean_string_append(v___x_3230_, v___x_3229_);
return v___x_3231_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__5(void){
_start:
{
uint8_t v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; 
v___x_3234_ = 1;
v___x_3235_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__4));
v___x_3236_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3235_, v___x_3234_);
return v___x_3236_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__6(void){
_start:
{
lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; 
v___x_3237_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__5, &l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__5);
v___x_3238_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__3);
v___x_3239_ = lean_string_append(v___x_3238_, v___x_3237_);
return v___x_3239_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__7(void){
_start:
{
lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; 
v___x_3240_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_3241_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__6);
v___x_3242_ = lean_string_append(v___x_3241_, v___x_3240_);
return v___x_3242_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__9(void){
_start:
{
uint8_t v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; 
v___x_3245_ = 1;
v___x_3246_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__8));
v___x_3247_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3246_, v___x_3245_);
return v___x_3247_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__10(void){
_start:
{
lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; 
v___x_3248_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__9, &l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__9);
v___x_3249_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__3);
v___x_3250_ = lean_string_append(v___x_3249_, v___x_3248_);
return v___x_3250_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__11(void){
_start:
{
lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; 
v___x_3251_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_3252_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__10, &l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__10);
v___x_3253_ = lean_string_append(v___x_3252_, v___x_3251_);
return v___x_3253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLineRange_fromJson(lean_object* v_json_3254_){
_start:
{
lean_object* v___x_3255_; lean_object* v___x_3256_; 
v___x_3255_ = ((lean_object*)(l_Lean_Lsp_instReprLineRange_repr___redArg___closed__1));
lean_inc(v_json_3254_);
v___x_3256_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson_spec__1(v_json_3254_, v___x_3255_);
if (lean_obj_tag(v___x_3256_) == 0)
{
lean_object* v_a_3257_; lean_object* v___x_3259_; uint8_t v_isShared_3260_; uint8_t v_isSharedCheck_3266_; 
lean_dec(v_json_3254_);
v_a_3257_ = lean_ctor_get(v___x_3256_, 0);
v_isSharedCheck_3266_ = !lean_is_exclusive(v___x_3256_);
if (v_isSharedCheck_3266_ == 0)
{
v___x_3259_ = v___x_3256_;
v_isShared_3260_ = v_isSharedCheck_3266_;
goto v_resetjp_3258_;
}
else
{
lean_inc(v_a_3257_);
lean_dec(v___x_3256_);
v___x_3259_ = lean_box(0);
v_isShared_3260_ = v_isSharedCheck_3266_;
goto v_resetjp_3258_;
}
v_resetjp_3258_:
{
lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3264_; 
v___x_3261_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__7);
v___x_3262_ = lean_string_append(v___x_3261_, v_a_3257_);
lean_dec(v_a_3257_);
if (v_isShared_3260_ == 0)
{
lean_ctor_set(v___x_3259_, 0, v___x_3262_);
v___x_3264_ = v___x_3259_;
goto v_reusejp_3263_;
}
else
{
lean_object* v_reuseFailAlloc_3265_; 
v_reuseFailAlloc_3265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3265_, 0, v___x_3262_);
v___x_3264_ = v_reuseFailAlloc_3265_;
goto v_reusejp_3263_;
}
v_reusejp_3263_:
{
return v___x_3264_;
}
}
}
else
{
if (lean_obj_tag(v___x_3256_) == 0)
{
lean_object* v_a_3267_; lean_object* v___x_3269_; uint8_t v_isShared_3270_; uint8_t v_isSharedCheck_3274_; 
lean_dec(v_json_3254_);
v_a_3267_ = lean_ctor_get(v___x_3256_, 0);
v_isSharedCheck_3274_ = !lean_is_exclusive(v___x_3256_);
if (v_isSharedCheck_3274_ == 0)
{
v___x_3269_ = v___x_3256_;
v_isShared_3270_ = v_isSharedCheck_3274_;
goto v_resetjp_3268_;
}
else
{
lean_inc(v_a_3267_);
lean_dec(v___x_3256_);
v___x_3269_ = lean_box(0);
v_isShared_3270_ = v_isSharedCheck_3274_;
goto v_resetjp_3268_;
}
v_resetjp_3268_:
{
lean_object* v___x_3272_; 
if (v_isShared_3270_ == 0)
{
lean_ctor_set_tag(v___x_3269_, 0);
v___x_3272_ = v___x_3269_;
goto v_reusejp_3271_;
}
else
{
lean_object* v_reuseFailAlloc_3273_; 
v_reuseFailAlloc_3273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3273_, 0, v_a_3267_);
v___x_3272_ = v_reuseFailAlloc_3273_;
goto v_reusejp_3271_;
}
v_reusejp_3271_:
{
return v___x_3272_;
}
}
}
else
{
lean_object* v_a_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; 
v_a_3275_ = lean_ctor_get(v___x_3256_, 0);
lean_inc(v_a_3275_);
lean_dec_ref_known(v___x_3256_, 1);
v___x_3276_ = ((lean_object*)(l_Lean_Lsp_instReprLineRange_repr___redArg___closed__10));
v___x_3277_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson_spec__1(v_json_3254_, v___x_3276_);
if (lean_obj_tag(v___x_3277_) == 0)
{
lean_object* v_a_3278_; lean_object* v___x_3280_; uint8_t v_isShared_3281_; uint8_t v_isSharedCheck_3287_; 
lean_dec(v_a_3275_);
v_a_3278_ = lean_ctor_get(v___x_3277_, 0);
v_isSharedCheck_3287_ = !lean_is_exclusive(v___x_3277_);
if (v_isSharedCheck_3287_ == 0)
{
v___x_3280_ = v___x_3277_;
v_isShared_3281_ = v_isSharedCheck_3287_;
goto v_resetjp_3279_;
}
else
{
lean_inc(v_a_3278_);
lean_dec(v___x_3277_);
v___x_3280_ = lean_box(0);
v_isShared_3281_ = v_isSharedCheck_3287_;
goto v_resetjp_3279_;
}
v_resetjp_3279_:
{
lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3285_; 
v___x_3282_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__11, &l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__11);
v___x_3283_ = lean_string_append(v___x_3282_, v_a_3278_);
lean_dec(v_a_3278_);
if (v_isShared_3281_ == 0)
{
lean_ctor_set(v___x_3280_, 0, v___x_3283_);
v___x_3285_ = v___x_3280_;
goto v_reusejp_3284_;
}
else
{
lean_object* v_reuseFailAlloc_3286_; 
v_reuseFailAlloc_3286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3286_, 0, v___x_3283_);
v___x_3285_ = v_reuseFailAlloc_3286_;
goto v_reusejp_3284_;
}
v_reusejp_3284_:
{
return v___x_3285_;
}
}
}
else
{
if (lean_obj_tag(v___x_3277_) == 0)
{
lean_object* v_a_3288_; lean_object* v___x_3290_; uint8_t v_isShared_3291_; uint8_t v_isSharedCheck_3295_; 
lean_dec(v_a_3275_);
v_a_3288_ = lean_ctor_get(v___x_3277_, 0);
v_isSharedCheck_3295_ = !lean_is_exclusive(v___x_3277_);
if (v_isSharedCheck_3295_ == 0)
{
v___x_3290_ = v___x_3277_;
v_isShared_3291_ = v_isSharedCheck_3295_;
goto v_resetjp_3289_;
}
else
{
lean_inc(v_a_3288_);
lean_dec(v___x_3277_);
v___x_3290_ = lean_box(0);
v_isShared_3291_ = v_isSharedCheck_3295_;
goto v_resetjp_3289_;
}
v_resetjp_3289_:
{
lean_object* v___x_3293_; 
if (v_isShared_3291_ == 0)
{
lean_ctor_set_tag(v___x_3290_, 0);
v___x_3293_ = v___x_3290_;
goto v_reusejp_3292_;
}
else
{
lean_object* v_reuseFailAlloc_3294_; 
v_reuseFailAlloc_3294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3294_, 0, v_a_3288_);
v___x_3293_ = v_reuseFailAlloc_3294_;
goto v_reusejp_3292_;
}
v_reusejp_3292_:
{
return v___x_3293_;
}
}
}
else
{
lean_object* v_a_3296_; lean_object* v___x_3298_; uint8_t v_isShared_3299_; uint8_t v_isSharedCheck_3304_; 
v_a_3296_ = lean_ctor_get(v___x_3277_, 0);
v_isSharedCheck_3304_ = !lean_is_exclusive(v___x_3277_);
if (v_isSharedCheck_3304_ == 0)
{
v___x_3298_ = v___x_3277_;
v_isShared_3299_ = v_isSharedCheck_3304_;
goto v_resetjp_3297_;
}
else
{
lean_inc(v_a_3296_);
lean_dec(v___x_3277_);
v___x_3298_ = lean_box(0);
v_isShared_3299_ = v_isSharedCheck_3304_;
goto v_resetjp_3297_;
}
v_resetjp_3297_:
{
lean_object* v___x_3300_; lean_object* v___x_3302_; 
v___x_3300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3300_, 0, v_a_3275_);
lean_ctor_set(v___x_3300_, 1, v_a_3296_);
if (v_isShared_3299_ == 0)
{
lean_ctor_set(v___x_3298_, 0, v___x_3300_);
v___x_3302_ = v___x_3298_;
goto v_reusejp_3301_;
}
else
{
lean_object* v_reuseFailAlloc_3303_; 
v_reuseFailAlloc_3303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3303_, 0, v___x_3300_);
v___x_3302_ = v_reuseFailAlloc_3303_;
goto v_reusejp_3301_;
}
v_reusejp_3301_:
{
return v___x_3302_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLineRange_toJson(lean_object* v_x_3307_){
_start:
{
lean_object* v_start_3308_; lean_object* v_end_3309_; lean_object* v___x_3311_; uint8_t v_isShared_3312_; uint8_t v_isSharedCheck_3331_; 
v_start_3308_ = lean_ctor_get(v_x_3307_, 0);
v_end_3309_ = lean_ctor_get(v_x_3307_, 1);
v_isSharedCheck_3331_ = !lean_is_exclusive(v_x_3307_);
if (v_isSharedCheck_3331_ == 0)
{
v___x_3311_ = v_x_3307_;
v_isShared_3312_ = v_isSharedCheck_3331_;
goto v_resetjp_3310_;
}
else
{
lean_inc(v_end_3309_);
lean_inc(v_start_3308_);
lean_dec(v_x_3307_);
v___x_3311_ = lean_box(0);
v_isShared_3312_ = v_isSharedCheck_3331_;
goto v_resetjp_3310_;
}
v_resetjp_3310_:
{
lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3317_; 
v___x_3313_ = ((lean_object*)(l_Lean_Lsp_instReprLineRange_repr___redArg___closed__1));
v___x_3314_ = l_Lean_JsonNumber_fromNat(v_start_3308_);
v___x_3315_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3315_, 0, v___x_3314_);
if (v_isShared_3312_ == 0)
{
lean_ctor_set(v___x_3311_, 1, v___x_3315_);
lean_ctor_set(v___x_3311_, 0, v___x_3313_);
v___x_3317_ = v___x_3311_;
goto v_reusejp_3316_;
}
else
{
lean_object* v_reuseFailAlloc_3330_; 
v_reuseFailAlloc_3330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3330_, 0, v___x_3313_);
lean_ctor_set(v_reuseFailAlloc_3330_, 1, v___x_3315_);
v___x_3317_ = v_reuseFailAlloc_3330_;
goto v_reusejp_3316_;
}
v_reusejp_3316_:
{
lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; 
v___x_3318_ = lean_box(0);
v___x_3319_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3319_, 0, v___x_3317_);
lean_ctor_set(v___x_3319_, 1, v___x_3318_);
v___x_3320_ = ((lean_object*)(l_Lean_Lsp_instReprLineRange_repr___redArg___closed__10));
v___x_3321_ = l_Lean_JsonNumber_fromNat(v_end_3309_);
v___x_3322_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3322_, 0, v___x_3321_);
v___x_3323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3323_, 0, v___x_3320_);
lean_ctor_set(v___x_3323_, 1, v___x_3322_);
v___x_3324_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3324_, 0, v___x_3323_);
lean_ctor_set(v___x_3324_, 1, v___x_3318_);
v___x_3325_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3325_, 0, v___x_3324_);
lean_ctor_set(v___x_3325_, 1, v___x_3318_);
v___x_3326_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3326_, 0, v___x_3319_);
lean_ctor_set(v___x_3326_, 1, v___x_3325_);
v___x_3327_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0));
v___x_3328_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_3326_, v___x_3327_);
v___x_3329_ = l_Lean_Json_mkObj(v___x_3328_);
lean_dec(v___x_3328_);
return v___x_3329_;
}
}
}
}
lean_object* runtime_initialize_Lean_Data_Lsp_TextSync(uint8_t builtin);
lean_object* runtime_initialize_Lean_Server_Rpc_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_Lsp_Extra(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Data_Lsp_TextSync(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Server_Rpc_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Lsp_instInhabitedDependencyBuildMode_default = _init_l_Lean_Lsp_instInhabitedDependencyBuildMode_default();
l_Lean_Lsp_instInhabitedDependencyBuildMode = _init_l_Lean_Lsp_instInhabitedDependencyBuildMode();
l_Lean_Lsp_instInhabitedLeanFileProgressKind_default = _init_l_Lean_Lsp_instInhabitedLeanFileProgressKind_default();
l_Lean_Lsp_instInhabitedLeanFileProgressKind = _init_l_Lean_Lsp_instInhabitedLeanFileProgressKind();
l_Lean_Lsp_instInhabitedLeanImportMetaKind_default = _init_l_Lean_Lsp_instInhabitedLeanImportMetaKind_default();
l_Lean_Lsp_instInhabitedLeanImportMetaKind = _init_l_Lean_Lsp_instInhabitedLeanImportMetaKind();
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Data_Lsp_Extra(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Data_Lsp_TextSync(uint8_t builtin);
lean_object* initialize_Lean_Server_Rpc_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_Lsp_Extra(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_Lsp_TextSync(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_Rpc_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Lsp_Extra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Data_Lsp_Extra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Data_Lsp_Extra(builtin);
}
#ifdef __cplusplus
}
#endif

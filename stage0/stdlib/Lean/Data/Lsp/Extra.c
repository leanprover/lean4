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
static const lean_ctor_object l_Lean_Lsp_instFromJsonWaitForILeans_fromJson___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Lsp_instFromJsonWaitForILeans_fromJson___redArg___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonWaitForILeans_fromJson___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonWaitForILeans_fromJson___redArg();
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonWaitForILeans_fromJson___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_Lsp_instFromJsonWaitForILeans_fromJson___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonWaitForILeans_fromJson___closed__0;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonWaitForILeans_fromJson(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonWaitForILeans_fromJson___boxed(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonWaitForILeans___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonWaitForILeans_fromJson___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonWaitForILeans___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonWaitForILeans___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonWaitForILeans = (const lean_object*)&l_Lean_Lsp_instFromJsonWaitForILeans___closed__0_value;
static lean_once_cell_t l_Lean_Lsp_instToJsonWaitForILeans_toJson___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instToJsonWaitForILeans_toJson___redArg___closed__0;
static lean_once_cell_t l_Lean_Lsp_instToJsonWaitForILeans_toJson___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instToJsonWaitForILeans_toJson___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonWaitForILeans_toJson___redArg();
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonWaitForILeans_toJson___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_Lsp_instToJsonWaitForILeans_toJson___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instToJsonWaitForILeans_toJson___closed__0;
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
static const lean_ctor_object l_Lean_Lsp_instFromJsonModuleHierarchyOptions_fromJson___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Lsp_instFromJsonModuleHierarchyOptions_fromJson___redArg___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonModuleHierarchyOptions_fromJson___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonModuleHierarchyOptions_fromJson___redArg();
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonModuleHierarchyOptions_fromJson___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_Lsp_instFromJsonModuleHierarchyOptions_fromJson___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonModuleHierarchyOptions_fromJson___closed__0;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonModuleHierarchyOptions_fromJson(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonModuleHierarchyOptions_fromJson___boxed(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonModuleHierarchyOptions___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonModuleHierarchyOptions_fromJson___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonModuleHierarchyOptions___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonModuleHierarchyOptions___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonModuleHierarchyOptions = (const lean_object*)&l_Lean_Lsp_instFromJsonModuleHierarchyOptions___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonModuleHierarchyOptions_toJson___redArg();
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonModuleHierarchyOptions_toJson___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_Lsp_instToJsonModuleHierarchyOptions_toJson___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instToJsonModuleHierarchyOptions_toJson___closed__0;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonModuleHierarchyOptions_toJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonModuleHierarchyOptions___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonModuleHierarchyOptions_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonModuleHierarchyOptions___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonModuleHierarchyOptions___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonModuleHierarchyOptions = (const lean_object*)&l_Lean_Lsp_instToJsonModuleHierarchyOptions___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonHighlightMatchesOptions_fromJson___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Lsp_instFromJsonHighlightMatchesOptions_fromJson___redArg___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonHighlightMatchesOptions_fromJson___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonHighlightMatchesOptions_fromJson___redArg();
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonHighlightMatchesOptions_fromJson___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_Lsp_instFromJsonHighlightMatchesOptions_fromJson___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonHighlightMatchesOptions_fromJson___closed__0;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonHighlightMatchesOptions_fromJson(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonHighlightMatchesOptions_fromJson___boxed(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonHighlightMatchesOptions___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonHighlightMatchesOptions_fromJson___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonHighlightMatchesOptions___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonHighlightMatchesOptions___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonHighlightMatchesOptions = (const lean_object*)&l_Lean_Lsp_instFromJsonHighlightMatchesOptions___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonHighlightMatchesOptions_toJson___redArg();
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonHighlightMatchesOptions_toJson___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_Lsp_instToJsonHighlightMatchesOptions_toJson___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instToJsonHighlightMatchesOptions_toJson___closed__0;
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
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonRpcOptions_toJson_spec__0___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonWaitForILeans_fromJson___redArg(){
_start:
{
lean_object* v___x_627_; 
v___x_627_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWaitForILeans_fromJson___redArg___closed__0));
return v___x_627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonWaitForILeans_fromJson___redArg___boxed(lean_object* v___dummy_628_){
_start:
{
lean_object* v_res_629_; 
v_res_629_ = l_Lean_Lsp_instFromJsonWaitForILeans_fromJson___redArg();
return v_res_629_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWaitForILeans_fromJson___closed__0(void){
_start:
{
lean_object* v___x_630_; 
v___x_630_ = l_Lean_Lsp_instFromJsonWaitForILeans_fromJson___redArg();
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonWaitForILeans_fromJson(lean_object* v_json_631_){
_start:
{
lean_object* v___x_632_; 
v___x_632_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWaitForILeans_fromJson___closed__0, &l_Lean_Lsp_instFromJsonWaitForILeans_fromJson___closed__0_once, _init_l_Lean_Lsp_instFromJsonWaitForILeans_fromJson___closed__0);
return v___x_632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonWaitForILeans_fromJson___boxed(lean_object* v_json_633_){
_start:
{
lean_object* v_res_634_; 
v_res_634_ = l_Lean_Lsp_instFromJsonWaitForILeans_fromJson(v_json_633_);
lean_dec(v_json_633_);
return v_res_634_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonWaitForILeans_toJson___redArg___closed__0(void){
_start:
{
lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_637_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0));
v___x_638_ = lean_box(0);
v___x_639_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_638_, v___x_637_);
return v___x_639_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonWaitForILeans_toJson___redArg___closed__1(void){
_start:
{
lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_640_ = lean_obj_once(&l_Lean_Lsp_instToJsonWaitForILeans_toJson___redArg___closed__0, &l_Lean_Lsp_instToJsonWaitForILeans_toJson___redArg___closed__0_once, _init_l_Lean_Lsp_instToJsonWaitForILeans_toJson___redArg___closed__0);
v___x_641_ = l_Lean_Json_mkObj(v___x_640_);
return v___x_641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonWaitForILeans_toJson___redArg(){
_start:
{
lean_object* v___x_643_; 
v___x_643_ = lean_obj_once(&l_Lean_Lsp_instToJsonWaitForILeans_toJson___redArg___closed__1, &l_Lean_Lsp_instToJsonWaitForILeans_toJson___redArg___closed__1_once, _init_l_Lean_Lsp_instToJsonWaitForILeans_toJson___redArg___closed__1);
return v___x_643_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonWaitForILeans_toJson___redArg___boxed(lean_object* v___dummy_644_){
_start:
{
lean_object* v_res_645_; 
v_res_645_ = l_Lean_Lsp_instToJsonWaitForILeans_toJson___redArg();
return v_res_645_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonWaitForILeans_toJson___closed__0(void){
_start:
{
lean_object* v___x_646_; 
v___x_646_ = l_Lean_Lsp_instToJsonWaitForILeans_toJson___redArg();
return v___x_646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonWaitForILeans_toJson(lean_object* v_x_647_){
_start:
{
lean_object* v___x_648_; 
v___x_648_ = lean_obj_once(&l_Lean_Lsp_instToJsonWaitForILeans_toJson___closed__0, &l_Lean_Lsp_instToJsonWaitForILeans_toJson___closed__0_once, _init_l_Lean_Lsp_instToJsonWaitForILeans_toJson___closed__0);
return v___x_648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanFileProgressKind_ctorIdx(uint8_t v_x_651_){
_start:
{
if (v_x_651_ == 0)
{
lean_object* v___x_652_; 
v___x_652_ = lean_unsigned_to_nat(0u);
return v___x_652_;
}
else
{
lean_object* v___x_653_; 
v___x_653_ = lean_unsigned_to_nat(1u);
return v___x_653_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanFileProgressKind_ctorIdx___boxed(lean_object* v_x_654_){
_start:
{
uint8_t v_x_boxed_655_; lean_object* v_res_656_; 
v_x_boxed_655_ = lean_unbox(v_x_654_);
v_res_656_ = l_Lean_Lsp_LeanFileProgressKind_ctorIdx(v_x_boxed_655_);
return v_res_656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanFileProgressKind_ctorElim___redArg(lean_object* v_k_657_){
_start:
{
lean_inc(v_k_657_);
return v_k_657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanFileProgressKind_ctorElim___redArg___boxed(lean_object* v_k_658_){
_start:
{
lean_object* v_res_659_; 
v_res_659_ = l_Lean_Lsp_LeanFileProgressKind_ctorElim___redArg(v_k_658_);
lean_dec(v_k_658_);
return v_res_659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanFileProgressKind_ctorElim(lean_object* v_motive_660_, lean_object* v_ctorIdx_661_, uint8_t v_t_662_, lean_object* v_h_663_, lean_object* v_k_664_){
_start:
{
lean_inc(v_k_664_);
return v_k_664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanFileProgressKind_ctorElim___boxed(lean_object* v_motive_665_, lean_object* v_ctorIdx_666_, lean_object* v_t_667_, lean_object* v_h_668_, lean_object* v_k_669_){
_start:
{
uint8_t v_t_boxed_670_; lean_object* v_res_671_; 
v_t_boxed_670_ = lean_unbox(v_t_667_);
v_res_671_ = l_Lean_Lsp_LeanFileProgressKind_ctorElim(v_motive_665_, v_ctorIdx_666_, v_t_boxed_670_, v_h_668_, v_k_669_);
lean_dec(v_k_669_);
lean_dec(v_ctorIdx_666_);
return v_res_671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanFileProgressKind_processing_elim___redArg(lean_object* v_processing_672_){
_start:
{
lean_inc(v_processing_672_);
return v_processing_672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanFileProgressKind_processing_elim___redArg___boxed(lean_object* v_processing_673_){
_start:
{
lean_object* v_res_674_; 
v_res_674_ = l_Lean_Lsp_LeanFileProgressKind_processing_elim___redArg(v_processing_673_);
lean_dec(v_processing_673_);
return v_res_674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanFileProgressKind_processing_elim(lean_object* v_motive_675_, uint8_t v_t_676_, lean_object* v_h_677_, lean_object* v_processing_678_){
_start:
{
lean_inc(v_processing_678_);
return v_processing_678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanFileProgressKind_processing_elim___boxed(lean_object* v_motive_679_, lean_object* v_t_680_, lean_object* v_h_681_, lean_object* v_processing_682_){
_start:
{
uint8_t v_t_boxed_683_; lean_object* v_res_684_; 
v_t_boxed_683_ = lean_unbox(v_t_680_);
v_res_684_ = l_Lean_Lsp_LeanFileProgressKind_processing_elim(v_motive_679_, v_t_boxed_683_, v_h_681_, v_processing_682_);
lean_dec(v_processing_682_);
return v_res_684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanFileProgressKind_fatalError_elim___redArg(lean_object* v_fatalError_685_){
_start:
{
lean_inc(v_fatalError_685_);
return v_fatalError_685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanFileProgressKind_fatalError_elim___redArg___boxed(lean_object* v_fatalError_686_){
_start:
{
lean_object* v_res_687_; 
v_res_687_ = l_Lean_Lsp_LeanFileProgressKind_fatalError_elim___redArg(v_fatalError_686_);
lean_dec(v_fatalError_686_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanFileProgressKind_fatalError_elim(lean_object* v_motive_688_, uint8_t v_t_689_, lean_object* v_h_690_, lean_object* v_fatalError_691_){
_start:
{
lean_inc(v_fatalError_691_);
return v_fatalError_691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanFileProgressKind_fatalError_elim___boxed(lean_object* v_motive_692_, lean_object* v_t_693_, lean_object* v_h_694_, lean_object* v_fatalError_695_){
_start:
{
uint8_t v_t_boxed_696_; lean_object* v_res_697_; 
v_t_boxed_696_ = lean_unbox(v_t_693_);
v_res_697_ = l_Lean_Lsp_LeanFileProgressKind_fatalError_elim(v_motive_692_, v_t_boxed_696_, v_h_694_, v_fatalError_695_);
lean_dec(v_fatalError_695_);
return v_res_697_;
}
}
static uint8_t _init_l_Lean_Lsp_instInhabitedLeanFileProgressKind_default(void){
_start:
{
uint8_t v___x_698_; 
v___x_698_ = 0;
return v___x_698_;
}
}
static uint8_t _init_l_Lean_Lsp_instInhabitedLeanFileProgressKind(void){
_start:
{
uint8_t v___x_699_; 
v___x_699_ = 0;
return v___x_699_;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_instBEqLeanFileProgressKind_beq(uint8_t v_x_700_, uint8_t v_y_701_){
_start:
{
lean_object* v___x_702_; lean_object* v___x_703_; uint8_t v___x_704_; 
v___x_702_ = l_Lean_Lsp_LeanFileProgressKind_ctorIdx(v_x_700_);
v___x_703_ = l_Lean_Lsp_LeanFileProgressKind_ctorIdx(v_y_701_);
v___x_704_ = lean_nat_dec_eq(v___x_702_, v___x_703_);
lean_dec(v___x_703_);
lean_dec(v___x_702_);
return v___x_704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqLeanFileProgressKind_beq___boxed(lean_object* v_x_705_, lean_object* v_y_706_){
_start:
{
uint8_t v_x_21__boxed_707_; uint8_t v_y_22__boxed_708_; uint8_t v_res_709_; lean_object* v_r_710_; 
v_x_21__boxed_707_ = lean_unbox(v_x_705_);
v_y_22__boxed_708_ = lean_unbox(v_y_706_);
v_res_709_ = l_Lean_Lsp_instBEqLeanFileProgressKind_beq(v_x_21__boxed_707_, v_y_22__boxed_708_);
v_r_710_ = lean_box(v_res_709_);
return v_r_710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanFileProgressKind___lam__0(lean_object* v_j_721_){
_start:
{
lean_object* v___x_730_; 
lean_inc(v_j_721_);
v___x_730_ = l_Lean_Json_getNat_x3f(v_j_721_);
if (lean_obj_tag(v___x_730_) == 1)
{
lean_object* v_a_731_; lean_object* v___x_732_; uint8_t v___x_733_; 
v_a_731_ = lean_ctor_get(v___x_730_, 0);
lean_inc(v_a_731_);
lean_dec_ref_known(v___x_730_, 1);
v___x_732_ = lean_unsigned_to_nat(1u);
v___x_733_ = lean_nat_dec_eq(v_a_731_, v___x_732_);
if (v___x_733_ == 0)
{
lean_object* v___x_734_; uint8_t v___x_735_; 
v___x_734_ = lean_unsigned_to_nat(2u);
v___x_735_ = lean_nat_dec_eq(v_a_731_, v___x_734_);
lean_dec(v_a_731_);
if (v___x_735_ == 0)
{
goto v___jp_722_;
}
else
{
lean_object* v___x_736_; 
lean_dec(v_j_721_);
v___x_736_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressKind___lam__0___closed__2));
return v___x_736_;
}
}
else
{
lean_object* v___x_737_; 
lean_dec(v_a_731_);
lean_dec(v_j_721_);
v___x_737_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressKind___lam__0___closed__3));
return v___x_737_;
}
}
else
{
lean_dec_ref(v___x_730_);
goto v___jp_722_;
}
v___jp_722_:
{
lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; 
v___x_723_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressKind___lam__0___closed__0));
v___x_724_ = lean_unsigned_to_nat(80u);
v___x_725_ = l_Lean_Json_pretty(v_j_721_, v___x_724_);
v___x_726_ = lean_string_append(v___x_723_, v___x_725_);
lean_dec_ref(v___x_725_);
v___x_727_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressKind___lam__0___closed__1));
v___x_728_ = lean_string_append(v___x_726_, v___x_727_);
v___x_729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_729_, 0, v___x_728_);
return v___x_729_;
}
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__0(void){
_start:
{
lean_object* v___x_740_; lean_object* v___x_741_; 
v___x_740_ = lean_unsigned_to_nat(1u);
v___x_741_ = l_Lean_JsonNumber_fromNat(v___x_740_);
return v___x_741_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__1(void){
_start:
{
lean_object* v___x_742_; lean_object* v___x_743_; 
v___x_742_ = lean_obj_once(&l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__0, &l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__0_once, _init_l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__0);
v___x_743_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_743_, 0, v___x_742_);
return v___x_743_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__2(void){
_start:
{
lean_object* v___x_744_; lean_object* v___x_745_; 
v___x_744_ = lean_unsigned_to_nat(2u);
v___x_745_ = l_Lean_JsonNumber_fromNat(v___x_744_);
return v___x_745_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__3(void){
_start:
{
lean_object* v___x_746_; lean_object* v___x_747_; 
v___x_746_ = lean_obj_once(&l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__2, &l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__2_once, _init_l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__2);
v___x_747_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_747_, 0, v___x_746_);
return v___x_747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0(uint8_t v_x_748_){
_start:
{
if (v_x_748_ == 0)
{
lean_object* v___x_749_; 
v___x_749_ = lean_obj_once(&l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__1, &l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__1_once, _init_l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__1);
return v___x_749_;
}
else
{
lean_object* v___x_750_; 
v___x_750_ = lean_obj_once(&l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__3, &l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__3_once, _init_l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__3);
return v___x_750_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___boxed(lean_object* v_x_751_){
_start:
{
uint8_t v_x_56__boxed_752_; lean_object* v_res_753_; 
v_x_56__boxed_752_ = lean_unbox(v_x_751_);
v_res_753_ = l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0(v_x_56__boxed_752_);
return v_res_753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson_spec__0(lean_object* v_j_756_, lean_object* v_k_757_){
_start:
{
lean_object* v___x_758_; lean_object* v___x_759_; 
v___x_758_ = l_Lean_Json_getObjValD(v_j_756_, v_k_757_);
v___x_759_ = l_Lean_Lsp_instFromJsonRange_fromJson(v___x_758_);
return v___x_759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson_spec__0___boxed(lean_object* v_j_760_, lean_object* v_k_761_){
_start:
{
lean_object* v_res_762_; 
v_res_762_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson_spec__0(v_j_760_, v_k_761_);
lean_dec_ref(v_k_761_);
return v_res_762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson_spec__1(lean_object* v_j_763_, lean_object* v_k_764_){
_start:
{
lean_object* v___x_765_; lean_object* v___x_774_; 
v___x_765_ = l_Lean_Json_getObjValD(v_j_763_, v_k_764_);
lean_inc(v___x_765_);
v___x_774_ = l_Lean_Json_getNat_x3f(v___x_765_);
if (lean_obj_tag(v___x_774_) == 1)
{
lean_object* v_a_775_; lean_object* v___x_776_; uint8_t v___x_777_; 
v_a_775_ = lean_ctor_get(v___x_774_, 0);
lean_inc(v_a_775_);
lean_dec_ref_known(v___x_774_, 1);
v___x_776_ = lean_unsigned_to_nat(1u);
v___x_777_ = lean_nat_dec_eq(v_a_775_, v___x_776_);
if (v___x_777_ == 0)
{
lean_object* v___x_778_; uint8_t v___x_779_; 
v___x_778_ = lean_unsigned_to_nat(2u);
v___x_779_ = lean_nat_dec_eq(v_a_775_, v___x_778_);
lean_dec(v_a_775_);
if (v___x_779_ == 0)
{
goto v___jp_766_;
}
else
{
lean_object* v___x_780_; 
lean_dec(v___x_765_);
v___x_780_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressKind___lam__0___closed__2));
return v___x_780_;
}
}
else
{
lean_object* v___x_781_; 
lean_dec(v_a_775_);
lean_dec(v___x_765_);
v___x_781_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressKind___lam__0___closed__3));
return v___x_781_;
}
}
else
{
lean_dec_ref(v___x_774_);
goto v___jp_766_;
}
v___jp_766_:
{
lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; 
v___x_767_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressKind___lam__0___closed__0));
v___x_768_ = lean_unsigned_to_nat(80u);
v___x_769_ = l_Lean_Json_pretty(v___x_765_, v___x_768_);
v___x_770_ = lean_string_append(v___x_767_, v___x_769_);
lean_dec_ref(v___x_769_);
v___x_771_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressKind___lam__0___closed__1));
v___x_772_ = lean_string_append(v___x_770_, v___x_771_);
v___x_773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_773_, 0, v___x_772_);
return v___x_773_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson_spec__1___boxed(lean_object* v_j_782_, lean_object* v_k_783_){
_start:
{
lean_object* v_res_784_; 
v_res_784_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson_spec__1(v_j_782_, v_k_783_);
lean_dec_ref(v_k_783_);
return v_res_784_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__3(void){
_start:
{
uint8_t v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; 
v___x_791_ = 1;
v___x_792_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__2));
v___x_793_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_792_, v___x_791_);
return v___x_793_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__4(void){
_start:
{
lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; 
v___x_794_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6));
v___x_795_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__3);
v___x_796_ = lean_string_append(v___x_795_, v___x_794_);
return v___x_796_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__6(void){
_start:
{
uint8_t v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; 
v___x_799_ = 1;
v___x_800_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__5));
v___x_801_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_800_, v___x_799_);
return v___x_801_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__7(void){
_start:
{
lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; 
v___x_802_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__6);
v___x_803_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__4);
v___x_804_ = lean_string_append(v___x_803_, v___x_802_);
return v___x_804_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__8(void){
_start:
{
lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; 
v___x_805_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_806_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__7);
v___x_807_ = lean_string_append(v___x_806_, v___x_805_);
return v___x_807_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__11(void){
_start:
{
uint8_t v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; 
v___x_811_ = 1;
v___x_812_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__10));
v___x_813_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_812_, v___x_811_);
return v___x_813_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__12(void){
_start:
{
lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; 
v___x_814_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__11, &l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__11);
v___x_815_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__4);
v___x_816_ = lean_string_append(v___x_815_, v___x_814_);
return v___x_816_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__13(void){
_start:
{
lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; 
v___x_817_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_818_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__12, &l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__12);
v___x_819_ = lean_string_append(v___x_818_, v___x_817_);
return v___x_819_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson(lean_object* v_json_820_){
_start:
{
lean_object* v___x_821_; lean_object* v___x_822_; 
v___x_821_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__0));
lean_inc(v_json_820_);
v___x_822_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson_spec__0(v_json_820_, v___x_821_);
if (lean_obj_tag(v___x_822_) == 0)
{
lean_object* v_a_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_832_; 
lean_dec(v_json_820_);
v_a_823_ = lean_ctor_get(v___x_822_, 0);
v_isSharedCheck_832_ = !lean_is_exclusive(v___x_822_);
if (v_isSharedCheck_832_ == 0)
{
v___x_825_ = v___x_822_;
v_isShared_826_ = v_isSharedCheck_832_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_a_823_);
lean_dec(v___x_822_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_832_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_830_; 
v___x_827_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__8);
v___x_828_ = lean_string_append(v___x_827_, v_a_823_);
lean_dec(v_a_823_);
if (v_isShared_826_ == 0)
{
lean_ctor_set(v___x_825_, 0, v___x_828_);
v___x_830_ = v___x_825_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v___x_828_);
v___x_830_ = v_reuseFailAlloc_831_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
return v___x_830_;
}
}
}
else
{
if (lean_obj_tag(v___x_822_) == 0)
{
lean_object* v_a_833_; lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_840_; 
lean_dec(v_json_820_);
v_a_833_ = lean_ctor_get(v___x_822_, 0);
v_isSharedCheck_840_ = !lean_is_exclusive(v___x_822_);
if (v_isSharedCheck_840_ == 0)
{
v___x_835_ = v___x_822_;
v_isShared_836_ = v_isSharedCheck_840_;
goto v_resetjp_834_;
}
else
{
lean_inc(v_a_833_);
lean_dec(v___x_822_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_840_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
lean_object* v___x_838_; 
if (v_isShared_836_ == 0)
{
lean_ctor_set_tag(v___x_835_, 0);
v___x_838_ = v___x_835_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v_a_833_);
v___x_838_ = v_reuseFailAlloc_839_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
return v___x_838_;
}
}
}
else
{
lean_object* v_a_841_; lean_object* v___x_842_; lean_object* v___x_843_; 
v_a_841_ = lean_ctor_get(v___x_822_, 0);
lean_inc(v_a_841_);
lean_dec_ref_known(v___x_822_, 1);
v___x_842_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__9));
v___x_843_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson_spec__1(v_json_820_, v___x_842_);
if (lean_obj_tag(v___x_843_) == 0)
{
lean_object* v_a_844_; lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_853_; 
lean_dec(v_a_841_);
v_a_844_ = lean_ctor_get(v___x_843_, 0);
v_isSharedCheck_853_ = !lean_is_exclusive(v___x_843_);
if (v_isSharedCheck_853_ == 0)
{
v___x_846_ = v___x_843_;
v_isShared_847_ = v_isSharedCheck_853_;
goto v_resetjp_845_;
}
else
{
lean_inc(v_a_844_);
lean_dec(v___x_843_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_853_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_851_; 
v___x_848_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__13, &l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__13);
v___x_849_ = lean_string_append(v___x_848_, v_a_844_);
lean_dec(v_a_844_);
if (v_isShared_847_ == 0)
{
lean_ctor_set(v___x_846_, 0, v___x_849_);
v___x_851_ = v___x_846_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v___x_849_);
v___x_851_ = v_reuseFailAlloc_852_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
return v___x_851_;
}
}
}
else
{
if (lean_obj_tag(v___x_843_) == 0)
{
lean_object* v_a_854_; lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_861_; 
lean_dec(v_a_841_);
v_a_854_ = lean_ctor_get(v___x_843_, 0);
v_isSharedCheck_861_ = !lean_is_exclusive(v___x_843_);
if (v_isSharedCheck_861_ == 0)
{
v___x_856_ = v___x_843_;
v_isShared_857_ = v_isSharedCheck_861_;
goto v_resetjp_855_;
}
else
{
lean_inc(v_a_854_);
lean_dec(v___x_843_);
v___x_856_ = lean_box(0);
v_isShared_857_ = v_isSharedCheck_861_;
goto v_resetjp_855_;
}
v_resetjp_855_:
{
lean_object* v___x_859_; 
if (v_isShared_857_ == 0)
{
lean_ctor_set_tag(v___x_856_, 0);
v___x_859_ = v___x_856_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v_a_854_);
v___x_859_ = v_reuseFailAlloc_860_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
return v___x_859_;
}
}
}
else
{
lean_object* v_a_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_871_; 
v_a_862_ = lean_ctor_get(v___x_843_, 0);
v_isSharedCheck_871_ = !lean_is_exclusive(v___x_843_);
if (v_isSharedCheck_871_ == 0)
{
v___x_864_ = v___x_843_;
v_isShared_865_ = v_isSharedCheck_871_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_a_862_);
lean_dec(v___x_843_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_871_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
lean_object* v___x_866_; uint8_t v___x_867_; lean_object* v___x_869_; 
v___x_866_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_866_, 0, v_a_841_);
v___x_867_ = lean_unbox(v_a_862_);
lean_dec(v_a_862_);
lean_ctor_set_uint8(v___x_866_, sizeof(void*)*1, v___x_867_);
if (v_isShared_865_ == 0)
{
lean_ctor_set(v___x_864_, 0, v___x_866_);
v___x_869_ = v___x_864_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v___x_866_);
v___x_869_ = v_reuseFailAlloc_870_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
return v___x_869_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanFileProgressProcessingInfo_toJson(lean_object* v_x_874_){
_start:
{
lean_object* v_range_875_; uint8_t v_kind_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___y_884_; 
v_range_875_ = lean_ctor_get(v_x_874_, 0);
lean_inc_ref(v_range_875_);
v_kind_876_ = lean_ctor_get_uint8(v_x_874_, sizeof(void*)*1);
lean_dec_ref(v_x_874_);
v___x_877_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__0));
v___x_878_ = l_Lean_Lsp_instToJsonRange_toJson(v_range_875_);
v___x_879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_879_, 0, v___x_877_);
lean_ctor_set(v___x_879_, 1, v___x_878_);
v___x_880_ = lean_box(0);
v___x_881_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_881_, 0, v___x_879_);
lean_ctor_set(v___x_881_, 1, v___x_880_);
v___x_882_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__9));
if (v_kind_876_ == 0)
{
lean_object* v___x_892_; 
v___x_892_ = lean_obj_once(&l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__1, &l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__1_once, _init_l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__1);
v___y_884_ = v___x_892_;
goto v___jp_883_;
}
else
{
lean_object* v___x_893_; 
v___x_893_ = lean_obj_once(&l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__3, &l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__3_once, _init_l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__3);
v___y_884_ = v___x_893_;
goto v___jp_883_;
}
v___jp_883_:
{
lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; 
lean_inc(v___y_884_);
v___x_885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_885_, 0, v___x_882_);
lean_ctor_set(v___x_885_, 1, v___y_884_);
v___x_886_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_886_, 0, v___x_885_);
lean_ctor_set(v___x_886_, 1, v___x_880_);
v___x_887_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_887_, 0, v___x_886_);
lean_ctor_set(v___x_887_, 1, v___x_880_);
v___x_888_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_888_, 0, v___x_881_);
lean_ctor_set(v___x_888_, 1, v___x_887_);
v___x_889_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0));
v___x_890_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_888_, v___x_889_);
v___x_891_ = l_Lean_Json_mkObj(v___x_890_);
lean_dec(v___x_890_);
return v___x_891_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__0(lean_object* v_j_896_, lean_object* v_k_897_){
_start:
{
lean_object* v___x_898_; lean_object* v___x_899_; 
v___x_898_ = l_Lean_Json_getObjValD(v_j_896_, v_k_897_);
v___x_899_ = l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson(v___x_898_);
return v___x_899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__0___boxed(lean_object* v_j_900_, lean_object* v_k_901_){
_start:
{
lean_object* v_res_902_; 
v_res_902_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__0(v_j_900_, v_k_901_);
lean_dec_ref(v_k_901_);
return v_res_902_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__1_spec__1_spec__2(size_t v_sz_903_, size_t v_i_904_, lean_object* v_bs_905_){
_start:
{
uint8_t v___x_906_; 
v___x_906_ = lean_usize_dec_lt(v_i_904_, v_sz_903_);
if (v___x_906_ == 0)
{
lean_object* v___x_907_; 
v___x_907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_907_, 0, v_bs_905_);
return v___x_907_;
}
else
{
lean_object* v_v_908_; lean_object* v___x_909_; 
v_v_908_ = lean_array_uget_borrowed(v_bs_905_, v_i_904_);
lean_inc(v_v_908_);
v___x_909_ = l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson(v_v_908_);
if (lean_obj_tag(v___x_909_) == 0)
{
lean_object* v_a_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_917_; 
lean_dec_ref(v_bs_905_);
v_a_910_ = lean_ctor_get(v___x_909_, 0);
v_isSharedCheck_917_ = !lean_is_exclusive(v___x_909_);
if (v_isSharedCheck_917_ == 0)
{
v___x_912_ = v___x_909_;
v_isShared_913_ = v_isSharedCheck_917_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_a_910_);
lean_dec(v___x_909_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_917_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
lean_object* v___x_915_; 
if (v_isShared_913_ == 0)
{
v___x_915_ = v___x_912_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_916_; 
v_reuseFailAlloc_916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_916_, 0, v_a_910_);
v___x_915_ = v_reuseFailAlloc_916_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
return v___x_915_;
}
}
}
else
{
lean_object* v_a_918_; lean_object* v___x_919_; lean_object* v_bs_x27_920_; size_t v___x_921_; size_t v___x_922_; lean_object* v___x_923_; 
v_a_918_ = lean_ctor_get(v___x_909_, 0);
lean_inc(v_a_918_);
lean_dec_ref_known(v___x_909_, 1);
v___x_919_ = lean_unsigned_to_nat(0u);
v_bs_x27_920_ = lean_array_uset(v_bs_905_, v_i_904_, v___x_919_);
v___x_921_ = ((size_t)1ULL);
v___x_922_ = lean_usize_add(v_i_904_, v___x_921_);
v___x_923_ = lean_array_uset(v_bs_x27_920_, v_i_904_, v_a_918_);
v_i_904_ = v___x_922_;
v_bs_905_ = v___x_923_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__1_spec__1_spec__2___boxed(lean_object* v_sz_925_, lean_object* v_i_926_, lean_object* v_bs_927_){
_start:
{
size_t v_sz_boxed_928_; size_t v_i_boxed_929_; lean_object* v_res_930_; 
v_sz_boxed_928_ = lean_unbox_usize(v_sz_925_);
lean_dec(v_sz_925_);
v_i_boxed_929_ = lean_unbox_usize(v_i_926_);
lean_dec(v_i_926_);
v_res_930_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__1_spec__1_spec__2(v_sz_boxed_928_, v_i_boxed_929_, v_bs_927_);
return v_res_930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__1_spec__1(lean_object* v_x_932_){
_start:
{
if (lean_obj_tag(v_x_932_) == 4)
{
lean_object* v_elems_933_; size_t v_sz_934_; size_t v___x_935_; lean_object* v___x_936_; 
v_elems_933_ = lean_ctor_get(v_x_932_, 0);
lean_inc_ref(v_elems_933_);
lean_dec_ref_known(v_x_932_, 1);
v_sz_934_ = lean_array_size(v_elems_933_);
v___x_935_ = ((size_t)0ULL);
v___x_936_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__1_spec__1_spec__2(v_sz_934_, v___x_935_, v_elems_933_);
return v___x_936_;
}
else
{
lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; 
v___x_937_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__1_spec__1___closed__0));
v___x_938_ = lean_unsigned_to_nat(80u);
v___x_939_ = l_Lean_Json_pretty(v_x_932_, v___x_938_);
v___x_940_ = lean_string_append(v___x_937_, v___x_939_);
lean_dec_ref(v___x_939_);
v___x_941_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressKind___lam__0___closed__1));
v___x_942_ = lean_string_append(v___x_940_, v___x_941_);
v___x_943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_943_, 0, v___x_942_);
return v___x_943_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__1(lean_object* v_j_944_, lean_object* v_k_945_){
_start:
{
lean_object* v___x_946_; lean_object* v___x_947_; 
v___x_946_ = l_Lean_Json_getObjValD(v_j_944_, v_k_945_);
v___x_947_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__1_spec__1(v___x_946_);
return v___x_947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__1___boxed(lean_object* v_j_948_, lean_object* v_k_949_){
_start:
{
lean_object* v_res_950_; 
v_res_950_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__1(v_j_948_, v_k_949_);
lean_dec_ref(v_k_949_);
return v_res_950_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__2(void){
_start:
{
uint8_t v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; 
v___x_956_ = 1;
v___x_957_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__1));
v___x_958_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_957_, v___x_956_);
return v___x_958_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__3(void){
_start:
{
lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; 
v___x_959_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6));
v___x_960_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__2, &l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__2);
v___x_961_ = lean_string_append(v___x_960_, v___x_959_);
return v___x_961_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_962_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9, &l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9);
v___x_963_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__3);
v___x_964_ = lean_string_append(v___x_963_, v___x_962_);
return v___x_964_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__5(void){
_start:
{
lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_965_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_966_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__4);
v___x_967_ = lean_string_append(v___x_966_, v___x_965_);
return v___x_967_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__8(void){
_start:
{
uint8_t v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; 
v___x_971_ = 1;
v___x_972_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__7));
v___x_973_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_972_, v___x_971_);
return v___x_973_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__9(void){
_start:
{
lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; 
v___x_974_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__8);
v___x_975_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__3);
v___x_976_ = lean_string_append(v___x_975_, v___x_974_);
return v___x_976_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__10(void){
_start:
{
lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; 
v___x_977_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_978_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__9, &l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__9);
v___x_979_ = lean_string_append(v___x_978_, v___x_977_);
return v___x_979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson(lean_object* v_json_980_){
_start:
{
lean_object* v___x_981_; lean_object* v___x_982_; 
v___x_981_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__0));
lean_inc(v_json_980_);
v___x_982_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__0(v_json_980_, v___x_981_);
if (lean_obj_tag(v___x_982_) == 0)
{
lean_object* v_a_983_; lean_object* v___x_985_; uint8_t v_isShared_986_; uint8_t v_isSharedCheck_992_; 
lean_dec(v_json_980_);
v_a_983_ = lean_ctor_get(v___x_982_, 0);
v_isSharedCheck_992_ = !lean_is_exclusive(v___x_982_);
if (v_isSharedCheck_992_ == 0)
{
v___x_985_ = v___x_982_;
v_isShared_986_ = v_isSharedCheck_992_;
goto v_resetjp_984_;
}
else
{
lean_inc(v_a_983_);
lean_dec(v___x_982_);
v___x_985_ = lean_box(0);
v_isShared_986_ = v_isSharedCheck_992_;
goto v_resetjp_984_;
}
v_resetjp_984_:
{
lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_990_; 
v___x_987_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__5, &l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__5);
v___x_988_ = lean_string_append(v___x_987_, v_a_983_);
lean_dec(v_a_983_);
if (v_isShared_986_ == 0)
{
lean_ctor_set(v___x_985_, 0, v___x_988_);
v___x_990_ = v___x_985_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v___x_988_);
v___x_990_ = v_reuseFailAlloc_991_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
return v___x_990_;
}
}
}
else
{
if (lean_obj_tag(v___x_982_) == 0)
{
lean_object* v_a_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1000_; 
lean_dec(v_json_980_);
v_a_993_ = lean_ctor_get(v___x_982_, 0);
v_isSharedCheck_1000_ = !lean_is_exclusive(v___x_982_);
if (v_isSharedCheck_1000_ == 0)
{
v___x_995_ = v___x_982_;
v_isShared_996_ = v_isSharedCheck_1000_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_a_993_);
lean_dec(v___x_982_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1000_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
lean_object* v___x_998_; 
if (v_isShared_996_ == 0)
{
lean_ctor_set_tag(v___x_995_, 0);
v___x_998_ = v___x_995_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v_a_993_);
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
lean_object* v_a_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; 
v_a_1001_ = lean_ctor_get(v___x_982_, 0);
lean_inc(v_a_1001_);
lean_dec_ref_known(v___x_982_, 1);
v___x_1002_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__6));
v___x_1003_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__1(v_json_980_, v___x_1002_);
if (lean_obj_tag(v___x_1003_) == 0)
{
lean_object* v_a_1004_; lean_object* v___x_1006_; uint8_t v_isShared_1007_; uint8_t v_isSharedCheck_1013_; 
lean_dec(v_a_1001_);
v_a_1004_ = lean_ctor_get(v___x_1003_, 0);
v_isSharedCheck_1013_ = !lean_is_exclusive(v___x_1003_);
if (v_isSharedCheck_1013_ == 0)
{
v___x_1006_ = v___x_1003_;
v_isShared_1007_ = v_isSharedCheck_1013_;
goto v_resetjp_1005_;
}
else
{
lean_inc(v_a_1004_);
lean_dec(v___x_1003_);
v___x_1006_ = lean_box(0);
v_isShared_1007_ = v_isSharedCheck_1013_;
goto v_resetjp_1005_;
}
v_resetjp_1005_:
{
lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1011_; 
v___x_1008_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__10, &l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__10);
v___x_1009_ = lean_string_append(v___x_1008_, v_a_1004_);
lean_dec(v_a_1004_);
if (v_isShared_1007_ == 0)
{
lean_ctor_set(v___x_1006_, 0, v___x_1009_);
v___x_1011_ = v___x_1006_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v___x_1009_);
v___x_1011_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
return v___x_1011_;
}
}
}
else
{
if (lean_obj_tag(v___x_1003_) == 0)
{
lean_object* v_a_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1021_; 
lean_dec(v_a_1001_);
v_a_1014_ = lean_ctor_get(v___x_1003_, 0);
v_isSharedCheck_1021_ = !lean_is_exclusive(v___x_1003_);
if (v_isSharedCheck_1021_ == 0)
{
v___x_1016_ = v___x_1003_;
v_isShared_1017_ = v_isSharedCheck_1021_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_a_1014_);
lean_dec(v___x_1003_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1021_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v___x_1019_; 
if (v_isShared_1017_ == 0)
{
lean_ctor_set_tag(v___x_1016_, 0);
v___x_1019_ = v___x_1016_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v_a_1014_);
v___x_1019_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
return v___x_1019_;
}
}
}
else
{
lean_object* v_a_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1030_; 
v_a_1022_ = lean_ctor_get(v___x_1003_, 0);
v_isSharedCheck_1030_ = !lean_is_exclusive(v___x_1003_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1024_ = v___x_1003_;
v_isShared_1025_ = v_isSharedCheck_1030_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_a_1022_);
lean_dec(v___x_1003_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1030_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v___x_1026_; lean_object* v___x_1028_; 
v___x_1026_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1026_, 0, v_a_1001_);
lean_ctor_set(v___x_1026_, 1, v_a_1022_);
if (v_isShared_1025_ == 0)
{
lean_ctor_set(v___x_1024_, 0, v___x_1026_);
v___x_1028_ = v___x_1024_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v___x_1026_);
v___x_1028_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
return v___x_1028_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanFileProgressParams_toJson_spec__0_spec__0(size_t v_sz_1033_, size_t v_i_1034_, lean_object* v_bs_1035_){
_start:
{
uint8_t v___x_1036_; 
v___x_1036_ = lean_usize_dec_lt(v_i_1034_, v_sz_1033_);
if (v___x_1036_ == 0)
{
return v_bs_1035_;
}
else
{
lean_object* v_v_1037_; lean_object* v___x_1038_; lean_object* v_bs_x27_1039_; lean_object* v___x_1040_; size_t v___x_1041_; size_t v___x_1042_; lean_object* v___x_1043_; 
v_v_1037_ = lean_array_uget(v_bs_1035_, v_i_1034_);
v___x_1038_ = lean_unsigned_to_nat(0u);
v_bs_x27_1039_ = lean_array_uset(v_bs_1035_, v_i_1034_, v___x_1038_);
v___x_1040_ = l_Lean_Lsp_instToJsonLeanFileProgressProcessingInfo_toJson(v_v_1037_);
v___x_1041_ = ((size_t)1ULL);
v___x_1042_ = lean_usize_add(v_i_1034_, v___x_1041_);
v___x_1043_ = lean_array_uset(v_bs_x27_1039_, v_i_1034_, v___x_1040_);
v_i_1034_ = v___x_1042_;
v_bs_1035_ = v___x_1043_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanFileProgressParams_toJson_spec__0_spec__0___boxed(lean_object* v_sz_1045_, lean_object* v_i_1046_, lean_object* v_bs_1047_){
_start:
{
size_t v_sz_boxed_1048_; size_t v_i_boxed_1049_; lean_object* v_res_1050_; 
v_sz_boxed_1048_ = lean_unbox_usize(v_sz_1045_);
lean_dec(v_sz_1045_);
v_i_boxed_1049_ = lean_unbox_usize(v_i_1046_);
lean_dec(v_i_1046_);
v_res_1050_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanFileProgressParams_toJson_spec__0_spec__0(v_sz_boxed_1048_, v_i_boxed_1049_, v_bs_1047_);
return v_res_1050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanFileProgressParams_toJson_spec__0(lean_object* v_a_1051_){
_start:
{
size_t v_sz_1052_; size_t v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; 
v_sz_1052_ = lean_array_size(v_a_1051_);
v___x_1053_ = ((size_t)0ULL);
v___x_1054_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanFileProgressParams_toJson_spec__0_spec__0(v_sz_1052_, v___x_1053_, v_a_1051_);
v___x_1055_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1055_, 0, v___x_1054_);
return v___x_1055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanFileProgressParams_toJson(lean_object* v_x_1056_){
_start:
{
lean_object* v_textDocument_1057_; lean_object* v_processing_1058_; lean_object* v___x_1060_; uint8_t v_isShared_1061_; uint8_t v_isSharedCheck_1078_; 
v_textDocument_1057_ = lean_ctor_get(v_x_1056_, 0);
v_processing_1058_ = lean_ctor_get(v_x_1056_, 1);
v_isSharedCheck_1078_ = !lean_is_exclusive(v_x_1056_);
if (v_isSharedCheck_1078_ == 0)
{
v___x_1060_ = v_x_1056_;
v_isShared_1061_ = v_isSharedCheck_1078_;
goto v_resetjp_1059_;
}
else
{
lean_inc(v_processing_1058_);
lean_inc(v_textDocument_1057_);
lean_dec(v_x_1056_);
v___x_1060_ = lean_box(0);
v_isShared_1061_ = v_isSharedCheck_1078_;
goto v_resetjp_1059_;
}
v_resetjp_1059_:
{
lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1065_; 
v___x_1062_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__0));
v___x_1063_ = l_Lean_Lsp_instToJsonVersionedTextDocumentIdentifier_toJson(v_textDocument_1057_);
if (v_isShared_1061_ == 0)
{
lean_ctor_set(v___x_1060_, 1, v___x_1063_);
lean_ctor_set(v___x_1060_, 0, v___x_1062_);
v___x_1065_ = v___x_1060_;
goto v_reusejp_1064_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v___x_1062_);
lean_ctor_set(v_reuseFailAlloc_1077_, 1, v___x_1063_);
v___x_1065_ = v_reuseFailAlloc_1077_;
goto v_reusejp_1064_;
}
v_reusejp_1064_:
{
lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; 
v___x_1066_ = lean_box(0);
v___x_1067_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1067_, 0, v___x_1065_);
lean_ctor_set(v___x_1067_, 1, v___x_1066_);
v___x_1068_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__6));
v___x_1069_ = l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanFileProgressParams_toJson_spec__0(v_processing_1058_);
v___x_1070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1068_);
lean_ctor_set(v___x_1070_, 1, v___x_1069_);
v___x_1071_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1071_, 0, v___x_1070_);
lean_ctor_set(v___x_1071_, 1, v___x_1066_);
v___x_1072_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1072_, 0, v___x_1071_);
lean_ctor_set(v___x_1072_, 1, v___x_1066_);
v___x_1073_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1073_, 0, v___x_1067_);
lean_ctor_set(v___x_1073_, 1, v___x_1072_);
v___x_1074_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0));
v___x_1075_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_1073_, v___x_1074_);
v___x_1076_ = l_Lean_Json_mkObj(v___x_1075_);
lean_dec(v___x_1075_);
return v___x_1076_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoalParams_fromJson_spec__0(lean_object* v_j_1081_, lean_object* v_k_1082_){
_start:
{
lean_object* v___x_1083_; lean_object* v___x_1084_; 
v___x_1083_ = l_Lean_Json_getObjValD(v_j_1081_, v_k_1082_);
v___x_1084_ = l_Lean_Lsp_instFromJsonTextDocumentIdentifier_fromJson(v___x_1083_);
return v___x_1084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoalParams_fromJson_spec__0___boxed(lean_object* v_j_1085_, lean_object* v_k_1086_){
_start:
{
lean_object* v_res_1087_; 
v_res_1087_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoalParams_fromJson_spec__0(v_j_1085_, v_k_1086_);
lean_dec_ref(v_k_1086_);
return v_res_1087_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoalParams_fromJson_spec__1(lean_object* v_j_1088_, lean_object* v_k_1089_){
_start:
{
lean_object* v___x_1090_; lean_object* v___x_1091_; 
v___x_1090_ = l_Lean_Json_getObjValD(v_j_1088_, v_k_1089_);
v___x_1091_ = l_Lean_Lsp_instFromJsonPosition_fromJson(v___x_1090_);
return v___x_1091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoalParams_fromJson_spec__1___boxed(lean_object* v_j_1092_, lean_object* v_k_1093_){
_start:
{
lean_object* v_res_1094_; 
v_res_1094_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoalParams_fromJson_spec__1(v_j_1092_, v_k_1093_);
lean_dec_ref(v_k_1093_);
return v_res_1094_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__2(void){
_start:
{
uint8_t v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; 
v___x_1100_ = 1;
v___x_1101_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__1));
v___x_1102_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1101_, v___x_1100_);
return v___x_1102_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__3(void){
_start:
{
lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; 
v___x_1103_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6));
v___x_1104_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__2, &l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__2);
v___x_1105_ = lean_string_append(v___x_1104_, v___x_1103_);
return v___x_1105_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; 
v___x_1106_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9, &l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9);
v___x_1107_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__3);
v___x_1108_ = lean_string_append(v___x_1107_, v___x_1106_);
return v___x_1108_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__5(void){
_start:
{
lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; 
v___x_1109_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_1110_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__4);
v___x_1111_ = lean_string_append(v___x_1110_, v___x_1109_);
return v___x_1111_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__8(void){
_start:
{
uint8_t v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; 
v___x_1115_ = 1;
v___x_1116_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__7));
v___x_1117_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1116_, v___x_1115_);
return v___x_1117_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__9(void){
_start:
{
lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; 
v___x_1118_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__8);
v___x_1119_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__3);
v___x_1120_ = lean_string_append(v___x_1119_, v___x_1118_);
return v___x_1120_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__10(void){
_start:
{
lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; 
v___x_1121_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_1122_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__9, &l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__9);
v___x_1123_ = lean_string_append(v___x_1122_, v___x_1121_);
return v___x_1123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson(lean_object* v_json_1124_){
_start:
{
lean_object* v___x_1125_; lean_object* v___x_1126_; 
v___x_1125_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__0));
lean_inc(v_json_1124_);
v___x_1126_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoalParams_fromJson_spec__0(v_json_1124_, v___x_1125_);
if (lean_obj_tag(v___x_1126_) == 0)
{
lean_object* v_a_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1136_; 
lean_dec(v_json_1124_);
v_a_1127_ = lean_ctor_get(v___x_1126_, 0);
v_isSharedCheck_1136_ = !lean_is_exclusive(v___x_1126_);
if (v_isSharedCheck_1136_ == 0)
{
v___x_1129_ = v___x_1126_;
v_isShared_1130_ = v_isSharedCheck_1136_;
goto v_resetjp_1128_;
}
else
{
lean_inc(v_a_1127_);
lean_dec(v___x_1126_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1136_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1134_; 
v___x_1131_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__5, &l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__5);
v___x_1132_ = lean_string_append(v___x_1131_, v_a_1127_);
lean_dec(v_a_1127_);
if (v_isShared_1130_ == 0)
{
lean_ctor_set(v___x_1129_, 0, v___x_1132_);
v___x_1134_ = v___x_1129_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v___x_1132_);
v___x_1134_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
return v___x_1134_;
}
}
}
else
{
if (lean_obj_tag(v___x_1126_) == 0)
{
lean_object* v_a_1137_; lean_object* v___x_1139_; uint8_t v_isShared_1140_; uint8_t v_isSharedCheck_1144_; 
lean_dec(v_json_1124_);
v_a_1137_ = lean_ctor_get(v___x_1126_, 0);
v_isSharedCheck_1144_ = !lean_is_exclusive(v___x_1126_);
if (v_isSharedCheck_1144_ == 0)
{
v___x_1139_ = v___x_1126_;
v_isShared_1140_ = v_isSharedCheck_1144_;
goto v_resetjp_1138_;
}
else
{
lean_inc(v_a_1137_);
lean_dec(v___x_1126_);
v___x_1139_ = lean_box(0);
v_isShared_1140_ = v_isSharedCheck_1144_;
goto v_resetjp_1138_;
}
v_resetjp_1138_:
{
lean_object* v___x_1142_; 
if (v_isShared_1140_ == 0)
{
lean_ctor_set_tag(v___x_1139_, 0);
v___x_1142_ = v___x_1139_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v_a_1137_);
v___x_1142_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
return v___x_1142_;
}
}
}
else
{
lean_object* v_a_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; 
v_a_1145_ = lean_ctor_get(v___x_1126_, 0);
lean_inc(v_a_1145_);
lean_dec_ref_known(v___x_1126_, 1);
v___x_1146_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__6));
v___x_1147_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoalParams_fromJson_spec__1(v_json_1124_, v___x_1146_);
if (lean_obj_tag(v___x_1147_) == 0)
{
lean_object* v_a_1148_; lean_object* v___x_1150_; uint8_t v_isShared_1151_; uint8_t v_isSharedCheck_1157_; 
lean_dec(v_a_1145_);
v_a_1148_ = lean_ctor_get(v___x_1147_, 0);
v_isSharedCheck_1157_ = !lean_is_exclusive(v___x_1147_);
if (v_isSharedCheck_1157_ == 0)
{
v___x_1150_ = v___x_1147_;
v_isShared_1151_ = v_isSharedCheck_1157_;
goto v_resetjp_1149_;
}
else
{
lean_inc(v_a_1148_);
lean_dec(v___x_1147_);
v___x_1150_ = lean_box(0);
v_isShared_1151_ = v_isSharedCheck_1157_;
goto v_resetjp_1149_;
}
v_resetjp_1149_:
{
lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1155_; 
v___x_1152_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__10, &l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__10);
v___x_1153_ = lean_string_append(v___x_1152_, v_a_1148_);
lean_dec(v_a_1148_);
if (v_isShared_1151_ == 0)
{
lean_ctor_set(v___x_1150_, 0, v___x_1153_);
v___x_1155_ = v___x_1150_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v___x_1153_);
v___x_1155_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
return v___x_1155_;
}
}
}
else
{
if (lean_obj_tag(v___x_1147_) == 0)
{
lean_object* v_a_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1165_; 
lean_dec(v_a_1145_);
v_a_1158_ = lean_ctor_get(v___x_1147_, 0);
v_isSharedCheck_1165_ = !lean_is_exclusive(v___x_1147_);
if (v_isSharedCheck_1165_ == 0)
{
v___x_1160_ = v___x_1147_;
v_isShared_1161_ = v_isSharedCheck_1165_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_a_1158_);
lean_dec(v___x_1147_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1165_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
lean_object* v___x_1163_; 
if (v_isShared_1161_ == 0)
{
lean_ctor_set_tag(v___x_1160_, 0);
v___x_1163_ = v___x_1160_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v_a_1158_);
v___x_1163_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
return v___x_1163_;
}
}
}
else
{
lean_object* v_a_1166_; lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1174_; 
v_a_1166_ = lean_ctor_get(v___x_1147_, 0);
v_isSharedCheck_1174_ = !lean_is_exclusive(v___x_1147_);
if (v_isSharedCheck_1174_ == 0)
{
v___x_1168_ = v___x_1147_;
v_isShared_1169_ = v_isSharedCheck_1174_;
goto v_resetjp_1167_;
}
else
{
lean_inc(v_a_1166_);
lean_dec(v___x_1147_);
v___x_1168_ = lean_box(0);
v_isShared_1169_ = v_isSharedCheck_1174_;
goto v_resetjp_1167_;
}
v_resetjp_1167_:
{
lean_object* v___x_1170_; lean_object* v___x_1172_; 
v___x_1170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1170_, 0, v_a_1145_);
lean_ctor_set(v___x_1170_, 1, v_a_1166_);
if (v_isShared_1169_ == 0)
{
lean_ctor_set(v___x_1168_, 0, v___x_1170_);
v___x_1172_ = v___x_1168_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v___x_1170_);
v___x_1172_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
return v___x_1172_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonPlainGoalParams_toJson(lean_object* v_x_1177_){
_start:
{
lean_object* v_textDocument_1178_; lean_object* v_position_1179_; lean_object* v___x_1181_; uint8_t v_isShared_1182_; uint8_t v_isSharedCheck_1199_; 
v_textDocument_1178_ = lean_ctor_get(v_x_1177_, 0);
v_position_1179_ = lean_ctor_get(v_x_1177_, 1);
v_isSharedCheck_1199_ = !lean_is_exclusive(v_x_1177_);
if (v_isSharedCheck_1199_ == 0)
{
v___x_1181_ = v_x_1177_;
v_isShared_1182_ = v_isSharedCheck_1199_;
goto v_resetjp_1180_;
}
else
{
lean_inc(v_position_1179_);
lean_inc(v_textDocument_1178_);
lean_dec(v_x_1177_);
v___x_1181_ = lean_box(0);
v_isShared_1182_ = v_isSharedCheck_1199_;
goto v_resetjp_1180_;
}
v_resetjp_1180_:
{
lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1186_; 
v___x_1183_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__0));
v___x_1184_ = l_Lean_Lsp_instToJsonTextDocumentIdentifier_toJson(v_textDocument_1178_);
if (v_isShared_1182_ == 0)
{
lean_ctor_set(v___x_1181_, 1, v___x_1184_);
lean_ctor_set(v___x_1181_, 0, v___x_1183_);
v___x_1186_ = v___x_1181_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v___x_1183_);
lean_ctor_set(v_reuseFailAlloc_1198_, 1, v___x_1184_);
v___x_1186_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; 
v___x_1187_ = lean_box(0);
v___x_1188_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1188_, 0, v___x_1186_);
lean_ctor_set(v___x_1188_, 1, v___x_1187_);
v___x_1189_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__6));
v___x_1190_ = l_Lean_Lsp_instToJsonPosition_toJson(v_position_1179_);
v___x_1191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1191_, 0, v___x_1189_);
lean_ctor_set(v___x_1191_, 1, v___x_1190_);
v___x_1192_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1192_, 0, v___x_1191_);
lean_ctor_set(v___x_1192_, 1, v___x_1187_);
v___x_1193_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1193_, 0, v___x_1192_);
lean_ctor_set(v___x_1193_, 1, v___x_1187_);
v___x_1194_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1194_, 0, v___x_1188_);
lean_ctor_set(v___x_1194_, 1, v___x_1193_);
v___x_1195_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0));
v___x_1196_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_1194_, v___x_1195_);
v___x_1197_ = l_Lean_Json_mkObj(v___x_1196_);
lean_dec(v___x_1196_);
return v___x_1197_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoal_fromJson_spec__0_spec__0_spec__1(size_t v_sz_1202_, size_t v_i_1203_, lean_object* v_bs_1204_){
_start:
{
uint8_t v___x_1205_; 
v___x_1205_ = lean_usize_dec_lt(v_i_1203_, v_sz_1202_);
if (v___x_1205_ == 0)
{
lean_object* v___x_1206_; 
v___x_1206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1206_, 0, v_bs_1204_);
return v___x_1206_;
}
else
{
lean_object* v_v_1207_; lean_object* v___x_1208_; 
v_v_1207_ = lean_array_uget_borrowed(v_bs_1204_, v_i_1203_);
lean_inc(v_v_1207_);
v___x_1208_ = l_Lean_Json_getStr_x3f(v_v_1207_);
if (lean_obj_tag(v___x_1208_) == 0)
{
lean_object* v_a_1209_; lean_object* v___x_1211_; uint8_t v_isShared_1212_; uint8_t v_isSharedCheck_1216_; 
lean_dec_ref(v_bs_1204_);
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
lean_object* v_a_1217_; lean_object* v___x_1218_; lean_object* v_bs_x27_1219_; size_t v___x_1220_; size_t v___x_1221_; lean_object* v___x_1222_; 
v_a_1217_ = lean_ctor_get(v___x_1208_, 0);
lean_inc(v_a_1217_);
lean_dec_ref_known(v___x_1208_, 1);
v___x_1218_ = lean_unsigned_to_nat(0u);
v_bs_x27_1219_ = lean_array_uset(v_bs_1204_, v_i_1203_, v___x_1218_);
v___x_1220_ = ((size_t)1ULL);
v___x_1221_ = lean_usize_add(v_i_1203_, v___x_1220_);
v___x_1222_ = lean_array_uset(v_bs_x27_1219_, v_i_1203_, v_a_1217_);
v_i_1203_ = v___x_1221_;
v_bs_1204_ = v___x_1222_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoal_fromJson_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_1224_, lean_object* v_i_1225_, lean_object* v_bs_1226_){
_start:
{
size_t v_sz_boxed_1227_; size_t v_i_boxed_1228_; lean_object* v_res_1229_; 
v_sz_boxed_1227_ = lean_unbox_usize(v_sz_1224_);
lean_dec(v_sz_1224_);
v_i_boxed_1228_ = lean_unbox_usize(v_i_1225_);
lean_dec(v_i_1225_);
v_res_1229_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoal_fromJson_spec__0_spec__0_spec__1(v_sz_boxed_1227_, v_i_boxed_1228_, v_bs_1226_);
return v_res_1229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoal_fromJson_spec__0_spec__0(lean_object* v_x_1230_){
_start:
{
if (lean_obj_tag(v_x_1230_) == 4)
{
lean_object* v_elems_1231_; size_t v_sz_1232_; size_t v___x_1233_; lean_object* v___x_1234_; 
v_elems_1231_ = lean_ctor_get(v_x_1230_, 0);
lean_inc_ref(v_elems_1231_);
lean_dec_ref_known(v_x_1230_, 1);
v_sz_1232_ = lean_array_size(v_elems_1231_);
v___x_1233_ = ((size_t)0ULL);
v___x_1234_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoal_fromJson_spec__0_spec__0_spec__1(v_sz_1232_, v___x_1233_, v_elems_1231_);
return v___x_1234_;
}
else
{
lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; 
v___x_1235_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__1_spec__1___closed__0));
v___x_1236_ = lean_unsigned_to_nat(80u);
v___x_1237_ = l_Lean_Json_pretty(v_x_1230_, v___x_1236_);
v___x_1238_ = lean_string_append(v___x_1235_, v___x_1237_);
lean_dec_ref(v___x_1237_);
v___x_1239_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressKind___lam__0___closed__1));
v___x_1240_ = lean_string_append(v___x_1238_, v___x_1239_);
v___x_1241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1241_, 0, v___x_1240_);
return v___x_1241_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoal_fromJson_spec__0(lean_object* v_j_1242_, lean_object* v_k_1243_){
_start:
{
lean_object* v___x_1244_; lean_object* v___x_1245_; 
v___x_1244_ = l_Lean_Json_getObjValD(v_j_1242_, v_k_1243_);
v___x_1245_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoal_fromJson_spec__0_spec__0(v___x_1244_);
return v___x_1245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoal_fromJson_spec__0___boxed(lean_object* v_j_1246_, lean_object* v_k_1247_){
_start:
{
lean_object* v_res_1248_; 
v_res_1248_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoal_fromJson_spec__0(v_j_1246_, v_k_1247_);
lean_dec_ref(v_k_1247_);
return v_res_1248_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__3(void){
_start:
{
uint8_t v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; 
v___x_1255_ = 1;
v___x_1256_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__2));
v___x_1257_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1256_, v___x_1255_);
return v___x_1257_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__4(void){
_start:
{
lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; 
v___x_1258_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6));
v___x_1259_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__3, &l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__3);
v___x_1260_ = lean_string_append(v___x_1259_, v___x_1258_);
return v___x_1260_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__6(void){
_start:
{
uint8_t v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; 
v___x_1263_ = 1;
v___x_1264_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__5));
v___x_1265_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1264_, v___x_1263_);
return v___x_1265_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__7(void){
_start:
{
lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; 
v___x_1266_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__6, &l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__6);
v___x_1267_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__4, &l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__4);
v___x_1268_ = lean_string_append(v___x_1267_, v___x_1266_);
return v___x_1268_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__8(void){
_start:
{
lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; 
v___x_1269_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_1270_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__7, &l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__7);
v___x_1271_ = lean_string_append(v___x_1270_, v___x_1269_);
return v___x_1271_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__11(void){
_start:
{
uint8_t v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; 
v___x_1275_ = 1;
v___x_1276_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__10));
v___x_1277_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1276_, v___x_1275_);
return v___x_1277_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__12(void){
_start:
{
lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; 
v___x_1278_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__11, &l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__11);
v___x_1279_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__4, &l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__4);
v___x_1280_ = lean_string_append(v___x_1279_, v___x_1278_);
return v___x_1280_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__13(void){
_start:
{
lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; 
v___x_1281_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_1282_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__12, &l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__12);
v___x_1283_ = lean_string_append(v___x_1282_, v___x_1281_);
return v___x_1283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonPlainGoal_fromJson(lean_object* v_json_1284_){
_start:
{
lean_object* v___x_1285_; lean_object* v___x_1286_; 
v___x_1285_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__0));
lean_inc(v_json_1284_);
v___x_1286_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson_spec__0(v_json_1284_, v___x_1285_);
if (lean_obj_tag(v___x_1286_) == 0)
{
lean_object* v_a_1287_; lean_object* v___x_1289_; uint8_t v_isShared_1290_; uint8_t v_isSharedCheck_1296_; 
lean_dec(v_json_1284_);
v_a_1287_ = lean_ctor_get(v___x_1286_, 0);
v_isSharedCheck_1296_ = !lean_is_exclusive(v___x_1286_);
if (v_isSharedCheck_1296_ == 0)
{
v___x_1289_ = v___x_1286_;
v_isShared_1290_ = v_isSharedCheck_1296_;
goto v_resetjp_1288_;
}
else
{
lean_inc(v_a_1287_);
lean_dec(v___x_1286_);
v___x_1289_ = lean_box(0);
v_isShared_1290_ = v_isSharedCheck_1296_;
goto v_resetjp_1288_;
}
v_resetjp_1288_:
{
lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1294_; 
v___x_1291_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__8, &l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__8);
v___x_1292_ = lean_string_append(v___x_1291_, v_a_1287_);
lean_dec(v_a_1287_);
if (v_isShared_1290_ == 0)
{
lean_ctor_set(v___x_1289_, 0, v___x_1292_);
v___x_1294_ = v___x_1289_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1295_; 
v_reuseFailAlloc_1295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1295_, 0, v___x_1292_);
v___x_1294_ = v_reuseFailAlloc_1295_;
goto v_reusejp_1293_;
}
v_reusejp_1293_:
{
return v___x_1294_;
}
}
}
else
{
if (lean_obj_tag(v___x_1286_) == 0)
{
lean_object* v_a_1297_; lean_object* v___x_1299_; uint8_t v_isShared_1300_; uint8_t v_isSharedCheck_1304_; 
lean_dec(v_json_1284_);
v_a_1297_ = lean_ctor_get(v___x_1286_, 0);
v_isSharedCheck_1304_ = !lean_is_exclusive(v___x_1286_);
if (v_isSharedCheck_1304_ == 0)
{
v___x_1299_ = v___x_1286_;
v_isShared_1300_ = v_isSharedCheck_1304_;
goto v_resetjp_1298_;
}
else
{
lean_inc(v_a_1297_);
lean_dec(v___x_1286_);
v___x_1299_ = lean_box(0);
v_isShared_1300_ = v_isSharedCheck_1304_;
goto v_resetjp_1298_;
}
v_resetjp_1298_:
{
lean_object* v___x_1302_; 
if (v_isShared_1300_ == 0)
{
lean_ctor_set_tag(v___x_1299_, 0);
v___x_1302_ = v___x_1299_;
goto v_reusejp_1301_;
}
else
{
lean_object* v_reuseFailAlloc_1303_; 
v_reuseFailAlloc_1303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1303_, 0, v_a_1297_);
v___x_1302_ = v_reuseFailAlloc_1303_;
goto v_reusejp_1301_;
}
v_reusejp_1301_:
{
return v___x_1302_;
}
}
}
else
{
lean_object* v_a_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; 
v_a_1305_ = lean_ctor_get(v___x_1286_, 0);
lean_inc(v_a_1305_);
lean_dec_ref_known(v___x_1286_, 1);
v___x_1306_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__9));
v___x_1307_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoal_fromJson_spec__0(v_json_1284_, v___x_1306_);
if (lean_obj_tag(v___x_1307_) == 0)
{
lean_object* v_a_1308_; lean_object* v___x_1310_; uint8_t v_isShared_1311_; uint8_t v_isSharedCheck_1317_; 
lean_dec(v_a_1305_);
v_a_1308_ = lean_ctor_get(v___x_1307_, 0);
v_isSharedCheck_1317_ = !lean_is_exclusive(v___x_1307_);
if (v_isSharedCheck_1317_ == 0)
{
v___x_1310_ = v___x_1307_;
v_isShared_1311_ = v_isSharedCheck_1317_;
goto v_resetjp_1309_;
}
else
{
lean_inc(v_a_1308_);
lean_dec(v___x_1307_);
v___x_1310_ = lean_box(0);
v_isShared_1311_ = v_isSharedCheck_1317_;
goto v_resetjp_1309_;
}
v_resetjp_1309_:
{
lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1315_; 
v___x_1312_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__13, &l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__13);
v___x_1313_ = lean_string_append(v___x_1312_, v_a_1308_);
lean_dec(v_a_1308_);
if (v_isShared_1311_ == 0)
{
lean_ctor_set(v___x_1310_, 0, v___x_1313_);
v___x_1315_ = v___x_1310_;
goto v_reusejp_1314_;
}
else
{
lean_object* v_reuseFailAlloc_1316_; 
v_reuseFailAlloc_1316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1316_, 0, v___x_1313_);
v___x_1315_ = v_reuseFailAlloc_1316_;
goto v_reusejp_1314_;
}
v_reusejp_1314_:
{
return v___x_1315_;
}
}
}
else
{
if (lean_obj_tag(v___x_1307_) == 0)
{
lean_object* v_a_1318_; lean_object* v___x_1320_; uint8_t v_isShared_1321_; uint8_t v_isSharedCheck_1325_; 
lean_dec(v_a_1305_);
v_a_1318_ = lean_ctor_get(v___x_1307_, 0);
v_isSharedCheck_1325_ = !lean_is_exclusive(v___x_1307_);
if (v_isSharedCheck_1325_ == 0)
{
v___x_1320_ = v___x_1307_;
v_isShared_1321_ = v_isSharedCheck_1325_;
goto v_resetjp_1319_;
}
else
{
lean_inc(v_a_1318_);
lean_dec(v___x_1307_);
v___x_1320_ = lean_box(0);
v_isShared_1321_ = v_isSharedCheck_1325_;
goto v_resetjp_1319_;
}
v_resetjp_1319_:
{
lean_object* v___x_1323_; 
if (v_isShared_1321_ == 0)
{
lean_ctor_set_tag(v___x_1320_, 0);
v___x_1323_ = v___x_1320_;
goto v_reusejp_1322_;
}
else
{
lean_object* v_reuseFailAlloc_1324_; 
v_reuseFailAlloc_1324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1324_, 0, v_a_1318_);
v___x_1323_ = v_reuseFailAlloc_1324_;
goto v_reusejp_1322_;
}
v_reusejp_1322_:
{
return v___x_1323_;
}
}
}
else
{
lean_object* v_a_1326_; lean_object* v___x_1328_; uint8_t v_isShared_1329_; uint8_t v_isSharedCheck_1334_; 
v_a_1326_ = lean_ctor_get(v___x_1307_, 0);
v_isSharedCheck_1334_ = !lean_is_exclusive(v___x_1307_);
if (v_isSharedCheck_1334_ == 0)
{
v___x_1328_ = v___x_1307_;
v_isShared_1329_ = v_isSharedCheck_1334_;
goto v_resetjp_1327_;
}
else
{
lean_inc(v_a_1326_);
lean_dec(v___x_1307_);
v___x_1328_ = lean_box(0);
v_isShared_1329_ = v_isSharedCheck_1334_;
goto v_resetjp_1327_;
}
v_resetjp_1327_:
{
lean_object* v___x_1330_; lean_object* v___x_1332_; 
v___x_1330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1330_, 0, v_a_1305_);
lean_ctor_set(v___x_1330_, 1, v_a_1326_);
if (v_isShared_1329_ == 0)
{
lean_ctor_set(v___x_1328_, 0, v___x_1330_);
v___x_1332_ = v___x_1328_;
goto v_reusejp_1331_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(1, 1, 0);
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
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPlainGoal_toJson_spec__0_spec__0(size_t v_sz_1337_, size_t v_i_1338_, lean_object* v_bs_1339_){
_start:
{
uint8_t v___x_1340_; 
v___x_1340_ = lean_usize_dec_lt(v_i_1338_, v_sz_1337_);
if (v___x_1340_ == 0)
{
return v_bs_1339_;
}
else
{
lean_object* v_v_1341_; lean_object* v___x_1342_; lean_object* v_bs_x27_1343_; lean_object* v___x_1344_; size_t v___x_1345_; size_t v___x_1346_; lean_object* v___x_1347_; 
v_v_1341_ = lean_array_uget(v_bs_1339_, v_i_1338_);
v___x_1342_ = lean_unsigned_to_nat(0u);
v_bs_x27_1343_ = lean_array_uset(v_bs_1339_, v_i_1338_, v___x_1342_);
v___x_1344_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1344_, 0, v_v_1341_);
v___x_1345_ = ((size_t)1ULL);
v___x_1346_ = lean_usize_add(v_i_1338_, v___x_1345_);
v___x_1347_ = lean_array_uset(v_bs_x27_1343_, v_i_1338_, v___x_1344_);
v_i_1338_ = v___x_1346_;
v_bs_1339_ = v___x_1347_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPlainGoal_toJson_spec__0_spec__0___boxed(lean_object* v_sz_1349_, lean_object* v_i_1350_, lean_object* v_bs_1351_){
_start:
{
size_t v_sz_boxed_1352_; size_t v_i_boxed_1353_; lean_object* v_res_1354_; 
v_sz_boxed_1352_ = lean_unbox_usize(v_sz_1349_);
lean_dec(v_sz_1349_);
v_i_boxed_1353_ = lean_unbox_usize(v_i_1350_);
lean_dec(v_i_1350_);
v_res_1354_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPlainGoal_toJson_spec__0_spec__0(v_sz_boxed_1352_, v_i_boxed_1353_, v_bs_1351_);
return v_res_1354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonPlainGoal_toJson_spec__0(lean_object* v_a_1355_){
_start:
{
size_t v_sz_1356_; size_t v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; 
v_sz_1356_ = lean_array_size(v_a_1355_);
v___x_1357_ = ((size_t)0ULL);
v___x_1358_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPlainGoal_toJson_spec__0_spec__0(v_sz_1356_, v___x_1357_, v_a_1355_);
v___x_1359_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1359_, 0, v___x_1358_);
return v___x_1359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonPlainGoal_toJson(lean_object* v_x_1360_){
_start:
{
lean_object* v_rendered_1361_; lean_object* v_goals_1362_; lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1382_; 
v_rendered_1361_ = lean_ctor_get(v_x_1360_, 0);
v_goals_1362_ = lean_ctor_get(v_x_1360_, 1);
v_isSharedCheck_1382_ = !lean_is_exclusive(v_x_1360_);
if (v_isSharedCheck_1382_ == 0)
{
v___x_1364_ = v_x_1360_;
v_isShared_1365_ = v_isSharedCheck_1382_;
goto v_resetjp_1363_;
}
else
{
lean_inc(v_goals_1362_);
lean_inc(v_rendered_1361_);
lean_dec(v_x_1360_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1382_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1369_; 
v___x_1366_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__0));
v___x_1367_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1367_, 0, v_rendered_1361_);
if (v_isShared_1365_ == 0)
{
lean_ctor_set(v___x_1364_, 1, v___x_1367_);
lean_ctor_set(v___x_1364_, 0, v___x_1366_);
v___x_1369_ = v___x_1364_;
goto v_reusejp_1368_;
}
else
{
lean_object* v_reuseFailAlloc_1381_; 
v_reuseFailAlloc_1381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1381_, 0, v___x_1366_);
lean_ctor_set(v_reuseFailAlloc_1381_, 1, v___x_1367_);
v___x_1369_ = v_reuseFailAlloc_1381_;
goto v_reusejp_1368_;
}
v_reusejp_1368_:
{
lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; 
v___x_1370_ = lean_box(0);
v___x_1371_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1371_, 0, v___x_1369_);
lean_ctor_set(v___x_1371_, 1, v___x_1370_);
v___x_1372_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__9));
v___x_1373_ = l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonPlainGoal_toJson_spec__0(v_goals_1362_);
v___x_1374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1374_, 0, v___x_1372_);
lean_ctor_set(v___x_1374_, 1, v___x_1373_);
v___x_1375_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1375_, 0, v___x_1374_);
lean_ctor_set(v___x_1375_, 1, v___x_1370_);
v___x_1376_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1376_, 0, v___x_1375_);
lean_ctor_set(v___x_1376_, 1, v___x_1370_);
v___x_1377_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1377_, 0, v___x_1371_);
lean_ctor_set(v___x_1377_, 1, v___x_1376_);
v___x_1378_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0));
v___x_1379_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_1377_, v___x_1378_);
v___x_1380_ = l_Lean_Json_mkObj(v___x_1379_);
lean_dec(v___x_1379_);
return v___x_1380_;
}
}
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__2(void){
_start:
{
uint8_t v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; 
v___x_1390_ = 1;
v___x_1391_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__1));
v___x_1392_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1391_, v___x_1390_);
return v___x_1392_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__3(void){
_start:
{
lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; 
v___x_1393_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6));
v___x_1394_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__2, &l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__2);
v___x_1395_ = lean_string_append(v___x_1394_, v___x_1393_);
return v___x_1395_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; 
v___x_1396_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9, &l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9);
v___x_1397_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__3);
v___x_1398_ = lean_string_append(v___x_1397_, v___x_1396_);
return v___x_1398_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__5(void){
_start:
{
lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; 
v___x_1399_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_1400_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__4);
v___x_1401_ = lean_string_append(v___x_1400_, v___x_1399_);
return v___x_1401_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__6(void){
_start:
{
lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; 
v___x_1402_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__8);
v___x_1403_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__3);
v___x_1404_ = lean_string_append(v___x_1403_, v___x_1402_);
return v___x_1404_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__7(void){
_start:
{
lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; 
v___x_1405_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_1406_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__6, &l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__6);
v___x_1407_ = lean_string_append(v___x_1406_, v___x_1405_);
return v___x_1407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson(lean_object* v_json_1408_){
_start:
{
lean_object* v___x_1409_; lean_object* v___x_1410_; 
v___x_1409_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__0));
lean_inc(v_json_1408_);
v___x_1410_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoalParams_fromJson_spec__0(v_json_1408_, v___x_1409_);
if (lean_obj_tag(v___x_1410_) == 0)
{
lean_object* v_a_1411_; lean_object* v___x_1413_; uint8_t v_isShared_1414_; uint8_t v_isSharedCheck_1420_; 
lean_dec(v_json_1408_);
v_a_1411_ = lean_ctor_get(v___x_1410_, 0);
v_isSharedCheck_1420_ = !lean_is_exclusive(v___x_1410_);
if (v_isSharedCheck_1420_ == 0)
{
v___x_1413_ = v___x_1410_;
v_isShared_1414_ = v_isSharedCheck_1420_;
goto v_resetjp_1412_;
}
else
{
lean_inc(v_a_1411_);
lean_dec(v___x_1410_);
v___x_1413_ = lean_box(0);
v_isShared_1414_ = v_isSharedCheck_1420_;
goto v_resetjp_1412_;
}
v_resetjp_1412_:
{
lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1418_; 
v___x_1415_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__5, &l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__5);
v___x_1416_ = lean_string_append(v___x_1415_, v_a_1411_);
lean_dec(v_a_1411_);
if (v_isShared_1414_ == 0)
{
lean_ctor_set(v___x_1413_, 0, v___x_1416_);
v___x_1418_ = v___x_1413_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v___x_1416_);
v___x_1418_ = v_reuseFailAlloc_1419_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
return v___x_1418_;
}
}
}
else
{
if (lean_obj_tag(v___x_1410_) == 0)
{
lean_object* v_a_1421_; lean_object* v___x_1423_; uint8_t v_isShared_1424_; uint8_t v_isSharedCheck_1428_; 
lean_dec(v_json_1408_);
v_a_1421_ = lean_ctor_get(v___x_1410_, 0);
v_isSharedCheck_1428_ = !lean_is_exclusive(v___x_1410_);
if (v_isSharedCheck_1428_ == 0)
{
v___x_1423_ = v___x_1410_;
v_isShared_1424_ = v_isSharedCheck_1428_;
goto v_resetjp_1422_;
}
else
{
lean_inc(v_a_1421_);
lean_dec(v___x_1410_);
v___x_1423_ = lean_box(0);
v_isShared_1424_ = v_isSharedCheck_1428_;
goto v_resetjp_1422_;
}
v_resetjp_1422_:
{
lean_object* v___x_1426_; 
if (v_isShared_1424_ == 0)
{
lean_ctor_set_tag(v___x_1423_, 0);
v___x_1426_ = v___x_1423_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v_a_1421_);
v___x_1426_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
return v___x_1426_;
}
}
}
else
{
lean_object* v_a_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; 
v_a_1429_ = lean_ctor_get(v___x_1410_, 0);
lean_inc(v_a_1429_);
lean_dec_ref_known(v___x_1410_, 1);
v___x_1430_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__6));
v___x_1431_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoalParams_fromJson_spec__1(v_json_1408_, v___x_1430_);
if (lean_obj_tag(v___x_1431_) == 0)
{
lean_object* v_a_1432_; lean_object* v___x_1434_; uint8_t v_isShared_1435_; uint8_t v_isSharedCheck_1441_; 
lean_dec(v_a_1429_);
v_a_1432_ = lean_ctor_get(v___x_1431_, 0);
v_isSharedCheck_1441_ = !lean_is_exclusive(v___x_1431_);
if (v_isSharedCheck_1441_ == 0)
{
v___x_1434_ = v___x_1431_;
v_isShared_1435_ = v_isSharedCheck_1441_;
goto v_resetjp_1433_;
}
else
{
lean_inc(v_a_1432_);
lean_dec(v___x_1431_);
v___x_1434_ = lean_box(0);
v_isShared_1435_ = v_isSharedCheck_1441_;
goto v_resetjp_1433_;
}
v_resetjp_1433_:
{
lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1439_; 
v___x_1436_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__7);
v___x_1437_ = lean_string_append(v___x_1436_, v_a_1432_);
lean_dec(v_a_1432_);
if (v_isShared_1435_ == 0)
{
lean_ctor_set(v___x_1434_, 0, v___x_1437_);
v___x_1439_ = v___x_1434_;
goto v_reusejp_1438_;
}
else
{
lean_object* v_reuseFailAlloc_1440_; 
v_reuseFailAlloc_1440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1440_, 0, v___x_1437_);
v___x_1439_ = v_reuseFailAlloc_1440_;
goto v_reusejp_1438_;
}
v_reusejp_1438_:
{
return v___x_1439_;
}
}
}
else
{
if (lean_obj_tag(v___x_1431_) == 0)
{
lean_object* v_a_1442_; lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1449_; 
lean_dec(v_a_1429_);
v_a_1442_ = lean_ctor_get(v___x_1431_, 0);
v_isSharedCheck_1449_ = !lean_is_exclusive(v___x_1431_);
if (v_isSharedCheck_1449_ == 0)
{
v___x_1444_ = v___x_1431_;
v_isShared_1445_ = v_isSharedCheck_1449_;
goto v_resetjp_1443_;
}
else
{
lean_inc(v_a_1442_);
lean_dec(v___x_1431_);
v___x_1444_ = lean_box(0);
v_isShared_1445_ = v_isSharedCheck_1449_;
goto v_resetjp_1443_;
}
v_resetjp_1443_:
{
lean_object* v___x_1447_; 
if (v_isShared_1445_ == 0)
{
lean_ctor_set_tag(v___x_1444_, 0);
v___x_1447_ = v___x_1444_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v_a_1442_);
v___x_1447_ = v_reuseFailAlloc_1448_;
goto v_reusejp_1446_;
}
v_reusejp_1446_:
{
return v___x_1447_;
}
}
}
else
{
lean_object* v_a_1450_; lean_object* v___x_1452_; uint8_t v_isShared_1453_; uint8_t v_isSharedCheck_1458_; 
v_a_1450_ = lean_ctor_get(v___x_1431_, 0);
v_isSharedCheck_1458_ = !lean_is_exclusive(v___x_1431_);
if (v_isSharedCheck_1458_ == 0)
{
v___x_1452_ = v___x_1431_;
v_isShared_1453_ = v_isSharedCheck_1458_;
goto v_resetjp_1451_;
}
else
{
lean_inc(v_a_1450_);
lean_dec(v___x_1431_);
v___x_1452_ = lean_box(0);
v_isShared_1453_ = v_isSharedCheck_1458_;
goto v_resetjp_1451_;
}
v_resetjp_1451_:
{
lean_object* v___x_1454_; lean_object* v___x_1456_; 
v___x_1454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1454_, 0, v_a_1429_);
lean_ctor_set(v___x_1454_, 1, v_a_1450_);
if (v_isShared_1453_ == 0)
{
lean_ctor_set(v___x_1452_, 0, v___x_1454_);
v___x_1456_ = v___x_1452_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v___x_1454_);
v___x_1456_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1455_;
}
v_reusejp_1455_:
{
return v___x_1456_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonPlainTermGoalParams_toJson(lean_object* v_x_1461_){
_start:
{
lean_object* v_textDocument_1462_; lean_object* v_position_1463_; lean_object* v___x_1465_; uint8_t v_isShared_1466_; uint8_t v_isSharedCheck_1483_; 
v_textDocument_1462_ = lean_ctor_get(v_x_1461_, 0);
v_position_1463_ = lean_ctor_get(v_x_1461_, 1);
v_isSharedCheck_1483_ = !lean_is_exclusive(v_x_1461_);
if (v_isSharedCheck_1483_ == 0)
{
v___x_1465_ = v_x_1461_;
v_isShared_1466_ = v_isSharedCheck_1483_;
goto v_resetjp_1464_;
}
else
{
lean_inc(v_position_1463_);
lean_inc(v_textDocument_1462_);
lean_dec(v_x_1461_);
v___x_1465_ = lean_box(0);
v_isShared_1466_ = v_isSharedCheck_1483_;
goto v_resetjp_1464_;
}
v_resetjp_1464_:
{
lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1470_; 
v___x_1467_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__0));
v___x_1468_ = l_Lean_Lsp_instToJsonTextDocumentIdentifier_toJson(v_textDocument_1462_);
if (v_isShared_1466_ == 0)
{
lean_ctor_set(v___x_1465_, 1, v___x_1468_);
lean_ctor_set(v___x_1465_, 0, v___x_1467_);
v___x_1470_ = v___x_1465_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1482_; 
v_reuseFailAlloc_1482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1482_, 0, v___x_1467_);
lean_ctor_set(v_reuseFailAlloc_1482_, 1, v___x_1468_);
v___x_1470_ = v_reuseFailAlloc_1482_;
goto v_reusejp_1469_;
}
v_reusejp_1469_:
{
lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; 
v___x_1471_ = lean_box(0);
v___x_1472_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1472_, 0, v___x_1470_);
lean_ctor_set(v___x_1472_, 1, v___x_1471_);
v___x_1473_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__6));
v___x_1474_ = l_Lean_Lsp_instToJsonPosition_toJson(v_position_1463_);
v___x_1475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1475_, 0, v___x_1473_);
lean_ctor_set(v___x_1475_, 1, v___x_1474_);
v___x_1476_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1476_, 0, v___x_1475_);
lean_ctor_set(v___x_1476_, 1, v___x_1471_);
v___x_1477_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1477_, 0, v___x_1476_);
lean_ctor_set(v___x_1477_, 1, v___x_1471_);
v___x_1478_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1478_, 0, v___x_1472_);
lean_ctor_set(v___x_1478_, 1, v___x_1477_);
v___x_1479_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0));
v___x_1480_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_1478_, v___x_1479_);
v___x_1481_ = l_Lean_Json_mkObj(v___x_1480_);
lean_dec(v___x_1480_);
return v___x_1481_;
}
}
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__3(void){
_start:
{
uint8_t v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; 
v___x_1492_ = 1;
v___x_1493_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__2));
v___x_1494_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1493_, v___x_1492_);
return v___x_1494_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__4(void){
_start:
{
lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; 
v___x_1495_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6));
v___x_1496_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__3, &l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__3);
v___x_1497_ = lean_string_append(v___x_1496_, v___x_1495_);
return v___x_1497_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__6(void){
_start:
{
uint8_t v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; 
v___x_1500_ = 1;
v___x_1501_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__5));
v___x_1502_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1501_, v___x_1500_);
return v___x_1502_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__7(void){
_start:
{
lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; 
v___x_1503_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__6, &l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__6);
v___x_1504_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__4, &l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__4);
v___x_1505_ = lean_string_append(v___x_1504_, v___x_1503_);
return v___x_1505_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__8(void){
_start:
{
lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; 
v___x_1506_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_1507_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__7, &l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__7);
v___x_1508_ = lean_string_append(v___x_1507_, v___x_1506_);
return v___x_1508_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__9(void){
_start:
{
lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; 
v___x_1509_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__6);
v___x_1510_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__4, &l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__4);
v___x_1511_ = lean_string_append(v___x_1510_, v___x_1509_);
return v___x_1511_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__10(void){
_start:
{
lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; 
v___x_1512_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_1513_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__9, &l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__9);
v___x_1514_ = lean_string_append(v___x_1513_, v___x_1512_);
return v___x_1514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson(lean_object* v_json_1515_){
_start:
{
lean_object* v___x_1516_; lean_object* v___x_1517_; 
v___x_1516_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__0));
lean_inc(v_json_1515_);
v___x_1517_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson_spec__0(v_json_1515_, v___x_1516_);
if (lean_obj_tag(v___x_1517_) == 0)
{
lean_object* v_a_1518_; lean_object* v___x_1520_; uint8_t v_isShared_1521_; uint8_t v_isSharedCheck_1527_; 
lean_dec(v_json_1515_);
v_a_1518_ = lean_ctor_get(v___x_1517_, 0);
v_isSharedCheck_1527_ = !lean_is_exclusive(v___x_1517_);
if (v_isSharedCheck_1527_ == 0)
{
v___x_1520_ = v___x_1517_;
v_isShared_1521_ = v_isSharedCheck_1527_;
goto v_resetjp_1519_;
}
else
{
lean_inc(v_a_1518_);
lean_dec(v___x_1517_);
v___x_1520_ = lean_box(0);
v_isShared_1521_ = v_isSharedCheck_1527_;
goto v_resetjp_1519_;
}
v_resetjp_1519_:
{
lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1525_; 
v___x_1522_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__8, &l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__8);
v___x_1523_ = lean_string_append(v___x_1522_, v_a_1518_);
lean_dec(v_a_1518_);
if (v_isShared_1521_ == 0)
{
lean_ctor_set(v___x_1520_, 0, v___x_1523_);
v___x_1525_ = v___x_1520_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1526_; 
v_reuseFailAlloc_1526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1526_, 0, v___x_1523_);
v___x_1525_ = v_reuseFailAlloc_1526_;
goto v_reusejp_1524_;
}
v_reusejp_1524_:
{
return v___x_1525_;
}
}
}
else
{
if (lean_obj_tag(v___x_1517_) == 0)
{
lean_object* v_a_1528_; lean_object* v___x_1530_; uint8_t v_isShared_1531_; uint8_t v_isSharedCheck_1535_; 
lean_dec(v_json_1515_);
v_a_1528_ = lean_ctor_get(v___x_1517_, 0);
v_isSharedCheck_1535_ = !lean_is_exclusive(v___x_1517_);
if (v_isSharedCheck_1535_ == 0)
{
v___x_1530_ = v___x_1517_;
v_isShared_1531_ = v_isSharedCheck_1535_;
goto v_resetjp_1529_;
}
else
{
lean_inc(v_a_1528_);
lean_dec(v___x_1517_);
v___x_1530_ = lean_box(0);
v_isShared_1531_ = v_isSharedCheck_1535_;
goto v_resetjp_1529_;
}
v_resetjp_1529_:
{
lean_object* v___x_1533_; 
if (v_isShared_1531_ == 0)
{
lean_ctor_set_tag(v___x_1530_, 0);
v___x_1533_ = v___x_1530_;
goto v_reusejp_1532_;
}
else
{
lean_object* v_reuseFailAlloc_1534_; 
v_reuseFailAlloc_1534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1534_, 0, v_a_1528_);
v___x_1533_ = v_reuseFailAlloc_1534_;
goto v_reusejp_1532_;
}
v_reusejp_1532_:
{
return v___x_1533_;
}
}
}
else
{
lean_object* v_a_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; 
v_a_1536_ = lean_ctor_get(v___x_1517_, 0);
lean_inc(v_a_1536_);
lean_dec_ref_known(v___x_1517_, 1);
v___x_1537_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__0));
v___x_1538_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson_spec__0(v_json_1515_, v___x_1537_);
if (lean_obj_tag(v___x_1538_) == 0)
{
lean_object* v_a_1539_; lean_object* v___x_1541_; uint8_t v_isShared_1542_; uint8_t v_isSharedCheck_1548_; 
lean_dec(v_a_1536_);
v_a_1539_ = lean_ctor_get(v___x_1538_, 0);
v_isSharedCheck_1548_ = !lean_is_exclusive(v___x_1538_);
if (v_isSharedCheck_1548_ == 0)
{
v___x_1541_ = v___x_1538_;
v_isShared_1542_ = v_isSharedCheck_1548_;
goto v_resetjp_1540_;
}
else
{
lean_inc(v_a_1539_);
lean_dec(v___x_1538_);
v___x_1541_ = lean_box(0);
v_isShared_1542_ = v_isSharedCheck_1548_;
goto v_resetjp_1540_;
}
v_resetjp_1540_:
{
lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1546_; 
v___x_1543_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__10, &l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__10);
v___x_1544_ = lean_string_append(v___x_1543_, v_a_1539_);
lean_dec(v_a_1539_);
if (v_isShared_1542_ == 0)
{
lean_ctor_set(v___x_1541_, 0, v___x_1544_);
v___x_1546_ = v___x_1541_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v___x_1544_);
v___x_1546_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
return v___x_1546_;
}
}
}
else
{
if (lean_obj_tag(v___x_1538_) == 0)
{
lean_object* v_a_1549_; lean_object* v___x_1551_; uint8_t v_isShared_1552_; uint8_t v_isSharedCheck_1556_; 
lean_dec(v_a_1536_);
v_a_1549_ = lean_ctor_get(v___x_1538_, 0);
v_isSharedCheck_1556_ = !lean_is_exclusive(v___x_1538_);
if (v_isSharedCheck_1556_ == 0)
{
v___x_1551_ = v___x_1538_;
v_isShared_1552_ = v_isSharedCheck_1556_;
goto v_resetjp_1550_;
}
else
{
lean_inc(v_a_1549_);
lean_dec(v___x_1538_);
v___x_1551_ = lean_box(0);
v_isShared_1552_ = v_isSharedCheck_1556_;
goto v_resetjp_1550_;
}
v_resetjp_1550_:
{
lean_object* v___x_1554_; 
if (v_isShared_1552_ == 0)
{
lean_ctor_set_tag(v___x_1551_, 0);
v___x_1554_ = v___x_1551_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1555_; 
v_reuseFailAlloc_1555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1555_, 0, v_a_1549_);
v___x_1554_ = v_reuseFailAlloc_1555_;
goto v_reusejp_1553_;
}
v_reusejp_1553_:
{
return v___x_1554_;
}
}
}
else
{
lean_object* v_a_1557_; lean_object* v___x_1559_; uint8_t v_isShared_1560_; uint8_t v_isSharedCheck_1565_; 
v_a_1557_ = lean_ctor_get(v___x_1538_, 0);
v_isSharedCheck_1565_ = !lean_is_exclusive(v___x_1538_);
if (v_isSharedCheck_1565_ == 0)
{
v___x_1559_ = v___x_1538_;
v_isShared_1560_ = v_isSharedCheck_1565_;
goto v_resetjp_1558_;
}
else
{
lean_inc(v_a_1557_);
lean_dec(v___x_1538_);
v___x_1559_ = lean_box(0);
v_isShared_1560_ = v_isSharedCheck_1565_;
goto v_resetjp_1558_;
}
v_resetjp_1558_:
{
lean_object* v___x_1561_; lean_object* v___x_1563_; 
v___x_1561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1561_, 0, v_a_1536_);
lean_ctor_set(v___x_1561_, 1, v_a_1557_);
if (v_isShared_1560_ == 0)
{
lean_ctor_set(v___x_1559_, 0, v___x_1561_);
v___x_1563_ = v___x_1559_;
goto v_reusejp_1562_;
}
else
{
lean_object* v_reuseFailAlloc_1564_; 
v_reuseFailAlloc_1564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1564_, 0, v___x_1561_);
v___x_1563_ = v_reuseFailAlloc_1564_;
goto v_reusejp_1562_;
}
v_reusejp_1562_:
{
return v___x_1563_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonPlainTermGoal_toJson(lean_object* v_x_1568_){
_start:
{
lean_object* v_goal_1569_; lean_object* v_range_1570_; lean_object* v___x_1572_; uint8_t v_isShared_1573_; uint8_t v_isSharedCheck_1590_; 
v_goal_1569_ = lean_ctor_get(v_x_1568_, 0);
v_range_1570_ = lean_ctor_get(v_x_1568_, 1);
v_isSharedCheck_1590_ = !lean_is_exclusive(v_x_1568_);
if (v_isSharedCheck_1590_ == 0)
{
v___x_1572_ = v_x_1568_;
v_isShared_1573_ = v_isSharedCheck_1590_;
goto v_resetjp_1571_;
}
else
{
lean_inc(v_range_1570_);
lean_inc(v_goal_1569_);
lean_dec(v_x_1568_);
v___x_1572_ = lean_box(0);
v_isShared_1573_ = v_isSharedCheck_1590_;
goto v_resetjp_1571_;
}
v_resetjp_1571_:
{
lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1577_; 
v___x_1574_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__0));
v___x_1575_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1575_, 0, v_goal_1569_);
if (v_isShared_1573_ == 0)
{
lean_ctor_set(v___x_1572_, 1, v___x_1575_);
lean_ctor_set(v___x_1572_, 0, v___x_1574_);
v___x_1577_ = v___x_1572_;
goto v_reusejp_1576_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v___x_1574_);
lean_ctor_set(v_reuseFailAlloc_1589_, 1, v___x_1575_);
v___x_1577_ = v_reuseFailAlloc_1589_;
goto v_reusejp_1576_;
}
v_reusejp_1576_:
{
lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; 
v___x_1578_ = lean_box(0);
v___x_1579_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1579_, 0, v___x_1577_);
lean_ctor_set(v___x_1579_, 1, v___x_1578_);
v___x_1580_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__0));
v___x_1581_ = l_Lean_Lsp_instToJsonRange_toJson(v_range_1570_);
v___x_1582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1582_, 0, v___x_1580_);
lean_ctor_set(v___x_1582_, 1, v___x_1581_);
v___x_1583_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1583_, 0, v___x_1582_);
lean_ctor_set(v___x_1583_, 1, v___x_1578_);
v___x_1584_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1584_, 0, v___x_1583_);
lean_ctor_set(v___x_1584_, 1, v___x_1578_);
v___x_1585_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1585_, 0, v___x_1579_);
lean_ctor_set(v___x_1585_, 1, v___x_1584_);
v___x_1586_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0));
v___x_1587_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_1585_, v___x_1586_);
v___x_1588_ = l_Lean_Json_mkObj(v___x_1587_);
lean_dec(v___x_1587_);
return v___x_1588_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonModuleHierarchyOptions_fromJson___redArg(){
_start:
{
lean_object* v___x_1596_; 
v___x_1596_ = ((lean_object*)(l_Lean_Lsp_instFromJsonModuleHierarchyOptions_fromJson___redArg___closed__0));
return v___x_1596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonModuleHierarchyOptions_fromJson___redArg___boxed(lean_object* v___dummy_1597_){
_start:
{
lean_object* v_res_1598_; 
v_res_1598_ = l_Lean_Lsp_instFromJsonModuleHierarchyOptions_fromJson___redArg();
return v_res_1598_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonModuleHierarchyOptions_fromJson___closed__0(void){
_start:
{
lean_object* v___x_1599_; 
v___x_1599_ = l_Lean_Lsp_instFromJsonModuleHierarchyOptions_fromJson___redArg();
return v___x_1599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonModuleHierarchyOptions_fromJson(lean_object* v_json_1600_){
_start:
{
lean_object* v___x_1601_; 
v___x_1601_ = lean_obj_once(&l_Lean_Lsp_instFromJsonModuleHierarchyOptions_fromJson___closed__0, &l_Lean_Lsp_instFromJsonModuleHierarchyOptions_fromJson___closed__0_once, _init_l_Lean_Lsp_instFromJsonModuleHierarchyOptions_fromJson___closed__0);
return v___x_1601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonModuleHierarchyOptions_fromJson___boxed(lean_object* v_json_1602_){
_start:
{
lean_object* v_res_1603_; 
v_res_1603_ = l_Lean_Lsp_instFromJsonModuleHierarchyOptions_fromJson(v_json_1602_);
lean_dec(v_json_1602_);
return v_res_1603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonModuleHierarchyOptions_toJson___redArg(){
_start:
{
lean_object* v___x_1607_; 
v___x_1607_ = lean_obj_once(&l_Lean_Lsp_instToJsonWaitForILeans_toJson___redArg___closed__1, &l_Lean_Lsp_instToJsonWaitForILeans_toJson___redArg___closed__1_once, _init_l_Lean_Lsp_instToJsonWaitForILeans_toJson___redArg___closed__1);
return v___x_1607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonModuleHierarchyOptions_toJson___redArg___boxed(lean_object* v___dummy_1608_){
_start:
{
lean_object* v_res_1609_; 
v_res_1609_ = l_Lean_Lsp_instToJsonModuleHierarchyOptions_toJson___redArg();
return v_res_1609_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonModuleHierarchyOptions_toJson___closed__0(void){
_start:
{
lean_object* v___x_1610_; 
v___x_1610_ = l_Lean_Lsp_instToJsonModuleHierarchyOptions_toJson___redArg();
return v___x_1610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonModuleHierarchyOptions_toJson(lean_object* v_x_1611_){
_start:
{
lean_object* v___x_1612_; 
v___x_1612_ = lean_obj_once(&l_Lean_Lsp_instToJsonModuleHierarchyOptions_toJson___closed__0, &l_Lean_Lsp_instToJsonModuleHierarchyOptions_toJson___closed__0_once, _init_l_Lean_Lsp_instToJsonModuleHierarchyOptions_toJson___closed__0);
return v___x_1612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonHighlightMatchesOptions_fromJson___redArg(){
_start:
{
lean_object* v___x_1618_; 
v___x_1618_ = ((lean_object*)(l_Lean_Lsp_instFromJsonHighlightMatchesOptions_fromJson___redArg___closed__0));
return v___x_1618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonHighlightMatchesOptions_fromJson___redArg___boxed(lean_object* v___dummy_1619_){
_start:
{
lean_object* v_res_1620_; 
v_res_1620_ = l_Lean_Lsp_instFromJsonHighlightMatchesOptions_fromJson___redArg();
return v_res_1620_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonHighlightMatchesOptions_fromJson___closed__0(void){
_start:
{
lean_object* v___x_1621_; 
v___x_1621_ = l_Lean_Lsp_instFromJsonHighlightMatchesOptions_fromJson___redArg();
return v___x_1621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonHighlightMatchesOptions_fromJson(lean_object* v_json_1622_){
_start:
{
lean_object* v___x_1623_; 
v___x_1623_ = lean_obj_once(&l_Lean_Lsp_instFromJsonHighlightMatchesOptions_fromJson___closed__0, &l_Lean_Lsp_instFromJsonHighlightMatchesOptions_fromJson___closed__0_once, _init_l_Lean_Lsp_instFromJsonHighlightMatchesOptions_fromJson___closed__0);
return v___x_1623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonHighlightMatchesOptions_fromJson___boxed(lean_object* v_json_1624_){
_start:
{
lean_object* v_res_1625_; 
v_res_1625_ = l_Lean_Lsp_instFromJsonHighlightMatchesOptions_fromJson(v_json_1624_);
lean_dec(v_json_1624_);
return v_res_1625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonHighlightMatchesOptions_toJson___redArg(){
_start:
{
lean_object* v___x_1629_; 
v___x_1629_ = lean_obj_once(&l_Lean_Lsp_instToJsonWaitForILeans_toJson___redArg___closed__1, &l_Lean_Lsp_instToJsonWaitForILeans_toJson___redArg___closed__1_once, _init_l_Lean_Lsp_instToJsonWaitForILeans_toJson___redArg___closed__1);
return v___x_1629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonHighlightMatchesOptions_toJson___redArg___boxed(lean_object* v___dummy_1630_){
_start:
{
lean_object* v_res_1631_; 
v_res_1631_ = l_Lean_Lsp_instToJsonHighlightMatchesOptions_toJson___redArg();
return v_res_1631_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonHighlightMatchesOptions_toJson___closed__0(void){
_start:
{
lean_object* v___x_1632_; 
v___x_1632_ = l_Lean_Lsp_instToJsonHighlightMatchesOptions_toJson___redArg();
return v___x_1632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonHighlightMatchesOptions_toJson(lean_object* v_x_1633_){
_start:
{
lean_object* v___x_1634_; 
v___x_1634_ = lean_obj_once(&l_Lean_Lsp_instToJsonHighlightMatchesOptions_toJson___closed__0, &l_Lean_Lsp_instToJsonHighlightMatchesOptions_toJson___closed__0_once, _init_l_Lean_Lsp_instToJsonHighlightMatchesOptions_toJson___closed__0);
return v___x_1634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__1_spec__2(lean_object* v_x_1639_){
_start:
{
if (lean_obj_tag(v_x_1639_) == 0)
{
lean_object* v___x_1640_; 
v___x_1640_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__1_spec__2___closed__0));
return v___x_1640_;
}
else
{
lean_object* v___x_1641_; 
v___x_1641_ = l_Lean_Lsp_instFromJsonRpcWireFormat_fromJson(v_x_1639_);
if (lean_obj_tag(v___x_1641_) == 0)
{
lean_object* v_a_1642_; lean_object* v___x_1644_; uint8_t v_isShared_1645_; uint8_t v_isSharedCheck_1649_; 
v_a_1642_ = lean_ctor_get(v___x_1641_, 0);
v_isSharedCheck_1649_ = !lean_is_exclusive(v___x_1641_);
if (v_isSharedCheck_1649_ == 0)
{
v___x_1644_ = v___x_1641_;
v_isShared_1645_ = v_isSharedCheck_1649_;
goto v_resetjp_1643_;
}
else
{
lean_inc(v_a_1642_);
lean_dec(v___x_1641_);
v___x_1644_ = lean_box(0);
v_isShared_1645_ = v_isSharedCheck_1649_;
goto v_resetjp_1643_;
}
v_resetjp_1643_:
{
lean_object* v___x_1647_; 
if (v_isShared_1645_ == 0)
{
v___x_1647_ = v___x_1644_;
goto v_reusejp_1646_;
}
else
{
lean_object* v_reuseFailAlloc_1648_; 
v_reuseFailAlloc_1648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1648_, 0, v_a_1642_);
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
lean_object* v_a_1650_; lean_object* v___x_1652_; uint8_t v_isShared_1653_; uint8_t v_isSharedCheck_1658_; 
v_a_1650_ = lean_ctor_get(v___x_1641_, 0);
v_isSharedCheck_1658_ = !lean_is_exclusive(v___x_1641_);
if (v_isSharedCheck_1658_ == 0)
{
v___x_1652_ = v___x_1641_;
v_isShared_1653_ = v_isSharedCheck_1658_;
goto v_resetjp_1651_;
}
else
{
lean_inc(v_a_1650_);
lean_dec(v___x_1641_);
v___x_1652_ = lean_box(0);
v_isShared_1653_ = v_isSharedCheck_1658_;
goto v_resetjp_1651_;
}
v_resetjp_1651_:
{
lean_object* v___x_1654_; lean_object* v___x_1656_; 
v___x_1654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1654_, 0, v_a_1650_);
if (v_isShared_1653_ == 0)
{
lean_ctor_set(v___x_1652_, 0, v___x_1654_);
v___x_1656_ = v___x_1652_;
goto v_reusejp_1655_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(1, 1, 0);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__1(lean_object* v_j_1659_, lean_object* v_k_1660_){
_start:
{
lean_object* v___x_1661_; lean_object* v___x_1662_; 
v___x_1661_ = l_Lean_Json_getObjValD(v_j_1659_, v_k_1660_);
v___x_1662_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__1_spec__2(v___x_1661_);
return v___x_1662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__1___boxed(lean_object* v_j_1663_, lean_object* v_k_1664_){
_start:
{
lean_object* v_res_1665_; 
v_res_1665_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__1(v_j_1663_, v_k_1664_);
lean_dec_ref(v_k_1664_);
return v_res_1665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__0_spec__0(lean_object* v_x_1668_){
_start:
{
if (lean_obj_tag(v_x_1668_) == 0)
{
lean_object* v___x_1669_; 
v___x_1669_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__0_spec__0___closed__0));
return v___x_1669_;
}
else
{
lean_object* v___x_1670_; lean_object* v_a_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; 
v___x_1670_ = lean_obj_once(&l_Lean_Lsp_instFromJsonHighlightMatchesOptions_fromJson___closed__0, &l_Lean_Lsp_instFromJsonHighlightMatchesOptions_fromJson___closed__0_once, _init_l_Lean_Lsp_instFromJsonHighlightMatchesOptions_fromJson___closed__0);
v_a_1671_ = lean_ctor_get(v___x_1670_, 0);
lean_inc(v_a_1671_);
v___x_1672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1672_, 0, v_a_1671_);
v___x_1673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1673_, 0, v___x_1672_);
return v___x_1673_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__0_spec__0___boxed(lean_object* v_x_1674_){
_start:
{
lean_object* v_res_1675_; 
v_res_1675_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__0_spec__0(v_x_1674_);
lean_dec(v_x_1674_);
return v_res_1675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__0(lean_object* v_j_1676_, lean_object* v_k_1677_){
_start:
{
lean_object* v___x_1678_; lean_object* v___x_1679_; 
v___x_1678_ = l_Lean_Json_getObjValD(v_j_1676_, v_k_1677_);
v___x_1679_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__0_spec__0(v___x_1678_);
lean_dec(v___x_1678_);
return v___x_1679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__0___boxed(lean_object* v_j_1680_, lean_object* v_k_1681_){
_start:
{
lean_object* v_res_1682_; 
v_res_1682_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__0(v_j_1680_, v_k_1681_);
lean_dec_ref(v_k_1681_);
return v_res_1682_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__3(void){
_start:
{
uint8_t v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; 
v___x_1689_ = 1;
v___x_1690_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__2));
v___x_1691_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1690_, v___x_1689_);
return v___x_1691_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__4(void){
_start:
{
lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; 
v___x_1692_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6));
v___x_1693_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__3, &l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__3);
v___x_1694_ = lean_string_append(v___x_1693_, v___x_1692_);
return v___x_1694_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__7(void){
_start:
{
uint8_t v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; 
v___x_1698_ = 1;
v___x_1699_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__6));
v___x_1700_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1699_, v___x_1698_);
return v___x_1700_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__8(void){
_start:
{
lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; 
v___x_1701_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__7, &l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__7);
v___x_1702_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__4, &l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__4);
v___x_1703_ = lean_string_append(v___x_1702_, v___x_1701_);
return v___x_1703_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__9(void){
_start:
{
lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; 
v___x_1704_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_1705_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__8, &l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__8);
v___x_1706_ = lean_string_append(v___x_1705_, v___x_1704_);
return v___x_1706_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__13(void){
_start:
{
uint8_t v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; 
v___x_1711_ = 1;
v___x_1712_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__12));
v___x_1713_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1712_, v___x_1711_);
return v___x_1713_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__14(void){
_start:
{
lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; 
v___x_1714_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__13, &l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__13);
v___x_1715_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__4, &l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__4);
v___x_1716_ = lean_string_append(v___x_1715_, v___x_1714_);
return v___x_1716_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__15(void){
_start:
{
lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; 
v___x_1717_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_1718_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__14, &l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__14_once, _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__14);
v___x_1719_ = lean_string_append(v___x_1718_, v___x_1717_);
return v___x_1719_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonRpcOptions_fromJson(lean_object* v_json_1720_){
_start:
{
lean_object* v___x_1721_; lean_object* v___x_1722_; 
v___x_1721_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__0));
lean_inc(v_json_1720_);
v___x_1722_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__0(v_json_1720_, v___x_1721_);
if (lean_obj_tag(v___x_1722_) == 0)
{
lean_object* v_a_1723_; lean_object* v___x_1725_; uint8_t v_isShared_1726_; uint8_t v_isSharedCheck_1732_; 
lean_dec(v_json_1720_);
v_a_1723_ = lean_ctor_get(v___x_1722_, 0);
v_isSharedCheck_1732_ = !lean_is_exclusive(v___x_1722_);
if (v_isSharedCheck_1732_ == 0)
{
v___x_1725_ = v___x_1722_;
v_isShared_1726_ = v_isSharedCheck_1732_;
goto v_resetjp_1724_;
}
else
{
lean_inc(v_a_1723_);
lean_dec(v___x_1722_);
v___x_1725_ = lean_box(0);
v_isShared_1726_ = v_isSharedCheck_1732_;
goto v_resetjp_1724_;
}
v_resetjp_1724_:
{
lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1730_; 
v___x_1727_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__9, &l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__9);
v___x_1728_ = lean_string_append(v___x_1727_, v_a_1723_);
lean_dec(v_a_1723_);
if (v_isShared_1726_ == 0)
{
lean_ctor_set(v___x_1725_, 0, v___x_1728_);
v___x_1730_ = v___x_1725_;
goto v_reusejp_1729_;
}
else
{
lean_object* v_reuseFailAlloc_1731_; 
v_reuseFailAlloc_1731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1731_, 0, v___x_1728_);
v___x_1730_ = v_reuseFailAlloc_1731_;
goto v_reusejp_1729_;
}
v_reusejp_1729_:
{
return v___x_1730_;
}
}
}
else
{
if (lean_obj_tag(v___x_1722_) == 0)
{
lean_object* v_a_1733_; lean_object* v___x_1735_; uint8_t v_isShared_1736_; uint8_t v_isSharedCheck_1740_; 
lean_dec(v_json_1720_);
v_a_1733_ = lean_ctor_get(v___x_1722_, 0);
v_isSharedCheck_1740_ = !lean_is_exclusive(v___x_1722_);
if (v_isSharedCheck_1740_ == 0)
{
v___x_1735_ = v___x_1722_;
v_isShared_1736_ = v_isSharedCheck_1740_;
goto v_resetjp_1734_;
}
else
{
lean_inc(v_a_1733_);
lean_dec(v___x_1722_);
v___x_1735_ = lean_box(0);
v_isShared_1736_ = v_isSharedCheck_1740_;
goto v_resetjp_1734_;
}
v_resetjp_1734_:
{
lean_object* v___x_1738_; 
if (v_isShared_1736_ == 0)
{
lean_ctor_set_tag(v___x_1735_, 0);
v___x_1738_ = v___x_1735_;
goto v_reusejp_1737_;
}
else
{
lean_object* v_reuseFailAlloc_1739_; 
v_reuseFailAlloc_1739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1739_, 0, v_a_1733_);
v___x_1738_ = v_reuseFailAlloc_1739_;
goto v_reusejp_1737_;
}
v_reusejp_1737_:
{
return v___x_1738_;
}
}
}
else
{
lean_object* v_a_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; 
v_a_1741_ = lean_ctor_get(v___x_1722_, 0);
lean_inc(v_a_1741_);
lean_dec_ref_known(v___x_1722_, 1);
v___x_1742_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__10));
v___x_1743_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__1(v_json_1720_, v___x_1742_);
if (lean_obj_tag(v___x_1743_) == 0)
{
lean_object* v_a_1744_; lean_object* v___x_1746_; uint8_t v_isShared_1747_; uint8_t v_isSharedCheck_1753_; 
lean_dec(v_a_1741_);
v_a_1744_ = lean_ctor_get(v___x_1743_, 0);
v_isSharedCheck_1753_ = !lean_is_exclusive(v___x_1743_);
if (v_isSharedCheck_1753_ == 0)
{
v___x_1746_ = v___x_1743_;
v_isShared_1747_ = v_isSharedCheck_1753_;
goto v_resetjp_1745_;
}
else
{
lean_inc(v_a_1744_);
lean_dec(v___x_1743_);
v___x_1746_ = lean_box(0);
v_isShared_1747_ = v_isSharedCheck_1753_;
goto v_resetjp_1745_;
}
v_resetjp_1745_:
{
lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1751_; 
v___x_1748_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__15, &l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__15_once, _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__15);
v___x_1749_ = lean_string_append(v___x_1748_, v_a_1744_);
lean_dec(v_a_1744_);
if (v_isShared_1747_ == 0)
{
lean_ctor_set(v___x_1746_, 0, v___x_1749_);
v___x_1751_ = v___x_1746_;
goto v_reusejp_1750_;
}
else
{
lean_object* v_reuseFailAlloc_1752_; 
v_reuseFailAlloc_1752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1752_, 0, v___x_1749_);
v___x_1751_ = v_reuseFailAlloc_1752_;
goto v_reusejp_1750_;
}
v_reusejp_1750_:
{
return v___x_1751_;
}
}
}
else
{
if (lean_obj_tag(v___x_1743_) == 0)
{
lean_object* v_a_1754_; lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1761_; 
lean_dec(v_a_1741_);
v_a_1754_ = lean_ctor_get(v___x_1743_, 0);
v_isSharedCheck_1761_ = !lean_is_exclusive(v___x_1743_);
if (v_isSharedCheck_1761_ == 0)
{
v___x_1756_ = v___x_1743_;
v_isShared_1757_ = v_isSharedCheck_1761_;
goto v_resetjp_1755_;
}
else
{
lean_inc(v_a_1754_);
lean_dec(v___x_1743_);
v___x_1756_ = lean_box(0);
v_isShared_1757_ = v_isSharedCheck_1761_;
goto v_resetjp_1755_;
}
v_resetjp_1755_:
{
lean_object* v___x_1759_; 
if (v_isShared_1757_ == 0)
{
lean_ctor_set_tag(v___x_1756_, 0);
v___x_1759_ = v___x_1756_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1760_; 
v_reuseFailAlloc_1760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1760_, 0, v_a_1754_);
v___x_1759_ = v_reuseFailAlloc_1760_;
goto v_reusejp_1758_;
}
v_reusejp_1758_:
{
return v___x_1759_;
}
}
}
else
{
lean_object* v_a_1762_; lean_object* v___x_1764_; uint8_t v_isShared_1765_; uint8_t v_isSharedCheck_1770_; 
v_a_1762_ = lean_ctor_get(v___x_1743_, 0);
v_isSharedCheck_1770_ = !lean_is_exclusive(v___x_1743_);
if (v_isSharedCheck_1770_ == 0)
{
v___x_1764_ = v___x_1743_;
v_isShared_1765_ = v_isSharedCheck_1770_;
goto v_resetjp_1763_;
}
else
{
lean_inc(v_a_1762_);
lean_dec(v___x_1743_);
v___x_1764_ = lean_box(0);
v_isShared_1765_ = v_isSharedCheck_1770_;
goto v_resetjp_1763_;
}
v_resetjp_1763_:
{
lean_object* v___x_1766_; lean_object* v___x_1768_; 
v___x_1766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1766_, 0, v_a_1741_);
lean_ctor_set(v___x_1766_, 1, v_a_1762_);
if (v_isShared_1765_ == 0)
{
lean_ctor_set(v___x_1764_, 0, v___x_1766_);
v___x_1768_ = v___x_1764_;
goto v_reusejp_1767_;
}
else
{
lean_object* v_reuseFailAlloc_1769_; 
v_reuseFailAlloc_1769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1769_, 0, v___x_1766_);
v___x_1768_ = v_reuseFailAlloc_1769_;
goto v_reusejp_1767_;
}
v_reusejp_1767_:
{
return v___x_1768_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonRpcOptions_toJson_spec__0(lean_object* v_k_1773_, lean_object* v_x_1774_){
_start:
{
if (lean_obj_tag(v_x_1774_) == 0)
{
lean_object* v___x_1775_; 
lean_dec_ref(v_k_1773_);
v___x_1775_ = lean_box(0);
return v___x_1775_;
}
else
{
lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; 
v___x_1776_ = lean_obj_once(&l_Lean_Lsp_instToJsonHighlightMatchesOptions_toJson___closed__0, &l_Lean_Lsp_instToJsonHighlightMatchesOptions_toJson___closed__0_once, _init_l_Lean_Lsp_instToJsonHighlightMatchesOptions_toJson___closed__0);
v___x_1777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1777_, 0, v_k_1773_);
lean_ctor_set(v___x_1777_, 1, v___x_1776_);
v___x_1778_ = lean_box(0);
v___x_1779_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1779_, 0, v___x_1777_);
lean_ctor_set(v___x_1779_, 1, v___x_1778_);
return v___x_1779_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonRpcOptions_toJson_spec__0___boxed(lean_object* v_k_1780_, lean_object* v_x_1781_){
_start:
{
lean_object* v_res_1782_; 
v_res_1782_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonRpcOptions_toJson_spec__0(v_k_1780_, v_x_1781_);
lean_dec(v_x_1781_);
return v_res_1782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonRpcOptions_toJson_spec__1(lean_object* v_k_1783_, lean_object* v_x_1784_){
_start:
{
if (lean_obj_tag(v_x_1784_) == 0)
{
lean_object* v___x_1785_; 
lean_dec_ref(v_k_1783_);
v___x_1785_ = lean_box(0);
return v___x_1785_;
}
else
{
lean_object* v_val_1786_; uint8_t v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; 
v_val_1786_ = lean_ctor_get(v_x_1784_, 0);
v___x_1787_ = lean_unbox(v_val_1786_);
v___x_1788_ = l_Lean_Lsp_instToJsonRpcWireFormat_toJson(v___x_1787_);
v___x_1789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1789_, 0, v_k_1783_);
lean_ctor_set(v___x_1789_, 1, v___x_1788_);
v___x_1790_ = lean_box(0);
v___x_1791_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1791_, 0, v___x_1789_);
lean_ctor_set(v___x_1791_, 1, v___x_1790_);
return v___x_1791_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonRpcOptions_toJson_spec__1___boxed(lean_object* v_k_1792_, lean_object* v_x_1793_){
_start:
{
lean_object* v_res_1794_; 
v_res_1794_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonRpcOptions_toJson_spec__1(v_k_1792_, v_x_1793_);
lean_dec(v_x_1793_);
return v_res_1794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRpcOptions_toJson(lean_object* v_x_1795_){
_start:
{
lean_object* v_highlightMatchesProvider_x3f_1796_; lean_object* v_rpcWireFormat_x3f_1797_; lean_object* v___x_1799_; uint8_t v_isShared_1800_; uint8_t v_isSharedCheck_1813_; 
v_highlightMatchesProvider_x3f_1796_ = lean_ctor_get(v_x_1795_, 0);
v_rpcWireFormat_x3f_1797_ = lean_ctor_get(v_x_1795_, 1);
v_isSharedCheck_1813_ = !lean_is_exclusive(v_x_1795_);
if (v_isSharedCheck_1813_ == 0)
{
v___x_1799_ = v_x_1795_;
v_isShared_1800_ = v_isSharedCheck_1813_;
goto v_resetjp_1798_;
}
else
{
lean_inc(v_rpcWireFormat_x3f_1797_);
lean_inc(v_highlightMatchesProvider_x3f_1796_);
lean_dec(v_x_1795_);
v___x_1799_ = lean_box(0);
v_isShared_1800_ = v_isSharedCheck_1813_;
goto v_resetjp_1798_;
}
v_resetjp_1798_:
{
lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1807_; 
v___x_1801_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__0));
v___x_1802_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonRpcOptions_toJson_spec__0(v___x_1801_, v_highlightMatchesProvider_x3f_1796_);
lean_dec(v_highlightMatchesProvider_x3f_1796_);
v___x_1803_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__10));
v___x_1804_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonRpcOptions_toJson_spec__1(v___x_1803_, v_rpcWireFormat_x3f_1797_);
lean_dec(v_rpcWireFormat_x3f_1797_);
v___x_1805_ = lean_box(0);
if (v_isShared_1800_ == 0)
{
lean_ctor_set_tag(v___x_1799_, 1);
lean_ctor_set(v___x_1799_, 1, v___x_1805_);
lean_ctor_set(v___x_1799_, 0, v___x_1804_);
v___x_1807_ = v___x_1799_;
goto v_reusejp_1806_;
}
else
{
lean_object* v_reuseFailAlloc_1812_; 
v_reuseFailAlloc_1812_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1812_, 0, v___x_1804_);
lean_ctor_set(v_reuseFailAlloc_1812_, 1, v___x_1805_);
v___x_1807_ = v_reuseFailAlloc_1812_;
goto v_reusejp_1806_;
}
v_reusejp_1806_:
{
lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; 
v___x_1808_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1808_, 0, v___x_1802_);
lean_ctor_set(v___x_1808_, 1, v___x_1807_);
v___x_1809_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0));
v___x_1810_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_1808_, v___x_1809_);
v___x_1811_ = l_Lean_Json_mkObj(v___x_1810_);
lean_dec(v___x_1810_);
return v___x_1811_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModule_fromJson_spec__0_spec__0(lean_object* v_x_1818_){
_start:
{
if (lean_obj_tag(v_x_1818_) == 0)
{
lean_object* v___x_1819_; 
v___x_1819_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModule_fromJson_spec__0_spec__0___closed__0));
return v___x_1819_;
}
else
{
lean_object* v___x_1820_; lean_object* v___x_1821_; 
v___x_1820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1820_, 0, v_x_1818_);
v___x_1821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1821_, 0, v___x_1820_);
return v___x_1821_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModule_fromJson_spec__0(lean_object* v_j_1822_, lean_object* v_k_1823_){
_start:
{
lean_object* v___x_1824_; lean_object* v___x_1825_; 
v___x_1824_ = l_Lean_Json_getObjValD(v_j_1822_, v_k_1823_);
v___x_1825_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModule_fromJson_spec__0_spec__0(v___x_1824_);
return v___x_1825_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModule_fromJson_spec__0___boxed(lean_object* v_j_1826_, lean_object* v_k_1827_){
_start:
{
lean_object* v_res_1828_; 
v_res_1828_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModule_fromJson_spec__0(v_j_1826_, v_k_1827_);
lean_dec_ref(v_k_1827_);
return v_res_1828_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__3(void){
_start:
{
uint8_t v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; 
v___x_1835_ = 1;
v___x_1836_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__2));
v___x_1837_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1836_, v___x_1835_);
return v___x_1837_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__4(void){
_start:
{
lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; 
v___x_1838_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6));
v___x_1839_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__3);
v___x_1840_ = lean_string_append(v___x_1839_, v___x_1838_);
return v___x_1840_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__6(void){
_start:
{
uint8_t v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; 
v___x_1843_ = 1;
v___x_1844_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__5));
v___x_1845_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1844_, v___x_1843_);
return v___x_1845_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__7(void){
_start:
{
lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; 
v___x_1846_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__6);
v___x_1847_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__4);
v___x_1848_ = lean_string_append(v___x_1847_, v___x_1846_);
return v___x_1848_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__8(void){
_start:
{
lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; 
v___x_1849_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_1850_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__7);
v___x_1851_ = lean_string_append(v___x_1850_, v___x_1849_);
return v___x_1851_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__9(void){
_start:
{
lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; 
v___x_1852_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__6, &l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__6);
v___x_1853_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__4);
v___x_1854_ = lean_string_append(v___x_1853_, v___x_1852_);
return v___x_1854_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__10(void){
_start:
{
lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; 
v___x_1855_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_1856_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__9, &l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__9);
v___x_1857_ = lean_string_append(v___x_1856_, v___x_1855_);
return v___x_1857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanModule_fromJson(lean_object* v_json_1859_){
_start:
{
lean_object* v___x_1860_; lean_object* v___x_1861_; 
v___x_1860_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__0));
lean_inc(v_json_1859_);
v___x_1861_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson_spec__0(v_json_1859_, v___x_1860_);
if (lean_obj_tag(v___x_1861_) == 0)
{
lean_object* v_a_1862_; lean_object* v___x_1864_; uint8_t v_isShared_1865_; uint8_t v_isSharedCheck_1871_; 
lean_dec(v_json_1859_);
v_a_1862_ = lean_ctor_get(v___x_1861_, 0);
v_isSharedCheck_1871_ = !lean_is_exclusive(v___x_1861_);
if (v_isSharedCheck_1871_ == 0)
{
v___x_1864_ = v___x_1861_;
v_isShared_1865_ = v_isSharedCheck_1871_;
goto v_resetjp_1863_;
}
else
{
lean_inc(v_a_1862_);
lean_dec(v___x_1861_);
v___x_1864_ = lean_box(0);
v_isShared_1865_ = v_isSharedCheck_1871_;
goto v_resetjp_1863_;
}
v_resetjp_1863_:
{
lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1869_; 
v___x_1866_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__8);
v___x_1867_ = lean_string_append(v___x_1866_, v_a_1862_);
lean_dec(v_a_1862_);
if (v_isShared_1865_ == 0)
{
lean_ctor_set(v___x_1864_, 0, v___x_1867_);
v___x_1869_ = v___x_1864_;
goto v_reusejp_1868_;
}
else
{
lean_object* v_reuseFailAlloc_1870_; 
v_reuseFailAlloc_1870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1870_, 0, v___x_1867_);
v___x_1869_ = v_reuseFailAlloc_1870_;
goto v_reusejp_1868_;
}
v_reusejp_1868_:
{
return v___x_1869_;
}
}
}
else
{
if (lean_obj_tag(v___x_1861_) == 0)
{
lean_object* v_a_1872_; lean_object* v___x_1874_; uint8_t v_isShared_1875_; uint8_t v_isSharedCheck_1879_; 
lean_dec(v_json_1859_);
v_a_1872_ = lean_ctor_get(v___x_1861_, 0);
v_isSharedCheck_1879_ = !lean_is_exclusive(v___x_1861_);
if (v_isSharedCheck_1879_ == 0)
{
v___x_1874_ = v___x_1861_;
v_isShared_1875_ = v_isSharedCheck_1879_;
goto v_resetjp_1873_;
}
else
{
lean_inc(v_a_1872_);
lean_dec(v___x_1861_);
v___x_1874_ = lean_box(0);
v_isShared_1875_ = v_isSharedCheck_1879_;
goto v_resetjp_1873_;
}
v_resetjp_1873_:
{
lean_object* v___x_1877_; 
if (v_isShared_1875_ == 0)
{
lean_ctor_set_tag(v___x_1874_, 0);
v___x_1877_ = v___x_1874_;
goto v_reusejp_1876_;
}
else
{
lean_object* v_reuseFailAlloc_1878_; 
v_reuseFailAlloc_1878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1878_, 0, v_a_1872_);
v___x_1877_ = v_reuseFailAlloc_1878_;
goto v_reusejp_1876_;
}
v_reusejp_1876_:
{
return v___x_1877_;
}
}
}
else
{
lean_object* v_a_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; 
v_a_1880_ = lean_ctor_get(v___x_1861_, 0);
lean_inc(v_a_1880_);
lean_dec_ref_known(v___x_1861_, 1);
v___x_1881_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__0));
lean_inc(v_json_1859_);
v___x_1882_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson_spec__0(v_json_1859_, v___x_1881_);
if (lean_obj_tag(v___x_1882_) == 0)
{
lean_object* v_a_1883_; lean_object* v___x_1885_; uint8_t v_isShared_1886_; uint8_t v_isSharedCheck_1892_; 
lean_dec(v_a_1880_);
lean_dec(v_json_1859_);
v_a_1883_ = lean_ctor_get(v___x_1882_, 0);
v_isSharedCheck_1892_ = !lean_is_exclusive(v___x_1882_);
if (v_isSharedCheck_1892_ == 0)
{
v___x_1885_ = v___x_1882_;
v_isShared_1886_ = v_isSharedCheck_1892_;
goto v_resetjp_1884_;
}
else
{
lean_inc(v_a_1883_);
lean_dec(v___x_1882_);
v___x_1885_ = lean_box(0);
v_isShared_1886_ = v_isSharedCheck_1892_;
goto v_resetjp_1884_;
}
v_resetjp_1884_:
{
lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1890_; 
v___x_1887_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__10, &l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__10);
v___x_1888_ = lean_string_append(v___x_1887_, v_a_1883_);
lean_dec(v_a_1883_);
if (v_isShared_1886_ == 0)
{
lean_ctor_set(v___x_1885_, 0, v___x_1888_);
v___x_1890_ = v___x_1885_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1891_; 
v_reuseFailAlloc_1891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1891_, 0, v___x_1888_);
v___x_1890_ = v_reuseFailAlloc_1891_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
return v___x_1890_;
}
}
}
else
{
if (lean_obj_tag(v___x_1882_) == 0)
{
lean_object* v_a_1893_; lean_object* v___x_1895_; uint8_t v_isShared_1896_; uint8_t v_isSharedCheck_1900_; 
lean_dec(v_a_1880_);
lean_dec(v_json_1859_);
v_a_1893_ = lean_ctor_get(v___x_1882_, 0);
v_isSharedCheck_1900_ = !lean_is_exclusive(v___x_1882_);
if (v_isSharedCheck_1900_ == 0)
{
v___x_1895_ = v___x_1882_;
v_isShared_1896_ = v_isSharedCheck_1900_;
goto v_resetjp_1894_;
}
else
{
lean_inc(v_a_1893_);
lean_dec(v___x_1882_);
v___x_1895_ = lean_box(0);
v_isShared_1896_ = v_isSharedCheck_1900_;
goto v_resetjp_1894_;
}
v_resetjp_1894_:
{
lean_object* v___x_1898_; 
if (v_isShared_1896_ == 0)
{
lean_ctor_set_tag(v___x_1895_, 0);
v___x_1898_ = v___x_1895_;
goto v_reusejp_1897_;
}
else
{
lean_object* v_reuseFailAlloc_1899_; 
v_reuseFailAlloc_1899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1899_, 0, v_a_1893_);
v___x_1898_ = v_reuseFailAlloc_1899_;
goto v_reusejp_1897_;
}
v_reusejp_1897_:
{
return v___x_1898_;
}
}
}
else
{
lean_object* v_a_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v_a_1904_; lean_object* v___x_1906_; uint8_t v_isShared_1907_; uint8_t v_isSharedCheck_1912_; 
v_a_1901_ = lean_ctor_get(v___x_1882_, 0);
lean_inc(v_a_1901_);
lean_dec_ref_known(v___x_1882_, 1);
v___x_1902_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__11));
v___x_1903_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModule_fromJson_spec__0(v_json_1859_, v___x_1902_);
v_a_1904_ = lean_ctor_get(v___x_1903_, 0);
v_isSharedCheck_1912_ = !lean_is_exclusive(v___x_1903_);
if (v_isSharedCheck_1912_ == 0)
{
v___x_1906_ = v___x_1903_;
v_isShared_1907_ = v_isSharedCheck_1912_;
goto v_resetjp_1905_;
}
else
{
lean_inc(v_a_1904_);
lean_dec(v___x_1903_);
v___x_1906_ = lean_box(0);
v_isShared_1907_ = v_isSharedCheck_1912_;
goto v_resetjp_1905_;
}
v_resetjp_1905_:
{
lean_object* v___x_1908_; lean_object* v___x_1910_; 
v___x_1908_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1908_, 0, v_a_1880_);
lean_ctor_set(v___x_1908_, 1, v_a_1901_);
lean_ctor_set(v___x_1908_, 2, v_a_1904_);
if (v_isShared_1907_ == 0)
{
lean_ctor_set(v___x_1906_, 0, v___x_1908_);
v___x_1910_ = v___x_1906_;
goto v_reusejp_1909_;
}
else
{
lean_object* v_reuseFailAlloc_1911_; 
v_reuseFailAlloc_1911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1911_, 0, v___x_1908_);
v___x_1910_ = v_reuseFailAlloc_1911_;
goto v_reusejp_1909_;
}
v_reusejp_1909_:
{
return v___x_1910_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanModule_toJson_spec__0(lean_object* v_k_1915_, lean_object* v_x_1916_){
_start:
{
if (lean_obj_tag(v_x_1916_) == 0)
{
lean_object* v___x_1917_; 
lean_dec_ref(v_k_1915_);
v___x_1917_ = lean_box(0);
return v___x_1917_;
}
else
{
lean_object* v_val_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; 
v_val_1918_ = lean_ctor_get(v_x_1916_, 0);
lean_inc(v_val_1918_);
v___x_1919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1919_, 0, v_k_1915_);
lean_ctor_set(v___x_1919_, 1, v_val_1918_);
v___x_1920_ = lean_box(0);
v___x_1921_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1921_, 0, v___x_1919_);
lean_ctor_set(v___x_1921_, 1, v___x_1920_);
return v___x_1921_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanModule_toJson_spec__0___boxed(lean_object* v_k_1922_, lean_object* v_x_1923_){
_start:
{
lean_object* v_res_1924_; 
v_res_1924_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanModule_toJson_spec__0(v_k_1922_, v_x_1923_);
lean_dec(v_x_1923_);
return v_res_1924_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanModule_toJson(lean_object* v_x_1925_){
_start:
{
lean_object* v_name_1926_; lean_object* v_uri_1927_; lean_object* v_data_x3f_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; 
v_name_1926_ = lean_ctor_get(v_x_1925_, 0);
v_uri_1927_ = lean_ctor_get(v_x_1925_, 1);
v_data_x3f_1928_ = lean_ctor_get(v_x_1925_, 2);
v___x_1929_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__0));
lean_inc_ref(v_name_1926_);
v___x_1930_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1930_, 0, v_name_1926_);
v___x_1931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1931_, 0, v___x_1929_);
lean_ctor_set(v___x_1931_, 1, v___x_1930_);
v___x_1932_ = lean_box(0);
v___x_1933_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1933_, 0, v___x_1931_);
lean_ctor_set(v___x_1933_, 1, v___x_1932_);
v___x_1934_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__0));
lean_inc_ref(v_uri_1927_);
v___x_1935_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1935_, 0, v_uri_1927_);
v___x_1936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1936_, 0, v___x_1934_);
lean_ctor_set(v___x_1936_, 1, v___x_1935_);
v___x_1937_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1937_, 0, v___x_1936_);
lean_ctor_set(v___x_1937_, 1, v___x_1932_);
v___x_1938_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__11));
v___x_1939_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanModule_toJson_spec__0(v___x_1938_, v_data_x3f_1928_);
v___x_1940_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1940_, 0, v___x_1939_);
lean_ctor_set(v___x_1940_, 1, v___x_1932_);
v___x_1941_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1941_, 0, v___x_1937_);
lean_ctor_set(v___x_1941_, 1, v___x_1940_);
v___x_1942_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1942_, 0, v___x_1933_);
lean_ctor_set(v___x_1942_, 1, v___x_1941_);
v___x_1943_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0));
v___x_1944_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_1942_, v___x_1943_);
v___x_1945_ = l_Lean_Json_mkObj(v___x_1944_);
lean_dec(v___x_1944_);
return v___x_1945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanModule_toJson___boxed(lean_object* v_x_1946_){
_start:
{
lean_object* v_res_1947_; 
v_res_1947_ = l_Lean_Lsp_instToJsonLeanModule_toJson(v_x_1946_);
lean_dec_ref(v_x_1946_);
return v_res_1947_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__2(void){
_start:
{
uint8_t v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; 
v___x_1955_ = 1;
v___x_1956_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__1));
v___x_1957_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1956_, v___x_1955_);
return v___x_1957_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__3(void){
_start:
{
lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; 
v___x_1958_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6));
v___x_1959_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__2, &l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__2);
v___x_1960_ = lean_string_append(v___x_1959_, v___x_1958_);
return v___x_1960_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; 
v___x_1961_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9, &l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9);
v___x_1962_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__3);
v___x_1963_ = lean_string_append(v___x_1962_, v___x_1961_);
return v___x_1963_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__5(void){
_start:
{
lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; 
v___x_1964_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_1965_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__4);
v___x_1966_ = lean_string_append(v___x_1965_, v___x_1964_);
return v___x_1966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson(lean_object* v_json_1967_){
_start:
{
lean_object* v___x_1968_; lean_object* v___x_1969_; 
v___x_1968_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__0));
v___x_1969_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoalParams_fromJson_spec__0(v_json_1967_, v___x_1968_);
if (lean_obj_tag(v___x_1969_) == 0)
{
lean_object* v_a_1970_; lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_1979_; 
v_a_1970_ = lean_ctor_get(v___x_1969_, 0);
v_isSharedCheck_1979_ = !lean_is_exclusive(v___x_1969_);
if (v_isSharedCheck_1979_ == 0)
{
v___x_1972_ = v___x_1969_;
v_isShared_1973_ = v_isSharedCheck_1979_;
goto v_resetjp_1971_;
}
else
{
lean_inc(v_a_1970_);
lean_dec(v___x_1969_);
v___x_1972_ = lean_box(0);
v_isShared_1973_ = v_isSharedCheck_1979_;
goto v_resetjp_1971_;
}
v_resetjp_1971_:
{
lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1977_; 
v___x_1974_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__5, &l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__5);
v___x_1975_ = lean_string_append(v___x_1974_, v_a_1970_);
lean_dec(v_a_1970_);
if (v_isShared_1973_ == 0)
{
lean_ctor_set(v___x_1972_, 0, v___x_1975_);
v___x_1977_ = v___x_1972_;
goto v_reusejp_1976_;
}
else
{
lean_object* v_reuseFailAlloc_1978_; 
v_reuseFailAlloc_1978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1978_, 0, v___x_1975_);
v___x_1977_ = v_reuseFailAlloc_1978_;
goto v_reusejp_1976_;
}
v_reusejp_1976_:
{
return v___x_1977_;
}
}
}
else
{
if (lean_obj_tag(v___x_1969_) == 0)
{
lean_object* v_a_1980_; lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_1987_; 
v_a_1980_ = lean_ctor_get(v___x_1969_, 0);
v_isSharedCheck_1987_ = !lean_is_exclusive(v___x_1969_);
if (v_isSharedCheck_1987_ == 0)
{
v___x_1982_ = v___x_1969_;
v_isShared_1983_ = v_isSharedCheck_1987_;
goto v_resetjp_1981_;
}
else
{
lean_inc(v_a_1980_);
lean_dec(v___x_1969_);
v___x_1982_ = lean_box(0);
v_isShared_1983_ = v_isSharedCheck_1987_;
goto v_resetjp_1981_;
}
v_resetjp_1981_:
{
lean_object* v___x_1985_; 
if (v_isShared_1983_ == 0)
{
lean_ctor_set_tag(v___x_1982_, 0);
v___x_1985_ = v___x_1982_;
goto v_reusejp_1984_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v_a_1980_);
v___x_1985_ = v_reuseFailAlloc_1986_;
goto v_reusejp_1984_;
}
v_reusejp_1984_:
{
return v___x_1985_;
}
}
}
else
{
lean_object* v_a_1988_; lean_object* v___x_1990_; uint8_t v_isShared_1991_; uint8_t v_isSharedCheck_1995_; 
v_a_1988_ = lean_ctor_get(v___x_1969_, 0);
v_isSharedCheck_1995_ = !lean_is_exclusive(v___x_1969_);
if (v_isSharedCheck_1995_ == 0)
{
v___x_1990_ = v___x_1969_;
v_isShared_1991_ = v_isSharedCheck_1995_;
goto v_resetjp_1989_;
}
else
{
lean_inc(v_a_1988_);
lean_dec(v___x_1969_);
v___x_1990_ = lean_box(0);
v_isShared_1991_ = v_isSharedCheck_1995_;
goto v_resetjp_1989_;
}
v_resetjp_1989_:
{
lean_object* v___x_1993_; 
if (v_isShared_1991_ == 0)
{
v___x_1993_ = v___x_1990_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v_a_1988_);
v___x_1993_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1992_;
}
v_reusejp_1992_:
{
return v___x_1993_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanPrepareModuleHierarchyParams_toJson(lean_object* v_x_1998_){
_start:
{
lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; 
v___x_1999_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__0));
v___x_2000_ = l_Lean_Lsp_instToJsonTextDocumentIdentifier_toJson(v_x_1998_);
v___x_2001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2001_, 0, v___x_1999_);
lean_ctor_set(v___x_2001_, 1, v___x_2000_);
v___x_2002_ = lean_box(0);
v___x_2003_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2003_, 0, v___x_2001_);
lean_ctor_set(v___x_2003_, 1, v___x_2002_);
v___x_2004_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2004_, 0, v___x_2003_);
lean_ctor_set(v___x_2004_, 1, v___x_2002_);
v___x_2005_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0));
v___x_2006_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_2004_, v___x_2005_);
v___x_2007_ = l_Lean_Json_mkObj(v___x_2006_);
lean_dec(v___x_2006_);
return v___x_2007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanImportMetaKind_ctorIdx(uint8_t v_x_2010_){
_start:
{
switch(v_x_2010_)
{
case 0:
{
lean_object* v___x_2011_; 
v___x_2011_ = lean_unsigned_to_nat(0u);
return v___x_2011_;
}
case 1:
{
lean_object* v___x_2012_; 
v___x_2012_ = lean_unsigned_to_nat(1u);
return v___x_2012_;
}
default: 
{
lean_object* v___x_2013_; 
v___x_2013_ = lean_unsigned_to_nat(2u);
return v___x_2013_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanImportMetaKind_ctorIdx___boxed(lean_object* v_x_2014_){
_start:
{
uint8_t v_x_boxed_2015_; lean_object* v_res_2016_; 
v_x_boxed_2015_ = lean_unbox(v_x_2014_);
v_res_2016_ = l_Lean_Lsp_LeanImportMetaKind_ctorIdx(v_x_boxed_2015_);
return v_res_2016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanImportMetaKind_ctorElim___redArg(lean_object* v_k_2017_){
_start:
{
lean_inc(v_k_2017_);
return v_k_2017_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanImportMetaKind_ctorElim___redArg___boxed(lean_object* v_k_2018_){
_start:
{
lean_object* v_res_2019_; 
v_res_2019_ = l_Lean_Lsp_LeanImportMetaKind_ctorElim___redArg(v_k_2018_);
lean_dec(v_k_2018_);
return v_res_2019_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanImportMetaKind_ctorElim(lean_object* v_motive_2020_, lean_object* v_ctorIdx_2021_, uint8_t v_t_2022_, lean_object* v_h_2023_, lean_object* v_k_2024_){
_start:
{
lean_inc(v_k_2024_);
return v_k_2024_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanImportMetaKind_ctorElim___boxed(lean_object* v_motive_2025_, lean_object* v_ctorIdx_2026_, lean_object* v_t_2027_, lean_object* v_h_2028_, lean_object* v_k_2029_){
_start:
{
uint8_t v_t_boxed_2030_; lean_object* v_res_2031_; 
v_t_boxed_2030_ = lean_unbox(v_t_2027_);
v_res_2031_ = l_Lean_Lsp_LeanImportMetaKind_ctorElim(v_motive_2025_, v_ctorIdx_2026_, v_t_boxed_2030_, v_h_2028_, v_k_2029_);
lean_dec(v_k_2029_);
lean_dec(v_ctorIdx_2026_);
return v_res_2031_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanImportMetaKind_nonMeta_elim___redArg(lean_object* v_nonMeta_2032_){
_start:
{
lean_inc(v_nonMeta_2032_);
return v_nonMeta_2032_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanImportMetaKind_nonMeta_elim___redArg___boxed(lean_object* v_nonMeta_2033_){
_start:
{
lean_object* v_res_2034_; 
v_res_2034_ = l_Lean_Lsp_LeanImportMetaKind_nonMeta_elim___redArg(v_nonMeta_2033_);
lean_dec(v_nonMeta_2033_);
return v_res_2034_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanImportMetaKind_nonMeta_elim(lean_object* v_motive_2035_, uint8_t v_t_2036_, lean_object* v_h_2037_, lean_object* v_nonMeta_2038_){
_start:
{
lean_inc(v_nonMeta_2038_);
return v_nonMeta_2038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanImportMetaKind_nonMeta_elim___boxed(lean_object* v_motive_2039_, lean_object* v_t_2040_, lean_object* v_h_2041_, lean_object* v_nonMeta_2042_){
_start:
{
uint8_t v_t_boxed_2043_; lean_object* v_res_2044_; 
v_t_boxed_2043_ = lean_unbox(v_t_2040_);
v_res_2044_ = l_Lean_Lsp_LeanImportMetaKind_nonMeta_elim(v_motive_2039_, v_t_boxed_2043_, v_h_2041_, v_nonMeta_2042_);
lean_dec(v_nonMeta_2042_);
return v_res_2044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanImportMetaKind_meta_elim___redArg(lean_object* v_meta_2045_){
_start:
{
lean_inc(v_meta_2045_);
return v_meta_2045_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanImportMetaKind_meta_elim___redArg___boxed(lean_object* v_meta_2046_){
_start:
{
lean_object* v_res_2047_; 
v_res_2047_ = l_Lean_Lsp_LeanImportMetaKind_meta_elim___redArg(v_meta_2046_);
lean_dec(v_meta_2046_);
return v_res_2047_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanImportMetaKind_meta_elim(lean_object* v_motive_2048_, uint8_t v_t_2049_, lean_object* v_h_2050_, lean_object* v_meta_2051_){
_start:
{
lean_inc(v_meta_2051_);
return v_meta_2051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanImportMetaKind_meta_elim___boxed(lean_object* v_motive_2052_, lean_object* v_t_2053_, lean_object* v_h_2054_, lean_object* v_meta_2055_){
_start:
{
uint8_t v_t_boxed_2056_; lean_object* v_res_2057_; 
v_t_boxed_2056_ = lean_unbox(v_t_2053_);
v_res_2057_ = l_Lean_Lsp_LeanImportMetaKind_meta_elim(v_motive_2052_, v_t_boxed_2056_, v_h_2054_, v_meta_2055_);
lean_dec(v_meta_2055_);
return v_res_2057_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanImportMetaKind_full_elim___redArg(lean_object* v_full_2058_){
_start:
{
lean_inc(v_full_2058_);
return v_full_2058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanImportMetaKind_full_elim___redArg___boxed(lean_object* v_full_2059_){
_start:
{
lean_object* v_res_2060_; 
v_res_2060_ = l_Lean_Lsp_LeanImportMetaKind_full_elim___redArg(v_full_2059_);
lean_dec(v_full_2059_);
return v_res_2060_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanImportMetaKind_full_elim(lean_object* v_motive_2061_, uint8_t v_t_2062_, lean_object* v_h_2063_, lean_object* v_full_2064_){
_start:
{
lean_inc(v_full_2064_);
return v_full_2064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanImportMetaKind_full_elim___boxed(lean_object* v_motive_2065_, lean_object* v_t_2066_, lean_object* v_h_2067_, lean_object* v_full_2068_){
_start:
{
uint8_t v_t_boxed_2069_; lean_object* v_res_2070_; 
v_t_boxed_2069_ = lean_unbox(v_t_2066_);
v_res_2070_ = l_Lean_Lsp_LeanImportMetaKind_full_elim(v_motive_2065_, v_t_boxed_2069_, v_h_2067_, v_full_2068_);
lean_dec(v_full_2068_);
return v_res_2070_;
}
}
static uint8_t _init_l_Lean_Lsp_instInhabitedLeanImportMetaKind_default(void){
_start:
{
uint8_t v___x_2071_; 
v___x_2071_ = 0;
return v___x_2071_;
}
}
static uint8_t _init_l_Lean_Lsp_instInhabitedLeanImportMetaKind(void){
_start:
{
uint8_t v___x_2072_; 
v___x_2072_ = 0;
return v___x_2072_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson(lean_object* v_json_2089_){
_start:
{
lean_object* v___x_2090_; 
v___x_2090_ = l_Lean_Json_getTag_x3f(v_json_2089_);
if (lean_obj_tag(v___x_2090_) == 0)
{
lean_object* v___x_2091_; 
v___x_2091_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson___closed__0));
return v___x_2091_;
}
else
{
lean_object* v_val_2092_; lean_object* v___x_2093_; uint8_t v___x_2094_; 
v_val_2092_ = lean_ctor_get(v___x_2090_, 0);
lean_inc(v_val_2092_);
lean_dec_ref_known(v___x_2090_, 1);
v___x_2093_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson___closed__1));
v___x_2094_ = lean_string_dec_eq(v_val_2092_, v___x_2093_);
if (v___x_2094_ == 0)
{
lean_object* v___x_2095_; uint8_t v___x_2096_; 
v___x_2095_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson___closed__2));
v___x_2096_ = lean_string_dec_eq(v_val_2092_, v___x_2095_);
if (v___x_2096_ == 0)
{
lean_object* v___x_2097_; uint8_t v___x_2098_; 
v___x_2097_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson___closed__3));
v___x_2098_ = lean_string_dec_eq(v_val_2092_, v___x_2097_);
lean_dec(v_val_2092_);
if (v___x_2098_ == 0)
{
lean_object* v___x_2099_; 
v___x_2099_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson___closed__4));
return v___x_2099_;
}
else
{
lean_object* v___x_2100_; 
v___x_2100_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson___closed__5));
return v___x_2100_;
}
}
else
{
lean_object* v___x_2101_; 
lean_dec(v_val_2092_);
v___x_2101_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson___closed__6));
return v___x_2101_;
}
}
else
{
lean_object* v___x_2102_; 
lean_dec(v_val_2092_);
v___x_2102_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson___closed__7));
return v___x_2102_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanImportMetaKind_toJson(uint8_t v_x_2111_){
_start:
{
switch(v_x_2111_)
{
case 0:
{
lean_object* v___x_2112_; 
v___x_2112_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanImportMetaKind_toJson___closed__0));
return v___x_2112_;
}
case 1:
{
lean_object* v___x_2113_; 
v___x_2113_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanImportMetaKind_toJson___closed__1));
return v___x_2113_;
}
default: 
{
lean_object* v___x_2114_; 
v___x_2114_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanImportMetaKind_toJson___closed__2));
return v___x_2114_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanImportMetaKind_toJson___boxed(lean_object* v_x_2115_){
_start:
{
uint8_t v_x_64__boxed_2116_; lean_object* v_res_2117_; 
v_x_64__boxed_2116_ = lean_unbox(v_x_2115_);
v_res_2117_ = l_Lean_Lsp_instToJsonLeanImportMetaKind_toJson(v_x_64__boxed_2116_);
return v_res_2117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportKind_fromJson_spec__0(lean_object* v_j_2120_, lean_object* v_k_2121_){
_start:
{
lean_object* v___x_2122_; lean_object* v___x_2123_; 
v___x_2122_ = l_Lean_Json_getObjValD(v_j_2120_, v_k_2121_);
v___x_2123_ = l_Lean_Json_getBool_x3f(v___x_2122_);
lean_dec(v___x_2122_);
return v___x_2123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportKind_fromJson_spec__0___boxed(lean_object* v_j_2124_, lean_object* v_k_2125_){
_start:
{
lean_object* v_res_2126_; 
v_res_2126_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportKind_fromJson_spec__0(v_j_2124_, v_k_2125_);
lean_dec_ref(v_k_2125_);
return v_res_2126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportKind_fromJson_spec__1(lean_object* v_j_2127_, lean_object* v_k_2128_){
_start:
{
lean_object* v___x_2129_; lean_object* v___x_2130_; 
v___x_2129_ = l_Lean_Json_getObjValD(v_j_2127_, v_k_2128_);
v___x_2130_ = l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson(v___x_2129_);
return v___x_2130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportKind_fromJson_spec__1___boxed(lean_object* v_j_2131_, lean_object* v_k_2132_){
_start:
{
lean_object* v_res_2133_; 
v_res_2133_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportKind_fromJson_spec__1(v_j_2131_, v_k_2132_);
lean_dec_ref(v_k_2132_);
return v_res_2133_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__3(void){
_start:
{
uint8_t v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; 
v___x_2140_ = 1;
v___x_2141_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__2));
v___x_2142_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2141_, v___x_2140_);
return v___x_2142_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__4(void){
_start:
{
lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; 
v___x_2143_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6));
v___x_2144_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__3);
v___x_2145_ = lean_string_append(v___x_2144_, v___x_2143_);
return v___x_2145_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__6(void){
_start:
{
uint8_t v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; 
v___x_2148_ = 1;
v___x_2149_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__5));
v___x_2150_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2149_, v___x_2148_);
return v___x_2150_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__7(void){
_start:
{
lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; 
v___x_2151_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__6);
v___x_2152_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__4);
v___x_2153_ = lean_string_append(v___x_2152_, v___x_2151_);
return v___x_2153_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__8(void){
_start:
{
lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; 
v___x_2154_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_2155_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__7);
v___x_2156_ = lean_string_append(v___x_2155_, v___x_2154_);
return v___x_2156_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__11(void){
_start:
{
uint8_t v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; 
v___x_2160_ = 1;
v___x_2161_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__10));
v___x_2162_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2161_, v___x_2160_);
return v___x_2162_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__12(void){
_start:
{
lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; 
v___x_2163_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__11, &l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__11);
v___x_2164_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__4);
v___x_2165_ = lean_string_append(v___x_2164_, v___x_2163_);
return v___x_2165_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__13(void){
_start:
{
lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; 
v___x_2166_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_2167_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__12, &l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__12);
v___x_2168_ = lean_string_append(v___x_2167_, v___x_2166_);
return v___x_2168_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__16(void){
_start:
{
uint8_t v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; 
v___x_2172_ = 1;
v___x_2173_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__15));
v___x_2174_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2173_, v___x_2172_);
return v___x_2174_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__17(void){
_start:
{
lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; 
v___x_2175_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__16, &l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__16_once, _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__16);
v___x_2176_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__4);
v___x_2177_ = lean_string_append(v___x_2176_, v___x_2175_);
return v___x_2177_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__18(void){
_start:
{
lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; 
v___x_2178_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_2179_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__17, &l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__17_once, _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__17);
v___x_2180_ = lean_string_append(v___x_2179_, v___x_2178_);
return v___x_2180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanImportKind_fromJson(lean_object* v_json_2181_){
_start:
{
lean_object* v___x_2182_; lean_object* v___x_2183_; 
v___x_2182_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__0));
lean_inc(v_json_2181_);
v___x_2183_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportKind_fromJson_spec__0(v_json_2181_, v___x_2182_);
if (lean_obj_tag(v___x_2183_) == 0)
{
lean_object* v_a_2184_; lean_object* v___x_2186_; uint8_t v_isShared_2187_; uint8_t v_isSharedCheck_2193_; 
lean_dec(v_json_2181_);
v_a_2184_ = lean_ctor_get(v___x_2183_, 0);
v_isSharedCheck_2193_ = !lean_is_exclusive(v___x_2183_);
if (v_isSharedCheck_2193_ == 0)
{
v___x_2186_ = v___x_2183_;
v_isShared_2187_ = v_isSharedCheck_2193_;
goto v_resetjp_2185_;
}
else
{
lean_inc(v_a_2184_);
lean_dec(v___x_2183_);
v___x_2186_ = lean_box(0);
v_isShared_2187_ = v_isSharedCheck_2193_;
goto v_resetjp_2185_;
}
v_resetjp_2185_:
{
lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2191_; 
v___x_2188_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__8);
v___x_2189_ = lean_string_append(v___x_2188_, v_a_2184_);
lean_dec(v_a_2184_);
if (v_isShared_2187_ == 0)
{
lean_ctor_set(v___x_2186_, 0, v___x_2189_);
v___x_2191_ = v___x_2186_;
goto v_reusejp_2190_;
}
else
{
lean_object* v_reuseFailAlloc_2192_; 
v_reuseFailAlloc_2192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2192_, 0, v___x_2189_);
v___x_2191_ = v_reuseFailAlloc_2192_;
goto v_reusejp_2190_;
}
v_reusejp_2190_:
{
return v___x_2191_;
}
}
}
else
{
if (lean_obj_tag(v___x_2183_) == 0)
{
lean_object* v_a_2194_; lean_object* v___x_2196_; uint8_t v_isShared_2197_; uint8_t v_isSharedCheck_2201_; 
lean_dec(v_json_2181_);
v_a_2194_ = lean_ctor_get(v___x_2183_, 0);
v_isSharedCheck_2201_ = !lean_is_exclusive(v___x_2183_);
if (v_isSharedCheck_2201_ == 0)
{
v___x_2196_ = v___x_2183_;
v_isShared_2197_ = v_isSharedCheck_2201_;
goto v_resetjp_2195_;
}
else
{
lean_inc(v_a_2194_);
lean_dec(v___x_2183_);
v___x_2196_ = lean_box(0);
v_isShared_2197_ = v_isSharedCheck_2201_;
goto v_resetjp_2195_;
}
v_resetjp_2195_:
{
lean_object* v___x_2199_; 
if (v_isShared_2197_ == 0)
{
lean_ctor_set_tag(v___x_2196_, 0);
v___x_2199_ = v___x_2196_;
goto v_reusejp_2198_;
}
else
{
lean_object* v_reuseFailAlloc_2200_; 
v_reuseFailAlloc_2200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2200_, 0, v_a_2194_);
v___x_2199_ = v_reuseFailAlloc_2200_;
goto v_reusejp_2198_;
}
v_reusejp_2198_:
{
return v___x_2199_;
}
}
}
else
{
lean_object* v_a_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; 
v_a_2202_ = lean_ctor_get(v___x_2183_, 0);
lean_inc(v_a_2202_);
lean_dec_ref_known(v___x_2183_, 1);
v___x_2203_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__9));
lean_inc(v_json_2181_);
v___x_2204_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportKind_fromJson_spec__0(v_json_2181_, v___x_2203_);
if (lean_obj_tag(v___x_2204_) == 0)
{
lean_object* v_a_2205_; lean_object* v___x_2207_; uint8_t v_isShared_2208_; uint8_t v_isSharedCheck_2214_; 
lean_dec(v_a_2202_);
lean_dec(v_json_2181_);
v_a_2205_ = lean_ctor_get(v___x_2204_, 0);
v_isSharedCheck_2214_ = !lean_is_exclusive(v___x_2204_);
if (v_isSharedCheck_2214_ == 0)
{
v___x_2207_ = v___x_2204_;
v_isShared_2208_ = v_isSharedCheck_2214_;
goto v_resetjp_2206_;
}
else
{
lean_inc(v_a_2205_);
lean_dec(v___x_2204_);
v___x_2207_ = lean_box(0);
v_isShared_2208_ = v_isSharedCheck_2214_;
goto v_resetjp_2206_;
}
v_resetjp_2206_:
{
lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2212_; 
v___x_2209_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__13, &l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__13);
v___x_2210_ = lean_string_append(v___x_2209_, v_a_2205_);
lean_dec(v_a_2205_);
if (v_isShared_2208_ == 0)
{
lean_ctor_set(v___x_2207_, 0, v___x_2210_);
v___x_2212_ = v___x_2207_;
goto v_reusejp_2211_;
}
else
{
lean_object* v_reuseFailAlloc_2213_; 
v_reuseFailAlloc_2213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2213_, 0, v___x_2210_);
v___x_2212_ = v_reuseFailAlloc_2213_;
goto v_reusejp_2211_;
}
v_reusejp_2211_:
{
return v___x_2212_;
}
}
}
else
{
if (lean_obj_tag(v___x_2204_) == 0)
{
lean_object* v_a_2215_; lean_object* v___x_2217_; uint8_t v_isShared_2218_; uint8_t v_isSharedCheck_2222_; 
lean_dec(v_a_2202_);
lean_dec(v_json_2181_);
v_a_2215_ = lean_ctor_get(v___x_2204_, 0);
v_isSharedCheck_2222_ = !lean_is_exclusive(v___x_2204_);
if (v_isSharedCheck_2222_ == 0)
{
v___x_2217_ = v___x_2204_;
v_isShared_2218_ = v_isSharedCheck_2222_;
goto v_resetjp_2216_;
}
else
{
lean_inc(v_a_2215_);
lean_dec(v___x_2204_);
v___x_2217_ = lean_box(0);
v_isShared_2218_ = v_isSharedCheck_2222_;
goto v_resetjp_2216_;
}
v_resetjp_2216_:
{
lean_object* v___x_2220_; 
if (v_isShared_2218_ == 0)
{
lean_ctor_set_tag(v___x_2217_, 0);
v___x_2220_ = v___x_2217_;
goto v_reusejp_2219_;
}
else
{
lean_object* v_reuseFailAlloc_2221_; 
v_reuseFailAlloc_2221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2221_, 0, v_a_2215_);
v___x_2220_ = v_reuseFailAlloc_2221_;
goto v_reusejp_2219_;
}
v_reusejp_2219_:
{
return v___x_2220_;
}
}
}
else
{
lean_object* v_a_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; 
v_a_2223_ = lean_ctor_get(v___x_2204_, 0);
lean_inc(v_a_2223_);
lean_dec_ref_known(v___x_2204_, 1);
v___x_2224_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__14));
v___x_2225_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportKind_fromJson_spec__1(v_json_2181_, v___x_2224_);
if (lean_obj_tag(v___x_2225_) == 0)
{
lean_object* v_a_2226_; lean_object* v___x_2228_; uint8_t v_isShared_2229_; uint8_t v_isSharedCheck_2235_; 
lean_dec(v_a_2223_);
lean_dec(v_a_2202_);
v_a_2226_ = lean_ctor_get(v___x_2225_, 0);
v_isSharedCheck_2235_ = !lean_is_exclusive(v___x_2225_);
if (v_isSharedCheck_2235_ == 0)
{
v___x_2228_ = v___x_2225_;
v_isShared_2229_ = v_isSharedCheck_2235_;
goto v_resetjp_2227_;
}
else
{
lean_inc(v_a_2226_);
lean_dec(v___x_2225_);
v___x_2228_ = lean_box(0);
v_isShared_2229_ = v_isSharedCheck_2235_;
goto v_resetjp_2227_;
}
v_resetjp_2227_:
{
lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2233_; 
v___x_2230_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__18, &l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__18_once, _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__18);
v___x_2231_ = lean_string_append(v___x_2230_, v_a_2226_);
lean_dec(v_a_2226_);
if (v_isShared_2229_ == 0)
{
lean_ctor_set(v___x_2228_, 0, v___x_2231_);
v___x_2233_ = v___x_2228_;
goto v_reusejp_2232_;
}
else
{
lean_object* v_reuseFailAlloc_2234_; 
v_reuseFailAlloc_2234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2234_, 0, v___x_2231_);
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
if (lean_obj_tag(v___x_2225_) == 0)
{
lean_object* v_a_2236_; lean_object* v___x_2238_; uint8_t v_isShared_2239_; uint8_t v_isSharedCheck_2243_; 
lean_dec(v_a_2223_);
lean_dec(v_a_2202_);
v_a_2236_ = lean_ctor_get(v___x_2225_, 0);
v_isSharedCheck_2243_ = !lean_is_exclusive(v___x_2225_);
if (v_isSharedCheck_2243_ == 0)
{
v___x_2238_ = v___x_2225_;
v_isShared_2239_ = v_isSharedCheck_2243_;
goto v_resetjp_2237_;
}
else
{
lean_inc(v_a_2236_);
lean_dec(v___x_2225_);
v___x_2238_ = lean_box(0);
v_isShared_2239_ = v_isSharedCheck_2243_;
goto v_resetjp_2237_;
}
v_resetjp_2237_:
{
lean_object* v___x_2241_; 
if (v_isShared_2239_ == 0)
{
lean_ctor_set_tag(v___x_2238_, 0);
v___x_2241_ = v___x_2238_;
goto v_reusejp_2240_;
}
else
{
lean_object* v_reuseFailAlloc_2242_; 
v_reuseFailAlloc_2242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2242_, 0, v_a_2236_);
v___x_2241_ = v_reuseFailAlloc_2242_;
goto v_reusejp_2240_;
}
v_reusejp_2240_:
{
return v___x_2241_;
}
}
}
else
{
lean_object* v_a_2244_; lean_object* v___x_2246_; uint8_t v_isShared_2247_; uint8_t v_isSharedCheck_2255_; 
v_a_2244_ = lean_ctor_get(v___x_2225_, 0);
v_isSharedCheck_2255_ = !lean_is_exclusive(v___x_2225_);
if (v_isSharedCheck_2255_ == 0)
{
v___x_2246_ = v___x_2225_;
v_isShared_2247_ = v_isSharedCheck_2255_;
goto v_resetjp_2245_;
}
else
{
lean_inc(v_a_2244_);
lean_dec(v___x_2225_);
v___x_2246_ = lean_box(0);
v_isShared_2247_ = v_isSharedCheck_2255_;
goto v_resetjp_2245_;
}
v_resetjp_2245_:
{
lean_object* v___x_2248_; uint8_t v___x_2249_; uint8_t v___x_2250_; uint8_t v___x_2251_; lean_object* v___x_2253_; 
v___x_2248_ = lean_alloc_ctor(0, 0, 3);
v___x_2249_ = lean_unbox(v_a_2202_);
lean_dec(v_a_2202_);
lean_ctor_set_uint8(v___x_2248_, 0, v___x_2249_);
v___x_2250_ = lean_unbox(v_a_2223_);
lean_dec(v_a_2223_);
lean_ctor_set_uint8(v___x_2248_, 1, v___x_2250_);
v___x_2251_ = lean_unbox(v_a_2244_);
lean_dec(v_a_2244_);
lean_ctor_set_uint8(v___x_2248_, 2, v___x_2251_);
if (v_isShared_2247_ == 0)
{
lean_ctor_set(v___x_2246_, 0, v___x_2248_);
v___x_2253_ = v___x_2246_;
goto v_reusejp_2252_;
}
else
{
lean_object* v_reuseFailAlloc_2254_; 
v_reuseFailAlloc_2254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2254_, 0, v___x_2248_);
v___x_2253_ = v_reuseFailAlloc_2254_;
goto v_reusejp_2252_;
}
v_reusejp_2252_:
{
return v___x_2253_;
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
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanImportKind_toJson(lean_object* v_x_2258_){
_start:
{
uint8_t v_isPrivate_2259_; uint8_t v_isAll_2260_; uint8_t v_metaKind_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; 
v_isPrivate_2259_ = lean_ctor_get_uint8(v_x_2258_, 0);
v_isAll_2260_ = lean_ctor_get_uint8(v_x_2258_, 1);
v_metaKind_2261_ = lean_ctor_get_uint8(v_x_2258_, 2);
v___x_2262_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__0));
v___x_2263_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2263_, 0, v_isPrivate_2259_);
v___x_2264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2264_, 0, v___x_2262_);
lean_ctor_set(v___x_2264_, 1, v___x_2263_);
v___x_2265_ = lean_box(0);
v___x_2266_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2266_, 0, v___x_2264_);
lean_ctor_set(v___x_2266_, 1, v___x_2265_);
v___x_2267_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__9));
v___x_2268_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2268_, 0, v_isAll_2260_);
v___x_2269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2269_, 0, v___x_2267_);
lean_ctor_set(v___x_2269_, 1, v___x_2268_);
v___x_2270_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2270_, 0, v___x_2269_);
lean_ctor_set(v___x_2270_, 1, v___x_2265_);
v___x_2271_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__14));
v___x_2272_ = l_Lean_Lsp_instToJsonLeanImportMetaKind_toJson(v_metaKind_2261_);
v___x_2273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2273_, 0, v___x_2271_);
lean_ctor_set(v___x_2273_, 1, v___x_2272_);
v___x_2274_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2274_, 0, v___x_2273_);
lean_ctor_set(v___x_2274_, 1, v___x_2265_);
v___x_2275_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2275_, 0, v___x_2274_);
lean_ctor_set(v___x_2275_, 1, v___x_2265_);
v___x_2276_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2276_, 0, v___x_2270_);
lean_ctor_set(v___x_2276_, 1, v___x_2275_);
v___x_2277_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2277_, 0, v___x_2266_);
lean_ctor_set(v___x_2277_, 1, v___x_2276_);
v___x_2278_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0));
v___x_2279_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_2277_, v___x_2278_);
v___x_2280_ = l_Lean_Json_mkObj(v___x_2279_);
lean_dec(v___x_2279_);
return v___x_2280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanImportKind_toJson___boxed(lean_object* v_x_2281_){
_start:
{
lean_object* v_res_2282_; 
v_res_2282_ = l_Lean_Lsp_instToJsonLeanImportKind_toJson(v_x_2281_);
lean_dec_ref(v_x_2281_);
return v_res_2282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImport_fromJson_spec__0(lean_object* v_j_2285_, lean_object* v_k_2286_){
_start:
{
lean_object* v___x_2287_; lean_object* v___x_2288_; 
v___x_2287_ = l_Lean_Json_getObjValD(v_j_2285_, v_k_2286_);
v___x_2288_ = l_Lean_Lsp_instFromJsonLeanModule_fromJson(v___x_2287_);
return v___x_2288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImport_fromJson_spec__0___boxed(lean_object* v_j_2289_, lean_object* v_k_2290_){
_start:
{
lean_object* v_res_2291_; 
v_res_2291_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImport_fromJson_spec__0(v_j_2289_, v_k_2290_);
lean_dec_ref(v_k_2290_);
return v_res_2291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImport_fromJson_spec__1(lean_object* v_j_2292_, lean_object* v_k_2293_){
_start:
{
lean_object* v___x_2294_; lean_object* v___x_2295_; 
v___x_2294_ = l_Lean_Json_getObjValD(v_j_2292_, v_k_2293_);
v___x_2295_ = l_Lean_Lsp_instFromJsonLeanImportKind_fromJson(v___x_2294_);
return v___x_2295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImport_fromJson_spec__1___boxed(lean_object* v_j_2296_, lean_object* v_k_2297_){
_start:
{
lean_object* v_res_2298_; 
v_res_2298_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImport_fromJson_spec__1(v_j_2296_, v_k_2297_);
lean_dec_ref(v_k_2297_);
return v_res_2298_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__3(void){
_start:
{
uint8_t v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; 
v___x_2305_ = 1;
v___x_2306_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__2));
v___x_2307_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2306_, v___x_2305_);
return v___x_2307_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__4(void){
_start:
{
lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; 
v___x_2308_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6));
v___x_2309_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__3);
v___x_2310_ = lean_string_append(v___x_2309_, v___x_2308_);
return v___x_2310_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__6(void){
_start:
{
uint8_t v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; 
v___x_2313_ = 1;
v___x_2314_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__5));
v___x_2315_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2314_, v___x_2313_);
return v___x_2315_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__7(void){
_start:
{
lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; 
v___x_2316_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__6);
v___x_2317_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__4);
v___x_2318_ = lean_string_append(v___x_2317_, v___x_2316_);
return v___x_2318_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__8(void){
_start:
{
lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; 
v___x_2319_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_2320_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__7);
v___x_2321_ = lean_string_append(v___x_2320_, v___x_2319_);
return v___x_2321_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__9(void){
_start:
{
lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; 
v___x_2322_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__11, &l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__11);
v___x_2323_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__4);
v___x_2324_ = lean_string_append(v___x_2323_, v___x_2322_);
return v___x_2324_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__10(void){
_start:
{
lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; 
v___x_2325_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_2326_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__9, &l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__9);
v___x_2327_ = lean_string_append(v___x_2326_, v___x_2325_);
return v___x_2327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanImport_fromJson(lean_object* v_json_2328_){
_start:
{
lean_object* v___x_2329_; lean_object* v___x_2330_; 
v___x_2329_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__0));
lean_inc(v_json_2328_);
v___x_2330_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImport_fromJson_spec__0(v_json_2328_, v___x_2329_);
if (lean_obj_tag(v___x_2330_) == 0)
{
lean_object* v_a_2331_; lean_object* v___x_2333_; uint8_t v_isShared_2334_; uint8_t v_isSharedCheck_2340_; 
lean_dec(v_json_2328_);
v_a_2331_ = lean_ctor_get(v___x_2330_, 0);
v_isSharedCheck_2340_ = !lean_is_exclusive(v___x_2330_);
if (v_isSharedCheck_2340_ == 0)
{
v___x_2333_ = v___x_2330_;
v_isShared_2334_ = v_isSharedCheck_2340_;
goto v_resetjp_2332_;
}
else
{
lean_inc(v_a_2331_);
lean_dec(v___x_2330_);
v___x_2333_ = lean_box(0);
v_isShared_2334_ = v_isSharedCheck_2340_;
goto v_resetjp_2332_;
}
v_resetjp_2332_:
{
lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2338_; 
v___x_2335_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__8);
v___x_2336_ = lean_string_append(v___x_2335_, v_a_2331_);
lean_dec(v_a_2331_);
if (v_isShared_2334_ == 0)
{
lean_ctor_set(v___x_2333_, 0, v___x_2336_);
v___x_2338_ = v___x_2333_;
goto v_reusejp_2337_;
}
else
{
lean_object* v_reuseFailAlloc_2339_; 
v_reuseFailAlloc_2339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2339_, 0, v___x_2336_);
v___x_2338_ = v_reuseFailAlloc_2339_;
goto v_reusejp_2337_;
}
v_reusejp_2337_:
{
return v___x_2338_;
}
}
}
else
{
if (lean_obj_tag(v___x_2330_) == 0)
{
lean_object* v_a_2341_; lean_object* v___x_2343_; uint8_t v_isShared_2344_; uint8_t v_isSharedCheck_2348_; 
lean_dec(v_json_2328_);
v_a_2341_ = lean_ctor_get(v___x_2330_, 0);
v_isSharedCheck_2348_ = !lean_is_exclusive(v___x_2330_);
if (v_isSharedCheck_2348_ == 0)
{
v___x_2343_ = v___x_2330_;
v_isShared_2344_ = v_isSharedCheck_2348_;
goto v_resetjp_2342_;
}
else
{
lean_inc(v_a_2341_);
lean_dec(v___x_2330_);
v___x_2343_ = lean_box(0);
v_isShared_2344_ = v_isSharedCheck_2348_;
goto v_resetjp_2342_;
}
v_resetjp_2342_:
{
lean_object* v___x_2346_; 
if (v_isShared_2344_ == 0)
{
lean_ctor_set_tag(v___x_2343_, 0);
v___x_2346_ = v___x_2343_;
goto v_reusejp_2345_;
}
else
{
lean_object* v_reuseFailAlloc_2347_; 
v_reuseFailAlloc_2347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2347_, 0, v_a_2341_);
v___x_2346_ = v_reuseFailAlloc_2347_;
goto v_reusejp_2345_;
}
v_reusejp_2345_:
{
return v___x_2346_;
}
}
}
else
{
lean_object* v_a_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; 
v_a_2349_ = lean_ctor_get(v___x_2330_, 0);
lean_inc(v_a_2349_);
lean_dec_ref_known(v___x_2330_, 1);
v___x_2350_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__9));
v___x_2351_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImport_fromJson_spec__1(v_json_2328_, v___x_2350_);
if (lean_obj_tag(v___x_2351_) == 0)
{
lean_object* v_a_2352_; lean_object* v___x_2354_; uint8_t v_isShared_2355_; uint8_t v_isSharedCheck_2361_; 
lean_dec(v_a_2349_);
v_a_2352_ = lean_ctor_get(v___x_2351_, 0);
v_isSharedCheck_2361_ = !lean_is_exclusive(v___x_2351_);
if (v_isSharedCheck_2361_ == 0)
{
v___x_2354_ = v___x_2351_;
v_isShared_2355_ = v_isSharedCheck_2361_;
goto v_resetjp_2353_;
}
else
{
lean_inc(v_a_2352_);
lean_dec(v___x_2351_);
v___x_2354_ = lean_box(0);
v_isShared_2355_ = v_isSharedCheck_2361_;
goto v_resetjp_2353_;
}
v_resetjp_2353_:
{
lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2359_; 
v___x_2356_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__10, &l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__10);
v___x_2357_ = lean_string_append(v___x_2356_, v_a_2352_);
lean_dec(v_a_2352_);
if (v_isShared_2355_ == 0)
{
lean_ctor_set(v___x_2354_, 0, v___x_2357_);
v___x_2359_ = v___x_2354_;
goto v_reusejp_2358_;
}
else
{
lean_object* v_reuseFailAlloc_2360_; 
v_reuseFailAlloc_2360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2360_, 0, v___x_2357_);
v___x_2359_ = v_reuseFailAlloc_2360_;
goto v_reusejp_2358_;
}
v_reusejp_2358_:
{
return v___x_2359_;
}
}
}
else
{
if (lean_obj_tag(v___x_2351_) == 0)
{
lean_object* v_a_2362_; lean_object* v___x_2364_; uint8_t v_isShared_2365_; uint8_t v_isSharedCheck_2369_; 
lean_dec(v_a_2349_);
v_a_2362_ = lean_ctor_get(v___x_2351_, 0);
v_isSharedCheck_2369_ = !lean_is_exclusive(v___x_2351_);
if (v_isSharedCheck_2369_ == 0)
{
v___x_2364_ = v___x_2351_;
v_isShared_2365_ = v_isSharedCheck_2369_;
goto v_resetjp_2363_;
}
else
{
lean_inc(v_a_2362_);
lean_dec(v___x_2351_);
v___x_2364_ = lean_box(0);
v_isShared_2365_ = v_isSharedCheck_2369_;
goto v_resetjp_2363_;
}
v_resetjp_2363_:
{
lean_object* v___x_2367_; 
if (v_isShared_2365_ == 0)
{
lean_ctor_set_tag(v___x_2364_, 0);
v___x_2367_ = v___x_2364_;
goto v_reusejp_2366_;
}
else
{
lean_object* v_reuseFailAlloc_2368_; 
v_reuseFailAlloc_2368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2368_, 0, v_a_2362_);
v___x_2367_ = v_reuseFailAlloc_2368_;
goto v_reusejp_2366_;
}
v_reusejp_2366_:
{
return v___x_2367_;
}
}
}
else
{
lean_object* v_a_2370_; lean_object* v___x_2372_; uint8_t v_isShared_2373_; uint8_t v_isSharedCheck_2378_; 
v_a_2370_ = lean_ctor_get(v___x_2351_, 0);
v_isSharedCheck_2378_ = !lean_is_exclusive(v___x_2351_);
if (v_isSharedCheck_2378_ == 0)
{
v___x_2372_ = v___x_2351_;
v_isShared_2373_ = v_isSharedCheck_2378_;
goto v_resetjp_2371_;
}
else
{
lean_inc(v_a_2370_);
lean_dec(v___x_2351_);
v___x_2372_ = lean_box(0);
v_isShared_2373_ = v_isSharedCheck_2378_;
goto v_resetjp_2371_;
}
v_resetjp_2371_:
{
lean_object* v___x_2374_; lean_object* v___x_2376_; 
v___x_2374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2374_, 0, v_a_2349_);
lean_ctor_set(v___x_2374_, 1, v_a_2370_);
if (v_isShared_2373_ == 0)
{
lean_ctor_set(v___x_2372_, 0, v___x_2374_);
v___x_2376_ = v___x_2372_;
goto v_reusejp_2375_;
}
else
{
lean_object* v_reuseFailAlloc_2377_; 
v_reuseFailAlloc_2377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2377_, 0, v___x_2374_);
v___x_2376_ = v_reuseFailAlloc_2377_;
goto v_reusejp_2375_;
}
v_reusejp_2375_:
{
return v___x_2376_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanImport_toJson(lean_object* v_x_2381_){
_start:
{
lean_object* v_module_2382_; lean_object* v_kind_2383_; lean_object* v___x_2385_; uint8_t v_isShared_2386_; uint8_t v_isSharedCheck_2403_; 
v_module_2382_ = lean_ctor_get(v_x_2381_, 0);
v_kind_2383_ = lean_ctor_get(v_x_2381_, 1);
v_isSharedCheck_2403_ = !lean_is_exclusive(v_x_2381_);
if (v_isSharedCheck_2403_ == 0)
{
v___x_2385_ = v_x_2381_;
v_isShared_2386_ = v_isSharedCheck_2403_;
goto v_resetjp_2384_;
}
else
{
lean_inc(v_kind_2383_);
lean_inc(v_module_2382_);
lean_dec(v_x_2381_);
v___x_2385_ = lean_box(0);
v_isShared_2386_ = v_isSharedCheck_2403_;
goto v_resetjp_2384_;
}
v_resetjp_2384_:
{
lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2390_; 
v___x_2387_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__0));
v___x_2388_ = l_Lean_Lsp_instToJsonLeanModule_toJson(v_module_2382_);
lean_dec_ref(v_module_2382_);
if (v_isShared_2386_ == 0)
{
lean_ctor_set(v___x_2385_, 1, v___x_2388_);
lean_ctor_set(v___x_2385_, 0, v___x_2387_);
v___x_2390_ = v___x_2385_;
goto v_reusejp_2389_;
}
else
{
lean_object* v_reuseFailAlloc_2402_; 
v_reuseFailAlloc_2402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2402_, 0, v___x_2387_);
lean_ctor_set(v_reuseFailAlloc_2402_, 1, v___x_2388_);
v___x_2390_ = v_reuseFailAlloc_2402_;
goto v_reusejp_2389_;
}
v_reusejp_2389_:
{
lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; 
v___x_2391_ = lean_box(0);
v___x_2392_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2392_, 0, v___x_2390_);
lean_ctor_set(v___x_2392_, 1, v___x_2391_);
v___x_2393_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__9));
v___x_2394_ = l_Lean_Lsp_instToJsonLeanImportKind_toJson(v_kind_2383_);
lean_dec_ref(v_kind_2383_);
v___x_2395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2395_, 0, v___x_2393_);
lean_ctor_set(v___x_2395_, 1, v___x_2394_);
v___x_2396_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2396_, 0, v___x_2395_);
lean_ctor_set(v___x_2396_, 1, v___x_2391_);
v___x_2397_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2397_, 0, v___x_2396_);
lean_ctor_set(v___x_2397_, 1, v___x_2391_);
v___x_2398_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2398_, 0, v___x_2392_);
lean_ctor_set(v___x_2398_, 1, v___x_2397_);
v___x_2399_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0));
v___x_2400_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_2398_, v___x_2399_);
v___x_2401_ = l_Lean_Json_mkObj(v___x_2400_);
lean_dec(v___x_2400_);
return v___x_2401_;
}
}
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__2(void){
_start:
{
uint8_t v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; 
v___x_2411_ = 1;
v___x_2412_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__1));
v___x_2413_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2412_, v___x_2411_);
return v___x_2413_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__3(void){
_start:
{
lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; 
v___x_2414_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6));
v___x_2415_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__2, &l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__2);
v___x_2416_ = lean_string_append(v___x_2415_, v___x_2414_);
return v___x_2416_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; 
v___x_2417_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__6);
v___x_2418_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__3);
v___x_2419_ = lean_string_append(v___x_2418_, v___x_2417_);
return v___x_2419_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__5(void){
_start:
{
lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; 
v___x_2420_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_2421_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__4);
v___x_2422_ = lean_string_append(v___x_2421_, v___x_2420_);
return v___x_2422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson(lean_object* v_json_2423_){
_start:
{
lean_object* v___x_2424_; lean_object* v___x_2425_; 
v___x_2424_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__0));
v___x_2425_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImport_fromJson_spec__0(v_json_2423_, v___x_2424_);
if (lean_obj_tag(v___x_2425_) == 0)
{
lean_object* v_a_2426_; lean_object* v___x_2428_; uint8_t v_isShared_2429_; uint8_t v_isSharedCheck_2435_; 
v_a_2426_ = lean_ctor_get(v___x_2425_, 0);
v_isSharedCheck_2435_ = !lean_is_exclusive(v___x_2425_);
if (v_isSharedCheck_2435_ == 0)
{
v___x_2428_ = v___x_2425_;
v_isShared_2429_ = v_isSharedCheck_2435_;
goto v_resetjp_2427_;
}
else
{
lean_inc(v_a_2426_);
lean_dec(v___x_2425_);
v___x_2428_ = lean_box(0);
v_isShared_2429_ = v_isSharedCheck_2435_;
goto v_resetjp_2427_;
}
v_resetjp_2427_:
{
lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2433_; 
v___x_2430_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__5, &l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__5);
v___x_2431_ = lean_string_append(v___x_2430_, v_a_2426_);
lean_dec(v_a_2426_);
if (v_isShared_2429_ == 0)
{
lean_ctor_set(v___x_2428_, 0, v___x_2431_);
v___x_2433_ = v___x_2428_;
goto v_reusejp_2432_;
}
else
{
lean_object* v_reuseFailAlloc_2434_; 
v_reuseFailAlloc_2434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2434_, 0, v___x_2431_);
v___x_2433_ = v_reuseFailAlloc_2434_;
goto v_reusejp_2432_;
}
v_reusejp_2432_:
{
return v___x_2433_;
}
}
}
else
{
if (lean_obj_tag(v___x_2425_) == 0)
{
lean_object* v_a_2436_; lean_object* v___x_2438_; uint8_t v_isShared_2439_; uint8_t v_isSharedCheck_2443_; 
v_a_2436_ = lean_ctor_get(v___x_2425_, 0);
v_isSharedCheck_2443_ = !lean_is_exclusive(v___x_2425_);
if (v_isSharedCheck_2443_ == 0)
{
v___x_2438_ = v___x_2425_;
v_isShared_2439_ = v_isSharedCheck_2443_;
goto v_resetjp_2437_;
}
else
{
lean_inc(v_a_2436_);
lean_dec(v___x_2425_);
v___x_2438_ = lean_box(0);
v_isShared_2439_ = v_isSharedCheck_2443_;
goto v_resetjp_2437_;
}
v_resetjp_2437_:
{
lean_object* v___x_2441_; 
if (v_isShared_2439_ == 0)
{
lean_ctor_set_tag(v___x_2438_, 0);
v___x_2441_ = v___x_2438_;
goto v_reusejp_2440_;
}
else
{
lean_object* v_reuseFailAlloc_2442_; 
v_reuseFailAlloc_2442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2442_, 0, v_a_2436_);
v___x_2441_ = v_reuseFailAlloc_2442_;
goto v_reusejp_2440_;
}
v_reusejp_2440_:
{
return v___x_2441_;
}
}
}
else
{
lean_object* v_a_2444_; lean_object* v___x_2446_; uint8_t v_isShared_2447_; uint8_t v_isSharedCheck_2451_; 
v_a_2444_ = lean_ctor_get(v___x_2425_, 0);
v_isSharedCheck_2451_ = !lean_is_exclusive(v___x_2425_);
if (v_isSharedCheck_2451_ == 0)
{
v___x_2446_ = v___x_2425_;
v_isShared_2447_ = v_isSharedCheck_2451_;
goto v_resetjp_2445_;
}
else
{
lean_inc(v_a_2444_);
lean_dec(v___x_2425_);
v___x_2446_ = lean_box(0);
v_isShared_2447_ = v_isSharedCheck_2451_;
goto v_resetjp_2445_;
}
v_resetjp_2445_:
{
lean_object* v___x_2449_; 
if (v_isShared_2447_ == 0)
{
v___x_2449_ = v___x_2446_;
goto v_reusejp_2448_;
}
else
{
lean_object* v_reuseFailAlloc_2450_; 
v_reuseFailAlloc_2450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2450_, 0, v_a_2444_);
v___x_2449_ = v_reuseFailAlloc_2450_;
goto v_reusejp_2448_;
}
v_reusejp_2448_:
{
return v___x_2449_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanModuleHierarchyImportsParams_toJson(lean_object* v_x_2454_){
_start:
{
lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; 
v___x_2455_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__0));
v___x_2456_ = l_Lean_Lsp_instToJsonLeanModule_toJson(v_x_2454_);
v___x_2457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2457_, 0, v___x_2455_);
lean_ctor_set(v___x_2457_, 1, v___x_2456_);
v___x_2458_ = lean_box(0);
v___x_2459_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2459_, 0, v___x_2457_);
lean_ctor_set(v___x_2459_, 1, v___x_2458_);
v___x_2460_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2460_, 0, v___x_2459_);
lean_ctor_set(v___x_2460_, 1, v___x_2458_);
v___x_2461_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0));
v___x_2462_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_2460_, v___x_2461_);
v___x_2463_ = l_Lean_Json_mkObj(v___x_2462_);
lean_dec(v___x_2462_);
return v___x_2463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanModuleHierarchyImportsParams_toJson___boxed(lean_object* v_x_2464_){
_start:
{
lean_object* v_res_2465_; 
v_res_2465_ = l_Lean_Lsp_instToJsonLeanModuleHierarchyImportsParams_toJson(v_x_2464_);
lean_dec_ref(v_x_2464_);
return v_res_2465_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__2(void){
_start:
{
uint8_t v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; 
v___x_2473_ = 1;
v___x_2474_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__1));
v___x_2475_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2474_, v___x_2473_);
return v___x_2475_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__3(void){
_start:
{
lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; 
v___x_2476_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6));
v___x_2477_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__2, &l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__2);
v___x_2478_ = lean_string_append(v___x_2477_, v___x_2476_);
return v___x_2478_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; 
v___x_2479_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__6);
v___x_2480_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__3);
v___x_2481_ = lean_string_append(v___x_2480_, v___x_2479_);
return v___x_2481_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__5(void){
_start:
{
lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; 
v___x_2482_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_2483_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__4);
v___x_2484_ = lean_string_append(v___x_2483_, v___x_2482_);
return v___x_2484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson(lean_object* v_json_2485_){
_start:
{
lean_object* v___x_2486_; lean_object* v___x_2487_; 
v___x_2486_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__0));
v___x_2487_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImport_fromJson_spec__0(v_json_2485_, v___x_2486_);
if (lean_obj_tag(v___x_2487_) == 0)
{
lean_object* v_a_2488_; lean_object* v___x_2490_; uint8_t v_isShared_2491_; uint8_t v_isSharedCheck_2497_; 
v_a_2488_ = lean_ctor_get(v___x_2487_, 0);
v_isSharedCheck_2497_ = !lean_is_exclusive(v___x_2487_);
if (v_isSharedCheck_2497_ == 0)
{
v___x_2490_ = v___x_2487_;
v_isShared_2491_ = v_isSharedCheck_2497_;
goto v_resetjp_2489_;
}
else
{
lean_inc(v_a_2488_);
lean_dec(v___x_2487_);
v___x_2490_ = lean_box(0);
v_isShared_2491_ = v_isSharedCheck_2497_;
goto v_resetjp_2489_;
}
v_resetjp_2489_:
{
lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2495_; 
v___x_2492_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__5, &l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__5);
v___x_2493_ = lean_string_append(v___x_2492_, v_a_2488_);
lean_dec(v_a_2488_);
if (v_isShared_2491_ == 0)
{
lean_ctor_set(v___x_2490_, 0, v___x_2493_);
v___x_2495_ = v___x_2490_;
goto v_reusejp_2494_;
}
else
{
lean_object* v_reuseFailAlloc_2496_; 
v_reuseFailAlloc_2496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2496_, 0, v___x_2493_);
v___x_2495_ = v_reuseFailAlloc_2496_;
goto v_reusejp_2494_;
}
v_reusejp_2494_:
{
return v___x_2495_;
}
}
}
else
{
if (lean_obj_tag(v___x_2487_) == 0)
{
lean_object* v_a_2498_; lean_object* v___x_2500_; uint8_t v_isShared_2501_; uint8_t v_isSharedCheck_2505_; 
v_a_2498_ = lean_ctor_get(v___x_2487_, 0);
v_isSharedCheck_2505_ = !lean_is_exclusive(v___x_2487_);
if (v_isSharedCheck_2505_ == 0)
{
v___x_2500_ = v___x_2487_;
v_isShared_2501_ = v_isSharedCheck_2505_;
goto v_resetjp_2499_;
}
else
{
lean_inc(v_a_2498_);
lean_dec(v___x_2487_);
v___x_2500_ = lean_box(0);
v_isShared_2501_ = v_isSharedCheck_2505_;
goto v_resetjp_2499_;
}
v_resetjp_2499_:
{
lean_object* v___x_2503_; 
if (v_isShared_2501_ == 0)
{
lean_ctor_set_tag(v___x_2500_, 0);
v___x_2503_ = v___x_2500_;
goto v_reusejp_2502_;
}
else
{
lean_object* v_reuseFailAlloc_2504_; 
v_reuseFailAlloc_2504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2504_, 0, v_a_2498_);
v___x_2503_ = v_reuseFailAlloc_2504_;
goto v_reusejp_2502_;
}
v_reusejp_2502_:
{
return v___x_2503_;
}
}
}
else
{
lean_object* v_a_2506_; lean_object* v___x_2508_; uint8_t v_isShared_2509_; uint8_t v_isSharedCheck_2513_; 
v_a_2506_ = lean_ctor_get(v___x_2487_, 0);
v_isSharedCheck_2513_ = !lean_is_exclusive(v___x_2487_);
if (v_isSharedCheck_2513_ == 0)
{
v___x_2508_ = v___x_2487_;
v_isShared_2509_ = v_isSharedCheck_2513_;
goto v_resetjp_2507_;
}
else
{
lean_inc(v_a_2506_);
lean_dec(v___x_2487_);
v___x_2508_ = lean_box(0);
v_isShared_2509_ = v_isSharedCheck_2513_;
goto v_resetjp_2507_;
}
v_resetjp_2507_:
{
lean_object* v___x_2511_; 
if (v_isShared_2509_ == 0)
{
v___x_2511_ = v___x_2508_;
goto v_reusejp_2510_;
}
else
{
lean_object* v_reuseFailAlloc_2512_; 
v_reuseFailAlloc_2512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2512_, 0, v_a_2506_);
v___x_2511_ = v_reuseFailAlloc_2512_;
goto v_reusejp_2510_;
}
v_reusejp_2510_:
{
return v___x_2511_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanModuleHierarchyImportedByParams_toJson(lean_object* v_x_2516_){
_start:
{
lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; 
v___x_2517_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__0));
v___x_2518_ = l_Lean_Lsp_instToJsonLeanModule_toJson(v_x_2516_);
v___x_2519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2519_, 0, v___x_2517_);
lean_ctor_set(v___x_2519_, 1, v___x_2518_);
v___x_2520_ = lean_box(0);
v___x_2521_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2521_, 0, v___x_2519_);
lean_ctor_set(v___x_2521_, 1, v___x_2520_);
v___x_2522_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2522_, 0, v___x_2521_);
lean_ctor_set(v___x_2522_, 1, v___x_2520_);
v___x_2523_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0));
v___x_2524_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_2522_, v___x_2523_);
v___x_2525_ = l_Lean_Json_mkObj(v___x_2524_);
lean_dec(v___x_2524_);
return v___x_2525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanModuleHierarchyImportedByParams_toJson___boxed(lean_object* v_x_2526_){
_start:
{
lean_object* v_res_2527_; 
v_res_2527_ = l_Lean_Lsp_instToJsonLeanModuleHierarchyImportedByParams_toJson(v_x_2526_);
lean_dec_ref(v_x_2526_);
return v_res_2527_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__2(void){
_start:
{
uint8_t v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; 
v___x_2535_ = 1;
v___x_2536_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__1));
v___x_2537_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2536_, v___x_2535_);
return v___x_2537_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__3(void){
_start:
{
lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; 
v___x_2538_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6));
v___x_2539_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__2, &l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__2);
v___x_2540_ = lean_string_append(v___x_2539_, v___x_2538_);
return v___x_2540_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; 
v___x_2541_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__6, &l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__6);
v___x_2542_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__3);
v___x_2543_ = lean_string_append(v___x_2542_, v___x_2541_);
return v___x_2543_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__5(void){
_start:
{
lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; 
v___x_2544_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_2545_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__4);
v___x_2546_ = lean_string_append(v___x_2545_, v___x_2544_);
return v___x_2546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson(lean_object* v_json_2547_){
_start:
{
lean_object* v___x_2548_; lean_object* v___x_2549_; 
v___x_2548_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__0));
v___x_2549_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson_spec__0(v_json_2547_, v___x_2548_);
if (lean_obj_tag(v___x_2549_) == 0)
{
lean_object* v_a_2550_; lean_object* v___x_2552_; uint8_t v_isShared_2553_; uint8_t v_isSharedCheck_2559_; 
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
v___x_2554_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__5, &l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__5);
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
if (lean_obj_tag(v___x_2549_) == 0)
{
lean_object* v_a_2560_; lean_object* v___x_2562_; uint8_t v_isShared_2563_; uint8_t v_isSharedCheck_2567_; 
v_a_2560_ = lean_ctor_get(v___x_2549_, 0);
v_isSharedCheck_2567_ = !lean_is_exclusive(v___x_2549_);
if (v_isSharedCheck_2567_ == 0)
{
v___x_2562_ = v___x_2549_;
v_isShared_2563_ = v_isSharedCheck_2567_;
goto v_resetjp_2561_;
}
else
{
lean_inc(v_a_2560_);
lean_dec(v___x_2549_);
v___x_2562_ = lean_box(0);
v_isShared_2563_ = v_isSharedCheck_2567_;
goto v_resetjp_2561_;
}
v_resetjp_2561_:
{
lean_object* v___x_2565_; 
if (v_isShared_2563_ == 0)
{
lean_ctor_set_tag(v___x_2562_, 0);
v___x_2565_ = v___x_2562_;
goto v_reusejp_2564_;
}
else
{
lean_object* v_reuseFailAlloc_2566_; 
v_reuseFailAlloc_2566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2566_, 0, v_a_2560_);
v___x_2565_ = v_reuseFailAlloc_2566_;
goto v_reusejp_2564_;
}
v_reusejp_2564_:
{
return v___x_2565_;
}
}
}
else
{
lean_object* v_a_2568_; lean_object* v___x_2570_; uint8_t v_isShared_2571_; uint8_t v_isSharedCheck_2575_; 
v_a_2568_ = lean_ctor_get(v___x_2549_, 0);
v_isSharedCheck_2575_ = !lean_is_exclusive(v___x_2549_);
if (v_isSharedCheck_2575_ == 0)
{
v___x_2570_ = v___x_2549_;
v_isShared_2571_ = v_isSharedCheck_2575_;
goto v_resetjp_2569_;
}
else
{
lean_inc(v_a_2568_);
lean_dec(v___x_2549_);
v___x_2570_ = lean_box(0);
v_isShared_2571_ = v_isSharedCheck_2575_;
goto v_resetjp_2569_;
}
v_resetjp_2569_:
{
lean_object* v___x_2573_; 
if (v_isShared_2571_ == 0)
{
v___x_2573_ = v___x_2570_;
goto v_reusejp_2572_;
}
else
{
lean_object* v_reuseFailAlloc_2574_; 
v_reuseFailAlloc_2574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2574_, 0, v_a_2568_);
v___x_2573_ = v_reuseFailAlloc_2574_;
goto v_reusejp_2572_;
}
v_reusejp_2572_:
{
return v___x_2573_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRpcConnectParams_toJson(lean_object* v_x_2578_){
_start:
{
lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; 
v___x_2579_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__0));
v___x_2580_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2580_, 0, v_x_2578_);
v___x_2581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2581_, 0, v___x_2579_);
lean_ctor_set(v___x_2581_, 1, v___x_2580_);
v___x_2582_ = lean_box(0);
v___x_2583_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2583_, 0, v___x_2581_);
lean_ctor_set(v___x_2583_, 1, v___x_2582_);
v___x_2584_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2584_, 0, v___x_2583_);
lean_ctor_set(v___x_2584_, 1, v___x_2582_);
v___x_2585_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0));
v___x_2586_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_2584_, v___x_2585_);
v___x_2587_ = l_Lean_Json_mkObj(v___x_2586_);
lean_dec(v___x_2586_);
return v___x_2587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcConnected_fromJson_spec__0(lean_object* v_j_2590_, lean_object* v_k_2591_){
_start:
{
lean_object* v___x_2592_; lean_object* v___x_2593_; 
v___x_2592_ = l_Lean_Json_getObjValD(v_j_2590_, v_k_2591_);
v___x_2593_ = l_Lean_UInt64_fromJson_x3f(v___x_2592_);
return v___x_2593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcConnected_fromJson_spec__0___boxed(lean_object* v_j_2594_, lean_object* v_k_2595_){
_start:
{
lean_object* v_res_2596_; 
v_res_2596_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcConnected_fromJson_spec__0(v_j_2594_, v_k_2595_);
lean_dec_ref(v_k_2595_);
return v_res_2596_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__3(void){
_start:
{
uint8_t v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; 
v___x_2603_ = 1;
v___x_2604_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__2));
v___x_2605_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2604_, v___x_2603_);
return v___x_2605_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__4(void){
_start:
{
lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; 
v___x_2606_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6));
v___x_2607_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__3, &l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__3);
v___x_2608_ = lean_string_append(v___x_2607_, v___x_2606_);
return v___x_2608_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__6(void){
_start:
{
uint8_t v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; 
v___x_2611_ = 1;
v___x_2612_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__5));
v___x_2613_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2612_, v___x_2611_);
return v___x_2613_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__7(void){
_start:
{
lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; 
v___x_2614_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__6, &l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__6);
v___x_2615_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__4, &l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__4);
v___x_2616_ = lean_string_append(v___x_2615_, v___x_2614_);
return v___x_2616_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__8(void){
_start:
{
lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; 
v___x_2617_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_2618_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__7, &l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__7);
v___x_2619_ = lean_string_append(v___x_2618_, v___x_2617_);
return v___x_2619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonRpcConnected_fromJson(lean_object* v_json_2620_){
_start:
{
lean_object* v___x_2621_; lean_object* v___x_2622_; 
v___x_2621_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__0));
v___x_2622_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcConnected_fromJson_spec__0(v_json_2620_, v___x_2621_);
if (lean_obj_tag(v___x_2622_) == 0)
{
lean_object* v_a_2623_; lean_object* v___x_2625_; uint8_t v_isShared_2626_; uint8_t v_isSharedCheck_2632_; 
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
v___x_2627_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__8, &l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__8);
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
lean_object* v_a_2641_; lean_object* v___x_2643_; uint8_t v_isShared_2644_; uint8_t v_isSharedCheck_2648_; 
v_a_2641_ = lean_ctor_get(v___x_2622_, 0);
v_isSharedCheck_2648_ = !lean_is_exclusive(v___x_2622_);
if (v_isSharedCheck_2648_ == 0)
{
v___x_2643_ = v___x_2622_;
v_isShared_2644_ = v_isSharedCheck_2648_;
goto v_resetjp_2642_;
}
else
{
lean_inc(v_a_2641_);
lean_dec(v___x_2622_);
v___x_2643_ = lean_box(0);
v_isShared_2644_ = v_isSharedCheck_2648_;
goto v_resetjp_2642_;
}
v_resetjp_2642_:
{
lean_object* v___x_2646_; 
if (v_isShared_2644_ == 0)
{
v___x_2646_ = v___x_2643_;
goto v_reusejp_2645_;
}
else
{
lean_object* v_reuseFailAlloc_2647_; 
v_reuseFailAlloc_2647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2647_, 0, v_a_2641_);
v___x_2646_ = v_reuseFailAlloc_2647_;
goto v_reusejp_2645_;
}
v_reusejp_2645_:
{
return v___x_2646_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRpcConnected_toJson(uint64_t v_x_2651_){
_start:
{
lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; 
v___x_2652_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__0));
v___x_2653_ = lean_uint64_to_nat(v_x_2651_);
v___x_2654_ = l_Lean_bignumToJson(v___x_2653_);
v___x_2655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2655_, 0, v___x_2652_);
lean_ctor_set(v___x_2655_, 1, v___x_2654_);
v___x_2656_ = lean_box(0);
v___x_2657_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2657_, 0, v___x_2655_);
lean_ctor_set(v___x_2657_, 1, v___x_2656_);
v___x_2658_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2658_, 0, v___x_2657_);
lean_ctor_set(v___x_2658_, 1, v___x_2656_);
v___x_2659_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0));
v___x_2660_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_2658_, v___x_2659_);
v___x_2661_ = l_Lean_Json_mkObj(v___x_2660_);
lean_dec(v___x_2660_);
return v___x_2661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRpcConnected_toJson___boxed(lean_object* v_x_2662_){
_start:
{
uint64_t v_x_30__boxed_2663_; lean_object* v_res_2664_; 
v_x_30__boxed_2663_ = lean_unbox_uint64(v_x_2662_);
lean_dec_ref(v_x_2662_);
v_res_2664_ = l_Lean_Lsp_instToJsonRpcConnected_toJson(v_x_30__boxed_2663_);
return v_res_2664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcCallParams_fromJson_spec__0(lean_object* v_j_2667_, lean_object* v_k_2668_){
_start:
{
lean_object* v___x_2669_; lean_object* v___x_2670_; 
v___x_2669_ = l_Lean_Json_getObjValD(v_j_2667_, v_k_2668_);
v___x_2670_ = l_Lean_Name_fromJson_x3f(v___x_2669_);
return v___x_2670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcCallParams_fromJson_spec__0___boxed(lean_object* v_j_2671_, lean_object* v_k_2672_){
_start:
{
lean_object* v_res_2673_; 
v_res_2673_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcCallParams_fromJson_spec__0(v_j_2671_, v_k_2672_);
lean_dec_ref(v_k_2672_);
return v_res_2673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcCallParams_fromJson_spec__1(lean_object* v_j_2674_, lean_object* v_k_2675_){
_start:
{
lean_object* v___x_2676_; lean_object* v___x_2677_; 
v___x_2676_ = l_Lean_Json_getObjValD(v_j_2674_, v_k_2675_);
v___x_2677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2677_, 0, v___x_2676_);
return v___x_2677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcCallParams_fromJson_spec__1___boxed(lean_object* v_j_2678_, lean_object* v_k_2679_){
_start:
{
lean_object* v_res_2680_; 
v_res_2680_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcCallParams_fromJson_spec__1(v_j_2678_, v_k_2679_);
lean_dec_ref(v_k_2679_);
return v_res_2680_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__2(void){
_start:
{
uint8_t v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; 
v___x_2686_ = 1;
v___x_2687_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__1));
v___x_2688_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2687_, v___x_2686_);
return v___x_2688_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__3(void){
_start:
{
lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; 
v___x_2689_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6));
v___x_2690_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__2, &l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__2);
v___x_2691_ = lean_string_append(v___x_2690_, v___x_2689_);
return v___x_2691_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; 
v___x_2692_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9, &l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9);
v___x_2693_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__3);
v___x_2694_ = lean_string_append(v___x_2693_, v___x_2692_);
return v___x_2694_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__5(void){
_start:
{
lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; 
v___x_2695_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_2696_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__4);
v___x_2697_ = lean_string_append(v___x_2696_, v___x_2695_);
return v___x_2697_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__6(void){
_start:
{
lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; 
v___x_2698_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__8);
v___x_2699_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__3);
v___x_2700_ = lean_string_append(v___x_2699_, v___x_2698_);
return v___x_2700_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__7(void){
_start:
{
lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; 
v___x_2701_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_2702_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__6, &l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__6);
v___x_2703_ = lean_string_append(v___x_2702_, v___x_2701_);
return v___x_2703_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__8(void){
_start:
{
lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; 
v___x_2704_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__6, &l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__6);
v___x_2705_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__3);
v___x_2706_ = lean_string_append(v___x_2705_, v___x_2704_);
return v___x_2706_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__9(void){
_start:
{
lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; 
v___x_2707_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_2708_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__8);
v___x_2709_ = lean_string_append(v___x_2708_, v___x_2707_);
return v___x_2709_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__12(void){
_start:
{
uint8_t v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; 
v___x_2713_ = 1;
v___x_2714_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__11));
v___x_2715_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2714_, v___x_2713_);
return v___x_2715_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__13(void){
_start:
{
lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; 
v___x_2716_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__12, &l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__12);
v___x_2717_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__3);
v___x_2718_ = lean_string_append(v___x_2717_, v___x_2716_);
return v___x_2718_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__14(void){
_start:
{
lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; 
v___x_2719_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_2720_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__13, &l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__13);
v___x_2721_ = lean_string_append(v___x_2720_, v___x_2719_);
return v___x_2721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonRpcCallParams_fromJson(lean_object* v_json_2723_){
_start:
{
lean_object* v___x_2724_; lean_object* v___x_2725_; 
v___x_2724_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__0));
lean_inc(v_json_2723_);
v___x_2725_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoalParams_fromJson_spec__0(v_json_2723_, v___x_2724_);
if (lean_obj_tag(v___x_2725_) == 0)
{
lean_object* v_a_2726_; lean_object* v___x_2728_; uint8_t v_isShared_2729_; uint8_t v_isSharedCheck_2735_; 
lean_dec(v_json_2723_);
v_a_2726_ = lean_ctor_get(v___x_2725_, 0);
v_isSharedCheck_2735_ = !lean_is_exclusive(v___x_2725_);
if (v_isSharedCheck_2735_ == 0)
{
v___x_2728_ = v___x_2725_;
v_isShared_2729_ = v_isSharedCheck_2735_;
goto v_resetjp_2727_;
}
else
{
lean_inc(v_a_2726_);
lean_dec(v___x_2725_);
v___x_2728_ = lean_box(0);
v_isShared_2729_ = v_isSharedCheck_2735_;
goto v_resetjp_2727_;
}
v_resetjp_2727_:
{
lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2733_; 
v___x_2730_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__5, &l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__5);
v___x_2731_ = lean_string_append(v___x_2730_, v_a_2726_);
lean_dec(v_a_2726_);
if (v_isShared_2729_ == 0)
{
lean_ctor_set(v___x_2728_, 0, v___x_2731_);
v___x_2733_ = v___x_2728_;
goto v_reusejp_2732_;
}
else
{
lean_object* v_reuseFailAlloc_2734_; 
v_reuseFailAlloc_2734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2734_, 0, v___x_2731_);
v___x_2733_ = v_reuseFailAlloc_2734_;
goto v_reusejp_2732_;
}
v_reusejp_2732_:
{
return v___x_2733_;
}
}
}
else
{
if (lean_obj_tag(v___x_2725_) == 0)
{
lean_object* v_a_2736_; lean_object* v___x_2738_; uint8_t v_isShared_2739_; uint8_t v_isSharedCheck_2743_; 
lean_dec(v_json_2723_);
v_a_2736_ = lean_ctor_get(v___x_2725_, 0);
v_isSharedCheck_2743_ = !lean_is_exclusive(v___x_2725_);
if (v_isSharedCheck_2743_ == 0)
{
v___x_2738_ = v___x_2725_;
v_isShared_2739_ = v_isSharedCheck_2743_;
goto v_resetjp_2737_;
}
else
{
lean_inc(v_a_2736_);
lean_dec(v___x_2725_);
v___x_2738_ = lean_box(0);
v_isShared_2739_ = v_isSharedCheck_2743_;
goto v_resetjp_2737_;
}
v_resetjp_2737_:
{
lean_object* v___x_2741_; 
if (v_isShared_2739_ == 0)
{
lean_ctor_set_tag(v___x_2738_, 0);
v___x_2741_ = v___x_2738_;
goto v_reusejp_2740_;
}
else
{
lean_object* v_reuseFailAlloc_2742_; 
v_reuseFailAlloc_2742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2742_, 0, v_a_2736_);
v___x_2741_ = v_reuseFailAlloc_2742_;
goto v_reusejp_2740_;
}
v_reusejp_2740_:
{
return v___x_2741_;
}
}
}
else
{
lean_object* v_a_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; 
v_a_2744_ = lean_ctor_get(v___x_2725_, 0);
lean_inc(v_a_2744_);
lean_dec_ref_known(v___x_2725_, 1);
v___x_2745_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__6));
lean_inc(v_json_2723_);
v___x_2746_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoalParams_fromJson_spec__1(v_json_2723_, v___x_2745_);
if (lean_obj_tag(v___x_2746_) == 0)
{
lean_object* v_a_2747_; lean_object* v___x_2749_; uint8_t v_isShared_2750_; uint8_t v_isSharedCheck_2756_; 
lean_dec(v_a_2744_);
lean_dec(v_json_2723_);
v_a_2747_ = lean_ctor_get(v___x_2746_, 0);
v_isSharedCheck_2756_ = !lean_is_exclusive(v___x_2746_);
if (v_isSharedCheck_2756_ == 0)
{
v___x_2749_ = v___x_2746_;
v_isShared_2750_ = v_isSharedCheck_2756_;
goto v_resetjp_2748_;
}
else
{
lean_inc(v_a_2747_);
lean_dec(v___x_2746_);
v___x_2749_ = lean_box(0);
v_isShared_2750_ = v_isSharedCheck_2756_;
goto v_resetjp_2748_;
}
v_resetjp_2748_:
{
lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2754_; 
v___x_2751_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__7);
v___x_2752_ = lean_string_append(v___x_2751_, v_a_2747_);
lean_dec(v_a_2747_);
if (v_isShared_2750_ == 0)
{
lean_ctor_set(v___x_2749_, 0, v___x_2752_);
v___x_2754_ = v___x_2749_;
goto v_reusejp_2753_;
}
else
{
lean_object* v_reuseFailAlloc_2755_; 
v_reuseFailAlloc_2755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2755_, 0, v___x_2752_);
v___x_2754_ = v_reuseFailAlloc_2755_;
goto v_reusejp_2753_;
}
v_reusejp_2753_:
{
return v___x_2754_;
}
}
}
else
{
if (lean_obj_tag(v___x_2746_) == 0)
{
lean_object* v_a_2757_; lean_object* v___x_2759_; uint8_t v_isShared_2760_; uint8_t v_isSharedCheck_2764_; 
lean_dec(v_a_2744_);
lean_dec(v_json_2723_);
v_a_2757_ = lean_ctor_get(v___x_2746_, 0);
v_isSharedCheck_2764_ = !lean_is_exclusive(v___x_2746_);
if (v_isSharedCheck_2764_ == 0)
{
v___x_2759_ = v___x_2746_;
v_isShared_2760_ = v_isSharedCheck_2764_;
goto v_resetjp_2758_;
}
else
{
lean_inc(v_a_2757_);
lean_dec(v___x_2746_);
v___x_2759_ = lean_box(0);
v_isShared_2760_ = v_isSharedCheck_2764_;
goto v_resetjp_2758_;
}
v_resetjp_2758_:
{
lean_object* v___x_2762_; 
if (v_isShared_2760_ == 0)
{
lean_ctor_set_tag(v___x_2759_, 0);
v___x_2762_ = v___x_2759_;
goto v_reusejp_2761_;
}
else
{
lean_object* v_reuseFailAlloc_2763_; 
v_reuseFailAlloc_2763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2763_, 0, v_a_2757_);
v___x_2762_ = v_reuseFailAlloc_2763_;
goto v_reusejp_2761_;
}
v_reusejp_2761_:
{
return v___x_2762_;
}
}
}
else
{
lean_object* v_a_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; 
v_a_2765_ = lean_ctor_get(v___x_2746_, 0);
lean_inc(v_a_2765_);
lean_dec_ref_known(v___x_2746_, 1);
v___x_2766_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__0));
lean_inc(v_json_2723_);
v___x_2767_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcConnected_fromJson_spec__0(v_json_2723_, v___x_2766_);
if (lean_obj_tag(v___x_2767_) == 0)
{
lean_object* v_a_2768_; lean_object* v___x_2770_; uint8_t v_isShared_2771_; uint8_t v_isSharedCheck_2777_; 
lean_dec(v_a_2765_);
lean_dec(v_a_2744_);
lean_dec(v_json_2723_);
v_a_2768_ = lean_ctor_get(v___x_2767_, 0);
v_isSharedCheck_2777_ = !lean_is_exclusive(v___x_2767_);
if (v_isSharedCheck_2777_ == 0)
{
v___x_2770_ = v___x_2767_;
v_isShared_2771_ = v_isSharedCheck_2777_;
goto v_resetjp_2769_;
}
else
{
lean_inc(v_a_2768_);
lean_dec(v___x_2767_);
v___x_2770_ = lean_box(0);
v_isShared_2771_ = v_isSharedCheck_2777_;
goto v_resetjp_2769_;
}
v_resetjp_2769_:
{
lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2775_; 
v___x_2772_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__9, &l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__9);
v___x_2773_ = lean_string_append(v___x_2772_, v_a_2768_);
lean_dec(v_a_2768_);
if (v_isShared_2771_ == 0)
{
lean_ctor_set(v___x_2770_, 0, v___x_2773_);
v___x_2775_ = v___x_2770_;
goto v_reusejp_2774_;
}
else
{
lean_object* v_reuseFailAlloc_2776_; 
v_reuseFailAlloc_2776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2776_, 0, v___x_2773_);
v___x_2775_ = v_reuseFailAlloc_2776_;
goto v_reusejp_2774_;
}
v_reusejp_2774_:
{
return v___x_2775_;
}
}
}
else
{
if (lean_obj_tag(v___x_2767_) == 0)
{
lean_object* v_a_2778_; lean_object* v___x_2780_; uint8_t v_isShared_2781_; uint8_t v_isSharedCheck_2785_; 
lean_dec(v_a_2765_);
lean_dec(v_a_2744_);
lean_dec(v_json_2723_);
v_a_2778_ = lean_ctor_get(v___x_2767_, 0);
v_isSharedCheck_2785_ = !lean_is_exclusive(v___x_2767_);
if (v_isSharedCheck_2785_ == 0)
{
v___x_2780_ = v___x_2767_;
v_isShared_2781_ = v_isSharedCheck_2785_;
goto v_resetjp_2779_;
}
else
{
lean_inc(v_a_2778_);
lean_dec(v___x_2767_);
v___x_2780_ = lean_box(0);
v_isShared_2781_ = v_isSharedCheck_2785_;
goto v_resetjp_2779_;
}
v_resetjp_2779_:
{
lean_object* v___x_2783_; 
if (v_isShared_2781_ == 0)
{
lean_ctor_set_tag(v___x_2780_, 0);
v___x_2783_ = v___x_2780_;
goto v_reusejp_2782_;
}
else
{
lean_object* v_reuseFailAlloc_2784_; 
v_reuseFailAlloc_2784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2784_, 0, v_a_2778_);
v___x_2783_ = v_reuseFailAlloc_2784_;
goto v_reusejp_2782_;
}
v_reusejp_2782_:
{
return v___x_2783_;
}
}
}
else
{
lean_object* v_a_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; 
v_a_2786_ = lean_ctor_get(v___x_2767_, 0);
lean_inc(v_a_2786_);
lean_dec_ref_known(v___x_2767_, 1);
v___x_2787_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__10));
lean_inc(v_json_2723_);
v___x_2788_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcCallParams_fromJson_spec__0(v_json_2723_, v___x_2787_);
if (lean_obj_tag(v___x_2788_) == 0)
{
lean_object* v_a_2789_; lean_object* v___x_2791_; uint8_t v_isShared_2792_; uint8_t v_isSharedCheck_2798_; 
lean_dec(v_a_2786_);
lean_dec(v_a_2765_);
lean_dec(v_a_2744_);
lean_dec(v_json_2723_);
v_a_2789_ = lean_ctor_get(v___x_2788_, 0);
v_isSharedCheck_2798_ = !lean_is_exclusive(v___x_2788_);
if (v_isSharedCheck_2798_ == 0)
{
v___x_2791_ = v___x_2788_;
v_isShared_2792_ = v_isSharedCheck_2798_;
goto v_resetjp_2790_;
}
else
{
lean_inc(v_a_2789_);
lean_dec(v___x_2788_);
v___x_2791_ = lean_box(0);
v_isShared_2792_ = v_isSharedCheck_2798_;
goto v_resetjp_2790_;
}
v_resetjp_2790_:
{
lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2796_; 
v___x_2793_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__14, &l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__14_once, _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__14);
v___x_2794_ = lean_string_append(v___x_2793_, v_a_2789_);
lean_dec(v_a_2789_);
if (v_isShared_2792_ == 0)
{
lean_ctor_set(v___x_2791_, 0, v___x_2794_);
v___x_2796_ = v___x_2791_;
goto v_reusejp_2795_;
}
else
{
lean_object* v_reuseFailAlloc_2797_; 
v_reuseFailAlloc_2797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2797_, 0, v___x_2794_);
v___x_2796_ = v_reuseFailAlloc_2797_;
goto v_reusejp_2795_;
}
v_reusejp_2795_:
{
return v___x_2796_;
}
}
}
else
{
if (lean_obj_tag(v___x_2788_) == 0)
{
lean_object* v_a_2799_; lean_object* v___x_2801_; uint8_t v_isShared_2802_; uint8_t v_isSharedCheck_2806_; 
lean_dec(v_a_2786_);
lean_dec(v_a_2765_);
lean_dec(v_a_2744_);
lean_dec(v_json_2723_);
v_a_2799_ = lean_ctor_get(v___x_2788_, 0);
v_isSharedCheck_2806_ = !lean_is_exclusive(v___x_2788_);
if (v_isSharedCheck_2806_ == 0)
{
v___x_2801_ = v___x_2788_;
v_isShared_2802_ = v_isSharedCheck_2806_;
goto v_resetjp_2800_;
}
else
{
lean_inc(v_a_2799_);
lean_dec(v___x_2788_);
v___x_2801_ = lean_box(0);
v_isShared_2802_ = v_isSharedCheck_2806_;
goto v_resetjp_2800_;
}
v_resetjp_2800_:
{
lean_object* v___x_2804_; 
if (v_isShared_2802_ == 0)
{
lean_ctor_set_tag(v___x_2801_, 0);
v___x_2804_ = v___x_2801_;
goto v_reusejp_2803_;
}
else
{
lean_object* v_reuseFailAlloc_2805_; 
v_reuseFailAlloc_2805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2805_, 0, v_a_2799_);
v___x_2804_ = v_reuseFailAlloc_2805_;
goto v_reusejp_2803_;
}
v_reusejp_2803_:
{
return v___x_2804_;
}
}
}
else
{
lean_object* v_a_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v_a_2810_; lean_object* v___x_2812_; uint8_t v_isShared_2813_; uint8_t v_isSharedCheck_2820_; 
v_a_2807_ = lean_ctor_get(v___x_2788_, 0);
lean_inc(v_a_2807_);
lean_dec_ref_known(v___x_2788_, 1);
v___x_2808_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__15));
v___x_2809_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcCallParams_fromJson_spec__1(v_json_2723_, v___x_2808_);
v_a_2810_ = lean_ctor_get(v___x_2809_, 0);
v_isSharedCheck_2820_ = !lean_is_exclusive(v___x_2809_);
if (v_isSharedCheck_2820_ == 0)
{
v___x_2812_ = v___x_2809_;
v_isShared_2813_ = v_isSharedCheck_2820_;
goto v_resetjp_2811_;
}
else
{
lean_inc(v_a_2810_);
lean_dec(v___x_2809_);
v___x_2812_ = lean_box(0);
v_isShared_2813_ = v_isSharedCheck_2820_;
goto v_resetjp_2811_;
}
v_resetjp_2811_:
{
lean_object* v___x_2814_; lean_object* v___x_2815_; uint64_t v___x_2816_; lean_object* v___x_2818_; 
v___x_2814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2814_, 0, v_a_2744_);
lean_ctor_set(v___x_2814_, 1, v_a_2765_);
v___x_2815_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_2815_, 0, v___x_2814_);
lean_ctor_set(v___x_2815_, 1, v_a_2807_);
lean_ctor_set(v___x_2815_, 2, v_a_2810_);
v___x_2816_ = lean_unbox_uint64(v_a_2786_);
lean_dec(v_a_2786_);
lean_ctor_set_uint64(v___x_2815_, sizeof(void*)*3, v___x_2816_);
if (v_isShared_2813_ == 0)
{
lean_ctor_set(v___x_2812_, 0, v___x_2815_);
v___x_2818_ = v___x_2812_;
goto v_reusejp_2817_;
}
else
{
lean_object* v_reuseFailAlloc_2819_; 
v_reuseFailAlloc_2819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2819_, 0, v___x_2815_);
v___x_2818_ = v_reuseFailAlloc_2819_;
goto v_reusejp_2817_;
}
v_reusejp_2817_:
{
return v___x_2818_;
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
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRpcCallParams_toJson(lean_object* v_x_2823_){
_start:
{
lean_object* v_toTextDocumentPositionParams_2824_; uint64_t v_sessionId_2825_; lean_object* v_method_2826_; lean_object* v_params_2827_; lean_object* v_textDocument_2828_; lean_object* v_position_2829_; lean_object* v___x_2831_; uint8_t v_isShared_2832_; uint8_t v_isSharedCheck_2866_; 
v_toTextDocumentPositionParams_2824_ = lean_ctor_get(v_x_2823_, 0);
lean_inc_ref(v_toTextDocumentPositionParams_2824_);
v_sessionId_2825_ = lean_ctor_get_uint64(v_x_2823_, sizeof(void*)*3);
v_method_2826_ = lean_ctor_get(v_x_2823_, 1);
lean_inc(v_method_2826_);
v_params_2827_ = lean_ctor_get(v_x_2823_, 2);
lean_inc(v_params_2827_);
lean_dec_ref(v_x_2823_);
v_textDocument_2828_ = lean_ctor_get(v_toTextDocumentPositionParams_2824_, 0);
v_position_2829_ = lean_ctor_get(v_toTextDocumentPositionParams_2824_, 1);
v_isSharedCheck_2866_ = !lean_is_exclusive(v_toTextDocumentPositionParams_2824_);
if (v_isSharedCheck_2866_ == 0)
{
v___x_2831_ = v_toTextDocumentPositionParams_2824_;
v_isShared_2832_ = v_isSharedCheck_2866_;
goto v_resetjp_2830_;
}
else
{
lean_inc(v_position_2829_);
lean_inc(v_textDocument_2828_);
lean_dec(v_toTextDocumentPositionParams_2824_);
v___x_2831_ = lean_box(0);
v_isShared_2832_ = v_isSharedCheck_2866_;
goto v_resetjp_2830_;
}
v_resetjp_2830_:
{
lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2836_; 
v___x_2833_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__0));
v___x_2834_ = l_Lean_Lsp_instToJsonTextDocumentIdentifier_toJson(v_textDocument_2828_);
if (v_isShared_2832_ == 0)
{
lean_ctor_set(v___x_2831_, 1, v___x_2834_);
lean_ctor_set(v___x_2831_, 0, v___x_2833_);
v___x_2836_ = v___x_2831_;
goto v_reusejp_2835_;
}
else
{
lean_object* v_reuseFailAlloc_2865_; 
v_reuseFailAlloc_2865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2865_, 0, v___x_2833_);
lean_ctor_set(v_reuseFailAlloc_2865_, 1, v___x_2834_);
v___x_2836_ = v_reuseFailAlloc_2865_;
goto v_reusejp_2835_;
}
v_reusejp_2835_:
{
lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; uint8_t v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; 
v___x_2837_ = lean_box(0);
v___x_2838_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2838_, 0, v___x_2836_);
lean_ctor_set(v___x_2838_, 1, v___x_2837_);
v___x_2839_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__6));
v___x_2840_ = l_Lean_Lsp_instToJsonPosition_toJson(v_position_2829_);
v___x_2841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2841_, 0, v___x_2839_);
lean_ctor_set(v___x_2841_, 1, v___x_2840_);
v___x_2842_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2842_, 0, v___x_2841_);
lean_ctor_set(v___x_2842_, 1, v___x_2837_);
v___x_2843_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__0));
v___x_2844_ = lean_uint64_to_nat(v_sessionId_2825_);
v___x_2845_ = l_Lean_bignumToJson(v___x_2844_);
v___x_2846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2846_, 0, v___x_2843_);
lean_ctor_set(v___x_2846_, 1, v___x_2845_);
v___x_2847_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2847_, 0, v___x_2846_);
lean_ctor_set(v___x_2847_, 1, v___x_2837_);
v___x_2848_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__10));
v___x_2849_ = 1;
v___x_2850_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_method_2826_, v___x_2849_);
v___x_2851_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2851_, 0, v___x_2850_);
v___x_2852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2852_, 0, v___x_2848_);
lean_ctor_set(v___x_2852_, 1, v___x_2851_);
v___x_2853_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2853_, 0, v___x_2852_);
lean_ctor_set(v___x_2853_, 1, v___x_2837_);
v___x_2854_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__15));
v___x_2855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2855_, 0, v___x_2854_);
lean_ctor_set(v___x_2855_, 1, v_params_2827_);
v___x_2856_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2856_, 0, v___x_2855_);
lean_ctor_set(v___x_2856_, 1, v___x_2837_);
v___x_2857_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2857_, 0, v___x_2856_);
lean_ctor_set(v___x_2857_, 1, v___x_2837_);
v___x_2858_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2858_, 0, v___x_2853_);
lean_ctor_set(v___x_2858_, 1, v___x_2857_);
v___x_2859_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2859_, 0, v___x_2847_);
lean_ctor_set(v___x_2859_, 1, v___x_2858_);
v___x_2860_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2860_, 0, v___x_2842_);
lean_ctor_set(v___x_2860_, 1, v___x_2859_);
v___x_2861_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2861_, 0, v___x_2838_);
lean_ctor_set(v___x_2861_, 1, v___x_2860_);
v___x_2862_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0));
v___x_2863_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_2861_, v___x_2862_);
v___x_2864_ = l_Lean_Json_mkObj(v___x_2863_);
lean_dec(v___x_2863_);
return v___x_2864_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcReleaseParams_fromJson_spec__0_spec__0_spec__1(size_t v_sz_2869_, size_t v_i_2870_, lean_object* v_bs_2871_){
_start:
{
uint8_t v___x_2872_; 
v___x_2872_ = lean_usize_dec_lt(v_i_2870_, v_sz_2869_);
if (v___x_2872_ == 0)
{
lean_object* v___x_2873_; 
v___x_2873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2873_, 0, v_bs_2871_);
return v___x_2873_;
}
else
{
lean_object* v_v_2874_; lean_object* v___x_2875_; lean_object* v_bs_x27_2876_; size_t v___x_2877_; size_t v___x_2878_; lean_object* v___x_2879_; 
v_v_2874_ = lean_array_uget(v_bs_2871_, v_i_2870_);
v___x_2875_ = lean_unsigned_to_nat(0u);
v_bs_x27_2876_ = lean_array_uset(v_bs_2871_, v_i_2870_, v___x_2875_);
v___x_2877_ = ((size_t)1ULL);
v___x_2878_ = lean_usize_add(v_i_2870_, v___x_2877_);
v___x_2879_ = lean_array_uset(v_bs_x27_2876_, v_i_2870_, v_v_2874_);
v_i_2870_ = v___x_2878_;
v_bs_2871_ = v___x_2879_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcReleaseParams_fromJson_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_2881_, lean_object* v_i_2882_, lean_object* v_bs_2883_){
_start:
{
size_t v_sz_boxed_2884_; size_t v_i_boxed_2885_; lean_object* v_res_2886_; 
v_sz_boxed_2884_ = lean_unbox_usize(v_sz_2881_);
lean_dec(v_sz_2881_);
v_i_boxed_2885_ = lean_unbox_usize(v_i_2882_);
lean_dec(v_i_2882_);
v_res_2886_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcReleaseParams_fromJson_spec__0_spec__0_spec__1(v_sz_boxed_2884_, v_i_boxed_2885_, v_bs_2883_);
return v_res_2886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcReleaseParams_fromJson_spec__0_spec__0(lean_object* v_x_2887_){
_start:
{
if (lean_obj_tag(v_x_2887_) == 4)
{
lean_object* v_elems_2888_; size_t v_sz_2889_; size_t v___x_2890_; lean_object* v___x_2891_; 
v_elems_2888_ = lean_ctor_get(v_x_2887_, 0);
lean_inc_ref(v_elems_2888_);
lean_dec_ref_known(v_x_2887_, 1);
v_sz_2889_ = lean_array_size(v_elems_2888_);
v___x_2890_ = ((size_t)0ULL);
v___x_2891_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcReleaseParams_fromJson_spec__0_spec__0_spec__1(v_sz_2889_, v___x_2890_, v_elems_2888_);
return v___x_2891_;
}
else
{
lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; 
v___x_2892_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__1_spec__1___closed__0));
v___x_2893_ = lean_unsigned_to_nat(80u);
v___x_2894_ = l_Lean_Json_pretty(v_x_2887_, v___x_2893_);
v___x_2895_ = lean_string_append(v___x_2892_, v___x_2894_);
lean_dec_ref(v___x_2894_);
v___x_2896_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressKind___lam__0___closed__1));
v___x_2897_ = lean_string_append(v___x_2895_, v___x_2896_);
v___x_2898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2898_, 0, v___x_2897_);
return v___x_2898_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcReleaseParams_fromJson_spec__0(lean_object* v_j_2899_, lean_object* v_k_2900_){
_start:
{
lean_object* v___x_2901_; lean_object* v___x_2902_; 
v___x_2901_ = l_Lean_Json_getObjValD(v_j_2899_, v_k_2900_);
v___x_2902_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcReleaseParams_fromJson_spec__0_spec__0(v___x_2901_);
return v___x_2902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcReleaseParams_fromJson_spec__0___boxed(lean_object* v_j_2903_, lean_object* v_k_2904_){
_start:
{
lean_object* v_res_2905_; 
v_res_2905_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcReleaseParams_fromJson_spec__0(v_j_2903_, v_k_2904_);
lean_dec_ref(v_k_2904_);
return v_res_2905_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__2(void){
_start:
{
uint8_t v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; 
v___x_2911_ = 1;
v___x_2912_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__1));
v___x_2913_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2912_, v___x_2911_);
return v___x_2913_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__3(void){
_start:
{
lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; 
v___x_2914_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6));
v___x_2915_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__2, &l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__2);
v___x_2916_ = lean_string_append(v___x_2915_, v___x_2914_);
return v___x_2916_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; 
v___x_2917_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__6, &l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__6);
v___x_2918_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__3);
v___x_2919_ = lean_string_append(v___x_2918_, v___x_2917_);
return v___x_2919_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__5(void){
_start:
{
lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; 
v___x_2920_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_2921_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__4);
v___x_2922_ = lean_string_append(v___x_2921_, v___x_2920_);
return v___x_2922_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__6(void){
_start:
{
lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; 
v___x_2923_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__6, &l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__6);
v___x_2924_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__3);
v___x_2925_ = lean_string_append(v___x_2924_, v___x_2923_);
return v___x_2925_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__7(void){
_start:
{
lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; 
v___x_2926_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_2927_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__6, &l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__6);
v___x_2928_ = lean_string_append(v___x_2927_, v___x_2926_);
return v___x_2928_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__10(void){
_start:
{
uint8_t v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; 
v___x_2932_ = 1;
v___x_2933_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__9));
v___x_2934_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2933_, v___x_2932_);
return v___x_2934_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__11(void){
_start:
{
lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; 
v___x_2935_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__10, &l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__10);
v___x_2936_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__3);
v___x_2937_ = lean_string_append(v___x_2936_, v___x_2935_);
return v___x_2937_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__12(void){
_start:
{
lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; 
v___x_2938_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_2939_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__11, &l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__11);
v___x_2940_ = lean_string_append(v___x_2939_, v___x_2938_);
return v___x_2940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson(lean_object* v_json_2941_){
_start:
{
lean_object* v___x_2942_; lean_object* v___x_2943_; 
v___x_2942_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__0));
lean_inc(v_json_2941_);
v___x_2943_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson_spec__0(v_json_2941_, v___x_2942_);
if (lean_obj_tag(v___x_2943_) == 0)
{
lean_object* v_a_2944_; lean_object* v___x_2946_; uint8_t v_isShared_2947_; uint8_t v_isSharedCheck_2953_; 
lean_dec(v_json_2941_);
v_a_2944_ = lean_ctor_get(v___x_2943_, 0);
v_isSharedCheck_2953_ = !lean_is_exclusive(v___x_2943_);
if (v_isSharedCheck_2953_ == 0)
{
v___x_2946_ = v___x_2943_;
v_isShared_2947_ = v_isSharedCheck_2953_;
goto v_resetjp_2945_;
}
else
{
lean_inc(v_a_2944_);
lean_dec(v___x_2943_);
v___x_2946_ = lean_box(0);
v_isShared_2947_ = v_isSharedCheck_2953_;
goto v_resetjp_2945_;
}
v_resetjp_2945_:
{
lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2951_; 
v___x_2948_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__5, &l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__5);
v___x_2949_ = lean_string_append(v___x_2948_, v_a_2944_);
lean_dec(v_a_2944_);
if (v_isShared_2947_ == 0)
{
lean_ctor_set(v___x_2946_, 0, v___x_2949_);
v___x_2951_ = v___x_2946_;
goto v_reusejp_2950_;
}
else
{
lean_object* v_reuseFailAlloc_2952_; 
v_reuseFailAlloc_2952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2952_, 0, v___x_2949_);
v___x_2951_ = v_reuseFailAlloc_2952_;
goto v_reusejp_2950_;
}
v_reusejp_2950_:
{
return v___x_2951_;
}
}
}
else
{
if (lean_obj_tag(v___x_2943_) == 0)
{
lean_object* v_a_2954_; lean_object* v___x_2956_; uint8_t v_isShared_2957_; uint8_t v_isSharedCheck_2961_; 
lean_dec(v_json_2941_);
v_a_2954_ = lean_ctor_get(v___x_2943_, 0);
v_isSharedCheck_2961_ = !lean_is_exclusive(v___x_2943_);
if (v_isSharedCheck_2961_ == 0)
{
v___x_2956_ = v___x_2943_;
v_isShared_2957_ = v_isSharedCheck_2961_;
goto v_resetjp_2955_;
}
else
{
lean_inc(v_a_2954_);
lean_dec(v___x_2943_);
v___x_2956_ = lean_box(0);
v_isShared_2957_ = v_isSharedCheck_2961_;
goto v_resetjp_2955_;
}
v_resetjp_2955_:
{
lean_object* v___x_2959_; 
if (v_isShared_2957_ == 0)
{
lean_ctor_set_tag(v___x_2956_, 0);
v___x_2959_ = v___x_2956_;
goto v_reusejp_2958_;
}
else
{
lean_object* v_reuseFailAlloc_2960_; 
v_reuseFailAlloc_2960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2960_, 0, v_a_2954_);
v___x_2959_ = v_reuseFailAlloc_2960_;
goto v_reusejp_2958_;
}
v_reusejp_2958_:
{
return v___x_2959_;
}
}
}
else
{
lean_object* v_a_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; 
v_a_2962_ = lean_ctor_get(v___x_2943_, 0);
lean_inc(v_a_2962_);
lean_dec_ref_known(v___x_2943_, 1);
v___x_2963_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__0));
lean_inc(v_json_2941_);
v___x_2964_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcConnected_fromJson_spec__0(v_json_2941_, v___x_2963_);
if (lean_obj_tag(v___x_2964_) == 0)
{
lean_object* v_a_2965_; lean_object* v___x_2967_; uint8_t v_isShared_2968_; uint8_t v_isSharedCheck_2974_; 
lean_dec(v_a_2962_);
lean_dec(v_json_2941_);
v_a_2965_ = lean_ctor_get(v___x_2964_, 0);
v_isSharedCheck_2974_ = !lean_is_exclusive(v___x_2964_);
if (v_isSharedCheck_2974_ == 0)
{
v___x_2967_ = v___x_2964_;
v_isShared_2968_ = v_isSharedCheck_2974_;
goto v_resetjp_2966_;
}
else
{
lean_inc(v_a_2965_);
lean_dec(v___x_2964_);
v___x_2967_ = lean_box(0);
v_isShared_2968_ = v_isSharedCheck_2974_;
goto v_resetjp_2966_;
}
v_resetjp_2966_:
{
lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2972_; 
v___x_2969_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__7);
v___x_2970_ = lean_string_append(v___x_2969_, v_a_2965_);
lean_dec(v_a_2965_);
if (v_isShared_2968_ == 0)
{
lean_ctor_set(v___x_2967_, 0, v___x_2970_);
v___x_2972_ = v___x_2967_;
goto v_reusejp_2971_;
}
else
{
lean_object* v_reuseFailAlloc_2973_; 
v_reuseFailAlloc_2973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2973_, 0, v___x_2970_);
v___x_2972_ = v_reuseFailAlloc_2973_;
goto v_reusejp_2971_;
}
v_reusejp_2971_:
{
return v___x_2972_;
}
}
}
else
{
if (lean_obj_tag(v___x_2964_) == 0)
{
lean_object* v_a_2975_; lean_object* v___x_2977_; uint8_t v_isShared_2978_; uint8_t v_isSharedCheck_2982_; 
lean_dec(v_a_2962_);
lean_dec(v_json_2941_);
v_a_2975_ = lean_ctor_get(v___x_2964_, 0);
v_isSharedCheck_2982_ = !lean_is_exclusive(v___x_2964_);
if (v_isSharedCheck_2982_ == 0)
{
v___x_2977_ = v___x_2964_;
v_isShared_2978_ = v_isSharedCheck_2982_;
goto v_resetjp_2976_;
}
else
{
lean_inc(v_a_2975_);
lean_dec(v___x_2964_);
v___x_2977_ = lean_box(0);
v_isShared_2978_ = v_isSharedCheck_2982_;
goto v_resetjp_2976_;
}
v_resetjp_2976_:
{
lean_object* v___x_2980_; 
if (v_isShared_2978_ == 0)
{
lean_ctor_set_tag(v___x_2977_, 0);
v___x_2980_ = v___x_2977_;
goto v_reusejp_2979_;
}
else
{
lean_object* v_reuseFailAlloc_2981_; 
v_reuseFailAlloc_2981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2981_, 0, v_a_2975_);
v___x_2980_ = v_reuseFailAlloc_2981_;
goto v_reusejp_2979_;
}
v_reusejp_2979_:
{
return v___x_2980_;
}
}
}
else
{
lean_object* v_a_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; 
v_a_2983_ = lean_ctor_get(v___x_2964_, 0);
lean_inc(v_a_2983_);
lean_dec_ref_known(v___x_2964_, 1);
v___x_2984_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__8));
v___x_2985_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcReleaseParams_fromJson_spec__0(v_json_2941_, v___x_2984_);
if (lean_obj_tag(v___x_2985_) == 0)
{
lean_object* v_a_2986_; lean_object* v___x_2988_; uint8_t v_isShared_2989_; uint8_t v_isSharedCheck_2995_; 
lean_dec(v_a_2983_);
lean_dec(v_a_2962_);
v_a_2986_ = lean_ctor_get(v___x_2985_, 0);
v_isSharedCheck_2995_ = !lean_is_exclusive(v___x_2985_);
if (v_isSharedCheck_2995_ == 0)
{
v___x_2988_ = v___x_2985_;
v_isShared_2989_ = v_isSharedCheck_2995_;
goto v_resetjp_2987_;
}
else
{
lean_inc(v_a_2986_);
lean_dec(v___x_2985_);
v___x_2988_ = lean_box(0);
v_isShared_2989_ = v_isSharedCheck_2995_;
goto v_resetjp_2987_;
}
v_resetjp_2987_:
{
lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2993_; 
v___x_2990_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__12, &l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__12);
v___x_2991_ = lean_string_append(v___x_2990_, v_a_2986_);
lean_dec(v_a_2986_);
if (v_isShared_2989_ == 0)
{
lean_ctor_set(v___x_2988_, 0, v___x_2991_);
v___x_2993_ = v___x_2988_;
goto v_reusejp_2992_;
}
else
{
lean_object* v_reuseFailAlloc_2994_; 
v_reuseFailAlloc_2994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2994_, 0, v___x_2991_);
v___x_2993_ = v_reuseFailAlloc_2994_;
goto v_reusejp_2992_;
}
v_reusejp_2992_:
{
return v___x_2993_;
}
}
}
else
{
if (lean_obj_tag(v___x_2985_) == 0)
{
lean_object* v_a_2996_; lean_object* v___x_2998_; uint8_t v_isShared_2999_; uint8_t v_isSharedCheck_3003_; 
lean_dec(v_a_2983_);
lean_dec(v_a_2962_);
v_a_2996_ = lean_ctor_get(v___x_2985_, 0);
v_isSharedCheck_3003_ = !lean_is_exclusive(v___x_2985_);
if (v_isSharedCheck_3003_ == 0)
{
v___x_2998_ = v___x_2985_;
v_isShared_2999_ = v_isSharedCheck_3003_;
goto v_resetjp_2997_;
}
else
{
lean_inc(v_a_2996_);
lean_dec(v___x_2985_);
v___x_2998_ = lean_box(0);
v_isShared_2999_ = v_isSharedCheck_3003_;
goto v_resetjp_2997_;
}
v_resetjp_2997_:
{
lean_object* v___x_3001_; 
if (v_isShared_2999_ == 0)
{
lean_ctor_set_tag(v___x_2998_, 0);
v___x_3001_ = v___x_2998_;
goto v_reusejp_3000_;
}
else
{
lean_object* v_reuseFailAlloc_3002_; 
v_reuseFailAlloc_3002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3002_, 0, v_a_2996_);
v___x_3001_ = v_reuseFailAlloc_3002_;
goto v_reusejp_3000_;
}
v_reusejp_3000_:
{
return v___x_3001_;
}
}
}
else
{
lean_object* v_a_3004_; lean_object* v___x_3006_; uint8_t v_isShared_3007_; uint8_t v_isSharedCheck_3013_; 
v_a_3004_ = lean_ctor_get(v___x_2985_, 0);
v_isSharedCheck_3013_ = !lean_is_exclusive(v___x_2985_);
if (v_isSharedCheck_3013_ == 0)
{
v___x_3006_ = v___x_2985_;
v_isShared_3007_ = v_isSharedCheck_3013_;
goto v_resetjp_3005_;
}
else
{
lean_inc(v_a_3004_);
lean_dec(v___x_2985_);
v___x_3006_ = lean_box(0);
v_isShared_3007_ = v_isSharedCheck_3013_;
goto v_resetjp_3005_;
}
v_resetjp_3005_:
{
lean_object* v___x_3008_; uint64_t v___x_3009_; lean_object* v___x_3011_; 
v___x_3008_ = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(v___x_3008_, 0, v_a_2962_);
lean_ctor_set(v___x_3008_, 1, v_a_3004_);
v___x_3009_ = lean_unbox_uint64(v_a_2983_);
lean_dec(v_a_2983_);
lean_ctor_set_uint64(v___x_3008_, sizeof(void*)*2, v___x_3009_);
if (v_isShared_3007_ == 0)
{
lean_ctor_set(v___x_3006_, 0, v___x_3008_);
v___x_3011_ = v___x_3006_;
goto v_reusejp_3010_;
}
else
{
lean_object* v_reuseFailAlloc_3012_; 
v_reuseFailAlloc_3012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3012_, 0, v___x_3008_);
v___x_3011_ = v_reuseFailAlloc_3012_;
goto v_reusejp_3010_;
}
v_reusejp_3010_:
{
return v___x_3011_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonRpcReleaseParams_toJson_spec__0_spec__0(size_t v_sz_3016_, size_t v_i_3017_, lean_object* v_bs_3018_){
_start:
{
uint8_t v___x_3019_; 
v___x_3019_ = lean_usize_dec_lt(v_i_3017_, v_sz_3016_);
if (v___x_3019_ == 0)
{
return v_bs_3018_;
}
else
{
lean_object* v_v_3020_; lean_object* v___x_3021_; lean_object* v_bs_x27_3022_; size_t v___x_3023_; size_t v___x_3024_; lean_object* v___x_3025_; 
v_v_3020_ = lean_array_uget(v_bs_3018_, v_i_3017_);
v___x_3021_ = lean_unsigned_to_nat(0u);
v_bs_x27_3022_ = lean_array_uset(v_bs_3018_, v_i_3017_, v___x_3021_);
v___x_3023_ = ((size_t)1ULL);
v___x_3024_ = lean_usize_add(v_i_3017_, v___x_3023_);
v___x_3025_ = lean_array_uset(v_bs_x27_3022_, v_i_3017_, v_v_3020_);
v_i_3017_ = v___x_3024_;
v_bs_3018_ = v___x_3025_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonRpcReleaseParams_toJson_spec__0_spec__0___boxed(lean_object* v_sz_3027_, lean_object* v_i_3028_, lean_object* v_bs_3029_){
_start:
{
size_t v_sz_boxed_3030_; size_t v_i_boxed_3031_; lean_object* v_res_3032_; 
v_sz_boxed_3030_ = lean_unbox_usize(v_sz_3027_);
lean_dec(v_sz_3027_);
v_i_boxed_3031_ = lean_unbox_usize(v_i_3028_);
lean_dec(v_i_3028_);
v_res_3032_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonRpcReleaseParams_toJson_spec__0_spec__0(v_sz_boxed_3030_, v_i_boxed_3031_, v_bs_3029_);
return v_res_3032_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonRpcReleaseParams_toJson_spec__0(lean_object* v_a_3033_){
_start:
{
size_t v_sz_3034_; size_t v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; 
v_sz_3034_ = lean_array_size(v_a_3033_);
v___x_3035_ = ((size_t)0ULL);
v___x_3036_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonRpcReleaseParams_toJson_spec__0_spec__0(v_sz_3034_, v___x_3035_, v_a_3033_);
v___x_3037_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3037_, 0, v___x_3036_);
return v___x_3037_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRpcReleaseParams_toJson(lean_object* v_x_3038_){
_start:
{
lean_object* v_uri_3039_; uint64_t v_sessionId_3040_; lean_object* v_refs_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; 
v_uri_3039_ = lean_ctor_get(v_x_3038_, 0);
lean_inc_ref(v_uri_3039_);
v_sessionId_3040_ = lean_ctor_get_uint64(v_x_3038_, sizeof(void*)*2);
v_refs_3041_ = lean_ctor_get(v_x_3038_, 1);
lean_inc_ref(v_refs_3041_);
lean_dec_ref(v_x_3038_);
v___x_3042_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__0));
v___x_3043_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3043_, 0, v_uri_3039_);
v___x_3044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3044_, 0, v___x_3042_);
lean_ctor_set(v___x_3044_, 1, v___x_3043_);
v___x_3045_ = lean_box(0);
v___x_3046_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3046_, 0, v___x_3044_);
lean_ctor_set(v___x_3046_, 1, v___x_3045_);
v___x_3047_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__0));
v___x_3048_ = lean_uint64_to_nat(v_sessionId_3040_);
v___x_3049_ = l_Lean_bignumToJson(v___x_3048_);
v___x_3050_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3050_, 0, v___x_3047_);
lean_ctor_set(v___x_3050_, 1, v___x_3049_);
v___x_3051_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3051_, 0, v___x_3050_);
lean_ctor_set(v___x_3051_, 1, v___x_3045_);
v___x_3052_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__8));
v___x_3053_ = l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonRpcReleaseParams_toJson_spec__0(v_refs_3041_);
v___x_3054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3054_, 0, v___x_3052_);
lean_ctor_set(v___x_3054_, 1, v___x_3053_);
v___x_3055_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3055_, 0, v___x_3054_);
lean_ctor_set(v___x_3055_, 1, v___x_3045_);
v___x_3056_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3056_, 0, v___x_3055_);
lean_ctor_set(v___x_3056_, 1, v___x_3045_);
v___x_3057_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3057_, 0, v___x_3051_);
lean_ctor_set(v___x_3057_, 1, v___x_3056_);
v___x_3058_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3058_, 0, v___x_3046_);
lean_ctor_set(v___x_3058_, 1, v___x_3057_);
v___x_3059_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0));
v___x_3060_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_3058_, v___x_3059_);
v___x_3061_ = l_Lean_Json_mkObj(v___x_3060_);
lean_dec(v___x_3060_);
return v___x_3061_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__2(void){
_start:
{
uint8_t v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; 
v___x_3069_ = 1;
v___x_3070_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__1));
v___x_3071_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3070_, v___x_3069_);
return v___x_3071_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__3(void){
_start:
{
lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; 
v___x_3072_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6));
v___x_3073_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__2, &l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__2);
v___x_3074_ = lean_string_append(v___x_3073_, v___x_3072_);
return v___x_3074_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; 
v___x_3075_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__6, &l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__6);
v___x_3076_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__3);
v___x_3077_ = lean_string_append(v___x_3076_, v___x_3075_);
return v___x_3077_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__5(void){
_start:
{
lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; 
v___x_3078_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_3079_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__4);
v___x_3080_ = lean_string_append(v___x_3079_, v___x_3078_);
return v___x_3080_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__6(void){
_start:
{
lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; 
v___x_3081_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__6, &l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__6);
v___x_3082_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__3);
v___x_3083_ = lean_string_append(v___x_3082_, v___x_3081_);
return v___x_3083_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__7(void){
_start:
{
lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; 
v___x_3084_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_3085_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__6, &l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__6);
v___x_3086_ = lean_string_append(v___x_3085_, v___x_3084_);
return v___x_3086_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson(lean_object* v_json_3087_){
_start:
{
lean_object* v___x_3088_; lean_object* v___x_3089_; 
v___x_3088_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__0));
lean_inc(v_json_3087_);
v___x_3089_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson_spec__0(v_json_3087_, v___x_3088_);
if (lean_obj_tag(v___x_3089_) == 0)
{
lean_object* v_a_3090_; lean_object* v___x_3092_; uint8_t v_isShared_3093_; uint8_t v_isSharedCheck_3099_; 
lean_dec(v_json_3087_);
v_a_3090_ = lean_ctor_get(v___x_3089_, 0);
v_isSharedCheck_3099_ = !lean_is_exclusive(v___x_3089_);
if (v_isSharedCheck_3099_ == 0)
{
v___x_3092_ = v___x_3089_;
v_isShared_3093_ = v_isSharedCheck_3099_;
goto v_resetjp_3091_;
}
else
{
lean_inc(v_a_3090_);
lean_dec(v___x_3089_);
v___x_3092_ = lean_box(0);
v_isShared_3093_ = v_isSharedCheck_3099_;
goto v_resetjp_3091_;
}
v_resetjp_3091_:
{
lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3097_; 
v___x_3094_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__5, &l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__5);
v___x_3095_ = lean_string_append(v___x_3094_, v_a_3090_);
lean_dec(v_a_3090_);
if (v_isShared_3093_ == 0)
{
lean_ctor_set(v___x_3092_, 0, v___x_3095_);
v___x_3097_ = v___x_3092_;
goto v_reusejp_3096_;
}
else
{
lean_object* v_reuseFailAlloc_3098_; 
v_reuseFailAlloc_3098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3098_, 0, v___x_3095_);
v___x_3097_ = v_reuseFailAlloc_3098_;
goto v_reusejp_3096_;
}
v_reusejp_3096_:
{
return v___x_3097_;
}
}
}
else
{
if (lean_obj_tag(v___x_3089_) == 0)
{
lean_object* v_a_3100_; lean_object* v___x_3102_; uint8_t v_isShared_3103_; uint8_t v_isSharedCheck_3107_; 
lean_dec(v_json_3087_);
v_a_3100_ = lean_ctor_get(v___x_3089_, 0);
v_isSharedCheck_3107_ = !lean_is_exclusive(v___x_3089_);
if (v_isSharedCheck_3107_ == 0)
{
v___x_3102_ = v___x_3089_;
v_isShared_3103_ = v_isSharedCheck_3107_;
goto v_resetjp_3101_;
}
else
{
lean_inc(v_a_3100_);
lean_dec(v___x_3089_);
v___x_3102_ = lean_box(0);
v_isShared_3103_ = v_isSharedCheck_3107_;
goto v_resetjp_3101_;
}
v_resetjp_3101_:
{
lean_object* v___x_3105_; 
if (v_isShared_3103_ == 0)
{
lean_ctor_set_tag(v___x_3102_, 0);
v___x_3105_ = v___x_3102_;
goto v_reusejp_3104_;
}
else
{
lean_object* v_reuseFailAlloc_3106_; 
v_reuseFailAlloc_3106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3106_, 0, v_a_3100_);
v___x_3105_ = v_reuseFailAlloc_3106_;
goto v_reusejp_3104_;
}
v_reusejp_3104_:
{
return v___x_3105_;
}
}
}
else
{
lean_object* v_a_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; 
v_a_3108_ = lean_ctor_get(v___x_3089_, 0);
lean_inc(v_a_3108_);
lean_dec_ref_known(v___x_3089_, 1);
v___x_3109_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__0));
v___x_3110_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcConnected_fromJson_spec__0(v_json_3087_, v___x_3109_);
if (lean_obj_tag(v___x_3110_) == 0)
{
lean_object* v_a_3111_; lean_object* v___x_3113_; uint8_t v_isShared_3114_; uint8_t v_isSharedCheck_3120_; 
lean_dec(v_a_3108_);
v_a_3111_ = lean_ctor_get(v___x_3110_, 0);
v_isSharedCheck_3120_ = !lean_is_exclusive(v___x_3110_);
if (v_isSharedCheck_3120_ == 0)
{
v___x_3113_ = v___x_3110_;
v_isShared_3114_ = v_isSharedCheck_3120_;
goto v_resetjp_3112_;
}
else
{
lean_inc(v_a_3111_);
lean_dec(v___x_3110_);
v___x_3113_ = lean_box(0);
v_isShared_3114_ = v_isSharedCheck_3120_;
goto v_resetjp_3112_;
}
v_resetjp_3112_:
{
lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3118_; 
v___x_3115_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__7);
v___x_3116_ = lean_string_append(v___x_3115_, v_a_3111_);
lean_dec(v_a_3111_);
if (v_isShared_3114_ == 0)
{
lean_ctor_set(v___x_3113_, 0, v___x_3116_);
v___x_3118_ = v___x_3113_;
goto v_reusejp_3117_;
}
else
{
lean_object* v_reuseFailAlloc_3119_; 
v_reuseFailAlloc_3119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3119_, 0, v___x_3116_);
v___x_3118_ = v_reuseFailAlloc_3119_;
goto v_reusejp_3117_;
}
v_reusejp_3117_:
{
return v___x_3118_;
}
}
}
else
{
if (lean_obj_tag(v___x_3110_) == 0)
{
lean_object* v_a_3121_; lean_object* v___x_3123_; uint8_t v_isShared_3124_; uint8_t v_isSharedCheck_3128_; 
lean_dec(v_a_3108_);
v_a_3121_ = lean_ctor_get(v___x_3110_, 0);
v_isSharedCheck_3128_ = !lean_is_exclusive(v___x_3110_);
if (v_isSharedCheck_3128_ == 0)
{
v___x_3123_ = v___x_3110_;
v_isShared_3124_ = v_isSharedCheck_3128_;
goto v_resetjp_3122_;
}
else
{
lean_inc(v_a_3121_);
lean_dec(v___x_3110_);
v___x_3123_ = lean_box(0);
v_isShared_3124_ = v_isSharedCheck_3128_;
goto v_resetjp_3122_;
}
v_resetjp_3122_:
{
lean_object* v___x_3126_; 
if (v_isShared_3124_ == 0)
{
lean_ctor_set_tag(v___x_3123_, 0);
v___x_3126_ = v___x_3123_;
goto v_reusejp_3125_;
}
else
{
lean_object* v_reuseFailAlloc_3127_; 
v_reuseFailAlloc_3127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3127_, 0, v_a_3121_);
v___x_3126_ = v_reuseFailAlloc_3127_;
goto v_reusejp_3125_;
}
v_reusejp_3125_:
{
return v___x_3126_;
}
}
}
else
{
lean_object* v_a_3129_; lean_object* v___x_3131_; uint8_t v_isShared_3132_; uint8_t v_isSharedCheck_3138_; 
v_a_3129_ = lean_ctor_get(v___x_3110_, 0);
v_isSharedCheck_3138_ = !lean_is_exclusive(v___x_3110_);
if (v_isSharedCheck_3138_ == 0)
{
v___x_3131_ = v___x_3110_;
v_isShared_3132_ = v_isSharedCheck_3138_;
goto v_resetjp_3130_;
}
else
{
lean_inc(v_a_3129_);
lean_dec(v___x_3110_);
v___x_3131_ = lean_box(0);
v_isShared_3132_ = v_isSharedCheck_3138_;
goto v_resetjp_3130_;
}
v_resetjp_3130_:
{
lean_object* v___x_3133_; uint64_t v___x_3134_; lean_object* v___x_3136_; 
v___x_3133_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3133_, 0, v_a_3108_);
v___x_3134_ = lean_unbox_uint64(v_a_3129_);
lean_dec(v_a_3129_);
lean_ctor_set_uint64(v___x_3133_, sizeof(void*)*1, v___x_3134_);
if (v_isShared_3132_ == 0)
{
lean_ctor_set(v___x_3131_, 0, v___x_3133_);
v___x_3136_ = v___x_3131_;
goto v_reusejp_3135_;
}
else
{
lean_object* v_reuseFailAlloc_3137_; 
v_reuseFailAlloc_3137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3137_, 0, v___x_3133_);
v___x_3136_ = v_reuseFailAlloc_3137_;
goto v_reusejp_3135_;
}
v_reusejp_3135_:
{
return v___x_3136_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRpcKeepAliveParams_toJson(lean_object* v_x_3141_){
_start:
{
lean_object* v_uri_3142_; uint64_t v_sessionId_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; 
v_uri_3142_ = lean_ctor_get(v_x_3141_, 0);
v_sessionId_3143_ = lean_ctor_get_uint64(v_x_3141_, sizeof(void*)*1);
v___x_3144_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__0));
lean_inc_ref(v_uri_3142_);
v___x_3145_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3145_, 0, v_uri_3142_);
v___x_3146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3146_, 0, v___x_3144_);
lean_ctor_set(v___x_3146_, 1, v___x_3145_);
v___x_3147_ = lean_box(0);
v___x_3148_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3148_, 0, v___x_3146_);
lean_ctor_set(v___x_3148_, 1, v___x_3147_);
v___x_3149_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__0));
v___x_3150_ = lean_uint64_to_nat(v_sessionId_3143_);
v___x_3151_ = l_Lean_bignumToJson(v___x_3150_);
v___x_3152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3152_, 0, v___x_3149_);
lean_ctor_set(v___x_3152_, 1, v___x_3151_);
v___x_3153_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3153_, 0, v___x_3152_);
lean_ctor_set(v___x_3153_, 1, v___x_3147_);
v___x_3154_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3154_, 0, v___x_3153_);
lean_ctor_set(v___x_3154_, 1, v___x_3147_);
v___x_3155_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3155_, 0, v___x_3148_);
lean_ctor_set(v___x_3155_, 1, v___x_3154_);
v___x_3156_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0));
v___x_3157_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_3155_, v___x_3156_);
v___x_3158_ = l_Lean_Json_mkObj(v___x_3157_);
lean_dec(v___x_3157_);
return v___x_3158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRpcKeepAliveParams_toJson___boxed(lean_object* v_x_3159_){
_start:
{
lean_object* v_res_3160_; 
v_res_3160_ = l_Lean_Lsp_instToJsonRpcKeepAliveParams_toJson(v_x_3159_);
lean_dec_ref(v_x_3159_);
return v_res_3160_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Lsp_instReprLineRange_repr_spec__0(lean_object* v_a_3167_){
_start:
{
lean_object* v___x_3168_; 
v___x_3168_ = lean_nat_to_int(v_a_3167_);
return v___x_3168_;
}
}
static lean_object* _init_l_Lean_Lsp_instReprLineRange_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_3182_; lean_object* v___x_3183_; 
v___x_3182_ = lean_unsigned_to_nat(9u);
v___x_3183_ = lean_nat_to_int(v___x_3182_);
return v___x_3183_;
}
}
static lean_object* _init_l_Lean_Lsp_instReprLineRange_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_3190_; lean_object* v___x_3191_; 
v___x_3190_ = lean_unsigned_to_nat(7u);
v___x_3191_ = lean_nat_to_int(v___x_3190_);
return v___x_3191_;
}
}
static lean_object* _init_l_Lean_Lsp_instReprLineRange_repr___redArg___closed__14(void){
_start:
{
lean_object* v___x_3193_; lean_object* v___x_3194_; 
v___x_3193_ = ((lean_object*)(l_Lean_Lsp_instReprLineRange_repr___redArg___closed__0));
v___x_3194_ = lean_string_length(v___x_3193_);
return v___x_3194_;
}
}
static lean_object* _init_l_Lean_Lsp_instReprLineRange_repr___redArg___closed__15(void){
_start:
{
lean_object* v___x_3195_; lean_object* v___x_3196_; 
v___x_3195_ = lean_obj_once(&l_Lean_Lsp_instReprLineRange_repr___redArg___closed__14, &l_Lean_Lsp_instReprLineRange_repr___redArg___closed__14_once, _init_l_Lean_Lsp_instReprLineRange_repr___redArg___closed__14);
v___x_3196_ = lean_nat_to_int(v___x_3195_);
return v___x_3196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instReprLineRange_repr___redArg(lean_object* v_x_3201_){
_start:
{
lean_object* v_start_3202_; lean_object* v_end_3203_; lean_object* v___x_3205_; uint8_t v_isShared_3206_; uint8_t v_isSharedCheck_3238_; 
v_start_3202_ = lean_ctor_get(v_x_3201_, 0);
v_end_3203_ = lean_ctor_get(v_x_3201_, 1);
v_isSharedCheck_3238_ = !lean_is_exclusive(v_x_3201_);
if (v_isSharedCheck_3238_ == 0)
{
v___x_3205_ = v_x_3201_;
v_isShared_3206_ = v_isSharedCheck_3238_;
goto v_resetjp_3204_;
}
else
{
lean_inc(v_end_3203_);
lean_inc(v_start_3202_);
lean_dec(v_x_3201_);
v___x_3205_ = lean_box(0);
v_isShared_3206_ = v_isSharedCheck_3238_;
goto v_resetjp_3204_;
}
v_resetjp_3204_:
{
lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3213_; 
v___x_3207_ = ((lean_object*)(l_Lean_Lsp_instReprLineRange_repr___redArg___closed__5));
v___x_3208_ = ((lean_object*)(l_Lean_Lsp_instReprLineRange_repr___redArg___closed__6));
v___x_3209_ = lean_obj_once(&l_Lean_Lsp_instReprLineRange_repr___redArg___closed__7, &l_Lean_Lsp_instReprLineRange_repr___redArg___closed__7_once, _init_l_Lean_Lsp_instReprLineRange_repr___redArg___closed__7);
v___x_3210_ = l_Nat_reprFast(v_start_3202_);
v___x_3211_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3211_, 0, v___x_3210_);
if (v_isShared_3206_ == 0)
{
lean_ctor_set_tag(v___x_3205_, 4);
lean_ctor_set(v___x_3205_, 1, v___x_3211_);
lean_ctor_set(v___x_3205_, 0, v___x_3209_);
v___x_3213_ = v___x_3205_;
goto v_reusejp_3212_;
}
else
{
lean_object* v_reuseFailAlloc_3237_; 
v_reuseFailAlloc_3237_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3237_, 0, v___x_3209_);
lean_ctor_set(v_reuseFailAlloc_3237_, 1, v___x_3211_);
v___x_3213_ = v_reuseFailAlloc_3237_;
goto v_reusejp_3212_;
}
v_reusejp_3212_:
{
uint8_t v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; 
v___x_3214_ = 0;
v___x_3215_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3215_, 0, v___x_3213_);
lean_ctor_set_uint8(v___x_3215_, sizeof(void*)*1, v___x_3214_);
v___x_3216_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3216_, 0, v___x_3208_);
lean_ctor_set(v___x_3216_, 1, v___x_3215_);
v___x_3217_ = ((lean_object*)(l_Lean_Lsp_instReprLineRange_repr___redArg___closed__9));
v___x_3218_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3218_, 0, v___x_3216_);
lean_ctor_set(v___x_3218_, 1, v___x_3217_);
v___x_3219_ = lean_box(1);
v___x_3220_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3220_, 0, v___x_3218_);
lean_ctor_set(v___x_3220_, 1, v___x_3219_);
v___x_3221_ = ((lean_object*)(l_Lean_Lsp_instReprLineRange_repr___redArg___closed__11));
v___x_3222_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3222_, 0, v___x_3220_);
lean_ctor_set(v___x_3222_, 1, v___x_3221_);
v___x_3223_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3223_, 0, v___x_3222_);
lean_ctor_set(v___x_3223_, 1, v___x_3207_);
v___x_3224_ = lean_obj_once(&l_Lean_Lsp_instReprLineRange_repr___redArg___closed__12, &l_Lean_Lsp_instReprLineRange_repr___redArg___closed__12_once, _init_l_Lean_Lsp_instReprLineRange_repr___redArg___closed__12);
v___x_3225_ = l_Nat_reprFast(v_end_3203_);
v___x_3226_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3226_, 0, v___x_3225_);
v___x_3227_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3227_, 0, v___x_3224_);
lean_ctor_set(v___x_3227_, 1, v___x_3226_);
v___x_3228_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3228_, 0, v___x_3227_);
lean_ctor_set_uint8(v___x_3228_, sizeof(void*)*1, v___x_3214_);
v___x_3229_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3229_, 0, v___x_3223_);
lean_ctor_set(v___x_3229_, 1, v___x_3228_);
v___x_3230_ = lean_obj_once(&l_Lean_Lsp_instReprLineRange_repr___redArg___closed__15, &l_Lean_Lsp_instReprLineRange_repr___redArg___closed__15_once, _init_l_Lean_Lsp_instReprLineRange_repr___redArg___closed__15);
v___x_3231_ = ((lean_object*)(l_Lean_Lsp_instReprLineRange_repr___redArg___closed__16));
v___x_3232_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3232_, 0, v___x_3231_);
lean_ctor_set(v___x_3232_, 1, v___x_3229_);
v___x_3233_ = ((lean_object*)(l_Lean_Lsp_instReprLineRange_repr___redArg___closed__17));
v___x_3234_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3234_, 0, v___x_3232_);
lean_ctor_set(v___x_3234_, 1, v___x_3233_);
v___x_3235_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3235_, 0, v___x_3230_);
lean_ctor_set(v___x_3235_, 1, v___x_3234_);
v___x_3236_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3236_, 0, v___x_3235_);
lean_ctor_set_uint8(v___x_3236_, sizeof(void*)*1, v___x_3214_);
return v___x_3236_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instReprLineRange_repr(lean_object* v_x_3239_, lean_object* v_prec_3240_){
_start:
{
lean_object* v___x_3241_; 
v___x_3241_ = l_Lean_Lsp_instReprLineRange_repr___redArg(v_x_3239_);
return v___x_3241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instReprLineRange_repr___boxed(lean_object* v_x_3242_, lean_object* v_prec_3243_){
_start:
{
lean_object* v_res_3244_; 
v_res_3244_ = l_Lean_Lsp_instReprLineRange_repr(v_x_3242_, v_prec_3243_);
lean_dec(v_prec_3243_);
return v_res_3244_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__2(void){
_start:
{
uint8_t v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; 
v___x_3252_ = 1;
v___x_3253_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__1));
v___x_3254_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3253_, v___x_3252_);
return v___x_3254_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__3(void){
_start:
{
lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; 
v___x_3255_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6));
v___x_3256_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__2, &l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__2);
v___x_3257_ = lean_string_append(v___x_3256_, v___x_3255_);
return v___x_3257_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__5(void){
_start:
{
uint8_t v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; 
v___x_3260_ = 1;
v___x_3261_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__4));
v___x_3262_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3261_, v___x_3260_);
return v___x_3262_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__6(void){
_start:
{
lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; 
v___x_3263_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__5, &l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__5);
v___x_3264_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__3);
v___x_3265_ = lean_string_append(v___x_3264_, v___x_3263_);
return v___x_3265_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__7(void){
_start:
{
lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; 
v___x_3266_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_3267_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__6);
v___x_3268_ = lean_string_append(v___x_3267_, v___x_3266_);
return v___x_3268_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__9(void){
_start:
{
uint8_t v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; 
v___x_3271_ = 1;
v___x_3272_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__8));
v___x_3273_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3272_, v___x_3271_);
return v___x_3273_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__10(void){
_start:
{
lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; 
v___x_3274_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__9, &l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__9);
v___x_3275_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__3);
v___x_3276_ = lean_string_append(v___x_3275_, v___x_3274_);
return v___x_3276_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__11(void){
_start:
{
lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; 
v___x_3277_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_3278_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__10, &l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__10);
v___x_3279_ = lean_string_append(v___x_3278_, v___x_3277_);
return v___x_3279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLineRange_fromJson(lean_object* v_json_3280_){
_start:
{
lean_object* v___x_3281_; lean_object* v___x_3282_; 
v___x_3281_ = ((lean_object*)(l_Lean_Lsp_instReprLineRange_repr___redArg___closed__1));
lean_inc(v_json_3280_);
v___x_3282_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson_spec__1(v_json_3280_, v___x_3281_);
if (lean_obj_tag(v___x_3282_) == 0)
{
lean_object* v_a_3283_; lean_object* v___x_3285_; uint8_t v_isShared_3286_; uint8_t v_isSharedCheck_3292_; 
lean_dec(v_json_3280_);
v_a_3283_ = lean_ctor_get(v___x_3282_, 0);
v_isSharedCheck_3292_ = !lean_is_exclusive(v___x_3282_);
if (v_isSharedCheck_3292_ == 0)
{
v___x_3285_ = v___x_3282_;
v_isShared_3286_ = v_isSharedCheck_3292_;
goto v_resetjp_3284_;
}
else
{
lean_inc(v_a_3283_);
lean_dec(v___x_3282_);
v___x_3285_ = lean_box(0);
v_isShared_3286_ = v_isSharedCheck_3292_;
goto v_resetjp_3284_;
}
v_resetjp_3284_:
{
lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3290_; 
v___x_3287_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__7);
v___x_3288_ = lean_string_append(v___x_3287_, v_a_3283_);
lean_dec(v_a_3283_);
if (v_isShared_3286_ == 0)
{
lean_ctor_set(v___x_3285_, 0, v___x_3288_);
v___x_3290_ = v___x_3285_;
goto v_reusejp_3289_;
}
else
{
lean_object* v_reuseFailAlloc_3291_; 
v_reuseFailAlloc_3291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3291_, 0, v___x_3288_);
v___x_3290_ = v_reuseFailAlloc_3291_;
goto v_reusejp_3289_;
}
v_reusejp_3289_:
{
return v___x_3290_;
}
}
}
else
{
if (lean_obj_tag(v___x_3282_) == 0)
{
lean_object* v_a_3293_; lean_object* v___x_3295_; uint8_t v_isShared_3296_; uint8_t v_isSharedCheck_3300_; 
lean_dec(v_json_3280_);
v_a_3293_ = lean_ctor_get(v___x_3282_, 0);
v_isSharedCheck_3300_ = !lean_is_exclusive(v___x_3282_);
if (v_isSharedCheck_3300_ == 0)
{
v___x_3295_ = v___x_3282_;
v_isShared_3296_ = v_isSharedCheck_3300_;
goto v_resetjp_3294_;
}
else
{
lean_inc(v_a_3293_);
lean_dec(v___x_3282_);
v___x_3295_ = lean_box(0);
v_isShared_3296_ = v_isSharedCheck_3300_;
goto v_resetjp_3294_;
}
v_resetjp_3294_:
{
lean_object* v___x_3298_; 
if (v_isShared_3296_ == 0)
{
lean_ctor_set_tag(v___x_3295_, 0);
v___x_3298_ = v___x_3295_;
goto v_reusejp_3297_;
}
else
{
lean_object* v_reuseFailAlloc_3299_; 
v_reuseFailAlloc_3299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3299_, 0, v_a_3293_);
v___x_3298_ = v_reuseFailAlloc_3299_;
goto v_reusejp_3297_;
}
v_reusejp_3297_:
{
return v___x_3298_;
}
}
}
else
{
lean_object* v_a_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; 
v_a_3301_ = lean_ctor_get(v___x_3282_, 0);
lean_inc(v_a_3301_);
lean_dec_ref_known(v___x_3282_, 1);
v___x_3302_ = ((lean_object*)(l_Lean_Lsp_instReprLineRange_repr___redArg___closed__10));
v___x_3303_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson_spec__1(v_json_3280_, v___x_3302_);
if (lean_obj_tag(v___x_3303_) == 0)
{
lean_object* v_a_3304_; lean_object* v___x_3306_; uint8_t v_isShared_3307_; uint8_t v_isSharedCheck_3313_; 
lean_dec(v_a_3301_);
v_a_3304_ = lean_ctor_get(v___x_3303_, 0);
v_isSharedCheck_3313_ = !lean_is_exclusive(v___x_3303_);
if (v_isSharedCheck_3313_ == 0)
{
v___x_3306_ = v___x_3303_;
v_isShared_3307_ = v_isSharedCheck_3313_;
goto v_resetjp_3305_;
}
else
{
lean_inc(v_a_3304_);
lean_dec(v___x_3303_);
v___x_3306_ = lean_box(0);
v_isShared_3307_ = v_isSharedCheck_3313_;
goto v_resetjp_3305_;
}
v_resetjp_3305_:
{
lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3311_; 
v___x_3308_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__11, &l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__11);
v___x_3309_ = lean_string_append(v___x_3308_, v_a_3304_);
lean_dec(v_a_3304_);
if (v_isShared_3307_ == 0)
{
lean_ctor_set(v___x_3306_, 0, v___x_3309_);
v___x_3311_ = v___x_3306_;
goto v_reusejp_3310_;
}
else
{
lean_object* v_reuseFailAlloc_3312_; 
v_reuseFailAlloc_3312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3312_, 0, v___x_3309_);
v___x_3311_ = v_reuseFailAlloc_3312_;
goto v_reusejp_3310_;
}
v_reusejp_3310_:
{
return v___x_3311_;
}
}
}
else
{
if (lean_obj_tag(v___x_3303_) == 0)
{
lean_object* v_a_3314_; lean_object* v___x_3316_; uint8_t v_isShared_3317_; uint8_t v_isSharedCheck_3321_; 
lean_dec(v_a_3301_);
v_a_3314_ = lean_ctor_get(v___x_3303_, 0);
v_isSharedCheck_3321_ = !lean_is_exclusive(v___x_3303_);
if (v_isSharedCheck_3321_ == 0)
{
v___x_3316_ = v___x_3303_;
v_isShared_3317_ = v_isSharedCheck_3321_;
goto v_resetjp_3315_;
}
else
{
lean_inc(v_a_3314_);
lean_dec(v___x_3303_);
v___x_3316_ = lean_box(0);
v_isShared_3317_ = v_isSharedCheck_3321_;
goto v_resetjp_3315_;
}
v_resetjp_3315_:
{
lean_object* v___x_3319_; 
if (v_isShared_3317_ == 0)
{
lean_ctor_set_tag(v___x_3316_, 0);
v___x_3319_ = v___x_3316_;
goto v_reusejp_3318_;
}
else
{
lean_object* v_reuseFailAlloc_3320_; 
v_reuseFailAlloc_3320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3320_, 0, v_a_3314_);
v___x_3319_ = v_reuseFailAlloc_3320_;
goto v_reusejp_3318_;
}
v_reusejp_3318_:
{
return v___x_3319_;
}
}
}
else
{
lean_object* v_a_3322_; lean_object* v___x_3324_; uint8_t v_isShared_3325_; uint8_t v_isSharedCheck_3330_; 
v_a_3322_ = lean_ctor_get(v___x_3303_, 0);
v_isSharedCheck_3330_ = !lean_is_exclusive(v___x_3303_);
if (v_isSharedCheck_3330_ == 0)
{
v___x_3324_ = v___x_3303_;
v_isShared_3325_ = v_isSharedCheck_3330_;
goto v_resetjp_3323_;
}
else
{
lean_inc(v_a_3322_);
lean_dec(v___x_3303_);
v___x_3324_ = lean_box(0);
v_isShared_3325_ = v_isSharedCheck_3330_;
goto v_resetjp_3323_;
}
v_resetjp_3323_:
{
lean_object* v___x_3326_; lean_object* v___x_3328_; 
v___x_3326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3326_, 0, v_a_3301_);
lean_ctor_set(v___x_3326_, 1, v_a_3322_);
if (v_isShared_3325_ == 0)
{
lean_ctor_set(v___x_3324_, 0, v___x_3326_);
v___x_3328_ = v___x_3324_;
goto v_reusejp_3327_;
}
else
{
lean_object* v_reuseFailAlloc_3329_; 
v_reuseFailAlloc_3329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3329_, 0, v___x_3326_);
v___x_3328_ = v_reuseFailAlloc_3329_;
goto v_reusejp_3327_;
}
v_reusejp_3327_:
{
return v___x_3328_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLineRange_toJson(lean_object* v_x_3333_){
_start:
{
lean_object* v_start_3334_; lean_object* v_end_3335_; lean_object* v___x_3337_; uint8_t v_isShared_3338_; uint8_t v_isSharedCheck_3357_; 
v_start_3334_ = lean_ctor_get(v_x_3333_, 0);
v_end_3335_ = lean_ctor_get(v_x_3333_, 1);
v_isSharedCheck_3357_ = !lean_is_exclusive(v_x_3333_);
if (v_isSharedCheck_3357_ == 0)
{
v___x_3337_ = v_x_3333_;
v_isShared_3338_ = v_isSharedCheck_3357_;
goto v_resetjp_3336_;
}
else
{
lean_inc(v_end_3335_);
lean_inc(v_start_3334_);
lean_dec(v_x_3333_);
v___x_3337_ = lean_box(0);
v_isShared_3338_ = v_isSharedCheck_3357_;
goto v_resetjp_3336_;
}
v_resetjp_3336_:
{
lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3343_; 
v___x_3339_ = ((lean_object*)(l_Lean_Lsp_instReprLineRange_repr___redArg___closed__1));
v___x_3340_ = l_Lean_JsonNumber_fromNat(v_start_3334_);
v___x_3341_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3341_, 0, v___x_3340_);
if (v_isShared_3338_ == 0)
{
lean_ctor_set(v___x_3337_, 1, v___x_3341_);
lean_ctor_set(v___x_3337_, 0, v___x_3339_);
v___x_3343_ = v___x_3337_;
goto v_reusejp_3342_;
}
else
{
lean_object* v_reuseFailAlloc_3356_; 
v_reuseFailAlloc_3356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3356_, 0, v___x_3339_);
lean_ctor_set(v_reuseFailAlloc_3356_, 1, v___x_3341_);
v___x_3343_ = v_reuseFailAlloc_3356_;
goto v_reusejp_3342_;
}
v_reusejp_3342_:
{
lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; 
v___x_3344_ = lean_box(0);
v___x_3345_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3345_, 0, v___x_3343_);
lean_ctor_set(v___x_3345_, 1, v___x_3344_);
v___x_3346_ = ((lean_object*)(l_Lean_Lsp_instReprLineRange_repr___redArg___closed__10));
v___x_3347_ = l_Lean_JsonNumber_fromNat(v_end_3335_);
v___x_3348_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3348_, 0, v___x_3347_);
v___x_3349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3349_, 0, v___x_3346_);
lean_ctor_set(v___x_3349_, 1, v___x_3348_);
v___x_3350_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3350_, 0, v___x_3349_);
lean_ctor_set(v___x_3350_, 1, v___x_3344_);
v___x_3351_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3351_, 0, v___x_3350_);
lean_ctor_set(v___x_3351_, 1, v___x_3344_);
v___x_3352_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3352_, 0, v___x_3345_);
lean_ctor_set(v___x_3352_, 1, v___x_3351_);
v___x_3353_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0));
v___x_3354_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_3352_, v___x_3353_);
v___x_3355_ = l_Lean_Json_mkObj(v___x_3354_);
lean_dec(v___x_3354_);
return v___x_3355_;
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

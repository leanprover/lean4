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
lean_object* l_UInt64_fromJson_x3f(lean_object*);
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
lean_object* l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson(lean_object*);
lean_object* l_Lean_Lsp_instToJsonVersionedTextDocumentIdentifier_toJson(lean_object*);
lean_object* l_Lean_Lsp_instToJsonRpcWireFormat_toJson(uint8_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson(lean_object*);
lean_object* l_Lean_Lsp_instToJsonTextDocumentItem_toJson(lean_object*);
lean_object* l_Lean_Name_fromJson_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DependencyBuildMode_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Lsp_DependencyBuildMode_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DependencyBuildMode_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Lsp_DependencyBuildMode_toCtorIdx___boxed(lean_object*);
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
static const lean_ctor_object l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson_spec__1_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson_spec__1_spec__1___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson_spec__1_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson_spec__1_spec__1(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Lsp_WaitForDiagnostics_toCtorIdx(lean_object*);
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
static const lean_ctor_object l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForILeansParams_fromJson_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForILeansParams_fromJson_spec__0_spec__0___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForILeansParams_fromJson_spec__0_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForILeansParams_fromJson_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForILeansParams_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForILeansParams_fromJson_spec__0___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForILeansParams_fromJson_spec__1_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForILeansParams_fromJson_spec__1_spec__2___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForILeansParams_fromJson_spec__1_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForILeansParams_fromJson_spec__1_spec__2(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Lsp_WaitForILeans_toCtorIdx(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanFileProgressKind_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanFileProgressKind_toCtorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__1_spec__1_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__1_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "expected JSON array, got '"};
static const lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__1_spec__1___closed__0 = (const lean_object*)&l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__1_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__1_spec__1(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanFileProgressParams_toJson_spec__0_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanFileProgressParams_toJson_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Lsp_instToJsonLeanFileProgressParams_toJson_spec__0(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoal_fromJson_spec__0_spec__0_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoal_fromJson_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoal_fromJson_spec__0_spec__0(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonPlainGoal_toJson_spec__0_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonPlainGoal_toJson_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Lsp_instToJsonPlainGoal_toJson_spec__0(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Lsp_ModuleHierarchyOptions_toCtorIdx(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Lsp_HighlightMatchesOptions_toCtorIdx(lean_object*);
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
static const lean_ctor_object l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__1_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__1_spec__2___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__1_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__1_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__1___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__0_spec__0___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__0_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__0_spec__0___boxed(lean_object*);
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
static const lean_ctor_object l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModule_fromJson_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModule_fromJson_spec__0_spec__0___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModule_fromJson_spec__0_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModule_fromJson_spec__0_spec__0(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanImportMetaKind_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanImportMetaKind_toCtorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcReleaseParams_fromJson_spec__0_spec__0_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcReleaseParams_fromJson_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcReleaseParams_fromJson_spec__0_spec__0(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonRpcReleaseParams_toJson_spec__0_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonRpcReleaseParams_toJson_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Lsp_instToJsonRpcReleaseParams_toJson_spec__0(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Lsp_DependencyBuildMode_toCtorIdx(uint8_t v_x_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = l_Lean_Lsp_DependencyBuildMode_ctorIdx(v_x_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DependencyBuildMode_toCtorIdx___boxed(lean_object* v_x_10_){
_start:
{
uint8_t v_x_4__boxed_11_; lean_object* v_res_12_; 
v_x_4__boxed_11_ = lean_unbox(v_x_10_);
v_res_12_ = l_Lean_Lsp_DependencyBuildMode_toCtorIdx(v_x_4__boxed_11_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DependencyBuildMode_ctorElim___redArg(lean_object* v_k_13_){
_start:
{
lean_inc(v_k_13_);
return v_k_13_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DependencyBuildMode_ctorElim___redArg___boxed(lean_object* v_k_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = l_Lean_Lsp_DependencyBuildMode_ctorElim___redArg(v_k_14_);
lean_dec(v_k_14_);
return v_res_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DependencyBuildMode_ctorElim(lean_object* v_motive_16_, lean_object* v_ctorIdx_17_, uint8_t v_t_18_, lean_object* v_h_19_, lean_object* v_k_20_){
_start:
{
lean_inc(v_k_20_);
return v_k_20_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DependencyBuildMode_ctorElim___boxed(lean_object* v_motive_21_, lean_object* v_ctorIdx_22_, lean_object* v_t_23_, lean_object* v_h_24_, lean_object* v_k_25_){
_start:
{
uint8_t v_t_boxed_26_; lean_object* v_res_27_; 
v_t_boxed_26_ = lean_unbox(v_t_23_);
v_res_27_ = l_Lean_Lsp_DependencyBuildMode_ctorElim(v_motive_21_, v_ctorIdx_22_, v_t_boxed_26_, v_h_24_, v_k_25_);
lean_dec(v_k_25_);
lean_dec(v_ctorIdx_22_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DependencyBuildMode_always_elim___redArg(lean_object* v_always_28_){
_start:
{
lean_inc(v_always_28_);
return v_always_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DependencyBuildMode_always_elim___redArg___boxed(lean_object* v_always_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_Lsp_DependencyBuildMode_always_elim___redArg(v_always_29_);
lean_dec(v_always_29_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DependencyBuildMode_always_elim(lean_object* v_motive_31_, uint8_t v_t_32_, lean_object* v_h_33_, lean_object* v_always_34_){
_start:
{
lean_inc(v_always_34_);
return v_always_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DependencyBuildMode_always_elim___boxed(lean_object* v_motive_35_, lean_object* v_t_36_, lean_object* v_h_37_, lean_object* v_always_38_){
_start:
{
uint8_t v_t_boxed_39_; lean_object* v_res_40_; 
v_t_boxed_39_ = lean_unbox(v_t_36_);
v_res_40_ = l_Lean_Lsp_DependencyBuildMode_always_elim(v_motive_35_, v_t_boxed_39_, v_h_37_, v_always_38_);
lean_dec(v_always_38_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DependencyBuildMode_once_elim___redArg(lean_object* v_once_41_){
_start:
{
lean_inc(v_once_41_);
return v_once_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DependencyBuildMode_once_elim___redArg___boxed(lean_object* v_once_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l_Lean_Lsp_DependencyBuildMode_once_elim___redArg(v_once_42_);
lean_dec(v_once_42_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DependencyBuildMode_once_elim(lean_object* v_motive_44_, uint8_t v_t_45_, lean_object* v_h_46_, lean_object* v_once_47_){
_start:
{
lean_inc(v_once_47_);
return v_once_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DependencyBuildMode_once_elim___boxed(lean_object* v_motive_48_, lean_object* v_t_49_, lean_object* v_h_50_, lean_object* v_once_51_){
_start:
{
uint8_t v_t_boxed_52_; lean_object* v_res_53_; 
v_t_boxed_52_ = lean_unbox(v_t_49_);
v_res_53_ = l_Lean_Lsp_DependencyBuildMode_once_elim(v_motive_48_, v_t_boxed_52_, v_h_50_, v_once_51_);
lean_dec(v_once_51_);
return v_res_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DependencyBuildMode_never_elim___redArg(lean_object* v_never_54_){
_start:
{
lean_inc(v_never_54_);
return v_never_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DependencyBuildMode_never_elim___redArg___boxed(lean_object* v_never_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_Lean_Lsp_DependencyBuildMode_never_elim___redArg(v_never_55_);
lean_dec(v_never_55_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DependencyBuildMode_never_elim(lean_object* v_motive_57_, uint8_t v_t_58_, lean_object* v_h_59_, lean_object* v_never_60_){
_start:
{
lean_inc(v_never_60_);
return v_never_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DependencyBuildMode_never_elim___boxed(lean_object* v_motive_61_, lean_object* v_t_62_, lean_object* v_h_63_, lean_object* v_never_64_){
_start:
{
uint8_t v_t_boxed_65_; lean_object* v_res_66_; 
v_t_boxed_65_ = lean_unbox(v_t_62_);
v_res_66_ = l_Lean_Lsp_DependencyBuildMode_never_elim(v_motive_61_, v_t_boxed_65_, v_h_63_, v_never_64_);
lean_dec(v_never_64_);
return v_res_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson(lean_object* v_json_85_){
_start:
{
lean_object* v___x_86_; 
v___x_86_ = l_Lean_Json_getTag_x3f(v_json_85_);
if (lean_obj_tag(v___x_86_) == 0)
{
lean_object* v___x_87_; 
v___x_87_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__1));
return v___x_87_;
}
else
{
lean_object* v_val_88_; lean_object* v___x_89_; uint8_t v___x_90_; 
v_val_88_ = lean_ctor_get(v___x_86_, 0);
lean_inc(v_val_88_);
lean_dec_ref(v___x_86_);
v___x_89_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__2));
v___x_90_ = lean_string_dec_eq(v_val_88_, v___x_89_);
if (v___x_90_ == 0)
{
lean_object* v___x_91_; uint8_t v___x_92_; 
v___x_91_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__3));
v___x_92_ = lean_string_dec_eq(v_val_88_, v___x_91_);
if (v___x_92_ == 0)
{
lean_object* v___x_93_; uint8_t v___x_94_; 
v___x_93_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__4));
v___x_94_ = lean_string_dec_eq(v_val_88_, v___x_93_);
lean_dec(v_val_88_);
if (v___x_94_ == 0)
{
lean_object* v___x_95_; 
v___x_95_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__6));
return v___x_95_;
}
else
{
lean_object* v___x_96_; 
v___x_96_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__7));
return v___x_96_;
}
}
else
{
lean_object* v___x_97_; 
lean_dec(v_val_88_);
v___x_97_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__8));
return v___x_97_;
}
}
else
{
lean_object* v___x_98_; 
lean_dec(v_val_88_);
v___x_98_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__9));
return v___x_98_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDependencyBuildMode_toJson(uint8_t v_x_107_){
_start:
{
switch(v_x_107_)
{
case 0:
{
lean_object* v___x_108_; 
v___x_108_ = ((lean_object*)(l_Lean_Lsp_instToJsonDependencyBuildMode_toJson___closed__0));
return v___x_108_;
}
case 1:
{
lean_object* v___x_109_; 
v___x_109_ = ((lean_object*)(l_Lean_Lsp_instToJsonDependencyBuildMode_toJson___closed__1));
return v___x_109_;
}
default: 
{
lean_object* v___x_110_; 
v___x_110_ = ((lean_object*)(l_Lean_Lsp_instToJsonDependencyBuildMode_toJson___closed__2));
return v___x_110_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDependencyBuildMode_toJson___boxed(lean_object* v_x_111_){
_start:
{
uint8_t v_x_64__boxed_112_; lean_object* v_res_113_; 
v_x_64__boxed_112_ = lean_unbox(v_x_111_);
v_res_113_ = l_Lean_Lsp_instToJsonDependencyBuildMode_toJson(v_x_64__boxed_112_);
return v_res_113_;
}
}
static uint8_t _init_l_Lean_Lsp_instInhabitedDependencyBuildMode_default(void){
_start:
{
uint8_t v___x_116_; 
v___x_116_ = 0;
return v___x_116_;
}
}
static uint8_t _init_l_Lean_Lsp_instInhabitedDependencyBuildMode(void){
_start:
{
uint8_t v___x_117_; 
v___x_117_ = 0;
return v___x_117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson_spec__0(lean_object* v_j_118_, lean_object* v_k_119_){
_start:
{
lean_object* v___x_120_; lean_object* v___x_121_; 
v___x_120_ = l_Lean_Json_getObjValD(v_j_118_, v_k_119_);
v___x_121_ = l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson(v___x_120_);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson_spec__0___boxed(lean_object* v_j_122_, lean_object* v_k_123_){
_start:
{
lean_object* v_res_124_; 
v_res_124_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson_spec__0(v_j_122_, v_k_123_);
lean_dec_ref(v_k_123_);
return v_res_124_;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson_spec__1_spec__1(lean_object* v_x_127_){
_start:
{
if (lean_obj_tag(v_x_127_) == 0)
{
lean_object* v___x_128_; 
v___x_128_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson_spec__1_spec__1___closed__0));
return v___x_128_;
}
else
{
lean_object* v___x_129_; 
v___x_129_ = l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson(v_x_127_);
if (lean_obj_tag(v___x_129_) == 0)
{
lean_object* v_a_130_; lean_object* v___x_132_; uint8_t v_isShared_133_; uint8_t v_isSharedCheck_137_; 
v_a_130_ = lean_ctor_get(v___x_129_, 0);
v_isSharedCheck_137_ = !lean_is_exclusive(v___x_129_);
if (v_isSharedCheck_137_ == 0)
{
v___x_132_ = v___x_129_;
v_isShared_133_ = v_isSharedCheck_137_;
goto v_resetjp_131_;
}
else
{
lean_inc(v_a_130_);
lean_dec(v___x_129_);
v___x_132_ = lean_box(0);
v_isShared_133_ = v_isSharedCheck_137_;
goto v_resetjp_131_;
}
v_resetjp_131_:
{
lean_object* v___x_135_; 
if (v_isShared_133_ == 0)
{
v___x_135_ = v___x_132_;
goto v_reusejp_134_;
}
else
{
lean_object* v_reuseFailAlloc_136_; 
v_reuseFailAlloc_136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_136_, 0, v_a_130_);
v___x_135_ = v_reuseFailAlloc_136_;
goto v_reusejp_134_;
}
v_reusejp_134_:
{
return v___x_135_;
}
}
}
else
{
lean_object* v_a_138_; lean_object* v___x_140_; uint8_t v_isShared_141_; uint8_t v_isSharedCheck_146_; 
v_a_138_ = lean_ctor_get(v___x_129_, 0);
v_isSharedCheck_146_ = !lean_is_exclusive(v___x_129_);
if (v_isSharedCheck_146_ == 0)
{
v___x_140_ = v___x_129_;
v_isShared_141_ = v_isSharedCheck_146_;
goto v_resetjp_139_;
}
else
{
lean_inc(v_a_138_);
lean_dec(v___x_129_);
v___x_140_ = lean_box(0);
v_isShared_141_ = v_isSharedCheck_146_;
goto v_resetjp_139_;
}
v_resetjp_139_:
{
lean_object* v___x_142_; lean_object* v___x_144_; 
v___x_142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_142_, 0, v_a_138_);
if (v_isShared_141_ == 0)
{
lean_ctor_set(v___x_140_, 0, v___x_142_);
v___x_144_ = v___x_140_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v___x_142_);
v___x_144_ = v_reuseFailAlloc_145_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
return v___x_144_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson_spec__1(lean_object* v_j_147_, lean_object* v_k_148_){
_start:
{
lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_149_ = l_Lean_Json_getObjValD(v_j_147_, v_k_148_);
v___x_150_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson_spec__1_spec__1(v___x_149_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson_spec__1___boxed(lean_object* v_j_151_, lean_object* v_k_152_){
_start:
{
lean_object* v_res_153_; 
v_res_153_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson_spec__1(v_j_151_, v_k_152_);
lean_dec_ref(v_k_152_);
return v_res_153_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__5(void){
_start:
{
uint8_t v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_162_ = 1;
v___x_163_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__4));
v___x_164_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_163_, v___x_162_);
return v___x_164_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__7(void){
_start:
{
lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_166_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6));
v___x_167_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__5, &l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__5);
v___x_168_ = lean_string_append(v___x_167_, v___x_166_);
return v___x_168_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9(void){
_start:
{
uint8_t v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_171_ = 1;
v___x_172_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__8));
v___x_173_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_172_, v___x_171_);
return v___x_173_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__10(void){
_start:
{
lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_174_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9, &l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9);
v___x_175_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__7);
v___x_176_ = lean_string_append(v___x_175_, v___x_174_);
return v___x_176_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__12(void){
_start:
{
lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_178_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_179_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__10, &l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__10);
v___x_180_ = lean_string_append(v___x_179_, v___x_178_);
return v___x_180_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__16(void){
_start:
{
uint8_t v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; 
v___x_185_ = 1;
v___x_186_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__15));
v___x_187_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_186_, v___x_185_);
return v___x_187_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__17(void){
_start:
{
lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; 
v___x_188_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__16, &l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__16_once, _init_l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__16);
v___x_189_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__7);
v___x_190_ = lean_string_append(v___x_189_, v___x_188_);
return v___x_190_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__18(void){
_start:
{
lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; 
v___x_191_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_192_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__17, &l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__17_once, _init_l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__17);
v___x_193_ = lean_string_append(v___x_192_, v___x_191_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson(lean_object* v_json_194_){
_start:
{
lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_195_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__0));
lean_inc(v_json_194_);
v___x_196_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson_spec__0(v_json_194_, v___x_195_);
if (lean_obj_tag(v___x_196_) == 0)
{
lean_object* v_a_197_; lean_object* v___x_199_; uint8_t v_isShared_200_; uint8_t v_isSharedCheck_206_; 
lean_dec(v_json_194_);
v_a_197_ = lean_ctor_get(v___x_196_, 0);
v_isSharedCheck_206_ = !lean_is_exclusive(v___x_196_);
if (v_isSharedCheck_206_ == 0)
{
v___x_199_ = v___x_196_;
v_isShared_200_ = v_isSharedCheck_206_;
goto v_resetjp_198_;
}
else
{
lean_inc(v_a_197_);
lean_dec(v___x_196_);
v___x_199_ = lean_box(0);
v_isShared_200_ = v_isSharedCheck_206_;
goto v_resetjp_198_;
}
v_resetjp_198_:
{
lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_204_; 
v___x_201_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__12, &l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__12);
v___x_202_ = lean_string_append(v___x_201_, v_a_197_);
lean_dec(v_a_197_);
if (v_isShared_200_ == 0)
{
lean_ctor_set(v___x_199_, 0, v___x_202_);
v___x_204_ = v___x_199_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v___x_202_);
v___x_204_ = v_reuseFailAlloc_205_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
return v___x_204_;
}
}
}
else
{
if (lean_obj_tag(v___x_196_) == 0)
{
lean_object* v_a_207_; lean_object* v___x_209_; uint8_t v_isShared_210_; uint8_t v_isSharedCheck_214_; 
lean_dec(v_json_194_);
v_a_207_ = lean_ctor_get(v___x_196_, 0);
v_isSharedCheck_214_ = !lean_is_exclusive(v___x_196_);
if (v_isSharedCheck_214_ == 0)
{
v___x_209_ = v___x_196_;
v_isShared_210_ = v_isSharedCheck_214_;
goto v_resetjp_208_;
}
else
{
lean_inc(v_a_207_);
lean_dec(v___x_196_);
v___x_209_ = lean_box(0);
v_isShared_210_ = v_isSharedCheck_214_;
goto v_resetjp_208_;
}
v_resetjp_208_:
{
lean_object* v___x_212_; 
if (v_isShared_210_ == 0)
{
lean_ctor_set_tag(v___x_209_, 0);
v___x_212_ = v___x_209_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_213_; 
v_reuseFailAlloc_213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_213_, 0, v_a_207_);
v___x_212_ = v_reuseFailAlloc_213_;
goto v_reusejp_211_;
}
v_reusejp_211_:
{
return v___x_212_;
}
}
}
else
{
lean_object* v_a_215_; lean_object* v___x_216_; lean_object* v___x_217_; 
v_a_215_ = lean_ctor_get(v___x_196_, 0);
lean_inc(v_a_215_);
lean_dec_ref(v___x_196_);
v___x_216_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__13));
v___x_217_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson_spec__1(v_json_194_, v___x_216_);
if (lean_obj_tag(v___x_217_) == 0)
{
lean_object* v_a_218_; lean_object* v___x_220_; uint8_t v_isShared_221_; uint8_t v_isSharedCheck_227_; 
lean_dec(v_a_215_);
v_a_218_ = lean_ctor_get(v___x_217_, 0);
v_isSharedCheck_227_ = !lean_is_exclusive(v___x_217_);
if (v_isSharedCheck_227_ == 0)
{
v___x_220_ = v___x_217_;
v_isShared_221_ = v_isSharedCheck_227_;
goto v_resetjp_219_;
}
else
{
lean_inc(v_a_218_);
lean_dec(v___x_217_);
v___x_220_ = lean_box(0);
v_isShared_221_ = v_isSharedCheck_227_;
goto v_resetjp_219_;
}
v_resetjp_219_:
{
lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_225_; 
v___x_222_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__18, &l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__18_once, _init_l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__18);
v___x_223_ = lean_string_append(v___x_222_, v_a_218_);
lean_dec(v_a_218_);
if (v_isShared_221_ == 0)
{
lean_ctor_set(v___x_220_, 0, v___x_223_);
v___x_225_ = v___x_220_;
goto v_reusejp_224_;
}
else
{
lean_object* v_reuseFailAlloc_226_; 
v_reuseFailAlloc_226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_226_, 0, v___x_223_);
v___x_225_ = v_reuseFailAlloc_226_;
goto v_reusejp_224_;
}
v_reusejp_224_:
{
return v___x_225_;
}
}
}
else
{
if (lean_obj_tag(v___x_217_) == 0)
{
lean_object* v_a_228_; lean_object* v___x_230_; uint8_t v_isShared_231_; uint8_t v_isSharedCheck_235_; 
lean_dec(v_a_215_);
v_a_228_ = lean_ctor_get(v___x_217_, 0);
v_isSharedCheck_235_ = !lean_is_exclusive(v___x_217_);
if (v_isSharedCheck_235_ == 0)
{
v___x_230_ = v___x_217_;
v_isShared_231_ = v_isSharedCheck_235_;
goto v_resetjp_229_;
}
else
{
lean_inc(v_a_228_);
lean_dec(v___x_217_);
v___x_230_ = lean_box(0);
v_isShared_231_ = v_isSharedCheck_235_;
goto v_resetjp_229_;
}
v_resetjp_229_:
{
lean_object* v___x_233_; 
if (v_isShared_231_ == 0)
{
lean_ctor_set_tag(v___x_230_, 0);
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
lean_object* v_a_236_; lean_object* v___x_238_; uint8_t v_isShared_239_; uint8_t v_isSharedCheck_244_; 
v_a_236_ = lean_ctor_get(v___x_217_, 0);
v_isSharedCheck_244_ = !lean_is_exclusive(v___x_217_);
if (v_isSharedCheck_244_ == 0)
{
v___x_238_ = v___x_217_;
v_isShared_239_ = v_isSharedCheck_244_;
goto v_resetjp_237_;
}
else
{
lean_inc(v_a_236_);
lean_dec(v___x_217_);
v___x_238_ = lean_box(0);
v_isShared_239_ = v_isSharedCheck_244_;
goto v_resetjp_237_;
}
v_resetjp_237_:
{
lean_object* v___x_240_; lean_object* v___x_242_; 
v___x_240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_240_, 0, v_a_215_);
lean_ctor_set(v___x_240_, 1, v_a_236_);
if (v_isShared_239_ == 0)
{
lean_ctor_set(v___x_238_, 0, v___x_240_);
v___x_242_ = v___x_238_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v___x_240_);
v___x_242_ = v_reuseFailAlloc_243_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
return v___x_242_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__0(lean_object* v_k_247_, lean_object* v_x_248_){
_start:
{
if (lean_obj_tag(v_x_248_) == 0)
{
lean_object* v___x_249_; 
lean_dec_ref(v_k_247_);
v___x_249_ = lean_box(0);
return v___x_249_;
}
else
{
lean_object* v_val_250_; uint8_t v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; 
v_val_250_ = lean_ctor_get(v_x_248_, 0);
v___x_251_ = lean_unbox(v_val_250_);
v___x_252_ = l_Lean_Lsp_instToJsonDependencyBuildMode_toJson(v___x_251_);
v___x_253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_253_, 0, v_k_247_);
lean_ctor_set(v___x_253_, 1, v___x_252_);
v___x_254_ = lean_box(0);
v___x_255_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_255_, 0, v___x_253_);
lean_ctor_set(v___x_255_, 1, v___x_254_);
return v___x_255_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__0___boxed(lean_object* v_k_256_, lean_object* v_x_257_){
_start:
{
lean_object* v_res_258_; 
v_res_258_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__0(v_k_256_, v_x_257_);
lean_dec(v_x_257_);
return v_res_258_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(lean_object* v_a_259_, lean_object* v_a_260_){
_start:
{
if (lean_obj_tag(v_a_259_) == 0)
{
lean_object* v___x_261_; 
v___x_261_ = lean_array_to_list(v_a_260_);
return v___x_261_;
}
else
{
lean_object* v_head_262_; lean_object* v_tail_263_; lean_object* v___x_264_; 
v_head_262_ = lean_ctor_get(v_a_259_, 0);
lean_inc(v_head_262_);
v_tail_263_ = lean_ctor_get(v_a_259_, 1);
lean_inc(v_tail_263_);
lean_dec_ref(v_a_259_);
v___x_264_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_260_, v_head_262_);
v_a_259_ = v_tail_263_;
v_a_260_ = v___x_264_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson(lean_object* v_x_268_){
_start:
{
lean_object* v_toDidOpenTextDocumentParams_269_; lean_object* v_dependencyBuildMode_x3f_270_; lean_object* v___x_272_; uint8_t v_isShared_273_; uint8_t v_isSharedCheck_288_; 
v_toDidOpenTextDocumentParams_269_ = lean_ctor_get(v_x_268_, 0);
v_dependencyBuildMode_x3f_270_ = lean_ctor_get(v_x_268_, 1);
v_isSharedCheck_288_ = !lean_is_exclusive(v_x_268_);
if (v_isSharedCheck_288_ == 0)
{
v___x_272_ = v_x_268_;
v_isShared_273_ = v_isSharedCheck_288_;
goto v_resetjp_271_;
}
else
{
lean_inc(v_dependencyBuildMode_x3f_270_);
lean_inc(v_toDidOpenTextDocumentParams_269_);
lean_dec(v_x_268_);
v___x_272_ = lean_box(0);
v_isShared_273_ = v_isSharedCheck_288_;
goto v_resetjp_271_;
}
v_resetjp_271_:
{
lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_277_; 
v___x_274_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__0));
v___x_275_ = l_Lean_Lsp_instToJsonTextDocumentItem_toJson(v_toDidOpenTextDocumentParams_269_);
if (v_isShared_273_ == 0)
{
lean_ctor_set(v___x_272_, 1, v___x_275_);
lean_ctor_set(v___x_272_, 0, v___x_274_);
v___x_277_ = v___x_272_;
goto v_reusejp_276_;
}
else
{
lean_object* v_reuseFailAlloc_287_; 
v_reuseFailAlloc_287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_287_, 0, v___x_274_);
lean_ctor_set(v_reuseFailAlloc_287_, 1, v___x_275_);
v___x_277_ = v_reuseFailAlloc_287_;
goto v_reusejp_276_;
}
v_reusejp_276_:
{
lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_278_ = lean_box(0);
v___x_279_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_279_, 0, v___x_277_);
lean_ctor_set(v___x_279_, 1, v___x_278_);
v___x_280_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__13));
v___x_281_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__0(v___x_280_, v_dependencyBuildMode_x3f_270_);
lean_dec(v_dependencyBuildMode_x3f_270_);
v___x_282_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_282_, 0, v___x_281_);
lean_ctor_set(v___x_282_, 1, v___x_278_);
v___x_283_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_283_, 0, v___x_279_);
lean_ctor_set(v___x_283_, 1, v___x_282_);
v___x_284_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0));
v___x_285_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_283_, v___x_284_);
v___x_286_ = l_Lean_Json_mkObj(v___x_285_);
lean_dec(v___x_285_);
return v___x_286_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson_spec__0(lean_object* v_j_291_, lean_object* v_k_292_){
_start:
{
lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_293_ = l_Lean_Json_getObjValD(v_j_291_, v_k_292_);
v___x_294_ = l_Lean_Json_getStr_x3f(v___x_293_);
return v___x_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson_spec__0___boxed(lean_object* v_j_295_, lean_object* v_k_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson_spec__0(v_j_295_, v_k_296_);
lean_dec_ref(v_k_296_);
return v_res_297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson_spec__1(lean_object* v_j_298_, lean_object* v_k_299_){
_start:
{
lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_300_ = l_Lean_Json_getObjValD(v_j_298_, v_k_299_);
v___x_301_ = l_Lean_Json_getNat_x3f(v___x_300_);
return v___x_301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson_spec__1___boxed(lean_object* v_j_302_, lean_object* v_k_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson_spec__1(v_j_302_, v_k_303_);
lean_dec_ref(v_k_303_);
return v_res_304_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__3(void){
_start:
{
uint8_t v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_311_ = 1;
v___x_312_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__2));
v___x_313_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_312_, v___x_311_);
return v___x_313_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_314_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6));
v___x_315_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__3);
v___x_316_ = lean_string_append(v___x_315_, v___x_314_);
return v___x_316_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__6(void){
_start:
{
uint8_t v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_319_ = 1;
v___x_320_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__5));
v___x_321_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_320_, v___x_319_);
return v___x_321_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__7(void){
_start:
{
lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_322_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__6, &l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__6);
v___x_323_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__4);
v___x_324_ = lean_string_append(v___x_323_, v___x_322_);
return v___x_324_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__8(void){
_start:
{
lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; 
v___x_325_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_326_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__7);
v___x_327_ = lean_string_append(v___x_326_, v___x_325_);
return v___x_327_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__11(void){
_start:
{
uint8_t v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_331_ = 1;
v___x_332_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__10));
v___x_333_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_332_, v___x_331_);
return v___x_333_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__12(void){
_start:
{
lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_334_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__11, &l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__11);
v___x_335_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__4);
v___x_336_ = lean_string_append(v___x_335_, v___x_334_);
return v___x_336_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__13(void){
_start:
{
lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_337_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_338_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__12, &l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__12);
v___x_339_ = lean_string_append(v___x_338_, v___x_337_);
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson(lean_object* v_json_340_){
_start:
{
lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_341_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__0));
lean_inc(v_json_340_);
v___x_342_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson_spec__0(v_json_340_, v___x_341_);
if (lean_obj_tag(v___x_342_) == 0)
{
lean_object* v_a_343_; lean_object* v___x_345_; uint8_t v_isShared_346_; uint8_t v_isSharedCheck_352_; 
lean_dec(v_json_340_);
v_a_343_ = lean_ctor_get(v___x_342_, 0);
v_isSharedCheck_352_ = !lean_is_exclusive(v___x_342_);
if (v_isSharedCheck_352_ == 0)
{
v___x_345_ = v___x_342_;
v_isShared_346_ = v_isSharedCheck_352_;
goto v_resetjp_344_;
}
else
{
lean_inc(v_a_343_);
lean_dec(v___x_342_);
v___x_345_ = lean_box(0);
v_isShared_346_ = v_isSharedCheck_352_;
goto v_resetjp_344_;
}
v_resetjp_344_:
{
lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_350_; 
v___x_347_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__8);
v___x_348_ = lean_string_append(v___x_347_, v_a_343_);
lean_dec(v_a_343_);
if (v_isShared_346_ == 0)
{
lean_ctor_set(v___x_345_, 0, v___x_348_);
v___x_350_ = v___x_345_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v___x_348_);
v___x_350_ = v_reuseFailAlloc_351_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
return v___x_350_;
}
}
}
else
{
if (lean_obj_tag(v___x_342_) == 0)
{
lean_object* v_a_353_; lean_object* v___x_355_; uint8_t v_isShared_356_; uint8_t v_isSharedCheck_360_; 
lean_dec(v_json_340_);
v_a_353_ = lean_ctor_get(v___x_342_, 0);
v_isSharedCheck_360_ = !lean_is_exclusive(v___x_342_);
if (v_isSharedCheck_360_ == 0)
{
v___x_355_ = v___x_342_;
v_isShared_356_ = v_isSharedCheck_360_;
goto v_resetjp_354_;
}
else
{
lean_inc(v_a_353_);
lean_dec(v___x_342_);
v___x_355_ = lean_box(0);
v_isShared_356_ = v_isSharedCheck_360_;
goto v_resetjp_354_;
}
v_resetjp_354_:
{
lean_object* v___x_358_; 
if (v_isShared_356_ == 0)
{
lean_ctor_set_tag(v___x_355_, 0);
v___x_358_ = v___x_355_;
goto v_reusejp_357_;
}
else
{
lean_object* v_reuseFailAlloc_359_; 
v_reuseFailAlloc_359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_359_, 0, v_a_353_);
v___x_358_ = v_reuseFailAlloc_359_;
goto v_reusejp_357_;
}
v_reusejp_357_:
{
return v___x_358_;
}
}
}
else
{
lean_object* v_a_361_; lean_object* v___x_362_; lean_object* v___x_363_; 
v_a_361_ = lean_ctor_get(v___x_342_, 0);
lean_inc(v_a_361_);
lean_dec_ref(v___x_342_);
v___x_362_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__9));
v___x_363_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson_spec__1(v_json_340_, v___x_362_);
if (lean_obj_tag(v___x_363_) == 0)
{
lean_object* v_a_364_; lean_object* v___x_366_; uint8_t v_isShared_367_; uint8_t v_isSharedCheck_373_; 
lean_dec(v_a_361_);
v_a_364_ = lean_ctor_get(v___x_363_, 0);
v_isSharedCheck_373_ = !lean_is_exclusive(v___x_363_);
if (v_isSharedCheck_373_ == 0)
{
v___x_366_ = v___x_363_;
v_isShared_367_ = v_isSharedCheck_373_;
goto v_resetjp_365_;
}
else
{
lean_inc(v_a_364_);
lean_dec(v___x_363_);
v___x_366_ = lean_box(0);
v_isShared_367_ = v_isSharedCheck_373_;
goto v_resetjp_365_;
}
v_resetjp_365_:
{
lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_371_; 
v___x_368_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__13, &l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__13);
v___x_369_ = lean_string_append(v___x_368_, v_a_364_);
lean_dec(v_a_364_);
if (v_isShared_367_ == 0)
{
lean_ctor_set(v___x_366_, 0, v___x_369_);
v___x_371_ = v___x_366_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v___x_369_);
v___x_371_ = v_reuseFailAlloc_372_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
return v___x_371_;
}
}
}
else
{
if (lean_obj_tag(v___x_363_) == 0)
{
lean_object* v_a_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_381_; 
lean_dec(v_a_361_);
v_a_374_ = lean_ctor_get(v___x_363_, 0);
v_isSharedCheck_381_ = !lean_is_exclusive(v___x_363_);
if (v_isSharedCheck_381_ == 0)
{
v___x_376_ = v___x_363_;
v_isShared_377_ = v_isSharedCheck_381_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_a_374_);
lean_dec(v___x_363_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_381_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
lean_object* v___x_379_; 
if (v_isShared_377_ == 0)
{
lean_ctor_set_tag(v___x_376_, 0);
v___x_379_ = v___x_376_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v_a_374_);
v___x_379_ = v_reuseFailAlloc_380_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
return v___x_379_;
}
}
}
else
{
lean_object* v_a_382_; lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_390_; 
v_a_382_ = lean_ctor_get(v___x_363_, 0);
v_isSharedCheck_390_ = !lean_is_exclusive(v___x_363_);
if (v_isSharedCheck_390_ == 0)
{
v___x_384_ = v___x_363_;
v_isShared_385_ = v_isSharedCheck_390_;
goto v_resetjp_383_;
}
else
{
lean_inc(v_a_382_);
lean_dec(v___x_363_);
v___x_384_ = lean_box(0);
v_isShared_385_ = v_isSharedCheck_390_;
goto v_resetjp_383_;
}
v_resetjp_383_:
{
lean_object* v___x_386_; lean_object* v___x_388_; 
v___x_386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_386_, 0, v_a_361_);
lean_ctor_set(v___x_386_, 1, v_a_382_);
if (v_isShared_385_ == 0)
{
lean_ctor_set(v___x_384_, 0, v___x_386_);
v___x_388_ = v___x_384_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v___x_386_);
v___x_388_ = v_reuseFailAlloc_389_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
return v___x_388_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonWaitForDiagnosticsParams_toJson(lean_object* v_x_393_){
_start:
{
lean_object* v_uri_394_; lean_object* v_version_395_; lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_416_; 
v_uri_394_ = lean_ctor_get(v_x_393_, 0);
v_version_395_ = lean_ctor_get(v_x_393_, 1);
v_isSharedCheck_416_ = !lean_is_exclusive(v_x_393_);
if (v_isSharedCheck_416_ == 0)
{
v___x_397_ = v_x_393_;
v_isShared_398_ = v_isSharedCheck_416_;
goto v_resetjp_396_;
}
else
{
lean_inc(v_version_395_);
lean_inc(v_uri_394_);
lean_dec(v_x_393_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_416_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_402_; 
v___x_399_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__0));
v___x_400_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_400_, 0, v_uri_394_);
if (v_isShared_398_ == 0)
{
lean_ctor_set(v___x_397_, 1, v___x_400_);
lean_ctor_set(v___x_397_, 0, v___x_399_);
v___x_402_ = v___x_397_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_415_; 
v_reuseFailAlloc_415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_415_, 0, v___x_399_);
lean_ctor_set(v_reuseFailAlloc_415_, 1, v___x_400_);
v___x_402_ = v_reuseFailAlloc_415_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; 
v___x_403_ = lean_box(0);
v___x_404_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_404_, 0, v___x_402_);
lean_ctor_set(v___x_404_, 1, v___x_403_);
v___x_405_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__9));
v___x_406_ = l_Lean_JsonNumber_fromNat(v_version_395_);
v___x_407_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_407_, 0, v___x_406_);
v___x_408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_408_, 0, v___x_405_);
lean_ctor_set(v___x_408_, 1, v___x_407_);
v___x_409_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_409_, 0, v___x_408_);
lean_ctor_set(v___x_409_, 1, v___x_403_);
v___x_410_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_410_, 0, v___x_409_);
lean_ctor_set(v___x_410_, 1, v___x_403_);
v___x_411_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_411_, 0, v___x_404_);
lean_ctor_set(v___x_411_, 1, v___x_410_);
v___x_412_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0));
v___x_413_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_411_, v___x_412_);
v___x_414_ = l_Lean_Json_mkObj(v___x_413_);
lean_dec(v___x_413_);
return v___x_414_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_WaitForDiagnostics_toCtorIdx(lean_object* v_x_419_){
_start:
{
lean_object* v___x_420_; 
v___x_420_ = lean_unsigned_to_nat(0u);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonWaitForDiagnostics___lam__0(lean_object* v_x_423_){
_start:
{
lean_object* v___x_424_; 
v___x_424_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWaitForDiagnostics___lam__0___closed__0));
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonWaitForDiagnostics___lam__0___boxed(lean_object* v_x_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l_Lean_Lsp_instFromJsonWaitForDiagnostics___lam__0(v_x_425_);
lean_dec(v_x_425_);
return v_res_426_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonWaitForDiagnostics___lam__0___closed__0(void){
_start:
{
lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_429_ = lean_box(0);
v___x_430_ = l_Lean_Json_mkObj(v___x_429_);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonWaitForDiagnostics___lam__0(lean_object* v_x_431_){
_start:
{
lean_object* v___x_432_; 
v___x_432_ = lean_obj_once(&l_Lean_Lsp_instToJsonWaitForDiagnostics___lam__0___closed__0, &l_Lean_Lsp_instToJsonWaitForDiagnostics___lam__0___closed__0_once, _init_l_Lean_Lsp_instToJsonWaitForDiagnostics___lam__0___closed__0);
return v___x_432_;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForILeansParams_fromJson_spec__0_spec__0(lean_object* v_x_437_){
_start:
{
if (lean_obj_tag(v_x_437_) == 0)
{
lean_object* v___x_438_; 
v___x_438_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForILeansParams_fromJson_spec__0_spec__0___closed__0));
return v___x_438_;
}
else
{
lean_object* v___x_439_; 
v___x_439_ = l_Lean_Json_getStr_x3f(v_x_437_);
if (lean_obj_tag(v___x_439_) == 0)
{
lean_object* v_a_440_; lean_object* v___x_442_; uint8_t v_isShared_443_; uint8_t v_isSharedCheck_447_; 
v_a_440_ = lean_ctor_get(v___x_439_, 0);
v_isSharedCheck_447_ = !lean_is_exclusive(v___x_439_);
if (v_isSharedCheck_447_ == 0)
{
v___x_442_ = v___x_439_;
v_isShared_443_ = v_isSharedCheck_447_;
goto v_resetjp_441_;
}
else
{
lean_inc(v_a_440_);
lean_dec(v___x_439_);
v___x_442_ = lean_box(0);
v_isShared_443_ = v_isSharedCheck_447_;
goto v_resetjp_441_;
}
v_resetjp_441_:
{
lean_object* v___x_445_; 
if (v_isShared_443_ == 0)
{
v___x_445_ = v___x_442_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v_a_440_);
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
lean_object* v_a_448_; lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_456_; 
v_a_448_ = lean_ctor_get(v___x_439_, 0);
v_isSharedCheck_456_ = !lean_is_exclusive(v___x_439_);
if (v_isSharedCheck_456_ == 0)
{
v___x_450_ = v___x_439_;
v_isShared_451_ = v_isSharedCheck_456_;
goto v_resetjp_449_;
}
else
{
lean_inc(v_a_448_);
lean_dec(v___x_439_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_456_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
lean_object* v___x_452_; lean_object* v___x_454_; 
v___x_452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_452_, 0, v_a_448_);
if (v_isShared_451_ == 0)
{
lean_ctor_set(v___x_450_, 0, v___x_452_);
v___x_454_ = v___x_450_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v___x_452_);
v___x_454_ = v_reuseFailAlloc_455_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
return v___x_454_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForILeansParams_fromJson_spec__0(lean_object* v_j_457_, lean_object* v_k_458_){
_start:
{
lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_459_ = l_Lean_Json_getObjValD(v_j_457_, v_k_458_);
v___x_460_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForILeansParams_fromJson_spec__0_spec__0(v___x_459_);
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForILeansParams_fromJson_spec__0___boxed(lean_object* v_j_461_, lean_object* v_k_462_){
_start:
{
lean_object* v_res_463_; 
v_res_463_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForILeansParams_fromJson_spec__0(v_j_461_, v_k_462_);
lean_dec_ref(v_k_462_);
return v_res_463_;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForILeansParams_fromJson_spec__1_spec__2(lean_object* v_x_466_){
_start:
{
if (lean_obj_tag(v_x_466_) == 0)
{
lean_object* v___x_467_; 
v___x_467_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForILeansParams_fromJson_spec__1_spec__2___closed__0));
return v___x_467_;
}
else
{
lean_object* v___x_468_; 
v___x_468_ = l_Lean_Json_getNat_x3f(v_x_466_);
if (lean_obj_tag(v___x_468_) == 0)
{
lean_object* v_a_469_; lean_object* v___x_471_; uint8_t v_isShared_472_; uint8_t v_isSharedCheck_476_; 
v_a_469_ = lean_ctor_get(v___x_468_, 0);
v_isSharedCheck_476_ = !lean_is_exclusive(v___x_468_);
if (v_isSharedCheck_476_ == 0)
{
v___x_471_ = v___x_468_;
v_isShared_472_ = v_isSharedCheck_476_;
goto v_resetjp_470_;
}
else
{
lean_inc(v_a_469_);
lean_dec(v___x_468_);
v___x_471_ = lean_box(0);
v_isShared_472_ = v_isSharedCheck_476_;
goto v_resetjp_470_;
}
v_resetjp_470_:
{
lean_object* v___x_474_; 
if (v_isShared_472_ == 0)
{
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
v_a_477_ = lean_ctor_get(v___x_468_, 0);
v_isSharedCheck_485_ = !lean_is_exclusive(v___x_468_);
if (v_isSharedCheck_485_ == 0)
{
v___x_479_ = v___x_468_;
v_isShared_480_ = v_isSharedCheck_485_;
goto v_resetjp_478_;
}
else
{
lean_inc(v_a_477_);
lean_dec(v___x_468_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_485_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
lean_object* v___x_481_; lean_object* v___x_483_; 
v___x_481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_481_, 0, v_a_477_);
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
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForILeansParams_fromJson_spec__1(lean_object* v_j_486_, lean_object* v_k_487_){
_start:
{
lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_488_ = l_Lean_Json_getObjValD(v_j_486_, v_k_487_);
v___x_489_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForILeansParams_fromJson_spec__1_spec__2(v___x_488_);
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForILeansParams_fromJson_spec__1___boxed(lean_object* v_j_490_, lean_object* v_k_491_){
_start:
{
lean_object* v_res_492_; 
v_res_492_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForILeansParams_fromJson_spec__1(v_j_490_, v_k_491_);
lean_dec_ref(v_k_491_);
return v_res_492_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__2(void){
_start:
{
uint8_t v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_498_ = 1;
v___x_499_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__1));
v___x_500_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_499_, v___x_498_);
return v___x_500_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__3(void){
_start:
{
lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_501_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6));
v___x_502_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__2, &l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__2);
v___x_503_ = lean_string_append(v___x_502_, v___x_501_);
return v___x_503_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__6(void){
_start:
{
uint8_t v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_507_ = 1;
v___x_508_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__5));
v___x_509_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_508_, v___x_507_);
return v___x_509_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__7(void){
_start:
{
lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; 
v___x_510_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__6, &l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__6);
v___x_511_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__3);
v___x_512_ = lean_string_append(v___x_511_, v___x_510_);
return v___x_512_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__8(void){
_start:
{
lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; 
v___x_513_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_514_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__7);
v___x_515_ = lean_string_append(v___x_514_, v___x_513_);
return v___x_515_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__11(void){
_start:
{
uint8_t v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_519_ = 1;
v___x_520_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__10));
v___x_521_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_520_, v___x_519_);
return v___x_521_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__12(void){
_start:
{
lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; 
v___x_522_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__11, &l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__11);
v___x_523_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__3);
v___x_524_ = lean_string_append(v___x_523_, v___x_522_);
return v___x_524_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__13(void){
_start:
{
lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_525_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_526_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__12, &l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__12);
v___x_527_ = lean_string_append(v___x_526_, v___x_525_);
return v___x_527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson(lean_object* v_json_528_){
_start:
{
lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_529_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__0));
lean_inc(v_json_528_);
v___x_530_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForILeansParams_fromJson_spec__0(v_json_528_, v___x_529_);
if (lean_obj_tag(v___x_530_) == 0)
{
lean_object* v_a_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_540_; 
lean_dec(v_json_528_);
v_a_531_ = lean_ctor_get(v___x_530_, 0);
v_isSharedCheck_540_ = !lean_is_exclusive(v___x_530_);
if (v_isSharedCheck_540_ == 0)
{
v___x_533_ = v___x_530_;
v_isShared_534_ = v_isSharedCheck_540_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_a_531_);
lean_dec(v___x_530_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_540_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_538_; 
v___x_535_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__8);
v___x_536_ = lean_string_append(v___x_535_, v_a_531_);
lean_dec(v_a_531_);
if (v_isShared_534_ == 0)
{
lean_ctor_set(v___x_533_, 0, v___x_536_);
v___x_538_ = v___x_533_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v___x_536_);
v___x_538_ = v_reuseFailAlloc_539_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
return v___x_538_;
}
}
}
else
{
if (lean_obj_tag(v___x_530_) == 0)
{
lean_object* v_a_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_548_; 
lean_dec(v_json_528_);
v_a_541_ = lean_ctor_get(v___x_530_, 0);
v_isSharedCheck_548_ = !lean_is_exclusive(v___x_530_);
if (v_isSharedCheck_548_ == 0)
{
v___x_543_ = v___x_530_;
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_a_541_);
lean_dec(v___x_530_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v___x_546_; 
if (v_isShared_544_ == 0)
{
lean_ctor_set_tag(v___x_543_, 0);
v___x_546_ = v___x_543_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v_a_541_);
v___x_546_ = v_reuseFailAlloc_547_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
return v___x_546_;
}
}
}
else
{
lean_object* v_a_549_; lean_object* v___x_550_; lean_object* v___x_551_; 
v_a_549_ = lean_ctor_get(v___x_530_, 0);
lean_inc(v_a_549_);
lean_dec_ref(v___x_530_);
v___x_550_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__9));
v___x_551_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForILeansParams_fromJson_spec__1(v_json_528_, v___x_550_);
if (lean_obj_tag(v___x_551_) == 0)
{
lean_object* v_a_552_; lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_561_; 
lean_dec(v_a_549_);
v_a_552_ = lean_ctor_get(v___x_551_, 0);
v_isSharedCheck_561_ = !lean_is_exclusive(v___x_551_);
if (v_isSharedCheck_561_ == 0)
{
v___x_554_ = v___x_551_;
v_isShared_555_ = v_isSharedCheck_561_;
goto v_resetjp_553_;
}
else
{
lean_inc(v_a_552_);
lean_dec(v___x_551_);
v___x_554_ = lean_box(0);
v_isShared_555_ = v_isSharedCheck_561_;
goto v_resetjp_553_;
}
v_resetjp_553_:
{
lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_559_; 
v___x_556_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__13, &l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__13);
v___x_557_ = lean_string_append(v___x_556_, v_a_552_);
lean_dec(v_a_552_);
if (v_isShared_555_ == 0)
{
lean_ctor_set(v___x_554_, 0, v___x_557_);
v___x_559_ = v___x_554_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v___x_557_);
v___x_559_ = v_reuseFailAlloc_560_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
return v___x_559_;
}
}
}
else
{
if (lean_obj_tag(v___x_551_) == 0)
{
lean_object* v_a_562_; lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_569_; 
lean_dec(v_a_549_);
v_a_562_ = lean_ctor_get(v___x_551_, 0);
v_isSharedCheck_569_ = !lean_is_exclusive(v___x_551_);
if (v_isSharedCheck_569_ == 0)
{
v___x_564_ = v___x_551_;
v_isShared_565_ = v_isSharedCheck_569_;
goto v_resetjp_563_;
}
else
{
lean_inc(v_a_562_);
lean_dec(v___x_551_);
v___x_564_ = lean_box(0);
v_isShared_565_ = v_isSharedCheck_569_;
goto v_resetjp_563_;
}
v_resetjp_563_:
{
lean_object* v___x_567_; 
if (v_isShared_565_ == 0)
{
lean_ctor_set_tag(v___x_564_, 0);
v___x_567_ = v___x_564_;
goto v_reusejp_566_;
}
else
{
lean_object* v_reuseFailAlloc_568_; 
v_reuseFailAlloc_568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_568_, 0, v_a_562_);
v___x_567_ = v_reuseFailAlloc_568_;
goto v_reusejp_566_;
}
v_reusejp_566_:
{
return v___x_567_;
}
}
}
else
{
lean_object* v_a_570_; lean_object* v___x_572_; uint8_t v_isShared_573_; uint8_t v_isSharedCheck_578_; 
v_a_570_ = lean_ctor_get(v___x_551_, 0);
v_isSharedCheck_578_ = !lean_is_exclusive(v___x_551_);
if (v_isSharedCheck_578_ == 0)
{
v___x_572_ = v___x_551_;
v_isShared_573_ = v_isSharedCheck_578_;
goto v_resetjp_571_;
}
else
{
lean_inc(v_a_570_);
lean_dec(v___x_551_);
v___x_572_ = lean_box(0);
v_isShared_573_ = v_isSharedCheck_578_;
goto v_resetjp_571_;
}
v_resetjp_571_:
{
lean_object* v___x_574_; lean_object* v___x_576_; 
v___x_574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_574_, 0, v_a_549_);
lean_ctor_set(v___x_574_, 1, v_a_570_);
if (v_isShared_573_ == 0)
{
lean_ctor_set(v___x_572_, 0, v___x_574_);
v___x_576_ = v___x_572_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v___x_574_);
v___x_576_ = v_reuseFailAlloc_577_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
return v___x_576_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonWaitForILeansParams_toJson_spec__0(lean_object* v_k_581_, lean_object* v_x_582_){
_start:
{
if (lean_obj_tag(v_x_582_) == 0)
{
lean_object* v___x_583_; 
lean_dec_ref(v_k_581_);
v___x_583_ = lean_box(0);
return v___x_583_;
}
else
{
lean_object* v_val_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_594_; 
v_val_584_ = lean_ctor_get(v_x_582_, 0);
v_isSharedCheck_594_ = !lean_is_exclusive(v_x_582_);
if (v_isSharedCheck_594_ == 0)
{
v___x_586_ = v_x_582_;
v_isShared_587_ = v_isSharedCheck_594_;
goto v_resetjp_585_;
}
else
{
lean_inc(v_val_584_);
lean_dec(v_x_582_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_594_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
lean_object* v___x_589_; 
if (v_isShared_587_ == 0)
{
lean_ctor_set_tag(v___x_586_, 3);
v___x_589_ = v___x_586_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v_val_584_);
v___x_589_ = v_reuseFailAlloc_593_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; 
v___x_590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_590_, 0, v_k_581_);
lean_ctor_set(v___x_590_, 1, v___x_589_);
v___x_591_ = lean_box(0);
v___x_592_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_592_, 0, v___x_590_);
lean_ctor_set(v___x_592_, 1, v___x_591_);
return v___x_592_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonWaitForILeansParams_toJson_spec__1(lean_object* v_k_595_, lean_object* v_x_596_){
_start:
{
if (lean_obj_tag(v_x_596_) == 0)
{
lean_object* v___x_597_; 
lean_dec_ref(v_k_595_);
v___x_597_ = lean_box(0);
return v___x_597_;
}
else
{
lean_object* v_val_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_609_; 
v_val_598_ = lean_ctor_get(v_x_596_, 0);
v_isSharedCheck_609_ = !lean_is_exclusive(v_x_596_);
if (v_isSharedCheck_609_ == 0)
{
v___x_600_ = v_x_596_;
v_isShared_601_ = v_isSharedCheck_609_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_val_598_);
lean_dec(v_x_596_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_609_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
lean_object* v___x_602_; lean_object* v___x_604_; 
v___x_602_ = l_Lean_JsonNumber_fromNat(v_val_598_);
if (v_isShared_601_ == 0)
{
lean_ctor_set_tag(v___x_600_, 2);
lean_ctor_set(v___x_600_, 0, v___x_602_);
v___x_604_ = v___x_600_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v___x_602_);
v___x_604_ = v_reuseFailAlloc_608_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_605_, 0, v_k_595_);
lean_ctor_set(v___x_605_, 1, v___x_604_);
v___x_606_ = lean_box(0);
v___x_607_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_607_, 0, v___x_605_);
lean_ctor_set(v___x_607_, 1, v___x_606_);
return v___x_607_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonWaitForILeansParams_toJson(lean_object* v_x_610_){
_start:
{
lean_object* v_uri_x3f_611_; lean_object* v_version_x3f_612_; lean_object* v___x_614_; uint8_t v_isShared_615_; uint8_t v_isSharedCheck_628_; 
v_uri_x3f_611_ = lean_ctor_get(v_x_610_, 0);
v_version_x3f_612_ = lean_ctor_get(v_x_610_, 1);
v_isSharedCheck_628_ = !lean_is_exclusive(v_x_610_);
if (v_isSharedCheck_628_ == 0)
{
v___x_614_ = v_x_610_;
v_isShared_615_ = v_isSharedCheck_628_;
goto v_resetjp_613_;
}
else
{
lean_inc(v_version_x3f_612_);
lean_inc(v_uri_x3f_611_);
lean_dec(v_x_610_);
v___x_614_ = lean_box(0);
v_isShared_615_ = v_isSharedCheck_628_;
goto v_resetjp_613_;
}
v_resetjp_613_:
{
lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_622_; 
v___x_616_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__0));
v___x_617_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonWaitForILeansParams_toJson_spec__0(v___x_616_, v_uri_x3f_611_);
v___x_618_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__9));
v___x_619_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonWaitForILeansParams_toJson_spec__1(v___x_618_, v_version_x3f_612_);
v___x_620_ = lean_box(0);
if (v_isShared_615_ == 0)
{
lean_ctor_set_tag(v___x_614_, 1);
lean_ctor_set(v___x_614_, 1, v___x_620_);
lean_ctor_set(v___x_614_, 0, v___x_619_);
v___x_622_ = v___x_614_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v___x_619_);
lean_ctor_set(v_reuseFailAlloc_627_, 1, v___x_620_);
v___x_622_ = v_reuseFailAlloc_627_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_623_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_623_, 0, v___x_617_);
lean_ctor_set(v___x_623_, 1, v___x_622_);
v___x_624_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0));
v___x_625_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_623_, v___x_624_);
v___x_626_ = l_Lean_Json_mkObj(v___x_625_);
lean_dec(v___x_625_);
return v___x_626_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_WaitForILeans_toCtorIdx(lean_object* v_x_631_){
_start:
{
lean_object* v___x_632_; 
v___x_632_ = lean_unsigned_to_nat(0u);
return v___x_632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonWaitForILeans_fromJson(lean_object* v_json_635_){
_start:
{
lean_object* v___x_636_; 
v___x_636_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWaitForILeans_fromJson___closed__0));
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonWaitForILeans_fromJson___boxed(lean_object* v_json_637_){
_start:
{
lean_object* v_res_638_; 
v_res_638_ = l_Lean_Lsp_instFromJsonWaitForILeans_fromJson(v_json_637_);
lean_dec(v_json_637_);
return v_res_638_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonWaitForILeans_toJson___closed__0(void){
_start:
{
lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_641_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0));
v___x_642_ = lean_box(0);
v___x_643_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_642_, v___x_641_);
return v___x_643_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonWaitForILeans_toJson___closed__1(void){
_start:
{
lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_644_ = lean_obj_once(&l_Lean_Lsp_instToJsonWaitForILeans_toJson___closed__0, &l_Lean_Lsp_instToJsonWaitForILeans_toJson___closed__0_once, _init_l_Lean_Lsp_instToJsonWaitForILeans_toJson___closed__0);
v___x_645_ = l_Lean_Json_mkObj(v___x_644_);
return v___x_645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonWaitForILeans_toJson(lean_object* v_x_646_){
_start:
{
lean_object* v___x_647_; 
v___x_647_ = lean_obj_once(&l_Lean_Lsp_instToJsonWaitForILeans_toJson___closed__1, &l_Lean_Lsp_instToJsonWaitForILeans_toJson___closed__1_once, _init_l_Lean_Lsp_instToJsonWaitForILeans_toJson___closed__1);
return v___x_647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanFileProgressKind_ctorIdx(uint8_t v_x_650_){
_start:
{
if (v_x_650_ == 0)
{
lean_object* v___x_651_; 
v___x_651_ = lean_unsigned_to_nat(0u);
return v___x_651_;
}
else
{
lean_object* v___x_652_; 
v___x_652_ = lean_unsigned_to_nat(1u);
return v___x_652_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanFileProgressKind_ctorIdx___boxed(lean_object* v_x_653_){
_start:
{
uint8_t v_x_boxed_654_; lean_object* v_res_655_; 
v_x_boxed_654_ = lean_unbox(v_x_653_);
v_res_655_ = l_Lean_Lsp_LeanFileProgressKind_ctorIdx(v_x_boxed_654_);
return v_res_655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanFileProgressKind_toCtorIdx(uint8_t v_x_656_){
_start:
{
lean_object* v___x_657_; 
v___x_657_ = l_Lean_Lsp_LeanFileProgressKind_ctorIdx(v_x_656_);
return v___x_657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanFileProgressKind_toCtorIdx___boxed(lean_object* v_x_658_){
_start:
{
uint8_t v_x_4__boxed_659_; lean_object* v_res_660_; 
v_x_4__boxed_659_ = lean_unbox(v_x_658_);
v_res_660_ = l_Lean_Lsp_LeanFileProgressKind_toCtorIdx(v_x_4__boxed_659_);
return v_res_660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanFileProgressKind_ctorElim___redArg(lean_object* v_k_661_){
_start:
{
lean_inc(v_k_661_);
return v_k_661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanFileProgressKind_ctorElim___redArg___boxed(lean_object* v_k_662_){
_start:
{
lean_object* v_res_663_; 
v_res_663_ = l_Lean_Lsp_LeanFileProgressKind_ctorElim___redArg(v_k_662_);
lean_dec(v_k_662_);
return v_res_663_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanFileProgressKind_ctorElim(lean_object* v_motive_664_, lean_object* v_ctorIdx_665_, uint8_t v_t_666_, lean_object* v_h_667_, lean_object* v_k_668_){
_start:
{
lean_inc(v_k_668_);
return v_k_668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanFileProgressKind_ctorElim___boxed(lean_object* v_motive_669_, lean_object* v_ctorIdx_670_, lean_object* v_t_671_, lean_object* v_h_672_, lean_object* v_k_673_){
_start:
{
uint8_t v_t_boxed_674_; lean_object* v_res_675_; 
v_t_boxed_674_ = lean_unbox(v_t_671_);
v_res_675_ = l_Lean_Lsp_LeanFileProgressKind_ctorElim(v_motive_669_, v_ctorIdx_670_, v_t_boxed_674_, v_h_672_, v_k_673_);
lean_dec(v_k_673_);
lean_dec(v_ctorIdx_670_);
return v_res_675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanFileProgressKind_processing_elim___redArg(lean_object* v_processing_676_){
_start:
{
lean_inc(v_processing_676_);
return v_processing_676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanFileProgressKind_processing_elim___redArg___boxed(lean_object* v_processing_677_){
_start:
{
lean_object* v_res_678_; 
v_res_678_ = l_Lean_Lsp_LeanFileProgressKind_processing_elim___redArg(v_processing_677_);
lean_dec(v_processing_677_);
return v_res_678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanFileProgressKind_processing_elim(lean_object* v_motive_679_, uint8_t v_t_680_, lean_object* v_h_681_, lean_object* v_processing_682_){
_start:
{
lean_inc(v_processing_682_);
return v_processing_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanFileProgressKind_processing_elim___boxed(lean_object* v_motive_683_, lean_object* v_t_684_, lean_object* v_h_685_, lean_object* v_processing_686_){
_start:
{
uint8_t v_t_boxed_687_; lean_object* v_res_688_; 
v_t_boxed_687_ = lean_unbox(v_t_684_);
v_res_688_ = l_Lean_Lsp_LeanFileProgressKind_processing_elim(v_motive_683_, v_t_boxed_687_, v_h_685_, v_processing_686_);
lean_dec(v_processing_686_);
return v_res_688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanFileProgressKind_fatalError_elim___redArg(lean_object* v_fatalError_689_){
_start:
{
lean_inc(v_fatalError_689_);
return v_fatalError_689_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanFileProgressKind_fatalError_elim___redArg___boxed(lean_object* v_fatalError_690_){
_start:
{
lean_object* v_res_691_; 
v_res_691_ = l_Lean_Lsp_LeanFileProgressKind_fatalError_elim___redArg(v_fatalError_690_);
lean_dec(v_fatalError_690_);
return v_res_691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanFileProgressKind_fatalError_elim(lean_object* v_motive_692_, uint8_t v_t_693_, lean_object* v_h_694_, lean_object* v_fatalError_695_){
_start:
{
lean_inc(v_fatalError_695_);
return v_fatalError_695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanFileProgressKind_fatalError_elim___boxed(lean_object* v_motive_696_, lean_object* v_t_697_, lean_object* v_h_698_, lean_object* v_fatalError_699_){
_start:
{
uint8_t v_t_boxed_700_; lean_object* v_res_701_; 
v_t_boxed_700_ = lean_unbox(v_t_697_);
v_res_701_ = l_Lean_Lsp_LeanFileProgressKind_fatalError_elim(v_motive_696_, v_t_boxed_700_, v_h_698_, v_fatalError_699_);
lean_dec(v_fatalError_699_);
return v_res_701_;
}
}
static uint8_t _init_l_Lean_Lsp_instInhabitedLeanFileProgressKind_default(void){
_start:
{
uint8_t v___x_702_; 
v___x_702_ = 0;
return v___x_702_;
}
}
static uint8_t _init_l_Lean_Lsp_instInhabitedLeanFileProgressKind(void){
_start:
{
uint8_t v___x_703_; 
v___x_703_ = 0;
return v___x_703_;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_instBEqLeanFileProgressKind_beq(uint8_t v_x_704_, uint8_t v_y_705_){
_start:
{
lean_object* v___x_706_; lean_object* v___x_707_; uint8_t v___x_708_; 
v___x_706_ = l_Lean_Lsp_LeanFileProgressKind_ctorIdx(v_x_704_);
v___x_707_ = l_Lean_Lsp_LeanFileProgressKind_ctorIdx(v_y_705_);
v___x_708_ = lean_nat_dec_eq(v___x_706_, v___x_707_);
lean_dec(v___x_707_);
lean_dec(v___x_706_);
return v___x_708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqLeanFileProgressKind_beq___boxed(lean_object* v_x_709_, lean_object* v_y_710_){
_start:
{
uint8_t v_x_17__boxed_711_; uint8_t v_y_18__boxed_712_; uint8_t v_res_713_; lean_object* v_r_714_; 
v_x_17__boxed_711_ = lean_unbox(v_x_709_);
v_y_18__boxed_712_ = lean_unbox(v_y_710_);
v_res_713_ = l_Lean_Lsp_instBEqLeanFileProgressKind_beq(v_x_17__boxed_711_, v_y_18__boxed_712_);
v_r_714_ = lean_box(v_res_713_);
return v_r_714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanFileProgressKind___lam__0(lean_object* v_j_725_){
_start:
{
lean_object* v___x_734_; 
lean_inc(v_j_725_);
v___x_734_ = l_Lean_Json_getNat_x3f(v_j_725_);
if (lean_obj_tag(v___x_734_) == 1)
{
lean_object* v_a_735_; lean_object* v___x_736_; uint8_t v___x_737_; 
v_a_735_ = lean_ctor_get(v___x_734_, 0);
lean_inc(v_a_735_);
lean_dec_ref(v___x_734_);
v___x_736_ = lean_unsigned_to_nat(1u);
v___x_737_ = lean_nat_dec_eq(v_a_735_, v___x_736_);
if (v___x_737_ == 0)
{
lean_object* v___x_738_; uint8_t v___x_739_; 
v___x_738_ = lean_unsigned_to_nat(2u);
v___x_739_ = lean_nat_dec_eq(v_a_735_, v___x_738_);
lean_dec(v_a_735_);
if (v___x_739_ == 0)
{
goto v___jp_726_;
}
else
{
lean_object* v___x_740_; 
lean_dec(v_j_725_);
v___x_740_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressKind___lam__0___closed__2));
return v___x_740_;
}
}
else
{
lean_object* v___x_741_; 
lean_dec(v_a_735_);
lean_dec(v_j_725_);
v___x_741_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressKind___lam__0___closed__3));
return v___x_741_;
}
}
else
{
lean_dec_ref(v___x_734_);
goto v___jp_726_;
}
v___jp_726_:
{
lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; 
v___x_727_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressKind___lam__0___closed__0));
v___x_728_ = lean_unsigned_to_nat(80u);
v___x_729_ = l_Lean_Json_pretty(v_j_725_, v___x_728_);
v___x_730_ = lean_string_append(v___x_727_, v___x_729_);
lean_dec_ref(v___x_729_);
v___x_731_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressKind___lam__0___closed__1));
v___x_732_ = lean_string_append(v___x_730_, v___x_731_);
v___x_733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_733_, 0, v___x_732_);
return v___x_733_;
}
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__0(void){
_start:
{
lean_object* v___x_744_; lean_object* v___x_745_; 
v___x_744_ = lean_unsigned_to_nat(1u);
v___x_745_ = l_Lean_JsonNumber_fromNat(v___x_744_);
return v___x_745_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__1(void){
_start:
{
lean_object* v___x_746_; lean_object* v___x_747_; 
v___x_746_ = lean_obj_once(&l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__0, &l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__0_once, _init_l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__0);
v___x_747_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_747_, 0, v___x_746_);
return v___x_747_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__2(void){
_start:
{
lean_object* v___x_748_; lean_object* v___x_749_; 
v___x_748_ = lean_unsigned_to_nat(2u);
v___x_749_ = l_Lean_JsonNumber_fromNat(v___x_748_);
return v___x_749_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__3(void){
_start:
{
lean_object* v___x_750_; lean_object* v___x_751_; 
v___x_750_ = lean_obj_once(&l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__2, &l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__2_once, _init_l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__2);
v___x_751_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_751_, 0, v___x_750_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0(uint8_t v_x_752_){
_start:
{
if (v_x_752_ == 0)
{
lean_object* v___x_753_; 
v___x_753_ = lean_obj_once(&l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__1, &l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__1_once, _init_l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__1);
return v___x_753_;
}
else
{
lean_object* v___x_754_; 
v___x_754_ = lean_obj_once(&l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__3, &l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__3_once, _init_l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__3);
return v___x_754_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___boxed(lean_object* v_x_755_){
_start:
{
uint8_t v_x_56__boxed_756_; lean_object* v_res_757_; 
v_x_56__boxed_756_ = lean_unbox(v_x_755_);
v_res_757_ = l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0(v_x_56__boxed_756_);
return v_res_757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson_spec__0(lean_object* v_j_760_, lean_object* v_k_761_){
_start:
{
lean_object* v___x_762_; lean_object* v___x_763_; 
v___x_762_ = l_Lean_Json_getObjValD(v_j_760_, v_k_761_);
v___x_763_ = l_Lean_Lsp_instFromJsonRange_fromJson(v___x_762_);
return v___x_763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson_spec__0___boxed(lean_object* v_j_764_, lean_object* v_k_765_){
_start:
{
lean_object* v_res_766_; 
v_res_766_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson_spec__0(v_j_764_, v_k_765_);
lean_dec_ref(v_k_765_);
return v_res_766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson_spec__1(lean_object* v_j_767_, lean_object* v_k_768_){
_start:
{
lean_object* v___x_769_; lean_object* v___x_778_; 
v___x_769_ = l_Lean_Json_getObjValD(v_j_767_, v_k_768_);
lean_inc(v___x_769_);
v___x_778_ = l_Lean_Json_getNat_x3f(v___x_769_);
if (lean_obj_tag(v___x_778_) == 1)
{
lean_object* v_a_779_; lean_object* v___x_780_; uint8_t v___x_781_; 
v_a_779_ = lean_ctor_get(v___x_778_, 0);
lean_inc(v_a_779_);
lean_dec_ref(v___x_778_);
v___x_780_ = lean_unsigned_to_nat(1u);
v___x_781_ = lean_nat_dec_eq(v_a_779_, v___x_780_);
if (v___x_781_ == 0)
{
lean_object* v___x_782_; uint8_t v___x_783_; 
v___x_782_ = lean_unsigned_to_nat(2u);
v___x_783_ = lean_nat_dec_eq(v_a_779_, v___x_782_);
lean_dec(v_a_779_);
if (v___x_783_ == 0)
{
goto v___jp_770_;
}
else
{
lean_object* v___x_784_; 
lean_dec(v___x_769_);
v___x_784_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressKind___lam__0___closed__2));
return v___x_784_;
}
}
else
{
lean_object* v___x_785_; 
lean_dec(v_a_779_);
lean_dec(v___x_769_);
v___x_785_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressKind___lam__0___closed__3));
return v___x_785_;
}
}
else
{
lean_dec_ref(v___x_778_);
goto v___jp_770_;
}
v___jp_770_:
{
lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; 
v___x_771_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressKind___lam__0___closed__0));
v___x_772_ = lean_unsigned_to_nat(80u);
v___x_773_ = l_Lean_Json_pretty(v___x_769_, v___x_772_);
v___x_774_ = lean_string_append(v___x_771_, v___x_773_);
lean_dec_ref(v___x_773_);
v___x_775_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressKind___lam__0___closed__1));
v___x_776_ = lean_string_append(v___x_774_, v___x_775_);
v___x_777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_777_, 0, v___x_776_);
return v___x_777_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson_spec__1___boxed(lean_object* v_j_786_, lean_object* v_k_787_){
_start:
{
lean_object* v_res_788_; 
v_res_788_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson_spec__1(v_j_786_, v_k_787_);
lean_dec_ref(v_k_787_);
return v_res_788_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__3(void){
_start:
{
uint8_t v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; 
v___x_795_ = 1;
v___x_796_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__2));
v___x_797_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_796_, v___x_795_);
return v___x_797_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__4(void){
_start:
{
lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; 
v___x_798_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6));
v___x_799_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__3);
v___x_800_ = lean_string_append(v___x_799_, v___x_798_);
return v___x_800_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__6(void){
_start:
{
uint8_t v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; 
v___x_803_ = 1;
v___x_804_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__5));
v___x_805_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_804_, v___x_803_);
return v___x_805_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__7(void){
_start:
{
lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; 
v___x_806_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__6);
v___x_807_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__4);
v___x_808_ = lean_string_append(v___x_807_, v___x_806_);
return v___x_808_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__8(void){
_start:
{
lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; 
v___x_809_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_810_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__7);
v___x_811_ = lean_string_append(v___x_810_, v___x_809_);
return v___x_811_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__11(void){
_start:
{
uint8_t v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; 
v___x_815_ = 1;
v___x_816_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__10));
v___x_817_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_816_, v___x_815_);
return v___x_817_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__12(void){
_start:
{
lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; 
v___x_818_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__11, &l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__11);
v___x_819_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__4);
v___x_820_ = lean_string_append(v___x_819_, v___x_818_);
return v___x_820_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__13(void){
_start:
{
lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; 
v___x_821_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_822_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__12, &l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__12);
v___x_823_ = lean_string_append(v___x_822_, v___x_821_);
return v___x_823_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson(lean_object* v_json_824_){
_start:
{
lean_object* v___x_825_; lean_object* v___x_826_; 
v___x_825_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__0));
lean_inc(v_json_824_);
v___x_826_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson_spec__0(v_json_824_, v___x_825_);
if (lean_obj_tag(v___x_826_) == 0)
{
lean_object* v_a_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_836_; 
lean_dec(v_json_824_);
v_a_827_ = lean_ctor_get(v___x_826_, 0);
v_isSharedCheck_836_ = !lean_is_exclusive(v___x_826_);
if (v_isSharedCheck_836_ == 0)
{
v___x_829_ = v___x_826_;
v_isShared_830_ = v_isSharedCheck_836_;
goto v_resetjp_828_;
}
else
{
lean_inc(v_a_827_);
lean_dec(v___x_826_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_836_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_834_; 
v___x_831_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__8);
v___x_832_ = lean_string_append(v___x_831_, v_a_827_);
lean_dec(v_a_827_);
if (v_isShared_830_ == 0)
{
lean_ctor_set(v___x_829_, 0, v___x_832_);
v___x_834_ = v___x_829_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v___x_832_);
v___x_834_ = v_reuseFailAlloc_835_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
return v___x_834_;
}
}
}
else
{
if (lean_obj_tag(v___x_826_) == 0)
{
lean_object* v_a_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_844_; 
lean_dec(v_json_824_);
v_a_837_ = lean_ctor_get(v___x_826_, 0);
v_isSharedCheck_844_ = !lean_is_exclusive(v___x_826_);
if (v_isSharedCheck_844_ == 0)
{
v___x_839_ = v___x_826_;
v_isShared_840_ = v_isSharedCheck_844_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_a_837_);
lean_dec(v___x_826_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_844_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
lean_object* v___x_842_; 
if (v_isShared_840_ == 0)
{
lean_ctor_set_tag(v___x_839_, 0);
v___x_842_ = v___x_839_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v_a_837_);
v___x_842_ = v_reuseFailAlloc_843_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
return v___x_842_;
}
}
}
else
{
lean_object* v_a_845_; lean_object* v___x_846_; lean_object* v___x_847_; 
v_a_845_ = lean_ctor_get(v___x_826_, 0);
lean_inc(v_a_845_);
lean_dec_ref(v___x_826_);
v___x_846_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__9));
v___x_847_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson_spec__1(v_json_824_, v___x_846_);
if (lean_obj_tag(v___x_847_) == 0)
{
lean_object* v_a_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_857_; 
lean_dec(v_a_845_);
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
v___x_852_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__13, &l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__13);
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
lean_dec(v_a_845_);
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
lean_object* v_a_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_875_; 
v_a_866_ = lean_ctor_get(v___x_847_, 0);
v_isSharedCheck_875_ = !lean_is_exclusive(v___x_847_);
if (v_isSharedCheck_875_ == 0)
{
v___x_868_ = v___x_847_;
v_isShared_869_ = v_isSharedCheck_875_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_a_866_);
lean_dec(v___x_847_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_875_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v___x_870_; uint8_t v___x_871_; lean_object* v___x_873_; 
v___x_870_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_870_, 0, v_a_845_);
v___x_871_ = lean_unbox(v_a_866_);
lean_dec(v_a_866_);
lean_ctor_set_uint8(v___x_870_, sizeof(void*)*1, v___x_871_);
if (v_isShared_869_ == 0)
{
lean_ctor_set(v___x_868_, 0, v___x_870_);
v___x_873_ = v___x_868_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v___x_870_);
v___x_873_ = v_reuseFailAlloc_874_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
return v___x_873_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanFileProgressProcessingInfo_toJson(lean_object* v_x_878_){
_start:
{
lean_object* v_range_879_; uint8_t v_kind_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___y_888_; 
v_range_879_ = lean_ctor_get(v_x_878_, 0);
lean_inc_ref(v_range_879_);
v_kind_880_ = lean_ctor_get_uint8(v_x_878_, sizeof(void*)*1);
lean_dec_ref(v_x_878_);
v___x_881_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__0));
v___x_882_ = l_Lean_Lsp_instToJsonRange_toJson(v_range_879_);
v___x_883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_883_, 0, v___x_881_);
lean_ctor_set(v___x_883_, 1, v___x_882_);
v___x_884_ = lean_box(0);
v___x_885_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_885_, 0, v___x_883_);
lean_ctor_set(v___x_885_, 1, v___x_884_);
v___x_886_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__9));
if (v_kind_880_ == 0)
{
lean_object* v___x_896_; 
v___x_896_ = lean_obj_once(&l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__1, &l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__1_once, _init_l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__1);
v___y_888_ = v___x_896_;
goto v___jp_887_;
}
else
{
lean_object* v___x_897_; 
v___x_897_ = lean_obj_once(&l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__3, &l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__3_once, _init_l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__3);
v___y_888_ = v___x_897_;
goto v___jp_887_;
}
v___jp_887_:
{
lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; 
lean_inc(v___y_888_);
v___x_889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_889_, 0, v___x_886_);
lean_ctor_set(v___x_889_, 1, v___y_888_);
v___x_890_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_890_, 0, v___x_889_);
lean_ctor_set(v___x_890_, 1, v___x_884_);
v___x_891_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_891_, 0, v___x_890_);
lean_ctor_set(v___x_891_, 1, v___x_884_);
v___x_892_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_892_, 0, v___x_885_);
lean_ctor_set(v___x_892_, 1, v___x_891_);
v___x_893_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0));
v___x_894_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_892_, v___x_893_);
v___x_895_ = l_Lean_Json_mkObj(v___x_894_);
lean_dec(v___x_894_);
return v___x_895_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__0(lean_object* v_j_900_, lean_object* v_k_901_){
_start:
{
lean_object* v___x_902_; lean_object* v___x_903_; 
v___x_902_ = l_Lean_Json_getObjValD(v_j_900_, v_k_901_);
v___x_903_ = l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson(v___x_902_);
return v___x_903_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__0___boxed(lean_object* v_j_904_, lean_object* v_k_905_){
_start:
{
lean_object* v_res_906_; 
v_res_906_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__0(v_j_904_, v_k_905_);
lean_dec_ref(v_k_905_);
return v_res_906_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__1_spec__1_spec__2(size_t v_sz_907_, size_t v_i_908_, lean_object* v_bs_909_){
_start:
{
uint8_t v___x_910_; 
v___x_910_ = lean_usize_dec_lt(v_i_908_, v_sz_907_);
if (v___x_910_ == 0)
{
lean_object* v___x_911_; 
v___x_911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_911_, 0, v_bs_909_);
return v___x_911_;
}
else
{
lean_object* v_v_912_; lean_object* v___x_913_; 
v_v_912_ = lean_array_uget_borrowed(v_bs_909_, v_i_908_);
lean_inc(v_v_912_);
v___x_913_ = l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson(v_v_912_);
if (lean_obj_tag(v___x_913_) == 0)
{
lean_object* v_a_914_; lean_object* v___x_916_; uint8_t v_isShared_917_; uint8_t v_isSharedCheck_921_; 
lean_dec_ref(v_bs_909_);
v_a_914_ = lean_ctor_get(v___x_913_, 0);
v_isSharedCheck_921_ = !lean_is_exclusive(v___x_913_);
if (v_isSharedCheck_921_ == 0)
{
v___x_916_ = v___x_913_;
v_isShared_917_ = v_isSharedCheck_921_;
goto v_resetjp_915_;
}
else
{
lean_inc(v_a_914_);
lean_dec(v___x_913_);
v___x_916_ = lean_box(0);
v_isShared_917_ = v_isSharedCheck_921_;
goto v_resetjp_915_;
}
v_resetjp_915_:
{
lean_object* v___x_919_; 
if (v_isShared_917_ == 0)
{
v___x_919_ = v___x_916_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v_a_914_);
v___x_919_ = v_reuseFailAlloc_920_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
return v___x_919_;
}
}
}
else
{
lean_object* v_a_922_; lean_object* v___x_923_; lean_object* v_bs_x27_924_; size_t v___x_925_; size_t v___x_926_; lean_object* v___x_927_; 
v_a_922_ = lean_ctor_get(v___x_913_, 0);
lean_inc(v_a_922_);
lean_dec_ref(v___x_913_);
v___x_923_ = lean_unsigned_to_nat(0u);
v_bs_x27_924_ = lean_array_uset(v_bs_909_, v_i_908_, v___x_923_);
v___x_925_ = ((size_t)1ULL);
v___x_926_ = lean_usize_add(v_i_908_, v___x_925_);
v___x_927_ = lean_array_uset(v_bs_x27_924_, v_i_908_, v_a_922_);
v_i_908_ = v___x_926_;
v_bs_909_ = v___x_927_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__1_spec__1_spec__2___boxed(lean_object* v_sz_929_, lean_object* v_i_930_, lean_object* v_bs_931_){
_start:
{
size_t v_sz_boxed_932_; size_t v_i_boxed_933_; lean_object* v_res_934_; 
v_sz_boxed_932_ = lean_unbox_usize(v_sz_929_);
lean_dec(v_sz_929_);
v_i_boxed_933_ = lean_unbox_usize(v_i_930_);
lean_dec(v_i_930_);
v_res_934_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__1_spec__1_spec__2(v_sz_boxed_932_, v_i_boxed_933_, v_bs_931_);
return v_res_934_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__1_spec__1(lean_object* v_x_936_){
_start:
{
if (lean_obj_tag(v_x_936_) == 4)
{
lean_object* v_elems_937_; size_t v_sz_938_; size_t v___x_939_; lean_object* v___x_940_; 
v_elems_937_ = lean_ctor_get(v_x_936_, 0);
lean_inc_ref(v_elems_937_);
lean_dec_ref(v_x_936_);
v_sz_938_ = lean_array_size(v_elems_937_);
v___x_939_ = ((size_t)0ULL);
v___x_940_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__1_spec__1_spec__2(v_sz_938_, v___x_939_, v_elems_937_);
return v___x_940_;
}
else
{
lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; 
v___x_941_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__1_spec__1___closed__0));
v___x_942_ = lean_unsigned_to_nat(80u);
v___x_943_ = l_Lean_Json_pretty(v_x_936_, v___x_942_);
v___x_944_ = lean_string_append(v___x_941_, v___x_943_);
lean_dec_ref(v___x_943_);
v___x_945_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressKind___lam__0___closed__1));
v___x_946_ = lean_string_append(v___x_944_, v___x_945_);
v___x_947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_947_, 0, v___x_946_);
return v___x_947_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__1(lean_object* v_j_948_, lean_object* v_k_949_){
_start:
{
lean_object* v___x_950_; lean_object* v___x_951_; 
v___x_950_ = l_Lean_Json_getObjValD(v_j_948_, v_k_949_);
v___x_951_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__1_spec__1(v___x_950_);
return v___x_951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__1___boxed(lean_object* v_j_952_, lean_object* v_k_953_){
_start:
{
lean_object* v_res_954_; 
v_res_954_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__1(v_j_952_, v_k_953_);
lean_dec_ref(v_k_953_);
return v_res_954_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__2(void){
_start:
{
uint8_t v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; 
v___x_960_ = 1;
v___x_961_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__1));
v___x_962_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_961_, v___x_960_);
return v___x_962_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__3(void){
_start:
{
lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; 
v___x_963_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6));
v___x_964_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__2, &l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__2);
v___x_965_ = lean_string_append(v___x_964_, v___x_963_);
return v___x_965_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; 
v___x_966_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9, &l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9);
v___x_967_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__3);
v___x_968_ = lean_string_append(v___x_967_, v___x_966_);
return v___x_968_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__5(void){
_start:
{
lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; 
v___x_969_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_970_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__4);
v___x_971_ = lean_string_append(v___x_970_, v___x_969_);
return v___x_971_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__8(void){
_start:
{
uint8_t v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; 
v___x_975_ = 1;
v___x_976_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__7));
v___x_977_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_976_, v___x_975_);
return v___x_977_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__9(void){
_start:
{
lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; 
v___x_978_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__8);
v___x_979_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__3);
v___x_980_ = lean_string_append(v___x_979_, v___x_978_);
return v___x_980_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__10(void){
_start:
{
lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; 
v___x_981_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_982_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__9, &l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__9);
v___x_983_ = lean_string_append(v___x_982_, v___x_981_);
return v___x_983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson(lean_object* v_json_984_){
_start:
{
lean_object* v___x_985_; lean_object* v___x_986_; 
v___x_985_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__0));
lean_inc(v_json_984_);
v___x_986_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__0(v_json_984_, v___x_985_);
if (lean_obj_tag(v___x_986_) == 0)
{
lean_object* v_a_987_; lean_object* v___x_989_; uint8_t v_isShared_990_; uint8_t v_isSharedCheck_996_; 
lean_dec(v_json_984_);
v_a_987_ = lean_ctor_get(v___x_986_, 0);
v_isSharedCheck_996_ = !lean_is_exclusive(v___x_986_);
if (v_isSharedCheck_996_ == 0)
{
v___x_989_ = v___x_986_;
v_isShared_990_ = v_isSharedCheck_996_;
goto v_resetjp_988_;
}
else
{
lean_inc(v_a_987_);
lean_dec(v___x_986_);
v___x_989_ = lean_box(0);
v_isShared_990_ = v_isSharedCheck_996_;
goto v_resetjp_988_;
}
v_resetjp_988_:
{
lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_994_; 
v___x_991_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__5, &l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__5);
v___x_992_ = lean_string_append(v___x_991_, v_a_987_);
lean_dec(v_a_987_);
if (v_isShared_990_ == 0)
{
lean_ctor_set(v___x_989_, 0, v___x_992_);
v___x_994_ = v___x_989_;
goto v_reusejp_993_;
}
else
{
lean_object* v_reuseFailAlloc_995_; 
v_reuseFailAlloc_995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_995_, 0, v___x_992_);
v___x_994_ = v_reuseFailAlloc_995_;
goto v_reusejp_993_;
}
v_reusejp_993_:
{
return v___x_994_;
}
}
}
else
{
if (lean_obj_tag(v___x_986_) == 0)
{
lean_object* v_a_997_; lean_object* v___x_999_; uint8_t v_isShared_1000_; uint8_t v_isSharedCheck_1004_; 
lean_dec(v_json_984_);
v_a_997_ = lean_ctor_get(v___x_986_, 0);
v_isSharedCheck_1004_ = !lean_is_exclusive(v___x_986_);
if (v_isSharedCheck_1004_ == 0)
{
v___x_999_ = v___x_986_;
v_isShared_1000_ = v_isSharedCheck_1004_;
goto v_resetjp_998_;
}
else
{
lean_inc(v_a_997_);
lean_dec(v___x_986_);
v___x_999_ = lean_box(0);
v_isShared_1000_ = v_isSharedCheck_1004_;
goto v_resetjp_998_;
}
v_resetjp_998_:
{
lean_object* v___x_1002_; 
if (v_isShared_1000_ == 0)
{
lean_ctor_set_tag(v___x_999_, 0);
v___x_1002_ = v___x_999_;
goto v_reusejp_1001_;
}
else
{
lean_object* v_reuseFailAlloc_1003_; 
v_reuseFailAlloc_1003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1003_, 0, v_a_997_);
v___x_1002_ = v_reuseFailAlloc_1003_;
goto v_reusejp_1001_;
}
v_reusejp_1001_:
{
return v___x_1002_;
}
}
}
else
{
lean_object* v_a_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; 
v_a_1005_ = lean_ctor_get(v___x_986_, 0);
lean_inc(v_a_1005_);
lean_dec_ref(v___x_986_);
v___x_1006_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__6));
v___x_1007_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__1(v_json_984_, v___x_1006_);
if (lean_obj_tag(v___x_1007_) == 0)
{
lean_object* v_a_1008_; lean_object* v___x_1010_; uint8_t v_isShared_1011_; uint8_t v_isSharedCheck_1017_; 
lean_dec(v_a_1005_);
v_a_1008_ = lean_ctor_get(v___x_1007_, 0);
v_isSharedCheck_1017_ = !lean_is_exclusive(v___x_1007_);
if (v_isSharedCheck_1017_ == 0)
{
v___x_1010_ = v___x_1007_;
v_isShared_1011_ = v_isSharedCheck_1017_;
goto v_resetjp_1009_;
}
else
{
lean_inc(v_a_1008_);
lean_dec(v___x_1007_);
v___x_1010_ = lean_box(0);
v_isShared_1011_ = v_isSharedCheck_1017_;
goto v_resetjp_1009_;
}
v_resetjp_1009_:
{
lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1015_; 
v___x_1012_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__10, &l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__10);
v___x_1013_ = lean_string_append(v___x_1012_, v_a_1008_);
lean_dec(v_a_1008_);
if (v_isShared_1011_ == 0)
{
lean_ctor_set(v___x_1010_, 0, v___x_1013_);
v___x_1015_ = v___x_1010_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(0, 1, 0);
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
else
{
if (lean_obj_tag(v___x_1007_) == 0)
{
lean_object* v_a_1018_; lean_object* v___x_1020_; uint8_t v_isShared_1021_; uint8_t v_isSharedCheck_1025_; 
lean_dec(v_a_1005_);
v_a_1018_ = lean_ctor_get(v___x_1007_, 0);
v_isSharedCheck_1025_ = !lean_is_exclusive(v___x_1007_);
if (v_isSharedCheck_1025_ == 0)
{
v___x_1020_ = v___x_1007_;
v_isShared_1021_ = v_isSharedCheck_1025_;
goto v_resetjp_1019_;
}
else
{
lean_inc(v_a_1018_);
lean_dec(v___x_1007_);
v___x_1020_ = lean_box(0);
v_isShared_1021_ = v_isSharedCheck_1025_;
goto v_resetjp_1019_;
}
v_resetjp_1019_:
{
lean_object* v___x_1023_; 
if (v_isShared_1021_ == 0)
{
lean_ctor_set_tag(v___x_1020_, 0);
v___x_1023_ = v___x_1020_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v_a_1018_);
v___x_1023_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
return v___x_1023_;
}
}
}
else
{
lean_object* v_a_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1034_; 
v_a_1026_ = lean_ctor_get(v___x_1007_, 0);
v_isSharedCheck_1034_ = !lean_is_exclusive(v___x_1007_);
if (v_isSharedCheck_1034_ == 0)
{
v___x_1028_ = v___x_1007_;
v_isShared_1029_ = v_isSharedCheck_1034_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_a_1026_);
lean_dec(v___x_1007_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1034_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
lean_object* v___x_1030_; lean_object* v___x_1032_; 
v___x_1030_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1030_, 0, v_a_1005_);
lean_ctor_set(v___x_1030_, 1, v_a_1026_);
if (v_isShared_1029_ == 0)
{
lean_ctor_set(v___x_1028_, 0, v___x_1030_);
v___x_1032_ = v___x_1028_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v___x_1030_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanFileProgressParams_toJson_spec__0_spec__0(size_t v_sz_1037_, size_t v_i_1038_, lean_object* v_bs_1039_){
_start:
{
uint8_t v___x_1040_; 
v___x_1040_ = lean_usize_dec_lt(v_i_1038_, v_sz_1037_);
if (v___x_1040_ == 0)
{
return v_bs_1039_;
}
else
{
lean_object* v_v_1041_; lean_object* v___x_1042_; lean_object* v_bs_x27_1043_; lean_object* v___x_1044_; size_t v___x_1045_; size_t v___x_1046_; lean_object* v___x_1047_; 
v_v_1041_ = lean_array_uget(v_bs_1039_, v_i_1038_);
v___x_1042_ = lean_unsigned_to_nat(0u);
v_bs_x27_1043_ = lean_array_uset(v_bs_1039_, v_i_1038_, v___x_1042_);
v___x_1044_ = l_Lean_Lsp_instToJsonLeanFileProgressProcessingInfo_toJson(v_v_1041_);
v___x_1045_ = ((size_t)1ULL);
v___x_1046_ = lean_usize_add(v_i_1038_, v___x_1045_);
v___x_1047_ = lean_array_uset(v_bs_x27_1043_, v_i_1038_, v___x_1044_);
v_i_1038_ = v___x_1046_;
v_bs_1039_ = v___x_1047_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanFileProgressParams_toJson_spec__0_spec__0___boxed(lean_object* v_sz_1049_, lean_object* v_i_1050_, lean_object* v_bs_1051_){
_start:
{
size_t v_sz_boxed_1052_; size_t v_i_boxed_1053_; lean_object* v_res_1054_; 
v_sz_boxed_1052_ = lean_unbox_usize(v_sz_1049_);
lean_dec(v_sz_1049_);
v_i_boxed_1053_ = lean_unbox_usize(v_i_1050_);
lean_dec(v_i_1050_);
v_res_1054_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanFileProgressParams_toJson_spec__0_spec__0(v_sz_boxed_1052_, v_i_boxed_1053_, v_bs_1051_);
return v_res_1054_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Lsp_instToJsonLeanFileProgressParams_toJson_spec__0(lean_object* v_a_1055_){
_start:
{
size_t v_sz_1056_; size_t v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; 
v_sz_1056_ = lean_array_size(v_a_1055_);
v___x_1057_ = ((size_t)0ULL);
v___x_1058_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonLeanFileProgressParams_toJson_spec__0_spec__0(v_sz_1056_, v___x_1057_, v_a_1055_);
v___x_1059_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1059_, 0, v___x_1058_);
return v___x_1059_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanFileProgressParams_toJson(lean_object* v_x_1060_){
_start:
{
lean_object* v_textDocument_1061_; lean_object* v_processing_1062_; lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1082_; 
v_textDocument_1061_ = lean_ctor_get(v_x_1060_, 0);
v_processing_1062_ = lean_ctor_get(v_x_1060_, 1);
v_isSharedCheck_1082_ = !lean_is_exclusive(v_x_1060_);
if (v_isSharedCheck_1082_ == 0)
{
v___x_1064_ = v_x_1060_;
v_isShared_1065_ = v_isSharedCheck_1082_;
goto v_resetjp_1063_;
}
else
{
lean_inc(v_processing_1062_);
lean_inc(v_textDocument_1061_);
lean_dec(v_x_1060_);
v___x_1064_ = lean_box(0);
v_isShared_1065_ = v_isSharedCheck_1082_;
goto v_resetjp_1063_;
}
v_resetjp_1063_:
{
lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1069_; 
v___x_1066_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__0));
v___x_1067_ = l_Lean_Lsp_instToJsonVersionedTextDocumentIdentifier_toJson(v_textDocument_1061_);
if (v_isShared_1065_ == 0)
{
lean_ctor_set(v___x_1064_, 1, v___x_1067_);
lean_ctor_set(v___x_1064_, 0, v___x_1066_);
v___x_1069_ = v___x_1064_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v___x_1066_);
lean_ctor_set(v_reuseFailAlloc_1081_, 1, v___x_1067_);
v___x_1069_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; 
v___x_1070_ = lean_box(0);
v___x_1071_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1071_, 0, v___x_1069_);
lean_ctor_set(v___x_1071_, 1, v___x_1070_);
v___x_1072_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__6));
v___x_1073_ = l_Array_toJson___at___00Lean_Lsp_instToJsonLeanFileProgressParams_toJson_spec__0(v_processing_1062_);
v___x_1074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1074_, 0, v___x_1072_);
lean_ctor_set(v___x_1074_, 1, v___x_1073_);
v___x_1075_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1075_, 0, v___x_1074_);
lean_ctor_set(v___x_1075_, 1, v___x_1070_);
v___x_1076_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1076_, 0, v___x_1075_);
lean_ctor_set(v___x_1076_, 1, v___x_1070_);
v___x_1077_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1077_, 0, v___x_1071_);
lean_ctor_set(v___x_1077_, 1, v___x_1076_);
v___x_1078_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0));
v___x_1079_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_1077_, v___x_1078_);
v___x_1080_ = l_Lean_Json_mkObj(v___x_1079_);
lean_dec(v___x_1079_);
return v___x_1080_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoalParams_fromJson_spec__0(lean_object* v_j_1085_, lean_object* v_k_1086_){
_start:
{
lean_object* v___x_1087_; lean_object* v___x_1088_; 
v___x_1087_ = l_Lean_Json_getObjValD(v_j_1085_, v_k_1086_);
v___x_1088_ = l_Lean_Lsp_instFromJsonTextDocumentIdentifier_fromJson(v___x_1087_);
return v___x_1088_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoalParams_fromJson_spec__0___boxed(lean_object* v_j_1089_, lean_object* v_k_1090_){
_start:
{
lean_object* v_res_1091_; 
v_res_1091_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoalParams_fromJson_spec__0(v_j_1089_, v_k_1090_);
lean_dec_ref(v_k_1090_);
return v_res_1091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoalParams_fromJson_spec__1(lean_object* v_j_1092_, lean_object* v_k_1093_){
_start:
{
lean_object* v___x_1094_; lean_object* v___x_1095_; 
v___x_1094_ = l_Lean_Json_getObjValD(v_j_1092_, v_k_1093_);
v___x_1095_ = l_Lean_Lsp_instFromJsonPosition_fromJson(v___x_1094_);
return v___x_1095_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoalParams_fromJson_spec__1___boxed(lean_object* v_j_1096_, lean_object* v_k_1097_){
_start:
{
lean_object* v_res_1098_; 
v_res_1098_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoalParams_fromJson_spec__1(v_j_1096_, v_k_1097_);
lean_dec_ref(v_k_1097_);
return v_res_1098_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__2(void){
_start:
{
uint8_t v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; 
v___x_1104_ = 1;
v___x_1105_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__1));
v___x_1106_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1105_, v___x_1104_);
return v___x_1106_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__3(void){
_start:
{
lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; 
v___x_1107_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6));
v___x_1108_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__2, &l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__2);
v___x_1109_ = lean_string_append(v___x_1108_, v___x_1107_);
return v___x_1109_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; 
v___x_1110_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9, &l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9);
v___x_1111_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__3);
v___x_1112_ = lean_string_append(v___x_1111_, v___x_1110_);
return v___x_1112_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__5(void){
_start:
{
lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; 
v___x_1113_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_1114_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__4);
v___x_1115_ = lean_string_append(v___x_1114_, v___x_1113_);
return v___x_1115_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__8(void){
_start:
{
uint8_t v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; 
v___x_1119_ = 1;
v___x_1120_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__7));
v___x_1121_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1120_, v___x_1119_);
return v___x_1121_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__9(void){
_start:
{
lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; 
v___x_1122_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__8);
v___x_1123_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__3);
v___x_1124_ = lean_string_append(v___x_1123_, v___x_1122_);
return v___x_1124_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__10(void){
_start:
{
lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; 
v___x_1125_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_1126_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__9, &l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__9);
v___x_1127_ = lean_string_append(v___x_1126_, v___x_1125_);
return v___x_1127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson(lean_object* v_json_1128_){
_start:
{
lean_object* v___x_1129_; lean_object* v___x_1130_; 
v___x_1129_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__0));
lean_inc(v_json_1128_);
v___x_1130_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoalParams_fromJson_spec__0(v_json_1128_, v___x_1129_);
if (lean_obj_tag(v___x_1130_) == 0)
{
lean_object* v_a_1131_; lean_object* v___x_1133_; uint8_t v_isShared_1134_; uint8_t v_isSharedCheck_1140_; 
lean_dec(v_json_1128_);
v_a_1131_ = lean_ctor_get(v___x_1130_, 0);
v_isSharedCheck_1140_ = !lean_is_exclusive(v___x_1130_);
if (v_isSharedCheck_1140_ == 0)
{
v___x_1133_ = v___x_1130_;
v_isShared_1134_ = v_isSharedCheck_1140_;
goto v_resetjp_1132_;
}
else
{
lean_inc(v_a_1131_);
lean_dec(v___x_1130_);
v___x_1133_ = lean_box(0);
v_isShared_1134_ = v_isSharedCheck_1140_;
goto v_resetjp_1132_;
}
v_resetjp_1132_:
{
lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1138_; 
v___x_1135_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__5, &l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__5);
v___x_1136_ = lean_string_append(v___x_1135_, v_a_1131_);
lean_dec(v_a_1131_);
if (v_isShared_1134_ == 0)
{
lean_ctor_set(v___x_1133_, 0, v___x_1136_);
v___x_1138_ = v___x_1133_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v___x_1136_);
v___x_1138_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
return v___x_1138_;
}
}
}
else
{
if (lean_obj_tag(v___x_1130_) == 0)
{
lean_object* v_a_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1148_; 
lean_dec(v_json_1128_);
v_a_1141_ = lean_ctor_get(v___x_1130_, 0);
v_isSharedCheck_1148_ = !lean_is_exclusive(v___x_1130_);
if (v_isSharedCheck_1148_ == 0)
{
v___x_1143_ = v___x_1130_;
v_isShared_1144_ = v_isSharedCheck_1148_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_a_1141_);
lean_dec(v___x_1130_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1148_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
lean_object* v___x_1146_; 
if (v_isShared_1144_ == 0)
{
lean_ctor_set_tag(v___x_1143_, 0);
v___x_1146_ = v___x_1143_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v_a_1141_);
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
lean_object* v_a_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; 
v_a_1149_ = lean_ctor_get(v___x_1130_, 0);
lean_inc(v_a_1149_);
lean_dec_ref(v___x_1130_);
v___x_1150_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__6));
v___x_1151_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoalParams_fromJson_spec__1(v_json_1128_, v___x_1150_);
if (lean_obj_tag(v___x_1151_) == 0)
{
lean_object* v_a_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1161_; 
lean_dec(v_a_1149_);
v_a_1152_ = lean_ctor_get(v___x_1151_, 0);
v_isSharedCheck_1161_ = !lean_is_exclusive(v___x_1151_);
if (v_isSharedCheck_1161_ == 0)
{
v___x_1154_ = v___x_1151_;
v_isShared_1155_ = v_isSharedCheck_1161_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_a_1152_);
lean_dec(v___x_1151_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1161_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1159_; 
v___x_1156_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__10, &l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__10);
v___x_1157_ = lean_string_append(v___x_1156_, v_a_1152_);
lean_dec(v_a_1152_);
if (v_isShared_1155_ == 0)
{
lean_ctor_set(v___x_1154_, 0, v___x_1157_);
v___x_1159_ = v___x_1154_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1160_; 
v_reuseFailAlloc_1160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1160_, 0, v___x_1157_);
v___x_1159_ = v_reuseFailAlloc_1160_;
goto v_reusejp_1158_;
}
v_reusejp_1158_:
{
return v___x_1159_;
}
}
}
else
{
if (lean_obj_tag(v___x_1151_) == 0)
{
lean_object* v_a_1162_; lean_object* v___x_1164_; uint8_t v_isShared_1165_; uint8_t v_isSharedCheck_1169_; 
lean_dec(v_a_1149_);
v_a_1162_ = lean_ctor_get(v___x_1151_, 0);
v_isSharedCheck_1169_ = !lean_is_exclusive(v___x_1151_);
if (v_isSharedCheck_1169_ == 0)
{
v___x_1164_ = v___x_1151_;
v_isShared_1165_ = v_isSharedCheck_1169_;
goto v_resetjp_1163_;
}
else
{
lean_inc(v_a_1162_);
lean_dec(v___x_1151_);
v___x_1164_ = lean_box(0);
v_isShared_1165_ = v_isSharedCheck_1169_;
goto v_resetjp_1163_;
}
v_resetjp_1163_:
{
lean_object* v___x_1167_; 
if (v_isShared_1165_ == 0)
{
lean_ctor_set_tag(v___x_1164_, 0);
v___x_1167_ = v___x_1164_;
goto v_reusejp_1166_;
}
else
{
lean_object* v_reuseFailAlloc_1168_; 
v_reuseFailAlloc_1168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1168_, 0, v_a_1162_);
v___x_1167_ = v_reuseFailAlloc_1168_;
goto v_reusejp_1166_;
}
v_reusejp_1166_:
{
return v___x_1167_;
}
}
}
else
{
lean_object* v_a_1170_; lean_object* v___x_1172_; uint8_t v_isShared_1173_; uint8_t v_isSharedCheck_1178_; 
v_a_1170_ = lean_ctor_get(v___x_1151_, 0);
v_isSharedCheck_1178_ = !lean_is_exclusive(v___x_1151_);
if (v_isSharedCheck_1178_ == 0)
{
v___x_1172_ = v___x_1151_;
v_isShared_1173_ = v_isSharedCheck_1178_;
goto v_resetjp_1171_;
}
else
{
lean_inc(v_a_1170_);
lean_dec(v___x_1151_);
v___x_1172_ = lean_box(0);
v_isShared_1173_ = v_isSharedCheck_1178_;
goto v_resetjp_1171_;
}
v_resetjp_1171_:
{
lean_object* v___x_1174_; lean_object* v___x_1176_; 
v___x_1174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1174_, 0, v_a_1149_);
lean_ctor_set(v___x_1174_, 1, v_a_1170_);
if (v_isShared_1173_ == 0)
{
lean_ctor_set(v___x_1172_, 0, v___x_1174_);
v___x_1176_ = v___x_1172_;
goto v_reusejp_1175_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v___x_1174_);
v___x_1176_ = v_reuseFailAlloc_1177_;
goto v_reusejp_1175_;
}
v_reusejp_1175_:
{
return v___x_1176_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonPlainGoalParams_toJson(lean_object* v_x_1181_){
_start:
{
lean_object* v_textDocument_1182_; lean_object* v_position_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1203_; 
v_textDocument_1182_ = lean_ctor_get(v_x_1181_, 0);
v_position_1183_ = lean_ctor_get(v_x_1181_, 1);
v_isSharedCheck_1203_ = !lean_is_exclusive(v_x_1181_);
if (v_isSharedCheck_1203_ == 0)
{
v___x_1185_ = v_x_1181_;
v_isShared_1186_ = v_isSharedCheck_1203_;
goto v_resetjp_1184_;
}
else
{
lean_inc(v_position_1183_);
lean_inc(v_textDocument_1182_);
lean_dec(v_x_1181_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1203_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1190_; 
v___x_1187_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__0));
v___x_1188_ = l_Lean_Lsp_instToJsonTextDocumentIdentifier_toJson(v_textDocument_1182_);
if (v_isShared_1186_ == 0)
{
lean_ctor_set(v___x_1185_, 1, v___x_1188_);
lean_ctor_set(v___x_1185_, 0, v___x_1187_);
v___x_1190_ = v___x_1185_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v___x_1187_);
lean_ctor_set(v_reuseFailAlloc_1202_, 1, v___x_1188_);
v___x_1190_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; 
v___x_1191_ = lean_box(0);
v___x_1192_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1192_, 0, v___x_1190_);
lean_ctor_set(v___x_1192_, 1, v___x_1191_);
v___x_1193_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__6));
v___x_1194_ = l_Lean_Lsp_instToJsonPosition_toJson(v_position_1183_);
v___x_1195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1195_, 0, v___x_1193_);
lean_ctor_set(v___x_1195_, 1, v___x_1194_);
v___x_1196_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1196_, 0, v___x_1195_);
lean_ctor_set(v___x_1196_, 1, v___x_1191_);
v___x_1197_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1197_, 0, v___x_1196_);
lean_ctor_set(v___x_1197_, 1, v___x_1191_);
v___x_1198_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1198_, 0, v___x_1192_);
lean_ctor_set(v___x_1198_, 1, v___x_1197_);
v___x_1199_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0));
v___x_1200_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_1198_, v___x_1199_);
v___x_1201_ = l_Lean_Json_mkObj(v___x_1200_);
lean_dec(v___x_1200_);
return v___x_1201_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoal_fromJson_spec__0_spec__0_spec__1(size_t v_sz_1206_, size_t v_i_1207_, lean_object* v_bs_1208_){
_start:
{
uint8_t v___x_1209_; 
v___x_1209_ = lean_usize_dec_lt(v_i_1207_, v_sz_1206_);
if (v___x_1209_ == 0)
{
lean_object* v___x_1210_; 
v___x_1210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1210_, 0, v_bs_1208_);
return v___x_1210_;
}
else
{
lean_object* v_v_1211_; lean_object* v___x_1212_; 
v_v_1211_ = lean_array_uget_borrowed(v_bs_1208_, v_i_1207_);
lean_inc(v_v_1211_);
v___x_1212_ = l_Lean_Json_getStr_x3f(v_v_1211_);
if (lean_obj_tag(v___x_1212_) == 0)
{
lean_object* v_a_1213_; lean_object* v___x_1215_; uint8_t v_isShared_1216_; uint8_t v_isSharedCheck_1220_; 
lean_dec_ref(v_bs_1208_);
v_a_1213_ = lean_ctor_get(v___x_1212_, 0);
v_isSharedCheck_1220_ = !lean_is_exclusive(v___x_1212_);
if (v_isSharedCheck_1220_ == 0)
{
v___x_1215_ = v___x_1212_;
v_isShared_1216_ = v_isSharedCheck_1220_;
goto v_resetjp_1214_;
}
else
{
lean_inc(v_a_1213_);
lean_dec(v___x_1212_);
v___x_1215_ = lean_box(0);
v_isShared_1216_ = v_isSharedCheck_1220_;
goto v_resetjp_1214_;
}
v_resetjp_1214_:
{
lean_object* v___x_1218_; 
if (v_isShared_1216_ == 0)
{
v___x_1218_ = v___x_1215_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v_a_1213_);
v___x_1218_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1217_;
}
v_reusejp_1217_:
{
return v___x_1218_;
}
}
}
else
{
lean_object* v_a_1221_; lean_object* v___x_1222_; lean_object* v_bs_x27_1223_; size_t v___x_1224_; size_t v___x_1225_; lean_object* v___x_1226_; 
v_a_1221_ = lean_ctor_get(v___x_1212_, 0);
lean_inc(v_a_1221_);
lean_dec_ref(v___x_1212_);
v___x_1222_ = lean_unsigned_to_nat(0u);
v_bs_x27_1223_ = lean_array_uset(v_bs_1208_, v_i_1207_, v___x_1222_);
v___x_1224_ = ((size_t)1ULL);
v___x_1225_ = lean_usize_add(v_i_1207_, v___x_1224_);
v___x_1226_ = lean_array_uset(v_bs_x27_1223_, v_i_1207_, v_a_1221_);
v_i_1207_ = v___x_1225_;
v_bs_1208_ = v___x_1226_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoal_fromJson_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_1228_, lean_object* v_i_1229_, lean_object* v_bs_1230_){
_start:
{
size_t v_sz_boxed_1231_; size_t v_i_boxed_1232_; lean_object* v_res_1233_; 
v_sz_boxed_1231_ = lean_unbox_usize(v_sz_1228_);
lean_dec(v_sz_1228_);
v_i_boxed_1232_ = lean_unbox_usize(v_i_1229_);
lean_dec(v_i_1229_);
v_res_1233_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoal_fromJson_spec__0_spec__0_spec__1(v_sz_boxed_1231_, v_i_boxed_1232_, v_bs_1230_);
return v_res_1233_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoal_fromJson_spec__0_spec__0(lean_object* v_x_1234_){
_start:
{
if (lean_obj_tag(v_x_1234_) == 4)
{
lean_object* v_elems_1235_; size_t v_sz_1236_; size_t v___x_1237_; lean_object* v___x_1238_; 
v_elems_1235_ = lean_ctor_get(v_x_1234_, 0);
lean_inc_ref(v_elems_1235_);
lean_dec_ref(v_x_1234_);
v_sz_1236_ = lean_array_size(v_elems_1235_);
v___x_1237_ = ((size_t)0ULL);
v___x_1238_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoal_fromJson_spec__0_spec__0_spec__1(v_sz_1236_, v___x_1237_, v_elems_1235_);
return v___x_1238_;
}
else
{
lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; 
v___x_1239_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__1_spec__1___closed__0));
v___x_1240_ = lean_unsigned_to_nat(80u);
v___x_1241_ = l_Lean_Json_pretty(v_x_1234_, v___x_1240_);
v___x_1242_ = lean_string_append(v___x_1239_, v___x_1241_);
lean_dec_ref(v___x_1241_);
v___x_1243_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressKind___lam__0___closed__1));
v___x_1244_ = lean_string_append(v___x_1242_, v___x_1243_);
v___x_1245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1245_, 0, v___x_1244_);
return v___x_1245_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoal_fromJson_spec__0(lean_object* v_j_1246_, lean_object* v_k_1247_){
_start:
{
lean_object* v___x_1248_; lean_object* v___x_1249_; 
v___x_1248_ = l_Lean_Json_getObjValD(v_j_1246_, v_k_1247_);
v___x_1249_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoal_fromJson_spec__0_spec__0(v___x_1248_);
return v___x_1249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoal_fromJson_spec__0___boxed(lean_object* v_j_1250_, lean_object* v_k_1251_){
_start:
{
lean_object* v_res_1252_; 
v_res_1252_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoal_fromJson_spec__0(v_j_1250_, v_k_1251_);
lean_dec_ref(v_k_1251_);
return v_res_1252_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__3(void){
_start:
{
uint8_t v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; 
v___x_1259_ = 1;
v___x_1260_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__2));
v___x_1261_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1260_, v___x_1259_);
return v___x_1261_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__4(void){
_start:
{
lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; 
v___x_1262_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6));
v___x_1263_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__3, &l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__3);
v___x_1264_ = lean_string_append(v___x_1263_, v___x_1262_);
return v___x_1264_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__6(void){
_start:
{
uint8_t v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; 
v___x_1267_ = 1;
v___x_1268_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__5));
v___x_1269_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1268_, v___x_1267_);
return v___x_1269_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__7(void){
_start:
{
lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; 
v___x_1270_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__6, &l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__6);
v___x_1271_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__4, &l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__4);
v___x_1272_ = lean_string_append(v___x_1271_, v___x_1270_);
return v___x_1272_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__8(void){
_start:
{
lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; 
v___x_1273_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_1274_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__7, &l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__7);
v___x_1275_ = lean_string_append(v___x_1274_, v___x_1273_);
return v___x_1275_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__11(void){
_start:
{
uint8_t v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; 
v___x_1279_ = 1;
v___x_1280_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__10));
v___x_1281_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1280_, v___x_1279_);
return v___x_1281_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__12(void){
_start:
{
lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; 
v___x_1282_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__11, &l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__11);
v___x_1283_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__4, &l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__4);
v___x_1284_ = lean_string_append(v___x_1283_, v___x_1282_);
return v___x_1284_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__13(void){
_start:
{
lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; 
v___x_1285_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_1286_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__12, &l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__12);
v___x_1287_ = lean_string_append(v___x_1286_, v___x_1285_);
return v___x_1287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonPlainGoal_fromJson(lean_object* v_json_1288_){
_start:
{
lean_object* v___x_1289_; lean_object* v___x_1290_; 
v___x_1289_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__0));
lean_inc(v_json_1288_);
v___x_1290_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson_spec__0(v_json_1288_, v___x_1289_);
if (lean_obj_tag(v___x_1290_) == 0)
{
lean_object* v_a_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1300_; 
lean_dec(v_json_1288_);
v_a_1291_ = lean_ctor_get(v___x_1290_, 0);
v_isSharedCheck_1300_ = !lean_is_exclusive(v___x_1290_);
if (v_isSharedCheck_1300_ == 0)
{
v___x_1293_ = v___x_1290_;
v_isShared_1294_ = v_isSharedCheck_1300_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_a_1291_);
lean_dec(v___x_1290_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1300_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1298_; 
v___x_1295_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__8, &l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__8);
v___x_1296_ = lean_string_append(v___x_1295_, v_a_1291_);
lean_dec(v_a_1291_);
if (v_isShared_1294_ == 0)
{
lean_ctor_set(v___x_1293_, 0, v___x_1296_);
v___x_1298_ = v___x_1293_;
goto v_reusejp_1297_;
}
else
{
lean_object* v_reuseFailAlloc_1299_; 
v_reuseFailAlloc_1299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1299_, 0, v___x_1296_);
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
if (lean_obj_tag(v___x_1290_) == 0)
{
lean_object* v_a_1301_; lean_object* v___x_1303_; uint8_t v_isShared_1304_; uint8_t v_isSharedCheck_1308_; 
lean_dec(v_json_1288_);
v_a_1301_ = lean_ctor_get(v___x_1290_, 0);
v_isSharedCheck_1308_ = !lean_is_exclusive(v___x_1290_);
if (v_isSharedCheck_1308_ == 0)
{
v___x_1303_ = v___x_1290_;
v_isShared_1304_ = v_isSharedCheck_1308_;
goto v_resetjp_1302_;
}
else
{
lean_inc(v_a_1301_);
lean_dec(v___x_1290_);
v___x_1303_ = lean_box(0);
v_isShared_1304_ = v_isSharedCheck_1308_;
goto v_resetjp_1302_;
}
v_resetjp_1302_:
{
lean_object* v___x_1306_; 
if (v_isShared_1304_ == 0)
{
lean_ctor_set_tag(v___x_1303_, 0);
v___x_1306_ = v___x_1303_;
goto v_reusejp_1305_;
}
else
{
lean_object* v_reuseFailAlloc_1307_; 
v_reuseFailAlloc_1307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1307_, 0, v_a_1301_);
v___x_1306_ = v_reuseFailAlloc_1307_;
goto v_reusejp_1305_;
}
v_reusejp_1305_:
{
return v___x_1306_;
}
}
}
else
{
lean_object* v_a_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; 
v_a_1309_ = lean_ctor_get(v___x_1290_, 0);
lean_inc(v_a_1309_);
lean_dec_ref(v___x_1290_);
v___x_1310_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__9));
v___x_1311_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoal_fromJson_spec__0(v_json_1288_, v___x_1310_);
if (lean_obj_tag(v___x_1311_) == 0)
{
lean_object* v_a_1312_; lean_object* v___x_1314_; uint8_t v_isShared_1315_; uint8_t v_isSharedCheck_1321_; 
lean_dec(v_a_1309_);
v_a_1312_ = lean_ctor_get(v___x_1311_, 0);
v_isSharedCheck_1321_ = !lean_is_exclusive(v___x_1311_);
if (v_isSharedCheck_1321_ == 0)
{
v___x_1314_ = v___x_1311_;
v_isShared_1315_ = v_isSharedCheck_1321_;
goto v_resetjp_1313_;
}
else
{
lean_inc(v_a_1312_);
lean_dec(v___x_1311_);
v___x_1314_ = lean_box(0);
v_isShared_1315_ = v_isSharedCheck_1321_;
goto v_resetjp_1313_;
}
v_resetjp_1313_:
{
lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1319_; 
v___x_1316_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__13, &l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__13);
v___x_1317_ = lean_string_append(v___x_1316_, v_a_1312_);
lean_dec(v_a_1312_);
if (v_isShared_1315_ == 0)
{
lean_ctor_set(v___x_1314_, 0, v___x_1317_);
v___x_1319_ = v___x_1314_;
goto v_reusejp_1318_;
}
else
{
lean_object* v_reuseFailAlloc_1320_; 
v_reuseFailAlloc_1320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1320_, 0, v___x_1317_);
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
if (lean_obj_tag(v___x_1311_) == 0)
{
lean_object* v_a_1322_; lean_object* v___x_1324_; uint8_t v_isShared_1325_; uint8_t v_isSharedCheck_1329_; 
lean_dec(v_a_1309_);
v_a_1322_ = lean_ctor_get(v___x_1311_, 0);
v_isSharedCheck_1329_ = !lean_is_exclusive(v___x_1311_);
if (v_isSharedCheck_1329_ == 0)
{
v___x_1324_ = v___x_1311_;
v_isShared_1325_ = v_isSharedCheck_1329_;
goto v_resetjp_1323_;
}
else
{
lean_inc(v_a_1322_);
lean_dec(v___x_1311_);
v___x_1324_ = lean_box(0);
v_isShared_1325_ = v_isSharedCheck_1329_;
goto v_resetjp_1323_;
}
v_resetjp_1323_:
{
lean_object* v___x_1327_; 
if (v_isShared_1325_ == 0)
{
lean_ctor_set_tag(v___x_1324_, 0);
v___x_1327_ = v___x_1324_;
goto v_reusejp_1326_;
}
else
{
lean_object* v_reuseFailAlloc_1328_; 
v_reuseFailAlloc_1328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1328_, 0, v_a_1322_);
v___x_1327_ = v_reuseFailAlloc_1328_;
goto v_reusejp_1326_;
}
v_reusejp_1326_:
{
return v___x_1327_;
}
}
}
else
{
lean_object* v_a_1330_; lean_object* v___x_1332_; uint8_t v_isShared_1333_; uint8_t v_isSharedCheck_1338_; 
v_a_1330_ = lean_ctor_get(v___x_1311_, 0);
v_isSharedCheck_1338_ = !lean_is_exclusive(v___x_1311_);
if (v_isSharedCheck_1338_ == 0)
{
v___x_1332_ = v___x_1311_;
v_isShared_1333_ = v_isSharedCheck_1338_;
goto v_resetjp_1331_;
}
else
{
lean_inc(v_a_1330_);
lean_dec(v___x_1311_);
v___x_1332_ = lean_box(0);
v_isShared_1333_ = v_isSharedCheck_1338_;
goto v_resetjp_1331_;
}
v_resetjp_1331_:
{
lean_object* v___x_1334_; lean_object* v___x_1336_; 
v___x_1334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1334_, 0, v_a_1309_);
lean_ctor_set(v___x_1334_, 1, v_a_1330_);
if (v_isShared_1333_ == 0)
{
lean_ctor_set(v___x_1332_, 0, v___x_1334_);
v___x_1336_ = v___x_1332_;
goto v_reusejp_1335_;
}
else
{
lean_object* v_reuseFailAlloc_1337_; 
v_reuseFailAlloc_1337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1337_, 0, v___x_1334_);
v___x_1336_ = v_reuseFailAlloc_1337_;
goto v_reusejp_1335_;
}
v_reusejp_1335_:
{
return v___x_1336_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonPlainGoal_toJson_spec__0_spec__0(size_t v_sz_1341_, size_t v_i_1342_, lean_object* v_bs_1343_){
_start:
{
uint8_t v___x_1344_; 
v___x_1344_ = lean_usize_dec_lt(v_i_1342_, v_sz_1341_);
if (v___x_1344_ == 0)
{
return v_bs_1343_;
}
else
{
lean_object* v_v_1345_; lean_object* v___x_1346_; lean_object* v_bs_x27_1347_; lean_object* v___x_1348_; size_t v___x_1349_; size_t v___x_1350_; lean_object* v___x_1351_; 
v_v_1345_ = lean_array_uget(v_bs_1343_, v_i_1342_);
v___x_1346_ = lean_unsigned_to_nat(0u);
v_bs_x27_1347_ = lean_array_uset(v_bs_1343_, v_i_1342_, v___x_1346_);
v___x_1348_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1348_, 0, v_v_1345_);
v___x_1349_ = ((size_t)1ULL);
v___x_1350_ = lean_usize_add(v_i_1342_, v___x_1349_);
v___x_1351_ = lean_array_uset(v_bs_x27_1347_, v_i_1342_, v___x_1348_);
v_i_1342_ = v___x_1350_;
v_bs_1343_ = v___x_1351_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonPlainGoal_toJson_spec__0_spec__0___boxed(lean_object* v_sz_1353_, lean_object* v_i_1354_, lean_object* v_bs_1355_){
_start:
{
size_t v_sz_boxed_1356_; size_t v_i_boxed_1357_; lean_object* v_res_1358_; 
v_sz_boxed_1356_ = lean_unbox_usize(v_sz_1353_);
lean_dec(v_sz_1353_);
v_i_boxed_1357_ = lean_unbox_usize(v_i_1354_);
lean_dec(v_i_1354_);
v_res_1358_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonPlainGoal_toJson_spec__0_spec__0(v_sz_boxed_1356_, v_i_boxed_1357_, v_bs_1355_);
return v_res_1358_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Lsp_instToJsonPlainGoal_toJson_spec__0(lean_object* v_a_1359_){
_start:
{
size_t v_sz_1360_; size_t v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; 
v_sz_1360_ = lean_array_size(v_a_1359_);
v___x_1361_ = ((size_t)0ULL);
v___x_1362_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonPlainGoal_toJson_spec__0_spec__0(v_sz_1360_, v___x_1361_, v_a_1359_);
v___x_1363_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1363_, 0, v___x_1362_);
return v___x_1363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonPlainGoal_toJson(lean_object* v_x_1364_){
_start:
{
lean_object* v_rendered_1365_; lean_object* v_goals_1366_; lean_object* v___x_1368_; uint8_t v_isShared_1369_; uint8_t v_isSharedCheck_1386_; 
v_rendered_1365_ = lean_ctor_get(v_x_1364_, 0);
v_goals_1366_ = lean_ctor_get(v_x_1364_, 1);
v_isSharedCheck_1386_ = !lean_is_exclusive(v_x_1364_);
if (v_isSharedCheck_1386_ == 0)
{
v___x_1368_ = v_x_1364_;
v_isShared_1369_ = v_isSharedCheck_1386_;
goto v_resetjp_1367_;
}
else
{
lean_inc(v_goals_1366_);
lean_inc(v_rendered_1365_);
lean_dec(v_x_1364_);
v___x_1368_ = lean_box(0);
v_isShared_1369_ = v_isSharedCheck_1386_;
goto v_resetjp_1367_;
}
v_resetjp_1367_:
{
lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1373_; 
v___x_1370_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__0));
v___x_1371_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1371_, 0, v_rendered_1365_);
if (v_isShared_1369_ == 0)
{
lean_ctor_set(v___x_1368_, 1, v___x_1371_);
lean_ctor_set(v___x_1368_, 0, v___x_1370_);
v___x_1373_ = v___x_1368_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v___x_1370_);
lean_ctor_set(v_reuseFailAlloc_1385_, 1, v___x_1371_);
v___x_1373_ = v_reuseFailAlloc_1385_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; 
v___x_1374_ = lean_box(0);
v___x_1375_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1375_, 0, v___x_1373_);
lean_ctor_set(v___x_1375_, 1, v___x_1374_);
v___x_1376_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__9));
v___x_1377_ = l_Array_toJson___at___00Lean_Lsp_instToJsonPlainGoal_toJson_spec__0(v_goals_1366_);
v___x_1378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1378_, 0, v___x_1376_);
lean_ctor_set(v___x_1378_, 1, v___x_1377_);
v___x_1379_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1379_, 0, v___x_1378_);
lean_ctor_set(v___x_1379_, 1, v___x_1374_);
v___x_1380_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1380_, 0, v___x_1379_);
lean_ctor_set(v___x_1380_, 1, v___x_1374_);
v___x_1381_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1381_, 0, v___x_1375_);
lean_ctor_set(v___x_1381_, 1, v___x_1380_);
v___x_1382_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0));
v___x_1383_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_1381_, v___x_1382_);
v___x_1384_ = l_Lean_Json_mkObj(v___x_1383_);
lean_dec(v___x_1383_);
return v___x_1384_;
}
}
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__2(void){
_start:
{
uint8_t v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; 
v___x_1394_ = 1;
v___x_1395_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__1));
v___x_1396_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1395_, v___x_1394_);
return v___x_1396_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__3(void){
_start:
{
lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; 
v___x_1397_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6));
v___x_1398_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__2, &l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__2);
v___x_1399_ = lean_string_append(v___x_1398_, v___x_1397_);
return v___x_1399_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; 
v___x_1400_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9, &l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9);
v___x_1401_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__3);
v___x_1402_ = lean_string_append(v___x_1401_, v___x_1400_);
return v___x_1402_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__5(void){
_start:
{
lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; 
v___x_1403_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_1404_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__4);
v___x_1405_ = lean_string_append(v___x_1404_, v___x_1403_);
return v___x_1405_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__6(void){
_start:
{
lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; 
v___x_1406_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__8);
v___x_1407_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__3);
v___x_1408_ = lean_string_append(v___x_1407_, v___x_1406_);
return v___x_1408_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__7(void){
_start:
{
lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; 
v___x_1409_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_1410_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__6, &l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__6);
v___x_1411_ = lean_string_append(v___x_1410_, v___x_1409_);
return v___x_1411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson(lean_object* v_json_1412_){
_start:
{
lean_object* v___x_1413_; lean_object* v___x_1414_; 
v___x_1413_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__0));
lean_inc(v_json_1412_);
v___x_1414_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoalParams_fromJson_spec__0(v_json_1412_, v___x_1413_);
if (lean_obj_tag(v___x_1414_) == 0)
{
lean_object* v_a_1415_; lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1424_; 
lean_dec(v_json_1412_);
v_a_1415_ = lean_ctor_get(v___x_1414_, 0);
v_isSharedCheck_1424_ = !lean_is_exclusive(v___x_1414_);
if (v_isSharedCheck_1424_ == 0)
{
v___x_1417_ = v___x_1414_;
v_isShared_1418_ = v_isSharedCheck_1424_;
goto v_resetjp_1416_;
}
else
{
lean_inc(v_a_1415_);
lean_dec(v___x_1414_);
v___x_1417_ = lean_box(0);
v_isShared_1418_ = v_isSharedCheck_1424_;
goto v_resetjp_1416_;
}
v_resetjp_1416_:
{
lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1422_; 
v___x_1419_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__5, &l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__5);
v___x_1420_ = lean_string_append(v___x_1419_, v_a_1415_);
lean_dec(v_a_1415_);
if (v_isShared_1418_ == 0)
{
lean_ctor_set(v___x_1417_, 0, v___x_1420_);
v___x_1422_ = v___x_1417_;
goto v_reusejp_1421_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v___x_1420_);
v___x_1422_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1421_;
}
v_reusejp_1421_:
{
return v___x_1422_;
}
}
}
else
{
if (lean_obj_tag(v___x_1414_) == 0)
{
lean_object* v_a_1425_; lean_object* v___x_1427_; uint8_t v_isShared_1428_; uint8_t v_isSharedCheck_1432_; 
lean_dec(v_json_1412_);
v_a_1425_ = lean_ctor_get(v___x_1414_, 0);
v_isSharedCheck_1432_ = !lean_is_exclusive(v___x_1414_);
if (v_isSharedCheck_1432_ == 0)
{
v___x_1427_ = v___x_1414_;
v_isShared_1428_ = v_isSharedCheck_1432_;
goto v_resetjp_1426_;
}
else
{
lean_inc(v_a_1425_);
lean_dec(v___x_1414_);
v___x_1427_ = lean_box(0);
v_isShared_1428_ = v_isSharedCheck_1432_;
goto v_resetjp_1426_;
}
v_resetjp_1426_:
{
lean_object* v___x_1430_; 
if (v_isShared_1428_ == 0)
{
lean_ctor_set_tag(v___x_1427_, 0);
v___x_1430_ = v___x_1427_;
goto v_reusejp_1429_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v_a_1425_);
v___x_1430_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1429_;
}
v_reusejp_1429_:
{
return v___x_1430_;
}
}
}
else
{
lean_object* v_a_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; 
v_a_1433_ = lean_ctor_get(v___x_1414_, 0);
lean_inc(v_a_1433_);
lean_dec_ref(v___x_1414_);
v___x_1434_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__6));
v___x_1435_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoalParams_fromJson_spec__1(v_json_1412_, v___x_1434_);
if (lean_obj_tag(v___x_1435_) == 0)
{
lean_object* v_a_1436_; lean_object* v___x_1438_; uint8_t v_isShared_1439_; uint8_t v_isSharedCheck_1445_; 
lean_dec(v_a_1433_);
v_a_1436_ = lean_ctor_get(v___x_1435_, 0);
v_isSharedCheck_1445_ = !lean_is_exclusive(v___x_1435_);
if (v_isSharedCheck_1445_ == 0)
{
v___x_1438_ = v___x_1435_;
v_isShared_1439_ = v_isSharedCheck_1445_;
goto v_resetjp_1437_;
}
else
{
lean_inc(v_a_1436_);
lean_dec(v___x_1435_);
v___x_1438_ = lean_box(0);
v_isShared_1439_ = v_isSharedCheck_1445_;
goto v_resetjp_1437_;
}
v_resetjp_1437_:
{
lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1443_; 
v___x_1440_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__7);
v___x_1441_ = lean_string_append(v___x_1440_, v_a_1436_);
lean_dec(v_a_1436_);
if (v_isShared_1439_ == 0)
{
lean_ctor_set(v___x_1438_, 0, v___x_1441_);
v___x_1443_ = v___x_1438_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v___x_1441_);
v___x_1443_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
return v___x_1443_;
}
}
}
else
{
if (lean_obj_tag(v___x_1435_) == 0)
{
lean_object* v_a_1446_; lean_object* v___x_1448_; uint8_t v_isShared_1449_; uint8_t v_isSharedCheck_1453_; 
lean_dec(v_a_1433_);
v_a_1446_ = lean_ctor_get(v___x_1435_, 0);
v_isSharedCheck_1453_ = !lean_is_exclusive(v___x_1435_);
if (v_isSharedCheck_1453_ == 0)
{
v___x_1448_ = v___x_1435_;
v_isShared_1449_ = v_isSharedCheck_1453_;
goto v_resetjp_1447_;
}
else
{
lean_inc(v_a_1446_);
lean_dec(v___x_1435_);
v___x_1448_ = lean_box(0);
v_isShared_1449_ = v_isSharedCheck_1453_;
goto v_resetjp_1447_;
}
v_resetjp_1447_:
{
lean_object* v___x_1451_; 
if (v_isShared_1449_ == 0)
{
lean_ctor_set_tag(v___x_1448_, 0);
v___x_1451_ = v___x_1448_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1452_; 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v_a_1446_);
v___x_1451_ = v_reuseFailAlloc_1452_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
return v___x_1451_;
}
}
}
else
{
lean_object* v_a_1454_; lean_object* v___x_1456_; uint8_t v_isShared_1457_; uint8_t v_isSharedCheck_1462_; 
v_a_1454_ = lean_ctor_get(v___x_1435_, 0);
v_isSharedCheck_1462_ = !lean_is_exclusive(v___x_1435_);
if (v_isSharedCheck_1462_ == 0)
{
v___x_1456_ = v___x_1435_;
v_isShared_1457_ = v_isSharedCheck_1462_;
goto v_resetjp_1455_;
}
else
{
lean_inc(v_a_1454_);
lean_dec(v___x_1435_);
v___x_1456_ = lean_box(0);
v_isShared_1457_ = v_isSharedCheck_1462_;
goto v_resetjp_1455_;
}
v_resetjp_1455_:
{
lean_object* v___x_1458_; lean_object* v___x_1460_; 
v___x_1458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1458_, 0, v_a_1433_);
lean_ctor_set(v___x_1458_, 1, v_a_1454_);
if (v_isShared_1457_ == 0)
{
lean_ctor_set(v___x_1456_, 0, v___x_1458_);
v___x_1460_ = v___x_1456_;
goto v_reusejp_1459_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v___x_1458_);
v___x_1460_ = v_reuseFailAlloc_1461_;
goto v_reusejp_1459_;
}
v_reusejp_1459_:
{
return v___x_1460_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonPlainTermGoalParams_toJson(lean_object* v_x_1465_){
_start:
{
lean_object* v_textDocument_1466_; lean_object* v_position_1467_; lean_object* v___x_1469_; uint8_t v_isShared_1470_; uint8_t v_isSharedCheck_1487_; 
v_textDocument_1466_ = lean_ctor_get(v_x_1465_, 0);
v_position_1467_ = lean_ctor_get(v_x_1465_, 1);
v_isSharedCheck_1487_ = !lean_is_exclusive(v_x_1465_);
if (v_isSharedCheck_1487_ == 0)
{
v___x_1469_ = v_x_1465_;
v_isShared_1470_ = v_isSharedCheck_1487_;
goto v_resetjp_1468_;
}
else
{
lean_inc(v_position_1467_);
lean_inc(v_textDocument_1466_);
lean_dec(v_x_1465_);
v___x_1469_ = lean_box(0);
v_isShared_1470_ = v_isSharedCheck_1487_;
goto v_resetjp_1468_;
}
v_resetjp_1468_:
{
lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1474_; 
v___x_1471_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__0));
v___x_1472_ = l_Lean_Lsp_instToJsonTextDocumentIdentifier_toJson(v_textDocument_1466_);
if (v_isShared_1470_ == 0)
{
lean_ctor_set(v___x_1469_, 1, v___x_1472_);
lean_ctor_set(v___x_1469_, 0, v___x_1471_);
v___x_1474_ = v___x_1469_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1486_; 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v___x_1471_);
lean_ctor_set(v_reuseFailAlloc_1486_, 1, v___x_1472_);
v___x_1474_ = v_reuseFailAlloc_1486_;
goto v_reusejp_1473_;
}
v_reusejp_1473_:
{
lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; 
v___x_1475_ = lean_box(0);
v___x_1476_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1476_, 0, v___x_1474_);
lean_ctor_set(v___x_1476_, 1, v___x_1475_);
v___x_1477_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__6));
v___x_1478_ = l_Lean_Lsp_instToJsonPosition_toJson(v_position_1467_);
v___x_1479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1479_, 0, v___x_1477_);
lean_ctor_set(v___x_1479_, 1, v___x_1478_);
v___x_1480_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1480_, 0, v___x_1479_);
lean_ctor_set(v___x_1480_, 1, v___x_1475_);
v___x_1481_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1481_, 0, v___x_1480_);
lean_ctor_set(v___x_1481_, 1, v___x_1475_);
v___x_1482_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1482_, 0, v___x_1476_);
lean_ctor_set(v___x_1482_, 1, v___x_1481_);
v___x_1483_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0));
v___x_1484_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_1482_, v___x_1483_);
v___x_1485_ = l_Lean_Json_mkObj(v___x_1484_);
lean_dec(v___x_1484_);
return v___x_1485_;
}
}
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__3(void){
_start:
{
uint8_t v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; 
v___x_1496_ = 1;
v___x_1497_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__2));
v___x_1498_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1497_, v___x_1496_);
return v___x_1498_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__4(void){
_start:
{
lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; 
v___x_1499_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6));
v___x_1500_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__3, &l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__3);
v___x_1501_ = lean_string_append(v___x_1500_, v___x_1499_);
return v___x_1501_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__6(void){
_start:
{
uint8_t v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; 
v___x_1504_ = 1;
v___x_1505_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__5));
v___x_1506_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1505_, v___x_1504_);
return v___x_1506_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__7(void){
_start:
{
lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; 
v___x_1507_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__6, &l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__6);
v___x_1508_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__4, &l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__4);
v___x_1509_ = lean_string_append(v___x_1508_, v___x_1507_);
return v___x_1509_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__8(void){
_start:
{
lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; 
v___x_1510_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_1511_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__7, &l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__7);
v___x_1512_ = lean_string_append(v___x_1511_, v___x_1510_);
return v___x_1512_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__9(void){
_start:
{
lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; 
v___x_1513_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__6);
v___x_1514_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__4, &l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__4);
v___x_1515_ = lean_string_append(v___x_1514_, v___x_1513_);
return v___x_1515_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__10(void){
_start:
{
lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; 
v___x_1516_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_1517_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__9, &l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__9);
v___x_1518_ = lean_string_append(v___x_1517_, v___x_1516_);
return v___x_1518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson(lean_object* v_json_1519_){
_start:
{
lean_object* v___x_1520_; lean_object* v___x_1521_; 
v___x_1520_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__0));
lean_inc(v_json_1519_);
v___x_1521_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson_spec__0(v_json_1519_, v___x_1520_);
if (lean_obj_tag(v___x_1521_) == 0)
{
lean_object* v_a_1522_; lean_object* v___x_1524_; uint8_t v_isShared_1525_; uint8_t v_isSharedCheck_1531_; 
lean_dec(v_json_1519_);
v_a_1522_ = lean_ctor_get(v___x_1521_, 0);
v_isSharedCheck_1531_ = !lean_is_exclusive(v___x_1521_);
if (v_isSharedCheck_1531_ == 0)
{
v___x_1524_ = v___x_1521_;
v_isShared_1525_ = v_isSharedCheck_1531_;
goto v_resetjp_1523_;
}
else
{
lean_inc(v_a_1522_);
lean_dec(v___x_1521_);
v___x_1524_ = lean_box(0);
v_isShared_1525_ = v_isSharedCheck_1531_;
goto v_resetjp_1523_;
}
v_resetjp_1523_:
{
lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1529_; 
v___x_1526_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__8, &l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__8);
v___x_1527_ = lean_string_append(v___x_1526_, v_a_1522_);
lean_dec(v_a_1522_);
if (v_isShared_1525_ == 0)
{
lean_ctor_set(v___x_1524_, 0, v___x_1527_);
v___x_1529_ = v___x_1524_;
goto v_reusejp_1528_;
}
else
{
lean_object* v_reuseFailAlloc_1530_; 
v_reuseFailAlloc_1530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1530_, 0, v___x_1527_);
v___x_1529_ = v_reuseFailAlloc_1530_;
goto v_reusejp_1528_;
}
v_reusejp_1528_:
{
return v___x_1529_;
}
}
}
else
{
if (lean_obj_tag(v___x_1521_) == 0)
{
lean_object* v_a_1532_; lean_object* v___x_1534_; uint8_t v_isShared_1535_; uint8_t v_isSharedCheck_1539_; 
lean_dec(v_json_1519_);
v_a_1532_ = lean_ctor_get(v___x_1521_, 0);
v_isSharedCheck_1539_ = !lean_is_exclusive(v___x_1521_);
if (v_isSharedCheck_1539_ == 0)
{
v___x_1534_ = v___x_1521_;
v_isShared_1535_ = v_isSharedCheck_1539_;
goto v_resetjp_1533_;
}
else
{
lean_inc(v_a_1532_);
lean_dec(v___x_1521_);
v___x_1534_ = lean_box(0);
v_isShared_1535_ = v_isSharedCheck_1539_;
goto v_resetjp_1533_;
}
v_resetjp_1533_:
{
lean_object* v___x_1537_; 
if (v_isShared_1535_ == 0)
{
lean_ctor_set_tag(v___x_1534_, 0);
v___x_1537_ = v___x_1534_;
goto v_reusejp_1536_;
}
else
{
lean_object* v_reuseFailAlloc_1538_; 
v_reuseFailAlloc_1538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1538_, 0, v_a_1532_);
v___x_1537_ = v_reuseFailAlloc_1538_;
goto v_reusejp_1536_;
}
v_reusejp_1536_:
{
return v___x_1537_;
}
}
}
else
{
lean_object* v_a_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; 
v_a_1540_ = lean_ctor_get(v___x_1521_, 0);
lean_inc(v_a_1540_);
lean_dec_ref(v___x_1521_);
v___x_1541_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__0));
v___x_1542_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson_spec__0(v_json_1519_, v___x_1541_);
if (lean_obj_tag(v___x_1542_) == 0)
{
lean_object* v_a_1543_; lean_object* v___x_1545_; uint8_t v_isShared_1546_; uint8_t v_isSharedCheck_1552_; 
lean_dec(v_a_1540_);
v_a_1543_ = lean_ctor_get(v___x_1542_, 0);
v_isSharedCheck_1552_ = !lean_is_exclusive(v___x_1542_);
if (v_isSharedCheck_1552_ == 0)
{
v___x_1545_ = v___x_1542_;
v_isShared_1546_ = v_isSharedCheck_1552_;
goto v_resetjp_1544_;
}
else
{
lean_inc(v_a_1543_);
lean_dec(v___x_1542_);
v___x_1545_ = lean_box(0);
v_isShared_1546_ = v_isSharedCheck_1552_;
goto v_resetjp_1544_;
}
v_resetjp_1544_:
{
lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1550_; 
v___x_1547_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__10, &l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__10);
v___x_1548_ = lean_string_append(v___x_1547_, v_a_1543_);
lean_dec(v_a_1543_);
if (v_isShared_1546_ == 0)
{
lean_ctor_set(v___x_1545_, 0, v___x_1548_);
v___x_1550_ = v___x_1545_;
goto v_reusejp_1549_;
}
else
{
lean_object* v_reuseFailAlloc_1551_; 
v_reuseFailAlloc_1551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1551_, 0, v___x_1548_);
v___x_1550_ = v_reuseFailAlloc_1551_;
goto v_reusejp_1549_;
}
v_reusejp_1549_:
{
return v___x_1550_;
}
}
}
else
{
if (lean_obj_tag(v___x_1542_) == 0)
{
lean_object* v_a_1553_; lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1560_; 
lean_dec(v_a_1540_);
v_a_1553_ = lean_ctor_get(v___x_1542_, 0);
v_isSharedCheck_1560_ = !lean_is_exclusive(v___x_1542_);
if (v_isSharedCheck_1560_ == 0)
{
v___x_1555_ = v___x_1542_;
v_isShared_1556_ = v_isSharedCheck_1560_;
goto v_resetjp_1554_;
}
else
{
lean_inc(v_a_1553_);
lean_dec(v___x_1542_);
v___x_1555_ = lean_box(0);
v_isShared_1556_ = v_isSharedCheck_1560_;
goto v_resetjp_1554_;
}
v_resetjp_1554_:
{
lean_object* v___x_1558_; 
if (v_isShared_1556_ == 0)
{
lean_ctor_set_tag(v___x_1555_, 0);
v___x_1558_ = v___x_1555_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1559_, 0, v_a_1553_);
v___x_1558_ = v_reuseFailAlloc_1559_;
goto v_reusejp_1557_;
}
v_reusejp_1557_:
{
return v___x_1558_;
}
}
}
else
{
lean_object* v_a_1561_; lean_object* v___x_1563_; uint8_t v_isShared_1564_; uint8_t v_isSharedCheck_1569_; 
v_a_1561_ = lean_ctor_get(v___x_1542_, 0);
v_isSharedCheck_1569_ = !lean_is_exclusive(v___x_1542_);
if (v_isSharedCheck_1569_ == 0)
{
v___x_1563_ = v___x_1542_;
v_isShared_1564_ = v_isSharedCheck_1569_;
goto v_resetjp_1562_;
}
else
{
lean_inc(v_a_1561_);
lean_dec(v___x_1542_);
v___x_1563_ = lean_box(0);
v_isShared_1564_ = v_isSharedCheck_1569_;
goto v_resetjp_1562_;
}
v_resetjp_1562_:
{
lean_object* v___x_1565_; lean_object* v___x_1567_; 
v___x_1565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1565_, 0, v_a_1540_);
lean_ctor_set(v___x_1565_, 1, v_a_1561_);
if (v_isShared_1564_ == 0)
{
lean_ctor_set(v___x_1563_, 0, v___x_1565_);
v___x_1567_ = v___x_1563_;
goto v_reusejp_1566_;
}
else
{
lean_object* v_reuseFailAlloc_1568_; 
v_reuseFailAlloc_1568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1568_, 0, v___x_1565_);
v___x_1567_ = v_reuseFailAlloc_1568_;
goto v_reusejp_1566_;
}
v_reusejp_1566_:
{
return v___x_1567_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonPlainTermGoal_toJson(lean_object* v_x_1572_){
_start:
{
lean_object* v_goal_1573_; lean_object* v_range_1574_; lean_object* v___x_1576_; uint8_t v_isShared_1577_; uint8_t v_isSharedCheck_1594_; 
v_goal_1573_ = lean_ctor_get(v_x_1572_, 0);
v_range_1574_ = lean_ctor_get(v_x_1572_, 1);
v_isSharedCheck_1594_ = !lean_is_exclusive(v_x_1572_);
if (v_isSharedCheck_1594_ == 0)
{
v___x_1576_ = v_x_1572_;
v_isShared_1577_ = v_isSharedCheck_1594_;
goto v_resetjp_1575_;
}
else
{
lean_inc(v_range_1574_);
lean_inc(v_goal_1573_);
lean_dec(v_x_1572_);
v___x_1576_ = lean_box(0);
v_isShared_1577_ = v_isSharedCheck_1594_;
goto v_resetjp_1575_;
}
v_resetjp_1575_:
{
lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1581_; 
v___x_1578_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__0));
v___x_1579_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1579_, 0, v_goal_1573_);
if (v_isShared_1577_ == 0)
{
lean_ctor_set(v___x_1576_, 1, v___x_1579_);
lean_ctor_set(v___x_1576_, 0, v___x_1578_);
v___x_1581_ = v___x_1576_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v___x_1578_);
lean_ctor_set(v_reuseFailAlloc_1593_, 1, v___x_1579_);
v___x_1581_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; 
v___x_1582_ = lean_box(0);
v___x_1583_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1583_, 0, v___x_1581_);
lean_ctor_set(v___x_1583_, 1, v___x_1582_);
v___x_1584_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__0));
v___x_1585_ = l_Lean_Lsp_instToJsonRange_toJson(v_range_1574_);
v___x_1586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1586_, 0, v___x_1584_);
lean_ctor_set(v___x_1586_, 1, v___x_1585_);
v___x_1587_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1587_, 0, v___x_1586_);
lean_ctor_set(v___x_1587_, 1, v___x_1582_);
v___x_1588_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1588_, 0, v___x_1587_);
lean_ctor_set(v___x_1588_, 1, v___x_1582_);
v___x_1589_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1589_, 0, v___x_1583_);
lean_ctor_set(v___x_1589_, 1, v___x_1588_);
v___x_1590_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0));
v___x_1591_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_1589_, v___x_1590_);
v___x_1592_ = l_Lean_Json_mkObj(v___x_1591_);
lean_dec(v___x_1591_);
return v___x_1592_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ModuleHierarchyOptions_toCtorIdx(lean_object* v_x_1597_){
_start:
{
lean_object* v___x_1598_; 
v___x_1598_ = lean_unsigned_to_nat(0u);
return v___x_1598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonModuleHierarchyOptions_fromJson(lean_object* v_json_1601_){
_start:
{
lean_object* v___x_1602_; 
v___x_1602_ = ((lean_object*)(l_Lean_Lsp_instFromJsonModuleHierarchyOptions_fromJson___closed__0));
return v___x_1602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonModuleHierarchyOptions_fromJson___boxed(lean_object* v_json_1603_){
_start:
{
lean_object* v_res_1604_; 
v_res_1604_ = l_Lean_Lsp_instFromJsonModuleHierarchyOptions_fromJson(v_json_1603_);
lean_dec(v_json_1603_);
return v_res_1604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonModuleHierarchyOptions_toJson(lean_object* v_x_1607_){
_start:
{
lean_object* v___x_1608_; 
v___x_1608_ = lean_obj_once(&l_Lean_Lsp_instToJsonWaitForILeans_toJson___closed__1, &l_Lean_Lsp_instToJsonWaitForILeans_toJson___closed__1_once, _init_l_Lean_Lsp_instToJsonWaitForILeans_toJson___closed__1);
return v___x_1608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_HighlightMatchesOptions_toCtorIdx(lean_object* v_x_1611_){
_start:
{
lean_object* v___x_1612_; 
v___x_1612_ = lean_unsigned_to_nat(0u);
return v___x_1612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonHighlightMatchesOptions_fromJson(lean_object* v_json_1615_){
_start:
{
lean_object* v___x_1616_; 
v___x_1616_ = ((lean_object*)(l_Lean_Lsp_instFromJsonHighlightMatchesOptions_fromJson___closed__0));
return v___x_1616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonHighlightMatchesOptions_fromJson___boxed(lean_object* v_json_1617_){
_start:
{
lean_object* v_res_1618_; 
v_res_1618_ = l_Lean_Lsp_instFromJsonHighlightMatchesOptions_fromJson(v_json_1617_);
lean_dec(v_json_1617_);
return v_res_1618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonHighlightMatchesOptions_toJson(lean_object* v_x_1621_){
_start:
{
lean_object* v___x_1622_; 
v___x_1622_ = lean_obj_once(&l_Lean_Lsp_instToJsonWaitForILeans_toJson___closed__1, &l_Lean_Lsp_instToJsonWaitForILeans_toJson___closed__1_once, _init_l_Lean_Lsp_instToJsonWaitForILeans_toJson___closed__1);
return v___x_1622_;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__1_spec__2(lean_object* v_x_1627_){
_start:
{
if (lean_obj_tag(v_x_1627_) == 0)
{
lean_object* v___x_1628_; 
v___x_1628_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__1_spec__2___closed__0));
return v___x_1628_;
}
else
{
lean_object* v___x_1629_; 
v___x_1629_ = l_Lean_Lsp_instFromJsonRpcWireFormat_fromJson(v_x_1627_);
if (lean_obj_tag(v___x_1629_) == 0)
{
lean_object* v_a_1630_; lean_object* v___x_1632_; uint8_t v_isShared_1633_; uint8_t v_isSharedCheck_1637_; 
v_a_1630_ = lean_ctor_get(v___x_1629_, 0);
v_isSharedCheck_1637_ = !lean_is_exclusive(v___x_1629_);
if (v_isSharedCheck_1637_ == 0)
{
v___x_1632_ = v___x_1629_;
v_isShared_1633_ = v_isSharedCheck_1637_;
goto v_resetjp_1631_;
}
else
{
lean_inc(v_a_1630_);
lean_dec(v___x_1629_);
v___x_1632_ = lean_box(0);
v_isShared_1633_ = v_isSharedCheck_1637_;
goto v_resetjp_1631_;
}
v_resetjp_1631_:
{
lean_object* v___x_1635_; 
if (v_isShared_1633_ == 0)
{
v___x_1635_ = v___x_1632_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v_a_1630_);
v___x_1635_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
return v___x_1635_;
}
}
}
else
{
lean_object* v_a_1638_; lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1646_; 
v_a_1638_ = lean_ctor_get(v___x_1629_, 0);
v_isSharedCheck_1646_ = !lean_is_exclusive(v___x_1629_);
if (v_isSharedCheck_1646_ == 0)
{
v___x_1640_ = v___x_1629_;
v_isShared_1641_ = v_isSharedCheck_1646_;
goto v_resetjp_1639_;
}
else
{
lean_inc(v_a_1638_);
lean_dec(v___x_1629_);
v___x_1640_ = lean_box(0);
v_isShared_1641_ = v_isSharedCheck_1646_;
goto v_resetjp_1639_;
}
v_resetjp_1639_:
{
lean_object* v___x_1642_; lean_object* v___x_1644_; 
v___x_1642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1642_, 0, v_a_1638_);
if (v_isShared_1641_ == 0)
{
lean_ctor_set(v___x_1640_, 0, v___x_1642_);
v___x_1644_ = v___x_1640_;
goto v_reusejp_1643_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(1, 1, 0);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__1(lean_object* v_j_1647_, lean_object* v_k_1648_){
_start:
{
lean_object* v___x_1649_; lean_object* v___x_1650_; 
v___x_1649_ = l_Lean_Json_getObjValD(v_j_1647_, v_k_1648_);
v___x_1650_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__1_spec__2(v___x_1649_);
return v___x_1650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__1___boxed(lean_object* v_j_1651_, lean_object* v_k_1652_){
_start:
{
lean_object* v_res_1653_; 
v_res_1653_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__1(v_j_1651_, v_k_1652_);
lean_dec_ref(v_k_1652_);
return v_res_1653_;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__0_spec__0(lean_object* v_x_1656_){
_start:
{
if (lean_obj_tag(v_x_1656_) == 0)
{
lean_object* v___x_1657_; 
v___x_1657_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__0_spec__0___closed__0));
return v___x_1657_;
}
else
{
lean_object* v___x_1658_; lean_object* v_a_1659_; lean_object* v___x_1661_; uint8_t v_isShared_1662_; uint8_t v_isSharedCheck_1667_; 
v___x_1658_ = l_Lean_Lsp_instFromJsonHighlightMatchesOptions_fromJson(v_x_1656_);
v_a_1659_ = lean_ctor_get(v___x_1658_, 0);
v_isSharedCheck_1667_ = !lean_is_exclusive(v___x_1658_);
if (v_isSharedCheck_1667_ == 0)
{
v___x_1661_ = v___x_1658_;
v_isShared_1662_ = v_isSharedCheck_1667_;
goto v_resetjp_1660_;
}
else
{
lean_inc(v_a_1659_);
lean_dec(v___x_1658_);
v___x_1661_ = lean_box(0);
v_isShared_1662_ = v_isSharedCheck_1667_;
goto v_resetjp_1660_;
}
v_resetjp_1660_:
{
lean_object* v___x_1663_; lean_object* v___x_1665_; 
v___x_1663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1663_, 0, v_a_1659_);
if (v_isShared_1662_ == 0)
{
lean_ctor_set(v___x_1661_, 0, v___x_1663_);
v___x_1665_ = v___x_1661_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__0_spec__0___boxed(lean_object* v_x_1668_){
_start:
{
lean_object* v_res_1669_; 
v_res_1669_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__0_spec__0(v_x_1668_);
lean_dec(v_x_1668_);
return v_res_1669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__0(lean_object* v_j_1670_, lean_object* v_k_1671_){
_start:
{
lean_object* v___x_1672_; lean_object* v___x_1673_; 
v___x_1672_ = l_Lean_Json_getObjValD(v_j_1670_, v_k_1671_);
v___x_1673_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__0_spec__0(v___x_1672_);
lean_dec(v___x_1672_);
return v___x_1673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__0___boxed(lean_object* v_j_1674_, lean_object* v_k_1675_){
_start:
{
lean_object* v_res_1676_; 
v_res_1676_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__0(v_j_1674_, v_k_1675_);
lean_dec_ref(v_k_1675_);
return v_res_1676_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__3(void){
_start:
{
uint8_t v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; 
v___x_1683_ = 1;
v___x_1684_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__2));
v___x_1685_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1684_, v___x_1683_);
return v___x_1685_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__4(void){
_start:
{
lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; 
v___x_1686_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6));
v___x_1687_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__3, &l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__3);
v___x_1688_ = lean_string_append(v___x_1687_, v___x_1686_);
return v___x_1688_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__7(void){
_start:
{
uint8_t v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; 
v___x_1692_ = 1;
v___x_1693_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__6));
v___x_1694_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1693_, v___x_1692_);
return v___x_1694_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__8(void){
_start:
{
lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; 
v___x_1695_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__7, &l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__7);
v___x_1696_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__4, &l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__4);
v___x_1697_ = lean_string_append(v___x_1696_, v___x_1695_);
return v___x_1697_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__9(void){
_start:
{
lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; 
v___x_1698_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_1699_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__8, &l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__8);
v___x_1700_ = lean_string_append(v___x_1699_, v___x_1698_);
return v___x_1700_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__13(void){
_start:
{
uint8_t v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; 
v___x_1705_ = 1;
v___x_1706_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__12));
v___x_1707_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1706_, v___x_1705_);
return v___x_1707_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__14(void){
_start:
{
lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; 
v___x_1708_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__13, &l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__13);
v___x_1709_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__4, &l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__4);
v___x_1710_ = lean_string_append(v___x_1709_, v___x_1708_);
return v___x_1710_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__15(void){
_start:
{
lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; 
v___x_1711_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_1712_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__14, &l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__14_once, _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__14);
v___x_1713_ = lean_string_append(v___x_1712_, v___x_1711_);
return v___x_1713_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonRpcOptions_fromJson(lean_object* v_json_1714_){
_start:
{
lean_object* v___x_1715_; lean_object* v___x_1716_; 
v___x_1715_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__0));
lean_inc(v_json_1714_);
v___x_1716_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__0(v_json_1714_, v___x_1715_);
if (lean_obj_tag(v___x_1716_) == 0)
{
lean_object* v_a_1717_; lean_object* v___x_1719_; uint8_t v_isShared_1720_; uint8_t v_isSharedCheck_1726_; 
lean_dec(v_json_1714_);
v_a_1717_ = lean_ctor_get(v___x_1716_, 0);
v_isSharedCheck_1726_ = !lean_is_exclusive(v___x_1716_);
if (v_isSharedCheck_1726_ == 0)
{
v___x_1719_ = v___x_1716_;
v_isShared_1720_ = v_isSharedCheck_1726_;
goto v_resetjp_1718_;
}
else
{
lean_inc(v_a_1717_);
lean_dec(v___x_1716_);
v___x_1719_ = lean_box(0);
v_isShared_1720_ = v_isSharedCheck_1726_;
goto v_resetjp_1718_;
}
v_resetjp_1718_:
{
lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1724_; 
v___x_1721_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__9, &l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__9);
v___x_1722_ = lean_string_append(v___x_1721_, v_a_1717_);
lean_dec(v_a_1717_);
if (v_isShared_1720_ == 0)
{
lean_ctor_set(v___x_1719_, 0, v___x_1722_);
v___x_1724_ = v___x_1719_;
goto v_reusejp_1723_;
}
else
{
lean_object* v_reuseFailAlloc_1725_; 
v_reuseFailAlloc_1725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1725_, 0, v___x_1722_);
v___x_1724_ = v_reuseFailAlloc_1725_;
goto v_reusejp_1723_;
}
v_reusejp_1723_:
{
return v___x_1724_;
}
}
}
else
{
if (lean_obj_tag(v___x_1716_) == 0)
{
lean_object* v_a_1727_; lean_object* v___x_1729_; uint8_t v_isShared_1730_; uint8_t v_isSharedCheck_1734_; 
lean_dec(v_json_1714_);
v_a_1727_ = lean_ctor_get(v___x_1716_, 0);
v_isSharedCheck_1734_ = !lean_is_exclusive(v___x_1716_);
if (v_isSharedCheck_1734_ == 0)
{
v___x_1729_ = v___x_1716_;
v_isShared_1730_ = v_isSharedCheck_1734_;
goto v_resetjp_1728_;
}
else
{
lean_inc(v_a_1727_);
lean_dec(v___x_1716_);
v___x_1729_ = lean_box(0);
v_isShared_1730_ = v_isSharedCheck_1734_;
goto v_resetjp_1728_;
}
v_resetjp_1728_:
{
lean_object* v___x_1732_; 
if (v_isShared_1730_ == 0)
{
lean_ctor_set_tag(v___x_1729_, 0);
v___x_1732_ = v___x_1729_;
goto v_reusejp_1731_;
}
else
{
lean_object* v_reuseFailAlloc_1733_; 
v_reuseFailAlloc_1733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1733_, 0, v_a_1727_);
v___x_1732_ = v_reuseFailAlloc_1733_;
goto v_reusejp_1731_;
}
v_reusejp_1731_:
{
return v___x_1732_;
}
}
}
else
{
lean_object* v_a_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; 
v_a_1735_ = lean_ctor_get(v___x_1716_, 0);
lean_inc(v_a_1735_);
lean_dec_ref(v___x_1716_);
v___x_1736_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__10));
v___x_1737_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__1(v_json_1714_, v___x_1736_);
if (lean_obj_tag(v___x_1737_) == 0)
{
lean_object* v_a_1738_; lean_object* v___x_1740_; uint8_t v_isShared_1741_; uint8_t v_isSharedCheck_1747_; 
lean_dec(v_a_1735_);
v_a_1738_ = lean_ctor_get(v___x_1737_, 0);
v_isSharedCheck_1747_ = !lean_is_exclusive(v___x_1737_);
if (v_isSharedCheck_1747_ == 0)
{
v___x_1740_ = v___x_1737_;
v_isShared_1741_ = v_isSharedCheck_1747_;
goto v_resetjp_1739_;
}
else
{
lean_inc(v_a_1738_);
lean_dec(v___x_1737_);
v___x_1740_ = lean_box(0);
v_isShared_1741_ = v_isSharedCheck_1747_;
goto v_resetjp_1739_;
}
v_resetjp_1739_:
{
lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1745_; 
v___x_1742_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__15, &l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__15_once, _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__15);
v___x_1743_ = lean_string_append(v___x_1742_, v_a_1738_);
lean_dec(v_a_1738_);
if (v_isShared_1741_ == 0)
{
lean_ctor_set(v___x_1740_, 0, v___x_1743_);
v___x_1745_ = v___x_1740_;
goto v_reusejp_1744_;
}
else
{
lean_object* v_reuseFailAlloc_1746_; 
v_reuseFailAlloc_1746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1746_, 0, v___x_1743_);
v___x_1745_ = v_reuseFailAlloc_1746_;
goto v_reusejp_1744_;
}
v_reusejp_1744_:
{
return v___x_1745_;
}
}
}
else
{
if (lean_obj_tag(v___x_1737_) == 0)
{
lean_object* v_a_1748_; lean_object* v___x_1750_; uint8_t v_isShared_1751_; uint8_t v_isSharedCheck_1755_; 
lean_dec(v_a_1735_);
v_a_1748_ = lean_ctor_get(v___x_1737_, 0);
v_isSharedCheck_1755_ = !lean_is_exclusive(v___x_1737_);
if (v_isSharedCheck_1755_ == 0)
{
v___x_1750_ = v___x_1737_;
v_isShared_1751_ = v_isSharedCheck_1755_;
goto v_resetjp_1749_;
}
else
{
lean_inc(v_a_1748_);
lean_dec(v___x_1737_);
v___x_1750_ = lean_box(0);
v_isShared_1751_ = v_isSharedCheck_1755_;
goto v_resetjp_1749_;
}
v_resetjp_1749_:
{
lean_object* v___x_1753_; 
if (v_isShared_1751_ == 0)
{
lean_ctor_set_tag(v___x_1750_, 0);
v___x_1753_ = v___x_1750_;
goto v_reusejp_1752_;
}
else
{
lean_object* v_reuseFailAlloc_1754_; 
v_reuseFailAlloc_1754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1754_, 0, v_a_1748_);
v___x_1753_ = v_reuseFailAlloc_1754_;
goto v_reusejp_1752_;
}
v_reusejp_1752_:
{
return v___x_1753_;
}
}
}
else
{
lean_object* v_a_1756_; lean_object* v___x_1758_; uint8_t v_isShared_1759_; uint8_t v_isSharedCheck_1764_; 
v_a_1756_ = lean_ctor_get(v___x_1737_, 0);
v_isSharedCheck_1764_ = !lean_is_exclusive(v___x_1737_);
if (v_isSharedCheck_1764_ == 0)
{
v___x_1758_ = v___x_1737_;
v_isShared_1759_ = v_isSharedCheck_1764_;
goto v_resetjp_1757_;
}
else
{
lean_inc(v_a_1756_);
lean_dec(v___x_1737_);
v___x_1758_ = lean_box(0);
v_isShared_1759_ = v_isSharedCheck_1764_;
goto v_resetjp_1757_;
}
v_resetjp_1757_:
{
lean_object* v___x_1760_; lean_object* v___x_1762_; 
v___x_1760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1760_, 0, v_a_1735_);
lean_ctor_set(v___x_1760_, 1, v_a_1756_);
if (v_isShared_1759_ == 0)
{
lean_ctor_set(v___x_1758_, 0, v___x_1760_);
v___x_1762_ = v___x_1758_;
goto v_reusejp_1761_;
}
else
{
lean_object* v_reuseFailAlloc_1763_; 
v_reuseFailAlloc_1763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1763_, 0, v___x_1760_);
v___x_1762_ = v_reuseFailAlloc_1763_;
goto v_reusejp_1761_;
}
v_reusejp_1761_:
{
return v___x_1762_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonRpcOptions_toJson_spec__0(lean_object* v_k_1767_, lean_object* v_x_1768_){
_start:
{
if (lean_obj_tag(v_x_1768_) == 0)
{
lean_object* v___x_1769_; 
lean_dec_ref(v_k_1767_);
v___x_1769_ = lean_box(0);
return v___x_1769_;
}
else
{
lean_object* v_val_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; 
v_val_1770_ = lean_ctor_get(v_x_1768_, 0);
lean_inc(v_val_1770_);
lean_dec_ref(v_x_1768_);
v___x_1771_ = l_Lean_Lsp_instToJsonHighlightMatchesOptions_toJson(v_val_1770_);
v___x_1772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1772_, 0, v_k_1767_);
lean_ctor_set(v___x_1772_, 1, v___x_1771_);
v___x_1773_ = lean_box(0);
v___x_1774_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1774_, 0, v___x_1772_);
lean_ctor_set(v___x_1774_, 1, v___x_1773_);
return v___x_1774_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonRpcOptions_toJson_spec__1(lean_object* v_k_1775_, lean_object* v_x_1776_){
_start:
{
if (lean_obj_tag(v_x_1776_) == 0)
{
lean_object* v___x_1777_; 
lean_dec_ref(v_k_1775_);
v___x_1777_ = lean_box(0);
return v___x_1777_;
}
else
{
lean_object* v_val_1778_; uint8_t v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; 
v_val_1778_ = lean_ctor_get(v_x_1776_, 0);
v___x_1779_ = lean_unbox(v_val_1778_);
v___x_1780_ = l_Lean_Lsp_instToJsonRpcWireFormat_toJson(v___x_1779_);
v___x_1781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1781_, 0, v_k_1775_);
lean_ctor_set(v___x_1781_, 1, v___x_1780_);
v___x_1782_ = lean_box(0);
v___x_1783_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1783_, 0, v___x_1781_);
lean_ctor_set(v___x_1783_, 1, v___x_1782_);
return v___x_1783_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonRpcOptions_toJson_spec__1___boxed(lean_object* v_k_1784_, lean_object* v_x_1785_){
_start:
{
lean_object* v_res_1786_; 
v_res_1786_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonRpcOptions_toJson_spec__1(v_k_1784_, v_x_1785_);
lean_dec(v_x_1785_);
return v_res_1786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRpcOptions_toJson(lean_object* v_x_1787_){
_start:
{
lean_object* v_highlightMatchesProvider_x3f_1788_; lean_object* v_rpcWireFormat_x3f_1789_; lean_object* v___x_1791_; uint8_t v_isShared_1792_; uint8_t v_isSharedCheck_1805_; 
v_highlightMatchesProvider_x3f_1788_ = lean_ctor_get(v_x_1787_, 0);
v_rpcWireFormat_x3f_1789_ = lean_ctor_get(v_x_1787_, 1);
v_isSharedCheck_1805_ = !lean_is_exclusive(v_x_1787_);
if (v_isSharedCheck_1805_ == 0)
{
v___x_1791_ = v_x_1787_;
v_isShared_1792_ = v_isSharedCheck_1805_;
goto v_resetjp_1790_;
}
else
{
lean_inc(v_rpcWireFormat_x3f_1789_);
lean_inc(v_highlightMatchesProvider_x3f_1788_);
lean_dec(v_x_1787_);
v___x_1791_ = lean_box(0);
v_isShared_1792_ = v_isSharedCheck_1805_;
goto v_resetjp_1790_;
}
v_resetjp_1790_:
{
lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1799_; 
v___x_1793_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__0));
v___x_1794_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonRpcOptions_toJson_spec__0(v___x_1793_, v_highlightMatchesProvider_x3f_1788_);
v___x_1795_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__10));
v___x_1796_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonRpcOptions_toJson_spec__1(v___x_1795_, v_rpcWireFormat_x3f_1789_);
lean_dec(v_rpcWireFormat_x3f_1789_);
v___x_1797_ = lean_box(0);
if (v_isShared_1792_ == 0)
{
lean_ctor_set_tag(v___x_1791_, 1);
lean_ctor_set(v___x_1791_, 1, v___x_1797_);
lean_ctor_set(v___x_1791_, 0, v___x_1796_);
v___x_1799_ = v___x_1791_;
goto v_reusejp_1798_;
}
else
{
lean_object* v_reuseFailAlloc_1804_; 
v_reuseFailAlloc_1804_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1804_, 0, v___x_1796_);
lean_ctor_set(v_reuseFailAlloc_1804_, 1, v___x_1797_);
v___x_1799_ = v_reuseFailAlloc_1804_;
goto v_reusejp_1798_;
}
v_reusejp_1798_:
{
lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; 
v___x_1800_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1800_, 0, v___x_1794_);
lean_ctor_set(v___x_1800_, 1, v___x_1799_);
v___x_1801_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0));
v___x_1802_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_1800_, v___x_1801_);
v___x_1803_ = l_Lean_Json_mkObj(v___x_1802_);
lean_dec(v___x_1802_);
return v___x_1803_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModule_fromJson_spec__0_spec__0(lean_object* v_x_1810_){
_start:
{
if (lean_obj_tag(v_x_1810_) == 0)
{
lean_object* v___x_1811_; 
v___x_1811_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModule_fromJson_spec__0_spec__0___closed__0));
return v___x_1811_;
}
else
{
lean_object* v___x_1812_; lean_object* v___x_1813_; 
v___x_1812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1812_, 0, v_x_1810_);
v___x_1813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1813_, 0, v___x_1812_);
return v___x_1813_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModule_fromJson_spec__0(lean_object* v_j_1814_, lean_object* v_k_1815_){
_start:
{
lean_object* v___x_1816_; lean_object* v___x_1817_; 
v___x_1816_ = l_Lean_Json_getObjValD(v_j_1814_, v_k_1815_);
v___x_1817_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModule_fromJson_spec__0_spec__0(v___x_1816_);
return v___x_1817_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModule_fromJson_spec__0___boxed(lean_object* v_j_1818_, lean_object* v_k_1819_){
_start:
{
lean_object* v_res_1820_; 
v_res_1820_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModule_fromJson_spec__0(v_j_1818_, v_k_1819_);
lean_dec_ref(v_k_1819_);
return v_res_1820_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__3(void){
_start:
{
uint8_t v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; 
v___x_1827_ = 1;
v___x_1828_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__2));
v___x_1829_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1828_, v___x_1827_);
return v___x_1829_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__4(void){
_start:
{
lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; 
v___x_1830_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6));
v___x_1831_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__3);
v___x_1832_ = lean_string_append(v___x_1831_, v___x_1830_);
return v___x_1832_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__6(void){
_start:
{
uint8_t v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; 
v___x_1835_ = 1;
v___x_1836_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__5));
v___x_1837_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1836_, v___x_1835_);
return v___x_1837_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__7(void){
_start:
{
lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; 
v___x_1838_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__6);
v___x_1839_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__4);
v___x_1840_ = lean_string_append(v___x_1839_, v___x_1838_);
return v___x_1840_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__8(void){
_start:
{
lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; 
v___x_1841_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_1842_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__7);
v___x_1843_ = lean_string_append(v___x_1842_, v___x_1841_);
return v___x_1843_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__9(void){
_start:
{
lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; 
v___x_1844_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__6, &l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__6);
v___x_1845_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__4);
v___x_1846_ = lean_string_append(v___x_1845_, v___x_1844_);
return v___x_1846_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__10(void){
_start:
{
lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; 
v___x_1847_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_1848_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__9, &l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__9);
v___x_1849_ = lean_string_append(v___x_1848_, v___x_1847_);
return v___x_1849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanModule_fromJson(lean_object* v_json_1851_){
_start:
{
lean_object* v___x_1852_; lean_object* v___x_1853_; 
v___x_1852_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__0));
lean_inc(v_json_1851_);
v___x_1853_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson_spec__0(v_json_1851_, v___x_1852_);
if (lean_obj_tag(v___x_1853_) == 0)
{
lean_object* v_a_1854_; lean_object* v___x_1856_; uint8_t v_isShared_1857_; uint8_t v_isSharedCheck_1863_; 
lean_dec(v_json_1851_);
v_a_1854_ = lean_ctor_get(v___x_1853_, 0);
v_isSharedCheck_1863_ = !lean_is_exclusive(v___x_1853_);
if (v_isSharedCheck_1863_ == 0)
{
v___x_1856_ = v___x_1853_;
v_isShared_1857_ = v_isSharedCheck_1863_;
goto v_resetjp_1855_;
}
else
{
lean_inc(v_a_1854_);
lean_dec(v___x_1853_);
v___x_1856_ = lean_box(0);
v_isShared_1857_ = v_isSharedCheck_1863_;
goto v_resetjp_1855_;
}
v_resetjp_1855_:
{
lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1861_; 
v___x_1858_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__8);
v___x_1859_ = lean_string_append(v___x_1858_, v_a_1854_);
lean_dec(v_a_1854_);
if (v_isShared_1857_ == 0)
{
lean_ctor_set(v___x_1856_, 0, v___x_1859_);
v___x_1861_ = v___x_1856_;
goto v_reusejp_1860_;
}
else
{
lean_object* v_reuseFailAlloc_1862_; 
v_reuseFailAlloc_1862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1862_, 0, v___x_1859_);
v___x_1861_ = v_reuseFailAlloc_1862_;
goto v_reusejp_1860_;
}
v_reusejp_1860_:
{
return v___x_1861_;
}
}
}
else
{
if (lean_obj_tag(v___x_1853_) == 0)
{
lean_object* v_a_1864_; lean_object* v___x_1866_; uint8_t v_isShared_1867_; uint8_t v_isSharedCheck_1871_; 
lean_dec(v_json_1851_);
v_a_1864_ = lean_ctor_get(v___x_1853_, 0);
v_isSharedCheck_1871_ = !lean_is_exclusive(v___x_1853_);
if (v_isSharedCheck_1871_ == 0)
{
v___x_1866_ = v___x_1853_;
v_isShared_1867_ = v_isSharedCheck_1871_;
goto v_resetjp_1865_;
}
else
{
lean_inc(v_a_1864_);
lean_dec(v___x_1853_);
v___x_1866_ = lean_box(0);
v_isShared_1867_ = v_isSharedCheck_1871_;
goto v_resetjp_1865_;
}
v_resetjp_1865_:
{
lean_object* v___x_1869_; 
if (v_isShared_1867_ == 0)
{
lean_ctor_set_tag(v___x_1866_, 0);
v___x_1869_ = v___x_1866_;
goto v_reusejp_1868_;
}
else
{
lean_object* v_reuseFailAlloc_1870_; 
v_reuseFailAlloc_1870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1870_, 0, v_a_1864_);
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
lean_object* v_a_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; 
v_a_1872_ = lean_ctor_get(v___x_1853_, 0);
lean_inc(v_a_1872_);
lean_dec_ref(v___x_1853_);
v___x_1873_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__0));
lean_inc(v_json_1851_);
v___x_1874_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson_spec__0(v_json_1851_, v___x_1873_);
if (lean_obj_tag(v___x_1874_) == 0)
{
lean_object* v_a_1875_; lean_object* v___x_1877_; uint8_t v_isShared_1878_; uint8_t v_isSharedCheck_1884_; 
lean_dec(v_a_1872_);
lean_dec(v_json_1851_);
v_a_1875_ = lean_ctor_get(v___x_1874_, 0);
v_isSharedCheck_1884_ = !lean_is_exclusive(v___x_1874_);
if (v_isSharedCheck_1884_ == 0)
{
v___x_1877_ = v___x_1874_;
v_isShared_1878_ = v_isSharedCheck_1884_;
goto v_resetjp_1876_;
}
else
{
lean_inc(v_a_1875_);
lean_dec(v___x_1874_);
v___x_1877_ = lean_box(0);
v_isShared_1878_ = v_isSharedCheck_1884_;
goto v_resetjp_1876_;
}
v_resetjp_1876_:
{
lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1882_; 
v___x_1879_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__10, &l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__10);
v___x_1880_ = lean_string_append(v___x_1879_, v_a_1875_);
lean_dec(v_a_1875_);
if (v_isShared_1878_ == 0)
{
lean_ctor_set(v___x_1877_, 0, v___x_1880_);
v___x_1882_ = v___x_1877_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v___x_1880_);
v___x_1882_ = v_reuseFailAlloc_1883_;
goto v_reusejp_1881_;
}
v_reusejp_1881_:
{
return v___x_1882_;
}
}
}
else
{
if (lean_obj_tag(v___x_1874_) == 0)
{
lean_object* v_a_1885_; lean_object* v___x_1887_; uint8_t v_isShared_1888_; uint8_t v_isSharedCheck_1892_; 
lean_dec(v_a_1872_);
lean_dec(v_json_1851_);
v_a_1885_ = lean_ctor_get(v___x_1874_, 0);
v_isSharedCheck_1892_ = !lean_is_exclusive(v___x_1874_);
if (v_isSharedCheck_1892_ == 0)
{
v___x_1887_ = v___x_1874_;
v_isShared_1888_ = v_isSharedCheck_1892_;
goto v_resetjp_1886_;
}
else
{
lean_inc(v_a_1885_);
lean_dec(v___x_1874_);
v___x_1887_ = lean_box(0);
v_isShared_1888_ = v_isSharedCheck_1892_;
goto v_resetjp_1886_;
}
v_resetjp_1886_:
{
lean_object* v___x_1890_; 
if (v_isShared_1888_ == 0)
{
lean_ctor_set_tag(v___x_1887_, 0);
v___x_1890_ = v___x_1887_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1891_; 
v_reuseFailAlloc_1891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1891_, 0, v_a_1885_);
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
lean_object* v_a_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v_a_1896_; lean_object* v___x_1898_; uint8_t v_isShared_1899_; uint8_t v_isSharedCheck_1904_; 
v_a_1893_ = lean_ctor_get(v___x_1874_, 0);
lean_inc(v_a_1893_);
lean_dec_ref(v___x_1874_);
v___x_1894_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__11));
v___x_1895_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModule_fromJson_spec__0(v_json_1851_, v___x_1894_);
v_a_1896_ = lean_ctor_get(v___x_1895_, 0);
v_isSharedCheck_1904_ = !lean_is_exclusive(v___x_1895_);
if (v_isSharedCheck_1904_ == 0)
{
v___x_1898_ = v___x_1895_;
v_isShared_1899_ = v_isSharedCheck_1904_;
goto v_resetjp_1897_;
}
else
{
lean_inc(v_a_1896_);
lean_dec(v___x_1895_);
v___x_1898_ = lean_box(0);
v_isShared_1899_ = v_isSharedCheck_1904_;
goto v_resetjp_1897_;
}
v_resetjp_1897_:
{
lean_object* v___x_1900_; lean_object* v___x_1902_; 
v___x_1900_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1900_, 0, v_a_1872_);
lean_ctor_set(v___x_1900_, 1, v_a_1893_);
lean_ctor_set(v___x_1900_, 2, v_a_1896_);
if (v_isShared_1899_ == 0)
{
lean_ctor_set(v___x_1898_, 0, v___x_1900_);
v___x_1902_ = v___x_1898_;
goto v_reusejp_1901_;
}
else
{
lean_object* v_reuseFailAlloc_1903_; 
v_reuseFailAlloc_1903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1903_, 0, v___x_1900_);
v___x_1902_ = v_reuseFailAlloc_1903_;
goto v_reusejp_1901_;
}
v_reusejp_1901_:
{
return v___x_1902_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanModule_toJson_spec__0(lean_object* v_k_1907_, lean_object* v_x_1908_){
_start:
{
if (lean_obj_tag(v_x_1908_) == 0)
{
lean_object* v___x_1909_; 
lean_dec_ref(v_k_1907_);
v___x_1909_ = lean_box(0);
return v___x_1909_;
}
else
{
lean_object* v_val_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; 
v_val_1910_ = lean_ctor_get(v_x_1908_, 0);
lean_inc(v_val_1910_);
v___x_1911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1911_, 0, v_k_1907_);
lean_ctor_set(v___x_1911_, 1, v_val_1910_);
v___x_1912_ = lean_box(0);
v___x_1913_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1913_, 0, v___x_1911_);
lean_ctor_set(v___x_1913_, 1, v___x_1912_);
return v___x_1913_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanModule_toJson_spec__0___boxed(lean_object* v_k_1914_, lean_object* v_x_1915_){
_start:
{
lean_object* v_res_1916_; 
v_res_1916_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanModule_toJson_spec__0(v_k_1914_, v_x_1915_);
lean_dec(v_x_1915_);
return v_res_1916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanModule_toJson(lean_object* v_x_1917_){
_start:
{
lean_object* v_name_1918_; lean_object* v_uri_1919_; lean_object* v_data_x3f_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; 
v_name_1918_ = lean_ctor_get(v_x_1917_, 0);
v_uri_1919_ = lean_ctor_get(v_x_1917_, 1);
v_data_x3f_1920_ = lean_ctor_get(v_x_1917_, 2);
v___x_1921_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__0));
lean_inc_ref(v_name_1918_);
v___x_1922_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1922_, 0, v_name_1918_);
v___x_1923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1923_, 0, v___x_1921_);
lean_ctor_set(v___x_1923_, 1, v___x_1922_);
v___x_1924_ = lean_box(0);
v___x_1925_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1925_, 0, v___x_1923_);
lean_ctor_set(v___x_1925_, 1, v___x_1924_);
v___x_1926_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__0));
lean_inc_ref(v_uri_1919_);
v___x_1927_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1927_, 0, v_uri_1919_);
v___x_1928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1928_, 0, v___x_1926_);
lean_ctor_set(v___x_1928_, 1, v___x_1927_);
v___x_1929_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1929_, 0, v___x_1928_);
lean_ctor_set(v___x_1929_, 1, v___x_1924_);
v___x_1930_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__11));
v___x_1931_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanModule_toJson_spec__0(v___x_1930_, v_data_x3f_1920_);
v___x_1932_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1932_, 0, v___x_1931_);
lean_ctor_set(v___x_1932_, 1, v___x_1924_);
v___x_1933_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1933_, 0, v___x_1929_);
lean_ctor_set(v___x_1933_, 1, v___x_1932_);
v___x_1934_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1934_, 0, v___x_1925_);
lean_ctor_set(v___x_1934_, 1, v___x_1933_);
v___x_1935_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0));
v___x_1936_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_1934_, v___x_1935_);
v___x_1937_ = l_Lean_Json_mkObj(v___x_1936_);
lean_dec(v___x_1936_);
return v___x_1937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanModule_toJson___boxed(lean_object* v_x_1938_){
_start:
{
lean_object* v_res_1939_; 
v_res_1939_ = l_Lean_Lsp_instToJsonLeanModule_toJson(v_x_1938_);
lean_dec_ref(v_x_1938_);
return v_res_1939_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__2(void){
_start:
{
uint8_t v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; 
v___x_1947_ = 1;
v___x_1948_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__1));
v___x_1949_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1948_, v___x_1947_);
return v___x_1949_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__3(void){
_start:
{
lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; 
v___x_1950_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6));
v___x_1951_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__2, &l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__2);
v___x_1952_ = lean_string_append(v___x_1951_, v___x_1950_);
return v___x_1952_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; 
v___x_1953_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9, &l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9);
v___x_1954_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__3);
v___x_1955_ = lean_string_append(v___x_1954_, v___x_1953_);
return v___x_1955_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__5(void){
_start:
{
lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; 
v___x_1956_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_1957_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__4);
v___x_1958_ = lean_string_append(v___x_1957_, v___x_1956_);
return v___x_1958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson(lean_object* v_json_1959_){
_start:
{
lean_object* v___x_1960_; lean_object* v___x_1961_; 
v___x_1960_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__0));
v___x_1961_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoalParams_fromJson_spec__0(v_json_1959_, v___x_1960_);
if (lean_obj_tag(v___x_1961_) == 0)
{
lean_object* v_a_1962_; lean_object* v___x_1964_; uint8_t v_isShared_1965_; uint8_t v_isSharedCheck_1971_; 
v_a_1962_ = lean_ctor_get(v___x_1961_, 0);
v_isSharedCheck_1971_ = !lean_is_exclusive(v___x_1961_);
if (v_isSharedCheck_1971_ == 0)
{
v___x_1964_ = v___x_1961_;
v_isShared_1965_ = v_isSharedCheck_1971_;
goto v_resetjp_1963_;
}
else
{
lean_inc(v_a_1962_);
lean_dec(v___x_1961_);
v___x_1964_ = lean_box(0);
v_isShared_1965_ = v_isSharedCheck_1971_;
goto v_resetjp_1963_;
}
v_resetjp_1963_:
{
lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1969_; 
v___x_1966_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__5, &l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__5);
v___x_1967_ = lean_string_append(v___x_1966_, v_a_1962_);
lean_dec(v_a_1962_);
if (v_isShared_1965_ == 0)
{
lean_ctor_set(v___x_1964_, 0, v___x_1967_);
v___x_1969_ = v___x_1964_;
goto v_reusejp_1968_;
}
else
{
lean_object* v_reuseFailAlloc_1970_; 
v_reuseFailAlloc_1970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1970_, 0, v___x_1967_);
v___x_1969_ = v_reuseFailAlloc_1970_;
goto v_reusejp_1968_;
}
v_reusejp_1968_:
{
return v___x_1969_;
}
}
}
else
{
if (lean_obj_tag(v___x_1961_) == 0)
{
lean_object* v_a_1972_; lean_object* v___x_1974_; uint8_t v_isShared_1975_; uint8_t v_isSharedCheck_1979_; 
v_a_1972_ = lean_ctor_get(v___x_1961_, 0);
v_isSharedCheck_1979_ = !lean_is_exclusive(v___x_1961_);
if (v_isSharedCheck_1979_ == 0)
{
v___x_1974_ = v___x_1961_;
v_isShared_1975_ = v_isSharedCheck_1979_;
goto v_resetjp_1973_;
}
else
{
lean_inc(v_a_1972_);
lean_dec(v___x_1961_);
v___x_1974_ = lean_box(0);
v_isShared_1975_ = v_isSharedCheck_1979_;
goto v_resetjp_1973_;
}
v_resetjp_1973_:
{
lean_object* v___x_1977_; 
if (v_isShared_1975_ == 0)
{
lean_ctor_set_tag(v___x_1974_, 0);
v___x_1977_ = v___x_1974_;
goto v_reusejp_1976_;
}
else
{
lean_object* v_reuseFailAlloc_1978_; 
v_reuseFailAlloc_1978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1978_, 0, v_a_1972_);
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
lean_object* v_a_1980_; lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_1987_; 
v_a_1980_ = lean_ctor_get(v___x_1961_, 0);
v_isSharedCheck_1987_ = !lean_is_exclusive(v___x_1961_);
if (v_isSharedCheck_1987_ == 0)
{
v___x_1982_ = v___x_1961_;
v_isShared_1983_ = v_isSharedCheck_1987_;
goto v_resetjp_1981_;
}
else
{
lean_inc(v_a_1980_);
lean_dec(v___x_1961_);
v___x_1982_ = lean_box(0);
v_isShared_1983_ = v_isSharedCheck_1987_;
goto v_resetjp_1981_;
}
v_resetjp_1981_:
{
lean_object* v___x_1985_; 
if (v_isShared_1983_ == 0)
{
v___x_1985_ = v___x_1982_;
goto v_reusejp_1984_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(1, 1, 0);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanPrepareModuleHierarchyParams_toJson(lean_object* v_x_1990_){
_start:
{
lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; 
v___x_1991_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__0));
v___x_1992_ = l_Lean_Lsp_instToJsonTextDocumentIdentifier_toJson(v_x_1990_);
v___x_1993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1993_, 0, v___x_1991_);
lean_ctor_set(v___x_1993_, 1, v___x_1992_);
v___x_1994_ = lean_box(0);
v___x_1995_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1995_, 0, v___x_1993_);
lean_ctor_set(v___x_1995_, 1, v___x_1994_);
v___x_1996_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1996_, 0, v___x_1995_);
lean_ctor_set(v___x_1996_, 1, v___x_1994_);
v___x_1997_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0));
v___x_1998_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_1996_, v___x_1997_);
v___x_1999_ = l_Lean_Json_mkObj(v___x_1998_);
lean_dec(v___x_1998_);
return v___x_1999_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanImportMetaKind_ctorIdx(uint8_t v_x_2002_){
_start:
{
switch(v_x_2002_)
{
case 0:
{
lean_object* v___x_2003_; 
v___x_2003_ = lean_unsigned_to_nat(0u);
return v___x_2003_;
}
case 1:
{
lean_object* v___x_2004_; 
v___x_2004_ = lean_unsigned_to_nat(1u);
return v___x_2004_;
}
default: 
{
lean_object* v___x_2005_; 
v___x_2005_ = lean_unsigned_to_nat(2u);
return v___x_2005_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanImportMetaKind_ctorIdx___boxed(lean_object* v_x_2006_){
_start:
{
uint8_t v_x_boxed_2007_; lean_object* v_res_2008_; 
v_x_boxed_2007_ = lean_unbox(v_x_2006_);
v_res_2008_ = l_Lean_Lsp_LeanImportMetaKind_ctorIdx(v_x_boxed_2007_);
return v_res_2008_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanImportMetaKind_toCtorIdx(uint8_t v_x_2009_){
_start:
{
lean_object* v___x_2010_; 
v___x_2010_ = l_Lean_Lsp_LeanImportMetaKind_ctorIdx(v_x_2009_);
return v___x_2010_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanImportMetaKind_toCtorIdx___boxed(lean_object* v_x_2011_){
_start:
{
uint8_t v_x_4__boxed_2012_; lean_object* v_res_2013_; 
v_x_4__boxed_2012_ = lean_unbox(v_x_2011_);
v_res_2013_ = l_Lean_Lsp_LeanImportMetaKind_toCtorIdx(v_x_4__boxed_2012_);
return v_res_2013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanImportMetaKind_ctorElim___redArg(lean_object* v_k_2014_){
_start:
{
lean_inc(v_k_2014_);
return v_k_2014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanImportMetaKind_ctorElim___redArg___boxed(lean_object* v_k_2015_){
_start:
{
lean_object* v_res_2016_; 
v_res_2016_ = l_Lean_Lsp_LeanImportMetaKind_ctorElim___redArg(v_k_2015_);
lean_dec(v_k_2015_);
return v_res_2016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanImportMetaKind_ctorElim(lean_object* v_motive_2017_, lean_object* v_ctorIdx_2018_, uint8_t v_t_2019_, lean_object* v_h_2020_, lean_object* v_k_2021_){
_start:
{
lean_inc(v_k_2021_);
return v_k_2021_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanImportMetaKind_ctorElim___boxed(lean_object* v_motive_2022_, lean_object* v_ctorIdx_2023_, lean_object* v_t_2024_, lean_object* v_h_2025_, lean_object* v_k_2026_){
_start:
{
uint8_t v_t_boxed_2027_; lean_object* v_res_2028_; 
v_t_boxed_2027_ = lean_unbox(v_t_2024_);
v_res_2028_ = l_Lean_Lsp_LeanImportMetaKind_ctorElim(v_motive_2022_, v_ctorIdx_2023_, v_t_boxed_2027_, v_h_2025_, v_k_2026_);
lean_dec(v_k_2026_);
lean_dec(v_ctorIdx_2023_);
return v_res_2028_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanImportMetaKind_nonMeta_elim___redArg(lean_object* v_nonMeta_2029_){
_start:
{
lean_inc(v_nonMeta_2029_);
return v_nonMeta_2029_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanImportMetaKind_nonMeta_elim___redArg___boxed(lean_object* v_nonMeta_2030_){
_start:
{
lean_object* v_res_2031_; 
v_res_2031_ = l_Lean_Lsp_LeanImportMetaKind_nonMeta_elim___redArg(v_nonMeta_2030_);
lean_dec(v_nonMeta_2030_);
return v_res_2031_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanImportMetaKind_nonMeta_elim(lean_object* v_motive_2032_, uint8_t v_t_2033_, lean_object* v_h_2034_, lean_object* v_nonMeta_2035_){
_start:
{
lean_inc(v_nonMeta_2035_);
return v_nonMeta_2035_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanImportMetaKind_nonMeta_elim___boxed(lean_object* v_motive_2036_, lean_object* v_t_2037_, lean_object* v_h_2038_, lean_object* v_nonMeta_2039_){
_start:
{
uint8_t v_t_boxed_2040_; lean_object* v_res_2041_; 
v_t_boxed_2040_ = lean_unbox(v_t_2037_);
v_res_2041_ = l_Lean_Lsp_LeanImportMetaKind_nonMeta_elim(v_motive_2036_, v_t_boxed_2040_, v_h_2038_, v_nonMeta_2039_);
lean_dec(v_nonMeta_2039_);
return v_res_2041_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanImportMetaKind_meta_elim___redArg(lean_object* v_meta_2042_){
_start:
{
lean_inc(v_meta_2042_);
return v_meta_2042_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanImportMetaKind_meta_elim___redArg___boxed(lean_object* v_meta_2043_){
_start:
{
lean_object* v_res_2044_; 
v_res_2044_ = l_Lean_Lsp_LeanImportMetaKind_meta_elim___redArg(v_meta_2043_);
lean_dec(v_meta_2043_);
return v_res_2044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanImportMetaKind_meta_elim(lean_object* v_motive_2045_, uint8_t v_t_2046_, lean_object* v_h_2047_, lean_object* v_meta_2048_){
_start:
{
lean_inc(v_meta_2048_);
return v_meta_2048_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanImportMetaKind_meta_elim___boxed(lean_object* v_motive_2049_, lean_object* v_t_2050_, lean_object* v_h_2051_, lean_object* v_meta_2052_){
_start:
{
uint8_t v_t_boxed_2053_; lean_object* v_res_2054_; 
v_t_boxed_2053_ = lean_unbox(v_t_2050_);
v_res_2054_ = l_Lean_Lsp_LeanImportMetaKind_meta_elim(v_motive_2049_, v_t_boxed_2053_, v_h_2051_, v_meta_2052_);
lean_dec(v_meta_2052_);
return v_res_2054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanImportMetaKind_full_elim___redArg(lean_object* v_full_2055_){
_start:
{
lean_inc(v_full_2055_);
return v_full_2055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanImportMetaKind_full_elim___redArg___boxed(lean_object* v_full_2056_){
_start:
{
lean_object* v_res_2057_; 
v_res_2057_ = l_Lean_Lsp_LeanImportMetaKind_full_elim___redArg(v_full_2056_);
lean_dec(v_full_2056_);
return v_res_2057_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanImportMetaKind_full_elim(lean_object* v_motive_2058_, uint8_t v_t_2059_, lean_object* v_h_2060_, lean_object* v_full_2061_){
_start:
{
lean_inc(v_full_2061_);
return v_full_2061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanImportMetaKind_full_elim___boxed(lean_object* v_motive_2062_, lean_object* v_t_2063_, lean_object* v_h_2064_, lean_object* v_full_2065_){
_start:
{
uint8_t v_t_boxed_2066_; lean_object* v_res_2067_; 
v_t_boxed_2066_ = lean_unbox(v_t_2063_);
v_res_2067_ = l_Lean_Lsp_LeanImportMetaKind_full_elim(v_motive_2062_, v_t_boxed_2066_, v_h_2064_, v_full_2065_);
lean_dec(v_full_2065_);
return v_res_2067_;
}
}
static uint8_t _init_l_Lean_Lsp_instInhabitedLeanImportMetaKind_default(void){
_start:
{
uint8_t v___x_2068_; 
v___x_2068_ = 0;
return v___x_2068_;
}
}
static uint8_t _init_l_Lean_Lsp_instInhabitedLeanImportMetaKind(void){
_start:
{
uint8_t v___x_2069_; 
v___x_2069_ = 0;
return v___x_2069_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson(lean_object* v_json_2086_){
_start:
{
lean_object* v___x_2087_; 
v___x_2087_ = l_Lean_Json_getTag_x3f(v_json_2086_);
if (lean_obj_tag(v___x_2087_) == 0)
{
lean_object* v___x_2088_; 
v___x_2088_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson___closed__0));
return v___x_2088_;
}
else
{
lean_object* v_val_2089_; lean_object* v___x_2090_; uint8_t v___x_2091_; 
v_val_2089_ = lean_ctor_get(v___x_2087_, 0);
lean_inc(v_val_2089_);
lean_dec_ref(v___x_2087_);
v___x_2090_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson___closed__1));
v___x_2091_ = lean_string_dec_eq(v_val_2089_, v___x_2090_);
if (v___x_2091_ == 0)
{
lean_object* v___x_2092_; uint8_t v___x_2093_; 
v___x_2092_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson___closed__2));
v___x_2093_ = lean_string_dec_eq(v_val_2089_, v___x_2092_);
if (v___x_2093_ == 0)
{
lean_object* v___x_2094_; uint8_t v___x_2095_; 
v___x_2094_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson___closed__3));
v___x_2095_ = lean_string_dec_eq(v_val_2089_, v___x_2094_);
lean_dec(v_val_2089_);
if (v___x_2095_ == 0)
{
lean_object* v___x_2096_; 
v___x_2096_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson___closed__4));
return v___x_2096_;
}
else
{
lean_object* v___x_2097_; 
v___x_2097_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson___closed__5));
return v___x_2097_;
}
}
else
{
lean_object* v___x_2098_; 
lean_dec(v_val_2089_);
v___x_2098_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson___closed__6));
return v___x_2098_;
}
}
else
{
lean_object* v___x_2099_; 
lean_dec(v_val_2089_);
v___x_2099_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson___closed__7));
return v___x_2099_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanImportMetaKind_toJson(uint8_t v_x_2108_){
_start:
{
switch(v_x_2108_)
{
case 0:
{
lean_object* v___x_2109_; 
v___x_2109_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanImportMetaKind_toJson___closed__0));
return v___x_2109_;
}
case 1:
{
lean_object* v___x_2110_; 
v___x_2110_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanImportMetaKind_toJson___closed__1));
return v___x_2110_;
}
default: 
{
lean_object* v___x_2111_; 
v___x_2111_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanImportMetaKind_toJson___closed__2));
return v___x_2111_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanImportMetaKind_toJson___boxed(lean_object* v_x_2112_){
_start:
{
uint8_t v_x_64__boxed_2113_; lean_object* v_res_2114_; 
v_x_64__boxed_2113_ = lean_unbox(v_x_2112_);
v_res_2114_ = l_Lean_Lsp_instToJsonLeanImportMetaKind_toJson(v_x_64__boxed_2113_);
return v_res_2114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportKind_fromJson_spec__0(lean_object* v_j_2117_, lean_object* v_k_2118_){
_start:
{
lean_object* v___x_2119_; lean_object* v___x_2120_; 
v___x_2119_ = l_Lean_Json_getObjValD(v_j_2117_, v_k_2118_);
v___x_2120_ = l_Lean_Json_getBool_x3f(v___x_2119_);
lean_dec(v___x_2119_);
return v___x_2120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportKind_fromJson_spec__0___boxed(lean_object* v_j_2121_, lean_object* v_k_2122_){
_start:
{
lean_object* v_res_2123_; 
v_res_2123_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportKind_fromJson_spec__0(v_j_2121_, v_k_2122_);
lean_dec_ref(v_k_2122_);
return v_res_2123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportKind_fromJson_spec__1(lean_object* v_j_2124_, lean_object* v_k_2125_){
_start:
{
lean_object* v___x_2126_; lean_object* v___x_2127_; 
v___x_2126_ = l_Lean_Json_getObjValD(v_j_2124_, v_k_2125_);
v___x_2127_ = l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson(v___x_2126_);
return v___x_2127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportKind_fromJson_spec__1___boxed(lean_object* v_j_2128_, lean_object* v_k_2129_){
_start:
{
lean_object* v_res_2130_; 
v_res_2130_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportKind_fromJson_spec__1(v_j_2128_, v_k_2129_);
lean_dec_ref(v_k_2129_);
return v_res_2130_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__3(void){
_start:
{
uint8_t v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; 
v___x_2137_ = 1;
v___x_2138_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__2));
v___x_2139_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2138_, v___x_2137_);
return v___x_2139_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__4(void){
_start:
{
lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; 
v___x_2140_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6));
v___x_2141_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__3);
v___x_2142_ = lean_string_append(v___x_2141_, v___x_2140_);
return v___x_2142_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__6(void){
_start:
{
uint8_t v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; 
v___x_2145_ = 1;
v___x_2146_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__5));
v___x_2147_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2146_, v___x_2145_);
return v___x_2147_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__7(void){
_start:
{
lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; 
v___x_2148_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__6);
v___x_2149_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__4);
v___x_2150_ = lean_string_append(v___x_2149_, v___x_2148_);
return v___x_2150_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__8(void){
_start:
{
lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; 
v___x_2151_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_2152_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__7);
v___x_2153_ = lean_string_append(v___x_2152_, v___x_2151_);
return v___x_2153_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__11(void){
_start:
{
uint8_t v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; 
v___x_2157_ = 1;
v___x_2158_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__10));
v___x_2159_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2158_, v___x_2157_);
return v___x_2159_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__12(void){
_start:
{
lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; 
v___x_2160_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__11, &l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__11);
v___x_2161_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__4);
v___x_2162_ = lean_string_append(v___x_2161_, v___x_2160_);
return v___x_2162_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__13(void){
_start:
{
lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; 
v___x_2163_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_2164_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__12, &l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__12);
v___x_2165_ = lean_string_append(v___x_2164_, v___x_2163_);
return v___x_2165_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__16(void){
_start:
{
uint8_t v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; 
v___x_2169_ = 1;
v___x_2170_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__15));
v___x_2171_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2170_, v___x_2169_);
return v___x_2171_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__17(void){
_start:
{
lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; 
v___x_2172_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__16, &l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__16_once, _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__16);
v___x_2173_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__4);
v___x_2174_ = lean_string_append(v___x_2173_, v___x_2172_);
return v___x_2174_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__18(void){
_start:
{
lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; 
v___x_2175_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_2176_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__17, &l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__17_once, _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__17);
v___x_2177_ = lean_string_append(v___x_2176_, v___x_2175_);
return v___x_2177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanImportKind_fromJson(lean_object* v_json_2178_){
_start:
{
lean_object* v___x_2179_; lean_object* v___x_2180_; 
v___x_2179_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__0));
lean_inc(v_json_2178_);
v___x_2180_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportKind_fromJson_spec__0(v_json_2178_, v___x_2179_);
if (lean_obj_tag(v___x_2180_) == 0)
{
lean_object* v_a_2181_; lean_object* v___x_2183_; uint8_t v_isShared_2184_; uint8_t v_isSharedCheck_2190_; 
lean_dec(v_json_2178_);
v_a_2181_ = lean_ctor_get(v___x_2180_, 0);
v_isSharedCheck_2190_ = !lean_is_exclusive(v___x_2180_);
if (v_isSharedCheck_2190_ == 0)
{
v___x_2183_ = v___x_2180_;
v_isShared_2184_ = v_isSharedCheck_2190_;
goto v_resetjp_2182_;
}
else
{
lean_inc(v_a_2181_);
lean_dec(v___x_2180_);
v___x_2183_ = lean_box(0);
v_isShared_2184_ = v_isSharedCheck_2190_;
goto v_resetjp_2182_;
}
v_resetjp_2182_:
{
lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2188_; 
v___x_2185_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__8);
v___x_2186_ = lean_string_append(v___x_2185_, v_a_2181_);
lean_dec(v_a_2181_);
if (v_isShared_2184_ == 0)
{
lean_ctor_set(v___x_2183_, 0, v___x_2186_);
v___x_2188_ = v___x_2183_;
goto v_reusejp_2187_;
}
else
{
lean_object* v_reuseFailAlloc_2189_; 
v_reuseFailAlloc_2189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2189_, 0, v___x_2186_);
v___x_2188_ = v_reuseFailAlloc_2189_;
goto v_reusejp_2187_;
}
v_reusejp_2187_:
{
return v___x_2188_;
}
}
}
else
{
if (lean_obj_tag(v___x_2180_) == 0)
{
lean_object* v_a_2191_; lean_object* v___x_2193_; uint8_t v_isShared_2194_; uint8_t v_isSharedCheck_2198_; 
lean_dec(v_json_2178_);
v_a_2191_ = lean_ctor_get(v___x_2180_, 0);
v_isSharedCheck_2198_ = !lean_is_exclusive(v___x_2180_);
if (v_isSharedCheck_2198_ == 0)
{
v___x_2193_ = v___x_2180_;
v_isShared_2194_ = v_isSharedCheck_2198_;
goto v_resetjp_2192_;
}
else
{
lean_inc(v_a_2191_);
lean_dec(v___x_2180_);
v___x_2193_ = lean_box(0);
v_isShared_2194_ = v_isSharedCheck_2198_;
goto v_resetjp_2192_;
}
v_resetjp_2192_:
{
lean_object* v___x_2196_; 
if (v_isShared_2194_ == 0)
{
lean_ctor_set_tag(v___x_2193_, 0);
v___x_2196_ = v___x_2193_;
goto v_reusejp_2195_;
}
else
{
lean_object* v_reuseFailAlloc_2197_; 
v_reuseFailAlloc_2197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2197_, 0, v_a_2191_);
v___x_2196_ = v_reuseFailAlloc_2197_;
goto v_reusejp_2195_;
}
v_reusejp_2195_:
{
return v___x_2196_;
}
}
}
else
{
lean_object* v_a_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; 
v_a_2199_ = lean_ctor_get(v___x_2180_, 0);
lean_inc(v_a_2199_);
lean_dec_ref(v___x_2180_);
v___x_2200_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__9));
lean_inc(v_json_2178_);
v___x_2201_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportKind_fromJson_spec__0(v_json_2178_, v___x_2200_);
if (lean_obj_tag(v___x_2201_) == 0)
{
lean_object* v_a_2202_; lean_object* v___x_2204_; uint8_t v_isShared_2205_; uint8_t v_isSharedCheck_2211_; 
lean_dec(v_a_2199_);
lean_dec(v_json_2178_);
v_a_2202_ = lean_ctor_get(v___x_2201_, 0);
v_isSharedCheck_2211_ = !lean_is_exclusive(v___x_2201_);
if (v_isSharedCheck_2211_ == 0)
{
v___x_2204_ = v___x_2201_;
v_isShared_2205_ = v_isSharedCheck_2211_;
goto v_resetjp_2203_;
}
else
{
lean_inc(v_a_2202_);
lean_dec(v___x_2201_);
v___x_2204_ = lean_box(0);
v_isShared_2205_ = v_isSharedCheck_2211_;
goto v_resetjp_2203_;
}
v_resetjp_2203_:
{
lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2209_; 
v___x_2206_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__13, &l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__13);
v___x_2207_ = lean_string_append(v___x_2206_, v_a_2202_);
lean_dec(v_a_2202_);
if (v_isShared_2205_ == 0)
{
lean_ctor_set(v___x_2204_, 0, v___x_2207_);
v___x_2209_ = v___x_2204_;
goto v_reusejp_2208_;
}
else
{
lean_object* v_reuseFailAlloc_2210_; 
v_reuseFailAlloc_2210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2210_, 0, v___x_2207_);
v___x_2209_ = v_reuseFailAlloc_2210_;
goto v_reusejp_2208_;
}
v_reusejp_2208_:
{
return v___x_2209_;
}
}
}
else
{
if (lean_obj_tag(v___x_2201_) == 0)
{
lean_object* v_a_2212_; lean_object* v___x_2214_; uint8_t v_isShared_2215_; uint8_t v_isSharedCheck_2219_; 
lean_dec(v_a_2199_);
lean_dec(v_json_2178_);
v_a_2212_ = lean_ctor_get(v___x_2201_, 0);
v_isSharedCheck_2219_ = !lean_is_exclusive(v___x_2201_);
if (v_isSharedCheck_2219_ == 0)
{
v___x_2214_ = v___x_2201_;
v_isShared_2215_ = v_isSharedCheck_2219_;
goto v_resetjp_2213_;
}
else
{
lean_inc(v_a_2212_);
lean_dec(v___x_2201_);
v___x_2214_ = lean_box(0);
v_isShared_2215_ = v_isSharedCheck_2219_;
goto v_resetjp_2213_;
}
v_resetjp_2213_:
{
lean_object* v___x_2217_; 
if (v_isShared_2215_ == 0)
{
lean_ctor_set_tag(v___x_2214_, 0);
v___x_2217_ = v___x_2214_;
goto v_reusejp_2216_;
}
else
{
lean_object* v_reuseFailAlloc_2218_; 
v_reuseFailAlloc_2218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2218_, 0, v_a_2212_);
v___x_2217_ = v_reuseFailAlloc_2218_;
goto v_reusejp_2216_;
}
v_reusejp_2216_:
{
return v___x_2217_;
}
}
}
else
{
lean_object* v_a_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; 
v_a_2220_ = lean_ctor_get(v___x_2201_, 0);
lean_inc(v_a_2220_);
lean_dec_ref(v___x_2201_);
v___x_2221_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__14));
v___x_2222_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportKind_fromJson_spec__1(v_json_2178_, v___x_2221_);
if (lean_obj_tag(v___x_2222_) == 0)
{
lean_object* v_a_2223_; lean_object* v___x_2225_; uint8_t v_isShared_2226_; uint8_t v_isSharedCheck_2232_; 
lean_dec(v_a_2220_);
lean_dec(v_a_2199_);
v_a_2223_ = lean_ctor_get(v___x_2222_, 0);
v_isSharedCheck_2232_ = !lean_is_exclusive(v___x_2222_);
if (v_isSharedCheck_2232_ == 0)
{
v___x_2225_ = v___x_2222_;
v_isShared_2226_ = v_isSharedCheck_2232_;
goto v_resetjp_2224_;
}
else
{
lean_inc(v_a_2223_);
lean_dec(v___x_2222_);
v___x_2225_ = lean_box(0);
v_isShared_2226_ = v_isSharedCheck_2232_;
goto v_resetjp_2224_;
}
v_resetjp_2224_:
{
lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2230_; 
v___x_2227_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__18, &l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__18_once, _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__18);
v___x_2228_ = lean_string_append(v___x_2227_, v_a_2223_);
lean_dec(v_a_2223_);
if (v_isShared_2226_ == 0)
{
lean_ctor_set(v___x_2225_, 0, v___x_2228_);
v___x_2230_ = v___x_2225_;
goto v_reusejp_2229_;
}
else
{
lean_object* v_reuseFailAlloc_2231_; 
v_reuseFailAlloc_2231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2231_, 0, v___x_2228_);
v___x_2230_ = v_reuseFailAlloc_2231_;
goto v_reusejp_2229_;
}
v_reusejp_2229_:
{
return v___x_2230_;
}
}
}
else
{
if (lean_obj_tag(v___x_2222_) == 0)
{
lean_object* v_a_2233_; lean_object* v___x_2235_; uint8_t v_isShared_2236_; uint8_t v_isSharedCheck_2240_; 
lean_dec(v_a_2220_);
lean_dec(v_a_2199_);
v_a_2233_ = lean_ctor_get(v___x_2222_, 0);
v_isSharedCheck_2240_ = !lean_is_exclusive(v___x_2222_);
if (v_isSharedCheck_2240_ == 0)
{
v___x_2235_ = v___x_2222_;
v_isShared_2236_ = v_isSharedCheck_2240_;
goto v_resetjp_2234_;
}
else
{
lean_inc(v_a_2233_);
lean_dec(v___x_2222_);
v___x_2235_ = lean_box(0);
v_isShared_2236_ = v_isSharedCheck_2240_;
goto v_resetjp_2234_;
}
v_resetjp_2234_:
{
lean_object* v___x_2238_; 
if (v_isShared_2236_ == 0)
{
lean_ctor_set_tag(v___x_2235_, 0);
v___x_2238_ = v___x_2235_;
goto v_reusejp_2237_;
}
else
{
lean_object* v_reuseFailAlloc_2239_; 
v_reuseFailAlloc_2239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2239_, 0, v_a_2233_);
v___x_2238_ = v_reuseFailAlloc_2239_;
goto v_reusejp_2237_;
}
v_reusejp_2237_:
{
return v___x_2238_;
}
}
}
else
{
lean_object* v_a_2241_; lean_object* v___x_2243_; uint8_t v_isShared_2244_; uint8_t v_isSharedCheck_2252_; 
v_a_2241_ = lean_ctor_get(v___x_2222_, 0);
v_isSharedCheck_2252_ = !lean_is_exclusive(v___x_2222_);
if (v_isSharedCheck_2252_ == 0)
{
v___x_2243_ = v___x_2222_;
v_isShared_2244_ = v_isSharedCheck_2252_;
goto v_resetjp_2242_;
}
else
{
lean_inc(v_a_2241_);
lean_dec(v___x_2222_);
v___x_2243_ = lean_box(0);
v_isShared_2244_ = v_isSharedCheck_2252_;
goto v_resetjp_2242_;
}
v_resetjp_2242_:
{
lean_object* v___x_2245_; uint8_t v___x_2246_; uint8_t v___x_2247_; uint8_t v___x_2248_; lean_object* v___x_2250_; 
v___x_2245_ = lean_alloc_ctor(0, 0, 3);
v___x_2246_ = lean_unbox(v_a_2199_);
lean_dec(v_a_2199_);
lean_ctor_set_uint8(v___x_2245_, 0, v___x_2246_);
v___x_2247_ = lean_unbox(v_a_2220_);
lean_dec(v_a_2220_);
lean_ctor_set_uint8(v___x_2245_, 1, v___x_2247_);
v___x_2248_ = lean_unbox(v_a_2241_);
lean_dec(v_a_2241_);
lean_ctor_set_uint8(v___x_2245_, 2, v___x_2248_);
if (v_isShared_2244_ == 0)
{
lean_ctor_set(v___x_2243_, 0, v___x_2245_);
v___x_2250_ = v___x_2243_;
goto v_reusejp_2249_;
}
else
{
lean_object* v_reuseFailAlloc_2251_; 
v_reuseFailAlloc_2251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2251_, 0, v___x_2245_);
v___x_2250_ = v_reuseFailAlloc_2251_;
goto v_reusejp_2249_;
}
v_reusejp_2249_:
{
return v___x_2250_;
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
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanImportKind_toJson(lean_object* v_x_2255_){
_start:
{
uint8_t v_isPrivate_2256_; uint8_t v_isAll_2257_; uint8_t v_metaKind_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; 
v_isPrivate_2256_ = lean_ctor_get_uint8(v_x_2255_, 0);
v_isAll_2257_ = lean_ctor_get_uint8(v_x_2255_, 1);
v_metaKind_2258_ = lean_ctor_get_uint8(v_x_2255_, 2);
v___x_2259_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__0));
v___x_2260_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2260_, 0, v_isPrivate_2256_);
v___x_2261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2261_, 0, v___x_2259_);
lean_ctor_set(v___x_2261_, 1, v___x_2260_);
v___x_2262_ = lean_box(0);
v___x_2263_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2263_, 0, v___x_2261_);
lean_ctor_set(v___x_2263_, 1, v___x_2262_);
v___x_2264_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__9));
v___x_2265_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2265_, 0, v_isAll_2257_);
v___x_2266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2266_, 0, v___x_2264_);
lean_ctor_set(v___x_2266_, 1, v___x_2265_);
v___x_2267_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2267_, 0, v___x_2266_);
lean_ctor_set(v___x_2267_, 1, v___x_2262_);
v___x_2268_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__14));
v___x_2269_ = l_Lean_Lsp_instToJsonLeanImportMetaKind_toJson(v_metaKind_2258_);
v___x_2270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2270_, 0, v___x_2268_);
lean_ctor_set(v___x_2270_, 1, v___x_2269_);
v___x_2271_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2271_, 0, v___x_2270_);
lean_ctor_set(v___x_2271_, 1, v___x_2262_);
v___x_2272_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2272_, 0, v___x_2271_);
lean_ctor_set(v___x_2272_, 1, v___x_2262_);
v___x_2273_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2273_, 0, v___x_2267_);
lean_ctor_set(v___x_2273_, 1, v___x_2272_);
v___x_2274_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2274_, 0, v___x_2263_);
lean_ctor_set(v___x_2274_, 1, v___x_2273_);
v___x_2275_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0));
v___x_2276_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_2274_, v___x_2275_);
v___x_2277_ = l_Lean_Json_mkObj(v___x_2276_);
lean_dec(v___x_2276_);
return v___x_2277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanImportKind_toJson___boxed(lean_object* v_x_2278_){
_start:
{
lean_object* v_res_2279_; 
v_res_2279_ = l_Lean_Lsp_instToJsonLeanImportKind_toJson(v_x_2278_);
lean_dec_ref(v_x_2278_);
return v_res_2279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImport_fromJson_spec__0(lean_object* v_j_2282_, lean_object* v_k_2283_){
_start:
{
lean_object* v___x_2284_; lean_object* v___x_2285_; 
v___x_2284_ = l_Lean_Json_getObjValD(v_j_2282_, v_k_2283_);
v___x_2285_ = l_Lean_Lsp_instFromJsonLeanModule_fromJson(v___x_2284_);
return v___x_2285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImport_fromJson_spec__0___boxed(lean_object* v_j_2286_, lean_object* v_k_2287_){
_start:
{
lean_object* v_res_2288_; 
v_res_2288_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImport_fromJson_spec__0(v_j_2286_, v_k_2287_);
lean_dec_ref(v_k_2287_);
return v_res_2288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImport_fromJson_spec__1(lean_object* v_j_2289_, lean_object* v_k_2290_){
_start:
{
lean_object* v___x_2291_; lean_object* v___x_2292_; 
v___x_2291_ = l_Lean_Json_getObjValD(v_j_2289_, v_k_2290_);
v___x_2292_ = l_Lean_Lsp_instFromJsonLeanImportKind_fromJson(v___x_2291_);
return v___x_2292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImport_fromJson_spec__1___boxed(lean_object* v_j_2293_, lean_object* v_k_2294_){
_start:
{
lean_object* v_res_2295_; 
v_res_2295_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImport_fromJson_spec__1(v_j_2293_, v_k_2294_);
lean_dec_ref(v_k_2294_);
return v_res_2295_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__3(void){
_start:
{
uint8_t v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; 
v___x_2302_ = 1;
v___x_2303_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__2));
v___x_2304_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2303_, v___x_2302_);
return v___x_2304_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__4(void){
_start:
{
lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; 
v___x_2305_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6));
v___x_2306_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__3);
v___x_2307_ = lean_string_append(v___x_2306_, v___x_2305_);
return v___x_2307_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__6(void){
_start:
{
uint8_t v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; 
v___x_2310_ = 1;
v___x_2311_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__5));
v___x_2312_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2311_, v___x_2310_);
return v___x_2312_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__7(void){
_start:
{
lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; 
v___x_2313_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__6);
v___x_2314_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__4);
v___x_2315_ = lean_string_append(v___x_2314_, v___x_2313_);
return v___x_2315_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__8(void){
_start:
{
lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; 
v___x_2316_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_2317_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__7);
v___x_2318_ = lean_string_append(v___x_2317_, v___x_2316_);
return v___x_2318_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__9(void){
_start:
{
lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; 
v___x_2319_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__11, &l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__11);
v___x_2320_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__4);
v___x_2321_ = lean_string_append(v___x_2320_, v___x_2319_);
return v___x_2321_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__10(void){
_start:
{
lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; 
v___x_2322_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_2323_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__9, &l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__9);
v___x_2324_ = lean_string_append(v___x_2323_, v___x_2322_);
return v___x_2324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanImport_fromJson(lean_object* v_json_2325_){
_start:
{
lean_object* v___x_2326_; lean_object* v___x_2327_; 
v___x_2326_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__0));
lean_inc(v_json_2325_);
v___x_2327_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImport_fromJson_spec__0(v_json_2325_, v___x_2326_);
if (lean_obj_tag(v___x_2327_) == 0)
{
lean_object* v_a_2328_; lean_object* v___x_2330_; uint8_t v_isShared_2331_; uint8_t v_isSharedCheck_2337_; 
lean_dec(v_json_2325_);
v_a_2328_ = lean_ctor_get(v___x_2327_, 0);
v_isSharedCheck_2337_ = !lean_is_exclusive(v___x_2327_);
if (v_isSharedCheck_2337_ == 0)
{
v___x_2330_ = v___x_2327_;
v_isShared_2331_ = v_isSharedCheck_2337_;
goto v_resetjp_2329_;
}
else
{
lean_inc(v_a_2328_);
lean_dec(v___x_2327_);
v___x_2330_ = lean_box(0);
v_isShared_2331_ = v_isSharedCheck_2337_;
goto v_resetjp_2329_;
}
v_resetjp_2329_:
{
lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2335_; 
v___x_2332_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__8);
v___x_2333_ = lean_string_append(v___x_2332_, v_a_2328_);
lean_dec(v_a_2328_);
if (v_isShared_2331_ == 0)
{
lean_ctor_set(v___x_2330_, 0, v___x_2333_);
v___x_2335_ = v___x_2330_;
goto v_reusejp_2334_;
}
else
{
lean_object* v_reuseFailAlloc_2336_; 
v_reuseFailAlloc_2336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2336_, 0, v___x_2333_);
v___x_2335_ = v_reuseFailAlloc_2336_;
goto v_reusejp_2334_;
}
v_reusejp_2334_:
{
return v___x_2335_;
}
}
}
else
{
if (lean_obj_tag(v___x_2327_) == 0)
{
lean_object* v_a_2338_; lean_object* v___x_2340_; uint8_t v_isShared_2341_; uint8_t v_isSharedCheck_2345_; 
lean_dec(v_json_2325_);
v_a_2338_ = lean_ctor_get(v___x_2327_, 0);
v_isSharedCheck_2345_ = !lean_is_exclusive(v___x_2327_);
if (v_isSharedCheck_2345_ == 0)
{
v___x_2340_ = v___x_2327_;
v_isShared_2341_ = v_isSharedCheck_2345_;
goto v_resetjp_2339_;
}
else
{
lean_inc(v_a_2338_);
lean_dec(v___x_2327_);
v___x_2340_ = lean_box(0);
v_isShared_2341_ = v_isSharedCheck_2345_;
goto v_resetjp_2339_;
}
v_resetjp_2339_:
{
lean_object* v___x_2343_; 
if (v_isShared_2341_ == 0)
{
lean_ctor_set_tag(v___x_2340_, 0);
v___x_2343_ = v___x_2340_;
goto v_reusejp_2342_;
}
else
{
lean_object* v_reuseFailAlloc_2344_; 
v_reuseFailAlloc_2344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2344_, 0, v_a_2338_);
v___x_2343_ = v_reuseFailAlloc_2344_;
goto v_reusejp_2342_;
}
v_reusejp_2342_:
{
return v___x_2343_;
}
}
}
else
{
lean_object* v_a_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; 
v_a_2346_ = lean_ctor_get(v___x_2327_, 0);
lean_inc(v_a_2346_);
lean_dec_ref(v___x_2327_);
v___x_2347_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__9));
v___x_2348_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImport_fromJson_spec__1(v_json_2325_, v___x_2347_);
if (lean_obj_tag(v___x_2348_) == 0)
{
lean_object* v_a_2349_; lean_object* v___x_2351_; uint8_t v_isShared_2352_; uint8_t v_isSharedCheck_2358_; 
lean_dec(v_a_2346_);
v_a_2349_ = lean_ctor_get(v___x_2348_, 0);
v_isSharedCheck_2358_ = !lean_is_exclusive(v___x_2348_);
if (v_isSharedCheck_2358_ == 0)
{
v___x_2351_ = v___x_2348_;
v_isShared_2352_ = v_isSharedCheck_2358_;
goto v_resetjp_2350_;
}
else
{
lean_inc(v_a_2349_);
lean_dec(v___x_2348_);
v___x_2351_ = lean_box(0);
v_isShared_2352_ = v_isSharedCheck_2358_;
goto v_resetjp_2350_;
}
v_resetjp_2350_:
{
lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2356_; 
v___x_2353_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__10, &l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__10);
v___x_2354_ = lean_string_append(v___x_2353_, v_a_2349_);
lean_dec(v_a_2349_);
if (v_isShared_2352_ == 0)
{
lean_ctor_set(v___x_2351_, 0, v___x_2354_);
v___x_2356_ = v___x_2351_;
goto v_reusejp_2355_;
}
else
{
lean_object* v_reuseFailAlloc_2357_; 
v_reuseFailAlloc_2357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2357_, 0, v___x_2354_);
v___x_2356_ = v_reuseFailAlloc_2357_;
goto v_reusejp_2355_;
}
v_reusejp_2355_:
{
return v___x_2356_;
}
}
}
else
{
if (lean_obj_tag(v___x_2348_) == 0)
{
lean_object* v_a_2359_; lean_object* v___x_2361_; uint8_t v_isShared_2362_; uint8_t v_isSharedCheck_2366_; 
lean_dec(v_a_2346_);
v_a_2359_ = lean_ctor_get(v___x_2348_, 0);
v_isSharedCheck_2366_ = !lean_is_exclusive(v___x_2348_);
if (v_isSharedCheck_2366_ == 0)
{
v___x_2361_ = v___x_2348_;
v_isShared_2362_ = v_isSharedCheck_2366_;
goto v_resetjp_2360_;
}
else
{
lean_inc(v_a_2359_);
lean_dec(v___x_2348_);
v___x_2361_ = lean_box(0);
v_isShared_2362_ = v_isSharedCheck_2366_;
goto v_resetjp_2360_;
}
v_resetjp_2360_:
{
lean_object* v___x_2364_; 
if (v_isShared_2362_ == 0)
{
lean_ctor_set_tag(v___x_2361_, 0);
v___x_2364_ = v___x_2361_;
goto v_reusejp_2363_;
}
else
{
lean_object* v_reuseFailAlloc_2365_; 
v_reuseFailAlloc_2365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2365_, 0, v_a_2359_);
v___x_2364_ = v_reuseFailAlloc_2365_;
goto v_reusejp_2363_;
}
v_reusejp_2363_:
{
return v___x_2364_;
}
}
}
else
{
lean_object* v_a_2367_; lean_object* v___x_2369_; uint8_t v_isShared_2370_; uint8_t v_isSharedCheck_2375_; 
v_a_2367_ = lean_ctor_get(v___x_2348_, 0);
v_isSharedCheck_2375_ = !lean_is_exclusive(v___x_2348_);
if (v_isSharedCheck_2375_ == 0)
{
v___x_2369_ = v___x_2348_;
v_isShared_2370_ = v_isSharedCheck_2375_;
goto v_resetjp_2368_;
}
else
{
lean_inc(v_a_2367_);
lean_dec(v___x_2348_);
v___x_2369_ = lean_box(0);
v_isShared_2370_ = v_isSharedCheck_2375_;
goto v_resetjp_2368_;
}
v_resetjp_2368_:
{
lean_object* v___x_2371_; lean_object* v___x_2373_; 
v___x_2371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2371_, 0, v_a_2346_);
lean_ctor_set(v___x_2371_, 1, v_a_2367_);
if (v_isShared_2370_ == 0)
{
lean_ctor_set(v___x_2369_, 0, v___x_2371_);
v___x_2373_ = v___x_2369_;
goto v_reusejp_2372_;
}
else
{
lean_object* v_reuseFailAlloc_2374_; 
v_reuseFailAlloc_2374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2374_, 0, v___x_2371_);
v___x_2373_ = v_reuseFailAlloc_2374_;
goto v_reusejp_2372_;
}
v_reusejp_2372_:
{
return v___x_2373_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanImport_toJson(lean_object* v_x_2378_){
_start:
{
lean_object* v_module_2379_; lean_object* v_kind_2380_; lean_object* v___x_2382_; uint8_t v_isShared_2383_; uint8_t v_isSharedCheck_2400_; 
v_module_2379_ = lean_ctor_get(v_x_2378_, 0);
v_kind_2380_ = lean_ctor_get(v_x_2378_, 1);
v_isSharedCheck_2400_ = !lean_is_exclusive(v_x_2378_);
if (v_isSharedCheck_2400_ == 0)
{
v___x_2382_ = v_x_2378_;
v_isShared_2383_ = v_isSharedCheck_2400_;
goto v_resetjp_2381_;
}
else
{
lean_inc(v_kind_2380_);
lean_inc(v_module_2379_);
lean_dec(v_x_2378_);
v___x_2382_ = lean_box(0);
v_isShared_2383_ = v_isSharedCheck_2400_;
goto v_resetjp_2381_;
}
v_resetjp_2381_:
{
lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2387_; 
v___x_2384_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__0));
v___x_2385_ = l_Lean_Lsp_instToJsonLeanModule_toJson(v_module_2379_);
lean_dec_ref(v_module_2379_);
if (v_isShared_2383_ == 0)
{
lean_ctor_set(v___x_2382_, 1, v___x_2385_);
lean_ctor_set(v___x_2382_, 0, v___x_2384_);
v___x_2387_ = v___x_2382_;
goto v_reusejp_2386_;
}
else
{
lean_object* v_reuseFailAlloc_2399_; 
v_reuseFailAlloc_2399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2399_, 0, v___x_2384_);
lean_ctor_set(v_reuseFailAlloc_2399_, 1, v___x_2385_);
v___x_2387_ = v_reuseFailAlloc_2399_;
goto v_reusejp_2386_;
}
v_reusejp_2386_:
{
lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; 
v___x_2388_ = lean_box(0);
v___x_2389_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2389_, 0, v___x_2387_);
lean_ctor_set(v___x_2389_, 1, v___x_2388_);
v___x_2390_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__9));
v___x_2391_ = l_Lean_Lsp_instToJsonLeanImportKind_toJson(v_kind_2380_);
lean_dec_ref(v_kind_2380_);
v___x_2392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2392_, 0, v___x_2390_);
lean_ctor_set(v___x_2392_, 1, v___x_2391_);
v___x_2393_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2393_, 0, v___x_2392_);
lean_ctor_set(v___x_2393_, 1, v___x_2388_);
v___x_2394_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2394_, 0, v___x_2393_);
lean_ctor_set(v___x_2394_, 1, v___x_2388_);
v___x_2395_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2395_, 0, v___x_2389_);
lean_ctor_set(v___x_2395_, 1, v___x_2394_);
v___x_2396_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0));
v___x_2397_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_2395_, v___x_2396_);
v___x_2398_ = l_Lean_Json_mkObj(v___x_2397_);
lean_dec(v___x_2397_);
return v___x_2398_;
}
}
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__2(void){
_start:
{
uint8_t v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; 
v___x_2408_ = 1;
v___x_2409_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__1));
v___x_2410_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2409_, v___x_2408_);
return v___x_2410_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__3(void){
_start:
{
lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; 
v___x_2411_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6));
v___x_2412_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__2, &l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__2);
v___x_2413_ = lean_string_append(v___x_2412_, v___x_2411_);
return v___x_2413_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; 
v___x_2414_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__6);
v___x_2415_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__3);
v___x_2416_ = lean_string_append(v___x_2415_, v___x_2414_);
return v___x_2416_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__5(void){
_start:
{
lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; 
v___x_2417_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_2418_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__4);
v___x_2419_ = lean_string_append(v___x_2418_, v___x_2417_);
return v___x_2419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson(lean_object* v_json_2420_){
_start:
{
lean_object* v___x_2421_; lean_object* v___x_2422_; 
v___x_2421_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__0));
v___x_2422_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImport_fromJson_spec__0(v_json_2420_, v___x_2421_);
if (lean_obj_tag(v___x_2422_) == 0)
{
lean_object* v_a_2423_; lean_object* v___x_2425_; uint8_t v_isShared_2426_; uint8_t v_isSharedCheck_2432_; 
v_a_2423_ = lean_ctor_get(v___x_2422_, 0);
v_isSharedCheck_2432_ = !lean_is_exclusive(v___x_2422_);
if (v_isSharedCheck_2432_ == 0)
{
v___x_2425_ = v___x_2422_;
v_isShared_2426_ = v_isSharedCheck_2432_;
goto v_resetjp_2424_;
}
else
{
lean_inc(v_a_2423_);
lean_dec(v___x_2422_);
v___x_2425_ = lean_box(0);
v_isShared_2426_ = v_isSharedCheck_2432_;
goto v_resetjp_2424_;
}
v_resetjp_2424_:
{
lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2430_; 
v___x_2427_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__5, &l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__5);
v___x_2428_ = lean_string_append(v___x_2427_, v_a_2423_);
lean_dec(v_a_2423_);
if (v_isShared_2426_ == 0)
{
lean_ctor_set(v___x_2425_, 0, v___x_2428_);
v___x_2430_ = v___x_2425_;
goto v_reusejp_2429_;
}
else
{
lean_object* v_reuseFailAlloc_2431_; 
v_reuseFailAlloc_2431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2431_, 0, v___x_2428_);
v___x_2430_ = v_reuseFailAlloc_2431_;
goto v_reusejp_2429_;
}
v_reusejp_2429_:
{
return v___x_2430_;
}
}
}
else
{
if (lean_obj_tag(v___x_2422_) == 0)
{
lean_object* v_a_2433_; lean_object* v___x_2435_; uint8_t v_isShared_2436_; uint8_t v_isSharedCheck_2440_; 
v_a_2433_ = lean_ctor_get(v___x_2422_, 0);
v_isSharedCheck_2440_ = !lean_is_exclusive(v___x_2422_);
if (v_isSharedCheck_2440_ == 0)
{
v___x_2435_ = v___x_2422_;
v_isShared_2436_ = v_isSharedCheck_2440_;
goto v_resetjp_2434_;
}
else
{
lean_inc(v_a_2433_);
lean_dec(v___x_2422_);
v___x_2435_ = lean_box(0);
v_isShared_2436_ = v_isSharedCheck_2440_;
goto v_resetjp_2434_;
}
v_resetjp_2434_:
{
lean_object* v___x_2438_; 
if (v_isShared_2436_ == 0)
{
lean_ctor_set_tag(v___x_2435_, 0);
v___x_2438_ = v___x_2435_;
goto v_reusejp_2437_;
}
else
{
lean_object* v_reuseFailAlloc_2439_; 
v_reuseFailAlloc_2439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2439_, 0, v_a_2433_);
v___x_2438_ = v_reuseFailAlloc_2439_;
goto v_reusejp_2437_;
}
v_reusejp_2437_:
{
return v___x_2438_;
}
}
}
else
{
lean_object* v_a_2441_; lean_object* v___x_2443_; uint8_t v_isShared_2444_; uint8_t v_isSharedCheck_2448_; 
v_a_2441_ = lean_ctor_get(v___x_2422_, 0);
v_isSharedCheck_2448_ = !lean_is_exclusive(v___x_2422_);
if (v_isSharedCheck_2448_ == 0)
{
v___x_2443_ = v___x_2422_;
v_isShared_2444_ = v_isSharedCheck_2448_;
goto v_resetjp_2442_;
}
else
{
lean_inc(v_a_2441_);
lean_dec(v___x_2422_);
v___x_2443_ = lean_box(0);
v_isShared_2444_ = v_isSharedCheck_2448_;
goto v_resetjp_2442_;
}
v_resetjp_2442_:
{
lean_object* v___x_2446_; 
if (v_isShared_2444_ == 0)
{
v___x_2446_ = v___x_2443_;
goto v_reusejp_2445_;
}
else
{
lean_object* v_reuseFailAlloc_2447_; 
v_reuseFailAlloc_2447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2447_, 0, v_a_2441_);
v___x_2446_ = v_reuseFailAlloc_2447_;
goto v_reusejp_2445_;
}
v_reusejp_2445_:
{
return v___x_2446_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanModuleHierarchyImportsParams_toJson(lean_object* v_x_2451_){
_start:
{
lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; 
v___x_2452_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__0));
v___x_2453_ = l_Lean_Lsp_instToJsonLeanModule_toJson(v_x_2451_);
v___x_2454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2454_, 0, v___x_2452_);
lean_ctor_set(v___x_2454_, 1, v___x_2453_);
v___x_2455_ = lean_box(0);
v___x_2456_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2456_, 0, v___x_2454_);
lean_ctor_set(v___x_2456_, 1, v___x_2455_);
v___x_2457_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2457_, 0, v___x_2456_);
lean_ctor_set(v___x_2457_, 1, v___x_2455_);
v___x_2458_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0));
v___x_2459_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_2457_, v___x_2458_);
v___x_2460_ = l_Lean_Json_mkObj(v___x_2459_);
lean_dec(v___x_2459_);
return v___x_2460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanModuleHierarchyImportsParams_toJson___boxed(lean_object* v_x_2461_){
_start:
{
lean_object* v_res_2462_; 
v_res_2462_ = l_Lean_Lsp_instToJsonLeanModuleHierarchyImportsParams_toJson(v_x_2461_);
lean_dec_ref(v_x_2461_);
return v_res_2462_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__2(void){
_start:
{
uint8_t v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; 
v___x_2470_ = 1;
v___x_2471_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__1));
v___x_2472_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2471_, v___x_2470_);
return v___x_2472_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__3(void){
_start:
{
lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; 
v___x_2473_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6));
v___x_2474_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__2, &l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__2);
v___x_2475_ = lean_string_append(v___x_2474_, v___x_2473_);
return v___x_2475_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; 
v___x_2476_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__6);
v___x_2477_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__3);
v___x_2478_ = lean_string_append(v___x_2477_, v___x_2476_);
return v___x_2478_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__5(void){
_start:
{
lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; 
v___x_2479_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_2480_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__4);
v___x_2481_ = lean_string_append(v___x_2480_, v___x_2479_);
return v___x_2481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson(lean_object* v_json_2482_){
_start:
{
lean_object* v___x_2483_; lean_object* v___x_2484_; 
v___x_2483_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__0));
v___x_2484_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImport_fromJson_spec__0(v_json_2482_, v___x_2483_);
if (lean_obj_tag(v___x_2484_) == 0)
{
lean_object* v_a_2485_; lean_object* v___x_2487_; uint8_t v_isShared_2488_; uint8_t v_isSharedCheck_2494_; 
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
v___x_2489_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__5, &l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__5);
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
if (lean_obj_tag(v___x_2484_) == 0)
{
lean_object* v_a_2495_; lean_object* v___x_2497_; uint8_t v_isShared_2498_; uint8_t v_isSharedCheck_2502_; 
v_a_2495_ = lean_ctor_get(v___x_2484_, 0);
v_isSharedCheck_2502_ = !lean_is_exclusive(v___x_2484_);
if (v_isSharedCheck_2502_ == 0)
{
v___x_2497_ = v___x_2484_;
v_isShared_2498_ = v_isSharedCheck_2502_;
goto v_resetjp_2496_;
}
else
{
lean_inc(v_a_2495_);
lean_dec(v___x_2484_);
v___x_2497_ = lean_box(0);
v_isShared_2498_ = v_isSharedCheck_2502_;
goto v_resetjp_2496_;
}
v_resetjp_2496_:
{
lean_object* v___x_2500_; 
if (v_isShared_2498_ == 0)
{
lean_ctor_set_tag(v___x_2497_, 0);
v___x_2500_ = v___x_2497_;
goto v_reusejp_2499_;
}
else
{
lean_object* v_reuseFailAlloc_2501_; 
v_reuseFailAlloc_2501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2501_, 0, v_a_2495_);
v___x_2500_ = v_reuseFailAlloc_2501_;
goto v_reusejp_2499_;
}
v_reusejp_2499_:
{
return v___x_2500_;
}
}
}
else
{
lean_object* v_a_2503_; lean_object* v___x_2505_; uint8_t v_isShared_2506_; uint8_t v_isSharedCheck_2510_; 
v_a_2503_ = lean_ctor_get(v___x_2484_, 0);
v_isSharedCheck_2510_ = !lean_is_exclusive(v___x_2484_);
if (v_isSharedCheck_2510_ == 0)
{
v___x_2505_ = v___x_2484_;
v_isShared_2506_ = v_isSharedCheck_2510_;
goto v_resetjp_2504_;
}
else
{
lean_inc(v_a_2503_);
lean_dec(v___x_2484_);
v___x_2505_ = lean_box(0);
v_isShared_2506_ = v_isSharedCheck_2510_;
goto v_resetjp_2504_;
}
v_resetjp_2504_:
{
lean_object* v___x_2508_; 
if (v_isShared_2506_ == 0)
{
v___x_2508_ = v___x_2505_;
goto v_reusejp_2507_;
}
else
{
lean_object* v_reuseFailAlloc_2509_; 
v_reuseFailAlloc_2509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2509_, 0, v_a_2503_);
v___x_2508_ = v_reuseFailAlloc_2509_;
goto v_reusejp_2507_;
}
v_reusejp_2507_:
{
return v___x_2508_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanModuleHierarchyImportedByParams_toJson(lean_object* v_x_2513_){
_start:
{
lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; 
v___x_2514_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__0));
v___x_2515_ = l_Lean_Lsp_instToJsonLeanModule_toJson(v_x_2513_);
v___x_2516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2516_, 0, v___x_2514_);
lean_ctor_set(v___x_2516_, 1, v___x_2515_);
v___x_2517_ = lean_box(0);
v___x_2518_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2518_, 0, v___x_2516_);
lean_ctor_set(v___x_2518_, 1, v___x_2517_);
v___x_2519_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2519_, 0, v___x_2518_);
lean_ctor_set(v___x_2519_, 1, v___x_2517_);
v___x_2520_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0));
v___x_2521_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_2519_, v___x_2520_);
v___x_2522_ = l_Lean_Json_mkObj(v___x_2521_);
lean_dec(v___x_2521_);
return v___x_2522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanModuleHierarchyImportedByParams_toJson___boxed(lean_object* v_x_2523_){
_start:
{
lean_object* v_res_2524_; 
v_res_2524_ = l_Lean_Lsp_instToJsonLeanModuleHierarchyImportedByParams_toJson(v_x_2523_);
lean_dec_ref(v_x_2523_);
return v_res_2524_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__2(void){
_start:
{
uint8_t v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; 
v___x_2532_ = 1;
v___x_2533_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__1));
v___x_2534_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2533_, v___x_2532_);
return v___x_2534_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__3(void){
_start:
{
lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; 
v___x_2535_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6));
v___x_2536_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__2, &l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__2);
v___x_2537_ = lean_string_append(v___x_2536_, v___x_2535_);
return v___x_2537_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; 
v___x_2538_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__6, &l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__6);
v___x_2539_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__3);
v___x_2540_ = lean_string_append(v___x_2539_, v___x_2538_);
return v___x_2540_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__5(void){
_start:
{
lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; 
v___x_2541_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_2542_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__4);
v___x_2543_ = lean_string_append(v___x_2542_, v___x_2541_);
return v___x_2543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson(lean_object* v_json_2544_){
_start:
{
lean_object* v___x_2545_; lean_object* v___x_2546_; 
v___x_2545_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__0));
v___x_2546_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson_spec__0(v_json_2544_, v___x_2545_);
if (lean_obj_tag(v___x_2546_) == 0)
{
lean_object* v_a_2547_; lean_object* v___x_2549_; uint8_t v_isShared_2550_; uint8_t v_isSharedCheck_2556_; 
v_a_2547_ = lean_ctor_get(v___x_2546_, 0);
v_isSharedCheck_2556_ = !lean_is_exclusive(v___x_2546_);
if (v_isSharedCheck_2556_ == 0)
{
v___x_2549_ = v___x_2546_;
v_isShared_2550_ = v_isSharedCheck_2556_;
goto v_resetjp_2548_;
}
else
{
lean_inc(v_a_2547_);
lean_dec(v___x_2546_);
v___x_2549_ = lean_box(0);
v_isShared_2550_ = v_isSharedCheck_2556_;
goto v_resetjp_2548_;
}
v_resetjp_2548_:
{
lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2554_; 
v___x_2551_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__5, &l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__5);
v___x_2552_ = lean_string_append(v___x_2551_, v_a_2547_);
lean_dec(v_a_2547_);
if (v_isShared_2550_ == 0)
{
lean_ctor_set(v___x_2549_, 0, v___x_2552_);
v___x_2554_ = v___x_2549_;
goto v_reusejp_2553_;
}
else
{
lean_object* v_reuseFailAlloc_2555_; 
v_reuseFailAlloc_2555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2555_, 0, v___x_2552_);
v___x_2554_ = v_reuseFailAlloc_2555_;
goto v_reusejp_2553_;
}
v_reusejp_2553_:
{
return v___x_2554_;
}
}
}
else
{
if (lean_obj_tag(v___x_2546_) == 0)
{
lean_object* v_a_2557_; lean_object* v___x_2559_; uint8_t v_isShared_2560_; uint8_t v_isSharedCheck_2564_; 
v_a_2557_ = lean_ctor_get(v___x_2546_, 0);
v_isSharedCheck_2564_ = !lean_is_exclusive(v___x_2546_);
if (v_isSharedCheck_2564_ == 0)
{
v___x_2559_ = v___x_2546_;
v_isShared_2560_ = v_isSharedCheck_2564_;
goto v_resetjp_2558_;
}
else
{
lean_inc(v_a_2557_);
lean_dec(v___x_2546_);
v___x_2559_ = lean_box(0);
v_isShared_2560_ = v_isSharedCheck_2564_;
goto v_resetjp_2558_;
}
v_resetjp_2558_:
{
lean_object* v___x_2562_; 
if (v_isShared_2560_ == 0)
{
lean_ctor_set_tag(v___x_2559_, 0);
v___x_2562_ = v___x_2559_;
goto v_reusejp_2561_;
}
else
{
lean_object* v_reuseFailAlloc_2563_; 
v_reuseFailAlloc_2563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2563_, 0, v_a_2557_);
v___x_2562_ = v_reuseFailAlloc_2563_;
goto v_reusejp_2561_;
}
v_reusejp_2561_:
{
return v___x_2562_;
}
}
}
else
{
lean_object* v_a_2565_; lean_object* v___x_2567_; uint8_t v_isShared_2568_; uint8_t v_isSharedCheck_2572_; 
v_a_2565_ = lean_ctor_get(v___x_2546_, 0);
v_isSharedCheck_2572_ = !lean_is_exclusive(v___x_2546_);
if (v_isSharedCheck_2572_ == 0)
{
v___x_2567_ = v___x_2546_;
v_isShared_2568_ = v_isSharedCheck_2572_;
goto v_resetjp_2566_;
}
else
{
lean_inc(v_a_2565_);
lean_dec(v___x_2546_);
v___x_2567_ = lean_box(0);
v_isShared_2568_ = v_isSharedCheck_2572_;
goto v_resetjp_2566_;
}
v_resetjp_2566_:
{
lean_object* v___x_2570_; 
if (v_isShared_2568_ == 0)
{
v___x_2570_ = v___x_2567_;
goto v_reusejp_2569_;
}
else
{
lean_object* v_reuseFailAlloc_2571_; 
v_reuseFailAlloc_2571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2571_, 0, v_a_2565_);
v___x_2570_ = v_reuseFailAlloc_2571_;
goto v_reusejp_2569_;
}
v_reusejp_2569_:
{
return v___x_2570_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRpcConnectParams_toJson(lean_object* v_x_2575_){
_start:
{
lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; 
v___x_2576_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__0));
v___x_2577_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2577_, 0, v_x_2575_);
v___x_2578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2578_, 0, v___x_2576_);
lean_ctor_set(v___x_2578_, 1, v___x_2577_);
v___x_2579_ = lean_box(0);
v___x_2580_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2580_, 0, v___x_2578_);
lean_ctor_set(v___x_2580_, 1, v___x_2579_);
v___x_2581_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2581_, 0, v___x_2580_);
lean_ctor_set(v___x_2581_, 1, v___x_2579_);
v___x_2582_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0));
v___x_2583_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_2581_, v___x_2582_);
v___x_2584_ = l_Lean_Json_mkObj(v___x_2583_);
lean_dec(v___x_2583_);
return v___x_2584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcConnected_fromJson_spec__0(lean_object* v_j_2587_, lean_object* v_k_2588_){
_start:
{
lean_object* v___x_2589_; lean_object* v___x_2590_; 
v___x_2589_ = l_Lean_Json_getObjValD(v_j_2587_, v_k_2588_);
v___x_2590_ = l_UInt64_fromJson_x3f(v___x_2589_);
return v___x_2590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcConnected_fromJson_spec__0___boxed(lean_object* v_j_2591_, lean_object* v_k_2592_){
_start:
{
lean_object* v_res_2593_; 
v_res_2593_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcConnected_fromJson_spec__0(v_j_2591_, v_k_2592_);
lean_dec_ref(v_k_2592_);
return v_res_2593_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__3(void){
_start:
{
uint8_t v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; 
v___x_2600_ = 1;
v___x_2601_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__2));
v___x_2602_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2601_, v___x_2600_);
return v___x_2602_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__4(void){
_start:
{
lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; 
v___x_2603_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6));
v___x_2604_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__3, &l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__3);
v___x_2605_ = lean_string_append(v___x_2604_, v___x_2603_);
return v___x_2605_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__6(void){
_start:
{
uint8_t v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; 
v___x_2608_ = 1;
v___x_2609_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__5));
v___x_2610_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2609_, v___x_2608_);
return v___x_2610_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__7(void){
_start:
{
lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; 
v___x_2611_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__6, &l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__6);
v___x_2612_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__4, &l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__4);
v___x_2613_ = lean_string_append(v___x_2612_, v___x_2611_);
return v___x_2613_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__8(void){
_start:
{
lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; 
v___x_2614_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_2615_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__7, &l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__7);
v___x_2616_ = lean_string_append(v___x_2615_, v___x_2614_);
return v___x_2616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonRpcConnected_fromJson(lean_object* v_json_2617_){
_start:
{
lean_object* v___x_2618_; lean_object* v___x_2619_; 
v___x_2618_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__0));
v___x_2619_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcConnected_fromJson_spec__0(v_json_2617_, v___x_2618_);
if (lean_obj_tag(v___x_2619_) == 0)
{
lean_object* v_a_2620_; lean_object* v___x_2622_; uint8_t v_isShared_2623_; uint8_t v_isSharedCheck_2629_; 
v_a_2620_ = lean_ctor_get(v___x_2619_, 0);
v_isSharedCheck_2629_ = !lean_is_exclusive(v___x_2619_);
if (v_isSharedCheck_2629_ == 0)
{
v___x_2622_ = v___x_2619_;
v_isShared_2623_ = v_isSharedCheck_2629_;
goto v_resetjp_2621_;
}
else
{
lean_inc(v_a_2620_);
lean_dec(v___x_2619_);
v___x_2622_ = lean_box(0);
v_isShared_2623_ = v_isSharedCheck_2629_;
goto v_resetjp_2621_;
}
v_resetjp_2621_:
{
lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2627_; 
v___x_2624_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__8, &l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__8);
v___x_2625_ = lean_string_append(v___x_2624_, v_a_2620_);
lean_dec(v_a_2620_);
if (v_isShared_2623_ == 0)
{
lean_ctor_set(v___x_2622_, 0, v___x_2625_);
v___x_2627_ = v___x_2622_;
goto v_reusejp_2626_;
}
else
{
lean_object* v_reuseFailAlloc_2628_; 
v_reuseFailAlloc_2628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2628_, 0, v___x_2625_);
v___x_2627_ = v_reuseFailAlloc_2628_;
goto v_reusejp_2626_;
}
v_reusejp_2626_:
{
return v___x_2627_;
}
}
}
else
{
if (lean_obj_tag(v___x_2619_) == 0)
{
lean_object* v_a_2630_; lean_object* v___x_2632_; uint8_t v_isShared_2633_; uint8_t v_isSharedCheck_2637_; 
v_a_2630_ = lean_ctor_get(v___x_2619_, 0);
v_isSharedCheck_2637_ = !lean_is_exclusive(v___x_2619_);
if (v_isSharedCheck_2637_ == 0)
{
v___x_2632_ = v___x_2619_;
v_isShared_2633_ = v_isSharedCheck_2637_;
goto v_resetjp_2631_;
}
else
{
lean_inc(v_a_2630_);
lean_dec(v___x_2619_);
v___x_2632_ = lean_box(0);
v_isShared_2633_ = v_isSharedCheck_2637_;
goto v_resetjp_2631_;
}
v_resetjp_2631_:
{
lean_object* v___x_2635_; 
if (v_isShared_2633_ == 0)
{
lean_ctor_set_tag(v___x_2632_, 0);
v___x_2635_ = v___x_2632_;
goto v_reusejp_2634_;
}
else
{
lean_object* v_reuseFailAlloc_2636_; 
v_reuseFailAlloc_2636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2636_, 0, v_a_2630_);
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
lean_object* v_a_2638_; lean_object* v___x_2640_; uint8_t v_isShared_2641_; uint8_t v_isSharedCheck_2645_; 
v_a_2638_ = lean_ctor_get(v___x_2619_, 0);
v_isSharedCheck_2645_ = !lean_is_exclusive(v___x_2619_);
if (v_isSharedCheck_2645_ == 0)
{
v___x_2640_ = v___x_2619_;
v_isShared_2641_ = v_isSharedCheck_2645_;
goto v_resetjp_2639_;
}
else
{
lean_inc(v_a_2638_);
lean_dec(v___x_2619_);
v___x_2640_ = lean_box(0);
v_isShared_2641_ = v_isSharedCheck_2645_;
goto v_resetjp_2639_;
}
v_resetjp_2639_:
{
lean_object* v___x_2643_; 
if (v_isShared_2641_ == 0)
{
v___x_2643_ = v___x_2640_;
goto v_reusejp_2642_;
}
else
{
lean_object* v_reuseFailAlloc_2644_; 
v_reuseFailAlloc_2644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2644_, 0, v_a_2638_);
v___x_2643_ = v_reuseFailAlloc_2644_;
goto v_reusejp_2642_;
}
v_reusejp_2642_:
{
return v___x_2643_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRpcConnected_toJson(uint64_t v_x_2648_){
_start:
{
lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; 
v___x_2649_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__0));
v___x_2650_ = lean_uint64_to_nat(v_x_2648_);
v___x_2651_ = l_Lean_bignumToJson(v___x_2650_);
v___x_2652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2652_, 0, v___x_2649_);
lean_ctor_set(v___x_2652_, 1, v___x_2651_);
v___x_2653_ = lean_box(0);
v___x_2654_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2654_, 0, v___x_2652_);
lean_ctor_set(v___x_2654_, 1, v___x_2653_);
v___x_2655_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2655_, 0, v___x_2654_);
lean_ctor_set(v___x_2655_, 1, v___x_2653_);
v___x_2656_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0));
v___x_2657_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_2655_, v___x_2656_);
v___x_2658_ = l_Lean_Json_mkObj(v___x_2657_);
lean_dec(v___x_2657_);
return v___x_2658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRpcConnected_toJson___boxed(lean_object* v_x_2659_){
_start:
{
uint64_t v_x_30__boxed_2660_; lean_object* v_res_2661_; 
v_x_30__boxed_2660_ = lean_unbox_uint64(v_x_2659_);
lean_dec_ref(v_x_2659_);
v_res_2661_ = l_Lean_Lsp_instToJsonRpcConnected_toJson(v_x_30__boxed_2660_);
return v_res_2661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcCallParams_fromJson_spec__0(lean_object* v_j_2664_, lean_object* v_k_2665_){
_start:
{
lean_object* v___x_2666_; lean_object* v___x_2667_; 
v___x_2666_ = l_Lean_Json_getObjValD(v_j_2664_, v_k_2665_);
v___x_2667_ = l_Lean_Name_fromJson_x3f(v___x_2666_);
return v___x_2667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcCallParams_fromJson_spec__0___boxed(lean_object* v_j_2668_, lean_object* v_k_2669_){
_start:
{
lean_object* v_res_2670_; 
v_res_2670_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcCallParams_fromJson_spec__0(v_j_2668_, v_k_2669_);
lean_dec_ref(v_k_2669_);
return v_res_2670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcCallParams_fromJson_spec__1(lean_object* v_j_2671_, lean_object* v_k_2672_){
_start:
{
lean_object* v___x_2673_; lean_object* v___x_2674_; 
v___x_2673_ = l_Lean_Json_getObjValD(v_j_2671_, v_k_2672_);
v___x_2674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2674_, 0, v___x_2673_);
return v___x_2674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcCallParams_fromJson_spec__1___boxed(lean_object* v_j_2675_, lean_object* v_k_2676_){
_start:
{
lean_object* v_res_2677_; 
v_res_2677_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcCallParams_fromJson_spec__1(v_j_2675_, v_k_2676_);
lean_dec_ref(v_k_2676_);
return v_res_2677_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__2(void){
_start:
{
uint8_t v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; 
v___x_2683_ = 1;
v___x_2684_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__1));
v___x_2685_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2684_, v___x_2683_);
return v___x_2685_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__3(void){
_start:
{
lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; 
v___x_2686_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6));
v___x_2687_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__2, &l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__2);
v___x_2688_ = lean_string_append(v___x_2687_, v___x_2686_);
return v___x_2688_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; 
v___x_2689_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9, &l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9);
v___x_2690_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__3);
v___x_2691_ = lean_string_append(v___x_2690_, v___x_2689_);
return v___x_2691_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__5(void){
_start:
{
lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; 
v___x_2692_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_2693_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__4);
v___x_2694_ = lean_string_append(v___x_2693_, v___x_2692_);
return v___x_2694_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__6(void){
_start:
{
lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; 
v___x_2695_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__8);
v___x_2696_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__3);
v___x_2697_ = lean_string_append(v___x_2696_, v___x_2695_);
return v___x_2697_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__7(void){
_start:
{
lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; 
v___x_2698_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_2699_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__6, &l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__6);
v___x_2700_ = lean_string_append(v___x_2699_, v___x_2698_);
return v___x_2700_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__8(void){
_start:
{
lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; 
v___x_2701_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__6, &l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__6);
v___x_2702_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__3);
v___x_2703_ = lean_string_append(v___x_2702_, v___x_2701_);
return v___x_2703_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__9(void){
_start:
{
lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; 
v___x_2704_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_2705_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__8);
v___x_2706_ = lean_string_append(v___x_2705_, v___x_2704_);
return v___x_2706_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__12(void){
_start:
{
uint8_t v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; 
v___x_2710_ = 1;
v___x_2711_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__11));
v___x_2712_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2711_, v___x_2710_);
return v___x_2712_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__13(void){
_start:
{
lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; 
v___x_2713_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__12, &l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__12);
v___x_2714_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__3);
v___x_2715_ = lean_string_append(v___x_2714_, v___x_2713_);
return v___x_2715_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__14(void){
_start:
{
lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; 
v___x_2716_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_2717_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__13, &l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__13);
v___x_2718_ = lean_string_append(v___x_2717_, v___x_2716_);
return v___x_2718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonRpcCallParams_fromJson(lean_object* v_json_2720_){
_start:
{
lean_object* v___x_2721_; lean_object* v___x_2722_; 
v___x_2721_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__0));
lean_inc(v_json_2720_);
v___x_2722_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoalParams_fromJson_spec__0(v_json_2720_, v___x_2721_);
if (lean_obj_tag(v___x_2722_) == 0)
{
lean_object* v_a_2723_; lean_object* v___x_2725_; uint8_t v_isShared_2726_; uint8_t v_isSharedCheck_2732_; 
lean_dec(v_json_2720_);
v_a_2723_ = lean_ctor_get(v___x_2722_, 0);
v_isSharedCheck_2732_ = !lean_is_exclusive(v___x_2722_);
if (v_isSharedCheck_2732_ == 0)
{
v___x_2725_ = v___x_2722_;
v_isShared_2726_ = v_isSharedCheck_2732_;
goto v_resetjp_2724_;
}
else
{
lean_inc(v_a_2723_);
lean_dec(v___x_2722_);
v___x_2725_ = lean_box(0);
v_isShared_2726_ = v_isSharedCheck_2732_;
goto v_resetjp_2724_;
}
v_resetjp_2724_:
{
lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2730_; 
v___x_2727_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__5, &l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__5);
v___x_2728_ = lean_string_append(v___x_2727_, v_a_2723_);
lean_dec(v_a_2723_);
if (v_isShared_2726_ == 0)
{
lean_ctor_set(v___x_2725_, 0, v___x_2728_);
v___x_2730_ = v___x_2725_;
goto v_reusejp_2729_;
}
else
{
lean_object* v_reuseFailAlloc_2731_; 
v_reuseFailAlloc_2731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2731_, 0, v___x_2728_);
v___x_2730_ = v_reuseFailAlloc_2731_;
goto v_reusejp_2729_;
}
v_reusejp_2729_:
{
return v___x_2730_;
}
}
}
else
{
if (lean_obj_tag(v___x_2722_) == 0)
{
lean_object* v_a_2733_; lean_object* v___x_2735_; uint8_t v_isShared_2736_; uint8_t v_isSharedCheck_2740_; 
lean_dec(v_json_2720_);
v_a_2733_ = lean_ctor_get(v___x_2722_, 0);
v_isSharedCheck_2740_ = !lean_is_exclusive(v___x_2722_);
if (v_isSharedCheck_2740_ == 0)
{
v___x_2735_ = v___x_2722_;
v_isShared_2736_ = v_isSharedCheck_2740_;
goto v_resetjp_2734_;
}
else
{
lean_inc(v_a_2733_);
lean_dec(v___x_2722_);
v___x_2735_ = lean_box(0);
v_isShared_2736_ = v_isSharedCheck_2740_;
goto v_resetjp_2734_;
}
v_resetjp_2734_:
{
lean_object* v___x_2738_; 
if (v_isShared_2736_ == 0)
{
lean_ctor_set_tag(v___x_2735_, 0);
v___x_2738_ = v___x_2735_;
goto v_reusejp_2737_;
}
else
{
lean_object* v_reuseFailAlloc_2739_; 
v_reuseFailAlloc_2739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2739_, 0, v_a_2733_);
v___x_2738_ = v_reuseFailAlloc_2739_;
goto v_reusejp_2737_;
}
v_reusejp_2737_:
{
return v___x_2738_;
}
}
}
else
{
lean_object* v_a_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; 
v_a_2741_ = lean_ctor_get(v___x_2722_, 0);
lean_inc(v_a_2741_);
lean_dec_ref(v___x_2722_);
v___x_2742_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__6));
lean_inc(v_json_2720_);
v___x_2743_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoalParams_fromJson_spec__1(v_json_2720_, v___x_2742_);
if (lean_obj_tag(v___x_2743_) == 0)
{
lean_object* v_a_2744_; lean_object* v___x_2746_; uint8_t v_isShared_2747_; uint8_t v_isSharedCheck_2753_; 
lean_dec(v_a_2741_);
lean_dec(v_json_2720_);
v_a_2744_ = lean_ctor_get(v___x_2743_, 0);
v_isSharedCheck_2753_ = !lean_is_exclusive(v___x_2743_);
if (v_isSharedCheck_2753_ == 0)
{
v___x_2746_ = v___x_2743_;
v_isShared_2747_ = v_isSharedCheck_2753_;
goto v_resetjp_2745_;
}
else
{
lean_inc(v_a_2744_);
lean_dec(v___x_2743_);
v___x_2746_ = lean_box(0);
v_isShared_2747_ = v_isSharedCheck_2753_;
goto v_resetjp_2745_;
}
v_resetjp_2745_:
{
lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2751_; 
v___x_2748_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__7);
v___x_2749_ = lean_string_append(v___x_2748_, v_a_2744_);
lean_dec(v_a_2744_);
if (v_isShared_2747_ == 0)
{
lean_ctor_set(v___x_2746_, 0, v___x_2749_);
v___x_2751_ = v___x_2746_;
goto v_reusejp_2750_;
}
else
{
lean_object* v_reuseFailAlloc_2752_; 
v_reuseFailAlloc_2752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2752_, 0, v___x_2749_);
v___x_2751_ = v_reuseFailAlloc_2752_;
goto v_reusejp_2750_;
}
v_reusejp_2750_:
{
return v___x_2751_;
}
}
}
else
{
if (lean_obj_tag(v___x_2743_) == 0)
{
lean_object* v_a_2754_; lean_object* v___x_2756_; uint8_t v_isShared_2757_; uint8_t v_isSharedCheck_2761_; 
lean_dec(v_a_2741_);
lean_dec(v_json_2720_);
v_a_2754_ = lean_ctor_get(v___x_2743_, 0);
v_isSharedCheck_2761_ = !lean_is_exclusive(v___x_2743_);
if (v_isSharedCheck_2761_ == 0)
{
v___x_2756_ = v___x_2743_;
v_isShared_2757_ = v_isSharedCheck_2761_;
goto v_resetjp_2755_;
}
else
{
lean_inc(v_a_2754_);
lean_dec(v___x_2743_);
v___x_2756_ = lean_box(0);
v_isShared_2757_ = v_isSharedCheck_2761_;
goto v_resetjp_2755_;
}
v_resetjp_2755_:
{
lean_object* v___x_2759_; 
if (v_isShared_2757_ == 0)
{
lean_ctor_set_tag(v___x_2756_, 0);
v___x_2759_ = v___x_2756_;
goto v_reusejp_2758_;
}
else
{
lean_object* v_reuseFailAlloc_2760_; 
v_reuseFailAlloc_2760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2760_, 0, v_a_2754_);
v___x_2759_ = v_reuseFailAlloc_2760_;
goto v_reusejp_2758_;
}
v_reusejp_2758_:
{
return v___x_2759_;
}
}
}
else
{
lean_object* v_a_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; 
v_a_2762_ = lean_ctor_get(v___x_2743_, 0);
lean_inc(v_a_2762_);
lean_dec_ref(v___x_2743_);
v___x_2763_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__0));
lean_inc(v_json_2720_);
v___x_2764_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcConnected_fromJson_spec__0(v_json_2720_, v___x_2763_);
if (lean_obj_tag(v___x_2764_) == 0)
{
lean_object* v_a_2765_; lean_object* v___x_2767_; uint8_t v_isShared_2768_; uint8_t v_isSharedCheck_2774_; 
lean_dec(v_a_2762_);
lean_dec(v_a_2741_);
lean_dec(v_json_2720_);
v_a_2765_ = lean_ctor_get(v___x_2764_, 0);
v_isSharedCheck_2774_ = !lean_is_exclusive(v___x_2764_);
if (v_isSharedCheck_2774_ == 0)
{
v___x_2767_ = v___x_2764_;
v_isShared_2768_ = v_isSharedCheck_2774_;
goto v_resetjp_2766_;
}
else
{
lean_inc(v_a_2765_);
lean_dec(v___x_2764_);
v___x_2767_ = lean_box(0);
v_isShared_2768_ = v_isSharedCheck_2774_;
goto v_resetjp_2766_;
}
v_resetjp_2766_:
{
lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2772_; 
v___x_2769_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__9, &l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__9);
v___x_2770_ = lean_string_append(v___x_2769_, v_a_2765_);
lean_dec(v_a_2765_);
if (v_isShared_2768_ == 0)
{
lean_ctor_set(v___x_2767_, 0, v___x_2770_);
v___x_2772_ = v___x_2767_;
goto v_reusejp_2771_;
}
else
{
lean_object* v_reuseFailAlloc_2773_; 
v_reuseFailAlloc_2773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2773_, 0, v___x_2770_);
v___x_2772_ = v_reuseFailAlloc_2773_;
goto v_reusejp_2771_;
}
v_reusejp_2771_:
{
return v___x_2772_;
}
}
}
else
{
if (lean_obj_tag(v___x_2764_) == 0)
{
lean_object* v_a_2775_; lean_object* v___x_2777_; uint8_t v_isShared_2778_; uint8_t v_isSharedCheck_2782_; 
lean_dec(v_a_2762_);
lean_dec(v_a_2741_);
lean_dec(v_json_2720_);
v_a_2775_ = lean_ctor_get(v___x_2764_, 0);
v_isSharedCheck_2782_ = !lean_is_exclusive(v___x_2764_);
if (v_isSharedCheck_2782_ == 0)
{
v___x_2777_ = v___x_2764_;
v_isShared_2778_ = v_isSharedCheck_2782_;
goto v_resetjp_2776_;
}
else
{
lean_inc(v_a_2775_);
lean_dec(v___x_2764_);
v___x_2777_ = lean_box(0);
v_isShared_2778_ = v_isSharedCheck_2782_;
goto v_resetjp_2776_;
}
v_resetjp_2776_:
{
lean_object* v___x_2780_; 
if (v_isShared_2778_ == 0)
{
lean_ctor_set_tag(v___x_2777_, 0);
v___x_2780_ = v___x_2777_;
goto v_reusejp_2779_;
}
else
{
lean_object* v_reuseFailAlloc_2781_; 
v_reuseFailAlloc_2781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2781_, 0, v_a_2775_);
v___x_2780_ = v_reuseFailAlloc_2781_;
goto v_reusejp_2779_;
}
v_reusejp_2779_:
{
return v___x_2780_;
}
}
}
else
{
lean_object* v_a_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; 
v_a_2783_ = lean_ctor_get(v___x_2764_, 0);
lean_inc(v_a_2783_);
lean_dec_ref(v___x_2764_);
v___x_2784_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__10));
lean_inc(v_json_2720_);
v___x_2785_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcCallParams_fromJson_spec__0(v_json_2720_, v___x_2784_);
if (lean_obj_tag(v___x_2785_) == 0)
{
lean_object* v_a_2786_; lean_object* v___x_2788_; uint8_t v_isShared_2789_; uint8_t v_isSharedCheck_2795_; 
lean_dec(v_a_2783_);
lean_dec(v_a_2762_);
lean_dec(v_a_2741_);
lean_dec(v_json_2720_);
v_a_2786_ = lean_ctor_get(v___x_2785_, 0);
v_isSharedCheck_2795_ = !lean_is_exclusive(v___x_2785_);
if (v_isSharedCheck_2795_ == 0)
{
v___x_2788_ = v___x_2785_;
v_isShared_2789_ = v_isSharedCheck_2795_;
goto v_resetjp_2787_;
}
else
{
lean_inc(v_a_2786_);
lean_dec(v___x_2785_);
v___x_2788_ = lean_box(0);
v_isShared_2789_ = v_isSharedCheck_2795_;
goto v_resetjp_2787_;
}
v_resetjp_2787_:
{
lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2793_; 
v___x_2790_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__14, &l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__14_once, _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__14);
v___x_2791_ = lean_string_append(v___x_2790_, v_a_2786_);
lean_dec(v_a_2786_);
if (v_isShared_2789_ == 0)
{
lean_ctor_set(v___x_2788_, 0, v___x_2791_);
v___x_2793_ = v___x_2788_;
goto v_reusejp_2792_;
}
else
{
lean_object* v_reuseFailAlloc_2794_; 
v_reuseFailAlloc_2794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2794_, 0, v___x_2791_);
v___x_2793_ = v_reuseFailAlloc_2794_;
goto v_reusejp_2792_;
}
v_reusejp_2792_:
{
return v___x_2793_;
}
}
}
else
{
if (lean_obj_tag(v___x_2785_) == 0)
{
lean_object* v_a_2796_; lean_object* v___x_2798_; uint8_t v_isShared_2799_; uint8_t v_isSharedCheck_2803_; 
lean_dec(v_a_2783_);
lean_dec(v_a_2762_);
lean_dec(v_a_2741_);
lean_dec(v_json_2720_);
v_a_2796_ = lean_ctor_get(v___x_2785_, 0);
v_isSharedCheck_2803_ = !lean_is_exclusive(v___x_2785_);
if (v_isSharedCheck_2803_ == 0)
{
v___x_2798_ = v___x_2785_;
v_isShared_2799_ = v_isSharedCheck_2803_;
goto v_resetjp_2797_;
}
else
{
lean_inc(v_a_2796_);
lean_dec(v___x_2785_);
v___x_2798_ = lean_box(0);
v_isShared_2799_ = v_isSharedCheck_2803_;
goto v_resetjp_2797_;
}
v_resetjp_2797_:
{
lean_object* v___x_2801_; 
if (v_isShared_2799_ == 0)
{
lean_ctor_set_tag(v___x_2798_, 0);
v___x_2801_ = v___x_2798_;
goto v_reusejp_2800_;
}
else
{
lean_object* v_reuseFailAlloc_2802_; 
v_reuseFailAlloc_2802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2802_, 0, v_a_2796_);
v___x_2801_ = v_reuseFailAlloc_2802_;
goto v_reusejp_2800_;
}
v_reusejp_2800_:
{
return v___x_2801_;
}
}
}
else
{
lean_object* v_a_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v_a_2807_; lean_object* v___x_2809_; uint8_t v_isShared_2810_; uint8_t v_isSharedCheck_2817_; 
v_a_2804_ = lean_ctor_get(v___x_2785_, 0);
lean_inc(v_a_2804_);
lean_dec_ref(v___x_2785_);
v___x_2805_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__15));
v___x_2806_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcCallParams_fromJson_spec__1(v_json_2720_, v___x_2805_);
v_a_2807_ = lean_ctor_get(v___x_2806_, 0);
v_isSharedCheck_2817_ = !lean_is_exclusive(v___x_2806_);
if (v_isSharedCheck_2817_ == 0)
{
v___x_2809_ = v___x_2806_;
v_isShared_2810_ = v_isSharedCheck_2817_;
goto v_resetjp_2808_;
}
else
{
lean_inc(v_a_2807_);
lean_dec(v___x_2806_);
v___x_2809_ = lean_box(0);
v_isShared_2810_ = v_isSharedCheck_2817_;
goto v_resetjp_2808_;
}
v_resetjp_2808_:
{
lean_object* v___x_2811_; lean_object* v___x_2812_; uint64_t v___x_2813_; lean_object* v___x_2815_; 
v___x_2811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2811_, 0, v_a_2741_);
lean_ctor_set(v___x_2811_, 1, v_a_2762_);
v___x_2812_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_2812_, 0, v___x_2811_);
lean_ctor_set(v___x_2812_, 1, v_a_2804_);
lean_ctor_set(v___x_2812_, 2, v_a_2807_);
v___x_2813_ = lean_unbox_uint64(v_a_2783_);
lean_dec(v_a_2783_);
lean_ctor_set_uint64(v___x_2812_, sizeof(void*)*3, v___x_2813_);
if (v_isShared_2810_ == 0)
{
lean_ctor_set(v___x_2809_, 0, v___x_2812_);
v___x_2815_ = v___x_2809_;
goto v_reusejp_2814_;
}
else
{
lean_object* v_reuseFailAlloc_2816_; 
v_reuseFailAlloc_2816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2816_, 0, v___x_2812_);
v___x_2815_ = v_reuseFailAlloc_2816_;
goto v_reusejp_2814_;
}
v_reusejp_2814_:
{
return v___x_2815_;
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
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRpcCallParams_toJson(lean_object* v_x_2820_){
_start:
{
lean_object* v_toTextDocumentPositionParams_2821_; uint64_t v_sessionId_2822_; lean_object* v_method_2823_; lean_object* v_params_2824_; lean_object* v_textDocument_2825_; lean_object* v_position_2826_; lean_object* v___x_2828_; uint8_t v_isShared_2829_; uint8_t v_isSharedCheck_2863_; 
v_toTextDocumentPositionParams_2821_ = lean_ctor_get(v_x_2820_, 0);
lean_inc_ref(v_toTextDocumentPositionParams_2821_);
v_sessionId_2822_ = lean_ctor_get_uint64(v_x_2820_, sizeof(void*)*3);
v_method_2823_ = lean_ctor_get(v_x_2820_, 1);
lean_inc(v_method_2823_);
v_params_2824_ = lean_ctor_get(v_x_2820_, 2);
lean_inc(v_params_2824_);
lean_dec_ref(v_x_2820_);
v_textDocument_2825_ = lean_ctor_get(v_toTextDocumentPositionParams_2821_, 0);
v_position_2826_ = lean_ctor_get(v_toTextDocumentPositionParams_2821_, 1);
v_isSharedCheck_2863_ = !lean_is_exclusive(v_toTextDocumentPositionParams_2821_);
if (v_isSharedCheck_2863_ == 0)
{
v___x_2828_ = v_toTextDocumentPositionParams_2821_;
v_isShared_2829_ = v_isSharedCheck_2863_;
goto v_resetjp_2827_;
}
else
{
lean_inc(v_position_2826_);
lean_inc(v_textDocument_2825_);
lean_dec(v_toTextDocumentPositionParams_2821_);
v___x_2828_ = lean_box(0);
v_isShared_2829_ = v_isSharedCheck_2863_;
goto v_resetjp_2827_;
}
v_resetjp_2827_:
{
lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2833_; 
v___x_2830_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__0));
v___x_2831_ = l_Lean_Lsp_instToJsonTextDocumentIdentifier_toJson(v_textDocument_2825_);
if (v_isShared_2829_ == 0)
{
lean_ctor_set(v___x_2828_, 1, v___x_2831_);
lean_ctor_set(v___x_2828_, 0, v___x_2830_);
v___x_2833_ = v___x_2828_;
goto v_reusejp_2832_;
}
else
{
lean_object* v_reuseFailAlloc_2862_; 
v_reuseFailAlloc_2862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2862_, 0, v___x_2830_);
lean_ctor_set(v_reuseFailAlloc_2862_, 1, v___x_2831_);
v___x_2833_ = v_reuseFailAlloc_2862_;
goto v_reusejp_2832_;
}
v_reusejp_2832_:
{
lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; uint8_t v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; 
v___x_2834_ = lean_box(0);
v___x_2835_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2835_, 0, v___x_2833_);
lean_ctor_set(v___x_2835_, 1, v___x_2834_);
v___x_2836_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__6));
v___x_2837_ = l_Lean_Lsp_instToJsonPosition_toJson(v_position_2826_);
v___x_2838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2838_, 0, v___x_2836_);
lean_ctor_set(v___x_2838_, 1, v___x_2837_);
v___x_2839_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2839_, 0, v___x_2838_);
lean_ctor_set(v___x_2839_, 1, v___x_2834_);
v___x_2840_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__0));
v___x_2841_ = lean_uint64_to_nat(v_sessionId_2822_);
v___x_2842_ = l_Lean_bignumToJson(v___x_2841_);
v___x_2843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2843_, 0, v___x_2840_);
lean_ctor_set(v___x_2843_, 1, v___x_2842_);
v___x_2844_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2844_, 0, v___x_2843_);
lean_ctor_set(v___x_2844_, 1, v___x_2834_);
v___x_2845_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__10));
v___x_2846_ = 1;
v___x_2847_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_method_2823_, v___x_2846_);
v___x_2848_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2848_, 0, v___x_2847_);
v___x_2849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2849_, 0, v___x_2845_);
lean_ctor_set(v___x_2849_, 1, v___x_2848_);
v___x_2850_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2850_, 0, v___x_2849_);
lean_ctor_set(v___x_2850_, 1, v___x_2834_);
v___x_2851_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__15));
v___x_2852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2852_, 0, v___x_2851_);
lean_ctor_set(v___x_2852_, 1, v_params_2824_);
v___x_2853_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2853_, 0, v___x_2852_);
lean_ctor_set(v___x_2853_, 1, v___x_2834_);
v___x_2854_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2854_, 0, v___x_2853_);
lean_ctor_set(v___x_2854_, 1, v___x_2834_);
v___x_2855_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2855_, 0, v___x_2850_);
lean_ctor_set(v___x_2855_, 1, v___x_2854_);
v___x_2856_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2856_, 0, v___x_2844_);
lean_ctor_set(v___x_2856_, 1, v___x_2855_);
v___x_2857_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2857_, 0, v___x_2839_);
lean_ctor_set(v___x_2857_, 1, v___x_2856_);
v___x_2858_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2858_, 0, v___x_2835_);
lean_ctor_set(v___x_2858_, 1, v___x_2857_);
v___x_2859_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0));
v___x_2860_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_2858_, v___x_2859_);
v___x_2861_ = l_Lean_Json_mkObj(v___x_2860_);
lean_dec(v___x_2860_);
return v___x_2861_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcReleaseParams_fromJson_spec__0_spec__0_spec__1(size_t v_sz_2866_, size_t v_i_2867_, lean_object* v_bs_2868_){
_start:
{
uint8_t v___x_2869_; 
v___x_2869_ = lean_usize_dec_lt(v_i_2867_, v_sz_2866_);
if (v___x_2869_ == 0)
{
lean_object* v___x_2870_; 
v___x_2870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2870_, 0, v_bs_2868_);
return v___x_2870_;
}
else
{
lean_object* v_v_2871_; lean_object* v___x_2872_; lean_object* v_bs_x27_2873_; size_t v___x_2874_; size_t v___x_2875_; lean_object* v___x_2876_; 
v_v_2871_ = lean_array_uget(v_bs_2868_, v_i_2867_);
v___x_2872_ = lean_unsigned_to_nat(0u);
v_bs_x27_2873_ = lean_array_uset(v_bs_2868_, v_i_2867_, v___x_2872_);
v___x_2874_ = ((size_t)1ULL);
v___x_2875_ = lean_usize_add(v_i_2867_, v___x_2874_);
v___x_2876_ = lean_array_uset(v_bs_x27_2873_, v_i_2867_, v_v_2871_);
v_i_2867_ = v___x_2875_;
v_bs_2868_ = v___x_2876_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcReleaseParams_fromJson_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_2878_, lean_object* v_i_2879_, lean_object* v_bs_2880_){
_start:
{
size_t v_sz_boxed_2881_; size_t v_i_boxed_2882_; lean_object* v_res_2883_; 
v_sz_boxed_2881_ = lean_unbox_usize(v_sz_2878_);
lean_dec(v_sz_2878_);
v_i_boxed_2882_ = lean_unbox_usize(v_i_2879_);
lean_dec(v_i_2879_);
v_res_2883_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcReleaseParams_fromJson_spec__0_spec__0_spec__1(v_sz_boxed_2881_, v_i_boxed_2882_, v_bs_2880_);
return v_res_2883_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcReleaseParams_fromJson_spec__0_spec__0(lean_object* v_x_2884_){
_start:
{
if (lean_obj_tag(v_x_2884_) == 4)
{
lean_object* v_elems_2885_; size_t v_sz_2886_; size_t v___x_2887_; lean_object* v___x_2888_; 
v_elems_2885_ = lean_ctor_get(v_x_2884_, 0);
lean_inc_ref(v_elems_2885_);
lean_dec_ref(v_x_2884_);
v_sz_2886_ = lean_array_size(v_elems_2885_);
v___x_2887_ = ((size_t)0ULL);
v___x_2888_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcReleaseParams_fromJson_spec__0_spec__0_spec__1(v_sz_2886_, v___x_2887_, v_elems_2885_);
return v___x_2888_;
}
else
{
lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; 
v___x_2889_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__1_spec__1___closed__0));
v___x_2890_ = lean_unsigned_to_nat(80u);
v___x_2891_ = l_Lean_Json_pretty(v_x_2884_, v___x_2890_);
v___x_2892_ = lean_string_append(v___x_2889_, v___x_2891_);
lean_dec_ref(v___x_2891_);
v___x_2893_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressKind___lam__0___closed__1));
v___x_2894_ = lean_string_append(v___x_2892_, v___x_2893_);
v___x_2895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2895_, 0, v___x_2894_);
return v___x_2895_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcReleaseParams_fromJson_spec__0(lean_object* v_j_2896_, lean_object* v_k_2897_){
_start:
{
lean_object* v___x_2898_; lean_object* v___x_2899_; 
v___x_2898_ = l_Lean_Json_getObjValD(v_j_2896_, v_k_2897_);
v___x_2899_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcReleaseParams_fromJson_spec__0_spec__0(v___x_2898_);
return v___x_2899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcReleaseParams_fromJson_spec__0___boxed(lean_object* v_j_2900_, lean_object* v_k_2901_){
_start:
{
lean_object* v_res_2902_; 
v_res_2902_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcReleaseParams_fromJson_spec__0(v_j_2900_, v_k_2901_);
lean_dec_ref(v_k_2901_);
return v_res_2902_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__2(void){
_start:
{
uint8_t v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; 
v___x_2908_ = 1;
v___x_2909_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__1));
v___x_2910_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2909_, v___x_2908_);
return v___x_2910_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__3(void){
_start:
{
lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; 
v___x_2911_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6));
v___x_2912_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__2, &l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__2);
v___x_2913_ = lean_string_append(v___x_2912_, v___x_2911_);
return v___x_2913_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; 
v___x_2914_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__6, &l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__6);
v___x_2915_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__3);
v___x_2916_ = lean_string_append(v___x_2915_, v___x_2914_);
return v___x_2916_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__5(void){
_start:
{
lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; 
v___x_2917_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_2918_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__4);
v___x_2919_ = lean_string_append(v___x_2918_, v___x_2917_);
return v___x_2919_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__6(void){
_start:
{
lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; 
v___x_2920_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__6, &l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__6);
v___x_2921_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__3);
v___x_2922_ = lean_string_append(v___x_2921_, v___x_2920_);
return v___x_2922_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__7(void){
_start:
{
lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; 
v___x_2923_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_2924_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__6, &l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__6);
v___x_2925_ = lean_string_append(v___x_2924_, v___x_2923_);
return v___x_2925_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__10(void){
_start:
{
uint8_t v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; 
v___x_2929_ = 1;
v___x_2930_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__9));
v___x_2931_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2930_, v___x_2929_);
return v___x_2931_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__11(void){
_start:
{
lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; 
v___x_2932_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__10, &l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__10);
v___x_2933_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__3);
v___x_2934_ = lean_string_append(v___x_2933_, v___x_2932_);
return v___x_2934_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__12(void){
_start:
{
lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; 
v___x_2935_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_2936_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__11, &l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__11);
v___x_2937_ = lean_string_append(v___x_2936_, v___x_2935_);
return v___x_2937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson(lean_object* v_json_2938_){
_start:
{
lean_object* v___x_2939_; lean_object* v___x_2940_; 
v___x_2939_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__0));
lean_inc(v_json_2938_);
v___x_2940_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson_spec__0(v_json_2938_, v___x_2939_);
if (lean_obj_tag(v___x_2940_) == 0)
{
lean_object* v_a_2941_; lean_object* v___x_2943_; uint8_t v_isShared_2944_; uint8_t v_isSharedCheck_2950_; 
lean_dec(v_json_2938_);
v_a_2941_ = lean_ctor_get(v___x_2940_, 0);
v_isSharedCheck_2950_ = !lean_is_exclusive(v___x_2940_);
if (v_isSharedCheck_2950_ == 0)
{
v___x_2943_ = v___x_2940_;
v_isShared_2944_ = v_isSharedCheck_2950_;
goto v_resetjp_2942_;
}
else
{
lean_inc(v_a_2941_);
lean_dec(v___x_2940_);
v___x_2943_ = lean_box(0);
v_isShared_2944_ = v_isSharedCheck_2950_;
goto v_resetjp_2942_;
}
v_resetjp_2942_:
{
lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2948_; 
v___x_2945_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__5, &l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__5);
v___x_2946_ = lean_string_append(v___x_2945_, v_a_2941_);
lean_dec(v_a_2941_);
if (v_isShared_2944_ == 0)
{
lean_ctor_set(v___x_2943_, 0, v___x_2946_);
v___x_2948_ = v___x_2943_;
goto v_reusejp_2947_;
}
else
{
lean_object* v_reuseFailAlloc_2949_; 
v_reuseFailAlloc_2949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2949_, 0, v___x_2946_);
v___x_2948_ = v_reuseFailAlloc_2949_;
goto v_reusejp_2947_;
}
v_reusejp_2947_:
{
return v___x_2948_;
}
}
}
else
{
if (lean_obj_tag(v___x_2940_) == 0)
{
lean_object* v_a_2951_; lean_object* v___x_2953_; uint8_t v_isShared_2954_; uint8_t v_isSharedCheck_2958_; 
lean_dec(v_json_2938_);
v_a_2951_ = lean_ctor_get(v___x_2940_, 0);
v_isSharedCheck_2958_ = !lean_is_exclusive(v___x_2940_);
if (v_isSharedCheck_2958_ == 0)
{
v___x_2953_ = v___x_2940_;
v_isShared_2954_ = v_isSharedCheck_2958_;
goto v_resetjp_2952_;
}
else
{
lean_inc(v_a_2951_);
lean_dec(v___x_2940_);
v___x_2953_ = lean_box(0);
v_isShared_2954_ = v_isSharedCheck_2958_;
goto v_resetjp_2952_;
}
v_resetjp_2952_:
{
lean_object* v___x_2956_; 
if (v_isShared_2954_ == 0)
{
lean_ctor_set_tag(v___x_2953_, 0);
v___x_2956_ = v___x_2953_;
goto v_reusejp_2955_;
}
else
{
lean_object* v_reuseFailAlloc_2957_; 
v_reuseFailAlloc_2957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2957_, 0, v_a_2951_);
v___x_2956_ = v_reuseFailAlloc_2957_;
goto v_reusejp_2955_;
}
v_reusejp_2955_:
{
return v___x_2956_;
}
}
}
else
{
lean_object* v_a_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; 
v_a_2959_ = lean_ctor_get(v___x_2940_, 0);
lean_inc(v_a_2959_);
lean_dec_ref(v___x_2940_);
v___x_2960_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__0));
lean_inc(v_json_2938_);
v___x_2961_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcConnected_fromJson_spec__0(v_json_2938_, v___x_2960_);
if (lean_obj_tag(v___x_2961_) == 0)
{
lean_object* v_a_2962_; lean_object* v___x_2964_; uint8_t v_isShared_2965_; uint8_t v_isSharedCheck_2971_; 
lean_dec(v_a_2959_);
lean_dec(v_json_2938_);
v_a_2962_ = lean_ctor_get(v___x_2961_, 0);
v_isSharedCheck_2971_ = !lean_is_exclusive(v___x_2961_);
if (v_isSharedCheck_2971_ == 0)
{
v___x_2964_ = v___x_2961_;
v_isShared_2965_ = v_isSharedCheck_2971_;
goto v_resetjp_2963_;
}
else
{
lean_inc(v_a_2962_);
lean_dec(v___x_2961_);
v___x_2964_ = lean_box(0);
v_isShared_2965_ = v_isSharedCheck_2971_;
goto v_resetjp_2963_;
}
v_resetjp_2963_:
{
lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2969_; 
v___x_2966_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__7);
v___x_2967_ = lean_string_append(v___x_2966_, v_a_2962_);
lean_dec(v_a_2962_);
if (v_isShared_2965_ == 0)
{
lean_ctor_set(v___x_2964_, 0, v___x_2967_);
v___x_2969_ = v___x_2964_;
goto v_reusejp_2968_;
}
else
{
lean_object* v_reuseFailAlloc_2970_; 
v_reuseFailAlloc_2970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2970_, 0, v___x_2967_);
v___x_2969_ = v_reuseFailAlloc_2970_;
goto v_reusejp_2968_;
}
v_reusejp_2968_:
{
return v___x_2969_;
}
}
}
else
{
if (lean_obj_tag(v___x_2961_) == 0)
{
lean_object* v_a_2972_; lean_object* v___x_2974_; uint8_t v_isShared_2975_; uint8_t v_isSharedCheck_2979_; 
lean_dec(v_a_2959_);
lean_dec(v_json_2938_);
v_a_2972_ = lean_ctor_get(v___x_2961_, 0);
v_isSharedCheck_2979_ = !lean_is_exclusive(v___x_2961_);
if (v_isSharedCheck_2979_ == 0)
{
v___x_2974_ = v___x_2961_;
v_isShared_2975_ = v_isSharedCheck_2979_;
goto v_resetjp_2973_;
}
else
{
lean_inc(v_a_2972_);
lean_dec(v___x_2961_);
v___x_2974_ = lean_box(0);
v_isShared_2975_ = v_isSharedCheck_2979_;
goto v_resetjp_2973_;
}
v_resetjp_2973_:
{
lean_object* v___x_2977_; 
if (v_isShared_2975_ == 0)
{
lean_ctor_set_tag(v___x_2974_, 0);
v___x_2977_ = v___x_2974_;
goto v_reusejp_2976_;
}
else
{
lean_object* v_reuseFailAlloc_2978_; 
v_reuseFailAlloc_2978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2978_, 0, v_a_2972_);
v___x_2977_ = v_reuseFailAlloc_2978_;
goto v_reusejp_2976_;
}
v_reusejp_2976_:
{
return v___x_2977_;
}
}
}
else
{
lean_object* v_a_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; 
v_a_2980_ = lean_ctor_get(v___x_2961_, 0);
lean_inc(v_a_2980_);
lean_dec_ref(v___x_2961_);
v___x_2981_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__8));
v___x_2982_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcReleaseParams_fromJson_spec__0(v_json_2938_, v___x_2981_);
if (lean_obj_tag(v___x_2982_) == 0)
{
lean_object* v_a_2983_; lean_object* v___x_2985_; uint8_t v_isShared_2986_; uint8_t v_isSharedCheck_2992_; 
lean_dec(v_a_2980_);
lean_dec(v_a_2959_);
v_a_2983_ = lean_ctor_get(v___x_2982_, 0);
v_isSharedCheck_2992_ = !lean_is_exclusive(v___x_2982_);
if (v_isSharedCheck_2992_ == 0)
{
v___x_2985_ = v___x_2982_;
v_isShared_2986_ = v_isSharedCheck_2992_;
goto v_resetjp_2984_;
}
else
{
lean_inc(v_a_2983_);
lean_dec(v___x_2982_);
v___x_2985_ = lean_box(0);
v_isShared_2986_ = v_isSharedCheck_2992_;
goto v_resetjp_2984_;
}
v_resetjp_2984_:
{
lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2990_; 
v___x_2987_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__12, &l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__12);
v___x_2988_ = lean_string_append(v___x_2987_, v_a_2983_);
lean_dec(v_a_2983_);
if (v_isShared_2986_ == 0)
{
lean_ctor_set(v___x_2985_, 0, v___x_2988_);
v___x_2990_ = v___x_2985_;
goto v_reusejp_2989_;
}
else
{
lean_object* v_reuseFailAlloc_2991_; 
v_reuseFailAlloc_2991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2991_, 0, v___x_2988_);
v___x_2990_ = v_reuseFailAlloc_2991_;
goto v_reusejp_2989_;
}
v_reusejp_2989_:
{
return v___x_2990_;
}
}
}
else
{
if (lean_obj_tag(v___x_2982_) == 0)
{
lean_object* v_a_2993_; lean_object* v___x_2995_; uint8_t v_isShared_2996_; uint8_t v_isSharedCheck_3000_; 
lean_dec(v_a_2980_);
lean_dec(v_a_2959_);
v_a_2993_ = lean_ctor_get(v___x_2982_, 0);
v_isSharedCheck_3000_ = !lean_is_exclusive(v___x_2982_);
if (v_isSharedCheck_3000_ == 0)
{
v___x_2995_ = v___x_2982_;
v_isShared_2996_ = v_isSharedCheck_3000_;
goto v_resetjp_2994_;
}
else
{
lean_inc(v_a_2993_);
lean_dec(v___x_2982_);
v___x_2995_ = lean_box(0);
v_isShared_2996_ = v_isSharedCheck_3000_;
goto v_resetjp_2994_;
}
v_resetjp_2994_:
{
lean_object* v___x_2998_; 
if (v_isShared_2996_ == 0)
{
lean_ctor_set_tag(v___x_2995_, 0);
v___x_2998_ = v___x_2995_;
goto v_reusejp_2997_;
}
else
{
lean_object* v_reuseFailAlloc_2999_; 
v_reuseFailAlloc_2999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2999_, 0, v_a_2993_);
v___x_2998_ = v_reuseFailAlloc_2999_;
goto v_reusejp_2997_;
}
v_reusejp_2997_:
{
return v___x_2998_;
}
}
}
else
{
lean_object* v_a_3001_; lean_object* v___x_3003_; uint8_t v_isShared_3004_; uint8_t v_isSharedCheck_3010_; 
v_a_3001_ = lean_ctor_get(v___x_2982_, 0);
v_isSharedCheck_3010_ = !lean_is_exclusive(v___x_2982_);
if (v_isSharedCheck_3010_ == 0)
{
v___x_3003_ = v___x_2982_;
v_isShared_3004_ = v_isSharedCheck_3010_;
goto v_resetjp_3002_;
}
else
{
lean_inc(v_a_3001_);
lean_dec(v___x_2982_);
v___x_3003_ = lean_box(0);
v_isShared_3004_ = v_isSharedCheck_3010_;
goto v_resetjp_3002_;
}
v_resetjp_3002_:
{
lean_object* v___x_3005_; uint64_t v___x_3006_; lean_object* v___x_3008_; 
v___x_3005_ = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(v___x_3005_, 0, v_a_2959_);
lean_ctor_set(v___x_3005_, 1, v_a_3001_);
v___x_3006_ = lean_unbox_uint64(v_a_2980_);
lean_dec(v_a_2980_);
lean_ctor_set_uint64(v___x_3005_, sizeof(void*)*2, v___x_3006_);
if (v_isShared_3004_ == 0)
{
lean_ctor_set(v___x_3003_, 0, v___x_3005_);
v___x_3008_ = v___x_3003_;
goto v_reusejp_3007_;
}
else
{
lean_object* v_reuseFailAlloc_3009_; 
v_reuseFailAlloc_3009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3009_, 0, v___x_3005_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonRpcReleaseParams_toJson_spec__0_spec__0(size_t v_sz_3013_, size_t v_i_3014_, lean_object* v_bs_3015_){
_start:
{
uint8_t v___x_3016_; 
v___x_3016_ = lean_usize_dec_lt(v_i_3014_, v_sz_3013_);
if (v___x_3016_ == 0)
{
return v_bs_3015_;
}
else
{
lean_object* v_v_3017_; lean_object* v___x_3018_; lean_object* v_bs_x27_3019_; size_t v___x_3020_; size_t v___x_3021_; lean_object* v___x_3022_; 
v_v_3017_ = lean_array_uget(v_bs_3015_, v_i_3014_);
v___x_3018_ = lean_unsigned_to_nat(0u);
v_bs_x27_3019_ = lean_array_uset(v_bs_3015_, v_i_3014_, v___x_3018_);
v___x_3020_ = ((size_t)1ULL);
v___x_3021_ = lean_usize_add(v_i_3014_, v___x_3020_);
v___x_3022_ = lean_array_uset(v_bs_x27_3019_, v_i_3014_, v_v_3017_);
v_i_3014_ = v___x_3021_;
v_bs_3015_ = v___x_3022_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonRpcReleaseParams_toJson_spec__0_spec__0___boxed(lean_object* v_sz_3024_, lean_object* v_i_3025_, lean_object* v_bs_3026_){
_start:
{
size_t v_sz_boxed_3027_; size_t v_i_boxed_3028_; lean_object* v_res_3029_; 
v_sz_boxed_3027_ = lean_unbox_usize(v_sz_3024_);
lean_dec(v_sz_3024_);
v_i_boxed_3028_ = lean_unbox_usize(v_i_3025_);
lean_dec(v_i_3025_);
v_res_3029_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonRpcReleaseParams_toJson_spec__0_spec__0(v_sz_boxed_3027_, v_i_boxed_3028_, v_bs_3026_);
return v_res_3029_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Lsp_instToJsonRpcReleaseParams_toJson_spec__0(lean_object* v_a_3030_){
_start:
{
size_t v_sz_3031_; size_t v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; 
v_sz_3031_ = lean_array_size(v_a_3030_);
v___x_3032_ = ((size_t)0ULL);
v___x_3033_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonRpcReleaseParams_toJson_spec__0_spec__0(v_sz_3031_, v___x_3032_, v_a_3030_);
v___x_3034_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3034_, 0, v___x_3033_);
return v___x_3034_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRpcReleaseParams_toJson(lean_object* v_x_3035_){
_start:
{
lean_object* v_uri_3036_; uint64_t v_sessionId_3037_; lean_object* v_refs_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; 
v_uri_3036_ = lean_ctor_get(v_x_3035_, 0);
lean_inc_ref(v_uri_3036_);
v_sessionId_3037_ = lean_ctor_get_uint64(v_x_3035_, sizeof(void*)*2);
v_refs_3038_ = lean_ctor_get(v_x_3035_, 1);
lean_inc_ref(v_refs_3038_);
lean_dec_ref(v_x_3035_);
v___x_3039_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__0));
v___x_3040_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3040_, 0, v_uri_3036_);
v___x_3041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3041_, 0, v___x_3039_);
lean_ctor_set(v___x_3041_, 1, v___x_3040_);
v___x_3042_ = lean_box(0);
v___x_3043_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3043_, 0, v___x_3041_);
lean_ctor_set(v___x_3043_, 1, v___x_3042_);
v___x_3044_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__0));
v___x_3045_ = lean_uint64_to_nat(v_sessionId_3037_);
v___x_3046_ = l_Lean_bignumToJson(v___x_3045_);
v___x_3047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3047_, 0, v___x_3044_);
lean_ctor_set(v___x_3047_, 1, v___x_3046_);
v___x_3048_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3048_, 0, v___x_3047_);
lean_ctor_set(v___x_3048_, 1, v___x_3042_);
v___x_3049_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__8));
v___x_3050_ = l_Array_toJson___at___00Lean_Lsp_instToJsonRpcReleaseParams_toJson_spec__0(v_refs_3038_);
v___x_3051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3051_, 0, v___x_3049_);
lean_ctor_set(v___x_3051_, 1, v___x_3050_);
v___x_3052_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3052_, 0, v___x_3051_);
lean_ctor_set(v___x_3052_, 1, v___x_3042_);
v___x_3053_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3053_, 0, v___x_3052_);
lean_ctor_set(v___x_3053_, 1, v___x_3042_);
v___x_3054_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3054_, 0, v___x_3048_);
lean_ctor_set(v___x_3054_, 1, v___x_3053_);
v___x_3055_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3055_, 0, v___x_3043_);
lean_ctor_set(v___x_3055_, 1, v___x_3054_);
v___x_3056_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0));
v___x_3057_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_3055_, v___x_3056_);
v___x_3058_ = l_Lean_Json_mkObj(v___x_3057_);
lean_dec(v___x_3057_);
return v___x_3058_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__2(void){
_start:
{
uint8_t v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; 
v___x_3066_ = 1;
v___x_3067_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__1));
v___x_3068_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3067_, v___x_3066_);
return v___x_3068_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__3(void){
_start:
{
lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; 
v___x_3069_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6));
v___x_3070_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__2, &l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__2);
v___x_3071_ = lean_string_append(v___x_3070_, v___x_3069_);
return v___x_3071_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; 
v___x_3072_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__6, &l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__6);
v___x_3073_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__3);
v___x_3074_ = lean_string_append(v___x_3073_, v___x_3072_);
return v___x_3074_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__5(void){
_start:
{
lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; 
v___x_3075_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_3076_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__4);
v___x_3077_ = lean_string_append(v___x_3076_, v___x_3075_);
return v___x_3077_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__6(void){
_start:
{
lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; 
v___x_3078_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__6, &l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__6);
v___x_3079_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__3);
v___x_3080_ = lean_string_append(v___x_3079_, v___x_3078_);
return v___x_3080_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__7(void){
_start:
{
lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; 
v___x_3081_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_3082_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__6, &l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__6);
v___x_3083_ = lean_string_append(v___x_3082_, v___x_3081_);
return v___x_3083_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson(lean_object* v_json_3084_){
_start:
{
lean_object* v___x_3085_; lean_object* v___x_3086_; 
v___x_3085_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__0));
lean_inc(v_json_3084_);
v___x_3086_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson_spec__0(v_json_3084_, v___x_3085_);
if (lean_obj_tag(v___x_3086_) == 0)
{
lean_object* v_a_3087_; lean_object* v___x_3089_; uint8_t v_isShared_3090_; uint8_t v_isSharedCheck_3096_; 
lean_dec(v_json_3084_);
v_a_3087_ = lean_ctor_get(v___x_3086_, 0);
v_isSharedCheck_3096_ = !lean_is_exclusive(v___x_3086_);
if (v_isSharedCheck_3096_ == 0)
{
v___x_3089_ = v___x_3086_;
v_isShared_3090_ = v_isSharedCheck_3096_;
goto v_resetjp_3088_;
}
else
{
lean_inc(v_a_3087_);
lean_dec(v___x_3086_);
v___x_3089_ = lean_box(0);
v_isShared_3090_ = v_isSharedCheck_3096_;
goto v_resetjp_3088_;
}
v_resetjp_3088_:
{
lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3094_; 
v___x_3091_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__5, &l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__5);
v___x_3092_ = lean_string_append(v___x_3091_, v_a_3087_);
lean_dec(v_a_3087_);
if (v_isShared_3090_ == 0)
{
lean_ctor_set(v___x_3089_, 0, v___x_3092_);
v___x_3094_ = v___x_3089_;
goto v_reusejp_3093_;
}
else
{
lean_object* v_reuseFailAlloc_3095_; 
v_reuseFailAlloc_3095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3095_, 0, v___x_3092_);
v___x_3094_ = v_reuseFailAlloc_3095_;
goto v_reusejp_3093_;
}
v_reusejp_3093_:
{
return v___x_3094_;
}
}
}
else
{
if (lean_obj_tag(v___x_3086_) == 0)
{
lean_object* v_a_3097_; lean_object* v___x_3099_; uint8_t v_isShared_3100_; uint8_t v_isSharedCheck_3104_; 
lean_dec(v_json_3084_);
v_a_3097_ = lean_ctor_get(v___x_3086_, 0);
v_isSharedCheck_3104_ = !lean_is_exclusive(v___x_3086_);
if (v_isSharedCheck_3104_ == 0)
{
v___x_3099_ = v___x_3086_;
v_isShared_3100_ = v_isSharedCheck_3104_;
goto v_resetjp_3098_;
}
else
{
lean_inc(v_a_3097_);
lean_dec(v___x_3086_);
v___x_3099_ = lean_box(0);
v_isShared_3100_ = v_isSharedCheck_3104_;
goto v_resetjp_3098_;
}
v_resetjp_3098_:
{
lean_object* v___x_3102_; 
if (v_isShared_3100_ == 0)
{
lean_ctor_set_tag(v___x_3099_, 0);
v___x_3102_ = v___x_3099_;
goto v_reusejp_3101_;
}
else
{
lean_object* v_reuseFailAlloc_3103_; 
v_reuseFailAlloc_3103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3103_, 0, v_a_3097_);
v___x_3102_ = v_reuseFailAlloc_3103_;
goto v_reusejp_3101_;
}
v_reusejp_3101_:
{
return v___x_3102_;
}
}
}
else
{
lean_object* v_a_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; 
v_a_3105_ = lean_ctor_get(v___x_3086_, 0);
lean_inc(v_a_3105_);
lean_dec_ref(v___x_3086_);
v___x_3106_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__0));
v___x_3107_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcConnected_fromJson_spec__0(v_json_3084_, v___x_3106_);
if (lean_obj_tag(v___x_3107_) == 0)
{
lean_object* v_a_3108_; lean_object* v___x_3110_; uint8_t v_isShared_3111_; uint8_t v_isSharedCheck_3117_; 
lean_dec(v_a_3105_);
v_a_3108_ = lean_ctor_get(v___x_3107_, 0);
v_isSharedCheck_3117_ = !lean_is_exclusive(v___x_3107_);
if (v_isSharedCheck_3117_ == 0)
{
v___x_3110_ = v___x_3107_;
v_isShared_3111_ = v_isSharedCheck_3117_;
goto v_resetjp_3109_;
}
else
{
lean_inc(v_a_3108_);
lean_dec(v___x_3107_);
v___x_3110_ = lean_box(0);
v_isShared_3111_ = v_isSharedCheck_3117_;
goto v_resetjp_3109_;
}
v_resetjp_3109_:
{
lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3115_; 
v___x_3112_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__7);
v___x_3113_ = lean_string_append(v___x_3112_, v_a_3108_);
lean_dec(v_a_3108_);
if (v_isShared_3111_ == 0)
{
lean_ctor_set(v___x_3110_, 0, v___x_3113_);
v___x_3115_ = v___x_3110_;
goto v_reusejp_3114_;
}
else
{
lean_object* v_reuseFailAlloc_3116_; 
v_reuseFailAlloc_3116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3116_, 0, v___x_3113_);
v___x_3115_ = v_reuseFailAlloc_3116_;
goto v_reusejp_3114_;
}
v_reusejp_3114_:
{
return v___x_3115_;
}
}
}
else
{
if (lean_obj_tag(v___x_3107_) == 0)
{
lean_object* v_a_3118_; lean_object* v___x_3120_; uint8_t v_isShared_3121_; uint8_t v_isSharedCheck_3125_; 
lean_dec(v_a_3105_);
v_a_3118_ = lean_ctor_get(v___x_3107_, 0);
v_isSharedCheck_3125_ = !lean_is_exclusive(v___x_3107_);
if (v_isSharedCheck_3125_ == 0)
{
v___x_3120_ = v___x_3107_;
v_isShared_3121_ = v_isSharedCheck_3125_;
goto v_resetjp_3119_;
}
else
{
lean_inc(v_a_3118_);
lean_dec(v___x_3107_);
v___x_3120_ = lean_box(0);
v_isShared_3121_ = v_isSharedCheck_3125_;
goto v_resetjp_3119_;
}
v_resetjp_3119_:
{
lean_object* v___x_3123_; 
if (v_isShared_3121_ == 0)
{
lean_ctor_set_tag(v___x_3120_, 0);
v___x_3123_ = v___x_3120_;
goto v_reusejp_3122_;
}
else
{
lean_object* v_reuseFailAlloc_3124_; 
v_reuseFailAlloc_3124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3124_, 0, v_a_3118_);
v___x_3123_ = v_reuseFailAlloc_3124_;
goto v_reusejp_3122_;
}
v_reusejp_3122_:
{
return v___x_3123_;
}
}
}
else
{
lean_object* v_a_3126_; lean_object* v___x_3128_; uint8_t v_isShared_3129_; uint8_t v_isSharedCheck_3135_; 
v_a_3126_ = lean_ctor_get(v___x_3107_, 0);
v_isSharedCheck_3135_ = !lean_is_exclusive(v___x_3107_);
if (v_isSharedCheck_3135_ == 0)
{
v___x_3128_ = v___x_3107_;
v_isShared_3129_ = v_isSharedCheck_3135_;
goto v_resetjp_3127_;
}
else
{
lean_inc(v_a_3126_);
lean_dec(v___x_3107_);
v___x_3128_ = lean_box(0);
v_isShared_3129_ = v_isSharedCheck_3135_;
goto v_resetjp_3127_;
}
v_resetjp_3127_:
{
lean_object* v___x_3130_; uint64_t v___x_3131_; lean_object* v___x_3133_; 
v___x_3130_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3130_, 0, v_a_3105_);
v___x_3131_ = lean_unbox_uint64(v_a_3126_);
lean_dec(v_a_3126_);
lean_ctor_set_uint64(v___x_3130_, sizeof(void*)*1, v___x_3131_);
if (v_isShared_3129_ == 0)
{
lean_ctor_set(v___x_3128_, 0, v___x_3130_);
v___x_3133_ = v___x_3128_;
goto v_reusejp_3132_;
}
else
{
lean_object* v_reuseFailAlloc_3134_; 
v_reuseFailAlloc_3134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3134_, 0, v___x_3130_);
v___x_3133_ = v_reuseFailAlloc_3134_;
goto v_reusejp_3132_;
}
v_reusejp_3132_:
{
return v___x_3133_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRpcKeepAliveParams_toJson(lean_object* v_x_3138_){
_start:
{
lean_object* v_uri_3139_; uint64_t v_sessionId_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; 
v_uri_3139_ = lean_ctor_get(v_x_3138_, 0);
v_sessionId_3140_ = lean_ctor_get_uint64(v_x_3138_, sizeof(void*)*1);
v___x_3141_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__0));
lean_inc_ref(v_uri_3139_);
v___x_3142_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3142_, 0, v_uri_3139_);
v___x_3143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3143_, 0, v___x_3141_);
lean_ctor_set(v___x_3143_, 1, v___x_3142_);
v___x_3144_ = lean_box(0);
v___x_3145_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3145_, 0, v___x_3143_);
lean_ctor_set(v___x_3145_, 1, v___x_3144_);
v___x_3146_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__0));
v___x_3147_ = lean_uint64_to_nat(v_sessionId_3140_);
v___x_3148_ = l_Lean_bignumToJson(v___x_3147_);
v___x_3149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3149_, 0, v___x_3146_);
lean_ctor_set(v___x_3149_, 1, v___x_3148_);
v___x_3150_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3150_, 0, v___x_3149_);
lean_ctor_set(v___x_3150_, 1, v___x_3144_);
v___x_3151_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3151_, 0, v___x_3150_);
lean_ctor_set(v___x_3151_, 1, v___x_3144_);
v___x_3152_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3152_, 0, v___x_3145_);
lean_ctor_set(v___x_3152_, 1, v___x_3151_);
v___x_3153_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0));
v___x_3154_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_3152_, v___x_3153_);
v___x_3155_ = l_Lean_Json_mkObj(v___x_3154_);
lean_dec(v___x_3154_);
return v___x_3155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRpcKeepAliveParams_toJson___boxed(lean_object* v_x_3156_){
_start:
{
lean_object* v_res_3157_; 
v_res_3157_ = l_Lean_Lsp_instToJsonRpcKeepAliveParams_toJson(v_x_3156_);
lean_dec_ref(v_x_3156_);
return v_res_3157_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Lsp_instReprLineRange_repr_spec__0(lean_object* v_a_3164_){
_start:
{
lean_object* v___x_3165_; 
v___x_3165_ = lean_nat_to_int(v_a_3164_);
return v___x_3165_;
}
}
static lean_object* _init_l_Lean_Lsp_instReprLineRange_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_3179_; lean_object* v___x_3180_; 
v___x_3179_ = lean_unsigned_to_nat(9u);
v___x_3180_ = lean_nat_to_int(v___x_3179_);
return v___x_3180_;
}
}
static lean_object* _init_l_Lean_Lsp_instReprLineRange_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_3187_; lean_object* v___x_3188_; 
v___x_3187_ = lean_unsigned_to_nat(7u);
v___x_3188_ = lean_nat_to_int(v___x_3187_);
return v___x_3188_;
}
}
static lean_object* _init_l_Lean_Lsp_instReprLineRange_repr___redArg___closed__14(void){
_start:
{
lean_object* v___x_3190_; lean_object* v___x_3191_; 
v___x_3190_ = ((lean_object*)(l_Lean_Lsp_instReprLineRange_repr___redArg___closed__0));
v___x_3191_ = lean_string_length(v___x_3190_);
return v___x_3191_;
}
}
static lean_object* _init_l_Lean_Lsp_instReprLineRange_repr___redArg___closed__15(void){
_start:
{
lean_object* v___x_3192_; lean_object* v___x_3193_; 
v___x_3192_ = lean_obj_once(&l_Lean_Lsp_instReprLineRange_repr___redArg___closed__14, &l_Lean_Lsp_instReprLineRange_repr___redArg___closed__14_once, _init_l_Lean_Lsp_instReprLineRange_repr___redArg___closed__14);
v___x_3193_ = lean_nat_to_int(v___x_3192_);
return v___x_3193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instReprLineRange_repr___redArg(lean_object* v_x_3198_){
_start:
{
lean_object* v_start_3199_; lean_object* v_end_3200_; lean_object* v___x_3202_; uint8_t v_isShared_3203_; uint8_t v_isSharedCheck_3235_; 
v_start_3199_ = lean_ctor_get(v_x_3198_, 0);
v_end_3200_ = lean_ctor_get(v_x_3198_, 1);
v_isSharedCheck_3235_ = !lean_is_exclusive(v_x_3198_);
if (v_isSharedCheck_3235_ == 0)
{
v___x_3202_ = v_x_3198_;
v_isShared_3203_ = v_isSharedCheck_3235_;
goto v_resetjp_3201_;
}
else
{
lean_inc(v_end_3200_);
lean_inc(v_start_3199_);
lean_dec(v_x_3198_);
v___x_3202_ = lean_box(0);
v_isShared_3203_ = v_isSharedCheck_3235_;
goto v_resetjp_3201_;
}
v_resetjp_3201_:
{
lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3210_; 
v___x_3204_ = ((lean_object*)(l_Lean_Lsp_instReprLineRange_repr___redArg___closed__5));
v___x_3205_ = ((lean_object*)(l_Lean_Lsp_instReprLineRange_repr___redArg___closed__6));
v___x_3206_ = lean_obj_once(&l_Lean_Lsp_instReprLineRange_repr___redArg___closed__7, &l_Lean_Lsp_instReprLineRange_repr___redArg___closed__7_once, _init_l_Lean_Lsp_instReprLineRange_repr___redArg___closed__7);
v___x_3207_ = l_Nat_reprFast(v_start_3199_);
v___x_3208_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3208_, 0, v___x_3207_);
if (v_isShared_3203_ == 0)
{
lean_ctor_set_tag(v___x_3202_, 4);
lean_ctor_set(v___x_3202_, 1, v___x_3208_);
lean_ctor_set(v___x_3202_, 0, v___x_3206_);
v___x_3210_ = v___x_3202_;
goto v_reusejp_3209_;
}
else
{
lean_object* v_reuseFailAlloc_3234_; 
v_reuseFailAlloc_3234_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3234_, 0, v___x_3206_);
lean_ctor_set(v_reuseFailAlloc_3234_, 1, v___x_3208_);
v___x_3210_ = v_reuseFailAlloc_3234_;
goto v_reusejp_3209_;
}
v_reusejp_3209_:
{
uint8_t v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; 
v___x_3211_ = 0;
v___x_3212_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3212_, 0, v___x_3210_);
lean_ctor_set_uint8(v___x_3212_, sizeof(void*)*1, v___x_3211_);
v___x_3213_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3213_, 0, v___x_3205_);
lean_ctor_set(v___x_3213_, 1, v___x_3212_);
v___x_3214_ = ((lean_object*)(l_Lean_Lsp_instReprLineRange_repr___redArg___closed__9));
v___x_3215_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3215_, 0, v___x_3213_);
lean_ctor_set(v___x_3215_, 1, v___x_3214_);
v___x_3216_ = lean_box(1);
v___x_3217_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3217_, 0, v___x_3215_);
lean_ctor_set(v___x_3217_, 1, v___x_3216_);
v___x_3218_ = ((lean_object*)(l_Lean_Lsp_instReprLineRange_repr___redArg___closed__11));
v___x_3219_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3219_, 0, v___x_3217_);
lean_ctor_set(v___x_3219_, 1, v___x_3218_);
v___x_3220_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3220_, 0, v___x_3219_);
lean_ctor_set(v___x_3220_, 1, v___x_3204_);
v___x_3221_ = lean_obj_once(&l_Lean_Lsp_instReprLineRange_repr___redArg___closed__12, &l_Lean_Lsp_instReprLineRange_repr___redArg___closed__12_once, _init_l_Lean_Lsp_instReprLineRange_repr___redArg___closed__12);
v___x_3222_ = l_Nat_reprFast(v_end_3200_);
v___x_3223_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3223_, 0, v___x_3222_);
v___x_3224_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3224_, 0, v___x_3221_);
lean_ctor_set(v___x_3224_, 1, v___x_3223_);
v___x_3225_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3225_, 0, v___x_3224_);
lean_ctor_set_uint8(v___x_3225_, sizeof(void*)*1, v___x_3211_);
v___x_3226_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3226_, 0, v___x_3220_);
lean_ctor_set(v___x_3226_, 1, v___x_3225_);
v___x_3227_ = lean_obj_once(&l_Lean_Lsp_instReprLineRange_repr___redArg___closed__15, &l_Lean_Lsp_instReprLineRange_repr___redArg___closed__15_once, _init_l_Lean_Lsp_instReprLineRange_repr___redArg___closed__15);
v___x_3228_ = ((lean_object*)(l_Lean_Lsp_instReprLineRange_repr___redArg___closed__16));
v___x_3229_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3229_, 0, v___x_3228_);
lean_ctor_set(v___x_3229_, 1, v___x_3226_);
v___x_3230_ = ((lean_object*)(l_Lean_Lsp_instReprLineRange_repr___redArg___closed__17));
v___x_3231_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3231_, 0, v___x_3229_);
lean_ctor_set(v___x_3231_, 1, v___x_3230_);
v___x_3232_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3232_, 0, v___x_3227_);
lean_ctor_set(v___x_3232_, 1, v___x_3231_);
v___x_3233_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3233_, 0, v___x_3232_);
lean_ctor_set_uint8(v___x_3233_, sizeof(void*)*1, v___x_3211_);
return v___x_3233_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instReprLineRange_repr(lean_object* v_x_3236_, lean_object* v_prec_3237_){
_start:
{
lean_object* v___x_3238_; 
v___x_3238_ = l_Lean_Lsp_instReprLineRange_repr___redArg(v_x_3236_);
return v___x_3238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instReprLineRange_repr___boxed(lean_object* v_x_3239_, lean_object* v_prec_3240_){
_start:
{
lean_object* v_res_3241_; 
v_res_3241_ = l_Lean_Lsp_instReprLineRange_repr(v_x_3239_, v_prec_3240_);
lean_dec(v_prec_3240_);
return v_res_3241_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__2(void){
_start:
{
uint8_t v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; 
v___x_3249_ = 1;
v___x_3250_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__1));
v___x_3251_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3250_, v___x_3249_);
return v___x_3251_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__3(void){
_start:
{
lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; 
v___x_3252_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6));
v___x_3253_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__2, &l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__2);
v___x_3254_ = lean_string_append(v___x_3253_, v___x_3252_);
return v___x_3254_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__5(void){
_start:
{
uint8_t v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; 
v___x_3257_ = 1;
v___x_3258_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__4));
v___x_3259_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3258_, v___x_3257_);
return v___x_3259_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__6(void){
_start:
{
lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; 
v___x_3260_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__5, &l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__5);
v___x_3261_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__3);
v___x_3262_ = lean_string_append(v___x_3261_, v___x_3260_);
return v___x_3262_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__7(void){
_start:
{
lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; 
v___x_3263_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_3264_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__6);
v___x_3265_ = lean_string_append(v___x_3264_, v___x_3263_);
return v___x_3265_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__9(void){
_start:
{
uint8_t v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; 
v___x_3268_ = 1;
v___x_3269_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__8));
v___x_3270_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3269_, v___x_3268_);
return v___x_3270_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__10(void){
_start:
{
lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; 
v___x_3271_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__9, &l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__9);
v___x_3272_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__3);
v___x_3273_ = lean_string_append(v___x_3272_, v___x_3271_);
return v___x_3273_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__11(void){
_start:
{
lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; 
v___x_3274_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_3275_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__10, &l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__10);
v___x_3276_ = lean_string_append(v___x_3275_, v___x_3274_);
return v___x_3276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLineRange_fromJson(lean_object* v_json_3277_){
_start:
{
lean_object* v___x_3278_; lean_object* v___x_3279_; 
v___x_3278_ = ((lean_object*)(l_Lean_Lsp_instReprLineRange_repr___redArg___closed__1));
lean_inc(v_json_3277_);
v___x_3279_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson_spec__1(v_json_3277_, v___x_3278_);
if (lean_obj_tag(v___x_3279_) == 0)
{
lean_object* v_a_3280_; lean_object* v___x_3282_; uint8_t v_isShared_3283_; uint8_t v_isSharedCheck_3289_; 
lean_dec(v_json_3277_);
v_a_3280_ = lean_ctor_get(v___x_3279_, 0);
v_isSharedCheck_3289_ = !lean_is_exclusive(v___x_3279_);
if (v_isSharedCheck_3289_ == 0)
{
v___x_3282_ = v___x_3279_;
v_isShared_3283_ = v_isSharedCheck_3289_;
goto v_resetjp_3281_;
}
else
{
lean_inc(v_a_3280_);
lean_dec(v___x_3279_);
v___x_3282_ = lean_box(0);
v_isShared_3283_ = v_isSharedCheck_3289_;
goto v_resetjp_3281_;
}
v_resetjp_3281_:
{
lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3287_; 
v___x_3284_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__7);
v___x_3285_ = lean_string_append(v___x_3284_, v_a_3280_);
lean_dec(v_a_3280_);
if (v_isShared_3283_ == 0)
{
lean_ctor_set(v___x_3282_, 0, v___x_3285_);
v___x_3287_ = v___x_3282_;
goto v_reusejp_3286_;
}
else
{
lean_object* v_reuseFailAlloc_3288_; 
v_reuseFailAlloc_3288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3288_, 0, v___x_3285_);
v___x_3287_ = v_reuseFailAlloc_3288_;
goto v_reusejp_3286_;
}
v_reusejp_3286_:
{
return v___x_3287_;
}
}
}
else
{
if (lean_obj_tag(v___x_3279_) == 0)
{
lean_object* v_a_3290_; lean_object* v___x_3292_; uint8_t v_isShared_3293_; uint8_t v_isSharedCheck_3297_; 
lean_dec(v_json_3277_);
v_a_3290_ = lean_ctor_get(v___x_3279_, 0);
v_isSharedCheck_3297_ = !lean_is_exclusive(v___x_3279_);
if (v_isSharedCheck_3297_ == 0)
{
v___x_3292_ = v___x_3279_;
v_isShared_3293_ = v_isSharedCheck_3297_;
goto v_resetjp_3291_;
}
else
{
lean_inc(v_a_3290_);
lean_dec(v___x_3279_);
v___x_3292_ = lean_box(0);
v_isShared_3293_ = v_isSharedCheck_3297_;
goto v_resetjp_3291_;
}
v_resetjp_3291_:
{
lean_object* v___x_3295_; 
if (v_isShared_3293_ == 0)
{
lean_ctor_set_tag(v___x_3292_, 0);
v___x_3295_ = v___x_3292_;
goto v_reusejp_3294_;
}
else
{
lean_object* v_reuseFailAlloc_3296_; 
v_reuseFailAlloc_3296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3296_, 0, v_a_3290_);
v___x_3295_ = v_reuseFailAlloc_3296_;
goto v_reusejp_3294_;
}
v_reusejp_3294_:
{
return v___x_3295_;
}
}
}
else
{
lean_object* v_a_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; 
v_a_3298_ = lean_ctor_get(v___x_3279_, 0);
lean_inc(v_a_3298_);
lean_dec_ref(v___x_3279_);
v___x_3299_ = ((lean_object*)(l_Lean_Lsp_instReprLineRange_repr___redArg___closed__10));
v___x_3300_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson_spec__1(v_json_3277_, v___x_3299_);
if (lean_obj_tag(v___x_3300_) == 0)
{
lean_object* v_a_3301_; lean_object* v___x_3303_; uint8_t v_isShared_3304_; uint8_t v_isSharedCheck_3310_; 
lean_dec(v_a_3298_);
v_a_3301_ = lean_ctor_get(v___x_3300_, 0);
v_isSharedCheck_3310_ = !lean_is_exclusive(v___x_3300_);
if (v_isSharedCheck_3310_ == 0)
{
v___x_3303_ = v___x_3300_;
v_isShared_3304_ = v_isSharedCheck_3310_;
goto v_resetjp_3302_;
}
else
{
lean_inc(v_a_3301_);
lean_dec(v___x_3300_);
v___x_3303_ = lean_box(0);
v_isShared_3304_ = v_isSharedCheck_3310_;
goto v_resetjp_3302_;
}
v_resetjp_3302_:
{
lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3308_; 
v___x_3305_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__11, &l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__11);
v___x_3306_ = lean_string_append(v___x_3305_, v_a_3301_);
lean_dec(v_a_3301_);
if (v_isShared_3304_ == 0)
{
lean_ctor_set(v___x_3303_, 0, v___x_3306_);
v___x_3308_ = v___x_3303_;
goto v_reusejp_3307_;
}
else
{
lean_object* v_reuseFailAlloc_3309_; 
v_reuseFailAlloc_3309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3309_, 0, v___x_3306_);
v___x_3308_ = v_reuseFailAlloc_3309_;
goto v_reusejp_3307_;
}
v_reusejp_3307_:
{
return v___x_3308_;
}
}
}
else
{
if (lean_obj_tag(v___x_3300_) == 0)
{
lean_object* v_a_3311_; lean_object* v___x_3313_; uint8_t v_isShared_3314_; uint8_t v_isSharedCheck_3318_; 
lean_dec(v_a_3298_);
v_a_3311_ = lean_ctor_get(v___x_3300_, 0);
v_isSharedCheck_3318_ = !lean_is_exclusive(v___x_3300_);
if (v_isSharedCheck_3318_ == 0)
{
v___x_3313_ = v___x_3300_;
v_isShared_3314_ = v_isSharedCheck_3318_;
goto v_resetjp_3312_;
}
else
{
lean_inc(v_a_3311_);
lean_dec(v___x_3300_);
v___x_3313_ = lean_box(0);
v_isShared_3314_ = v_isSharedCheck_3318_;
goto v_resetjp_3312_;
}
v_resetjp_3312_:
{
lean_object* v___x_3316_; 
if (v_isShared_3314_ == 0)
{
lean_ctor_set_tag(v___x_3313_, 0);
v___x_3316_ = v___x_3313_;
goto v_reusejp_3315_;
}
else
{
lean_object* v_reuseFailAlloc_3317_; 
v_reuseFailAlloc_3317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3317_, 0, v_a_3311_);
v___x_3316_ = v_reuseFailAlloc_3317_;
goto v_reusejp_3315_;
}
v_reusejp_3315_:
{
return v___x_3316_;
}
}
}
else
{
lean_object* v_a_3319_; lean_object* v___x_3321_; uint8_t v_isShared_3322_; uint8_t v_isSharedCheck_3327_; 
v_a_3319_ = lean_ctor_get(v___x_3300_, 0);
v_isSharedCheck_3327_ = !lean_is_exclusive(v___x_3300_);
if (v_isSharedCheck_3327_ == 0)
{
v___x_3321_ = v___x_3300_;
v_isShared_3322_ = v_isSharedCheck_3327_;
goto v_resetjp_3320_;
}
else
{
lean_inc(v_a_3319_);
lean_dec(v___x_3300_);
v___x_3321_ = lean_box(0);
v_isShared_3322_ = v_isSharedCheck_3327_;
goto v_resetjp_3320_;
}
v_resetjp_3320_:
{
lean_object* v___x_3323_; lean_object* v___x_3325_; 
v___x_3323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3323_, 0, v_a_3298_);
lean_ctor_set(v___x_3323_, 1, v_a_3319_);
if (v_isShared_3322_ == 0)
{
lean_ctor_set(v___x_3321_, 0, v___x_3323_);
v___x_3325_ = v___x_3321_;
goto v_reusejp_3324_;
}
else
{
lean_object* v_reuseFailAlloc_3326_; 
v_reuseFailAlloc_3326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3326_, 0, v___x_3323_);
v___x_3325_ = v_reuseFailAlloc_3326_;
goto v_reusejp_3324_;
}
v_reusejp_3324_:
{
return v___x_3325_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLineRange_toJson(lean_object* v_x_3330_){
_start:
{
lean_object* v_start_3331_; lean_object* v_end_3332_; lean_object* v___x_3334_; uint8_t v_isShared_3335_; uint8_t v_isSharedCheck_3354_; 
v_start_3331_ = lean_ctor_get(v_x_3330_, 0);
v_end_3332_ = lean_ctor_get(v_x_3330_, 1);
v_isSharedCheck_3354_ = !lean_is_exclusive(v_x_3330_);
if (v_isSharedCheck_3354_ == 0)
{
v___x_3334_ = v_x_3330_;
v_isShared_3335_ = v_isSharedCheck_3354_;
goto v_resetjp_3333_;
}
else
{
lean_inc(v_end_3332_);
lean_inc(v_start_3331_);
lean_dec(v_x_3330_);
v___x_3334_ = lean_box(0);
v_isShared_3335_ = v_isSharedCheck_3354_;
goto v_resetjp_3333_;
}
v_resetjp_3333_:
{
lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3340_; 
v___x_3336_ = ((lean_object*)(l_Lean_Lsp_instReprLineRange_repr___redArg___closed__1));
v___x_3337_ = l_Lean_JsonNumber_fromNat(v_start_3331_);
v___x_3338_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3338_, 0, v___x_3337_);
if (v_isShared_3335_ == 0)
{
lean_ctor_set(v___x_3334_, 1, v___x_3338_);
lean_ctor_set(v___x_3334_, 0, v___x_3336_);
v___x_3340_ = v___x_3334_;
goto v_reusejp_3339_;
}
else
{
lean_object* v_reuseFailAlloc_3353_; 
v_reuseFailAlloc_3353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3353_, 0, v___x_3336_);
lean_ctor_set(v_reuseFailAlloc_3353_, 1, v___x_3338_);
v___x_3340_ = v_reuseFailAlloc_3353_;
goto v_reusejp_3339_;
}
v_reusejp_3339_:
{
lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; 
v___x_3341_ = lean_box(0);
v___x_3342_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3342_, 0, v___x_3340_);
lean_ctor_set(v___x_3342_, 1, v___x_3341_);
v___x_3343_ = ((lean_object*)(l_Lean_Lsp_instReprLineRange_repr___redArg___closed__10));
v___x_3344_ = l_Lean_JsonNumber_fromNat(v_end_3332_);
v___x_3345_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3345_, 0, v___x_3344_);
v___x_3346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3346_, 0, v___x_3343_);
lean_ctor_set(v___x_3346_, 1, v___x_3345_);
v___x_3347_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3347_, 0, v___x_3346_);
lean_ctor_set(v___x_3347_, 1, v___x_3341_);
v___x_3348_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3348_, 0, v___x_3347_);
lean_ctor_set(v___x_3348_, 1, v___x_3341_);
v___x_3349_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3349_, 0, v___x_3342_);
lean_ctor_set(v___x_3349_, 1, v___x_3348_);
v___x_3350_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0));
v___x_3351_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_3349_, v___x_3350_);
v___x_3352_ = l_Lean_Json_mkObj(v___x_3351_);
lean_dec(v___x_3351_);
return v___x_3352_;
}
}
}
}
lean_object* runtime_initialize_Lean_Data_Lsp_TextSync(uint8_t builtin);
lean_object* runtime_initialize_Lean_Server_Rpc_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_Lsp_Extra(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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

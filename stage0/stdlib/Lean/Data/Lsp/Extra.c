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
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson(lean_object*);
lean_object* l_Lean_Lsp_instToJsonVersionedTextDocumentIdentifier_toJson(lean_object*);
lean_object* l_Lean_Lsp_instToJsonRpcWireFormat_toJson(uint8_t);
lean_object* l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson(lean_object*);
lean_object* l_Lean_Lsp_instToJsonTextDocumentItem_toJson(lean_object*);
lean_object* l_Lean_Name_fromJson_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DependencyBuildMode_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Lsp_DependencyBuildMode_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanFileProgressKind_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanFileProgressKind_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanImportMetaKind_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanImportMetaKind_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Lsp_DependencyBuildMode_ctorIdx___impl(uint8_t v_x_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(v_x_1_);
v___x_3_ = lean_obj_tag_nat(v___x_2_);
lean_dec(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DependencyBuildMode_ctorIdx___impl___boxed(lean_object* v_x_4_){
_start:
{
uint8_t v_x_4__boxed_5_; lean_object* v_res_6_; 
v_x_4__boxed_5_ = lean_unbox(v_x_4_);
v_res_6_ = l_Lean_Lsp_DependencyBuildMode_ctorIdx___impl(v_x_4__boxed_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DependencyBuildMode_ctorElim___redArg(lean_object* v_k_7_){
_start:
{
lean_inc(v_k_7_);
return v_k_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DependencyBuildMode_ctorElim___redArg___boxed(lean_object* v_k_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Lean_Lsp_DependencyBuildMode_ctorElim___redArg(v_k_8_);
lean_dec(v_k_8_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DependencyBuildMode_ctorElim(lean_object* v_motive_10_, lean_object* v_ctorIdx_11_, uint8_t v_t_12_, lean_object* v_h_13_, lean_object* v_k_14_){
_start:
{
lean_inc(v_k_14_);
return v_k_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DependencyBuildMode_ctorElim___boxed(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, lean_object* v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
uint8_t v_t_boxed_20_; lean_object* v_res_21_; 
v_t_boxed_20_ = lean_unbox(v_t_17_);
v_res_21_ = l_Lean_Lsp_DependencyBuildMode_ctorElim(v_motive_15_, v_ctorIdx_16_, v_t_boxed_20_, v_h_18_, v_k_19_);
lean_dec(v_k_19_);
lean_dec(v_ctorIdx_16_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DependencyBuildMode_always_elim___redArg(lean_object* v_always_22_){
_start:
{
lean_inc(v_always_22_);
return v_always_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DependencyBuildMode_always_elim___redArg___boxed(lean_object* v_always_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Lean_Lsp_DependencyBuildMode_always_elim___redArg(v_always_23_);
lean_dec(v_always_23_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DependencyBuildMode_always_elim(lean_object* v_motive_25_, uint8_t v_t_26_, lean_object* v_h_27_, lean_object* v_always_28_){
_start:
{
lean_inc(v_always_28_);
return v_always_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DependencyBuildMode_always_elim___boxed(lean_object* v_motive_29_, lean_object* v_t_30_, lean_object* v_h_31_, lean_object* v_always_32_){
_start:
{
uint8_t v_t_boxed_33_; lean_object* v_res_34_; 
v_t_boxed_33_ = lean_unbox(v_t_30_);
v_res_34_ = l_Lean_Lsp_DependencyBuildMode_always_elim(v_motive_29_, v_t_boxed_33_, v_h_31_, v_always_32_);
lean_dec(v_always_32_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DependencyBuildMode_once_elim___redArg(lean_object* v_once_35_){
_start:
{
lean_inc(v_once_35_);
return v_once_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DependencyBuildMode_once_elim___redArg___boxed(lean_object* v_once_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Lean_Lsp_DependencyBuildMode_once_elim___redArg(v_once_36_);
lean_dec(v_once_36_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DependencyBuildMode_once_elim(lean_object* v_motive_38_, uint8_t v_t_39_, lean_object* v_h_40_, lean_object* v_once_41_){
_start:
{
lean_inc(v_once_41_);
return v_once_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DependencyBuildMode_once_elim___boxed(lean_object* v_motive_42_, lean_object* v_t_43_, lean_object* v_h_44_, lean_object* v_once_45_){
_start:
{
uint8_t v_t_boxed_46_; lean_object* v_res_47_; 
v_t_boxed_46_ = lean_unbox(v_t_43_);
v_res_47_ = l_Lean_Lsp_DependencyBuildMode_once_elim(v_motive_42_, v_t_boxed_46_, v_h_44_, v_once_45_);
lean_dec(v_once_45_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DependencyBuildMode_never_elim___redArg(lean_object* v_never_48_){
_start:
{
lean_inc(v_never_48_);
return v_never_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DependencyBuildMode_never_elim___redArg___boxed(lean_object* v_never_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_Lean_Lsp_DependencyBuildMode_never_elim___redArg(v_never_49_);
lean_dec(v_never_49_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DependencyBuildMode_never_elim(lean_object* v_motive_51_, uint8_t v_t_52_, lean_object* v_h_53_, lean_object* v_never_54_){
_start:
{
lean_inc(v_never_54_);
return v_never_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DependencyBuildMode_never_elim___boxed(lean_object* v_motive_55_, lean_object* v_t_56_, lean_object* v_h_57_, lean_object* v_never_58_){
_start:
{
uint8_t v_t_boxed_59_; lean_object* v_res_60_; 
v_t_boxed_59_ = lean_unbox(v_t_56_);
v_res_60_ = l_Lean_Lsp_DependencyBuildMode_never_elim(v_motive_55_, v_t_boxed_59_, v_h_57_, v_never_58_);
lean_dec(v_never_58_);
return v_res_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson(lean_object* v_json_79_){
_start:
{
lean_object* v___x_80_; 
v___x_80_ = l_Lean_Json_getTag_x3f(v_json_79_);
if (lean_obj_tag(v___x_80_) == 0)
{
lean_object* v___x_81_; 
v___x_81_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__1));
return v___x_81_;
}
else
{
lean_object* v_val_82_; lean_object* v___x_83_; uint8_t v___x_84_; 
v_val_82_ = lean_ctor_get(v___x_80_, 0);
lean_inc(v_val_82_);
lean_dec_ref_known(v___x_80_, 1);
v___x_83_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__2));
v___x_84_ = lean_string_dec_eq(v_val_82_, v___x_83_);
if (v___x_84_ == 0)
{
lean_object* v___x_85_; uint8_t v___x_86_; 
v___x_85_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__3));
v___x_86_ = lean_string_dec_eq(v_val_82_, v___x_85_);
if (v___x_86_ == 0)
{
lean_object* v___x_87_; uint8_t v___x_88_; 
v___x_87_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__4));
v___x_88_ = lean_string_dec_eq(v_val_82_, v___x_87_);
lean_dec(v_val_82_);
if (v___x_88_ == 0)
{
lean_object* v___x_89_; 
v___x_89_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__6));
return v___x_89_;
}
else
{
lean_object* v___x_90_; 
v___x_90_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__7));
return v___x_90_;
}
}
else
{
lean_object* v___x_91_; 
lean_dec(v_val_82_);
v___x_91_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__8));
return v___x_91_;
}
}
else
{
lean_object* v___x_92_; 
lean_dec(v_val_82_);
v___x_92_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__9));
return v___x_92_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDependencyBuildMode_toJson(uint8_t v_x_101_){
_start:
{
switch(v_x_101_)
{
case 0:
{
lean_object* v___x_102_; 
v___x_102_ = ((lean_object*)(l_Lean_Lsp_instToJsonDependencyBuildMode_toJson___closed__0));
return v___x_102_;
}
case 1:
{
lean_object* v___x_103_; 
v___x_103_ = ((lean_object*)(l_Lean_Lsp_instToJsonDependencyBuildMode_toJson___closed__1));
return v___x_103_;
}
default: 
{
lean_object* v___x_104_; 
v___x_104_ = ((lean_object*)(l_Lean_Lsp_instToJsonDependencyBuildMode_toJson___closed__2));
return v___x_104_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDependencyBuildMode_toJson___boxed(lean_object* v_x_105_){
_start:
{
uint8_t v_x_64__boxed_106_; lean_object* v_res_107_; 
v_x_64__boxed_106_ = lean_unbox(v_x_105_);
v_res_107_ = l_Lean_Lsp_instToJsonDependencyBuildMode_toJson(v_x_64__boxed_106_);
return v_res_107_;
}
}
static uint8_t _init_l_Lean_Lsp_instInhabitedDependencyBuildMode_default(void){
_start:
{
uint8_t v___x_110_; 
v___x_110_ = 0;
return v___x_110_;
}
}
static uint8_t _init_l_Lean_Lsp_instInhabitedDependencyBuildMode(void){
_start:
{
uint8_t v___x_111_; 
v___x_111_ = 0;
return v___x_111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson_spec__0(lean_object* v_j_112_, lean_object* v_k_113_){
_start:
{
lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_114_ = l_Lean_Json_getObjValD(v_j_112_, v_k_113_);
v___x_115_ = l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson(v___x_114_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson_spec__0___boxed(lean_object* v_j_116_, lean_object* v_k_117_){
_start:
{
lean_object* v_res_118_; 
v_res_118_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson_spec__0(v_j_116_, v_k_117_);
lean_dec_ref(v_k_117_);
return v_res_118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson_spec__1_spec__1(lean_object* v_x_121_){
_start:
{
if (lean_obj_tag(v_x_121_) == 0)
{
lean_object* v___x_122_; 
v___x_122_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson_spec__1_spec__1___closed__0));
return v___x_122_;
}
else
{
lean_object* v___x_123_; 
v___x_123_ = l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson(v_x_121_);
if (lean_obj_tag(v___x_123_) == 0)
{
lean_object* v_a_124_; lean_object* v___x_126_; uint8_t v_isShared_127_; uint8_t v_isSharedCheck_131_; 
v_a_124_ = lean_ctor_get(v___x_123_, 0);
v_isSharedCheck_131_ = !lean_is_exclusive(v___x_123_);
if (v_isSharedCheck_131_ == 0)
{
v___x_126_ = v___x_123_;
v_isShared_127_ = v_isSharedCheck_131_;
goto v_resetjp_125_;
}
else
{
lean_inc(v_a_124_);
lean_dec(v___x_123_);
v___x_126_ = lean_box(0);
v_isShared_127_ = v_isSharedCheck_131_;
goto v_resetjp_125_;
}
v_resetjp_125_:
{
lean_object* v___x_129_; 
if (v_isShared_127_ == 0)
{
v___x_129_ = v___x_126_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_130_; 
v_reuseFailAlloc_130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_130_, 0, v_a_124_);
v___x_129_ = v_reuseFailAlloc_130_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
return v___x_129_;
}
}
}
else
{
lean_object* v_a_132_; lean_object* v___x_134_; uint8_t v_isShared_135_; uint8_t v_isSharedCheck_140_; 
v_a_132_ = lean_ctor_get(v___x_123_, 0);
v_isSharedCheck_140_ = !lean_is_exclusive(v___x_123_);
if (v_isSharedCheck_140_ == 0)
{
v___x_134_ = v___x_123_;
v_isShared_135_ = v_isSharedCheck_140_;
goto v_resetjp_133_;
}
else
{
lean_inc(v_a_132_);
lean_dec(v___x_123_);
v___x_134_ = lean_box(0);
v_isShared_135_ = v_isSharedCheck_140_;
goto v_resetjp_133_;
}
v_resetjp_133_:
{
lean_object* v___x_136_; lean_object* v___x_138_; 
v___x_136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_136_, 0, v_a_132_);
if (v_isShared_135_ == 0)
{
lean_ctor_set(v___x_134_, 0, v___x_136_);
v___x_138_ = v___x_134_;
goto v_reusejp_137_;
}
else
{
lean_object* v_reuseFailAlloc_139_; 
v_reuseFailAlloc_139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_139_, 0, v___x_136_);
v___x_138_ = v_reuseFailAlloc_139_;
goto v_reusejp_137_;
}
v_reusejp_137_:
{
return v___x_138_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson_spec__1(lean_object* v_j_141_, lean_object* v_k_142_){
_start:
{
lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_143_ = l_Lean_Json_getObjValD(v_j_141_, v_k_142_);
v___x_144_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson_spec__1_spec__1(v___x_143_);
return v___x_144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson_spec__1___boxed(lean_object* v_j_145_, lean_object* v_k_146_){
_start:
{
lean_object* v_res_147_; 
v_res_147_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson_spec__1(v_j_145_, v_k_146_);
lean_dec_ref(v_k_146_);
return v_res_147_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__5(void){
_start:
{
uint8_t v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_156_ = 1;
v___x_157_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__4));
v___x_158_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_157_, v___x_156_);
return v___x_158_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__7(void){
_start:
{
lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_160_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6));
v___x_161_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__5, &l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__5);
v___x_162_ = lean_string_append(v___x_161_, v___x_160_);
return v___x_162_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9(void){
_start:
{
uint8_t v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_165_ = 1;
v___x_166_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__8));
v___x_167_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_166_, v___x_165_);
return v___x_167_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__10(void){
_start:
{
lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_168_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9, &l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9);
v___x_169_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__7);
v___x_170_ = lean_string_append(v___x_169_, v___x_168_);
return v___x_170_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__12(void){
_start:
{
lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_172_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_173_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__10, &l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__10);
v___x_174_ = lean_string_append(v___x_173_, v___x_172_);
return v___x_174_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__16(void){
_start:
{
uint8_t v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_179_ = 1;
v___x_180_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__15));
v___x_181_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_180_, v___x_179_);
return v___x_181_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__17(void){
_start:
{
lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_182_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__16, &l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__16_once, _init_l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__16);
v___x_183_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__7);
v___x_184_ = lean_string_append(v___x_183_, v___x_182_);
return v___x_184_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__18(void){
_start:
{
lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; 
v___x_185_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_186_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__17, &l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__17_once, _init_l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__17);
v___x_187_ = lean_string_append(v___x_186_, v___x_185_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson(lean_object* v_json_188_){
_start:
{
lean_object* v___x_189_; lean_object* v___x_190_; 
v___x_189_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__0));
lean_inc(v_json_188_);
v___x_190_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson_spec__0(v_json_188_, v___x_189_);
if (lean_obj_tag(v___x_190_) == 0)
{
lean_object* v_a_191_; lean_object* v___x_193_; uint8_t v_isShared_194_; uint8_t v_isSharedCheck_200_; 
lean_dec(v_json_188_);
v_a_191_ = lean_ctor_get(v___x_190_, 0);
v_isSharedCheck_200_ = !lean_is_exclusive(v___x_190_);
if (v_isSharedCheck_200_ == 0)
{
v___x_193_ = v___x_190_;
v_isShared_194_ = v_isSharedCheck_200_;
goto v_resetjp_192_;
}
else
{
lean_inc(v_a_191_);
lean_dec(v___x_190_);
v___x_193_ = lean_box(0);
v_isShared_194_ = v_isSharedCheck_200_;
goto v_resetjp_192_;
}
v_resetjp_192_:
{
lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_198_; 
v___x_195_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__12, &l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__12);
v___x_196_ = lean_string_append(v___x_195_, v_a_191_);
lean_dec(v_a_191_);
if (v_isShared_194_ == 0)
{
lean_ctor_set(v___x_193_, 0, v___x_196_);
v___x_198_ = v___x_193_;
goto v_reusejp_197_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v___x_196_);
v___x_198_ = v_reuseFailAlloc_199_;
goto v_reusejp_197_;
}
v_reusejp_197_:
{
return v___x_198_;
}
}
}
else
{
if (lean_obj_tag(v___x_190_) == 0)
{
lean_object* v_a_201_; lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_208_; 
lean_dec(v_json_188_);
v_a_201_ = lean_ctor_get(v___x_190_, 0);
v_isSharedCheck_208_ = !lean_is_exclusive(v___x_190_);
if (v_isSharedCheck_208_ == 0)
{
v___x_203_ = v___x_190_;
v_isShared_204_ = v_isSharedCheck_208_;
goto v_resetjp_202_;
}
else
{
lean_inc(v_a_201_);
lean_dec(v___x_190_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_208_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
lean_object* v___x_206_; 
if (v_isShared_204_ == 0)
{
lean_ctor_set_tag(v___x_203_, 0);
v___x_206_ = v___x_203_;
goto v_reusejp_205_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_207_, 0, v_a_201_);
v___x_206_ = v_reuseFailAlloc_207_;
goto v_reusejp_205_;
}
v_reusejp_205_:
{
return v___x_206_;
}
}
}
else
{
lean_object* v_a_209_; lean_object* v___x_210_; lean_object* v___x_211_; 
v_a_209_ = lean_ctor_get(v___x_190_, 0);
lean_inc(v_a_209_);
lean_dec_ref_known(v___x_190_, 1);
v___x_210_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__13));
v___x_211_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson_spec__1(v_json_188_, v___x_210_);
if (lean_obj_tag(v___x_211_) == 0)
{
lean_object* v_a_212_; lean_object* v___x_214_; uint8_t v_isShared_215_; uint8_t v_isSharedCheck_221_; 
lean_dec(v_a_209_);
v_a_212_ = lean_ctor_get(v___x_211_, 0);
v_isSharedCheck_221_ = !lean_is_exclusive(v___x_211_);
if (v_isSharedCheck_221_ == 0)
{
v___x_214_ = v___x_211_;
v_isShared_215_ = v_isSharedCheck_221_;
goto v_resetjp_213_;
}
else
{
lean_inc(v_a_212_);
lean_dec(v___x_211_);
v___x_214_ = lean_box(0);
v_isShared_215_ = v_isSharedCheck_221_;
goto v_resetjp_213_;
}
v_resetjp_213_:
{
lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_219_; 
v___x_216_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__18, &l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__18_once, _init_l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__18);
v___x_217_ = lean_string_append(v___x_216_, v_a_212_);
lean_dec(v_a_212_);
if (v_isShared_215_ == 0)
{
lean_ctor_set(v___x_214_, 0, v___x_217_);
v___x_219_ = v___x_214_;
goto v_reusejp_218_;
}
else
{
lean_object* v_reuseFailAlloc_220_; 
v_reuseFailAlloc_220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_220_, 0, v___x_217_);
v___x_219_ = v_reuseFailAlloc_220_;
goto v_reusejp_218_;
}
v_reusejp_218_:
{
return v___x_219_;
}
}
}
else
{
if (lean_obj_tag(v___x_211_) == 0)
{
lean_object* v_a_222_; lean_object* v___x_224_; uint8_t v_isShared_225_; uint8_t v_isSharedCheck_229_; 
lean_dec(v_a_209_);
v_a_222_ = lean_ctor_get(v___x_211_, 0);
v_isSharedCheck_229_ = !lean_is_exclusive(v___x_211_);
if (v_isSharedCheck_229_ == 0)
{
v___x_224_ = v___x_211_;
v_isShared_225_ = v_isSharedCheck_229_;
goto v_resetjp_223_;
}
else
{
lean_inc(v_a_222_);
lean_dec(v___x_211_);
v___x_224_ = lean_box(0);
v_isShared_225_ = v_isSharedCheck_229_;
goto v_resetjp_223_;
}
v_resetjp_223_:
{
lean_object* v___x_227_; 
if (v_isShared_225_ == 0)
{
lean_ctor_set_tag(v___x_224_, 0);
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
lean_object* v_a_230_; lean_object* v___x_232_; uint8_t v_isShared_233_; uint8_t v_isSharedCheck_238_; 
v_a_230_ = lean_ctor_get(v___x_211_, 0);
v_isSharedCheck_238_ = !lean_is_exclusive(v___x_211_);
if (v_isSharedCheck_238_ == 0)
{
v___x_232_ = v___x_211_;
v_isShared_233_ = v_isSharedCheck_238_;
goto v_resetjp_231_;
}
else
{
lean_inc(v_a_230_);
lean_dec(v___x_211_);
v___x_232_ = lean_box(0);
v_isShared_233_ = v_isSharedCheck_238_;
goto v_resetjp_231_;
}
v_resetjp_231_:
{
lean_object* v___x_234_; lean_object* v___x_236_; 
v___x_234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_234_, 0, v_a_209_);
lean_ctor_set(v___x_234_, 1, v_a_230_);
if (v_isShared_233_ == 0)
{
lean_ctor_set(v___x_232_, 0, v___x_234_);
v___x_236_ = v___x_232_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_237_, 0, v___x_234_);
v___x_236_ = v_reuseFailAlloc_237_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
return v___x_236_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__0(lean_object* v_k_241_, lean_object* v_x_242_){
_start:
{
if (lean_obj_tag(v_x_242_) == 0)
{
lean_object* v___x_243_; 
lean_dec_ref(v_k_241_);
v___x_243_ = lean_box(0);
return v___x_243_;
}
else
{
lean_object* v_val_244_; uint8_t v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; 
v_val_244_ = lean_ctor_get(v_x_242_, 0);
v___x_245_ = lean_unbox(v_val_244_);
v___x_246_ = l_Lean_Lsp_instToJsonDependencyBuildMode_toJson(v___x_245_);
v___x_247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_247_, 0, v_k_241_);
lean_ctor_set(v___x_247_, 1, v___x_246_);
v___x_248_ = lean_box(0);
v___x_249_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_249_, 0, v___x_247_);
lean_ctor_set(v___x_249_, 1, v___x_248_);
return v___x_249_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__0___boxed(lean_object* v_k_250_, lean_object* v_x_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__0(v_k_250_, v_x_251_);
lean_dec(v_x_251_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(lean_object* v_a_253_, lean_object* v_a_254_){
_start:
{
if (lean_obj_tag(v_a_253_) == 0)
{
lean_object* v___x_255_; 
v___x_255_ = lean_array_to_list(v_a_254_);
return v___x_255_;
}
else
{
lean_object* v_head_256_; lean_object* v_tail_257_; lean_object* v___x_258_; 
v_head_256_ = lean_ctor_get(v_a_253_, 0);
lean_inc(v_head_256_);
v_tail_257_ = lean_ctor_get(v_a_253_, 1);
lean_inc(v_tail_257_);
lean_dec_ref_known(v_a_253_, 2);
v___x_258_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_254_, v_head_256_);
v_a_253_ = v_tail_257_;
v_a_254_ = v___x_258_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson(lean_object* v_x_262_){
_start:
{
lean_object* v_toDidOpenTextDocumentParams_263_; lean_object* v_dependencyBuildMode_x3f_264_; lean_object* v___x_266_; uint8_t v_isShared_267_; uint8_t v_isSharedCheck_282_; 
v_toDidOpenTextDocumentParams_263_ = lean_ctor_get(v_x_262_, 0);
v_dependencyBuildMode_x3f_264_ = lean_ctor_get(v_x_262_, 1);
v_isSharedCheck_282_ = !lean_is_exclusive(v_x_262_);
if (v_isSharedCheck_282_ == 0)
{
v___x_266_ = v_x_262_;
v_isShared_267_ = v_isSharedCheck_282_;
goto v_resetjp_265_;
}
else
{
lean_inc(v_dependencyBuildMode_x3f_264_);
lean_inc(v_toDidOpenTextDocumentParams_263_);
lean_dec(v_x_262_);
v___x_266_ = lean_box(0);
v_isShared_267_ = v_isSharedCheck_282_;
goto v_resetjp_265_;
}
v_resetjp_265_:
{
lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_271_; 
v___x_268_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__0));
v___x_269_ = l_Lean_Lsp_instToJsonTextDocumentItem_toJson(v_toDidOpenTextDocumentParams_263_);
if (v_isShared_267_ == 0)
{
lean_ctor_set(v___x_266_, 1, v___x_269_);
lean_ctor_set(v___x_266_, 0, v___x_268_);
v___x_271_ = v___x_266_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v___x_268_);
lean_ctor_set(v_reuseFailAlloc_281_, 1, v___x_269_);
v___x_271_ = v_reuseFailAlloc_281_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_272_ = lean_box(0);
v___x_273_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_273_, 0, v___x_271_);
lean_ctor_set(v___x_273_, 1, v___x_272_);
v___x_274_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__13));
v___x_275_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__0(v___x_274_, v_dependencyBuildMode_x3f_264_);
lean_dec(v_dependencyBuildMode_x3f_264_);
v___x_276_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_276_, 0, v___x_275_);
lean_ctor_set(v___x_276_, 1, v___x_272_);
v___x_277_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_277_, 0, v___x_273_);
lean_ctor_set(v___x_277_, 1, v___x_276_);
v___x_278_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0));
v___x_279_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_277_, v___x_278_);
v___x_280_ = l_Lean_Json_mkObj(v___x_279_);
lean_dec(v___x_279_);
return v___x_280_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson_spec__0(lean_object* v_j_285_, lean_object* v_k_286_){
_start:
{
lean_object* v___x_287_; lean_object* v___x_288_; 
v___x_287_ = l_Lean_Json_getObjValD(v_j_285_, v_k_286_);
v___x_288_ = l_Lean_Json_getStr_x3f(v___x_287_);
return v___x_288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson_spec__0___boxed(lean_object* v_j_289_, lean_object* v_k_290_){
_start:
{
lean_object* v_res_291_; 
v_res_291_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson_spec__0(v_j_289_, v_k_290_);
lean_dec_ref(v_k_290_);
return v_res_291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson_spec__1(lean_object* v_j_292_, lean_object* v_k_293_){
_start:
{
lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_294_ = l_Lean_Json_getObjValD(v_j_292_, v_k_293_);
v___x_295_ = l_Lean_Json_getNat_x3f(v___x_294_);
return v___x_295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson_spec__1___boxed(lean_object* v_j_296_, lean_object* v_k_297_){
_start:
{
lean_object* v_res_298_; 
v_res_298_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson_spec__1(v_j_296_, v_k_297_);
lean_dec_ref(v_k_297_);
return v_res_298_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__3(void){
_start:
{
uint8_t v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_305_ = 1;
v___x_306_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__2));
v___x_307_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_306_, v___x_305_);
return v___x_307_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_308_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6));
v___x_309_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__3);
v___x_310_ = lean_string_append(v___x_309_, v___x_308_);
return v___x_310_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__6(void){
_start:
{
uint8_t v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_313_ = 1;
v___x_314_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__5));
v___x_315_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_314_, v___x_313_);
return v___x_315_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__7(void){
_start:
{
lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_316_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__6, &l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__6);
v___x_317_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__4);
v___x_318_ = lean_string_append(v___x_317_, v___x_316_);
return v___x_318_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__8(void){
_start:
{
lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_319_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_320_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__7);
v___x_321_ = lean_string_append(v___x_320_, v___x_319_);
return v___x_321_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__11(void){
_start:
{
uint8_t v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; 
v___x_325_ = 1;
v___x_326_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__10));
v___x_327_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_326_, v___x_325_);
return v___x_327_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__12(void){
_start:
{
lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_328_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__11, &l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__11);
v___x_329_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__4);
v___x_330_ = lean_string_append(v___x_329_, v___x_328_);
return v___x_330_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__13(void){
_start:
{
lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_331_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_332_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__12, &l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__12);
v___x_333_ = lean_string_append(v___x_332_, v___x_331_);
return v___x_333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson(lean_object* v_json_334_){
_start:
{
lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_335_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__0));
lean_inc(v_json_334_);
v___x_336_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson_spec__0(v_json_334_, v___x_335_);
if (lean_obj_tag(v___x_336_) == 0)
{
lean_object* v_a_337_; lean_object* v___x_339_; uint8_t v_isShared_340_; uint8_t v_isSharedCheck_346_; 
lean_dec(v_json_334_);
v_a_337_ = lean_ctor_get(v___x_336_, 0);
v_isSharedCheck_346_ = !lean_is_exclusive(v___x_336_);
if (v_isSharedCheck_346_ == 0)
{
v___x_339_ = v___x_336_;
v_isShared_340_ = v_isSharedCheck_346_;
goto v_resetjp_338_;
}
else
{
lean_inc(v_a_337_);
lean_dec(v___x_336_);
v___x_339_ = lean_box(0);
v_isShared_340_ = v_isSharedCheck_346_;
goto v_resetjp_338_;
}
v_resetjp_338_:
{
lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_344_; 
v___x_341_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__8);
v___x_342_ = lean_string_append(v___x_341_, v_a_337_);
lean_dec(v_a_337_);
if (v_isShared_340_ == 0)
{
lean_ctor_set(v___x_339_, 0, v___x_342_);
v___x_344_ = v___x_339_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v___x_342_);
v___x_344_ = v_reuseFailAlloc_345_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
return v___x_344_;
}
}
}
else
{
if (lean_obj_tag(v___x_336_) == 0)
{
lean_object* v_a_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_354_; 
lean_dec(v_json_334_);
v_a_347_ = lean_ctor_get(v___x_336_, 0);
v_isSharedCheck_354_ = !lean_is_exclusive(v___x_336_);
if (v_isSharedCheck_354_ == 0)
{
v___x_349_ = v___x_336_;
v_isShared_350_ = v_isSharedCheck_354_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_a_347_);
lean_dec(v___x_336_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_354_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
lean_object* v___x_352_; 
if (v_isShared_350_ == 0)
{
lean_ctor_set_tag(v___x_349_, 0);
v___x_352_ = v___x_349_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v_a_347_);
v___x_352_ = v_reuseFailAlloc_353_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
return v___x_352_;
}
}
}
else
{
lean_object* v_a_355_; lean_object* v___x_356_; lean_object* v___x_357_; 
v_a_355_ = lean_ctor_get(v___x_336_, 0);
lean_inc(v_a_355_);
lean_dec_ref_known(v___x_336_, 1);
v___x_356_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__9));
v___x_357_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson_spec__1(v_json_334_, v___x_356_);
if (lean_obj_tag(v___x_357_) == 0)
{
lean_object* v_a_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_367_; 
lean_dec(v_a_355_);
v_a_358_ = lean_ctor_get(v___x_357_, 0);
v_isSharedCheck_367_ = !lean_is_exclusive(v___x_357_);
if (v_isSharedCheck_367_ == 0)
{
v___x_360_ = v___x_357_;
v_isShared_361_ = v_isSharedCheck_367_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_a_358_);
lean_dec(v___x_357_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_367_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_365_; 
v___x_362_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__13, &l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__13);
v___x_363_ = lean_string_append(v___x_362_, v_a_358_);
lean_dec(v_a_358_);
if (v_isShared_361_ == 0)
{
lean_ctor_set(v___x_360_, 0, v___x_363_);
v___x_365_ = v___x_360_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v___x_363_);
v___x_365_ = v_reuseFailAlloc_366_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
return v___x_365_;
}
}
}
else
{
if (lean_obj_tag(v___x_357_) == 0)
{
lean_object* v_a_368_; lean_object* v___x_370_; uint8_t v_isShared_371_; uint8_t v_isSharedCheck_375_; 
lean_dec(v_a_355_);
v_a_368_ = lean_ctor_get(v___x_357_, 0);
v_isSharedCheck_375_ = !lean_is_exclusive(v___x_357_);
if (v_isSharedCheck_375_ == 0)
{
v___x_370_ = v___x_357_;
v_isShared_371_ = v_isSharedCheck_375_;
goto v_resetjp_369_;
}
else
{
lean_inc(v_a_368_);
lean_dec(v___x_357_);
v___x_370_ = lean_box(0);
v_isShared_371_ = v_isSharedCheck_375_;
goto v_resetjp_369_;
}
v_resetjp_369_:
{
lean_object* v___x_373_; 
if (v_isShared_371_ == 0)
{
lean_ctor_set_tag(v___x_370_, 0);
v___x_373_ = v___x_370_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v_a_368_);
v___x_373_ = v_reuseFailAlloc_374_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
return v___x_373_;
}
}
}
else
{
lean_object* v_a_376_; lean_object* v___x_378_; uint8_t v_isShared_379_; uint8_t v_isSharedCheck_384_; 
v_a_376_ = lean_ctor_get(v___x_357_, 0);
v_isSharedCheck_384_ = !lean_is_exclusive(v___x_357_);
if (v_isSharedCheck_384_ == 0)
{
v___x_378_ = v___x_357_;
v_isShared_379_ = v_isSharedCheck_384_;
goto v_resetjp_377_;
}
else
{
lean_inc(v_a_376_);
lean_dec(v___x_357_);
v___x_378_ = lean_box(0);
v_isShared_379_ = v_isSharedCheck_384_;
goto v_resetjp_377_;
}
v_resetjp_377_:
{
lean_object* v___x_380_; lean_object* v___x_382_; 
v___x_380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_380_, 0, v_a_355_);
lean_ctor_set(v___x_380_, 1, v_a_376_);
if (v_isShared_379_ == 0)
{
lean_ctor_set(v___x_378_, 0, v___x_380_);
v___x_382_ = v___x_378_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v___x_380_);
v___x_382_ = v_reuseFailAlloc_383_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
return v___x_382_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonWaitForDiagnosticsParams_toJson(lean_object* v_x_387_){
_start:
{
lean_object* v_uri_388_; lean_object* v_version_389_; lean_object* v___x_391_; uint8_t v_isShared_392_; uint8_t v_isSharedCheck_410_; 
v_uri_388_ = lean_ctor_get(v_x_387_, 0);
v_version_389_ = lean_ctor_get(v_x_387_, 1);
v_isSharedCheck_410_ = !lean_is_exclusive(v_x_387_);
if (v_isSharedCheck_410_ == 0)
{
v___x_391_ = v_x_387_;
v_isShared_392_ = v_isSharedCheck_410_;
goto v_resetjp_390_;
}
else
{
lean_inc(v_version_389_);
lean_inc(v_uri_388_);
lean_dec(v_x_387_);
v___x_391_ = lean_box(0);
v_isShared_392_ = v_isSharedCheck_410_;
goto v_resetjp_390_;
}
v_resetjp_390_:
{
lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_396_; 
v___x_393_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__0));
v___x_394_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_394_, 0, v_uri_388_);
if (v_isShared_392_ == 0)
{
lean_ctor_set(v___x_391_, 1, v___x_394_);
lean_ctor_set(v___x_391_, 0, v___x_393_);
v___x_396_ = v___x_391_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v___x_393_);
lean_ctor_set(v_reuseFailAlloc_409_, 1, v___x_394_);
v___x_396_ = v_reuseFailAlloc_409_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_397_ = lean_box(0);
v___x_398_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_398_, 0, v___x_396_);
lean_ctor_set(v___x_398_, 1, v___x_397_);
v___x_399_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__9));
v___x_400_ = l_Lean_JsonNumber_fromNat(v_version_389_);
v___x_401_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_401_, 0, v___x_400_);
v___x_402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_402_, 0, v___x_399_);
lean_ctor_set(v___x_402_, 1, v___x_401_);
v___x_403_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_403_, 0, v___x_402_);
lean_ctor_set(v___x_403_, 1, v___x_397_);
v___x_404_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_404_, 0, v___x_403_);
lean_ctor_set(v___x_404_, 1, v___x_397_);
v___x_405_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_405_, 0, v___x_398_);
lean_ctor_set(v___x_405_, 1, v___x_404_);
v___x_406_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0));
v___x_407_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_405_, v___x_406_);
v___x_408_ = l_Lean_Json_mkObj(v___x_407_);
lean_dec(v___x_407_);
return v___x_408_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonWaitForDiagnostics___lam__0(lean_object* v_x_415_){
_start:
{
lean_object* v___x_416_; 
v___x_416_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWaitForDiagnostics___lam__0___closed__0));
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonWaitForDiagnostics___lam__0___boxed(lean_object* v_x_417_){
_start:
{
lean_object* v_res_418_; 
v_res_418_ = l_Lean_Lsp_instFromJsonWaitForDiagnostics___lam__0(v_x_417_);
lean_dec(v_x_417_);
return v_res_418_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonWaitForDiagnostics___lam__0___closed__0(void){
_start:
{
lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_421_ = lean_box(0);
v___x_422_ = l_Lean_Json_mkObj(v___x_421_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonWaitForDiagnostics___lam__0(lean_object* v_x_423_){
_start:
{
lean_object* v___x_424_; 
v___x_424_ = lean_obj_once(&l_Lean_Lsp_instToJsonWaitForDiagnostics___lam__0___closed__0, &l_Lean_Lsp_instToJsonWaitForDiagnostics___lam__0___closed__0_once, _init_l_Lean_Lsp_instToJsonWaitForDiagnostics___lam__0___closed__0);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForILeansParams_fromJson_spec__0_spec__0(lean_object* v_x_429_){
_start:
{
if (lean_obj_tag(v_x_429_) == 0)
{
lean_object* v___x_430_; 
v___x_430_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForILeansParams_fromJson_spec__0_spec__0___closed__0));
return v___x_430_;
}
else
{
lean_object* v___x_431_; 
v___x_431_ = l_Lean_Json_getStr_x3f(v_x_429_);
if (lean_obj_tag(v___x_431_) == 0)
{
lean_object* v_a_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_439_; 
v_a_432_ = lean_ctor_get(v___x_431_, 0);
v_isSharedCheck_439_ = !lean_is_exclusive(v___x_431_);
if (v_isSharedCheck_439_ == 0)
{
v___x_434_ = v___x_431_;
v_isShared_435_ = v_isSharedCheck_439_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_a_432_);
lean_dec(v___x_431_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_439_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
lean_object* v___x_437_; 
if (v_isShared_435_ == 0)
{
v___x_437_ = v___x_434_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v_a_432_);
v___x_437_ = v_reuseFailAlloc_438_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
return v___x_437_;
}
}
}
else
{
lean_object* v_a_440_; lean_object* v___x_442_; uint8_t v_isShared_443_; uint8_t v_isSharedCheck_448_; 
v_a_440_ = lean_ctor_get(v___x_431_, 0);
v_isSharedCheck_448_ = !lean_is_exclusive(v___x_431_);
if (v_isSharedCheck_448_ == 0)
{
v___x_442_ = v___x_431_;
v_isShared_443_ = v_isSharedCheck_448_;
goto v_resetjp_441_;
}
else
{
lean_inc(v_a_440_);
lean_dec(v___x_431_);
v___x_442_ = lean_box(0);
v_isShared_443_ = v_isSharedCheck_448_;
goto v_resetjp_441_;
}
v_resetjp_441_:
{
lean_object* v___x_444_; lean_object* v___x_446_; 
v___x_444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_444_, 0, v_a_440_);
if (v_isShared_443_ == 0)
{
lean_ctor_set(v___x_442_, 0, v___x_444_);
v___x_446_ = v___x_442_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v___x_444_);
v___x_446_ = v_reuseFailAlloc_447_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
return v___x_446_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForILeansParams_fromJson_spec__0(lean_object* v_j_449_, lean_object* v_k_450_){
_start:
{
lean_object* v___x_451_; lean_object* v___x_452_; 
v___x_451_ = l_Lean_Json_getObjValD(v_j_449_, v_k_450_);
v___x_452_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForILeansParams_fromJson_spec__0_spec__0(v___x_451_);
return v___x_452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForILeansParams_fromJson_spec__0___boxed(lean_object* v_j_453_, lean_object* v_k_454_){
_start:
{
lean_object* v_res_455_; 
v_res_455_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForILeansParams_fromJson_spec__0(v_j_453_, v_k_454_);
lean_dec_ref(v_k_454_);
return v_res_455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForILeansParams_fromJson_spec__1_spec__2(lean_object* v_x_458_){
_start:
{
if (lean_obj_tag(v_x_458_) == 0)
{
lean_object* v___x_459_; 
v___x_459_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForILeansParams_fromJson_spec__1_spec__2___closed__0));
return v___x_459_;
}
else
{
lean_object* v___x_460_; 
v___x_460_ = l_Lean_Json_getNat_x3f(v_x_458_);
if (lean_obj_tag(v___x_460_) == 0)
{
lean_object* v_a_461_; lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_468_; 
v_a_461_ = lean_ctor_get(v___x_460_, 0);
v_isSharedCheck_468_ = !lean_is_exclusive(v___x_460_);
if (v_isSharedCheck_468_ == 0)
{
v___x_463_ = v___x_460_;
v_isShared_464_ = v_isSharedCheck_468_;
goto v_resetjp_462_;
}
else
{
lean_inc(v_a_461_);
lean_dec(v___x_460_);
v___x_463_ = lean_box(0);
v_isShared_464_ = v_isSharedCheck_468_;
goto v_resetjp_462_;
}
v_resetjp_462_:
{
lean_object* v___x_466_; 
if (v_isShared_464_ == 0)
{
v___x_466_ = v___x_463_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v_a_461_);
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
lean_object* v_a_469_; lean_object* v___x_471_; uint8_t v_isShared_472_; uint8_t v_isSharedCheck_477_; 
v_a_469_ = lean_ctor_get(v___x_460_, 0);
v_isSharedCheck_477_ = !lean_is_exclusive(v___x_460_);
if (v_isSharedCheck_477_ == 0)
{
v___x_471_ = v___x_460_;
v_isShared_472_ = v_isSharedCheck_477_;
goto v_resetjp_470_;
}
else
{
lean_inc(v_a_469_);
lean_dec(v___x_460_);
v___x_471_ = lean_box(0);
v_isShared_472_ = v_isSharedCheck_477_;
goto v_resetjp_470_;
}
v_resetjp_470_:
{
lean_object* v___x_473_; lean_object* v___x_475_; 
v___x_473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_473_, 0, v_a_469_);
if (v_isShared_472_ == 0)
{
lean_ctor_set(v___x_471_, 0, v___x_473_);
v___x_475_ = v___x_471_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_476_; 
v_reuseFailAlloc_476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_476_, 0, v___x_473_);
v___x_475_ = v_reuseFailAlloc_476_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
return v___x_475_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForILeansParams_fromJson_spec__1(lean_object* v_j_478_, lean_object* v_k_479_){
_start:
{
lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_480_ = l_Lean_Json_getObjValD(v_j_478_, v_k_479_);
v___x_481_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForILeansParams_fromJson_spec__1_spec__2(v___x_480_);
return v___x_481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForILeansParams_fromJson_spec__1___boxed(lean_object* v_j_482_, lean_object* v_k_483_){
_start:
{
lean_object* v_res_484_; 
v_res_484_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForILeansParams_fromJson_spec__1(v_j_482_, v_k_483_);
lean_dec_ref(v_k_483_);
return v_res_484_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__2(void){
_start:
{
uint8_t v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; 
v___x_490_ = 1;
v___x_491_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__1));
v___x_492_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_491_, v___x_490_);
return v___x_492_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__3(void){
_start:
{
lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_493_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6));
v___x_494_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__2, &l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__2);
v___x_495_ = lean_string_append(v___x_494_, v___x_493_);
return v___x_495_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__6(void){
_start:
{
uint8_t v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_499_ = 1;
v___x_500_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__5));
v___x_501_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_500_, v___x_499_);
return v___x_501_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__7(void){
_start:
{
lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; 
v___x_502_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__6, &l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__6);
v___x_503_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__3);
v___x_504_ = lean_string_append(v___x_503_, v___x_502_);
return v___x_504_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__8(void){
_start:
{
lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; 
v___x_505_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_506_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__7);
v___x_507_ = lean_string_append(v___x_506_, v___x_505_);
return v___x_507_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__11(void){
_start:
{
uint8_t v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; 
v___x_511_ = 1;
v___x_512_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__10));
v___x_513_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_512_, v___x_511_);
return v___x_513_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__12(void){
_start:
{
lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_514_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__11, &l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__11);
v___x_515_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__3);
v___x_516_ = lean_string_append(v___x_515_, v___x_514_);
return v___x_516_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__13(void){
_start:
{
lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; 
v___x_517_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_518_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__12, &l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__12);
v___x_519_ = lean_string_append(v___x_518_, v___x_517_);
return v___x_519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson(lean_object* v_json_520_){
_start:
{
lean_object* v___x_521_; lean_object* v___x_522_; 
v___x_521_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__0));
lean_inc(v_json_520_);
v___x_522_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForILeansParams_fromJson_spec__0(v_json_520_, v___x_521_);
if (lean_obj_tag(v___x_522_) == 0)
{
lean_object* v_a_523_; lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_532_; 
lean_dec(v_json_520_);
v_a_523_ = lean_ctor_get(v___x_522_, 0);
v_isSharedCheck_532_ = !lean_is_exclusive(v___x_522_);
if (v_isSharedCheck_532_ == 0)
{
v___x_525_ = v___x_522_;
v_isShared_526_ = v_isSharedCheck_532_;
goto v_resetjp_524_;
}
else
{
lean_inc(v_a_523_);
lean_dec(v___x_522_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_532_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_530_; 
v___x_527_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__8);
v___x_528_ = lean_string_append(v___x_527_, v_a_523_);
lean_dec(v_a_523_);
if (v_isShared_526_ == 0)
{
lean_ctor_set(v___x_525_, 0, v___x_528_);
v___x_530_ = v___x_525_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v___x_528_);
v___x_530_ = v_reuseFailAlloc_531_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
return v___x_530_;
}
}
}
else
{
if (lean_obj_tag(v___x_522_) == 0)
{
lean_object* v_a_533_; lean_object* v___x_535_; uint8_t v_isShared_536_; uint8_t v_isSharedCheck_540_; 
lean_dec(v_json_520_);
v_a_533_ = lean_ctor_get(v___x_522_, 0);
v_isSharedCheck_540_ = !lean_is_exclusive(v___x_522_);
if (v_isSharedCheck_540_ == 0)
{
v___x_535_ = v___x_522_;
v_isShared_536_ = v_isSharedCheck_540_;
goto v_resetjp_534_;
}
else
{
lean_inc(v_a_533_);
lean_dec(v___x_522_);
v___x_535_ = lean_box(0);
v_isShared_536_ = v_isSharedCheck_540_;
goto v_resetjp_534_;
}
v_resetjp_534_:
{
lean_object* v___x_538_; 
if (v_isShared_536_ == 0)
{
lean_ctor_set_tag(v___x_535_, 0);
v___x_538_ = v___x_535_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v_a_533_);
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
lean_object* v_a_541_; lean_object* v___x_542_; lean_object* v___x_543_; 
v_a_541_ = lean_ctor_get(v___x_522_, 0);
lean_inc(v_a_541_);
lean_dec_ref_known(v___x_522_, 1);
v___x_542_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__9));
v___x_543_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForILeansParams_fromJson_spec__1(v_json_520_, v___x_542_);
if (lean_obj_tag(v___x_543_) == 0)
{
lean_object* v_a_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_553_; 
lean_dec(v_a_541_);
v_a_544_ = lean_ctor_get(v___x_543_, 0);
v_isSharedCheck_553_ = !lean_is_exclusive(v___x_543_);
if (v_isSharedCheck_553_ == 0)
{
v___x_546_ = v___x_543_;
v_isShared_547_ = v_isSharedCheck_553_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_a_544_);
lean_dec(v___x_543_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_553_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_551_; 
v___x_548_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__13, &l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__13);
v___x_549_ = lean_string_append(v___x_548_, v_a_544_);
lean_dec(v_a_544_);
if (v_isShared_547_ == 0)
{
lean_ctor_set(v___x_546_, 0, v___x_549_);
v___x_551_ = v___x_546_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v___x_549_);
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
if (lean_obj_tag(v___x_543_) == 0)
{
lean_object* v_a_554_; lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_561_; 
lean_dec(v_a_541_);
v_a_554_ = lean_ctor_get(v___x_543_, 0);
v_isSharedCheck_561_ = !lean_is_exclusive(v___x_543_);
if (v_isSharedCheck_561_ == 0)
{
v___x_556_ = v___x_543_;
v_isShared_557_ = v_isSharedCheck_561_;
goto v_resetjp_555_;
}
else
{
lean_inc(v_a_554_);
lean_dec(v___x_543_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_561_;
goto v_resetjp_555_;
}
v_resetjp_555_:
{
lean_object* v___x_559_; 
if (v_isShared_557_ == 0)
{
lean_ctor_set_tag(v___x_556_, 0);
v___x_559_ = v___x_556_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_562_; lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_570_; 
v_a_562_ = lean_ctor_get(v___x_543_, 0);
v_isSharedCheck_570_ = !lean_is_exclusive(v___x_543_);
if (v_isSharedCheck_570_ == 0)
{
v___x_564_ = v___x_543_;
v_isShared_565_ = v_isSharedCheck_570_;
goto v_resetjp_563_;
}
else
{
lean_inc(v_a_562_);
lean_dec(v___x_543_);
v___x_564_ = lean_box(0);
v_isShared_565_ = v_isSharedCheck_570_;
goto v_resetjp_563_;
}
v_resetjp_563_:
{
lean_object* v___x_566_; lean_object* v___x_568_; 
v___x_566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_566_, 0, v_a_541_);
lean_ctor_set(v___x_566_, 1, v_a_562_);
if (v_isShared_565_ == 0)
{
lean_ctor_set(v___x_564_, 0, v___x_566_);
v___x_568_ = v___x_564_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v___x_566_);
v___x_568_ = v_reuseFailAlloc_569_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
return v___x_568_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonWaitForILeansParams_toJson_spec__0(lean_object* v_k_573_, lean_object* v_x_574_){
_start:
{
if (lean_obj_tag(v_x_574_) == 0)
{
lean_object* v___x_575_; 
lean_dec_ref(v_k_573_);
v___x_575_ = lean_box(0);
return v___x_575_;
}
else
{
lean_object* v_val_576_; lean_object* v___x_578_; uint8_t v_isShared_579_; uint8_t v_isSharedCheck_586_; 
v_val_576_ = lean_ctor_get(v_x_574_, 0);
v_isSharedCheck_586_ = !lean_is_exclusive(v_x_574_);
if (v_isSharedCheck_586_ == 0)
{
v___x_578_ = v_x_574_;
v_isShared_579_ = v_isSharedCheck_586_;
goto v_resetjp_577_;
}
else
{
lean_inc(v_val_576_);
lean_dec(v_x_574_);
v___x_578_ = lean_box(0);
v_isShared_579_ = v_isSharedCheck_586_;
goto v_resetjp_577_;
}
v_resetjp_577_:
{
lean_object* v___x_581_; 
if (v_isShared_579_ == 0)
{
lean_ctor_set_tag(v___x_578_, 3);
v___x_581_ = v___x_578_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v_val_576_);
v___x_581_ = v_reuseFailAlloc_585_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; 
v___x_582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_582_, 0, v_k_573_);
lean_ctor_set(v___x_582_, 1, v___x_581_);
v___x_583_ = lean_box(0);
v___x_584_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_584_, 0, v___x_582_);
lean_ctor_set(v___x_584_, 1, v___x_583_);
return v___x_584_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonWaitForILeansParams_toJson_spec__1(lean_object* v_k_587_, lean_object* v_x_588_){
_start:
{
if (lean_obj_tag(v_x_588_) == 0)
{
lean_object* v___x_589_; 
lean_dec_ref(v_k_587_);
v___x_589_ = lean_box(0);
return v___x_589_;
}
else
{
lean_object* v_val_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_601_; 
v_val_590_ = lean_ctor_get(v_x_588_, 0);
v_isSharedCheck_601_ = !lean_is_exclusive(v_x_588_);
if (v_isSharedCheck_601_ == 0)
{
v___x_592_ = v_x_588_;
v_isShared_593_ = v_isSharedCheck_601_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_val_590_);
lean_dec(v_x_588_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_601_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
lean_object* v___x_594_; lean_object* v___x_596_; 
v___x_594_ = l_Lean_JsonNumber_fromNat(v_val_590_);
if (v_isShared_593_ == 0)
{
lean_ctor_set_tag(v___x_592_, 2);
lean_ctor_set(v___x_592_, 0, v___x_594_);
v___x_596_ = v___x_592_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v___x_594_);
v___x_596_ = v_reuseFailAlloc_600_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_597_, 0, v_k_587_);
lean_ctor_set(v___x_597_, 1, v___x_596_);
v___x_598_ = lean_box(0);
v___x_599_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_599_, 0, v___x_597_);
lean_ctor_set(v___x_599_, 1, v___x_598_);
return v___x_599_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonWaitForILeansParams_toJson(lean_object* v_x_602_){
_start:
{
lean_object* v_uri_x3f_603_; lean_object* v_version_x3f_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_620_; 
v_uri_x3f_603_ = lean_ctor_get(v_x_602_, 0);
v_version_x3f_604_ = lean_ctor_get(v_x_602_, 1);
v_isSharedCheck_620_ = !lean_is_exclusive(v_x_602_);
if (v_isSharedCheck_620_ == 0)
{
v___x_606_ = v_x_602_;
v_isShared_607_ = v_isSharedCheck_620_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_version_x3f_604_);
lean_inc(v_uri_x3f_603_);
lean_dec(v_x_602_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_620_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_614_; 
v___x_608_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__0));
v___x_609_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonWaitForILeansParams_toJson_spec__0(v___x_608_, v_uri_x3f_603_);
v___x_610_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__9));
v___x_611_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonWaitForILeansParams_toJson_spec__1(v___x_610_, v_version_x3f_604_);
v___x_612_ = lean_box(0);
if (v_isShared_607_ == 0)
{
lean_ctor_set_tag(v___x_606_, 1);
lean_ctor_set(v___x_606_, 1, v___x_612_);
lean_ctor_set(v___x_606_, 0, v___x_611_);
v___x_614_ = v___x_606_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v___x_611_);
lean_ctor_set(v_reuseFailAlloc_619_, 1, v___x_612_);
v___x_614_ = v_reuseFailAlloc_619_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; 
v___x_615_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_615_, 0, v___x_609_);
lean_ctor_set(v___x_615_, 1, v___x_614_);
v___x_616_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0));
v___x_617_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_615_, v___x_616_);
v___x_618_ = l_Lean_Json_mkObj(v___x_617_);
lean_dec(v___x_617_);
return v___x_618_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonWaitForILeans_fromJson___redArg(){
_start:
{
lean_object* v___x_626_; 
v___x_626_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWaitForILeans_fromJson___redArg___closed__0));
return v___x_626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonWaitForILeans_fromJson___redArg___boxed(lean_object* v___dummy_627_){
_start:
{
lean_object* v_res_628_; 
v_res_628_ = l_Lean_Lsp_instFromJsonWaitForILeans_fromJson___redArg();
return v_res_628_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWaitForILeans_fromJson___closed__0(void){
_start:
{
lean_object* v___x_629_; 
v___x_629_ = l_Lean_Lsp_instFromJsonWaitForILeans_fromJson___redArg();
return v___x_629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonWaitForILeans_fromJson(lean_object* v_json_630_){
_start:
{
lean_object* v___x_631_; 
v___x_631_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWaitForILeans_fromJson___closed__0, &l_Lean_Lsp_instFromJsonWaitForILeans_fromJson___closed__0_once, _init_l_Lean_Lsp_instFromJsonWaitForILeans_fromJson___closed__0);
return v___x_631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonWaitForILeans_fromJson___boxed(lean_object* v_json_632_){
_start:
{
lean_object* v_res_633_; 
v_res_633_ = l_Lean_Lsp_instFromJsonWaitForILeans_fromJson(v_json_632_);
lean_dec(v_json_632_);
return v_res_633_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonWaitForILeans_toJson___redArg___closed__0(void){
_start:
{
lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; 
v___x_636_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0));
v___x_637_ = lean_box(0);
v___x_638_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_637_, v___x_636_);
return v___x_638_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonWaitForILeans_toJson___redArg___closed__1(void){
_start:
{
lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_639_ = lean_obj_once(&l_Lean_Lsp_instToJsonWaitForILeans_toJson___redArg___closed__0, &l_Lean_Lsp_instToJsonWaitForILeans_toJson___redArg___closed__0_once, _init_l_Lean_Lsp_instToJsonWaitForILeans_toJson___redArg___closed__0);
v___x_640_ = l_Lean_Json_mkObj(v___x_639_);
return v___x_640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonWaitForILeans_toJson___redArg(){
_start:
{
lean_object* v___x_642_; 
v___x_642_ = lean_obj_once(&l_Lean_Lsp_instToJsonWaitForILeans_toJson___redArg___closed__1, &l_Lean_Lsp_instToJsonWaitForILeans_toJson___redArg___closed__1_once, _init_l_Lean_Lsp_instToJsonWaitForILeans_toJson___redArg___closed__1);
return v___x_642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonWaitForILeans_toJson___redArg___boxed(lean_object* v___dummy_643_){
_start:
{
lean_object* v_res_644_; 
v_res_644_ = l_Lean_Lsp_instToJsonWaitForILeans_toJson___redArg();
return v_res_644_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonWaitForILeans_toJson___closed__0(void){
_start:
{
lean_object* v___x_645_; 
v___x_645_ = l_Lean_Lsp_instToJsonWaitForILeans_toJson___redArg();
return v___x_645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonWaitForILeans_toJson(lean_object* v_x_646_){
_start:
{
lean_object* v___x_647_; 
v___x_647_ = lean_obj_once(&l_Lean_Lsp_instToJsonWaitForILeans_toJson___closed__0, &l_Lean_Lsp_instToJsonWaitForILeans_toJson___closed__0_once, _init_l_Lean_Lsp_instToJsonWaitForILeans_toJson___closed__0);
return v___x_647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanFileProgressKind_ctorIdx___impl(uint8_t v_x_650_){
_start:
{
lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_651_ = lean_box(v_x_650_);
v___x_652_ = lean_obj_tag_nat(v___x_651_);
lean_dec(v___x_651_);
return v___x_652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanFileProgressKind_ctorIdx___impl___boxed(lean_object* v_x_653_){
_start:
{
uint8_t v_x_4__boxed_654_; lean_object* v_res_655_; 
v_x_4__boxed_654_ = lean_unbox(v_x_653_);
v_res_655_ = l_Lean_Lsp_LeanFileProgressKind_ctorIdx___impl(v_x_4__boxed_654_);
return v_res_655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanFileProgressKind_ctorElim___redArg(lean_object* v_k_656_){
_start:
{
lean_inc(v_k_656_);
return v_k_656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanFileProgressKind_ctorElim___redArg___boxed(lean_object* v_k_657_){
_start:
{
lean_object* v_res_658_; 
v_res_658_ = l_Lean_Lsp_LeanFileProgressKind_ctorElim___redArg(v_k_657_);
lean_dec(v_k_657_);
return v_res_658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanFileProgressKind_ctorElim(lean_object* v_motive_659_, lean_object* v_ctorIdx_660_, uint8_t v_t_661_, lean_object* v_h_662_, lean_object* v_k_663_){
_start:
{
lean_inc(v_k_663_);
return v_k_663_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanFileProgressKind_ctorElim___boxed(lean_object* v_motive_664_, lean_object* v_ctorIdx_665_, lean_object* v_t_666_, lean_object* v_h_667_, lean_object* v_k_668_){
_start:
{
uint8_t v_t_boxed_669_; lean_object* v_res_670_; 
v_t_boxed_669_ = lean_unbox(v_t_666_);
v_res_670_ = l_Lean_Lsp_LeanFileProgressKind_ctorElim(v_motive_664_, v_ctorIdx_665_, v_t_boxed_669_, v_h_667_, v_k_668_);
lean_dec(v_k_668_);
lean_dec(v_ctorIdx_665_);
return v_res_670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanFileProgressKind_processing_elim___redArg(lean_object* v_processing_671_){
_start:
{
lean_inc(v_processing_671_);
return v_processing_671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanFileProgressKind_processing_elim___redArg___boxed(lean_object* v_processing_672_){
_start:
{
lean_object* v_res_673_; 
v_res_673_ = l_Lean_Lsp_LeanFileProgressKind_processing_elim___redArg(v_processing_672_);
lean_dec(v_processing_672_);
return v_res_673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanFileProgressKind_processing_elim(lean_object* v_motive_674_, uint8_t v_t_675_, lean_object* v_h_676_, lean_object* v_processing_677_){
_start:
{
lean_inc(v_processing_677_);
return v_processing_677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanFileProgressKind_processing_elim___boxed(lean_object* v_motive_678_, lean_object* v_t_679_, lean_object* v_h_680_, lean_object* v_processing_681_){
_start:
{
uint8_t v_t_boxed_682_; lean_object* v_res_683_; 
v_t_boxed_682_ = lean_unbox(v_t_679_);
v_res_683_ = l_Lean_Lsp_LeanFileProgressKind_processing_elim(v_motive_678_, v_t_boxed_682_, v_h_680_, v_processing_681_);
lean_dec(v_processing_681_);
return v_res_683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanFileProgressKind_fatalError_elim___redArg(lean_object* v_fatalError_684_){
_start:
{
lean_inc(v_fatalError_684_);
return v_fatalError_684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanFileProgressKind_fatalError_elim___redArg___boxed(lean_object* v_fatalError_685_){
_start:
{
lean_object* v_res_686_; 
v_res_686_ = l_Lean_Lsp_LeanFileProgressKind_fatalError_elim___redArg(v_fatalError_685_);
lean_dec(v_fatalError_685_);
return v_res_686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanFileProgressKind_fatalError_elim(lean_object* v_motive_687_, uint8_t v_t_688_, lean_object* v_h_689_, lean_object* v_fatalError_690_){
_start:
{
lean_inc(v_fatalError_690_);
return v_fatalError_690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanFileProgressKind_fatalError_elim___boxed(lean_object* v_motive_691_, lean_object* v_t_692_, lean_object* v_h_693_, lean_object* v_fatalError_694_){
_start:
{
uint8_t v_t_boxed_695_; lean_object* v_res_696_; 
v_t_boxed_695_ = lean_unbox(v_t_692_);
v_res_696_ = l_Lean_Lsp_LeanFileProgressKind_fatalError_elim(v_motive_691_, v_t_boxed_695_, v_h_693_, v_fatalError_694_);
lean_dec(v_fatalError_694_);
return v_res_696_;
}
}
static uint8_t _init_l_Lean_Lsp_instInhabitedLeanFileProgressKind_default(void){
_start:
{
uint8_t v___x_697_; 
v___x_697_ = 0;
return v___x_697_;
}
}
static uint8_t _init_l_Lean_Lsp_instInhabitedLeanFileProgressKind(void){
_start:
{
uint8_t v___x_698_; 
v___x_698_ = 0;
return v___x_698_;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_instBEqLeanFileProgressKind_beq(uint8_t v_x_699_, uint8_t v_y_700_){
_start:
{
lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; uint8_t v___x_705_; 
v___x_701_ = lean_box(v_x_699_);
v___x_702_ = lean_obj_tag_nat(v___x_701_);
lean_dec(v___x_701_);
v___x_703_ = lean_box(v_y_700_);
v___x_704_ = lean_obj_tag_nat(v___x_703_);
lean_dec(v___x_703_);
v___x_705_ = lean_nat_dec_eq(v___x_702_, v___x_704_);
return v___x_705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqLeanFileProgressKind_beq___boxed(lean_object* v_x_706_, lean_object* v_y_707_){
_start:
{
uint8_t v_x_24__boxed_708_; uint8_t v_y_25__boxed_709_; uint8_t v_res_710_; lean_object* v_r_711_; 
v_x_24__boxed_708_ = lean_unbox(v_x_706_);
v_y_25__boxed_709_ = lean_unbox(v_y_707_);
v_res_710_ = l_Lean_Lsp_instBEqLeanFileProgressKind_beq(v_x_24__boxed_708_, v_y_25__boxed_709_);
v_r_711_ = lean_box(v_res_710_);
return v_r_711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanFileProgressKind___lam__0(lean_object* v_j_722_){
_start:
{
lean_object* v___x_731_; 
lean_inc(v_j_722_);
v___x_731_ = l_Lean_Json_getNat_x3f(v_j_722_);
if (lean_obj_tag(v___x_731_) == 1)
{
lean_object* v_a_732_; lean_object* v___x_733_; uint8_t v___x_734_; 
v_a_732_ = lean_ctor_get(v___x_731_, 0);
lean_inc(v_a_732_);
lean_dec_ref_known(v___x_731_, 1);
v___x_733_ = lean_unsigned_to_nat(1u);
v___x_734_ = lean_nat_dec_eq(v_a_732_, v___x_733_);
if (v___x_734_ == 0)
{
lean_object* v___x_735_; uint8_t v___x_736_; 
v___x_735_ = lean_unsigned_to_nat(2u);
v___x_736_ = lean_nat_dec_eq(v_a_732_, v___x_735_);
lean_dec(v_a_732_);
if (v___x_736_ == 0)
{
goto v___jp_723_;
}
else
{
lean_object* v___x_737_; 
lean_dec(v_j_722_);
v___x_737_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressKind___lam__0___closed__2));
return v___x_737_;
}
}
else
{
lean_object* v___x_738_; 
lean_dec(v_a_732_);
lean_dec(v_j_722_);
v___x_738_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressKind___lam__0___closed__3));
return v___x_738_;
}
}
else
{
lean_dec_ref(v___x_731_);
goto v___jp_723_;
}
v___jp_723_:
{
lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; 
v___x_724_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressKind___lam__0___closed__0));
v___x_725_ = lean_unsigned_to_nat(80u);
v___x_726_ = l_Lean_Json_pretty(v_j_722_, v___x_725_);
v___x_727_ = lean_string_append(v___x_724_, v___x_726_);
lean_dec_ref(v___x_726_);
v___x_728_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressKind___lam__0___closed__1));
v___x_729_ = lean_string_append(v___x_727_, v___x_728_);
v___x_730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_730_, 0, v___x_729_);
return v___x_730_;
}
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__0(void){
_start:
{
lean_object* v___x_741_; lean_object* v___x_742_; 
v___x_741_ = lean_unsigned_to_nat(1u);
v___x_742_ = l_Lean_JsonNumber_fromNat(v___x_741_);
return v___x_742_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__1(void){
_start:
{
lean_object* v___x_743_; lean_object* v___x_744_; 
v___x_743_ = lean_obj_once(&l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__0, &l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__0_once, _init_l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__0);
v___x_744_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_744_, 0, v___x_743_);
return v___x_744_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__2(void){
_start:
{
lean_object* v___x_745_; lean_object* v___x_746_; 
v___x_745_ = lean_unsigned_to_nat(2u);
v___x_746_ = l_Lean_JsonNumber_fromNat(v___x_745_);
return v___x_746_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__3(void){
_start:
{
lean_object* v___x_747_; lean_object* v___x_748_; 
v___x_747_ = lean_obj_once(&l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__2, &l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__2_once, _init_l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__2);
v___x_748_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_748_, 0, v___x_747_);
return v___x_748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0(uint8_t v_x_749_){
_start:
{
if (v_x_749_ == 0)
{
lean_object* v___x_750_; 
v___x_750_ = lean_obj_once(&l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__1, &l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__1_once, _init_l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__1);
return v___x_750_;
}
else
{
lean_object* v___x_751_; 
v___x_751_ = lean_obj_once(&l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__3, &l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__3_once, _init_l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__3);
return v___x_751_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___boxed(lean_object* v_x_752_){
_start:
{
uint8_t v_x_56__boxed_753_; lean_object* v_res_754_; 
v_x_56__boxed_753_ = lean_unbox(v_x_752_);
v_res_754_ = l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0(v_x_56__boxed_753_);
return v_res_754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson_spec__0(lean_object* v_j_757_, lean_object* v_k_758_){
_start:
{
lean_object* v___x_759_; lean_object* v___x_760_; 
v___x_759_ = l_Lean_Json_getObjValD(v_j_757_, v_k_758_);
v___x_760_ = l_Lean_Lsp_instFromJsonRange_fromJson(v___x_759_);
return v___x_760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson_spec__0___boxed(lean_object* v_j_761_, lean_object* v_k_762_){
_start:
{
lean_object* v_res_763_; 
v_res_763_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson_spec__0(v_j_761_, v_k_762_);
lean_dec_ref(v_k_762_);
return v_res_763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson_spec__1(lean_object* v_j_764_, lean_object* v_k_765_){
_start:
{
lean_object* v___x_766_; lean_object* v___x_775_; 
v___x_766_ = l_Lean_Json_getObjValD(v_j_764_, v_k_765_);
lean_inc(v___x_766_);
v___x_775_ = l_Lean_Json_getNat_x3f(v___x_766_);
if (lean_obj_tag(v___x_775_) == 1)
{
lean_object* v_a_776_; lean_object* v___x_777_; uint8_t v___x_778_; 
v_a_776_ = lean_ctor_get(v___x_775_, 0);
lean_inc(v_a_776_);
lean_dec_ref_known(v___x_775_, 1);
v___x_777_ = lean_unsigned_to_nat(1u);
v___x_778_ = lean_nat_dec_eq(v_a_776_, v___x_777_);
if (v___x_778_ == 0)
{
lean_object* v___x_779_; uint8_t v___x_780_; 
v___x_779_ = lean_unsigned_to_nat(2u);
v___x_780_ = lean_nat_dec_eq(v_a_776_, v___x_779_);
lean_dec(v_a_776_);
if (v___x_780_ == 0)
{
goto v___jp_767_;
}
else
{
lean_object* v___x_781_; 
lean_dec(v___x_766_);
v___x_781_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressKind___lam__0___closed__2));
return v___x_781_;
}
}
else
{
lean_object* v___x_782_; 
lean_dec(v_a_776_);
lean_dec(v___x_766_);
v___x_782_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressKind___lam__0___closed__3));
return v___x_782_;
}
}
else
{
lean_dec_ref(v___x_775_);
goto v___jp_767_;
}
v___jp_767_:
{
lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; 
v___x_768_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressKind___lam__0___closed__0));
v___x_769_ = lean_unsigned_to_nat(80u);
v___x_770_ = l_Lean_Json_pretty(v___x_766_, v___x_769_);
v___x_771_ = lean_string_append(v___x_768_, v___x_770_);
lean_dec_ref(v___x_770_);
v___x_772_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressKind___lam__0___closed__1));
v___x_773_ = lean_string_append(v___x_771_, v___x_772_);
v___x_774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_774_, 0, v___x_773_);
return v___x_774_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson_spec__1___boxed(lean_object* v_j_783_, lean_object* v_k_784_){
_start:
{
lean_object* v_res_785_; 
v_res_785_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson_spec__1(v_j_783_, v_k_784_);
lean_dec_ref(v_k_784_);
return v_res_785_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__3(void){
_start:
{
uint8_t v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; 
v___x_792_ = 1;
v___x_793_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__2));
v___x_794_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_793_, v___x_792_);
return v___x_794_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__4(void){
_start:
{
lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; 
v___x_795_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6));
v___x_796_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__3);
v___x_797_ = lean_string_append(v___x_796_, v___x_795_);
return v___x_797_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__6(void){
_start:
{
uint8_t v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; 
v___x_800_ = 1;
v___x_801_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__5));
v___x_802_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_801_, v___x_800_);
return v___x_802_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__7(void){
_start:
{
lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; 
v___x_803_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__6);
v___x_804_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__4);
v___x_805_ = lean_string_append(v___x_804_, v___x_803_);
return v___x_805_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__8(void){
_start:
{
lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; 
v___x_806_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_807_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__7);
v___x_808_ = lean_string_append(v___x_807_, v___x_806_);
return v___x_808_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__11(void){
_start:
{
uint8_t v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; 
v___x_812_ = 1;
v___x_813_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__10));
v___x_814_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_813_, v___x_812_);
return v___x_814_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__12(void){
_start:
{
lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; 
v___x_815_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__11, &l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__11);
v___x_816_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__4);
v___x_817_ = lean_string_append(v___x_816_, v___x_815_);
return v___x_817_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__13(void){
_start:
{
lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; 
v___x_818_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_819_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__12, &l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__12);
v___x_820_ = lean_string_append(v___x_819_, v___x_818_);
return v___x_820_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson(lean_object* v_json_821_){
_start:
{
lean_object* v___x_822_; lean_object* v___x_823_; 
v___x_822_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__0));
lean_inc(v_json_821_);
v___x_823_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson_spec__0(v_json_821_, v___x_822_);
if (lean_obj_tag(v___x_823_) == 0)
{
lean_object* v_a_824_; lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_833_; 
lean_dec(v_json_821_);
v_a_824_ = lean_ctor_get(v___x_823_, 0);
v_isSharedCheck_833_ = !lean_is_exclusive(v___x_823_);
if (v_isSharedCheck_833_ == 0)
{
v___x_826_ = v___x_823_;
v_isShared_827_ = v_isSharedCheck_833_;
goto v_resetjp_825_;
}
else
{
lean_inc(v_a_824_);
lean_dec(v___x_823_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_833_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_831_; 
v___x_828_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__8);
v___x_829_ = lean_string_append(v___x_828_, v_a_824_);
lean_dec(v_a_824_);
if (v_isShared_827_ == 0)
{
lean_ctor_set(v___x_826_, 0, v___x_829_);
v___x_831_ = v___x_826_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v___x_829_);
v___x_831_ = v_reuseFailAlloc_832_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
return v___x_831_;
}
}
}
else
{
if (lean_obj_tag(v___x_823_) == 0)
{
lean_object* v_a_834_; lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_841_; 
lean_dec(v_json_821_);
v_a_834_ = lean_ctor_get(v___x_823_, 0);
v_isSharedCheck_841_ = !lean_is_exclusive(v___x_823_);
if (v_isSharedCheck_841_ == 0)
{
v___x_836_ = v___x_823_;
v_isShared_837_ = v_isSharedCheck_841_;
goto v_resetjp_835_;
}
else
{
lean_inc(v_a_834_);
lean_dec(v___x_823_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_841_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
lean_object* v___x_839_; 
if (v_isShared_837_ == 0)
{
lean_ctor_set_tag(v___x_836_, 0);
v___x_839_ = v___x_836_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v_a_834_);
v___x_839_ = v_reuseFailAlloc_840_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
return v___x_839_;
}
}
}
else
{
lean_object* v_a_842_; lean_object* v___x_843_; lean_object* v___x_844_; 
v_a_842_ = lean_ctor_get(v___x_823_, 0);
lean_inc(v_a_842_);
lean_dec_ref_known(v___x_823_, 1);
v___x_843_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__9));
v___x_844_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson_spec__1(v_json_821_, v___x_843_);
if (lean_obj_tag(v___x_844_) == 0)
{
lean_object* v_a_845_; lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_854_; 
lean_dec(v_a_842_);
v_a_845_ = lean_ctor_get(v___x_844_, 0);
v_isSharedCheck_854_ = !lean_is_exclusive(v___x_844_);
if (v_isSharedCheck_854_ == 0)
{
v___x_847_ = v___x_844_;
v_isShared_848_ = v_isSharedCheck_854_;
goto v_resetjp_846_;
}
else
{
lean_inc(v_a_845_);
lean_dec(v___x_844_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_854_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_852_; 
v___x_849_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__13, &l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__13);
v___x_850_ = lean_string_append(v___x_849_, v_a_845_);
lean_dec(v_a_845_);
if (v_isShared_848_ == 0)
{
lean_ctor_set(v___x_847_, 0, v___x_850_);
v___x_852_ = v___x_847_;
goto v_reusejp_851_;
}
else
{
lean_object* v_reuseFailAlloc_853_; 
v_reuseFailAlloc_853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_853_, 0, v___x_850_);
v___x_852_ = v_reuseFailAlloc_853_;
goto v_reusejp_851_;
}
v_reusejp_851_:
{
return v___x_852_;
}
}
}
else
{
if (lean_obj_tag(v___x_844_) == 0)
{
lean_object* v_a_855_; lean_object* v___x_857_; uint8_t v_isShared_858_; uint8_t v_isSharedCheck_862_; 
lean_dec(v_a_842_);
v_a_855_ = lean_ctor_get(v___x_844_, 0);
v_isSharedCheck_862_ = !lean_is_exclusive(v___x_844_);
if (v_isSharedCheck_862_ == 0)
{
v___x_857_ = v___x_844_;
v_isShared_858_ = v_isSharedCheck_862_;
goto v_resetjp_856_;
}
else
{
lean_inc(v_a_855_);
lean_dec(v___x_844_);
v___x_857_ = lean_box(0);
v_isShared_858_ = v_isSharedCheck_862_;
goto v_resetjp_856_;
}
v_resetjp_856_:
{
lean_object* v___x_860_; 
if (v_isShared_858_ == 0)
{
lean_ctor_set_tag(v___x_857_, 0);
v___x_860_ = v___x_857_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v_a_855_);
v___x_860_ = v_reuseFailAlloc_861_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
return v___x_860_;
}
}
}
else
{
lean_object* v_a_863_; lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_872_; 
v_a_863_ = lean_ctor_get(v___x_844_, 0);
v_isSharedCheck_872_ = !lean_is_exclusive(v___x_844_);
if (v_isSharedCheck_872_ == 0)
{
v___x_865_ = v___x_844_;
v_isShared_866_ = v_isSharedCheck_872_;
goto v_resetjp_864_;
}
else
{
lean_inc(v_a_863_);
lean_dec(v___x_844_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_872_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
lean_object* v___x_867_; uint8_t v___x_868_; lean_object* v___x_870_; 
v___x_867_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_867_, 0, v_a_842_);
v___x_868_ = lean_unbox(v_a_863_);
lean_dec(v_a_863_);
lean_ctor_set_uint8(v___x_867_, sizeof(void*)*1, v___x_868_);
if (v_isShared_866_ == 0)
{
lean_ctor_set(v___x_865_, 0, v___x_867_);
v___x_870_ = v___x_865_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v___x_867_);
v___x_870_ = v_reuseFailAlloc_871_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
return v___x_870_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanFileProgressProcessingInfo_toJson(lean_object* v_x_875_){
_start:
{
lean_object* v_range_876_; uint8_t v_kind_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___y_885_; 
v_range_876_ = lean_ctor_get(v_x_875_, 0);
lean_inc_ref(v_range_876_);
v_kind_877_ = lean_ctor_get_uint8(v_x_875_, sizeof(void*)*1);
lean_dec_ref(v_x_875_);
v___x_878_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__0));
v___x_879_ = l_Lean_Lsp_instToJsonRange_toJson(v_range_876_);
v___x_880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_880_, 0, v___x_878_);
lean_ctor_set(v___x_880_, 1, v___x_879_);
v___x_881_ = lean_box(0);
v___x_882_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_882_, 0, v___x_880_);
lean_ctor_set(v___x_882_, 1, v___x_881_);
v___x_883_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__9));
if (v_kind_877_ == 0)
{
lean_object* v___x_893_; 
v___x_893_ = lean_obj_once(&l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__1, &l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__1_once, _init_l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__1);
v___y_885_ = v___x_893_;
goto v___jp_884_;
}
else
{
lean_object* v___x_894_; 
v___x_894_ = lean_obj_once(&l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__3, &l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__3_once, _init_l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__3);
v___y_885_ = v___x_894_;
goto v___jp_884_;
}
v___jp_884_:
{
lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; 
lean_inc(v___y_885_);
v___x_886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_886_, 0, v___x_883_);
lean_ctor_set(v___x_886_, 1, v___y_885_);
v___x_887_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_887_, 0, v___x_886_);
lean_ctor_set(v___x_887_, 1, v___x_881_);
v___x_888_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_888_, 0, v___x_887_);
lean_ctor_set(v___x_888_, 1, v___x_881_);
v___x_889_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_889_, 0, v___x_882_);
lean_ctor_set(v___x_889_, 1, v___x_888_);
v___x_890_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0));
v___x_891_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_889_, v___x_890_);
v___x_892_ = l_Lean_Json_mkObj(v___x_891_);
lean_dec(v___x_891_);
return v___x_892_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__0(lean_object* v_j_897_, lean_object* v_k_898_){
_start:
{
lean_object* v___x_899_; lean_object* v___x_900_; 
v___x_899_ = l_Lean_Json_getObjValD(v_j_897_, v_k_898_);
v___x_900_ = l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson(v___x_899_);
return v___x_900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__0___boxed(lean_object* v_j_901_, lean_object* v_k_902_){
_start:
{
lean_object* v_res_903_; 
v_res_903_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__0(v_j_901_, v_k_902_);
lean_dec_ref(v_k_902_);
return v_res_903_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__1_spec__1_spec__2(size_t v_sz_904_, size_t v_i_905_, lean_object* v_bs_906_){
_start:
{
uint8_t v___x_907_; 
v___x_907_ = lean_usize_dec_lt(v_i_905_, v_sz_904_);
if (v___x_907_ == 0)
{
lean_object* v___x_908_; 
v___x_908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_908_, 0, v_bs_906_);
return v___x_908_;
}
else
{
lean_object* v_v_909_; lean_object* v___x_910_; 
v_v_909_ = lean_array_uget_borrowed(v_bs_906_, v_i_905_);
lean_inc(v_v_909_);
v___x_910_ = l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson(v_v_909_);
if (lean_obj_tag(v___x_910_) == 0)
{
lean_object* v_a_911_; lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_918_; 
lean_dec_ref(v_bs_906_);
v_a_911_ = lean_ctor_get(v___x_910_, 0);
v_isSharedCheck_918_ = !lean_is_exclusive(v___x_910_);
if (v_isSharedCheck_918_ == 0)
{
v___x_913_ = v___x_910_;
v_isShared_914_ = v_isSharedCheck_918_;
goto v_resetjp_912_;
}
else
{
lean_inc(v_a_911_);
lean_dec(v___x_910_);
v___x_913_ = lean_box(0);
v_isShared_914_ = v_isSharedCheck_918_;
goto v_resetjp_912_;
}
v_resetjp_912_:
{
lean_object* v___x_916_; 
if (v_isShared_914_ == 0)
{
v___x_916_ = v___x_913_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v_a_911_);
v___x_916_ = v_reuseFailAlloc_917_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
return v___x_916_;
}
}
}
else
{
lean_object* v_a_919_; lean_object* v___x_920_; lean_object* v_bs_x27_921_; size_t v___x_922_; size_t v___x_923_; lean_object* v___x_924_; 
v_a_919_ = lean_ctor_get(v___x_910_, 0);
lean_inc(v_a_919_);
lean_dec_ref_known(v___x_910_, 1);
v___x_920_ = lean_unsigned_to_nat(0u);
v_bs_x27_921_ = lean_array_uset(v_bs_906_, v_i_905_, v___x_920_);
v___x_922_ = ((size_t)1ULL);
v___x_923_ = lean_usize_add(v_i_905_, v___x_922_);
v___x_924_ = lean_array_uset(v_bs_x27_921_, v_i_905_, v_a_919_);
v_i_905_ = v___x_923_;
v_bs_906_ = v___x_924_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__1_spec__1_spec__2___boxed(lean_object* v_sz_926_, lean_object* v_i_927_, lean_object* v_bs_928_){
_start:
{
size_t v_sz_boxed_929_; size_t v_i_boxed_930_; lean_object* v_res_931_; 
v_sz_boxed_929_ = lean_unbox_usize(v_sz_926_);
lean_dec(v_sz_926_);
v_i_boxed_930_ = lean_unbox_usize(v_i_927_);
lean_dec(v_i_927_);
v_res_931_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__1_spec__1_spec__2(v_sz_boxed_929_, v_i_boxed_930_, v_bs_928_);
return v_res_931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__1_spec__1(lean_object* v_x_933_){
_start:
{
if (lean_obj_tag(v_x_933_) == 4)
{
lean_object* v_elems_934_; size_t v_sz_935_; size_t v___x_936_; lean_object* v___x_937_; 
v_elems_934_ = lean_ctor_get(v_x_933_, 0);
lean_inc_ref(v_elems_934_);
lean_dec_ref_known(v_x_933_, 1);
v_sz_935_ = lean_array_size(v_elems_934_);
v___x_936_ = ((size_t)0ULL);
v___x_937_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__1_spec__1_spec__2(v_sz_935_, v___x_936_, v_elems_934_);
return v___x_937_;
}
else
{
lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; 
v___x_938_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__1_spec__1___closed__0));
v___x_939_ = lean_unsigned_to_nat(80u);
v___x_940_ = l_Lean_Json_pretty(v_x_933_, v___x_939_);
v___x_941_ = lean_string_append(v___x_938_, v___x_940_);
lean_dec_ref(v___x_940_);
v___x_942_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressKind___lam__0___closed__1));
v___x_943_ = lean_string_append(v___x_941_, v___x_942_);
v___x_944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_944_, 0, v___x_943_);
return v___x_944_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__1(lean_object* v_j_945_, lean_object* v_k_946_){
_start:
{
lean_object* v___x_947_; lean_object* v___x_948_; 
v___x_947_ = l_Lean_Json_getObjValD(v_j_945_, v_k_946_);
v___x_948_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__1_spec__1(v___x_947_);
return v___x_948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__1___boxed(lean_object* v_j_949_, lean_object* v_k_950_){
_start:
{
lean_object* v_res_951_; 
v_res_951_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__1(v_j_949_, v_k_950_);
lean_dec_ref(v_k_950_);
return v_res_951_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__2(void){
_start:
{
uint8_t v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; 
v___x_957_ = 1;
v___x_958_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__1));
v___x_959_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_958_, v___x_957_);
return v___x_959_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__3(void){
_start:
{
lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; 
v___x_960_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6));
v___x_961_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__2, &l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__2);
v___x_962_ = lean_string_append(v___x_961_, v___x_960_);
return v___x_962_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; 
v___x_963_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9, &l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9);
v___x_964_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__3);
v___x_965_ = lean_string_append(v___x_964_, v___x_963_);
return v___x_965_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__5(void){
_start:
{
lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; 
v___x_966_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_967_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__4);
v___x_968_ = lean_string_append(v___x_967_, v___x_966_);
return v___x_968_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__8(void){
_start:
{
uint8_t v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; 
v___x_972_ = 1;
v___x_973_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__7));
v___x_974_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_973_, v___x_972_);
return v___x_974_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__9(void){
_start:
{
lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; 
v___x_975_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__8);
v___x_976_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__3);
v___x_977_ = lean_string_append(v___x_976_, v___x_975_);
return v___x_977_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__10(void){
_start:
{
lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; 
v___x_978_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_979_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__9, &l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__9);
v___x_980_ = lean_string_append(v___x_979_, v___x_978_);
return v___x_980_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson(lean_object* v_json_981_){
_start:
{
lean_object* v___x_982_; lean_object* v___x_983_; 
v___x_982_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__0));
lean_inc(v_json_981_);
v___x_983_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__0(v_json_981_, v___x_982_);
if (lean_obj_tag(v___x_983_) == 0)
{
lean_object* v_a_984_; lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_993_; 
lean_dec(v_json_981_);
v_a_984_ = lean_ctor_get(v___x_983_, 0);
v_isSharedCheck_993_ = !lean_is_exclusive(v___x_983_);
if (v_isSharedCheck_993_ == 0)
{
v___x_986_ = v___x_983_;
v_isShared_987_ = v_isSharedCheck_993_;
goto v_resetjp_985_;
}
else
{
lean_inc(v_a_984_);
lean_dec(v___x_983_);
v___x_986_ = lean_box(0);
v_isShared_987_ = v_isSharedCheck_993_;
goto v_resetjp_985_;
}
v_resetjp_985_:
{
lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_991_; 
v___x_988_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__5, &l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__5);
v___x_989_ = lean_string_append(v___x_988_, v_a_984_);
lean_dec(v_a_984_);
if (v_isShared_987_ == 0)
{
lean_ctor_set(v___x_986_, 0, v___x_989_);
v___x_991_ = v___x_986_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v___x_989_);
v___x_991_ = v_reuseFailAlloc_992_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
return v___x_991_;
}
}
}
else
{
if (lean_obj_tag(v___x_983_) == 0)
{
lean_object* v_a_994_; lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1001_; 
lean_dec(v_json_981_);
v_a_994_ = lean_ctor_get(v___x_983_, 0);
v_isSharedCheck_1001_ = !lean_is_exclusive(v___x_983_);
if (v_isSharedCheck_1001_ == 0)
{
v___x_996_ = v___x_983_;
v_isShared_997_ = v_isSharedCheck_1001_;
goto v_resetjp_995_;
}
else
{
lean_inc(v_a_994_);
lean_dec(v___x_983_);
v___x_996_ = lean_box(0);
v_isShared_997_ = v_isSharedCheck_1001_;
goto v_resetjp_995_;
}
v_resetjp_995_:
{
lean_object* v___x_999_; 
if (v_isShared_997_ == 0)
{
lean_ctor_set_tag(v___x_996_, 0);
v___x_999_ = v___x_996_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v_a_994_);
v___x_999_ = v_reuseFailAlloc_1000_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
return v___x_999_;
}
}
}
else
{
lean_object* v_a_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; 
v_a_1002_ = lean_ctor_get(v___x_983_, 0);
lean_inc(v_a_1002_);
lean_dec_ref_known(v___x_983_, 1);
v___x_1003_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__6));
v___x_1004_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__1(v_json_981_, v___x_1003_);
if (lean_obj_tag(v___x_1004_) == 0)
{
lean_object* v_a_1005_; lean_object* v___x_1007_; uint8_t v_isShared_1008_; uint8_t v_isSharedCheck_1014_; 
lean_dec(v_a_1002_);
v_a_1005_ = lean_ctor_get(v___x_1004_, 0);
v_isSharedCheck_1014_ = !lean_is_exclusive(v___x_1004_);
if (v_isSharedCheck_1014_ == 0)
{
v___x_1007_ = v___x_1004_;
v_isShared_1008_ = v_isSharedCheck_1014_;
goto v_resetjp_1006_;
}
else
{
lean_inc(v_a_1005_);
lean_dec(v___x_1004_);
v___x_1007_ = lean_box(0);
v_isShared_1008_ = v_isSharedCheck_1014_;
goto v_resetjp_1006_;
}
v_resetjp_1006_:
{
lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1012_; 
v___x_1009_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__10, &l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__10);
v___x_1010_ = lean_string_append(v___x_1009_, v_a_1005_);
lean_dec(v_a_1005_);
if (v_isShared_1008_ == 0)
{
lean_ctor_set(v___x_1007_, 0, v___x_1010_);
v___x_1012_ = v___x_1007_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v___x_1010_);
v___x_1012_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
return v___x_1012_;
}
}
}
else
{
if (lean_obj_tag(v___x_1004_) == 0)
{
lean_object* v_a_1015_; lean_object* v___x_1017_; uint8_t v_isShared_1018_; uint8_t v_isSharedCheck_1022_; 
lean_dec(v_a_1002_);
v_a_1015_ = lean_ctor_get(v___x_1004_, 0);
v_isSharedCheck_1022_ = !lean_is_exclusive(v___x_1004_);
if (v_isSharedCheck_1022_ == 0)
{
v___x_1017_ = v___x_1004_;
v_isShared_1018_ = v_isSharedCheck_1022_;
goto v_resetjp_1016_;
}
else
{
lean_inc(v_a_1015_);
lean_dec(v___x_1004_);
v___x_1017_ = lean_box(0);
v_isShared_1018_ = v_isSharedCheck_1022_;
goto v_resetjp_1016_;
}
v_resetjp_1016_:
{
lean_object* v___x_1020_; 
if (v_isShared_1018_ == 0)
{
lean_ctor_set_tag(v___x_1017_, 0);
v___x_1020_ = v___x_1017_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v_a_1015_);
v___x_1020_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
return v___x_1020_;
}
}
}
else
{
lean_object* v_a_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1031_; 
v_a_1023_ = lean_ctor_get(v___x_1004_, 0);
v_isSharedCheck_1031_ = !lean_is_exclusive(v___x_1004_);
if (v_isSharedCheck_1031_ == 0)
{
v___x_1025_ = v___x_1004_;
v_isShared_1026_ = v_isSharedCheck_1031_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_a_1023_);
lean_dec(v___x_1004_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1031_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v___x_1027_; lean_object* v___x_1029_; 
v___x_1027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1027_, 0, v_a_1002_);
lean_ctor_set(v___x_1027_, 1, v_a_1023_);
if (v_isShared_1026_ == 0)
{
lean_ctor_set(v___x_1025_, 0, v___x_1027_);
v___x_1029_ = v___x_1025_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v___x_1027_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanFileProgressParams_toJson_spec__0_spec__0(size_t v_sz_1034_, size_t v_i_1035_, lean_object* v_bs_1036_){
_start:
{
uint8_t v___x_1037_; 
v___x_1037_ = lean_usize_dec_lt(v_i_1035_, v_sz_1034_);
if (v___x_1037_ == 0)
{
return v_bs_1036_;
}
else
{
lean_object* v_v_1038_; lean_object* v___x_1039_; lean_object* v_bs_x27_1040_; lean_object* v___x_1041_; size_t v___x_1042_; size_t v___x_1043_; lean_object* v___x_1044_; 
v_v_1038_ = lean_array_uget(v_bs_1036_, v_i_1035_);
v___x_1039_ = lean_unsigned_to_nat(0u);
v_bs_x27_1040_ = lean_array_uset(v_bs_1036_, v_i_1035_, v___x_1039_);
v___x_1041_ = l_Lean_Lsp_instToJsonLeanFileProgressProcessingInfo_toJson(v_v_1038_);
v___x_1042_ = ((size_t)1ULL);
v___x_1043_ = lean_usize_add(v_i_1035_, v___x_1042_);
v___x_1044_ = lean_array_uset(v_bs_x27_1040_, v_i_1035_, v___x_1041_);
v_i_1035_ = v___x_1043_;
v_bs_1036_ = v___x_1044_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanFileProgressParams_toJson_spec__0_spec__0___boxed(lean_object* v_sz_1046_, lean_object* v_i_1047_, lean_object* v_bs_1048_){
_start:
{
size_t v_sz_boxed_1049_; size_t v_i_boxed_1050_; lean_object* v_res_1051_; 
v_sz_boxed_1049_ = lean_unbox_usize(v_sz_1046_);
lean_dec(v_sz_1046_);
v_i_boxed_1050_ = lean_unbox_usize(v_i_1047_);
lean_dec(v_i_1047_);
v_res_1051_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanFileProgressParams_toJson_spec__0_spec__0(v_sz_boxed_1049_, v_i_boxed_1050_, v_bs_1048_);
return v_res_1051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanFileProgressParams_toJson_spec__0(lean_object* v_a_1052_){
_start:
{
size_t v_sz_1053_; size_t v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; 
v_sz_1053_ = lean_array_size(v_a_1052_);
v___x_1054_ = ((size_t)0ULL);
v___x_1055_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanFileProgressParams_toJson_spec__0_spec__0(v_sz_1053_, v___x_1054_, v_a_1052_);
v___x_1056_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1056_, 0, v___x_1055_);
return v___x_1056_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanFileProgressParams_toJson(lean_object* v_x_1057_){
_start:
{
lean_object* v_textDocument_1058_; lean_object* v_processing_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1079_; 
v_textDocument_1058_ = lean_ctor_get(v_x_1057_, 0);
v_processing_1059_ = lean_ctor_get(v_x_1057_, 1);
v_isSharedCheck_1079_ = !lean_is_exclusive(v_x_1057_);
if (v_isSharedCheck_1079_ == 0)
{
v___x_1061_ = v_x_1057_;
v_isShared_1062_ = v_isSharedCheck_1079_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_processing_1059_);
lean_inc(v_textDocument_1058_);
lean_dec(v_x_1057_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1079_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1066_; 
v___x_1063_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__0));
v___x_1064_ = l_Lean_Lsp_instToJsonVersionedTextDocumentIdentifier_toJson(v_textDocument_1058_);
if (v_isShared_1062_ == 0)
{
lean_ctor_set(v___x_1061_, 1, v___x_1064_);
lean_ctor_set(v___x_1061_, 0, v___x_1063_);
v___x_1066_ = v___x_1061_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v___x_1063_);
lean_ctor_set(v_reuseFailAlloc_1078_, 1, v___x_1064_);
v___x_1066_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; 
v___x_1067_ = lean_box(0);
v___x_1068_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1068_, 0, v___x_1066_);
lean_ctor_set(v___x_1068_, 1, v___x_1067_);
v___x_1069_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__6));
v___x_1070_ = l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanFileProgressParams_toJson_spec__0(v_processing_1059_);
v___x_1071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1071_, 0, v___x_1069_);
lean_ctor_set(v___x_1071_, 1, v___x_1070_);
v___x_1072_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1072_, 0, v___x_1071_);
lean_ctor_set(v___x_1072_, 1, v___x_1067_);
v___x_1073_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1073_, 0, v___x_1072_);
lean_ctor_set(v___x_1073_, 1, v___x_1067_);
v___x_1074_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1074_, 0, v___x_1068_);
lean_ctor_set(v___x_1074_, 1, v___x_1073_);
v___x_1075_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0));
v___x_1076_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_1074_, v___x_1075_);
v___x_1077_ = l_Lean_Json_mkObj(v___x_1076_);
lean_dec(v___x_1076_);
return v___x_1077_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoalParams_fromJson_spec__0(lean_object* v_j_1082_, lean_object* v_k_1083_){
_start:
{
lean_object* v___x_1084_; lean_object* v___x_1085_; 
v___x_1084_ = l_Lean_Json_getObjValD(v_j_1082_, v_k_1083_);
v___x_1085_ = l_Lean_Lsp_instFromJsonTextDocumentIdentifier_fromJson(v___x_1084_);
return v___x_1085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoalParams_fromJson_spec__0___boxed(lean_object* v_j_1086_, lean_object* v_k_1087_){
_start:
{
lean_object* v_res_1088_; 
v_res_1088_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoalParams_fromJson_spec__0(v_j_1086_, v_k_1087_);
lean_dec_ref(v_k_1087_);
return v_res_1088_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoalParams_fromJson_spec__1(lean_object* v_j_1089_, lean_object* v_k_1090_){
_start:
{
lean_object* v___x_1091_; lean_object* v___x_1092_; 
v___x_1091_ = l_Lean_Json_getObjValD(v_j_1089_, v_k_1090_);
v___x_1092_ = l_Lean_Lsp_instFromJsonPosition_fromJson(v___x_1091_);
return v___x_1092_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoalParams_fromJson_spec__1___boxed(lean_object* v_j_1093_, lean_object* v_k_1094_){
_start:
{
lean_object* v_res_1095_; 
v_res_1095_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoalParams_fromJson_spec__1(v_j_1093_, v_k_1094_);
lean_dec_ref(v_k_1094_);
return v_res_1095_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__2(void){
_start:
{
uint8_t v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; 
v___x_1101_ = 1;
v___x_1102_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__1));
v___x_1103_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1102_, v___x_1101_);
return v___x_1103_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__3(void){
_start:
{
lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; 
v___x_1104_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6));
v___x_1105_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__2, &l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__2);
v___x_1106_ = lean_string_append(v___x_1105_, v___x_1104_);
return v___x_1106_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; 
v___x_1107_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9, &l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9);
v___x_1108_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__3);
v___x_1109_ = lean_string_append(v___x_1108_, v___x_1107_);
return v___x_1109_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__5(void){
_start:
{
lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; 
v___x_1110_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_1111_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__4);
v___x_1112_ = lean_string_append(v___x_1111_, v___x_1110_);
return v___x_1112_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__8(void){
_start:
{
uint8_t v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; 
v___x_1116_ = 1;
v___x_1117_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__7));
v___x_1118_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1117_, v___x_1116_);
return v___x_1118_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__9(void){
_start:
{
lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; 
v___x_1119_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__8);
v___x_1120_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__3);
v___x_1121_ = lean_string_append(v___x_1120_, v___x_1119_);
return v___x_1121_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__10(void){
_start:
{
lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; 
v___x_1122_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_1123_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__9, &l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__9);
v___x_1124_ = lean_string_append(v___x_1123_, v___x_1122_);
return v___x_1124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson(lean_object* v_json_1125_){
_start:
{
lean_object* v___x_1126_; lean_object* v___x_1127_; 
v___x_1126_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__0));
lean_inc(v_json_1125_);
v___x_1127_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoalParams_fromJson_spec__0(v_json_1125_, v___x_1126_);
if (lean_obj_tag(v___x_1127_) == 0)
{
lean_object* v_a_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1137_; 
lean_dec(v_json_1125_);
v_a_1128_ = lean_ctor_get(v___x_1127_, 0);
v_isSharedCheck_1137_ = !lean_is_exclusive(v___x_1127_);
if (v_isSharedCheck_1137_ == 0)
{
v___x_1130_ = v___x_1127_;
v_isShared_1131_ = v_isSharedCheck_1137_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_a_1128_);
lean_dec(v___x_1127_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1137_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1135_; 
v___x_1132_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__5, &l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__5);
v___x_1133_ = lean_string_append(v___x_1132_, v_a_1128_);
lean_dec(v_a_1128_);
if (v_isShared_1131_ == 0)
{
lean_ctor_set(v___x_1130_, 0, v___x_1133_);
v___x_1135_ = v___x_1130_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v___x_1133_);
v___x_1135_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
return v___x_1135_;
}
}
}
else
{
if (lean_obj_tag(v___x_1127_) == 0)
{
lean_object* v_a_1138_; lean_object* v___x_1140_; uint8_t v_isShared_1141_; uint8_t v_isSharedCheck_1145_; 
lean_dec(v_json_1125_);
v_a_1138_ = lean_ctor_get(v___x_1127_, 0);
v_isSharedCheck_1145_ = !lean_is_exclusive(v___x_1127_);
if (v_isSharedCheck_1145_ == 0)
{
v___x_1140_ = v___x_1127_;
v_isShared_1141_ = v_isSharedCheck_1145_;
goto v_resetjp_1139_;
}
else
{
lean_inc(v_a_1138_);
lean_dec(v___x_1127_);
v___x_1140_ = lean_box(0);
v_isShared_1141_ = v_isSharedCheck_1145_;
goto v_resetjp_1139_;
}
v_resetjp_1139_:
{
lean_object* v___x_1143_; 
if (v_isShared_1141_ == 0)
{
lean_ctor_set_tag(v___x_1140_, 0);
v___x_1143_ = v___x_1140_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v_a_1138_);
v___x_1143_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1142_;
}
v_reusejp_1142_:
{
return v___x_1143_;
}
}
}
else
{
lean_object* v_a_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; 
v_a_1146_ = lean_ctor_get(v___x_1127_, 0);
lean_inc(v_a_1146_);
lean_dec_ref_known(v___x_1127_, 1);
v___x_1147_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__6));
v___x_1148_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoalParams_fromJson_spec__1(v_json_1125_, v___x_1147_);
if (lean_obj_tag(v___x_1148_) == 0)
{
lean_object* v_a_1149_; lean_object* v___x_1151_; uint8_t v_isShared_1152_; uint8_t v_isSharedCheck_1158_; 
lean_dec(v_a_1146_);
v_a_1149_ = lean_ctor_get(v___x_1148_, 0);
v_isSharedCheck_1158_ = !lean_is_exclusive(v___x_1148_);
if (v_isSharedCheck_1158_ == 0)
{
v___x_1151_ = v___x_1148_;
v_isShared_1152_ = v_isSharedCheck_1158_;
goto v_resetjp_1150_;
}
else
{
lean_inc(v_a_1149_);
lean_dec(v___x_1148_);
v___x_1151_ = lean_box(0);
v_isShared_1152_ = v_isSharedCheck_1158_;
goto v_resetjp_1150_;
}
v_resetjp_1150_:
{
lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1156_; 
v___x_1153_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__10, &l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__10);
v___x_1154_ = lean_string_append(v___x_1153_, v_a_1149_);
lean_dec(v_a_1149_);
if (v_isShared_1152_ == 0)
{
lean_ctor_set(v___x_1151_, 0, v___x_1154_);
v___x_1156_ = v___x_1151_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v___x_1154_);
v___x_1156_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1155_;
}
v_reusejp_1155_:
{
return v___x_1156_;
}
}
}
else
{
if (lean_obj_tag(v___x_1148_) == 0)
{
lean_object* v_a_1159_; lean_object* v___x_1161_; uint8_t v_isShared_1162_; uint8_t v_isSharedCheck_1166_; 
lean_dec(v_a_1146_);
v_a_1159_ = lean_ctor_get(v___x_1148_, 0);
v_isSharedCheck_1166_ = !lean_is_exclusive(v___x_1148_);
if (v_isSharedCheck_1166_ == 0)
{
v___x_1161_ = v___x_1148_;
v_isShared_1162_ = v_isSharedCheck_1166_;
goto v_resetjp_1160_;
}
else
{
lean_inc(v_a_1159_);
lean_dec(v___x_1148_);
v___x_1161_ = lean_box(0);
v_isShared_1162_ = v_isSharedCheck_1166_;
goto v_resetjp_1160_;
}
v_resetjp_1160_:
{
lean_object* v___x_1164_; 
if (v_isShared_1162_ == 0)
{
lean_ctor_set_tag(v___x_1161_, 0);
v___x_1164_ = v___x_1161_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v_a_1159_);
v___x_1164_ = v_reuseFailAlloc_1165_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
return v___x_1164_;
}
}
}
else
{
lean_object* v_a_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1175_; 
v_a_1167_ = lean_ctor_get(v___x_1148_, 0);
v_isSharedCheck_1175_ = !lean_is_exclusive(v___x_1148_);
if (v_isSharedCheck_1175_ == 0)
{
v___x_1169_ = v___x_1148_;
v_isShared_1170_ = v_isSharedCheck_1175_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_a_1167_);
lean_dec(v___x_1148_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1175_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
lean_object* v___x_1171_; lean_object* v___x_1173_; 
v___x_1171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1171_, 0, v_a_1146_);
lean_ctor_set(v___x_1171_, 1, v_a_1167_);
if (v_isShared_1170_ == 0)
{
lean_ctor_set(v___x_1169_, 0, v___x_1171_);
v___x_1173_ = v___x_1169_;
goto v_reusejp_1172_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v___x_1171_);
v___x_1173_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1172_;
}
v_reusejp_1172_:
{
return v___x_1173_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonPlainGoalParams_toJson(lean_object* v_x_1178_){
_start:
{
lean_object* v_textDocument_1179_; lean_object* v_position_1180_; lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1200_; 
v_textDocument_1179_ = lean_ctor_get(v_x_1178_, 0);
v_position_1180_ = lean_ctor_get(v_x_1178_, 1);
v_isSharedCheck_1200_ = !lean_is_exclusive(v_x_1178_);
if (v_isSharedCheck_1200_ == 0)
{
v___x_1182_ = v_x_1178_;
v_isShared_1183_ = v_isSharedCheck_1200_;
goto v_resetjp_1181_;
}
else
{
lean_inc(v_position_1180_);
lean_inc(v_textDocument_1179_);
lean_dec(v_x_1178_);
v___x_1182_ = lean_box(0);
v_isShared_1183_ = v_isSharedCheck_1200_;
goto v_resetjp_1181_;
}
v_resetjp_1181_:
{
lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1187_; 
v___x_1184_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__0));
v___x_1185_ = l_Lean_Lsp_instToJsonTextDocumentIdentifier_toJson(v_textDocument_1179_);
if (v_isShared_1183_ == 0)
{
lean_ctor_set(v___x_1182_, 1, v___x_1185_);
lean_ctor_set(v___x_1182_, 0, v___x_1184_);
v___x_1187_ = v___x_1182_;
goto v_reusejp_1186_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v___x_1184_);
lean_ctor_set(v_reuseFailAlloc_1199_, 1, v___x_1185_);
v___x_1187_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1186_;
}
v_reusejp_1186_:
{
lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; 
v___x_1188_ = lean_box(0);
v___x_1189_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1189_, 0, v___x_1187_);
lean_ctor_set(v___x_1189_, 1, v___x_1188_);
v___x_1190_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__6));
v___x_1191_ = l_Lean_Lsp_instToJsonPosition_toJson(v_position_1180_);
v___x_1192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1192_, 0, v___x_1190_);
lean_ctor_set(v___x_1192_, 1, v___x_1191_);
v___x_1193_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1193_, 0, v___x_1192_);
lean_ctor_set(v___x_1193_, 1, v___x_1188_);
v___x_1194_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1194_, 0, v___x_1193_);
lean_ctor_set(v___x_1194_, 1, v___x_1188_);
v___x_1195_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1195_, 0, v___x_1189_);
lean_ctor_set(v___x_1195_, 1, v___x_1194_);
v___x_1196_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0));
v___x_1197_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_1195_, v___x_1196_);
v___x_1198_ = l_Lean_Json_mkObj(v___x_1197_);
lean_dec(v___x_1197_);
return v___x_1198_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoal_fromJson_spec__0_spec__0_spec__1(size_t v_sz_1203_, size_t v_i_1204_, lean_object* v_bs_1205_){
_start:
{
uint8_t v___x_1206_; 
v___x_1206_ = lean_usize_dec_lt(v_i_1204_, v_sz_1203_);
if (v___x_1206_ == 0)
{
lean_object* v___x_1207_; 
v___x_1207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1207_, 0, v_bs_1205_);
return v___x_1207_;
}
else
{
lean_object* v_v_1208_; lean_object* v___x_1209_; 
v_v_1208_ = lean_array_uget_borrowed(v_bs_1205_, v_i_1204_);
lean_inc(v_v_1208_);
v___x_1209_ = l_Lean_Json_getStr_x3f(v_v_1208_);
if (lean_obj_tag(v___x_1209_) == 0)
{
lean_object* v_a_1210_; lean_object* v___x_1212_; uint8_t v_isShared_1213_; uint8_t v_isSharedCheck_1217_; 
lean_dec_ref(v_bs_1205_);
v_a_1210_ = lean_ctor_get(v___x_1209_, 0);
v_isSharedCheck_1217_ = !lean_is_exclusive(v___x_1209_);
if (v_isSharedCheck_1217_ == 0)
{
v___x_1212_ = v___x_1209_;
v_isShared_1213_ = v_isSharedCheck_1217_;
goto v_resetjp_1211_;
}
else
{
lean_inc(v_a_1210_);
lean_dec(v___x_1209_);
v___x_1212_ = lean_box(0);
v_isShared_1213_ = v_isSharedCheck_1217_;
goto v_resetjp_1211_;
}
v_resetjp_1211_:
{
lean_object* v___x_1215_; 
if (v_isShared_1213_ == 0)
{
v___x_1215_ = v___x_1212_;
goto v_reusejp_1214_;
}
else
{
lean_object* v_reuseFailAlloc_1216_; 
v_reuseFailAlloc_1216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1216_, 0, v_a_1210_);
v___x_1215_ = v_reuseFailAlloc_1216_;
goto v_reusejp_1214_;
}
v_reusejp_1214_:
{
return v___x_1215_;
}
}
}
else
{
lean_object* v_a_1218_; lean_object* v___x_1219_; lean_object* v_bs_x27_1220_; size_t v___x_1221_; size_t v___x_1222_; lean_object* v___x_1223_; 
v_a_1218_ = lean_ctor_get(v___x_1209_, 0);
lean_inc(v_a_1218_);
lean_dec_ref_known(v___x_1209_, 1);
v___x_1219_ = lean_unsigned_to_nat(0u);
v_bs_x27_1220_ = lean_array_uset(v_bs_1205_, v_i_1204_, v___x_1219_);
v___x_1221_ = ((size_t)1ULL);
v___x_1222_ = lean_usize_add(v_i_1204_, v___x_1221_);
v___x_1223_ = lean_array_uset(v_bs_x27_1220_, v_i_1204_, v_a_1218_);
v_i_1204_ = v___x_1222_;
v_bs_1205_ = v___x_1223_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoal_fromJson_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_1225_, lean_object* v_i_1226_, lean_object* v_bs_1227_){
_start:
{
size_t v_sz_boxed_1228_; size_t v_i_boxed_1229_; lean_object* v_res_1230_; 
v_sz_boxed_1228_ = lean_unbox_usize(v_sz_1225_);
lean_dec(v_sz_1225_);
v_i_boxed_1229_ = lean_unbox_usize(v_i_1226_);
lean_dec(v_i_1226_);
v_res_1230_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoal_fromJson_spec__0_spec__0_spec__1(v_sz_boxed_1228_, v_i_boxed_1229_, v_bs_1227_);
return v_res_1230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoal_fromJson_spec__0_spec__0(lean_object* v_x_1231_){
_start:
{
if (lean_obj_tag(v_x_1231_) == 4)
{
lean_object* v_elems_1232_; size_t v_sz_1233_; size_t v___x_1234_; lean_object* v___x_1235_; 
v_elems_1232_ = lean_ctor_get(v_x_1231_, 0);
lean_inc_ref(v_elems_1232_);
lean_dec_ref_known(v_x_1231_, 1);
v_sz_1233_ = lean_array_size(v_elems_1232_);
v___x_1234_ = ((size_t)0ULL);
v___x_1235_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoal_fromJson_spec__0_spec__0_spec__1(v_sz_1233_, v___x_1234_, v_elems_1232_);
return v___x_1235_;
}
else
{
lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; 
v___x_1236_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__1_spec__1___closed__0));
v___x_1237_ = lean_unsigned_to_nat(80u);
v___x_1238_ = l_Lean_Json_pretty(v_x_1231_, v___x_1237_);
v___x_1239_ = lean_string_append(v___x_1236_, v___x_1238_);
lean_dec_ref(v___x_1238_);
v___x_1240_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressKind___lam__0___closed__1));
v___x_1241_ = lean_string_append(v___x_1239_, v___x_1240_);
v___x_1242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1242_, 0, v___x_1241_);
return v___x_1242_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoal_fromJson_spec__0(lean_object* v_j_1243_, lean_object* v_k_1244_){
_start:
{
lean_object* v___x_1245_; lean_object* v___x_1246_; 
v___x_1245_ = l_Lean_Json_getObjValD(v_j_1243_, v_k_1244_);
v___x_1246_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoal_fromJson_spec__0_spec__0(v___x_1245_);
return v___x_1246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoal_fromJson_spec__0___boxed(lean_object* v_j_1247_, lean_object* v_k_1248_){
_start:
{
lean_object* v_res_1249_; 
v_res_1249_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoal_fromJson_spec__0(v_j_1247_, v_k_1248_);
lean_dec_ref(v_k_1248_);
return v_res_1249_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__3(void){
_start:
{
uint8_t v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; 
v___x_1256_ = 1;
v___x_1257_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__2));
v___x_1258_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1257_, v___x_1256_);
return v___x_1258_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__4(void){
_start:
{
lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; 
v___x_1259_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6));
v___x_1260_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__3, &l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__3);
v___x_1261_ = lean_string_append(v___x_1260_, v___x_1259_);
return v___x_1261_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__6(void){
_start:
{
uint8_t v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; 
v___x_1264_ = 1;
v___x_1265_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__5));
v___x_1266_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1265_, v___x_1264_);
return v___x_1266_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__7(void){
_start:
{
lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; 
v___x_1267_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__6, &l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__6);
v___x_1268_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__4, &l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__4);
v___x_1269_ = lean_string_append(v___x_1268_, v___x_1267_);
return v___x_1269_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__8(void){
_start:
{
lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; 
v___x_1270_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_1271_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__7, &l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__7);
v___x_1272_ = lean_string_append(v___x_1271_, v___x_1270_);
return v___x_1272_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__11(void){
_start:
{
uint8_t v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; 
v___x_1276_ = 1;
v___x_1277_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__10));
v___x_1278_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1277_, v___x_1276_);
return v___x_1278_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__12(void){
_start:
{
lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; 
v___x_1279_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__11, &l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__11);
v___x_1280_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__4, &l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__4);
v___x_1281_ = lean_string_append(v___x_1280_, v___x_1279_);
return v___x_1281_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__13(void){
_start:
{
lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; 
v___x_1282_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_1283_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__12, &l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__12);
v___x_1284_ = lean_string_append(v___x_1283_, v___x_1282_);
return v___x_1284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonPlainGoal_fromJson(lean_object* v_json_1285_){
_start:
{
lean_object* v___x_1286_; lean_object* v___x_1287_; 
v___x_1286_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__0));
lean_inc(v_json_1285_);
v___x_1287_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson_spec__0(v_json_1285_, v___x_1286_);
if (lean_obj_tag(v___x_1287_) == 0)
{
lean_object* v_a_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1297_; 
lean_dec(v_json_1285_);
v_a_1288_ = lean_ctor_get(v___x_1287_, 0);
v_isSharedCheck_1297_ = !lean_is_exclusive(v___x_1287_);
if (v_isSharedCheck_1297_ == 0)
{
v___x_1290_ = v___x_1287_;
v_isShared_1291_ = v_isSharedCheck_1297_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_a_1288_);
lean_dec(v___x_1287_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1297_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1295_; 
v___x_1292_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__8, &l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__8);
v___x_1293_ = lean_string_append(v___x_1292_, v_a_1288_);
lean_dec(v_a_1288_);
if (v_isShared_1291_ == 0)
{
lean_ctor_set(v___x_1290_, 0, v___x_1293_);
v___x_1295_ = v___x_1290_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v___x_1293_);
v___x_1295_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1294_;
}
v_reusejp_1294_:
{
return v___x_1295_;
}
}
}
else
{
if (lean_obj_tag(v___x_1287_) == 0)
{
lean_object* v_a_1298_; lean_object* v___x_1300_; uint8_t v_isShared_1301_; uint8_t v_isSharedCheck_1305_; 
lean_dec(v_json_1285_);
v_a_1298_ = lean_ctor_get(v___x_1287_, 0);
v_isSharedCheck_1305_ = !lean_is_exclusive(v___x_1287_);
if (v_isSharedCheck_1305_ == 0)
{
v___x_1300_ = v___x_1287_;
v_isShared_1301_ = v_isSharedCheck_1305_;
goto v_resetjp_1299_;
}
else
{
lean_inc(v_a_1298_);
lean_dec(v___x_1287_);
v___x_1300_ = lean_box(0);
v_isShared_1301_ = v_isSharedCheck_1305_;
goto v_resetjp_1299_;
}
v_resetjp_1299_:
{
lean_object* v___x_1303_; 
if (v_isShared_1301_ == 0)
{
lean_ctor_set_tag(v___x_1300_, 0);
v___x_1303_ = v___x_1300_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1304_; 
v_reuseFailAlloc_1304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1304_, 0, v_a_1298_);
v___x_1303_ = v_reuseFailAlloc_1304_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
return v___x_1303_;
}
}
}
else
{
lean_object* v_a_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; 
v_a_1306_ = lean_ctor_get(v___x_1287_, 0);
lean_inc(v_a_1306_);
lean_dec_ref_known(v___x_1287_, 1);
v___x_1307_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__9));
v___x_1308_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoal_fromJson_spec__0(v_json_1285_, v___x_1307_);
if (lean_obj_tag(v___x_1308_) == 0)
{
lean_object* v_a_1309_; lean_object* v___x_1311_; uint8_t v_isShared_1312_; uint8_t v_isSharedCheck_1318_; 
lean_dec(v_a_1306_);
v_a_1309_ = lean_ctor_get(v___x_1308_, 0);
v_isSharedCheck_1318_ = !lean_is_exclusive(v___x_1308_);
if (v_isSharedCheck_1318_ == 0)
{
v___x_1311_ = v___x_1308_;
v_isShared_1312_ = v_isSharedCheck_1318_;
goto v_resetjp_1310_;
}
else
{
lean_inc(v_a_1309_);
lean_dec(v___x_1308_);
v___x_1311_ = lean_box(0);
v_isShared_1312_ = v_isSharedCheck_1318_;
goto v_resetjp_1310_;
}
v_resetjp_1310_:
{
lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1316_; 
v___x_1313_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__13, &l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__13);
v___x_1314_ = lean_string_append(v___x_1313_, v_a_1309_);
lean_dec(v_a_1309_);
if (v_isShared_1312_ == 0)
{
lean_ctor_set(v___x_1311_, 0, v___x_1314_);
v___x_1316_ = v___x_1311_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v___x_1314_);
v___x_1316_ = v_reuseFailAlloc_1317_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
return v___x_1316_;
}
}
}
else
{
if (lean_obj_tag(v___x_1308_) == 0)
{
lean_object* v_a_1319_; lean_object* v___x_1321_; uint8_t v_isShared_1322_; uint8_t v_isSharedCheck_1326_; 
lean_dec(v_a_1306_);
v_a_1319_ = lean_ctor_get(v___x_1308_, 0);
v_isSharedCheck_1326_ = !lean_is_exclusive(v___x_1308_);
if (v_isSharedCheck_1326_ == 0)
{
v___x_1321_ = v___x_1308_;
v_isShared_1322_ = v_isSharedCheck_1326_;
goto v_resetjp_1320_;
}
else
{
lean_inc(v_a_1319_);
lean_dec(v___x_1308_);
v___x_1321_ = lean_box(0);
v_isShared_1322_ = v_isSharedCheck_1326_;
goto v_resetjp_1320_;
}
v_resetjp_1320_:
{
lean_object* v___x_1324_; 
if (v_isShared_1322_ == 0)
{
lean_ctor_set_tag(v___x_1321_, 0);
v___x_1324_ = v___x_1321_;
goto v_reusejp_1323_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v_a_1319_);
v___x_1324_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1323_;
}
v_reusejp_1323_:
{
return v___x_1324_;
}
}
}
else
{
lean_object* v_a_1327_; lean_object* v___x_1329_; uint8_t v_isShared_1330_; uint8_t v_isSharedCheck_1335_; 
v_a_1327_ = lean_ctor_get(v___x_1308_, 0);
v_isSharedCheck_1335_ = !lean_is_exclusive(v___x_1308_);
if (v_isSharedCheck_1335_ == 0)
{
v___x_1329_ = v___x_1308_;
v_isShared_1330_ = v_isSharedCheck_1335_;
goto v_resetjp_1328_;
}
else
{
lean_inc(v_a_1327_);
lean_dec(v___x_1308_);
v___x_1329_ = lean_box(0);
v_isShared_1330_ = v_isSharedCheck_1335_;
goto v_resetjp_1328_;
}
v_resetjp_1328_:
{
lean_object* v___x_1331_; lean_object* v___x_1333_; 
v___x_1331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1331_, 0, v_a_1306_);
lean_ctor_set(v___x_1331_, 1, v_a_1327_);
if (v_isShared_1330_ == 0)
{
lean_ctor_set(v___x_1329_, 0, v___x_1331_);
v___x_1333_ = v___x_1329_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v___x_1331_);
v___x_1333_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
return v___x_1333_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPlainGoal_toJson_spec__0_spec__0(size_t v_sz_1338_, size_t v_i_1339_, lean_object* v_bs_1340_){
_start:
{
uint8_t v___x_1341_; 
v___x_1341_ = lean_usize_dec_lt(v_i_1339_, v_sz_1338_);
if (v___x_1341_ == 0)
{
return v_bs_1340_;
}
else
{
lean_object* v_v_1342_; lean_object* v___x_1343_; lean_object* v_bs_x27_1344_; lean_object* v___x_1345_; size_t v___x_1346_; size_t v___x_1347_; lean_object* v___x_1348_; 
v_v_1342_ = lean_array_uget(v_bs_1340_, v_i_1339_);
v___x_1343_ = lean_unsigned_to_nat(0u);
v_bs_x27_1344_ = lean_array_uset(v_bs_1340_, v_i_1339_, v___x_1343_);
v___x_1345_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1345_, 0, v_v_1342_);
v___x_1346_ = ((size_t)1ULL);
v___x_1347_ = lean_usize_add(v_i_1339_, v___x_1346_);
v___x_1348_ = lean_array_uset(v_bs_x27_1344_, v_i_1339_, v___x_1345_);
v_i_1339_ = v___x_1347_;
v_bs_1340_ = v___x_1348_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPlainGoal_toJson_spec__0_spec__0___boxed(lean_object* v_sz_1350_, lean_object* v_i_1351_, lean_object* v_bs_1352_){
_start:
{
size_t v_sz_boxed_1353_; size_t v_i_boxed_1354_; lean_object* v_res_1355_; 
v_sz_boxed_1353_ = lean_unbox_usize(v_sz_1350_);
lean_dec(v_sz_1350_);
v_i_boxed_1354_ = lean_unbox_usize(v_i_1351_);
lean_dec(v_i_1351_);
v_res_1355_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPlainGoal_toJson_spec__0_spec__0(v_sz_boxed_1353_, v_i_boxed_1354_, v_bs_1352_);
return v_res_1355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonPlainGoal_toJson_spec__0(lean_object* v_a_1356_){
_start:
{
size_t v_sz_1357_; size_t v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; 
v_sz_1357_ = lean_array_size(v_a_1356_);
v___x_1358_ = ((size_t)0ULL);
v___x_1359_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPlainGoal_toJson_spec__0_spec__0(v_sz_1357_, v___x_1358_, v_a_1356_);
v___x_1360_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1360_, 0, v___x_1359_);
return v___x_1360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonPlainGoal_toJson(lean_object* v_x_1361_){
_start:
{
lean_object* v_rendered_1362_; lean_object* v_goals_1363_; lean_object* v___x_1365_; uint8_t v_isShared_1366_; uint8_t v_isSharedCheck_1383_; 
v_rendered_1362_ = lean_ctor_get(v_x_1361_, 0);
v_goals_1363_ = lean_ctor_get(v_x_1361_, 1);
v_isSharedCheck_1383_ = !lean_is_exclusive(v_x_1361_);
if (v_isSharedCheck_1383_ == 0)
{
v___x_1365_ = v_x_1361_;
v_isShared_1366_ = v_isSharedCheck_1383_;
goto v_resetjp_1364_;
}
else
{
lean_inc(v_goals_1363_);
lean_inc(v_rendered_1362_);
lean_dec(v_x_1361_);
v___x_1365_ = lean_box(0);
v_isShared_1366_ = v_isSharedCheck_1383_;
goto v_resetjp_1364_;
}
v_resetjp_1364_:
{
lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1370_; 
v___x_1367_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__0));
v___x_1368_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1368_, 0, v_rendered_1362_);
if (v_isShared_1366_ == 0)
{
lean_ctor_set(v___x_1365_, 1, v___x_1368_);
lean_ctor_set(v___x_1365_, 0, v___x_1367_);
v___x_1370_ = v___x_1365_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1382_; 
v_reuseFailAlloc_1382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1382_, 0, v___x_1367_);
lean_ctor_set(v_reuseFailAlloc_1382_, 1, v___x_1368_);
v___x_1370_ = v_reuseFailAlloc_1382_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; 
v___x_1371_ = lean_box(0);
v___x_1372_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1372_, 0, v___x_1370_);
lean_ctor_set(v___x_1372_, 1, v___x_1371_);
v___x_1373_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__9));
v___x_1374_ = l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonPlainGoal_toJson_spec__0(v_goals_1363_);
v___x_1375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1375_, 0, v___x_1373_);
lean_ctor_set(v___x_1375_, 1, v___x_1374_);
v___x_1376_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1376_, 0, v___x_1375_);
lean_ctor_set(v___x_1376_, 1, v___x_1371_);
v___x_1377_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1377_, 0, v___x_1376_);
lean_ctor_set(v___x_1377_, 1, v___x_1371_);
v___x_1378_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1378_, 0, v___x_1372_);
lean_ctor_set(v___x_1378_, 1, v___x_1377_);
v___x_1379_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0));
v___x_1380_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_1378_, v___x_1379_);
v___x_1381_ = l_Lean_Json_mkObj(v___x_1380_);
lean_dec(v___x_1380_);
return v___x_1381_;
}
}
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__2(void){
_start:
{
uint8_t v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; 
v___x_1391_ = 1;
v___x_1392_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__1));
v___x_1393_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1392_, v___x_1391_);
return v___x_1393_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__3(void){
_start:
{
lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; 
v___x_1394_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6));
v___x_1395_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__2, &l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__2);
v___x_1396_ = lean_string_append(v___x_1395_, v___x_1394_);
return v___x_1396_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; 
v___x_1397_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9, &l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9);
v___x_1398_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__3);
v___x_1399_ = lean_string_append(v___x_1398_, v___x_1397_);
return v___x_1399_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__5(void){
_start:
{
lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; 
v___x_1400_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_1401_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__4);
v___x_1402_ = lean_string_append(v___x_1401_, v___x_1400_);
return v___x_1402_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__6(void){
_start:
{
lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; 
v___x_1403_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__8);
v___x_1404_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__3);
v___x_1405_ = lean_string_append(v___x_1404_, v___x_1403_);
return v___x_1405_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__7(void){
_start:
{
lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; 
v___x_1406_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_1407_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__6, &l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__6);
v___x_1408_ = lean_string_append(v___x_1407_, v___x_1406_);
return v___x_1408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson(lean_object* v_json_1409_){
_start:
{
lean_object* v___x_1410_; lean_object* v___x_1411_; 
v___x_1410_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__0));
lean_inc(v_json_1409_);
v___x_1411_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoalParams_fromJson_spec__0(v_json_1409_, v___x_1410_);
if (lean_obj_tag(v___x_1411_) == 0)
{
lean_object* v_a_1412_; lean_object* v___x_1414_; uint8_t v_isShared_1415_; uint8_t v_isSharedCheck_1421_; 
lean_dec(v_json_1409_);
v_a_1412_ = lean_ctor_get(v___x_1411_, 0);
v_isSharedCheck_1421_ = !lean_is_exclusive(v___x_1411_);
if (v_isSharedCheck_1421_ == 0)
{
v___x_1414_ = v___x_1411_;
v_isShared_1415_ = v_isSharedCheck_1421_;
goto v_resetjp_1413_;
}
else
{
lean_inc(v_a_1412_);
lean_dec(v___x_1411_);
v___x_1414_ = lean_box(0);
v_isShared_1415_ = v_isSharedCheck_1421_;
goto v_resetjp_1413_;
}
v_resetjp_1413_:
{
lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1419_; 
v___x_1416_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__5, &l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__5);
v___x_1417_ = lean_string_append(v___x_1416_, v_a_1412_);
lean_dec(v_a_1412_);
if (v_isShared_1415_ == 0)
{
lean_ctor_set(v___x_1414_, 0, v___x_1417_);
v___x_1419_ = v___x_1414_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v___x_1417_);
v___x_1419_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
return v___x_1419_;
}
}
}
else
{
if (lean_obj_tag(v___x_1411_) == 0)
{
lean_object* v_a_1422_; lean_object* v___x_1424_; uint8_t v_isShared_1425_; uint8_t v_isSharedCheck_1429_; 
lean_dec(v_json_1409_);
v_a_1422_ = lean_ctor_get(v___x_1411_, 0);
v_isSharedCheck_1429_ = !lean_is_exclusive(v___x_1411_);
if (v_isSharedCheck_1429_ == 0)
{
v___x_1424_ = v___x_1411_;
v_isShared_1425_ = v_isSharedCheck_1429_;
goto v_resetjp_1423_;
}
else
{
lean_inc(v_a_1422_);
lean_dec(v___x_1411_);
v___x_1424_ = lean_box(0);
v_isShared_1425_ = v_isSharedCheck_1429_;
goto v_resetjp_1423_;
}
v_resetjp_1423_:
{
lean_object* v___x_1427_; 
if (v_isShared_1425_ == 0)
{
lean_ctor_set_tag(v___x_1424_, 0);
v___x_1427_ = v___x_1424_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v_a_1422_);
v___x_1427_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
return v___x_1427_;
}
}
}
else
{
lean_object* v_a_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; 
v_a_1430_ = lean_ctor_get(v___x_1411_, 0);
lean_inc(v_a_1430_);
lean_dec_ref_known(v___x_1411_, 1);
v___x_1431_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__6));
v___x_1432_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoalParams_fromJson_spec__1(v_json_1409_, v___x_1431_);
if (lean_obj_tag(v___x_1432_) == 0)
{
lean_object* v_a_1433_; lean_object* v___x_1435_; uint8_t v_isShared_1436_; uint8_t v_isSharedCheck_1442_; 
lean_dec(v_a_1430_);
v_a_1433_ = lean_ctor_get(v___x_1432_, 0);
v_isSharedCheck_1442_ = !lean_is_exclusive(v___x_1432_);
if (v_isSharedCheck_1442_ == 0)
{
v___x_1435_ = v___x_1432_;
v_isShared_1436_ = v_isSharedCheck_1442_;
goto v_resetjp_1434_;
}
else
{
lean_inc(v_a_1433_);
lean_dec(v___x_1432_);
v___x_1435_ = lean_box(0);
v_isShared_1436_ = v_isSharedCheck_1442_;
goto v_resetjp_1434_;
}
v_resetjp_1434_:
{
lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1440_; 
v___x_1437_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__7);
v___x_1438_ = lean_string_append(v___x_1437_, v_a_1433_);
lean_dec(v_a_1433_);
if (v_isShared_1436_ == 0)
{
lean_ctor_set(v___x_1435_, 0, v___x_1438_);
v___x_1440_ = v___x_1435_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v___x_1438_);
v___x_1440_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
return v___x_1440_;
}
}
}
else
{
if (lean_obj_tag(v___x_1432_) == 0)
{
lean_object* v_a_1443_; lean_object* v___x_1445_; uint8_t v_isShared_1446_; uint8_t v_isSharedCheck_1450_; 
lean_dec(v_a_1430_);
v_a_1443_ = lean_ctor_get(v___x_1432_, 0);
v_isSharedCheck_1450_ = !lean_is_exclusive(v___x_1432_);
if (v_isSharedCheck_1450_ == 0)
{
v___x_1445_ = v___x_1432_;
v_isShared_1446_ = v_isSharedCheck_1450_;
goto v_resetjp_1444_;
}
else
{
lean_inc(v_a_1443_);
lean_dec(v___x_1432_);
v___x_1445_ = lean_box(0);
v_isShared_1446_ = v_isSharedCheck_1450_;
goto v_resetjp_1444_;
}
v_resetjp_1444_:
{
lean_object* v___x_1448_; 
if (v_isShared_1446_ == 0)
{
lean_ctor_set_tag(v___x_1445_, 0);
v___x_1448_ = v___x_1445_;
goto v_reusejp_1447_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v_a_1443_);
v___x_1448_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1447_;
}
v_reusejp_1447_:
{
return v___x_1448_;
}
}
}
else
{
lean_object* v_a_1451_; lean_object* v___x_1453_; uint8_t v_isShared_1454_; uint8_t v_isSharedCheck_1459_; 
v_a_1451_ = lean_ctor_get(v___x_1432_, 0);
v_isSharedCheck_1459_ = !lean_is_exclusive(v___x_1432_);
if (v_isSharedCheck_1459_ == 0)
{
v___x_1453_ = v___x_1432_;
v_isShared_1454_ = v_isSharedCheck_1459_;
goto v_resetjp_1452_;
}
else
{
lean_inc(v_a_1451_);
lean_dec(v___x_1432_);
v___x_1453_ = lean_box(0);
v_isShared_1454_ = v_isSharedCheck_1459_;
goto v_resetjp_1452_;
}
v_resetjp_1452_:
{
lean_object* v___x_1455_; lean_object* v___x_1457_; 
v___x_1455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1455_, 0, v_a_1430_);
lean_ctor_set(v___x_1455_, 1, v_a_1451_);
if (v_isShared_1454_ == 0)
{
lean_ctor_set(v___x_1453_, 0, v___x_1455_);
v___x_1457_ = v___x_1453_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1458_; 
v_reuseFailAlloc_1458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1458_, 0, v___x_1455_);
v___x_1457_ = v_reuseFailAlloc_1458_;
goto v_reusejp_1456_;
}
v_reusejp_1456_:
{
return v___x_1457_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonPlainTermGoalParams_toJson(lean_object* v_x_1462_){
_start:
{
lean_object* v_textDocument_1463_; lean_object* v_position_1464_; lean_object* v___x_1466_; uint8_t v_isShared_1467_; uint8_t v_isSharedCheck_1484_; 
v_textDocument_1463_ = lean_ctor_get(v_x_1462_, 0);
v_position_1464_ = lean_ctor_get(v_x_1462_, 1);
v_isSharedCheck_1484_ = !lean_is_exclusive(v_x_1462_);
if (v_isSharedCheck_1484_ == 0)
{
v___x_1466_ = v_x_1462_;
v_isShared_1467_ = v_isSharedCheck_1484_;
goto v_resetjp_1465_;
}
else
{
lean_inc(v_position_1464_);
lean_inc(v_textDocument_1463_);
lean_dec(v_x_1462_);
v___x_1466_ = lean_box(0);
v_isShared_1467_ = v_isSharedCheck_1484_;
goto v_resetjp_1465_;
}
v_resetjp_1465_:
{
lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1471_; 
v___x_1468_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__0));
v___x_1469_ = l_Lean_Lsp_instToJsonTextDocumentIdentifier_toJson(v_textDocument_1463_);
if (v_isShared_1467_ == 0)
{
lean_ctor_set(v___x_1466_, 1, v___x_1469_);
lean_ctor_set(v___x_1466_, 0, v___x_1468_);
v___x_1471_ = v___x_1466_;
goto v_reusejp_1470_;
}
else
{
lean_object* v_reuseFailAlloc_1483_; 
v_reuseFailAlloc_1483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1483_, 0, v___x_1468_);
lean_ctor_set(v_reuseFailAlloc_1483_, 1, v___x_1469_);
v___x_1471_ = v_reuseFailAlloc_1483_;
goto v_reusejp_1470_;
}
v_reusejp_1470_:
{
lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; 
v___x_1472_ = lean_box(0);
v___x_1473_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1473_, 0, v___x_1471_);
lean_ctor_set(v___x_1473_, 1, v___x_1472_);
v___x_1474_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__6));
v___x_1475_ = l_Lean_Lsp_instToJsonPosition_toJson(v_position_1464_);
v___x_1476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1476_, 0, v___x_1474_);
lean_ctor_set(v___x_1476_, 1, v___x_1475_);
v___x_1477_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1477_, 0, v___x_1476_);
lean_ctor_set(v___x_1477_, 1, v___x_1472_);
v___x_1478_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1478_, 0, v___x_1477_);
lean_ctor_set(v___x_1478_, 1, v___x_1472_);
v___x_1479_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1479_, 0, v___x_1473_);
lean_ctor_set(v___x_1479_, 1, v___x_1478_);
v___x_1480_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0));
v___x_1481_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_1479_, v___x_1480_);
v___x_1482_ = l_Lean_Json_mkObj(v___x_1481_);
lean_dec(v___x_1481_);
return v___x_1482_;
}
}
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__3(void){
_start:
{
uint8_t v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; 
v___x_1493_ = 1;
v___x_1494_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__2));
v___x_1495_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1494_, v___x_1493_);
return v___x_1495_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__4(void){
_start:
{
lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; 
v___x_1496_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6));
v___x_1497_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__3, &l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__3);
v___x_1498_ = lean_string_append(v___x_1497_, v___x_1496_);
return v___x_1498_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__6(void){
_start:
{
uint8_t v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; 
v___x_1501_ = 1;
v___x_1502_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__5));
v___x_1503_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1502_, v___x_1501_);
return v___x_1503_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__7(void){
_start:
{
lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; 
v___x_1504_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__6, &l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__6);
v___x_1505_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__4, &l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__4);
v___x_1506_ = lean_string_append(v___x_1505_, v___x_1504_);
return v___x_1506_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__8(void){
_start:
{
lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; 
v___x_1507_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_1508_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__7, &l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__7);
v___x_1509_ = lean_string_append(v___x_1508_, v___x_1507_);
return v___x_1509_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__9(void){
_start:
{
lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; 
v___x_1510_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__6);
v___x_1511_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__4, &l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__4);
v___x_1512_ = lean_string_append(v___x_1511_, v___x_1510_);
return v___x_1512_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__10(void){
_start:
{
lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; 
v___x_1513_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_1514_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__9, &l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__9);
v___x_1515_ = lean_string_append(v___x_1514_, v___x_1513_);
return v___x_1515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson(lean_object* v_json_1516_){
_start:
{
lean_object* v___x_1517_; lean_object* v___x_1518_; 
v___x_1517_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__0));
lean_inc(v_json_1516_);
v___x_1518_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson_spec__0(v_json_1516_, v___x_1517_);
if (lean_obj_tag(v___x_1518_) == 0)
{
lean_object* v_a_1519_; lean_object* v___x_1521_; uint8_t v_isShared_1522_; uint8_t v_isSharedCheck_1528_; 
lean_dec(v_json_1516_);
v_a_1519_ = lean_ctor_get(v___x_1518_, 0);
v_isSharedCheck_1528_ = !lean_is_exclusive(v___x_1518_);
if (v_isSharedCheck_1528_ == 0)
{
v___x_1521_ = v___x_1518_;
v_isShared_1522_ = v_isSharedCheck_1528_;
goto v_resetjp_1520_;
}
else
{
lean_inc(v_a_1519_);
lean_dec(v___x_1518_);
v___x_1521_ = lean_box(0);
v_isShared_1522_ = v_isSharedCheck_1528_;
goto v_resetjp_1520_;
}
v_resetjp_1520_:
{
lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1526_; 
v___x_1523_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__8, &l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__8);
v___x_1524_ = lean_string_append(v___x_1523_, v_a_1519_);
lean_dec(v_a_1519_);
if (v_isShared_1522_ == 0)
{
lean_ctor_set(v___x_1521_, 0, v___x_1524_);
v___x_1526_ = v___x_1521_;
goto v_reusejp_1525_;
}
else
{
lean_object* v_reuseFailAlloc_1527_; 
v_reuseFailAlloc_1527_ = lean_alloc_ctor(0, 1, 0);
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
else
{
if (lean_obj_tag(v___x_1518_) == 0)
{
lean_object* v_a_1529_; lean_object* v___x_1531_; uint8_t v_isShared_1532_; uint8_t v_isSharedCheck_1536_; 
lean_dec(v_json_1516_);
v_a_1529_ = lean_ctor_get(v___x_1518_, 0);
v_isSharedCheck_1536_ = !lean_is_exclusive(v___x_1518_);
if (v_isSharedCheck_1536_ == 0)
{
v___x_1531_ = v___x_1518_;
v_isShared_1532_ = v_isSharedCheck_1536_;
goto v_resetjp_1530_;
}
else
{
lean_inc(v_a_1529_);
lean_dec(v___x_1518_);
v___x_1531_ = lean_box(0);
v_isShared_1532_ = v_isSharedCheck_1536_;
goto v_resetjp_1530_;
}
v_resetjp_1530_:
{
lean_object* v___x_1534_; 
if (v_isShared_1532_ == 0)
{
lean_ctor_set_tag(v___x_1531_, 0);
v___x_1534_ = v___x_1531_;
goto v_reusejp_1533_;
}
else
{
lean_object* v_reuseFailAlloc_1535_; 
v_reuseFailAlloc_1535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1535_, 0, v_a_1529_);
v___x_1534_ = v_reuseFailAlloc_1535_;
goto v_reusejp_1533_;
}
v_reusejp_1533_:
{
return v___x_1534_;
}
}
}
else
{
lean_object* v_a_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; 
v_a_1537_ = lean_ctor_get(v___x_1518_, 0);
lean_inc(v_a_1537_);
lean_dec_ref_known(v___x_1518_, 1);
v___x_1538_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__0));
v___x_1539_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson_spec__0(v_json_1516_, v___x_1538_);
if (lean_obj_tag(v___x_1539_) == 0)
{
lean_object* v_a_1540_; lean_object* v___x_1542_; uint8_t v_isShared_1543_; uint8_t v_isSharedCheck_1549_; 
lean_dec(v_a_1537_);
v_a_1540_ = lean_ctor_get(v___x_1539_, 0);
v_isSharedCheck_1549_ = !lean_is_exclusive(v___x_1539_);
if (v_isSharedCheck_1549_ == 0)
{
v___x_1542_ = v___x_1539_;
v_isShared_1543_ = v_isSharedCheck_1549_;
goto v_resetjp_1541_;
}
else
{
lean_inc(v_a_1540_);
lean_dec(v___x_1539_);
v___x_1542_ = lean_box(0);
v_isShared_1543_ = v_isSharedCheck_1549_;
goto v_resetjp_1541_;
}
v_resetjp_1541_:
{
lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1547_; 
v___x_1544_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__10, &l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__10);
v___x_1545_ = lean_string_append(v___x_1544_, v_a_1540_);
lean_dec(v_a_1540_);
if (v_isShared_1543_ == 0)
{
lean_ctor_set(v___x_1542_, 0, v___x_1545_);
v___x_1547_ = v___x_1542_;
goto v_reusejp_1546_;
}
else
{
lean_object* v_reuseFailAlloc_1548_; 
v_reuseFailAlloc_1548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1548_, 0, v___x_1545_);
v___x_1547_ = v_reuseFailAlloc_1548_;
goto v_reusejp_1546_;
}
v_reusejp_1546_:
{
return v___x_1547_;
}
}
}
else
{
if (lean_obj_tag(v___x_1539_) == 0)
{
lean_object* v_a_1550_; lean_object* v___x_1552_; uint8_t v_isShared_1553_; uint8_t v_isSharedCheck_1557_; 
lean_dec(v_a_1537_);
v_a_1550_ = lean_ctor_get(v___x_1539_, 0);
v_isSharedCheck_1557_ = !lean_is_exclusive(v___x_1539_);
if (v_isSharedCheck_1557_ == 0)
{
v___x_1552_ = v___x_1539_;
v_isShared_1553_ = v_isSharedCheck_1557_;
goto v_resetjp_1551_;
}
else
{
lean_inc(v_a_1550_);
lean_dec(v___x_1539_);
v___x_1552_ = lean_box(0);
v_isShared_1553_ = v_isSharedCheck_1557_;
goto v_resetjp_1551_;
}
v_resetjp_1551_:
{
lean_object* v___x_1555_; 
if (v_isShared_1553_ == 0)
{
lean_ctor_set_tag(v___x_1552_, 0);
v___x_1555_ = v___x_1552_;
goto v_reusejp_1554_;
}
else
{
lean_object* v_reuseFailAlloc_1556_; 
v_reuseFailAlloc_1556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1556_, 0, v_a_1550_);
v___x_1555_ = v_reuseFailAlloc_1556_;
goto v_reusejp_1554_;
}
v_reusejp_1554_:
{
return v___x_1555_;
}
}
}
else
{
lean_object* v_a_1558_; lean_object* v___x_1560_; uint8_t v_isShared_1561_; uint8_t v_isSharedCheck_1566_; 
v_a_1558_ = lean_ctor_get(v___x_1539_, 0);
v_isSharedCheck_1566_ = !lean_is_exclusive(v___x_1539_);
if (v_isSharedCheck_1566_ == 0)
{
v___x_1560_ = v___x_1539_;
v_isShared_1561_ = v_isSharedCheck_1566_;
goto v_resetjp_1559_;
}
else
{
lean_inc(v_a_1558_);
lean_dec(v___x_1539_);
v___x_1560_ = lean_box(0);
v_isShared_1561_ = v_isSharedCheck_1566_;
goto v_resetjp_1559_;
}
v_resetjp_1559_:
{
lean_object* v___x_1562_; lean_object* v___x_1564_; 
v___x_1562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1562_, 0, v_a_1537_);
lean_ctor_set(v___x_1562_, 1, v_a_1558_);
if (v_isShared_1561_ == 0)
{
lean_ctor_set(v___x_1560_, 0, v___x_1562_);
v___x_1564_ = v___x_1560_;
goto v_reusejp_1563_;
}
else
{
lean_object* v_reuseFailAlloc_1565_; 
v_reuseFailAlloc_1565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1565_, 0, v___x_1562_);
v___x_1564_ = v_reuseFailAlloc_1565_;
goto v_reusejp_1563_;
}
v_reusejp_1563_:
{
return v___x_1564_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonPlainTermGoal_toJson(lean_object* v_x_1569_){
_start:
{
lean_object* v_goal_1570_; lean_object* v_range_1571_; lean_object* v___x_1573_; uint8_t v_isShared_1574_; uint8_t v_isSharedCheck_1591_; 
v_goal_1570_ = lean_ctor_get(v_x_1569_, 0);
v_range_1571_ = lean_ctor_get(v_x_1569_, 1);
v_isSharedCheck_1591_ = !lean_is_exclusive(v_x_1569_);
if (v_isSharedCheck_1591_ == 0)
{
v___x_1573_ = v_x_1569_;
v_isShared_1574_ = v_isSharedCheck_1591_;
goto v_resetjp_1572_;
}
else
{
lean_inc(v_range_1571_);
lean_inc(v_goal_1570_);
lean_dec(v_x_1569_);
v___x_1573_ = lean_box(0);
v_isShared_1574_ = v_isSharedCheck_1591_;
goto v_resetjp_1572_;
}
v_resetjp_1572_:
{
lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1578_; 
v___x_1575_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__0));
v___x_1576_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1576_, 0, v_goal_1570_);
if (v_isShared_1574_ == 0)
{
lean_ctor_set(v___x_1573_, 1, v___x_1576_);
lean_ctor_set(v___x_1573_, 0, v___x_1575_);
v___x_1578_ = v___x_1573_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v___x_1575_);
lean_ctor_set(v_reuseFailAlloc_1590_, 1, v___x_1576_);
v___x_1578_ = v_reuseFailAlloc_1590_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; 
v___x_1579_ = lean_box(0);
v___x_1580_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1580_, 0, v___x_1578_);
lean_ctor_set(v___x_1580_, 1, v___x_1579_);
v___x_1581_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__0));
v___x_1582_ = l_Lean_Lsp_instToJsonRange_toJson(v_range_1571_);
v___x_1583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1583_, 0, v___x_1581_);
lean_ctor_set(v___x_1583_, 1, v___x_1582_);
v___x_1584_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1584_, 0, v___x_1583_);
lean_ctor_set(v___x_1584_, 1, v___x_1579_);
v___x_1585_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1585_, 0, v___x_1584_);
lean_ctor_set(v___x_1585_, 1, v___x_1579_);
v___x_1586_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1586_, 0, v___x_1580_);
lean_ctor_set(v___x_1586_, 1, v___x_1585_);
v___x_1587_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0));
v___x_1588_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_1586_, v___x_1587_);
v___x_1589_ = l_Lean_Json_mkObj(v___x_1588_);
lean_dec(v___x_1588_);
return v___x_1589_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonModuleHierarchyOptions_fromJson___redArg(){
_start:
{
lean_object* v___x_1597_; 
v___x_1597_ = ((lean_object*)(l_Lean_Lsp_instFromJsonModuleHierarchyOptions_fromJson___redArg___closed__0));
return v___x_1597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonModuleHierarchyOptions_fromJson___redArg___boxed(lean_object* v___dummy_1598_){
_start:
{
lean_object* v_res_1599_; 
v_res_1599_ = l_Lean_Lsp_instFromJsonModuleHierarchyOptions_fromJson___redArg();
return v_res_1599_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonModuleHierarchyOptions_fromJson___closed__0(void){
_start:
{
lean_object* v___x_1600_; 
v___x_1600_ = l_Lean_Lsp_instFromJsonModuleHierarchyOptions_fromJson___redArg();
return v___x_1600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonModuleHierarchyOptions_fromJson(lean_object* v_json_1601_){
_start:
{
lean_object* v___x_1602_; 
v___x_1602_ = lean_obj_once(&l_Lean_Lsp_instFromJsonModuleHierarchyOptions_fromJson___closed__0, &l_Lean_Lsp_instFromJsonModuleHierarchyOptions_fromJson___closed__0_once, _init_l_Lean_Lsp_instFromJsonModuleHierarchyOptions_fromJson___closed__0);
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
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonModuleHierarchyOptions_toJson___redArg(){
_start:
{
lean_object* v___x_1608_; 
v___x_1608_ = lean_obj_once(&l_Lean_Lsp_instToJsonWaitForILeans_toJson___redArg___closed__1, &l_Lean_Lsp_instToJsonWaitForILeans_toJson___redArg___closed__1_once, _init_l_Lean_Lsp_instToJsonWaitForILeans_toJson___redArg___closed__1);
return v___x_1608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonModuleHierarchyOptions_toJson___redArg___boxed(lean_object* v___dummy_1609_){
_start:
{
lean_object* v_res_1610_; 
v_res_1610_ = l_Lean_Lsp_instToJsonModuleHierarchyOptions_toJson___redArg();
return v_res_1610_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonModuleHierarchyOptions_toJson___closed__0(void){
_start:
{
lean_object* v___x_1611_; 
v___x_1611_ = l_Lean_Lsp_instToJsonModuleHierarchyOptions_toJson___redArg();
return v___x_1611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonModuleHierarchyOptions_toJson(lean_object* v_x_1612_){
_start:
{
lean_object* v___x_1613_; 
v___x_1613_ = lean_obj_once(&l_Lean_Lsp_instToJsonModuleHierarchyOptions_toJson___closed__0, &l_Lean_Lsp_instToJsonModuleHierarchyOptions_toJson___closed__0_once, _init_l_Lean_Lsp_instToJsonModuleHierarchyOptions_toJson___closed__0);
return v___x_1613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonHighlightMatchesOptions_fromJson___redArg(){
_start:
{
lean_object* v___x_1619_; 
v___x_1619_ = ((lean_object*)(l_Lean_Lsp_instFromJsonHighlightMatchesOptions_fromJson___redArg___closed__0));
return v___x_1619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonHighlightMatchesOptions_fromJson___redArg___boxed(lean_object* v___dummy_1620_){
_start:
{
lean_object* v_res_1621_; 
v_res_1621_ = l_Lean_Lsp_instFromJsonHighlightMatchesOptions_fromJson___redArg();
return v_res_1621_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonHighlightMatchesOptions_fromJson___closed__0(void){
_start:
{
lean_object* v___x_1622_; 
v___x_1622_ = l_Lean_Lsp_instFromJsonHighlightMatchesOptions_fromJson___redArg();
return v___x_1622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonHighlightMatchesOptions_fromJson(lean_object* v_json_1623_){
_start:
{
lean_object* v___x_1624_; 
v___x_1624_ = lean_obj_once(&l_Lean_Lsp_instFromJsonHighlightMatchesOptions_fromJson___closed__0, &l_Lean_Lsp_instFromJsonHighlightMatchesOptions_fromJson___closed__0_once, _init_l_Lean_Lsp_instFromJsonHighlightMatchesOptions_fromJson___closed__0);
return v___x_1624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonHighlightMatchesOptions_fromJson___boxed(lean_object* v_json_1625_){
_start:
{
lean_object* v_res_1626_; 
v_res_1626_ = l_Lean_Lsp_instFromJsonHighlightMatchesOptions_fromJson(v_json_1625_);
lean_dec(v_json_1625_);
return v_res_1626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonHighlightMatchesOptions_toJson___redArg(){
_start:
{
lean_object* v___x_1630_; 
v___x_1630_ = lean_obj_once(&l_Lean_Lsp_instToJsonWaitForILeans_toJson___redArg___closed__1, &l_Lean_Lsp_instToJsonWaitForILeans_toJson___redArg___closed__1_once, _init_l_Lean_Lsp_instToJsonWaitForILeans_toJson___redArg___closed__1);
return v___x_1630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonHighlightMatchesOptions_toJson___redArg___boxed(lean_object* v___dummy_1631_){
_start:
{
lean_object* v_res_1632_; 
v_res_1632_ = l_Lean_Lsp_instToJsonHighlightMatchesOptions_toJson___redArg();
return v_res_1632_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonHighlightMatchesOptions_toJson___closed__0(void){
_start:
{
lean_object* v___x_1633_; 
v___x_1633_ = l_Lean_Lsp_instToJsonHighlightMatchesOptions_toJson___redArg();
return v___x_1633_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonHighlightMatchesOptions_toJson(lean_object* v_x_1634_){
_start:
{
lean_object* v___x_1635_; 
v___x_1635_ = lean_obj_once(&l_Lean_Lsp_instToJsonHighlightMatchesOptions_toJson___closed__0, &l_Lean_Lsp_instToJsonHighlightMatchesOptions_toJson___closed__0_once, _init_l_Lean_Lsp_instToJsonHighlightMatchesOptions_toJson___closed__0);
return v___x_1635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__1_spec__2(lean_object* v_x_1640_){
_start:
{
if (lean_obj_tag(v_x_1640_) == 0)
{
lean_object* v___x_1641_; 
v___x_1641_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__1_spec__2___closed__0));
return v___x_1641_;
}
else
{
lean_object* v___x_1642_; 
v___x_1642_ = l_Lean_Lsp_instFromJsonRpcWireFormat_fromJson(v_x_1640_);
if (lean_obj_tag(v___x_1642_) == 0)
{
lean_object* v_a_1643_; lean_object* v___x_1645_; uint8_t v_isShared_1646_; uint8_t v_isSharedCheck_1650_; 
v_a_1643_ = lean_ctor_get(v___x_1642_, 0);
v_isSharedCheck_1650_ = !lean_is_exclusive(v___x_1642_);
if (v_isSharedCheck_1650_ == 0)
{
v___x_1645_ = v___x_1642_;
v_isShared_1646_ = v_isSharedCheck_1650_;
goto v_resetjp_1644_;
}
else
{
lean_inc(v_a_1643_);
lean_dec(v___x_1642_);
v___x_1645_ = lean_box(0);
v_isShared_1646_ = v_isSharedCheck_1650_;
goto v_resetjp_1644_;
}
v_resetjp_1644_:
{
lean_object* v___x_1648_; 
if (v_isShared_1646_ == 0)
{
v___x_1648_ = v___x_1645_;
goto v_reusejp_1647_;
}
else
{
lean_object* v_reuseFailAlloc_1649_; 
v_reuseFailAlloc_1649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1649_, 0, v_a_1643_);
v___x_1648_ = v_reuseFailAlloc_1649_;
goto v_reusejp_1647_;
}
v_reusejp_1647_:
{
return v___x_1648_;
}
}
}
else
{
lean_object* v_a_1651_; lean_object* v___x_1653_; uint8_t v_isShared_1654_; uint8_t v_isSharedCheck_1659_; 
v_a_1651_ = lean_ctor_get(v___x_1642_, 0);
v_isSharedCheck_1659_ = !lean_is_exclusive(v___x_1642_);
if (v_isSharedCheck_1659_ == 0)
{
v___x_1653_ = v___x_1642_;
v_isShared_1654_ = v_isSharedCheck_1659_;
goto v_resetjp_1652_;
}
else
{
lean_inc(v_a_1651_);
lean_dec(v___x_1642_);
v___x_1653_ = lean_box(0);
v_isShared_1654_ = v_isSharedCheck_1659_;
goto v_resetjp_1652_;
}
v_resetjp_1652_:
{
lean_object* v___x_1655_; lean_object* v___x_1657_; 
v___x_1655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1655_, 0, v_a_1651_);
if (v_isShared_1654_ == 0)
{
lean_ctor_set(v___x_1653_, 0, v___x_1655_);
v___x_1657_ = v___x_1653_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v___x_1655_);
v___x_1657_ = v_reuseFailAlloc_1658_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
return v___x_1657_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__1(lean_object* v_j_1660_, lean_object* v_k_1661_){
_start:
{
lean_object* v___x_1662_; lean_object* v___x_1663_; 
v___x_1662_ = l_Lean_Json_getObjValD(v_j_1660_, v_k_1661_);
v___x_1663_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__1_spec__2(v___x_1662_);
return v___x_1663_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__1___boxed(lean_object* v_j_1664_, lean_object* v_k_1665_){
_start:
{
lean_object* v_res_1666_; 
v_res_1666_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__1(v_j_1664_, v_k_1665_);
lean_dec_ref(v_k_1665_);
return v_res_1666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__0_spec__0(lean_object* v_x_1669_){
_start:
{
if (lean_obj_tag(v_x_1669_) == 0)
{
lean_object* v___x_1670_; 
v___x_1670_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__0_spec__0___closed__0));
return v___x_1670_;
}
else
{
lean_object* v___x_1671_; lean_object* v_a_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; 
v___x_1671_ = lean_obj_once(&l_Lean_Lsp_instFromJsonHighlightMatchesOptions_fromJson___closed__0, &l_Lean_Lsp_instFromJsonHighlightMatchesOptions_fromJson___closed__0_once, _init_l_Lean_Lsp_instFromJsonHighlightMatchesOptions_fromJson___closed__0);
v_a_1672_ = lean_ctor_get(v___x_1671_, 0);
lean_inc(v_a_1672_);
v___x_1673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1673_, 0, v_a_1672_);
v___x_1674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1674_, 0, v___x_1673_);
return v___x_1674_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__0_spec__0___boxed(lean_object* v_x_1675_){
_start:
{
lean_object* v_res_1676_; 
v_res_1676_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__0_spec__0(v_x_1675_);
lean_dec(v_x_1675_);
return v_res_1676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__0(lean_object* v_j_1677_, lean_object* v_k_1678_){
_start:
{
lean_object* v___x_1679_; lean_object* v___x_1680_; 
v___x_1679_ = l_Lean_Json_getObjValD(v_j_1677_, v_k_1678_);
v___x_1680_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__0_spec__0(v___x_1679_);
lean_dec(v___x_1679_);
return v___x_1680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__0___boxed(lean_object* v_j_1681_, lean_object* v_k_1682_){
_start:
{
lean_object* v_res_1683_; 
v_res_1683_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__0(v_j_1681_, v_k_1682_);
lean_dec_ref(v_k_1682_);
return v_res_1683_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__3(void){
_start:
{
uint8_t v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; 
v___x_1690_ = 1;
v___x_1691_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__2));
v___x_1692_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1691_, v___x_1690_);
return v___x_1692_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__4(void){
_start:
{
lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; 
v___x_1693_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6));
v___x_1694_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__3, &l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__3);
v___x_1695_ = lean_string_append(v___x_1694_, v___x_1693_);
return v___x_1695_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__7(void){
_start:
{
uint8_t v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; 
v___x_1699_ = 1;
v___x_1700_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__6));
v___x_1701_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1700_, v___x_1699_);
return v___x_1701_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__8(void){
_start:
{
lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; 
v___x_1702_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__7, &l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__7);
v___x_1703_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__4, &l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__4);
v___x_1704_ = lean_string_append(v___x_1703_, v___x_1702_);
return v___x_1704_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__9(void){
_start:
{
lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; 
v___x_1705_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_1706_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__8, &l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__8);
v___x_1707_ = lean_string_append(v___x_1706_, v___x_1705_);
return v___x_1707_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__13(void){
_start:
{
uint8_t v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; 
v___x_1712_ = 1;
v___x_1713_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__12));
v___x_1714_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1713_, v___x_1712_);
return v___x_1714_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__14(void){
_start:
{
lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; 
v___x_1715_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__13, &l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__13);
v___x_1716_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__4, &l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__4);
v___x_1717_ = lean_string_append(v___x_1716_, v___x_1715_);
return v___x_1717_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__15(void){
_start:
{
lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; 
v___x_1718_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_1719_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__14, &l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__14_once, _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__14);
v___x_1720_ = lean_string_append(v___x_1719_, v___x_1718_);
return v___x_1720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonRpcOptions_fromJson(lean_object* v_json_1721_){
_start:
{
lean_object* v___x_1722_; lean_object* v___x_1723_; 
v___x_1722_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__0));
lean_inc(v_json_1721_);
v___x_1723_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__0(v_json_1721_, v___x_1722_);
if (lean_obj_tag(v___x_1723_) == 0)
{
lean_object* v_a_1724_; lean_object* v___x_1726_; uint8_t v_isShared_1727_; uint8_t v_isSharedCheck_1733_; 
lean_dec(v_json_1721_);
v_a_1724_ = lean_ctor_get(v___x_1723_, 0);
v_isSharedCheck_1733_ = !lean_is_exclusive(v___x_1723_);
if (v_isSharedCheck_1733_ == 0)
{
v___x_1726_ = v___x_1723_;
v_isShared_1727_ = v_isSharedCheck_1733_;
goto v_resetjp_1725_;
}
else
{
lean_inc(v_a_1724_);
lean_dec(v___x_1723_);
v___x_1726_ = lean_box(0);
v_isShared_1727_ = v_isSharedCheck_1733_;
goto v_resetjp_1725_;
}
v_resetjp_1725_:
{
lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1731_; 
v___x_1728_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__9, &l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__9);
v___x_1729_ = lean_string_append(v___x_1728_, v_a_1724_);
lean_dec(v_a_1724_);
if (v_isShared_1727_ == 0)
{
lean_ctor_set(v___x_1726_, 0, v___x_1729_);
v___x_1731_ = v___x_1726_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1732_; 
v_reuseFailAlloc_1732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1732_, 0, v___x_1729_);
v___x_1731_ = v_reuseFailAlloc_1732_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
return v___x_1731_;
}
}
}
else
{
if (lean_obj_tag(v___x_1723_) == 0)
{
lean_object* v_a_1734_; lean_object* v___x_1736_; uint8_t v_isShared_1737_; uint8_t v_isSharedCheck_1741_; 
lean_dec(v_json_1721_);
v_a_1734_ = lean_ctor_get(v___x_1723_, 0);
v_isSharedCheck_1741_ = !lean_is_exclusive(v___x_1723_);
if (v_isSharedCheck_1741_ == 0)
{
v___x_1736_ = v___x_1723_;
v_isShared_1737_ = v_isSharedCheck_1741_;
goto v_resetjp_1735_;
}
else
{
lean_inc(v_a_1734_);
lean_dec(v___x_1723_);
v___x_1736_ = lean_box(0);
v_isShared_1737_ = v_isSharedCheck_1741_;
goto v_resetjp_1735_;
}
v_resetjp_1735_:
{
lean_object* v___x_1739_; 
if (v_isShared_1737_ == 0)
{
lean_ctor_set_tag(v___x_1736_, 0);
v___x_1739_ = v___x_1736_;
goto v_reusejp_1738_;
}
else
{
lean_object* v_reuseFailAlloc_1740_; 
v_reuseFailAlloc_1740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1740_, 0, v_a_1734_);
v___x_1739_ = v_reuseFailAlloc_1740_;
goto v_reusejp_1738_;
}
v_reusejp_1738_:
{
return v___x_1739_;
}
}
}
else
{
lean_object* v_a_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; 
v_a_1742_ = lean_ctor_get(v___x_1723_, 0);
lean_inc(v_a_1742_);
lean_dec_ref_known(v___x_1723_, 1);
v___x_1743_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__10));
v___x_1744_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__1(v_json_1721_, v___x_1743_);
if (lean_obj_tag(v___x_1744_) == 0)
{
lean_object* v_a_1745_; lean_object* v___x_1747_; uint8_t v_isShared_1748_; uint8_t v_isSharedCheck_1754_; 
lean_dec(v_a_1742_);
v_a_1745_ = lean_ctor_get(v___x_1744_, 0);
v_isSharedCheck_1754_ = !lean_is_exclusive(v___x_1744_);
if (v_isSharedCheck_1754_ == 0)
{
v___x_1747_ = v___x_1744_;
v_isShared_1748_ = v_isSharedCheck_1754_;
goto v_resetjp_1746_;
}
else
{
lean_inc(v_a_1745_);
lean_dec(v___x_1744_);
v___x_1747_ = lean_box(0);
v_isShared_1748_ = v_isSharedCheck_1754_;
goto v_resetjp_1746_;
}
v_resetjp_1746_:
{
lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1752_; 
v___x_1749_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__15, &l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__15_once, _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__15);
v___x_1750_ = lean_string_append(v___x_1749_, v_a_1745_);
lean_dec(v_a_1745_);
if (v_isShared_1748_ == 0)
{
lean_ctor_set(v___x_1747_, 0, v___x_1750_);
v___x_1752_ = v___x_1747_;
goto v_reusejp_1751_;
}
else
{
lean_object* v_reuseFailAlloc_1753_; 
v_reuseFailAlloc_1753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1753_, 0, v___x_1750_);
v___x_1752_ = v_reuseFailAlloc_1753_;
goto v_reusejp_1751_;
}
v_reusejp_1751_:
{
return v___x_1752_;
}
}
}
else
{
if (lean_obj_tag(v___x_1744_) == 0)
{
lean_object* v_a_1755_; lean_object* v___x_1757_; uint8_t v_isShared_1758_; uint8_t v_isSharedCheck_1762_; 
lean_dec(v_a_1742_);
v_a_1755_ = lean_ctor_get(v___x_1744_, 0);
v_isSharedCheck_1762_ = !lean_is_exclusive(v___x_1744_);
if (v_isSharedCheck_1762_ == 0)
{
v___x_1757_ = v___x_1744_;
v_isShared_1758_ = v_isSharedCheck_1762_;
goto v_resetjp_1756_;
}
else
{
lean_inc(v_a_1755_);
lean_dec(v___x_1744_);
v___x_1757_ = lean_box(0);
v_isShared_1758_ = v_isSharedCheck_1762_;
goto v_resetjp_1756_;
}
v_resetjp_1756_:
{
lean_object* v___x_1760_; 
if (v_isShared_1758_ == 0)
{
lean_ctor_set_tag(v___x_1757_, 0);
v___x_1760_ = v___x_1757_;
goto v_reusejp_1759_;
}
else
{
lean_object* v_reuseFailAlloc_1761_; 
v_reuseFailAlloc_1761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1761_, 0, v_a_1755_);
v___x_1760_ = v_reuseFailAlloc_1761_;
goto v_reusejp_1759_;
}
v_reusejp_1759_:
{
return v___x_1760_;
}
}
}
else
{
lean_object* v_a_1763_; lean_object* v___x_1765_; uint8_t v_isShared_1766_; uint8_t v_isSharedCheck_1771_; 
v_a_1763_ = lean_ctor_get(v___x_1744_, 0);
v_isSharedCheck_1771_ = !lean_is_exclusive(v___x_1744_);
if (v_isSharedCheck_1771_ == 0)
{
v___x_1765_ = v___x_1744_;
v_isShared_1766_ = v_isSharedCheck_1771_;
goto v_resetjp_1764_;
}
else
{
lean_inc(v_a_1763_);
lean_dec(v___x_1744_);
v___x_1765_ = lean_box(0);
v_isShared_1766_ = v_isSharedCheck_1771_;
goto v_resetjp_1764_;
}
v_resetjp_1764_:
{
lean_object* v___x_1767_; lean_object* v___x_1769_; 
v___x_1767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1767_, 0, v_a_1742_);
lean_ctor_set(v___x_1767_, 1, v_a_1763_);
if (v_isShared_1766_ == 0)
{
lean_ctor_set(v___x_1765_, 0, v___x_1767_);
v___x_1769_ = v___x_1765_;
goto v_reusejp_1768_;
}
else
{
lean_object* v_reuseFailAlloc_1770_; 
v_reuseFailAlloc_1770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1770_, 0, v___x_1767_);
v___x_1769_ = v_reuseFailAlloc_1770_;
goto v_reusejp_1768_;
}
v_reusejp_1768_:
{
return v___x_1769_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonRpcOptions_toJson_spec__0(lean_object* v_k_1774_, lean_object* v_x_1775_){
_start:
{
if (lean_obj_tag(v_x_1775_) == 0)
{
lean_object* v___x_1776_; 
lean_dec_ref(v_k_1774_);
v___x_1776_ = lean_box(0);
return v___x_1776_;
}
else
{
lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; 
v___x_1777_ = lean_obj_once(&l_Lean_Lsp_instToJsonHighlightMatchesOptions_toJson___closed__0, &l_Lean_Lsp_instToJsonHighlightMatchesOptions_toJson___closed__0_once, _init_l_Lean_Lsp_instToJsonHighlightMatchesOptions_toJson___closed__0);
v___x_1778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1778_, 0, v_k_1774_);
lean_ctor_set(v___x_1778_, 1, v___x_1777_);
v___x_1779_ = lean_box(0);
v___x_1780_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1780_, 0, v___x_1778_);
lean_ctor_set(v___x_1780_, 1, v___x_1779_);
return v___x_1780_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonRpcOptions_toJson_spec__0___boxed(lean_object* v_k_1781_, lean_object* v_x_1782_){
_start:
{
lean_object* v_res_1783_; 
v_res_1783_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonRpcOptions_toJson_spec__0(v_k_1781_, v_x_1782_);
lean_dec(v_x_1782_);
return v_res_1783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonRpcOptions_toJson_spec__1(lean_object* v_k_1784_, lean_object* v_x_1785_){
_start:
{
if (lean_obj_tag(v_x_1785_) == 0)
{
lean_object* v___x_1786_; 
lean_dec_ref(v_k_1784_);
v___x_1786_ = lean_box(0);
return v___x_1786_;
}
else
{
lean_object* v_val_1787_; uint8_t v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; 
v_val_1787_ = lean_ctor_get(v_x_1785_, 0);
v___x_1788_ = lean_unbox(v_val_1787_);
v___x_1789_ = l_Lean_Lsp_instToJsonRpcWireFormat_toJson(v___x_1788_);
v___x_1790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1790_, 0, v_k_1784_);
lean_ctor_set(v___x_1790_, 1, v___x_1789_);
v___x_1791_ = lean_box(0);
v___x_1792_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1792_, 0, v___x_1790_);
lean_ctor_set(v___x_1792_, 1, v___x_1791_);
return v___x_1792_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonRpcOptions_toJson_spec__1___boxed(lean_object* v_k_1793_, lean_object* v_x_1794_){
_start:
{
lean_object* v_res_1795_; 
v_res_1795_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonRpcOptions_toJson_spec__1(v_k_1793_, v_x_1794_);
lean_dec(v_x_1794_);
return v_res_1795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRpcOptions_toJson(lean_object* v_x_1796_){
_start:
{
lean_object* v_highlightMatchesProvider_x3f_1797_; lean_object* v_rpcWireFormat_x3f_1798_; lean_object* v___x_1800_; uint8_t v_isShared_1801_; uint8_t v_isSharedCheck_1814_; 
v_highlightMatchesProvider_x3f_1797_ = lean_ctor_get(v_x_1796_, 0);
v_rpcWireFormat_x3f_1798_ = lean_ctor_get(v_x_1796_, 1);
v_isSharedCheck_1814_ = !lean_is_exclusive(v_x_1796_);
if (v_isSharedCheck_1814_ == 0)
{
v___x_1800_ = v_x_1796_;
v_isShared_1801_ = v_isSharedCheck_1814_;
goto v_resetjp_1799_;
}
else
{
lean_inc(v_rpcWireFormat_x3f_1798_);
lean_inc(v_highlightMatchesProvider_x3f_1797_);
lean_dec(v_x_1796_);
v___x_1800_ = lean_box(0);
v_isShared_1801_ = v_isSharedCheck_1814_;
goto v_resetjp_1799_;
}
v_resetjp_1799_:
{
lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1808_; 
v___x_1802_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__0));
v___x_1803_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonRpcOptions_toJson_spec__0(v___x_1802_, v_highlightMatchesProvider_x3f_1797_);
lean_dec(v_highlightMatchesProvider_x3f_1797_);
v___x_1804_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__10));
v___x_1805_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonRpcOptions_toJson_spec__1(v___x_1804_, v_rpcWireFormat_x3f_1798_);
lean_dec(v_rpcWireFormat_x3f_1798_);
v___x_1806_ = lean_box(0);
if (v_isShared_1801_ == 0)
{
lean_ctor_set_tag(v___x_1800_, 1);
lean_ctor_set(v___x_1800_, 1, v___x_1806_);
lean_ctor_set(v___x_1800_, 0, v___x_1805_);
v___x_1808_ = v___x_1800_;
goto v_reusejp_1807_;
}
else
{
lean_object* v_reuseFailAlloc_1813_; 
v_reuseFailAlloc_1813_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1813_, 0, v___x_1805_);
lean_ctor_set(v_reuseFailAlloc_1813_, 1, v___x_1806_);
v___x_1808_ = v_reuseFailAlloc_1813_;
goto v_reusejp_1807_;
}
v_reusejp_1807_:
{
lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; 
v___x_1809_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1809_, 0, v___x_1803_);
lean_ctor_set(v___x_1809_, 1, v___x_1808_);
v___x_1810_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0));
v___x_1811_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_1809_, v___x_1810_);
v___x_1812_ = l_Lean_Json_mkObj(v___x_1811_);
lean_dec(v___x_1811_);
return v___x_1812_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModule_fromJson_spec__0_spec__0(lean_object* v_x_1819_){
_start:
{
if (lean_obj_tag(v_x_1819_) == 0)
{
lean_object* v___x_1820_; 
v___x_1820_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModule_fromJson_spec__0_spec__0___closed__0));
return v___x_1820_;
}
else
{
lean_object* v___x_1821_; lean_object* v___x_1822_; 
v___x_1821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1821_, 0, v_x_1819_);
v___x_1822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1822_, 0, v___x_1821_);
return v___x_1822_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModule_fromJson_spec__0(lean_object* v_j_1823_, lean_object* v_k_1824_){
_start:
{
lean_object* v___x_1825_; lean_object* v___x_1826_; 
v___x_1825_ = l_Lean_Json_getObjValD(v_j_1823_, v_k_1824_);
v___x_1826_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModule_fromJson_spec__0_spec__0(v___x_1825_);
return v___x_1826_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModule_fromJson_spec__0___boxed(lean_object* v_j_1827_, lean_object* v_k_1828_){
_start:
{
lean_object* v_res_1829_; 
v_res_1829_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModule_fromJson_spec__0(v_j_1827_, v_k_1828_);
lean_dec_ref(v_k_1828_);
return v_res_1829_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__3(void){
_start:
{
uint8_t v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; 
v___x_1836_ = 1;
v___x_1837_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__2));
v___x_1838_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1837_, v___x_1836_);
return v___x_1838_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__4(void){
_start:
{
lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; 
v___x_1839_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6));
v___x_1840_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__3);
v___x_1841_ = lean_string_append(v___x_1840_, v___x_1839_);
return v___x_1841_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__6(void){
_start:
{
uint8_t v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; 
v___x_1844_ = 1;
v___x_1845_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__5));
v___x_1846_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1845_, v___x_1844_);
return v___x_1846_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__7(void){
_start:
{
lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; 
v___x_1847_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__6);
v___x_1848_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__4);
v___x_1849_ = lean_string_append(v___x_1848_, v___x_1847_);
return v___x_1849_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__8(void){
_start:
{
lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; 
v___x_1850_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_1851_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__7);
v___x_1852_ = lean_string_append(v___x_1851_, v___x_1850_);
return v___x_1852_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__9(void){
_start:
{
lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; 
v___x_1853_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__6, &l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__6);
v___x_1854_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__4);
v___x_1855_ = lean_string_append(v___x_1854_, v___x_1853_);
return v___x_1855_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__10(void){
_start:
{
lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; 
v___x_1856_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_1857_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__9, &l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__9);
v___x_1858_ = lean_string_append(v___x_1857_, v___x_1856_);
return v___x_1858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanModule_fromJson(lean_object* v_json_1860_){
_start:
{
lean_object* v___x_1861_; lean_object* v___x_1862_; 
v___x_1861_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__0));
lean_inc(v_json_1860_);
v___x_1862_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson_spec__0(v_json_1860_, v___x_1861_);
if (lean_obj_tag(v___x_1862_) == 0)
{
lean_object* v_a_1863_; lean_object* v___x_1865_; uint8_t v_isShared_1866_; uint8_t v_isSharedCheck_1872_; 
lean_dec(v_json_1860_);
v_a_1863_ = lean_ctor_get(v___x_1862_, 0);
v_isSharedCheck_1872_ = !lean_is_exclusive(v___x_1862_);
if (v_isSharedCheck_1872_ == 0)
{
v___x_1865_ = v___x_1862_;
v_isShared_1866_ = v_isSharedCheck_1872_;
goto v_resetjp_1864_;
}
else
{
lean_inc(v_a_1863_);
lean_dec(v___x_1862_);
v___x_1865_ = lean_box(0);
v_isShared_1866_ = v_isSharedCheck_1872_;
goto v_resetjp_1864_;
}
v_resetjp_1864_:
{
lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1870_; 
v___x_1867_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__8);
v___x_1868_ = lean_string_append(v___x_1867_, v_a_1863_);
lean_dec(v_a_1863_);
if (v_isShared_1866_ == 0)
{
lean_ctor_set(v___x_1865_, 0, v___x_1868_);
v___x_1870_ = v___x_1865_;
goto v_reusejp_1869_;
}
else
{
lean_object* v_reuseFailAlloc_1871_; 
v_reuseFailAlloc_1871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1871_, 0, v___x_1868_);
v___x_1870_ = v_reuseFailAlloc_1871_;
goto v_reusejp_1869_;
}
v_reusejp_1869_:
{
return v___x_1870_;
}
}
}
else
{
if (lean_obj_tag(v___x_1862_) == 0)
{
lean_object* v_a_1873_; lean_object* v___x_1875_; uint8_t v_isShared_1876_; uint8_t v_isSharedCheck_1880_; 
lean_dec(v_json_1860_);
v_a_1873_ = lean_ctor_get(v___x_1862_, 0);
v_isSharedCheck_1880_ = !lean_is_exclusive(v___x_1862_);
if (v_isSharedCheck_1880_ == 0)
{
v___x_1875_ = v___x_1862_;
v_isShared_1876_ = v_isSharedCheck_1880_;
goto v_resetjp_1874_;
}
else
{
lean_inc(v_a_1873_);
lean_dec(v___x_1862_);
v___x_1875_ = lean_box(0);
v_isShared_1876_ = v_isSharedCheck_1880_;
goto v_resetjp_1874_;
}
v_resetjp_1874_:
{
lean_object* v___x_1878_; 
if (v_isShared_1876_ == 0)
{
lean_ctor_set_tag(v___x_1875_, 0);
v___x_1878_ = v___x_1875_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1879_; 
v_reuseFailAlloc_1879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1879_, 0, v_a_1873_);
v___x_1878_ = v_reuseFailAlloc_1879_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
return v___x_1878_;
}
}
}
else
{
lean_object* v_a_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; 
v_a_1881_ = lean_ctor_get(v___x_1862_, 0);
lean_inc(v_a_1881_);
lean_dec_ref_known(v___x_1862_, 1);
v___x_1882_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__0));
lean_inc(v_json_1860_);
v___x_1883_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson_spec__0(v_json_1860_, v___x_1882_);
if (lean_obj_tag(v___x_1883_) == 0)
{
lean_object* v_a_1884_; lean_object* v___x_1886_; uint8_t v_isShared_1887_; uint8_t v_isSharedCheck_1893_; 
lean_dec(v_a_1881_);
lean_dec(v_json_1860_);
v_a_1884_ = lean_ctor_get(v___x_1883_, 0);
v_isSharedCheck_1893_ = !lean_is_exclusive(v___x_1883_);
if (v_isSharedCheck_1893_ == 0)
{
v___x_1886_ = v___x_1883_;
v_isShared_1887_ = v_isSharedCheck_1893_;
goto v_resetjp_1885_;
}
else
{
lean_inc(v_a_1884_);
lean_dec(v___x_1883_);
v___x_1886_ = lean_box(0);
v_isShared_1887_ = v_isSharedCheck_1893_;
goto v_resetjp_1885_;
}
v_resetjp_1885_:
{
lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1891_; 
v___x_1888_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__10, &l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__10);
v___x_1889_ = lean_string_append(v___x_1888_, v_a_1884_);
lean_dec(v_a_1884_);
if (v_isShared_1887_ == 0)
{
lean_ctor_set(v___x_1886_, 0, v___x_1889_);
v___x_1891_ = v___x_1886_;
goto v_reusejp_1890_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v___x_1889_);
v___x_1891_ = v_reuseFailAlloc_1892_;
goto v_reusejp_1890_;
}
v_reusejp_1890_:
{
return v___x_1891_;
}
}
}
else
{
if (lean_obj_tag(v___x_1883_) == 0)
{
lean_object* v_a_1894_; lean_object* v___x_1896_; uint8_t v_isShared_1897_; uint8_t v_isSharedCheck_1901_; 
lean_dec(v_a_1881_);
lean_dec(v_json_1860_);
v_a_1894_ = lean_ctor_get(v___x_1883_, 0);
v_isSharedCheck_1901_ = !lean_is_exclusive(v___x_1883_);
if (v_isSharedCheck_1901_ == 0)
{
v___x_1896_ = v___x_1883_;
v_isShared_1897_ = v_isSharedCheck_1901_;
goto v_resetjp_1895_;
}
else
{
lean_inc(v_a_1894_);
lean_dec(v___x_1883_);
v___x_1896_ = lean_box(0);
v_isShared_1897_ = v_isSharedCheck_1901_;
goto v_resetjp_1895_;
}
v_resetjp_1895_:
{
lean_object* v___x_1899_; 
if (v_isShared_1897_ == 0)
{
lean_ctor_set_tag(v___x_1896_, 0);
v___x_1899_ = v___x_1896_;
goto v_reusejp_1898_;
}
else
{
lean_object* v_reuseFailAlloc_1900_; 
v_reuseFailAlloc_1900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1900_, 0, v_a_1894_);
v___x_1899_ = v_reuseFailAlloc_1900_;
goto v_reusejp_1898_;
}
v_reusejp_1898_:
{
return v___x_1899_;
}
}
}
else
{
lean_object* v_a_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v_a_1905_; lean_object* v___x_1907_; uint8_t v_isShared_1908_; uint8_t v_isSharedCheck_1913_; 
v_a_1902_ = lean_ctor_get(v___x_1883_, 0);
lean_inc(v_a_1902_);
lean_dec_ref_known(v___x_1883_, 1);
v___x_1903_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__11));
v___x_1904_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModule_fromJson_spec__0(v_json_1860_, v___x_1903_);
v_a_1905_ = lean_ctor_get(v___x_1904_, 0);
v_isSharedCheck_1913_ = !lean_is_exclusive(v___x_1904_);
if (v_isSharedCheck_1913_ == 0)
{
v___x_1907_ = v___x_1904_;
v_isShared_1908_ = v_isSharedCheck_1913_;
goto v_resetjp_1906_;
}
else
{
lean_inc(v_a_1905_);
lean_dec(v___x_1904_);
v___x_1907_ = lean_box(0);
v_isShared_1908_ = v_isSharedCheck_1913_;
goto v_resetjp_1906_;
}
v_resetjp_1906_:
{
lean_object* v___x_1909_; lean_object* v___x_1911_; 
v___x_1909_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1909_, 0, v_a_1881_);
lean_ctor_set(v___x_1909_, 1, v_a_1902_);
lean_ctor_set(v___x_1909_, 2, v_a_1905_);
if (v_isShared_1908_ == 0)
{
lean_ctor_set(v___x_1907_, 0, v___x_1909_);
v___x_1911_ = v___x_1907_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v___x_1909_);
v___x_1911_ = v_reuseFailAlloc_1912_;
goto v_reusejp_1910_;
}
v_reusejp_1910_:
{
return v___x_1911_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanModule_toJson_spec__0(lean_object* v_k_1916_, lean_object* v_x_1917_){
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
lean_object* v_val_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; 
v_val_1919_ = lean_ctor_get(v_x_1917_, 0);
lean_inc(v_val_1919_);
v___x_1920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1920_, 0, v_k_1916_);
lean_ctor_set(v___x_1920_, 1, v_val_1919_);
v___x_1921_ = lean_box(0);
v___x_1922_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1922_, 0, v___x_1920_);
lean_ctor_set(v___x_1922_, 1, v___x_1921_);
return v___x_1922_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanModule_toJson_spec__0___boxed(lean_object* v_k_1923_, lean_object* v_x_1924_){
_start:
{
lean_object* v_res_1925_; 
v_res_1925_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanModule_toJson_spec__0(v_k_1923_, v_x_1924_);
lean_dec(v_x_1924_);
return v_res_1925_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanModule_toJson(lean_object* v_x_1926_){
_start:
{
lean_object* v_name_1927_; lean_object* v_uri_1928_; lean_object* v_data_x3f_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; 
v_name_1927_ = lean_ctor_get(v_x_1926_, 0);
v_uri_1928_ = lean_ctor_get(v_x_1926_, 1);
v_data_x3f_1929_ = lean_ctor_get(v_x_1926_, 2);
v___x_1930_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__0));
lean_inc_ref(v_name_1927_);
v___x_1931_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1931_, 0, v_name_1927_);
v___x_1932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1932_, 0, v___x_1930_);
lean_ctor_set(v___x_1932_, 1, v___x_1931_);
v___x_1933_ = lean_box(0);
v___x_1934_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1934_, 0, v___x_1932_);
lean_ctor_set(v___x_1934_, 1, v___x_1933_);
v___x_1935_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__0));
lean_inc_ref(v_uri_1928_);
v___x_1936_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1936_, 0, v_uri_1928_);
v___x_1937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1937_, 0, v___x_1935_);
lean_ctor_set(v___x_1937_, 1, v___x_1936_);
v___x_1938_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1938_, 0, v___x_1937_);
lean_ctor_set(v___x_1938_, 1, v___x_1933_);
v___x_1939_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__11));
v___x_1940_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanModule_toJson_spec__0(v___x_1939_, v_data_x3f_1929_);
v___x_1941_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1941_, 0, v___x_1940_);
lean_ctor_set(v___x_1941_, 1, v___x_1933_);
v___x_1942_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1942_, 0, v___x_1938_);
lean_ctor_set(v___x_1942_, 1, v___x_1941_);
v___x_1943_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1943_, 0, v___x_1934_);
lean_ctor_set(v___x_1943_, 1, v___x_1942_);
v___x_1944_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0));
v___x_1945_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_1943_, v___x_1944_);
v___x_1946_ = l_Lean_Json_mkObj(v___x_1945_);
lean_dec(v___x_1945_);
return v___x_1946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanModule_toJson___boxed(lean_object* v_x_1947_){
_start:
{
lean_object* v_res_1948_; 
v_res_1948_ = l_Lean_Lsp_instToJsonLeanModule_toJson(v_x_1947_);
lean_dec_ref(v_x_1947_);
return v_res_1948_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__2(void){
_start:
{
uint8_t v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; 
v___x_1956_ = 1;
v___x_1957_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__1));
v___x_1958_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1957_, v___x_1956_);
return v___x_1958_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__3(void){
_start:
{
lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; 
v___x_1959_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6));
v___x_1960_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__2, &l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__2);
v___x_1961_ = lean_string_append(v___x_1960_, v___x_1959_);
return v___x_1961_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; 
v___x_1962_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9, &l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9);
v___x_1963_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__3);
v___x_1964_ = lean_string_append(v___x_1963_, v___x_1962_);
return v___x_1964_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__5(void){
_start:
{
lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; 
v___x_1965_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_1966_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__4);
v___x_1967_ = lean_string_append(v___x_1966_, v___x_1965_);
return v___x_1967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson(lean_object* v_json_1968_){
_start:
{
lean_object* v___x_1969_; lean_object* v___x_1970_; 
v___x_1969_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__0));
v___x_1970_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoalParams_fromJson_spec__0(v_json_1968_, v___x_1969_);
if (lean_obj_tag(v___x_1970_) == 0)
{
lean_object* v_a_1971_; lean_object* v___x_1973_; uint8_t v_isShared_1974_; uint8_t v_isSharedCheck_1980_; 
v_a_1971_ = lean_ctor_get(v___x_1970_, 0);
v_isSharedCheck_1980_ = !lean_is_exclusive(v___x_1970_);
if (v_isSharedCheck_1980_ == 0)
{
v___x_1973_ = v___x_1970_;
v_isShared_1974_ = v_isSharedCheck_1980_;
goto v_resetjp_1972_;
}
else
{
lean_inc(v_a_1971_);
lean_dec(v___x_1970_);
v___x_1973_ = lean_box(0);
v_isShared_1974_ = v_isSharedCheck_1980_;
goto v_resetjp_1972_;
}
v_resetjp_1972_:
{
lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1978_; 
v___x_1975_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__5, &l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__5);
v___x_1976_ = lean_string_append(v___x_1975_, v_a_1971_);
lean_dec(v_a_1971_);
if (v_isShared_1974_ == 0)
{
lean_ctor_set(v___x_1973_, 0, v___x_1976_);
v___x_1978_ = v___x_1973_;
goto v_reusejp_1977_;
}
else
{
lean_object* v_reuseFailAlloc_1979_; 
v_reuseFailAlloc_1979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1979_, 0, v___x_1976_);
v___x_1978_ = v_reuseFailAlloc_1979_;
goto v_reusejp_1977_;
}
v_reusejp_1977_:
{
return v___x_1978_;
}
}
}
else
{
if (lean_obj_tag(v___x_1970_) == 0)
{
lean_object* v_a_1981_; lean_object* v___x_1983_; uint8_t v_isShared_1984_; uint8_t v_isSharedCheck_1988_; 
v_a_1981_ = lean_ctor_get(v___x_1970_, 0);
v_isSharedCheck_1988_ = !lean_is_exclusive(v___x_1970_);
if (v_isSharedCheck_1988_ == 0)
{
v___x_1983_ = v___x_1970_;
v_isShared_1984_ = v_isSharedCheck_1988_;
goto v_resetjp_1982_;
}
else
{
lean_inc(v_a_1981_);
lean_dec(v___x_1970_);
v___x_1983_ = lean_box(0);
v_isShared_1984_ = v_isSharedCheck_1988_;
goto v_resetjp_1982_;
}
v_resetjp_1982_:
{
lean_object* v___x_1986_; 
if (v_isShared_1984_ == 0)
{
lean_ctor_set_tag(v___x_1983_, 0);
v___x_1986_ = v___x_1983_;
goto v_reusejp_1985_;
}
else
{
lean_object* v_reuseFailAlloc_1987_; 
v_reuseFailAlloc_1987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1987_, 0, v_a_1981_);
v___x_1986_ = v_reuseFailAlloc_1987_;
goto v_reusejp_1985_;
}
v_reusejp_1985_:
{
return v___x_1986_;
}
}
}
else
{
lean_object* v_a_1989_; lean_object* v___x_1991_; uint8_t v_isShared_1992_; uint8_t v_isSharedCheck_1996_; 
v_a_1989_ = lean_ctor_get(v___x_1970_, 0);
v_isSharedCheck_1996_ = !lean_is_exclusive(v___x_1970_);
if (v_isSharedCheck_1996_ == 0)
{
v___x_1991_ = v___x_1970_;
v_isShared_1992_ = v_isSharedCheck_1996_;
goto v_resetjp_1990_;
}
else
{
lean_inc(v_a_1989_);
lean_dec(v___x_1970_);
v___x_1991_ = lean_box(0);
v_isShared_1992_ = v_isSharedCheck_1996_;
goto v_resetjp_1990_;
}
v_resetjp_1990_:
{
lean_object* v___x_1994_; 
if (v_isShared_1992_ == 0)
{
v___x_1994_ = v___x_1991_;
goto v_reusejp_1993_;
}
else
{
lean_object* v_reuseFailAlloc_1995_; 
v_reuseFailAlloc_1995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1995_, 0, v_a_1989_);
v___x_1994_ = v_reuseFailAlloc_1995_;
goto v_reusejp_1993_;
}
v_reusejp_1993_:
{
return v___x_1994_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanPrepareModuleHierarchyParams_toJson(lean_object* v_x_1999_){
_start:
{
lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; 
v___x_2000_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__0));
v___x_2001_ = l_Lean_Lsp_instToJsonTextDocumentIdentifier_toJson(v_x_1999_);
v___x_2002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2002_, 0, v___x_2000_);
lean_ctor_set(v___x_2002_, 1, v___x_2001_);
v___x_2003_ = lean_box(0);
v___x_2004_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2004_, 0, v___x_2002_);
lean_ctor_set(v___x_2004_, 1, v___x_2003_);
v___x_2005_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2005_, 0, v___x_2004_);
lean_ctor_set(v___x_2005_, 1, v___x_2003_);
v___x_2006_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0));
v___x_2007_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_2005_, v___x_2006_);
v___x_2008_ = l_Lean_Json_mkObj(v___x_2007_);
lean_dec(v___x_2007_);
return v___x_2008_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanImportMetaKind_ctorIdx___impl(uint8_t v_x_2011_){
_start:
{
lean_object* v___x_2012_; lean_object* v___x_2013_; 
v___x_2012_ = lean_box(v_x_2011_);
v___x_2013_ = lean_obj_tag_nat(v___x_2012_);
lean_dec(v___x_2012_);
return v___x_2013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanImportMetaKind_ctorIdx___impl___boxed(lean_object* v_x_2014_){
_start:
{
uint8_t v_x_4__boxed_2015_; lean_object* v_res_2016_; 
v_x_4__boxed_2015_ = lean_unbox(v_x_2014_);
v_res_2016_ = l_Lean_Lsp_LeanImportMetaKind_ctorIdx___impl(v_x_4__boxed_2015_);
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

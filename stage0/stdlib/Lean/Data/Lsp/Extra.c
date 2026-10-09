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
lean_object* l_Lean_Lsp_DependencyBuildMode_ctorIdx___impl(uint8_t v_x_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(v_x_1_);
v___x_3_ = lean_obj_tag_nat(v___x_2_);
lean_dec(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT void l_Lean_Lsp_DependencyBuildMode_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_1_ = stack[0].m_num;
lean_object* v_res_4_;
v_res_4_ = l_Lean_Lsp_DependencyBuildMode_ctorIdx___impl(v_x_1_);
stack->m_obj
 = v_res_4_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DependencyBuildMode_ctorIdx___impl___boxed(lean_object* v_x_5_){
_start:
{
uint8_t v_x_4__boxed_6_; lean_object* v_res_7_; 
v_x_4__boxed_6_ = lean_unbox(v_x_5_);
v_res_7_ = l_Lean_Lsp_DependencyBuildMode_ctorIdx___impl(v_x_4__boxed_6_);
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
lean_object* l_Lean_Lsp_DependencyBuildMode_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, uint8_t v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_inc(v_k_15_);
return v_k_15_;
}
}
LEAN_EXPORT void l_Lean_Lsp_DependencyBuildMode_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_12_ = stack[1].m_obj;
uint8_t v_t_13_ = stack[2].m_num;
lean_object* v_k_15_ = stack[4].m_obj;
lean_object* v_res_16_;
v_res_16_ = l_Lean_Lsp_DependencyBuildMode_ctorElim(lean_box(0), v_ctorIdx_12_, v_t_13_, lean_box(0), v_k_15_);
stack->m_obj
 = v_res_16_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DependencyBuildMode_ctorElim___boxed(lean_object* v_motive_17_, lean_object* v_ctorIdx_18_, lean_object* v_t_19_, lean_object* v_h_20_, lean_object* v_k_21_){
_start:
{
uint8_t v_t_boxed_22_; lean_object* v_res_23_; 
v_t_boxed_22_ = lean_unbox(v_t_19_);
v_res_23_ = l_Lean_Lsp_DependencyBuildMode_ctorElim(v_motive_17_, v_ctorIdx_18_, v_t_boxed_22_, v_h_20_, v_k_21_);
lean_dec(v_k_21_);
lean_dec(v_ctorIdx_18_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DependencyBuildMode_always_elim___redArg(lean_object* v_always_24_){
_start:
{
lean_inc(v_always_24_);
return v_always_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DependencyBuildMode_always_elim___redArg___boxed(lean_object* v_always_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Lean_Lsp_DependencyBuildMode_always_elim___redArg(v_always_25_);
lean_dec(v_always_25_);
return v_res_26_;
}
}
lean_object* l_Lean_Lsp_DependencyBuildMode_always_elim(lean_object* v_motive_27_, uint8_t v_t_28_, lean_object* v_h_29_, lean_object* v_always_30_){
_start:
{
lean_inc(v_always_30_);
return v_always_30_;
}
}
LEAN_EXPORT void l_Lean_Lsp_DependencyBuildMode_always_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_28_ = stack[1].m_num;
lean_object* v_always_30_ = stack[3].m_obj;
lean_object* v_res_31_;
v_res_31_ = l_Lean_Lsp_DependencyBuildMode_always_elim(lean_box(0), v_t_28_, lean_box(0), v_always_30_);
stack->m_obj
 = v_res_31_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DependencyBuildMode_always_elim___boxed(lean_object* v_motive_32_, lean_object* v_t_33_, lean_object* v_h_34_, lean_object* v_always_35_){
_start:
{
uint8_t v_t_boxed_36_; lean_object* v_res_37_; 
v_t_boxed_36_ = lean_unbox(v_t_33_);
v_res_37_ = l_Lean_Lsp_DependencyBuildMode_always_elim(v_motive_32_, v_t_boxed_36_, v_h_34_, v_always_35_);
lean_dec(v_always_35_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DependencyBuildMode_once_elim___redArg(lean_object* v_once_38_){
_start:
{
lean_inc(v_once_38_);
return v_once_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DependencyBuildMode_once_elim___redArg___boxed(lean_object* v_once_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Lean_Lsp_DependencyBuildMode_once_elim___redArg(v_once_39_);
lean_dec(v_once_39_);
return v_res_40_;
}
}
lean_object* l_Lean_Lsp_DependencyBuildMode_once_elim(lean_object* v_motive_41_, uint8_t v_t_42_, lean_object* v_h_43_, lean_object* v_once_44_){
_start:
{
lean_inc(v_once_44_);
return v_once_44_;
}
}
LEAN_EXPORT void l_Lean_Lsp_DependencyBuildMode_once_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_42_ = stack[1].m_num;
lean_object* v_once_44_ = stack[3].m_obj;
lean_object* v_res_45_;
v_res_45_ = l_Lean_Lsp_DependencyBuildMode_once_elim(lean_box(0), v_t_42_, lean_box(0), v_once_44_);
stack->m_obj
 = v_res_45_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DependencyBuildMode_once_elim___boxed(lean_object* v_motive_46_, lean_object* v_t_47_, lean_object* v_h_48_, lean_object* v_once_49_){
_start:
{
uint8_t v_t_boxed_50_; lean_object* v_res_51_; 
v_t_boxed_50_ = lean_unbox(v_t_47_);
v_res_51_ = l_Lean_Lsp_DependencyBuildMode_once_elim(v_motive_46_, v_t_boxed_50_, v_h_48_, v_once_49_);
lean_dec(v_once_49_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DependencyBuildMode_never_elim___redArg(lean_object* v_never_52_){
_start:
{
lean_inc(v_never_52_);
return v_never_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DependencyBuildMode_never_elim___redArg___boxed(lean_object* v_never_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l_Lean_Lsp_DependencyBuildMode_never_elim___redArg(v_never_53_);
lean_dec(v_never_53_);
return v_res_54_;
}
}
lean_object* l_Lean_Lsp_DependencyBuildMode_never_elim(lean_object* v_motive_55_, uint8_t v_t_56_, lean_object* v_h_57_, lean_object* v_never_58_){
_start:
{
lean_inc(v_never_58_);
return v_never_58_;
}
}
LEAN_EXPORT void l_Lean_Lsp_DependencyBuildMode_never_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_56_ = stack[1].m_num;
lean_object* v_never_58_ = stack[3].m_obj;
lean_object* v_res_59_;
v_res_59_ = l_Lean_Lsp_DependencyBuildMode_never_elim(lean_box(0), v_t_56_, lean_box(0), v_never_58_);
stack->m_obj
 = v_res_59_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DependencyBuildMode_never_elim___boxed(lean_object* v_motive_60_, lean_object* v_t_61_, lean_object* v_h_62_, lean_object* v_never_63_){
_start:
{
uint8_t v_t_boxed_64_; lean_object* v_res_65_; 
v_t_boxed_64_ = lean_unbox(v_t_61_);
v_res_65_ = l_Lean_Lsp_DependencyBuildMode_never_elim(v_motive_60_, v_t_boxed_64_, v_h_62_, v_never_63_);
lean_dec(v_never_63_);
return v_res_65_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson(lean_object* v_json_84_){
_start:
{
lean_object* v___x_85_; 
v___x_85_ = l_Lean_Json_getTag_x3f(v_json_84_);
if (lean_obj_tag(v___x_85_) == 0)
{
lean_object* v___x_86_; 
v___x_86_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__1));
return v___x_86_;
}
else
{
lean_object* v_val_87_; lean_object* v___x_88_; uint8_t v___x_89_; 
v_val_87_ = lean_ctor_get(v___x_85_, 0);
lean_inc(v_val_87_);
lean_dec_ref_known(v___x_85_, 1);
v___x_88_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__2));
v___x_89_ = lean_string_dec_eq(v_val_87_, v___x_88_);
if (v___x_89_ == 0)
{
lean_object* v___x_90_; uint8_t v___x_91_; 
v___x_90_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__3));
v___x_91_ = lean_string_dec_eq(v_val_87_, v___x_90_);
if (v___x_91_ == 0)
{
lean_object* v___x_92_; uint8_t v___x_93_; 
v___x_92_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__4));
v___x_93_ = lean_string_dec_eq(v_val_87_, v___x_92_);
lean_dec(v_val_87_);
if (v___x_93_ == 0)
{
lean_object* v___x_94_; 
v___x_94_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__6));
return v___x_94_;
}
else
{
lean_object* v___x_95_; 
v___x_95_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__7));
return v___x_95_;
}
}
else
{
lean_object* v___x_96_; 
lean_dec(v_val_87_);
v___x_96_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__8));
return v___x_96_;
}
}
else
{
lean_object* v___x_97_; 
lean_dec(v_val_87_);
v___x_97_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDependencyBuildMode_fromJson___closed__9));
return v___x_97_;
}
}
}
}
lean_object* l_Lean_Lsp_instToJsonDependencyBuildMode_toJson(uint8_t v_x_106_){
_start:
{
switch(v_x_106_)
{
case 0:
{
lean_object* v___x_107_; 
v___x_107_ = ((lean_object*)(l_Lean_Lsp_instToJsonDependencyBuildMode_toJson___closed__0));
return v___x_107_;
}
case 1:
{
lean_object* v___x_108_; 
v___x_108_ = ((lean_object*)(l_Lean_Lsp_instToJsonDependencyBuildMode_toJson___closed__1));
return v___x_108_;
}
default: 
{
lean_object* v___x_109_; 
v___x_109_ = ((lean_object*)(l_Lean_Lsp_instToJsonDependencyBuildMode_toJson___closed__2));
return v___x_109_;
}
}
}
}
LEAN_EXPORT void l_Lean_Lsp_instToJsonDependencyBuildMode_toJson_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_106_ = stack[0].m_num;
lean_object* v_res_110_;
v_res_110_ = l_Lean_Lsp_instToJsonDependencyBuildMode_toJson(v_x_106_);
stack->m_obj
 = v_res_110_;
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
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson_spec__1_spec__1(lean_object* v_x_127_){
_start:
{
if (lean_obj_tag(v_x_127_) == 0)
{
lean_object* v___x_128_; 
v___x_128_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson_spec__1_spec__1___closed__0));
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
v___x_150_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson_spec__1_spec__1(v___x_149_);
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
lean_dec_ref_known(v___x_196_, 1);
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
lean_dec_ref_known(v_a_259_, 2);
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
lean_dec_ref_known(v___x_342_, 1);
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
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonWaitForDiagnostics___lam__0(lean_object* v_x_421_){
_start:
{
lean_object* v___x_422_; 
v___x_422_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWaitForDiagnostics___lam__0___closed__0));
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonWaitForDiagnostics___lam__0___boxed(lean_object* v_x_423_){
_start:
{
lean_object* v_res_424_; 
v_res_424_ = l_Lean_Lsp_instFromJsonWaitForDiagnostics___lam__0(v_x_423_);
lean_dec(v_x_423_);
return v_res_424_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonWaitForDiagnostics___lam__0___closed__0(void){
_start:
{
lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_427_ = lean_box(0);
v___x_428_ = l_Lean_Json_mkObj(v___x_427_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonWaitForDiagnostics___lam__0(lean_object* v_x_429_){
_start:
{
lean_object* v___x_430_; 
v___x_430_ = lean_obj_once(&l_Lean_Lsp_instToJsonWaitForDiagnostics___lam__0___closed__0, &l_Lean_Lsp_instToJsonWaitForDiagnostics___lam__0___closed__0_once, _init_l_Lean_Lsp_instToJsonWaitForDiagnostics___lam__0___closed__0);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForILeansParams_fromJson_spec__0_spec__0(lean_object* v_x_435_){
_start:
{
if (lean_obj_tag(v_x_435_) == 0)
{
lean_object* v___x_436_; 
v___x_436_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForILeansParams_fromJson_spec__0_spec__0___closed__0));
return v___x_436_;
}
else
{
lean_object* v___x_437_; 
v___x_437_ = l_Lean_Json_getStr_x3f(v_x_435_);
if (lean_obj_tag(v___x_437_) == 0)
{
lean_object* v_a_438_; lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_445_; 
v_a_438_ = lean_ctor_get(v___x_437_, 0);
v_isSharedCheck_445_ = !lean_is_exclusive(v___x_437_);
if (v_isSharedCheck_445_ == 0)
{
v___x_440_ = v___x_437_;
v_isShared_441_ = v_isSharedCheck_445_;
goto v_resetjp_439_;
}
else
{
lean_inc(v_a_438_);
lean_dec(v___x_437_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_445_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
lean_object* v___x_443_; 
if (v_isShared_441_ == 0)
{
v___x_443_ = v___x_440_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v_a_438_);
v___x_443_ = v_reuseFailAlloc_444_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
return v___x_443_;
}
}
}
else
{
lean_object* v_a_446_; lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_454_; 
v_a_446_ = lean_ctor_get(v___x_437_, 0);
v_isSharedCheck_454_ = !lean_is_exclusive(v___x_437_);
if (v_isSharedCheck_454_ == 0)
{
v___x_448_ = v___x_437_;
v_isShared_449_ = v_isSharedCheck_454_;
goto v_resetjp_447_;
}
else
{
lean_inc(v_a_446_);
lean_dec(v___x_437_);
v___x_448_ = lean_box(0);
v_isShared_449_ = v_isSharedCheck_454_;
goto v_resetjp_447_;
}
v_resetjp_447_:
{
lean_object* v___x_450_; lean_object* v___x_452_; 
v___x_450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_450_, 0, v_a_446_);
if (v_isShared_449_ == 0)
{
lean_ctor_set(v___x_448_, 0, v___x_450_);
v___x_452_ = v___x_448_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v___x_450_);
v___x_452_ = v_reuseFailAlloc_453_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
return v___x_452_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForILeansParams_fromJson_spec__0(lean_object* v_j_455_, lean_object* v_k_456_){
_start:
{
lean_object* v___x_457_; lean_object* v___x_458_; 
v___x_457_ = l_Lean_Json_getObjValD(v_j_455_, v_k_456_);
v___x_458_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForILeansParams_fromJson_spec__0_spec__0(v___x_457_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForILeansParams_fromJson_spec__0___boxed(lean_object* v_j_459_, lean_object* v_k_460_){
_start:
{
lean_object* v_res_461_; 
v_res_461_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForILeansParams_fromJson_spec__0(v_j_459_, v_k_460_);
lean_dec_ref(v_k_460_);
return v_res_461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForILeansParams_fromJson_spec__1_spec__2(lean_object* v_x_464_){
_start:
{
if (lean_obj_tag(v_x_464_) == 0)
{
lean_object* v___x_465_; 
v___x_465_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForILeansParams_fromJson_spec__1_spec__2___closed__0));
return v___x_465_;
}
else
{
lean_object* v___x_466_; 
v___x_466_ = l_Lean_Json_getNat_x3f(v_x_464_);
if (lean_obj_tag(v___x_466_) == 0)
{
lean_object* v_a_467_; lean_object* v___x_469_; uint8_t v_isShared_470_; uint8_t v_isSharedCheck_474_; 
v_a_467_ = lean_ctor_get(v___x_466_, 0);
v_isSharedCheck_474_ = !lean_is_exclusive(v___x_466_);
if (v_isSharedCheck_474_ == 0)
{
v___x_469_ = v___x_466_;
v_isShared_470_ = v_isSharedCheck_474_;
goto v_resetjp_468_;
}
else
{
lean_inc(v_a_467_);
lean_dec(v___x_466_);
v___x_469_ = lean_box(0);
v_isShared_470_ = v_isSharedCheck_474_;
goto v_resetjp_468_;
}
v_resetjp_468_:
{
lean_object* v___x_472_; 
if (v_isShared_470_ == 0)
{
v___x_472_ = v___x_469_;
goto v_reusejp_471_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v_a_467_);
v___x_472_ = v_reuseFailAlloc_473_;
goto v_reusejp_471_;
}
v_reusejp_471_:
{
return v___x_472_;
}
}
}
else
{
lean_object* v_a_475_; lean_object* v___x_477_; uint8_t v_isShared_478_; uint8_t v_isSharedCheck_483_; 
v_a_475_ = lean_ctor_get(v___x_466_, 0);
v_isSharedCheck_483_ = !lean_is_exclusive(v___x_466_);
if (v_isSharedCheck_483_ == 0)
{
v___x_477_ = v___x_466_;
v_isShared_478_ = v_isSharedCheck_483_;
goto v_resetjp_476_;
}
else
{
lean_inc(v_a_475_);
lean_dec(v___x_466_);
v___x_477_ = lean_box(0);
v_isShared_478_ = v_isSharedCheck_483_;
goto v_resetjp_476_;
}
v_resetjp_476_:
{
lean_object* v___x_479_; lean_object* v___x_481_; 
v___x_479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_479_, 0, v_a_475_);
if (v_isShared_478_ == 0)
{
lean_ctor_set(v___x_477_, 0, v___x_479_);
v___x_481_ = v___x_477_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v___x_479_);
v___x_481_ = v_reuseFailAlloc_482_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
return v___x_481_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForILeansParams_fromJson_spec__1(lean_object* v_j_484_, lean_object* v_k_485_){
_start:
{
lean_object* v___x_486_; lean_object* v___x_487_; 
v___x_486_ = l_Lean_Json_getObjValD(v_j_484_, v_k_485_);
v___x_487_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForILeansParams_fromJson_spec__1_spec__2(v___x_486_);
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForILeansParams_fromJson_spec__1___boxed(lean_object* v_j_488_, lean_object* v_k_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForILeansParams_fromJson_spec__1(v_j_488_, v_k_489_);
lean_dec_ref(v_k_489_);
return v_res_490_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__2(void){
_start:
{
uint8_t v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; 
v___x_496_ = 1;
v___x_497_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__1));
v___x_498_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_497_, v___x_496_);
return v___x_498_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__3(void){
_start:
{
lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_499_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6));
v___x_500_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__2, &l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__2);
v___x_501_ = lean_string_append(v___x_500_, v___x_499_);
return v___x_501_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__6(void){
_start:
{
uint8_t v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; 
v___x_505_ = 1;
v___x_506_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__5));
v___x_507_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_506_, v___x_505_);
return v___x_507_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__7(void){
_start:
{
lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; 
v___x_508_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__6, &l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__6);
v___x_509_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__3);
v___x_510_ = lean_string_append(v___x_509_, v___x_508_);
return v___x_510_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__8(void){
_start:
{
lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; 
v___x_511_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_512_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__7);
v___x_513_ = lean_string_append(v___x_512_, v___x_511_);
return v___x_513_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__11(void){
_start:
{
uint8_t v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; 
v___x_517_ = 1;
v___x_518_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__10));
v___x_519_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_518_, v___x_517_);
return v___x_519_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__12(void){
_start:
{
lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; 
v___x_520_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__11, &l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__11);
v___x_521_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__3);
v___x_522_ = lean_string_append(v___x_521_, v___x_520_);
return v___x_522_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__13(void){
_start:
{
lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; 
v___x_523_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_524_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__12, &l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__12);
v___x_525_ = lean_string_append(v___x_524_, v___x_523_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson(lean_object* v_json_526_){
_start:
{
lean_object* v___x_527_; lean_object* v___x_528_; 
v___x_527_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__0));
lean_inc(v_json_526_);
v___x_528_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForILeansParams_fromJson_spec__0(v_json_526_, v___x_527_);
if (lean_obj_tag(v___x_528_) == 0)
{
lean_object* v_a_529_; lean_object* v___x_531_; uint8_t v_isShared_532_; uint8_t v_isSharedCheck_538_; 
lean_dec(v_json_526_);
v_a_529_ = lean_ctor_get(v___x_528_, 0);
v_isSharedCheck_538_ = !lean_is_exclusive(v___x_528_);
if (v_isSharedCheck_538_ == 0)
{
v___x_531_ = v___x_528_;
v_isShared_532_ = v_isSharedCheck_538_;
goto v_resetjp_530_;
}
else
{
lean_inc(v_a_529_);
lean_dec(v___x_528_);
v___x_531_ = lean_box(0);
v_isShared_532_ = v_isSharedCheck_538_;
goto v_resetjp_530_;
}
v_resetjp_530_:
{
lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_536_; 
v___x_533_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__8);
v___x_534_ = lean_string_append(v___x_533_, v_a_529_);
lean_dec(v_a_529_);
if (v_isShared_532_ == 0)
{
lean_ctor_set(v___x_531_, 0, v___x_534_);
v___x_536_ = v___x_531_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v___x_534_);
v___x_536_ = v_reuseFailAlloc_537_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
return v___x_536_;
}
}
}
else
{
if (lean_obj_tag(v___x_528_) == 0)
{
lean_object* v_a_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_546_; 
lean_dec(v_json_526_);
v_a_539_ = lean_ctor_get(v___x_528_, 0);
v_isSharedCheck_546_ = !lean_is_exclusive(v___x_528_);
if (v_isSharedCheck_546_ == 0)
{
v___x_541_ = v___x_528_;
v_isShared_542_ = v_isSharedCheck_546_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_a_539_);
lean_dec(v___x_528_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_546_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v___x_544_; 
if (v_isShared_542_ == 0)
{
lean_ctor_set_tag(v___x_541_, 0);
v___x_544_ = v___x_541_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v_a_539_);
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
lean_object* v_a_547_; lean_object* v___x_548_; lean_object* v___x_549_; 
v_a_547_ = lean_ctor_get(v___x_528_, 0);
lean_inc(v_a_547_);
lean_dec_ref_known(v___x_528_, 1);
v___x_548_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__9));
v___x_549_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForILeansParams_fromJson_spec__1(v_json_526_, v___x_548_);
if (lean_obj_tag(v___x_549_) == 0)
{
lean_object* v_a_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_559_; 
lean_dec(v_a_547_);
v_a_550_ = lean_ctor_get(v___x_549_, 0);
v_isSharedCheck_559_ = !lean_is_exclusive(v___x_549_);
if (v_isSharedCheck_559_ == 0)
{
v___x_552_ = v___x_549_;
v_isShared_553_ = v_isSharedCheck_559_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_a_550_);
lean_dec(v___x_549_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_559_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_557_; 
v___x_554_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__13, &l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonWaitForILeansParams_fromJson___closed__13);
v___x_555_ = lean_string_append(v___x_554_, v_a_550_);
lean_dec(v_a_550_);
if (v_isShared_553_ == 0)
{
lean_ctor_set(v___x_552_, 0, v___x_555_);
v___x_557_ = v___x_552_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v___x_555_);
v___x_557_ = v_reuseFailAlloc_558_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
return v___x_557_;
}
}
}
else
{
if (lean_obj_tag(v___x_549_) == 0)
{
lean_object* v_a_560_; lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_567_; 
lean_dec(v_a_547_);
v_a_560_ = lean_ctor_get(v___x_549_, 0);
v_isSharedCheck_567_ = !lean_is_exclusive(v___x_549_);
if (v_isSharedCheck_567_ == 0)
{
v___x_562_ = v___x_549_;
v_isShared_563_ = v_isSharedCheck_567_;
goto v_resetjp_561_;
}
else
{
lean_inc(v_a_560_);
lean_dec(v___x_549_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_567_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
lean_object* v___x_565_; 
if (v_isShared_563_ == 0)
{
lean_ctor_set_tag(v___x_562_, 0);
v___x_565_ = v___x_562_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v_a_560_);
v___x_565_ = v_reuseFailAlloc_566_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
return v___x_565_;
}
}
}
else
{
lean_object* v_a_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_576_; 
v_a_568_ = lean_ctor_get(v___x_549_, 0);
v_isSharedCheck_576_ = !lean_is_exclusive(v___x_549_);
if (v_isSharedCheck_576_ == 0)
{
v___x_570_ = v___x_549_;
v_isShared_571_ = v_isSharedCheck_576_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_a_568_);
lean_dec(v___x_549_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_576_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
lean_object* v___x_572_; lean_object* v___x_574_; 
v___x_572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_572_, 0, v_a_547_);
lean_ctor_set(v___x_572_, 1, v_a_568_);
if (v_isShared_571_ == 0)
{
lean_ctor_set(v___x_570_, 0, v___x_572_);
v___x_574_ = v___x_570_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_575_; 
v_reuseFailAlloc_575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_575_, 0, v___x_572_);
v___x_574_ = v_reuseFailAlloc_575_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
return v___x_574_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonWaitForILeansParams_toJson_spec__0(lean_object* v_k_579_, lean_object* v_x_580_){
_start:
{
if (lean_obj_tag(v_x_580_) == 0)
{
lean_object* v___x_581_; 
lean_dec_ref(v_k_579_);
v___x_581_ = lean_box(0);
return v___x_581_;
}
else
{
lean_object* v_val_582_; lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_592_; 
v_val_582_ = lean_ctor_get(v_x_580_, 0);
v_isSharedCheck_592_ = !lean_is_exclusive(v_x_580_);
if (v_isSharedCheck_592_ == 0)
{
v___x_584_ = v_x_580_;
v_isShared_585_ = v_isSharedCheck_592_;
goto v_resetjp_583_;
}
else
{
lean_inc(v_val_582_);
lean_dec(v_x_580_);
v___x_584_ = lean_box(0);
v_isShared_585_ = v_isSharedCheck_592_;
goto v_resetjp_583_;
}
v_resetjp_583_:
{
lean_object* v___x_587_; 
if (v_isShared_585_ == 0)
{
lean_ctor_set_tag(v___x_584_, 3);
v___x_587_ = v___x_584_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v_val_582_);
v___x_587_ = v_reuseFailAlloc_591_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; 
v___x_588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_588_, 0, v_k_579_);
lean_ctor_set(v___x_588_, 1, v___x_587_);
v___x_589_ = lean_box(0);
v___x_590_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_590_, 0, v___x_588_);
lean_ctor_set(v___x_590_, 1, v___x_589_);
return v___x_590_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonWaitForILeansParams_toJson_spec__1(lean_object* v_k_593_, lean_object* v_x_594_){
_start:
{
if (lean_obj_tag(v_x_594_) == 0)
{
lean_object* v___x_595_; 
lean_dec_ref(v_k_593_);
v___x_595_ = lean_box(0);
return v___x_595_;
}
else
{
lean_object* v_val_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_607_; 
v_val_596_ = lean_ctor_get(v_x_594_, 0);
v_isSharedCheck_607_ = !lean_is_exclusive(v_x_594_);
if (v_isSharedCheck_607_ == 0)
{
v___x_598_ = v_x_594_;
v_isShared_599_ = v_isSharedCheck_607_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_val_596_);
lean_dec(v_x_594_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_607_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v___x_600_; lean_object* v___x_602_; 
v___x_600_ = l_Lean_JsonNumber_fromNat(v_val_596_);
if (v_isShared_599_ == 0)
{
lean_ctor_set_tag(v___x_598_, 2);
lean_ctor_set(v___x_598_, 0, v___x_600_);
v___x_602_ = v___x_598_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v___x_600_);
v___x_602_ = v_reuseFailAlloc_606_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_603_, 0, v_k_593_);
lean_ctor_set(v___x_603_, 1, v___x_602_);
v___x_604_ = lean_box(0);
v___x_605_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_605_, 0, v___x_603_);
lean_ctor_set(v___x_605_, 1, v___x_604_);
return v___x_605_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonWaitForILeansParams_toJson(lean_object* v_x_608_){
_start:
{
lean_object* v_uri_x3f_609_; lean_object* v_version_x3f_610_; lean_object* v___x_612_; uint8_t v_isShared_613_; uint8_t v_isSharedCheck_626_; 
v_uri_x3f_609_ = lean_ctor_get(v_x_608_, 0);
v_version_x3f_610_ = lean_ctor_get(v_x_608_, 1);
v_isSharedCheck_626_ = !lean_is_exclusive(v_x_608_);
if (v_isSharedCheck_626_ == 0)
{
v___x_612_ = v_x_608_;
v_isShared_613_ = v_isSharedCheck_626_;
goto v_resetjp_611_;
}
else
{
lean_inc(v_version_x3f_610_);
lean_inc(v_uri_x3f_609_);
lean_dec(v_x_608_);
v___x_612_ = lean_box(0);
v_isShared_613_ = v_isSharedCheck_626_;
goto v_resetjp_611_;
}
v_resetjp_611_:
{
lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_620_; 
v___x_614_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__0));
v___x_615_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonWaitForILeansParams_toJson_spec__0(v___x_614_, v_uri_x3f_609_);
v___x_616_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__9));
v___x_617_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonWaitForILeansParams_toJson_spec__1(v___x_616_, v_version_x3f_610_);
v___x_618_ = lean_box(0);
if (v_isShared_613_ == 0)
{
lean_ctor_set_tag(v___x_612_, 1);
lean_ctor_set(v___x_612_, 1, v___x_618_);
lean_ctor_set(v___x_612_, 0, v___x_617_);
v___x_620_ = v___x_612_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v___x_617_);
lean_ctor_set(v_reuseFailAlloc_625_, 1, v___x_618_);
v___x_620_ = v_reuseFailAlloc_625_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; 
v___x_621_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_621_, 0, v___x_615_);
lean_ctor_set(v___x_621_, 1, v___x_620_);
v___x_622_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0));
v___x_623_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_621_, v___x_622_);
v___x_624_ = l_Lean_Json_mkObj(v___x_623_);
lean_dec(v___x_623_);
return v___x_624_;
}
}
}
}
lean_object* l_Lean_Lsp_instFromJsonWaitForILeans_fromJson___redArg(){
_start:
{
lean_object* v___x_632_; 
v___x_632_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWaitForILeans_fromJson___redArg___closed__0));
return v___x_632_;
}
}
LEAN_EXPORT void l_Lean_Lsp_instFromJsonWaitForILeans_fromJson___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_633_;
v_res_633_ = l_Lean_Lsp_instFromJsonWaitForILeans_fromJson___redArg();
stack->m_obj
 = v_res_633_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonWaitForILeans_fromJson___redArg___boxed(lean_object* v___dummy_634_){
_start:
{
lean_object* v_res_635_; 
v_res_635_ = l_Lean_Lsp_instFromJsonWaitForILeans_fromJson___redArg();
return v_res_635_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWaitForILeans_fromJson___closed__0(void){
_start:
{
lean_object* v___x_636_; 
v___x_636_ = l_Lean_Lsp_instFromJsonWaitForILeans_fromJson___redArg();
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonWaitForILeans_fromJson(lean_object* v_json_637_){
_start:
{
lean_object* v___x_638_; 
v___x_638_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWaitForILeans_fromJson___closed__0, &l_Lean_Lsp_instFromJsonWaitForILeans_fromJson___closed__0_once, _init_l_Lean_Lsp_instFromJsonWaitForILeans_fromJson___closed__0);
return v___x_638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonWaitForILeans_fromJson___boxed(lean_object* v_json_639_){
_start:
{
lean_object* v_res_640_; 
v_res_640_ = l_Lean_Lsp_instFromJsonWaitForILeans_fromJson(v_json_639_);
lean_dec(v_json_639_);
return v_res_640_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonWaitForILeans_toJson___redArg___closed__0(void){
_start:
{
lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_643_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0));
v___x_644_ = lean_box(0);
v___x_645_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_644_, v___x_643_);
return v___x_645_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonWaitForILeans_toJson___redArg___closed__1(void){
_start:
{
lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_646_ = lean_obj_once(&l_Lean_Lsp_instToJsonWaitForILeans_toJson___redArg___closed__0, &l_Lean_Lsp_instToJsonWaitForILeans_toJson___redArg___closed__0_once, _init_l_Lean_Lsp_instToJsonWaitForILeans_toJson___redArg___closed__0);
v___x_647_ = l_Lean_Json_mkObj(v___x_646_);
return v___x_647_;
}
}
lean_object* l_Lean_Lsp_instToJsonWaitForILeans_toJson___redArg(){
_start:
{
lean_object* v___x_649_; 
v___x_649_ = lean_obj_once(&l_Lean_Lsp_instToJsonWaitForILeans_toJson___redArg___closed__1, &l_Lean_Lsp_instToJsonWaitForILeans_toJson___redArg___closed__1_once, _init_l_Lean_Lsp_instToJsonWaitForILeans_toJson___redArg___closed__1);
return v___x_649_;
}
}
LEAN_EXPORT void l_Lean_Lsp_instToJsonWaitForILeans_toJson___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_650_;
v_res_650_ = l_Lean_Lsp_instToJsonWaitForILeans_toJson___redArg();
stack->m_obj
 = v_res_650_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonWaitForILeans_toJson___redArg___boxed(lean_object* v___dummy_651_){
_start:
{
lean_object* v_res_652_; 
v_res_652_ = l_Lean_Lsp_instToJsonWaitForILeans_toJson___redArg();
return v_res_652_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonWaitForILeans_toJson___closed__0(void){
_start:
{
lean_object* v___x_653_; 
v___x_653_ = l_Lean_Lsp_instToJsonWaitForILeans_toJson___redArg();
return v___x_653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonWaitForILeans_toJson(lean_object* v_x_654_){
_start:
{
lean_object* v___x_655_; 
v___x_655_ = lean_obj_once(&l_Lean_Lsp_instToJsonWaitForILeans_toJson___closed__0, &l_Lean_Lsp_instToJsonWaitForILeans_toJson___closed__0_once, _init_l_Lean_Lsp_instToJsonWaitForILeans_toJson___closed__0);
return v___x_655_;
}
}
lean_object* l_Lean_Lsp_LeanFileProgressKind_ctorIdx___impl(uint8_t v_x_658_){
_start:
{
lean_object* v___x_659_; lean_object* v___x_660_; 
v___x_659_ = lean_box(v_x_658_);
v___x_660_ = lean_obj_tag_nat(v___x_659_);
lean_dec(v___x_659_);
return v___x_660_;
}
}
LEAN_EXPORT void l_Lean_Lsp_LeanFileProgressKind_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_658_ = stack[0].m_num;
lean_object* v_res_661_;
v_res_661_ = l_Lean_Lsp_LeanFileProgressKind_ctorIdx___impl(v_x_658_);
stack->m_obj
 = v_res_661_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanFileProgressKind_ctorIdx___impl___boxed(lean_object* v_x_662_){
_start:
{
uint8_t v_x_4__boxed_663_; lean_object* v_res_664_; 
v_x_4__boxed_663_ = lean_unbox(v_x_662_);
v_res_664_ = l_Lean_Lsp_LeanFileProgressKind_ctorIdx___impl(v_x_4__boxed_663_);
return v_res_664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanFileProgressKind_ctorElim___redArg(lean_object* v_k_665_){
_start:
{
lean_inc(v_k_665_);
return v_k_665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanFileProgressKind_ctorElim___redArg___boxed(lean_object* v_k_666_){
_start:
{
lean_object* v_res_667_; 
v_res_667_ = l_Lean_Lsp_LeanFileProgressKind_ctorElim___redArg(v_k_666_);
lean_dec(v_k_666_);
return v_res_667_;
}
}
lean_object* l_Lean_Lsp_LeanFileProgressKind_ctorElim(lean_object* v_motive_668_, lean_object* v_ctorIdx_669_, uint8_t v_t_670_, lean_object* v_h_671_, lean_object* v_k_672_){
_start:
{
lean_inc(v_k_672_);
return v_k_672_;
}
}
LEAN_EXPORT void l_Lean_Lsp_LeanFileProgressKind_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_669_ = stack[1].m_obj;
uint8_t v_t_670_ = stack[2].m_num;
lean_object* v_k_672_ = stack[4].m_obj;
lean_object* v_res_673_;
v_res_673_ = l_Lean_Lsp_LeanFileProgressKind_ctorElim(lean_box(0), v_ctorIdx_669_, v_t_670_, lean_box(0), v_k_672_);
stack->m_obj
 = v_res_673_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanFileProgressKind_ctorElim___boxed(lean_object* v_motive_674_, lean_object* v_ctorIdx_675_, lean_object* v_t_676_, lean_object* v_h_677_, lean_object* v_k_678_){
_start:
{
uint8_t v_t_boxed_679_; lean_object* v_res_680_; 
v_t_boxed_679_ = lean_unbox(v_t_676_);
v_res_680_ = l_Lean_Lsp_LeanFileProgressKind_ctorElim(v_motive_674_, v_ctorIdx_675_, v_t_boxed_679_, v_h_677_, v_k_678_);
lean_dec(v_k_678_);
lean_dec(v_ctorIdx_675_);
return v_res_680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanFileProgressKind_processing_elim___redArg(lean_object* v_processing_681_){
_start:
{
lean_inc(v_processing_681_);
return v_processing_681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanFileProgressKind_processing_elim___redArg___boxed(lean_object* v_processing_682_){
_start:
{
lean_object* v_res_683_; 
v_res_683_ = l_Lean_Lsp_LeanFileProgressKind_processing_elim___redArg(v_processing_682_);
lean_dec(v_processing_682_);
return v_res_683_;
}
}
lean_object* l_Lean_Lsp_LeanFileProgressKind_processing_elim(lean_object* v_motive_684_, uint8_t v_t_685_, lean_object* v_h_686_, lean_object* v_processing_687_){
_start:
{
lean_inc(v_processing_687_);
return v_processing_687_;
}
}
LEAN_EXPORT void l_Lean_Lsp_LeanFileProgressKind_processing_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_685_ = stack[1].m_num;
lean_object* v_processing_687_ = stack[3].m_obj;
lean_object* v_res_688_;
v_res_688_ = l_Lean_Lsp_LeanFileProgressKind_processing_elim(lean_box(0), v_t_685_, lean_box(0), v_processing_687_);
stack->m_obj
 = v_res_688_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanFileProgressKind_processing_elim___boxed(lean_object* v_motive_689_, lean_object* v_t_690_, lean_object* v_h_691_, lean_object* v_processing_692_){
_start:
{
uint8_t v_t_boxed_693_; lean_object* v_res_694_; 
v_t_boxed_693_ = lean_unbox(v_t_690_);
v_res_694_ = l_Lean_Lsp_LeanFileProgressKind_processing_elim(v_motive_689_, v_t_boxed_693_, v_h_691_, v_processing_692_);
lean_dec(v_processing_692_);
return v_res_694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanFileProgressKind_fatalError_elim___redArg(lean_object* v_fatalError_695_){
_start:
{
lean_inc(v_fatalError_695_);
return v_fatalError_695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanFileProgressKind_fatalError_elim___redArg___boxed(lean_object* v_fatalError_696_){
_start:
{
lean_object* v_res_697_; 
v_res_697_ = l_Lean_Lsp_LeanFileProgressKind_fatalError_elim___redArg(v_fatalError_696_);
lean_dec(v_fatalError_696_);
return v_res_697_;
}
}
lean_object* l_Lean_Lsp_LeanFileProgressKind_fatalError_elim(lean_object* v_motive_698_, uint8_t v_t_699_, lean_object* v_h_700_, lean_object* v_fatalError_701_){
_start:
{
lean_inc(v_fatalError_701_);
return v_fatalError_701_;
}
}
LEAN_EXPORT void l_Lean_Lsp_LeanFileProgressKind_fatalError_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_699_ = stack[1].m_num;
lean_object* v_fatalError_701_ = stack[3].m_obj;
lean_object* v_res_702_;
v_res_702_ = l_Lean_Lsp_LeanFileProgressKind_fatalError_elim(lean_box(0), v_t_699_, lean_box(0), v_fatalError_701_);
stack->m_obj
 = v_res_702_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanFileProgressKind_fatalError_elim___boxed(lean_object* v_motive_703_, lean_object* v_t_704_, lean_object* v_h_705_, lean_object* v_fatalError_706_){
_start:
{
uint8_t v_t_boxed_707_; lean_object* v_res_708_; 
v_t_boxed_707_ = lean_unbox(v_t_704_);
v_res_708_ = l_Lean_Lsp_LeanFileProgressKind_fatalError_elim(v_motive_703_, v_t_boxed_707_, v_h_705_, v_fatalError_706_);
lean_dec(v_fatalError_706_);
return v_res_708_;
}
}
static uint8_t _init_l_Lean_Lsp_instInhabitedLeanFileProgressKind_default(void){
_start:
{
uint8_t v___x_709_; 
v___x_709_ = 0;
return v___x_709_;
}
}
static uint8_t _init_l_Lean_Lsp_instInhabitedLeanFileProgressKind(void){
_start:
{
uint8_t v___x_710_; 
v___x_710_ = 0;
return v___x_710_;
}
}
uint8_t l_Lean_Lsp_instBEqLeanFileProgressKind_beq(uint8_t v_x_711_, uint8_t v_y_712_){
_start:
{
lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; uint8_t v___x_717_; 
v___x_713_ = lean_box(v_x_711_);
v___x_714_ = lean_obj_tag_nat(v___x_713_);
lean_dec(v___x_713_);
v___x_715_ = lean_box(v_y_712_);
v___x_716_ = lean_obj_tag_nat(v___x_715_);
lean_dec(v___x_715_);
v___x_717_ = lean_nat_dec_eq(v___x_714_, v___x_716_);
return v___x_717_;
}
}
LEAN_EXPORT void l_Lean_Lsp_instBEqLeanFileProgressKind_beq_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_711_ = stack[0].m_num;
uint8_t v_y_712_ = stack[1].m_num;
uint8_t v_res_718_;
v_res_718_ = l_Lean_Lsp_instBEqLeanFileProgressKind_beq(v_x_711_, v_y_712_);
stack->m_num = v_res_718_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqLeanFileProgressKind_beq___boxed(lean_object* v_x_719_, lean_object* v_y_720_){
_start:
{
uint8_t v_x_24__boxed_721_; uint8_t v_y_25__boxed_722_; uint8_t v_res_723_; lean_object* v_r_724_; 
v_x_24__boxed_721_ = lean_unbox(v_x_719_);
v_y_25__boxed_722_ = lean_unbox(v_y_720_);
v_res_723_ = l_Lean_Lsp_instBEqLeanFileProgressKind_beq(v_x_24__boxed_721_, v_y_25__boxed_722_);
v_r_724_ = lean_box(v_res_723_);
return v_r_724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanFileProgressKind___lam__0(lean_object* v_j_735_){
_start:
{
lean_object* v___x_744_; 
lean_inc(v_j_735_);
v___x_744_ = l_Lean_Json_getNat_x3f(v_j_735_);
if (lean_obj_tag(v___x_744_) == 1)
{
lean_object* v_a_745_; lean_object* v___x_746_; uint8_t v___x_747_; 
v_a_745_ = lean_ctor_get(v___x_744_, 0);
lean_inc(v_a_745_);
lean_dec_ref_known(v___x_744_, 1);
v___x_746_ = lean_unsigned_to_nat(1u);
v___x_747_ = lean_nat_dec_eq(v_a_745_, v___x_746_);
if (v___x_747_ == 0)
{
lean_object* v___x_748_; uint8_t v___x_749_; 
v___x_748_ = lean_unsigned_to_nat(2u);
v___x_749_ = lean_nat_dec_eq(v_a_745_, v___x_748_);
lean_dec(v_a_745_);
if (v___x_749_ == 0)
{
goto v___jp_736_;
}
else
{
lean_object* v___x_750_; 
lean_dec(v_j_735_);
v___x_750_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressKind___lam__0___closed__2));
return v___x_750_;
}
}
else
{
lean_object* v___x_751_; 
lean_dec(v_a_745_);
lean_dec(v_j_735_);
v___x_751_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressKind___lam__0___closed__3));
return v___x_751_;
}
}
else
{
lean_dec_ref(v___x_744_);
goto v___jp_736_;
}
v___jp_736_:
{
lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; 
v___x_737_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressKind___lam__0___closed__0));
v___x_738_ = lean_unsigned_to_nat(80u);
v___x_739_ = l_Lean_Json_pretty(v_j_735_, v___x_738_);
v___x_740_ = lean_string_append(v___x_737_, v___x_739_);
lean_dec_ref(v___x_739_);
v___x_741_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressKind___lam__0___closed__1));
v___x_742_ = lean_string_append(v___x_740_, v___x_741_);
v___x_743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_743_, 0, v___x_742_);
return v___x_743_;
}
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__0(void){
_start:
{
lean_object* v___x_754_; lean_object* v___x_755_; 
v___x_754_ = lean_unsigned_to_nat(1u);
v___x_755_ = l_Lean_JsonNumber_fromNat(v___x_754_);
return v___x_755_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__1(void){
_start:
{
lean_object* v___x_756_; lean_object* v___x_757_; 
v___x_756_ = lean_obj_once(&l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__0, &l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__0_once, _init_l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__0);
v___x_757_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_757_, 0, v___x_756_);
return v___x_757_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__2(void){
_start:
{
lean_object* v___x_758_; lean_object* v___x_759_; 
v___x_758_ = lean_unsigned_to_nat(2u);
v___x_759_ = l_Lean_JsonNumber_fromNat(v___x_758_);
return v___x_759_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__3(void){
_start:
{
lean_object* v___x_760_; lean_object* v___x_761_; 
v___x_760_ = lean_obj_once(&l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__2, &l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__2_once, _init_l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__2);
v___x_761_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_761_, 0, v___x_760_);
return v___x_761_;
}
}
lean_object* l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0(uint8_t v_x_762_){
_start:
{
if (v_x_762_ == 0)
{
lean_object* v___x_763_; 
v___x_763_ = lean_obj_once(&l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__1, &l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__1_once, _init_l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__1);
return v___x_763_;
}
else
{
lean_object* v___x_764_; 
v___x_764_ = lean_obj_once(&l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__3, &l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__3_once, _init_l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__3);
return v___x_764_;
}
}
}
LEAN_EXPORT void l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_762_ = stack[0].m_num;
lean_object* v_res_765_;
v_res_765_ = l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0(v_x_762_);
stack->m_obj
 = v_res_765_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___boxed(lean_object* v_x_766_){
_start:
{
uint8_t v_x_56__boxed_767_; lean_object* v_res_768_; 
v_x_56__boxed_767_ = lean_unbox(v_x_766_);
v_res_768_ = l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0(v_x_56__boxed_767_);
return v_res_768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson_spec__0(lean_object* v_j_771_, lean_object* v_k_772_){
_start:
{
lean_object* v___x_773_; lean_object* v___x_774_; 
v___x_773_ = l_Lean_Json_getObjValD(v_j_771_, v_k_772_);
v___x_774_ = l_Lean_Lsp_instFromJsonRange_fromJson(v___x_773_);
return v___x_774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson_spec__0___boxed(lean_object* v_j_775_, lean_object* v_k_776_){
_start:
{
lean_object* v_res_777_; 
v_res_777_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson_spec__0(v_j_775_, v_k_776_);
lean_dec_ref(v_k_776_);
return v_res_777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson_spec__1(lean_object* v_j_778_, lean_object* v_k_779_){
_start:
{
lean_object* v___x_780_; lean_object* v___x_789_; 
v___x_780_ = l_Lean_Json_getObjValD(v_j_778_, v_k_779_);
lean_inc(v___x_780_);
v___x_789_ = l_Lean_Json_getNat_x3f(v___x_780_);
if (lean_obj_tag(v___x_789_) == 1)
{
lean_object* v_a_790_; lean_object* v___x_791_; uint8_t v___x_792_; 
v_a_790_ = lean_ctor_get(v___x_789_, 0);
lean_inc(v_a_790_);
lean_dec_ref_known(v___x_789_, 1);
v___x_791_ = lean_unsigned_to_nat(1u);
v___x_792_ = lean_nat_dec_eq(v_a_790_, v___x_791_);
if (v___x_792_ == 0)
{
lean_object* v___x_793_; uint8_t v___x_794_; 
v___x_793_ = lean_unsigned_to_nat(2u);
v___x_794_ = lean_nat_dec_eq(v_a_790_, v___x_793_);
lean_dec(v_a_790_);
if (v___x_794_ == 0)
{
goto v___jp_781_;
}
else
{
lean_object* v___x_795_; 
lean_dec(v___x_780_);
v___x_795_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressKind___lam__0___closed__2));
return v___x_795_;
}
}
else
{
lean_object* v___x_796_; 
lean_dec(v_a_790_);
lean_dec(v___x_780_);
v___x_796_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressKind___lam__0___closed__3));
return v___x_796_;
}
}
else
{
lean_dec_ref(v___x_789_);
goto v___jp_781_;
}
v___jp_781_:
{
lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; 
v___x_782_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressKind___lam__0___closed__0));
v___x_783_ = lean_unsigned_to_nat(80u);
v___x_784_ = l_Lean_Json_pretty(v___x_780_, v___x_783_);
v___x_785_ = lean_string_append(v___x_782_, v___x_784_);
lean_dec_ref(v___x_784_);
v___x_786_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressKind___lam__0___closed__1));
v___x_787_ = lean_string_append(v___x_785_, v___x_786_);
v___x_788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_788_, 0, v___x_787_);
return v___x_788_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson_spec__1___boxed(lean_object* v_j_797_, lean_object* v_k_798_){
_start:
{
lean_object* v_res_799_; 
v_res_799_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson_spec__1(v_j_797_, v_k_798_);
lean_dec_ref(v_k_798_);
return v_res_799_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__3(void){
_start:
{
uint8_t v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; 
v___x_806_ = 1;
v___x_807_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__2));
v___x_808_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_807_, v___x_806_);
return v___x_808_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__4(void){
_start:
{
lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; 
v___x_809_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6));
v___x_810_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__3);
v___x_811_ = lean_string_append(v___x_810_, v___x_809_);
return v___x_811_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__6(void){
_start:
{
uint8_t v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; 
v___x_814_ = 1;
v___x_815_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__5));
v___x_816_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_815_, v___x_814_);
return v___x_816_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__7(void){
_start:
{
lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; 
v___x_817_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__6);
v___x_818_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__4);
v___x_819_ = lean_string_append(v___x_818_, v___x_817_);
return v___x_819_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__8(void){
_start:
{
lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; 
v___x_820_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_821_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__7);
v___x_822_ = lean_string_append(v___x_821_, v___x_820_);
return v___x_822_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__11(void){
_start:
{
uint8_t v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; 
v___x_826_ = 1;
v___x_827_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__10));
v___x_828_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_827_, v___x_826_);
return v___x_828_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__12(void){
_start:
{
lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; 
v___x_829_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__11, &l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__11);
v___x_830_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__4);
v___x_831_ = lean_string_append(v___x_830_, v___x_829_);
return v___x_831_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__13(void){
_start:
{
lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; 
v___x_832_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_833_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__12, &l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__12);
v___x_834_ = lean_string_append(v___x_833_, v___x_832_);
return v___x_834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson(lean_object* v_json_835_){
_start:
{
lean_object* v___x_836_; lean_object* v___x_837_; 
v___x_836_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__0));
lean_inc(v_json_835_);
v___x_837_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson_spec__0(v_json_835_, v___x_836_);
if (lean_obj_tag(v___x_837_) == 0)
{
lean_object* v_a_838_; lean_object* v___x_840_; uint8_t v_isShared_841_; uint8_t v_isSharedCheck_847_; 
lean_dec(v_json_835_);
v_a_838_ = lean_ctor_get(v___x_837_, 0);
v_isSharedCheck_847_ = !lean_is_exclusive(v___x_837_);
if (v_isSharedCheck_847_ == 0)
{
v___x_840_ = v___x_837_;
v_isShared_841_ = v_isSharedCheck_847_;
goto v_resetjp_839_;
}
else
{
lean_inc(v_a_838_);
lean_dec(v___x_837_);
v___x_840_ = lean_box(0);
v_isShared_841_ = v_isSharedCheck_847_;
goto v_resetjp_839_;
}
v_resetjp_839_:
{
lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_845_; 
v___x_842_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__8);
v___x_843_ = lean_string_append(v___x_842_, v_a_838_);
lean_dec(v_a_838_);
if (v_isShared_841_ == 0)
{
lean_ctor_set(v___x_840_, 0, v___x_843_);
v___x_845_ = v___x_840_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v___x_843_);
v___x_845_ = v_reuseFailAlloc_846_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
return v___x_845_;
}
}
}
else
{
if (lean_obj_tag(v___x_837_) == 0)
{
lean_object* v_a_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_855_; 
lean_dec(v_json_835_);
v_a_848_ = lean_ctor_get(v___x_837_, 0);
v_isSharedCheck_855_ = !lean_is_exclusive(v___x_837_);
if (v_isSharedCheck_855_ == 0)
{
v___x_850_ = v___x_837_;
v_isShared_851_ = v_isSharedCheck_855_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_a_848_);
lean_dec(v___x_837_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_855_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
lean_object* v___x_853_; 
if (v_isShared_851_ == 0)
{
lean_ctor_set_tag(v___x_850_, 0);
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
lean_object* v_a_856_; lean_object* v___x_857_; lean_object* v___x_858_; 
v_a_856_ = lean_ctor_get(v___x_837_, 0);
lean_inc(v_a_856_);
lean_dec_ref_known(v___x_837_, 1);
v___x_857_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__9));
v___x_858_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson_spec__1(v_json_835_, v___x_857_);
if (lean_obj_tag(v___x_858_) == 0)
{
lean_object* v_a_859_; lean_object* v___x_861_; uint8_t v_isShared_862_; uint8_t v_isSharedCheck_868_; 
lean_dec(v_a_856_);
v_a_859_ = lean_ctor_get(v___x_858_, 0);
v_isSharedCheck_868_ = !lean_is_exclusive(v___x_858_);
if (v_isSharedCheck_868_ == 0)
{
v___x_861_ = v___x_858_;
v_isShared_862_ = v_isSharedCheck_868_;
goto v_resetjp_860_;
}
else
{
lean_inc(v_a_859_);
lean_dec(v___x_858_);
v___x_861_ = lean_box(0);
v_isShared_862_ = v_isSharedCheck_868_;
goto v_resetjp_860_;
}
v_resetjp_860_:
{
lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_866_; 
v___x_863_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__13, &l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__13);
v___x_864_ = lean_string_append(v___x_863_, v_a_859_);
lean_dec(v_a_859_);
if (v_isShared_862_ == 0)
{
lean_ctor_set(v___x_861_, 0, v___x_864_);
v___x_866_ = v___x_861_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_867_; 
v_reuseFailAlloc_867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_867_, 0, v___x_864_);
v___x_866_ = v_reuseFailAlloc_867_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
return v___x_866_;
}
}
}
else
{
if (lean_obj_tag(v___x_858_) == 0)
{
lean_object* v_a_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_876_; 
lean_dec(v_a_856_);
v_a_869_ = lean_ctor_get(v___x_858_, 0);
v_isSharedCheck_876_ = !lean_is_exclusive(v___x_858_);
if (v_isSharedCheck_876_ == 0)
{
v___x_871_ = v___x_858_;
v_isShared_872_ = v_isSharedCheck_876_;
goto v_resetjp_870_;
}
else
{
lean_inc(v_a_869_);
lean_dec(v___x_858_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_876_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
lean_object* v___x_874_; 
if (v_isShared_872_ == 0)
{
lean_ctor_set_tag(v___x_871_, 0);
v___x_874_ = v___x_871_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v_a_869_);
v___x_874_ = v_reuseFailAlloc_875_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
return v___x_874_;
}
}
}
else
{
lean_object* v_a_877_; lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_886_; 
v_a_877_ = lean_ctor_get(v___x_858_, 0);
v_isSharedCheck_886_ = !lean_is_exclusive(v___x_858_);
if (v_isSharedCheck_886_ == 0)
{
v___x_879_ = v___x_858_;
v_isShared_880_ = v_isSharedCheck_886_;
goto v_resetjp_878_;
}
else
{
lean_inc(v_a_877_);
lean_dec(v___x_858_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_886_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
lean_object* v___x_881_; uint8_t v___x_882_; lean_object* v___x_884_; 
v___x_881_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_881_, 0, v_a_856_);
v___x_882_ = lean_unbox(v_a_877_);
lean_dec(v_a_877_);
lean_ctor_set_uint8(v___x_881_, sizeof(void*)*1, v___x_882_);
if (v_isShared_880_ == 0)
{
lean_ctor_set(v___x_879_, 0, v___x_881_);
v___x_884_ = v___x_879_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v___x_881_);
v___x_884_ = v_reuseFailAlloc_885_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
return v___x_884_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanFileProgressProcessingInfo_toJson(lean_object* v_x_889_){
_start:
{
lean_object* v_range_890_; uint8_t v_kind_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___y_899_; 
v_range_890_ = lean_ctor_get(v_x_889_, 0);
lean_inc_ref(v_range_890_);
v_kind_891_ = lean_ctor_get_uint8(v_x_889_, sizeof(void*)*1);
lean_dec_ref(v_x_889_);
v___x_892_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__0));
v___x_893_ = l_Lean_Lsp_instToJsonRange_toJson(v_range_890_);
v___x_894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_894_, 0, v___x_892_);
lean_ctor_set(v___x_894_, 1, v___x_893_);
v___x_895_ = lean_box(0);
v___x_896_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_896_, 0, v___x_894_);
lean_ctor_set(v___x_896_, 1, v___x_895_);
v___x_897_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__9));
if (v_kind_891_ == 0)
{
lean_object* v___x_907_; 
v___x_907_ = lean_obj_once(&l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__1, &l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__1_once, _init_l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__1);
v___y_899_ = v___x_907_;
goto v___jp_898_;
}
else
{
lean_object* v___x_908_; 
v___x_908_ = lean_obj_once(&l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__3, &l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__3_once, _init_l_Lean_Lsp_instToJsonLeanFileProgressKind___lam__0___closed__3);
v___y_899_ = v___x_908_;
goto v___jp_898_;
}
v___jp_898_:
{
lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; 
lean_inc(v___y_899_);
v___x_900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_900_, 0, v___x_897_);
lean_ctor_set(v___x_900_, 1, v___y_899_);
v___x_901_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_901_, 0, v___x_900_);
lean_ctor_set(v___x_901_, 1, v___x_895_);
v___x_902_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_902_, 0, v___x_901_);
lean_ctor_set(v___x_902_, 1, v___x_895_);
v___x_903_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_903_, 0, v___x_896_);
lean_ctor_set(v___x_903_, 1, v___x_902_);
v___x_904_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0));
v___x_905_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_903_, v___x_904_);
v___x_906_ = l_Lean_Json_mkObj(v___x_905_);
lean_dec(v___x_905_);
return v___x_906_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__0(lean_object* v_j_911_, lean_object* v_k_912_){
_start:
{
lean_object* v___x_913_; lean_object* v___x_914_; 
v___x_913_ = l_Lean_Json_getObjValD(v_j_911_, v_k_912_);
v___x_914_ = l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson(v___x_913_);
return v___x_914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__0___boxed(lean_object* v_j_915_, lean_object* v_k_916_){
_start:
{
lean_object* v_res_917_; 
v_res_917_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__0(v_j_915_, v_k_916_);
lean_dec_ref(v_k_916_);
return v_res_917_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__1_spec__1_spec__2(size_t v_sz_918_, size_t v_i_919_, lean_object* v_bs_920_){
_start:
{
uint8_t v___x_921_; 
v___x_921_ = lean_usize_dec_lt(v_i_919_, v_sz_918_);
if (v___x_921_ == 0)
{
lean_object* v___x_922_; 
v___x_922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_922_, 0, v_bs_920_);
return v___x_922_;
}
else
{
lean_object* v_v_923_; lean_object* v___x_924_; 
v_v_923_ = lean_array_uget_borrowed(v_bs_920_, v_i_919_);
lean_inc(v_v_923_);
v___x_924_ = l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson(v_v_923_);
if (lean_obj_tag(v___x_924_) == 0)
{
lean_object* v_a_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_932_; 
lean_dec_ref(v_bs_920_);
v_a_925_ = lean_ctor_get(v___x_924_, 0);
v_isSharedCheck_932_ = !lean_is_exclusive(v___x_924_);
if (v_isSharedCheck_932_ == 0)
{
v___x_927_ = v___x_924_;
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_a_925_);
lean_dec(v___x_924_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
lean_object* v___x_930_; 
if (v_isShared_928_ == 0)
{
v___x_930_ = v___x_927_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v_a_925_);
v___x_930_ = v_reuseFailAlloc_931_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
return v___x_930_;
}
}
}
else
{
lean_object* v_a_933_; lean_object* v___x_934_; lean_object* v_bs_x27_935_; size_t v___x_936_; size_t v___x_937_; lean_object* v___x_938_; 
v_a_933_ = lean_ctor_get(v___x_924_, 0);
lean_inc(v_a_933_);
lean_dec_ref_known(v___x_924_, 1);
v___x_934_ = lean_unsigned_to_nat(0u);
v_bs_x27_935_ = lean_array_uset(v_bs_920_, v_i_919_, v___x_934_);
v___x_936_ = ((size_t)1ULL);
v___x_937_ = lean_usize_add(v_i_919_, v___x_936_);
v___x_938_ = lean_array_uset(v_bs_x27_935_, v_i_919_, v_a_933_);
v_i_919_ = v___x_937_;
v_bs_920_ = v___x_938_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__1_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
size_t v_sz_918_ = stack[0].m_num;
size_t v_i_919_ = stack[1].m_num;
lean_object* v_bs_920_ = stack[2].m_obj;
lean_object* v_res_940_;
v_res_940_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__1_spec__1_spec__2(v_sz_918_, v_i_919_, v_bs_920_);
stack->m_obj
 = v_res_940_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__1_spec__1_spec__2___boxed(lean_object* v_sz_941_, lean_object* v_i_942_, lean_object* v_bs_943_){
_start:
{
size_t v_sz_boxed_944_; size_t v_i_boxed_945_; lean_object* v_res_946_; 
v_sz_boxed_944_ = lean_unbox_usize(v_sz_941_);
lean_dec(v_sz_941_);
v_i_boxed_945_ = lean_unbox_usize(v_i_942_);
lean_dec(v_i_942_);
v_res_946_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__1_spec__1_spec__2(v_sz_boxed_944_, v_i_boxed_945_, v_bs_943_);
return v_res_946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__1_spec__1(lean_object* v_x_948_){
_start:
{
if (lean_obj_tag(v_x_948_) == 4)
{
lean_object* v_elems_949_; size_t v_sz_950_; size_t v___x_951_; lean_object* v___x_952_; 
v_elems_949_ = lean_ctor_get(v_x_948_, 0);
lean_inc_ref(v_elems_949_);
lean_dec_ref_known(v_x_948_, 1);
v_sz_950_ = lean_array_size(v_elems_949_);
v___x_951_ = ((size_t)0ULL);
v___x_952_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__1_spec__1_spec__2(v_sz_950_, v___x_951_, v_elems_949_);
return v___x_952_;
}
else
{
lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; 
v___x_953_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__1_spec__1___closed__0));
v___x_954_ = lean_unsigned_to_nat(80u);
v___x_955_ = l_Lean_Json_pretty(v_x_948_, v___x_954_);
v___x_956_ = lean_string_append(v___x_953_, v___x_955_);
lean_dec_ref(v___x_955_);
v___x_957_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressKind___lam__0___closed__1));
v___x_958_ = lean_string_append(v___x_956_, v___x_957_);
v___x_959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_959_, 0, v___x_958_);
return v___x_959_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__1(lean_object* v_j_960_, lean_object* v_k_961_){
_start:
{
lean_object* v___x_962_; lean_object* v___x_963_; 
v___x_962_ = l_Lean_Json_getObjValD(v_j_960_, v_k_961_);
v___x_963_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__1_spec__1(v___x_962_);
return v___x_963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__1___boxed(lean_object* v_j_964_, lean_object* v_k_965_){
_start:
{
lean_object* v_res_966_; 
v_res_966_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__1(v_j_964_, v_k_965_);
lean_dec_ref(v_k_965_);
return v_res_966_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__2(void){
_start:
{
uint8_t v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; 
v___x_972_ = 1;
v___x_973_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__1));
v___x_974_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_973_, v___x_972_);
return v___x_974_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__3(void){
_start:
{
lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; 
v___x_975_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6));
v___x_976_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__2, &l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__2);
v___x_977_ = lean_string_append(v___x_976_, v___x_975_);
return v___x_977_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; 
v___x_978_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9, &l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9);
v___x_979_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__3);
v___x_980_ = lean_string_append(v___x_979_, v___x_978_);
return v___x_980_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__5(void){
_start:
{
lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; 
v___x_981_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_982_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__4);
v___x_983_ = lean_string_append(v___x_982_, v___x_981_);
return v___x_983_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__8(void){
_start:
{
uint8_t v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; 
v___x_987_ = 1;
v___x_988_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__7));
v___x_989_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_988_, v___x_987_);
return v___x_989_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__9(void){
_start:
{
lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; 
v___x_990_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__8);
v___x_991_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__3);
v___x_992_ = lean_string_append(v___x_991_, v___x_990_);
return v___x_992_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__10(void){
_start:
{
lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; 
v___x_993_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_994_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__9, &l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__9);
v___x_995_ = lean_string_append(v___x_994_, v___x_993_);
return v___x_995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson(lean_object* v_json_996_){
_start:
{
lean_object* v___x_997_; lean_object* v___x_998_; 
v___x_997_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__0));
lean_inc(v_json_996_);
v___x_998_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__0(v_json_996_, v___x_997_);
if (lean_obj_tag(v___x_998_) == 0)
{
lean_object* v_a_999_; lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1008_; 
lean_dec(v_json_996_);
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
v___x_1003_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__5, &l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__5);
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
lean_dec(v_json_996_);
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
lean_object* v_a_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; 
v_a_1017_ = lean_ctor_get(v___x_998_, 0);
lean_inc(v_a_1017_);
lean_dec_ref_known(v___x_998_, 1);
v___x_1018_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__6));
v___x_1019_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__1(v_json_996_, v___x_1018_);
if (lean_obj_tag(v___x_1019_) == 0)
{
lean_object* v_a_1020_; lean_object* v___x_1022_; uint8_t v_isShared_1023_; uint8_t v_isSharedCheck_1029_; 
lean_dec(v_a_1017_);
v_a_1020_ = lean_ctor_get(v___x_1019_, 0);
v_isSharedCheck_1029_ = !lean_is_exclusive(v___x_1019_);
if (v_isSharedCheck_1029_ == 0)
{
v___x_1022_ = v___x_1019_;
v_isShared_1023_ = v_isSharedCheck_1029_;
goto v_resetjp_1021_;
}
else
{
lean_inc(v_a_1020_);
lean_dec(v___x_1019_);
v___x_1022_ = lean_box(0);
v_isShared_1023_ = v_isSharedCheck_1029_;
goto v_resetjp_1021_;
}
v_resetjp_1021_:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1027_; 
v___x_1024_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__10, &l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__10);
v___x_1025_ = lean_string_append(v___x_1024_, v_a_1020_);
lean_dec(v_a_1020_);
if (v_isShared_1023_ == 0)
{
lean_ctor_set(v___x_1022_, 0, v___x_1025_);
v___x_1027_ = v___x_1022_;
goto v_reusejp_1026_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v___x_1025_);
v___x_1027_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1026_;
}
v_reusejp_1026_:
{
return v___x_1027_;
}
}
}
else
{
if (lean_obj_tag(v___x_1019_) == 0)
{
lean_object* v_a_1030_; lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1037_; 
lean_dec(v_a_1017_);
v_a_1030_ = lean_ctor_get(v___x_1019_, 0);
v_isSharedCheck_1037_ = !lean_is_exclusive(v___x_1019_);
if (v_isSharedCheck_1037_ == 0)
{
v___x_1032_ = v___x_1019_;
v_isShared_1033_ = v_isSharedCheck_1037_;
goto v_resetjp_1031_;
}
else
{
lean_inc(v_a_1030_);
lean_dec(v___x_1019_);
v___x_1032_ = lean_box(0);
v_isShared_1033_ = v_isSharedCheck_1037_;
goto v_resetjp_1031_;
}
v_resetjp_1031_:
{
lean_object* v___x_1035_; 
if (v_isShared_1033_ == 0)
{
lean_ctor_set_tag(v___x_1032_, 0);
v___x_1035_ = v___x_1032_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v_a_1030_);
v___x_1035_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
return v___x_1035_;
}
}
}
else
{
lean_object* v_a_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1046_; 
v_a_1038_ = lean_ctor_get(v___x_1019_, 0);
v_isSharedCheck_1046_ = !lean_is_exclusive(v___x_1019_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_1040_ = v___x_1019_;
v_isShared_1041_ = v_isSharedCheck_1046_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_a_1038_);
lean_dec(v___x_1019_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1046_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
lean_object* v___x_1042_; lean_object* v___x_1044_; 
v___x_1042_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1042_, 0, v_a_1017_);
lean_ctor_set(v___x_1042_, 1, v_a_1038_);
if (v_isShared_1041_ == 0)
{
lean_ctor_set(v___x_1040_, 0, v___x_1042_);
v___x_1044_ = v___x_1040_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v___x_1042_);
v___x_1044_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
return v___x_1044_;
}
}
}
}
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanFileProgressParams_toJson_spec__0_spec__0(size_t v_sz_1049_, size_t v_i_1050_, lean_object* v_bs_1051_){
_start:
{
uint8_t v___x_1052_; 
v___x_1052_ = lean_usize_dec_lt(v_i_1050_, v_sz_1049_);
if (v___x_1052_ == 0)
{
return v_bs_1051_;
}
else
{
lean_object* v_v_1053_; lean_object* v___x_1054_; lean_object* v_bs_x27_1055_; lean_object* v___x_1056_; size_t v___x_1057_; size_t v___x_1058_; lean_object* v___x_1059_; 
v_v_1053_ = lean_array_uget(v_bs_1051_, v_i_1050_);
v___x_1054_ = lean_unsigned_to_nat(0u);
v_bs_x27_1055_ = lean_array_uset(v_bs_1051_, v_i_1050_, v___x_1054_);
v___x_1056_ = l_Lean_Lsp_instToJsonLeanFileProgressProcessingInfo_toJson(v_v_1053_);
v___x_1057_ = ((size_t)1ULL);
v___x_1058_ = lean_usize_add(v_i_1050_, v___x_1057_);
v___x_1059_ = lean_array_uset(v_bs_x27_1055_, v_i_1050_, v___x_1056_);
v_i_1050_ = v___x_1058_;
v_bs_1051_ = v___x_1059_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanFileProgressParams_toJson_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1049_ = stack[0].m_num;
size_t v_i_1050_ = stack[1].m_num;
lean_object* v_bs_1051_ = stack[2].m_obj;
lean_object* v_res_1061_;
v_res_1061_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanFileProgressParams_toJson_spec__0_spec__0(v_sz_1049_, v_i_1050_, v_bs_1051_);
stack->m_obj
 = v_res_1061_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanFileProgressParams_toJson_spec__0_spec__0___boxed(lean_object* v_sz_1062_, lean_object* v_i_1063_, lean_object* v_bs_1064_){
_start:
{
size_t v_sz_boxed_1065_; size_t v_i_boxed_1066_; lean_object* v_res_1067_; 
v_sz_boxed_1065_ = lean_unbox_usize(v_sz_1062_);
lean_dec(v_sz_1062_);
v_i_boxed_1066_ = lean_unbox_usize(v_i_1063_);
lean_dec(v_i_1063_);
v_res_1067_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanFileProgressParams_toJson_spec__0_spec__0(v_sz_boxed_1065_, v_i_boxed_1066_, v_bs_1064_);
return v_res_1067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanFileProgressParams_toJson_spec__0(lean_object* v_a_1068_){
_start:
{
size_t v_sz_1069_; size_t v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; 
v_sz_1069_ = lean_array_size(v_a_1068_);
v___x_1070_ = ((size_t)0ULL);
v___x_1071_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanFileProgressParams_toJson_spec__0_spec__0(v_sz_1069_, v___x_1070_, v_a_1068_);
v___x_1072_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1072_, 0, v___x_1071_);
return v___x_1072_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanFileProgressParams_toJson(lean_object* v_x_1073_){
_start:
{
lean_object* v_textDocument_1074_; lean_object* v_processing_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1095_; 
v_textDocument_1074_ = lean_ctor_get(v_x_1073_, 0);
v_processing_1075_ = lean_ctor_get(v_x_1073_, 1);
v_isSharedCheck_1095_ = !lean_is_exclusive(v_x_1073_);
if (v_isSharedCheck_1095_ == 0)
{
v___x_1077_ = v_x_1073_;
v_isShared_1078_ = v_isSharedCheck_1095_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_processing_1075_);
lean_inc(v_textDocument_1074_);
lean_dec(v_x_1073_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1095_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1082_; 
v___x_1079_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__0));
v___x_1080_ = l_Lean_Lsp_instToJsonVersionedTextDocumentIdentifier_toJson(v_textDocument_1074_);
if (v_isShared_1078_ == 0)
{
lean_ctor_set(v___x_1077_, 1, v___x_1080_);
lean_ctor_set(v___x_1077_, 0, v___x_1079_);
v___x_1082_ = v___x_1077_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v___x_1079_);
lean_ctor_set(v_reuseFailAlloc_1094_, 1, v___x_1080_);
v___x_1082_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; 
v___x_1083_ = lean_box(0);
v___x_1084_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1084_, 0, v___x_1082_);
lean_ctor_set(v___x_1084_, 1, v___x_1083_);
v___x_1085_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson___closed__6));
v___x_1086_ = l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonLeanFileProgressParams_toJson_spec__0(v_processing_1075_);
v___x_1087_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1087_, 0, v___x_1085_);
lean_ctor_set(v___x_1087_, 1, v___x_1086_);
v___x_1088_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1088_, 0, v___x_1087_);
lean_ctor_set(v___x_1088_, 1, v___x_1083_);
v___x_1089_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1089_, 0, v___x_1088_);
lean_ctor_set(v___x_1089_, 1, v___x_1083_);
v___x_1090_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1090_, 0, v___x_1084_);
lean_ctor_set(v___x_1090_, 1, v___x_1089_);
v___x_1091_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0));
v___x_1092_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_1090_, v___x_1091_);
v___x_1093_ = l_Lean_Json_mkObj(v___x_1092_);
lean_dec(v___x_1092_);
return v___x_1093_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoalParams_fromJson_spec__0(lean_object* v_j_1098_, lean_object* v_k_1099_){
_start:
{
lean_object* v___x_1100_; lean_object* v___x_1101_; 
v___x_1100_ = l_Lean_Json_getObjValD(v_j_1098_, v_k_1099_);
v___x_1101_ = l_Lean_Lsp_instFromJsonTextDocumentIdentifier_fromJson(v___x_1100_);
return v___x_1101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoalParams_fromJson_spec__0___boxed(lean_object* v_j_1102_, lean_object* v_k_1103_){
_start:
{
lean_object* v_res_1104_; 
v_res_1104_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoalParams_fromJson_spec__0(v_j_1102_, v_k_1103_);
lean_dec_ref(v_k_1103_);
return v_res_1104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoalParams_fromJson_spec__1(lean_object* v_j_1105_, lean_object* v_k_1106_){
_start:
{
lean_object* v___x_1107_; lean_object* v___x_1108_; 
v___x_1107_ = l_Lean_Json_getObjValD(v_j_1105_, v_k_1106_);
v___x_1108_ = l_Lean_Lsp_instFromJsonPosition_fromJson(v___x_1107_);
return v___x_1108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoalParams_fromJson_spec__1___boxed(lean_object* v_j_1109_, lean_object* v_k_1110_){
_start:
{
lean_object* v_res_1111_; 
v_res_1111_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoalParams_fromJson_spec__1(v_j_1109_, v_k_1110_);
lean_dec_ref(v_k_1110_);
return v_res_1111_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__2(void){
_start:
{
uint8_t v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; 
v___x_1117_ = 1;
v___x_1118_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__1));
v___x_1119_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1118_, v___x_1117_);
return v___x_1119_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__3(void){
_start:
{
lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; 
v___x_1120_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6));
v___x_1121_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__2, &l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__2);
v___x_1122_ = lean_string_append(v___x_1121_, v___x_1120_);
return v___x_1122_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; 
v___x_1123_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9, &l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9);
v___x_1124_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__3);
v___x_1125_ = lean_string_append(v___x_1124_, v___x_1123_);
return v___x_1125_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__5(void){
_start:
{
lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; 
v___x_1126_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_1127_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__4);
v___x_1128_ = lean_string_append(v___x_1127_, v___x_1126_);
return v___x_1128_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__8(void){
_start:
{
uint8_t v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; 
v___x_1132_ = 1;
v___x_1133_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__7));
v___x_1134_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1133_, v___x_1132_);
return v___x_1134_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__9(void){
_start:
{
lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; 
v___x_1135_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__8);
v___x_1136_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__3);
v___x_1137_ = lean_string_append(v___x_1136_, v___x_1135_);
return v___x_1137_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__10(void){
_start:
{
lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; 
v___x_1138_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_1139_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__9, &l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__9);
v___x_1140_ = lean_string_append(v___x_1139_, v___x_1138_);
return v___x_1140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson(lean_object* v_json_1141_){
_start:
{
lean_object* v___x_1142_; lean_object* v___x_1143_; 
v___x_1142_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__0));
lean_inc(v_json_1141_);
v___x_1143_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoalParams_fromJson_spec__0(v_json_1141_, v___x_1142_);
if (lean_obj_tag(v___x_1143_) == 0)
{
lean_object* v_a_1144_; lean_object* v___x_1146_; uint8_t v_isShared_1147_; uint8_t v_isSharedCheck_1153_; 
lean_dec(v_json_1141_);
v_a_1144_ = lean_ctor_get(v___x_1143_, 0);
v_isSharedCheck_1153_ = !lean_is_exclusive(v___x_1143_);
if (v_isSharedCheck_1153_ == 0)
{
v___x_1146_ = v___x_1143_;
v_isShared_1147_ = v_isSharedCheck_1153_;
goto v_resetjp_1145_;
}
else
{
lean_inc(v_a_1144_);
lean_dec(v___x_1143_);
v___x_1146_ = lean_box(0);
v_isShared_1147_ = v_isSharedCheck_1153_;
goto v_resetjp_1145_;
}
v_resetjp_1145_:
{
lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1151_; 
v___x_1148_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__5, &l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__5);
v___x_1149_ = lean_string_append(v___x_1148_, v_a_1144_);
lean_dec(v_a_1144_);
if (v_isShared_1147_ == 0)
{
lean_ctor_set(v___x_1146_, 0, v___x_1149_);
v___x_1151_ = v___x_1146_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v___x_1149_);
v___x_1151_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
return v___x_1151_;
}
}
}
else
{
if (lean_obj_tag(v___x_1143_) == 0)
{
lean_object* v_a_1154_; lean_object* v___x_1156_; uint8_t v_isShared_1157_; uint8_t v_isSharedCheck_1161_; 
lean_dec(v_json_1141_);
v_a_1154_ = lean_ctor_get(v___x_1143_, 0);
v_isSharedCheck_1161_ = !lean_is_exclusive(v___x_1143_);
if (v_isSharedCheck_1161_ == 0)
{
v___x_1156_ = v___x_1143_;
v_isShared_1157_ = v_isSharedCheck_1161_;
goto v_resetjp_1155_;
}
else
{
lean_inc(v_a_1154_);
lean_dec(v___x_1143_);
v___x_1156_ = lean_box(0);
v_isShared_1157_ = v_isSharedCheck_1161_;
goto v_resetjp_1155_;
}
v_resetjp_1155_:
{
lean_object* v___x_1159_; 
if (v_isShared_1157_ == 0)
{
lean_ctor_set_tag(v___x_1156_, 0);
v___x_1159_ = v___x_1156_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1160_; 
v_reuseFailAlloc_1160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1160_, 0, v_a_1154_);
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
lean_object* v_a_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; 
v_a_1162_ = lean_ctor_get(v___x_1143_, 0);
lean_inc(v_a_1162_);
lean_dec_ref_known(v___x_1143_, 1);
v___x_1163_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__6));
v___x_1164_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoalParams_fromJson_spec__1(v_json_1141_, v___x_1163_);
if (lean_obj_tag(v___x_1164_) == 0)
{
lean_object* v_a_1165_; lean_object* v___x_1167_; uint8_t v_isShared_1168_; uint8_t v_isSharedCheck_1174_; 
lean_dec(v_a_1162_);
v_a_1165_ = lean_ctor_get(v___x_1164_, 0);
v_isSharedCheck_1174_ = !lean_is_exclusive(v___x_1164_);
if (v_isSharedCheck_1174_ == 0)
{
v___x_1167_ = v___x_1164_;
v_isShared_1168_ = v_isSharedCheck_1174_;
goto v_resetjp_1166_;
}
else
{
lean_inc(v_a_1165_);
lean_dec(v___x_1164_);
v___x_1167_ = lean_box(0);
v_isShared_1168_ = v_isSharedCheck_1174_;
goto v_resetjp_1166_;
}
v_resetjp_1166_:
{
lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1172_; 
v___x_1169_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__10, &l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__10);
v___x_1170_ = lean_string_append(v___x_1169_, v_a_1165_);
lean_dec(v_a_1165_);
if (v_isShared_1168_ == 0)
{
lean_ctor_set(v___x_1167_, 0, v___x_1170_);
v___x_1172_ = v___x_1167_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(0, 1, 0);
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
else
{
if (lean_obj_tag(v___x_1164_) == 0)
{
lean_object* v_a_1175_; lean_object* v___x_1177_; uint8_t v_isShared_1178_; uint8_t v_isSharedCheck_1182_; 
lean_dec(v_a_1162_);
v_a_1175_ = lean_ctor_get(v___x_1164_, 0);
v_isSharedCheck_1182_ = !lean_is_exclusive(v___x_1164_);
if (v_isSharedCheck_1182_ == 0)
{
v___x_1177_ = v___x_1164_;
v_isShared_1178_ = v_isSharedCheck_1182_;
goto v_resetjp_1176_;
}
else
{
lean_inc(v_a_1175_);
lean_dec(v___x_1164_);
v___x_1177_ = lean_box(0);
v_isShared_1178_ = v_isSharedCheck_1182_;
goto v_resetjp_1176_;
}
v_resetjp_1176_:
{
lean_object* v___x_1180_; 
if (v_isShared_1178_ == 0)
{
lean_ctor_set_tag(v___x_1177_, 0);
v___x_1180_ = v___x_1177_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v_a_1175_);
v___x_1180_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
return v___x_1180_;
}
}
}
else
{
lean_object* v_a_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1191_; 
v_a_1183_ = lean_ctor_get(v___x_1164_, 0);
v_isSharedCheck_1191_ = !lean_is_exclusive(v___x_1164_);
if (v_isSharedCheck_1191_ == 0)
{
v___x_1185_ = v___x_1164_;
v_isShared_1186_ = v_isSharedCheck_1191_;
goto v_resetjp_1184_;
}
else
{
lean_inc(v_a_1183_);
lean_dec(v___x_1164_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1191_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
lean_object* v___x_1187_; lean_object* v___x_1189_; 
v___x_1187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1187_, 0, v_a_1162_);
lean_ctor_set(v___x_1187_, 1, v_a_1183_);
if (v_isShared_1186_ == 0)
{
lean_ctor_set(v___x_1185_, 0, v___x_1187_);
v___x_1189_ = v___x_1185_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v___x_1187_);
v___x_1189_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
return v___x_1189_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonPlainGoalParams_toJson(lean_object* v_x_1194_){
_start:
{
lean_object* v_textDocument_1195_; lean_object* v_position_1196_; lean_object* v___x_1198_; uint8_t v_isShared_1199_; uint8_t v_isSharedCheck_1216_; 
v_textDocument_1195_ = lean_ctor_get(v_x_1194_, 0);
v_position_1196_ = lean_ctor_get(v_x_1194_, 1);
v_isSharedCheck_1216_ = !lean_is_exclusive(v_x_1194_);
if (v_isSharedCheck_1216_ == 0)
{
v___x_1198_ = v_x_1194_;
v_isShared_1199_ = v_isSharedCheck_1216_;
goto v_resetjp_1197_;
}
else
{
lean_inc(v_position_1196_);
lean_inc(v_textDocument_1195_);
lean_dec(v_x_1194_);
v___x_1198_ = lean_box(0);
v_isShared_1199_ = v_isSharedCheck_1216_;
goto v_resetjp_1197_;
}
v_resetjp_1197_:
{
lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1203_; 
v___x_1200_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__0));
v___x_1201_ = l_Lean_Lsp_instToJsonTextDocumentIdentifier_toJson(v_textDocument_1195_);
if (v_isShared_1199_ == 0)
{
lean_ctor_set(v___x_1198_, 1, v___x_1201_);
lean_ctor_set(v___x_1198_, 0, v___x_1200_);
v___x_1203_ = v___x_1198_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v___x_1200_);
lean_ctor_set(v_reuseFailAlloc_1215_, 1, v___x_1201_);
v___x_1203_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; 
v___x_1204_ = lean_box(0);
v___x_1205_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1205_, 0, v___x_1203_);
lean_ctor_set(v___x_1205_, 1, v___x_1204_);
v___x_1206_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__6));
v___x_1207_ = l_Lean_Lsp_instToJsonPosition_toJson(v_position_1196_);
v___x_1208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1208_, 0, v___x_1206_);
lean_ctor_set(v___x_1208_, 1, v___x_1207_);
v___x_1209_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1209_, 0, v___x_1208_);
lean_ctor_set(v___x_1209_, 1, v___x_1204_);
v___x_1210_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1210_, 0, v___x_1209_);
lean_ctor_set(v___x_1210_, 1, v___x_1204_);
v___x_1211_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1211_, 0, v___x_1205_);
lean_ctor_set(v___x_1211_, 1, v___x_1210_);
v___x_1212_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0));
v___x_1213_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_1211_, v___x_1212_);
v___x_1214_ = l_Lean_Json_mkObj(v___x_1213_);
lean_dec(v___x_1213_);
return v___x_1214_;
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoal_fromJson_spec__0_spec__0_spec__1(size_t v_sz_1219_, size_t v_i_1220_, lean_object* v_bs_1221_){
_start:
{
uint8_t v___x_1222_; 
v___x_1222_ = lean_usize_dec_lt(v_i_1220_, v_sz_1219_);
if (v___x_1222_ == 0)
{
lean_object* v___x_1223_; 
v___x_1223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1223_, 0, v_bs_1221_);
return v___x_1223_;
}
else
{
lean_object* v_v_1224_; lean_object* v___x_1225_; 
v_v_1224_ = lean_array_uget_borrowed(v_bs_1221_, v_i_1220_);
lean_inc(v_v_1224_);
v___x_1225_ = l_Lean_Json_getStr_x3f(v_v_1224_);
if (lean_obj_tag(v___x_1225_) == 0)
{
lean_object* v_a_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1233_; 
lean_dec_ref(v_bs_1221_);
v_a_1226_ = lean_ctor_get(v___x_1225_, 0);
v_isSharedCheck_1233_ = !lean_is_exclusive(v___x_1225_);
if (v_isSharedCheck_1233_ == 0)
{
v___x_1228_ = v___x_1225_;
v_isShared_1229_ = v_isSharedCheck_1233_;
goto v_resetjp_1227_;
}
else
{
lean_inc(v_a_1226_);
lean_dec(v___x_1225_);
v___x_1228_ = lean_box(0);
v_isShared_1229_ = v_isSharedCheck_1233_;
goto v_resetjp_1227_;
}
v_resetjp_1227_:
{
lean_object* v___x_1231_; 
if (v_isShared_1229_ == 0)
{
v___x_1231_ = v___x_1228_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v_a_1226_);
v___x_1231_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
return v___x_1231_;
}
}
}
else
{
lean_object* v_a_1234_; lean_object* v___x_1235_; lean_object* v_bs_x27_1236_; size_t v___x_1237_; size_t v___x_1238_; lean_object* v___x_1239_; 
v_a_1234_ = lean_ctor_get(v___x_1225_, 0);
lean_inc(v_a_1234_);
lean_dec_ref_known(v___x_1225_, 1);
v___x_1235_ = lean_unsigned_to_nat(0u);
v_bs_x27_1236_ = lean_array_uset(v_bs_1221_, v_i_1220_, v___x_1235_);
v___x_1237_ = ((size_t)1ULL);
v___x_1238_ = lean_usize_add(v_i_1220_, v___x_1237_);
v___x_1239_ = lean_array_uset(v_bs_x27_1236_, v_i_1220_, v_a_1234_);
v_i_1220_ = v___x_1238_;
v_bs_1221_ = v___x_1239_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoal_fromJson_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1219_ = stack[0].m_num;
size_t v_i_1220_ = stack[1].m_num;
lean_object* v_bs_1221_ = stack[2].m_obj;
lean_object* v_res_1241_;
v_res_1241_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoal_fromJson_spec__0_spec__0_spec__1(v_sz_1219_, v_i_1220_, v_bs_1221_);
stack->m_obj
 = v_res_1241_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoal_fromJson_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_1242_, lean_object* v_i_1243_, lean_object* v_bs_1244_){
_start:
{
size_t v_sz_boxed_1245_; size_t v_i_boxed_1246_; lean_object* v_res_1247_; 
v_sz_boxed_1245_ = lean_unbox_usize(v_sz_1242_);
lean_dec(v_sz_1242_);
v_i_boxed_1246_ = lean_unbox_usize(v_i_1243_);
lean_dec(v_i_1243_);
v_res_1247_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoal_fromJson_spec__0_spec__0_spec__1(v_sz_boxed_1245_, v_i_boxed_1246_, v_bs_1244_);
return v_res_1247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoal_fromJson_spec__0_spec__0(lean_object* v_x_1248_){
_start:
{
if (lean_obj_tag(v_x_1248_) == 4)
{
lean_object* v_elems_1249_; size_t v_sz_1250_; size_t v___x_1251_; lean_object* v___x_1252_; 
v_elems_1249_ = lean_ctor_get(v_x_1248_, 0);
lean_inc_ref(v_elems_1249_);
lean_dec_ref_known(v_x_1248_, 1);
v_sz_1250_ = lean_array_size(v_elems_1249_);
v___x_1251_ = ((size_t)0ULL);
v___x_1252_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoal_fromJson_spec__0_spec__0_spec__1(v_sz_1250_, v___x_1251_, v_elems_1249_);
return v___x_1252_;
}
else
{
lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; 
v___x_1253_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__1_spec__1___closed__0));
v___x_1254_ = lean_unsigned_to_nat(80u);
v___x_1255_ = l_Lean_Json_pretty(v_x_1248_, v___x_1254_);
v___x_1256_ = lean_string_append(v___x_1253_, v___x_1255_);
lean_dec_ref(v___x_1255_);
v___x_1257_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressKind___lam__0___closed__1));
v___x_1258_ = lean_string_append(v___x_1256_, v___x_1257_);
v___x_1259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1259_, 0, v___x_1258_);
return v___x_1259_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoal_fromJson_spec__0(lean_object* v_j_1260_, lean_object* v_k_1261_){
_start:
{
lean_object* v___x_1262_; lean_object* v___x_1263_; 
v___x_1262_ = l_Lean_Json_getObjValD(v_j_1260_, v_k_1261_);
v___x_1263_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoal_fromJson_spec__0_spec__0(v___x_1262_);
return v___x_1263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoal_fromJson_spec__0___boxed(lean_object* v_j_1264_, lean_object* v_k_1265_){
_start:
{
lean_object* v_res_1266_; 
v_res_1266_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoal_fromJson_spec__0(v_j_1264_, v_k_1265_);
lean_dec_ref(v_k_1265_);
return v_res_1266_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__3(void){
_start:
{
uint8_t v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; 
v___x_1273_ = 1;
v___x_1274_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__2));
v___x_1275_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1274_, v___x_1273_);
return v___x_1275_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__4(void){
_start:
{
lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; 
v___x_1276_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6));
v___x_1277_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__3, &l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__3);
v___x_1278_ = lean_string_append(v___x_1277_, v___x_1276_);
return v___x_1278_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__6(void){
_start:
{
uint8_t v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; 
v___x_1281_ = 1;
v___x_1282_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__5));
v___x_1283_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1282_, v___x_1281_);
return v___x_1283_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__7(void){
_start:
{
lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; 
v___x_1284_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__6, &l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__6);
v___x_1285_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__4, &l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__4);
v___x_1286_ = lean_string_append(v___x_1285_, v___x_1284_);
return v___x_1286_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__8(void){
_start:
{
lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; 
v___x_1287_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_1288_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__7, &l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__7);
v___x_1289_ = lean_string_append(v___x_1288_, v___x_1287_);
return v___x_1289_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__11(void){
_start:
{
uint8_t v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; 
v___x_1293_ = 1;
v___x_1294_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__10));
v___x_1295_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1294_, v___x_1293_);
return v___x_1295_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__12(void){
_start:
{
lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; 
v___x_1296_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__11, &l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__11);
v___x_1297_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__4, &l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__4);
v___x_1298_ = lean_string_append(v___x_1297_, v___x_1296_);
return v___x_1298_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__13(void){
_start:
{
lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; 
v___x_1299_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_1300_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__12, &l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__12);
v___x_1301_ = lean_string_append(v___x_1300_, v___x_1299_);
return v___x_1301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonPlainGoal_fromJson(lean_object* v_json_1302_){
_start:
{
lean_object* v___x_1303_; lean_object* v___x_1304_; 
v___x_1303_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__0));
lean_inc(v_json_1302_);
v___x_1304_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson_spec__0(v_json_1302_, v___x_1303_);
if (lean_obj_tag(v___x_1304_) == 0)
{
lean_object* v_a_1305_; lean_object* v___x_1307_; uint8_t v_isShared_1308_; uint8_t v_isSharedCheck_1314_; 
lean_dec(v_json_1302_);
v_a_1305_ = lean_ctor_get(v___x_1304_, 0);
v_isSharedCheck_1314_ = !lean_is_exclusive(v___x_1304_);
if (v_isSharedCheck_1314_ == 0)
{
v___x_1307_ = v___x_1304_;
v_isShared_1308_ = v_isSharedCheck_1314_;
goto v_resetjp_1306_;
}
else
{
lean_inc(v_a_1305_);
lean_dec(v___x_1304_);
v___x_1307_ = lean_box(0);
v_isShared_1308_ = v_isSharedCheck_1314_;
goto v_resetjp_1306_;
}
v_resetjp_1306_:
{
lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1312_; 
v___x_1309_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__8, &l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__8);
v___x_1310_ = lean_string_append(v___x_1309_, v_a_1305_);
lean_dec(v_a_1305_);
if (v_isShared_1308_ == 0)
{
lean_ctor_set(v___x_1307_, 0, v___x_1310_);
v___x_1312_ = v___x_1307_;
goto v_reusejp_1311_;
}
else
{
lean_object* v_reuseFailAlloc_1313_; 
v_reuseFailAlloc_1313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1313_, 0, v___x_1310_);
v___x_1312_ = v_reuseFailAlloc_1313_;
goto v_reusejp_1311_;
}
v_reusejp_1311_:
{
return v___x_1312_;
}
}
}
else
{
if (lean_obj_tag(v___x_1304_) == 0)
{
lean_object* v_a_1315_; lean_object* v___x_1317_; uint8_t v_isShared_1318_; uint8_t v_isSharedCheck_1322_; 
lean_dec(v_json_1302_);
v_a_1315_ = lean_ctor_get(v___x_1304_, 0);
v_isSharedCheck_1322_ = !lean_is_exclusive(v___x_1304_);
if (v_isSharedCheck_1322_ == 0)
{
v___x_1317_ = v___x_1304_;
v_isShared_1318_ = v_isSharedCheck_1322_;
goto v_resetjp_1316_;
}
else
{
lean_inc(v_a_1315_);
lean_dec(v___x_1304_);
v___x_1317_ = lean_box(0);
v_isShared_1318_ = v_isSharedCheck_1322_;
goto v_resetjp_1316_;
}
v_resetjp_1316_:
{
lean_object* v___x_1320_; 
if (v_isShared_1318_ == 0)
{
lean_ctor_set_tag(v___x_1317_, 0);
v___x_1320_ = v___x_1317_;
goto v_reusejp_1319_;
}
else
{
lean_object* v_reuseFailAlloc_1321_; 
v_reuseFailAlloc_1321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1321_, 0, v_a_1315_);
v___x_1320_ = v_reuseFailAlloc_1321_;
goto v_reusejp_1319_;
}
v_reusejp_1319_:
{
return v___x_1320_;
}
}
}
else
{
lean_object* v_a_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; 
v_a_1323_ = lean_ctor_get(v___x_1304_, 0);
lean_inc(v_a_1323_);
lean_dec_ref_known(v___x_1304_, 1);
v___x_1324_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__9));
v___x_1325_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoal_fromJson_spec__0(v_json_1302_, v___x_1324_);
if (lean_obj_tag(v___x_1325_) == 0)
{
lean_object* v_a_1326_; lean_object* v___x_1328_; uint8_t v_isShared_1329_; uint8_t v_isSharedCheck_1335_; 
lean_dec(v_a_1323_);
v_a_1326_ = lean_ctor_get(v___x_1325_, 0);
v_isSharedCheck_1335_ = !lean_is_exclusive(v___x_1325_);
if (v_isSharedCheck_1335_ == 0)
{
v___x_1328_ = v___x_1325_;
v_isShared_1329_ = v_isSharedCheck_1335_;
goto v_resetjp_1327_;
}
else
{
lean_inc(v_a_1326_);
lean_dec(v___x_1325_);
v___x_1328_ = lean_box(0);
v_isShared_1329_ = v_isSharedCheck_1335_;
goto v_resetjp_1327_;
}
v_resetjp_1327_:
{
lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1333_; 
v___x_1330_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__13, &l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__13);
v___x_1331_ = lean_string_append(v___x_1330_, v_a_1326_);
lean_dec(v_a_1326_);
if (v_isShared_1329_ == 0)
{
lean_ctor_set(v___x_1328_, 0, v___x_1331_);
v___x_1333_ = v___x_1328_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(0, 1, 0);
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
else
{
if (lean_obj_tag(v___x_1325_) == 0)
{
lean_object* v_a_1336_; lean_object* v___x_1338_; uint8_t v_isShared_1339_; uint8_t v_isSharedCheck_1343_; 
lean_dec(v_a_1323_);
v_a_1336_ = lean_ctor_get(v___x_1325_, 0);
v_isSharedCheck_1343_ = !lean_is_exclusive(v___x_1325_);
if (v_isSharedCheck_1343_ == 0)
{
v___x_1338_ = v___x_1325_;
v_isShared_1339_ = v_isSharedCheck_1343_;
goto v_resetjp_1337_;
}
else
{
lean_inc(v_a_1336_);
lean_dec(v___x_1325_);
v___x_1338_ = lean_box(0);
v_isShared_1339_ = v_isSharedCheck_1343_;
goto v_resetjp_1337_;
}
v_resetjp_1337_:
{
lean_object* v___x_1341_; 
if (v_isShared_1339_ == 0)
{
lean_ctor_set_tag(v___x_1338_, 0);
v___x_1341_ = v___x_1338_;
goto v_reusejp_1340_;
}
else
{
lean_object* v_reuseFailAlloc_1342_; 
v_reuseFailAlloc_1342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1342_, 0, v_a_1336_);
v___x_1341_ = v_reuseFailAlloc_1342_;
goto v_reusejp_1340_;
}
v_reusejp_1340_:
{
return v___x_1341_;
}
}
}
else
{
lean_object* v_a_1344_; lean_object* v___x_1346_; uint8_t v_isShared_1347_; uint8_t v_isSharedCheck_1352_; 
v_a_1344_ = lean_ctor_get(v___x_1325_, 0);
v_isSharedCheck_1352_ = !lean_is_exclusive(v___x_1325_);
if (v_isSharedCheck_1352_ == 0)
{
v___x_1346_ = v___x_1325_;
v_isShared_1347_ = v_isSharedCheck_1352_;
goto v_resetjp_1345_;
}
else
{
lean_inc(v_a_1344_);
lean_dec(v___x_1325_);
v___x_1346_ = lean_box(0);
v_isShared_1347_ = v_isSharedCheck_1352_;
goto v_resetjp_1345_;
}
v_resetjp_1345_:
{
lean_object* v___x_1348_; lean_object* v___x_1350_; 
v___x_1348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1348_, 0, v_a_1323_);
lean_ctor_set(v___x_1348_, 1, v_a_1344_);
if (v_isShared_1347_ == 0)
{
lean_ctor_set(v___x_1346_, 0, v___x_1348_);
v___x_1350_ = v___x_1346_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1351_; 
v_reuseFailAlloc_1351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1351_, 0, v___x_1348_);
v___x_1350_ = v_reuseFailAlloc_1351_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
return v___x_1350_;
}
}
}
}
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPlainGoal_toJson_spec__0_spec__0(size_t v_sz_1355_, size_t v_i_1356_, lean_object* v_bs_1357_){
_start:
{
uint8_t v___x_1358_; 
v___x_1358_ = lean_usize_dec_lt(v_i_1356_, v_sz_1355_);
if (v___x_1358_ == 0)
{
return v_bs_1357_;
}
else
{
lean_object* v_v_1359_; lean_object* v___x_1360_; lean_object* v_bs_x27_1361_; lean_object* v___x_1362_; size_t v___x_1363_; size_t v___x_1364_; lean_object* v___x_1365_; 
v_v_1359_ = lean_array_uget(v_bs_1357_, v_i_1356_);
v___x_1360_ = lean_unsigned_to_nat(0u);
v_bs_x27_1361_ = lean_array_uset(v_bs_1357_, v_i_1356_, v___x_1360_);
v___x_1362_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1362_, 0, v_v_1359_);
v___x_1363_ = ((size_t)1ULL);
v___x_1364_ = lean_usize_add(v_i_1356_, v___x_1363_);
v___x_1365_ = lean_array_uset(v_bs_x27_1361_, v_i_1356_, v___x_1362_);
v_i_1356_ = v___x_1364_;
v_bs_1357_ = v___x_1365_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPlainGoal_toJson_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1355_ = stack[0].m_num;
size_t v_i_1356_ = stack[1].m_num;
lean_object* v_bs_1357_ = stack[2].m_obj;
lean_object* v_res_1367_;
v_res_1367_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPlainGoal_toJson_spec__0_spec__0(v_sz_1355_, v_i_1356_, v_bs_1357_);
stack->m_obj
 = v_res_1367_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPlainGoal_toJson_spec__0_spec__0___boxed(lean_object* v_sz_1368_, lean_object* v_i_1369_, lean_object* v_bs_1370_){
_start:
{
size_t v_sz_boxed_1371_; size_t v_i_boxed_1372_; lean_object* v_res_1373_; 
v_sz_boxed_1371_ = lean_unbox_usize(v_sz_1368_);
lean_dec(v_sz_1368_);
v_i_boxed_1372_ = lean_unbox_usize(v_i_1369_);
lean_dec(v_i_1369_);
v_res_1373_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPlainGoal_toJson_spec__0_spec__0(v_sz_boxed_1371_, v_i_boxed_1372_, v_bs_1370_);
return v_res_1373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonPlainGoal_toJson_spec__0(lean_object* v_a_1374_){
_start:
{
size_t v_sz_1375_; size_t v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; 
v_sz_1375_ = lean_array_size(v_a_1374_);
v___x_1376_ = ((size_t)0ULL);
v___x_1377_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonPlainGoal_toJson_spec__0_spec__0(v_sz_1375_, v___x_1376_, v_a_1374_);
v___x_1378_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1378_, 0, v___x_1377_);
return v___x_1378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonPlainGoal_toJson(lean_object* v_x_1379_){
_start:
{
lean_object* v_rendered_1380_; lean_object* v_goals_1381_; lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1401_; 
v_rendered_1380_ = lean_ctor_get(v_x_1379_, 0);
v_goals_1381_ = lean_ctor_get(v_x_1379_, 1);
v_isSharedCheck_1401_ = !lean_is_exclusive(v_x_1379_);
if (v_isSharedCheck_1401_ == 0)
{
v___x_1383_ = v_x_1379_;
v_isShared_1384_ = v_isSharedCheck_1401_;
goto v_resetjp_1382_;
}
else
{
lean_inc(v_goals_1381_);
lean_inc(v_rendered_1380_);
lean_dec(v_x_1379_);
v___x_1383_ = lean_box(0);
v_isShared_1384_ = v_isSharedCheck_1401_;
goto v_resetjp_1382_;
}
v_resetjp_1382_:
{
lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1388_; 
v___x_1385_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__0));
v___x_1386_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1386_, 0, v_rendered_1380_);
if (v_isShared_1384_ == 0)
{
lean_ctor_set(v___x_1383_, 1, v___x_1386_);
lean_ctor_set(v___x_1383_, 0, v___x_1385_);
v___x_1388_ = v___x_1383_;
goto v_reusejp_1387_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v___x_1385_);
lean_ctor_set(v_reuseFailAlloc_1400_, 1, v___x_1386_);
v___x_1388_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1387_;
}
v_reusejp_1387_:
{
lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; 
v___x_1389_ = lean_box(0);
v___x_1390_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1390_, 0, v___x_1388_);
lean_ctor_set(v___x_1390_, 1, v___x_1389_);
v___x_1391_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPlainGoal_fromJson___closed__9));
v___x_1392_ = l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonPlainGoal_toJson_spec__0(v_goals_1381_);
v___x_1393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1393_, 0, v___x_1391_);
lean_ctor_set(v___x_1393_, 1, v___x_1392_);
v___x_1394_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1394_, 0, v___x_1393_);
lean_ctor_set(v___x_1394_, 1, v___x_1389_);
v___x_1395_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1395_, 0, v___x_1394_);
lean_ctor_set(v___x_1395_, 1, v___x_1389_);
v___x_1396_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1396_, 0, v___x_1390_);
lean_ctor_set(v___x_1396_, 1, v___x_1395_);
v___x_1397_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0));
v___x_1398_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_1396_, v___x_1397_);
v___x_1399_ = l_Lean_Json_mkObj(v___x_1398_);
lean_dec(v___x_1398_);
return v___x_1399_;
}
}
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__2(void){
_start:
{
uint8_t v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; 
v___x_1409_ = 1;
v___x_1410_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__1));
v___x_1411_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1410_, v___x_1409_);
return v___x_1411_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__3(void){
_start:
{
lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; 
v___x_1412_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6));
v___x_1413_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__2, &l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__2);
v___x_1414_ = lean_string_append(v___x_1413_, v___x_1412_);
return v___x_1414_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; 
v___x_1415_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9, &l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9);
v___x_1416_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__3);
v___x_1417_ = lean_string_append(v___x_1416_, v___x_1415_);
return v___x_1417_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__5(void){
_start:
{
lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; 
v___x_1418_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_1419_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__4);
v___x_1420_ = lean_string_append(v___x_1419_, v___x_1418_);
return v___x_1420_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__6(void){
_start:
{
lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; 
v___x_1421_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__8);
v___x_1422_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__3);
v___x_1423_ = lean_string_append(v___x_1422_, v___x_1421_);
return v___x_1423_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__7(void){
_start:
{
lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; 
v___x_1424_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_1425_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__6, &l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__6);
v___x_1426_ = lean_string_append(v___x_1425_, v___x_1424_);
return v___x_1426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson(lean_object* v_json_1427_){
_start:
{
lean_object* v___x_1428_; lean_object* v___x_1429_; 
v___x_1428_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__0));
lean_inc(v_json_1427_);
v___x_1429_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoalParams_fromJson_spec__0(v_json_1427_, v___x_1428_);
if (lean_obj_tag(v___x_1429_) == 0)
{
lean_object* v_a_1430_; lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1439_; 
lean_dec(v_json_1427_);
v_a_1430_ = lean_ctor_get(v___x_1429_, 0);
v_isSharedCheck_1439_ = !lean_is_exclusive(v___x_1429_);
if (v_isSharedCheck_1439_ == 0)
{
v___x_1432_ = v___x_1429_;
v_isShared_1433_ = v_isSharedCheck_1439_;
goto v_resetjp_1431_;
}
else
{
lean_inc(v_a_1430_);
lean_dec(v___x_1429_);
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1439_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1437_; 
v___x_1434_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__5, &l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__5);
v___x_1435_ = lean_string_append(v___x_1434_, v_a_1430_);
lean_dec(v_a_1430_);
if (v_isShared_1433_ == 0)
{
lean_ctor_set(v___x_1432_, 0, v___x_1435_);
v___x_1437_ = v___x_1432_;
goto v_reusejp_1436_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v___x_1435_);
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
if (lean_obj_tag(v___x_1429_) == 0)
{
lean_object* v_a_1440_; lean_object* v___x_1442_; uint8_t v_isShared_1443_; uint8_t v_isSharedCheck_1447_; 
lean_dec(v_json_1427_);
v_a_1440_ = lean_ctor_get(v___x_1429_, 0);
v_isSharedCheck_1447_ = !lean_is_exclusive(v___x_1429_);
if (v_isSharedCheck_1447_ == 0)
{
v___x_1442_ = v___x_1429_;
v_isShared_1443_ = v_isSharedCheck_1447_;
goto v_resetjp_1441_;
}
else
{
lean_inc(v_a_1440_);
lean_dec(v___x_1429_);
v___x_1442_ = lean_box(0);
v_isShared_1443_ = v_isSharedCheck_1447_;
goto v_resetjp_1441_;
}
v_resetjp_1441_:
{
lean_object* v___x_1445_; 
if (v_isShared_1443_ == 0)
{
lean_ctor_set_tag(v___x_1442_, 0);
v___x_1445_ = v___x_1442_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v_a_1440_);
v___x_1445_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
return v___x_1445_;
}
}
}
else
{
lean_object* v_a_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; 
v_a_1448_ = lean_ctor_get(v___x_1429_, 0);
lean_inc(v_a_1448_);
lean_dec_ref_known(v___x_1429_, 1);
v___x_1449_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__6));
v___x_1450_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoalParams_fromJson_spec__1(v_json_1427_, v___x_1449_);
if (lean_obj_tag(v___x_1450_) == 0)
{
lean_object* v_a_1451_; lean_object* v___x_1453_; uint8_t v_isShared_1454_; uint8_t v_isSharedCheck_1460_; 
lean_dec(v_a_1448_);
v_a_1451_ = lean_ctor_get(v___x_1450_, 0);
v_isSharedCheck_1460_ = !lean_is_exclusive(v___x_1450_);
if (v_isSharedCheck_1460_ == 0)
{
v___x_1453_ = v___x_1450_;
v_isShared_1454_ = v_isSharedCheck_1460_;
goto v_resetjp_1452_;
}
else
{
lean_inc(v_a_1451_);
lean_dec(v___x_1450_);
v___x_1453_ = lean_box(0);
v_isShared_1454_ = v_isSharedCheck_1460_;
goto v_resetjp_1452_;
}
v_resetjp_1452_:
{
lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1458_; 
v___x_1455_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonPlainTermGoalParams_fromJson___closed__7);
v___x_1456_ = lean_string_append(v___x_1455_, v_a_1451_);
lean_dec(v_a_1451_);
if (v_isShared_1454_ == 0)
{
lean_ctor_set(v___x_1453_, 0, v___x_1456_);
v___x_1458_ = v___x_1453_;
goto v_reusejp_1457_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v___x_1456_);
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
if (lean_obj_tag(v___x_1450_) == 0)
{
lean_object* v_a_1461_; lean_object* v___x_1463_; uint8_t v_isShared_1464_; uint8_t v_isSharedCheck_1468_; 
lean_dec(v_a_1448_);
v_a_1461_ = lean_ctor_get(v___x_1450_, 0);
v_isSharedCheck_1468_ = !lean_is_exclusive(v___x_1450_);
if (v_isSharedCheck_1468_ == 0)
{
v___x_1463_ = v___x_1450_;
v_isShared_1464_ = v_isSharedCheck_1468_;
goto v_resetjp_1462_;
}
else
{
lean_inc(v_a_1461_);
lean_dec(v___x_1450_);
v___x_1463_ = lean_box(0);
v_isShared_1464_ = v_isSharedCheck_1468_;
goto v_resetjp_1462_;
}
v_resetjp_1462_:
{
lean_object* v___x_1466_; 
if (v_isShared_1464_ == 0)
{
lean_ctor_set_tag(v___x_1463_, 0);
v___x_1466_ = v___x_1463_;
goto v_reusejp_1465_;
}
else
{
lean_object* v_reuseFailAlloc_1467_; 
v_reuseFailAlloc_1467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1467_, 0, v_a_1461_);
v___x_1466_ = v_reuseFailAlloc_1467_;
goto v_reusejp_1465_;
}
v_reusejp_1465_:
{
return v___x_1466_;
}
}
}
else
{
lean_object* v_a_1469_; lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1477_; 
v_a_1469_ = lean_ctor_get(v___x_1450_, 0);
v_isSharedCheck_1477_ = !lean_is_exclusive(v___x_1450_);
if (v_isSharedCheck_1477_ == 0)
{
v___x_1471_ = v___x_1450_;
v_isShared_1472_ = v_isSharedCheck_1477_;
goto v_resetjp_1470_;
}
else
{
lean_inc(v_a_1469_);
lean_dec(v___x_1450_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1477_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
lean_object* v___x_1473_; lean_object* v___x_1475_; 
v___x_1473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1473_, 0, v_a_1448_);
lean_ctor_set(v___x_1473_, 1, v_a_1469_);
if (v_isShared_1472_ == 0)
{
lean_ctor_set(v___x_1471_, 0, v___x_1473_);
v___x_1475_ = v___x_1471_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1476_; 
v_reuseFailAlloc_1476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1476_, 0, v___x_1473_);
v___x_1475_ = v_reuseFailAlloc_1476_;
goto v_reusejp_1474_;
}
v_reusejp_1474_:
{
return v___x_1475_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonPlainTermGoalParams_toJson(lean_object* v_x_1480_){
_start:
{
lean_object* v_textDocument_1481_; lean_object* v_position_1482_; lean_object* v___x_1484_; uint8_t v_isShared_1485_; uint8_t v_isSharedCheck_1502_; 
v_textDocument_1481_ = lean_ctor_get(v_x_1480_, 0);
v_position_1482_ = lean_ctor_get(v_x_1480_, 1);
v_isSharedCheck_1502_ = !lean_is_exclusive(v_x_1480_);
if (v_isSharedCheck_1502_ == 0)
{
v___x_1484_ = v_x_1480_;
v_isShared_1485_ = v_isSharedCheck_1502_;
goto v_resetjp_1483_;
}
else
{
lean_inc(v_position_1482_);
lean_inc(v_textDocument_1481_);
lean_dec(v_x_1480_);
v___x_1484_ = lean_box(0);
v_isShared_1485_ = v_isSharedCheck_1502_;
goto v_resetjp_1483_;
}
v_resetjp_1483_:
{
lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1489_; 
v___x_1486_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__0));
v___x_1487_ = l_Lean_Lsp_instToJsonTextDocumentIdentifier_toJson(v_textDocument_1481_);
if (v_isShared_1485_ == 0)
{
lean_ctor_set(v___x_1484_, 1, v___x_1487_);
lean_ctor_set(v___x_1484_, 0, v___x_1486_);
v___x_1489_ = v___x_1484_;
goto v_reusejp_1488_;
}
else
{
lean_object* v_reuseFailAlloc_1501_; 
v_reuseFailAlloc_1501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1501_, 0, v___x_1486_);
lean_ctor_set(v_reuseFailAlloc_1501_, 1, v___x_1487_);
v___x_1489_ = v_reuseFailAlloc_1501_;
goto v_reusejp_1488_;
}
v_reusejp_1488_:
{
lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; 
v___x_1490_ = lean_box(0);
v___x_1491_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1491_, 0, v___x_1489_);
lean_ctor_set(v___x_1491_, 1, v___x_1490_);
v___x_1492_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__6));
v___x_1493_ = l_Lean_Lsp_instToJsonPosition_toJson(v_position_1482_);
v___x_1494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1494_, 0, v___x_1492_);
lean_ctor_set(v___x_1494_, 1, v___x_1493_);
v___x_1495_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1495_, 0, v___x_1494_);
lean_ctor_set(v___x_1495_, 1, v___x_1490_);
v___x_1496_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1496_, 0, v___x_1495_);
lean_ctor_set(v___x_1496_, 1, v___x_1490_);
v___x_1497_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1497_, 0, v___x_1491_);
lean_ctor_set(v___x_1497_, 1, v___x_1496_);
v___x_1498_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0));
v___x_1499_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_1497_, v___x_1498_);
v___x_1500_ = l_Lean_Json_mkObj(v___x_1499_);
lean_dec(v___x_1499_);
return v___x_1500_;
}
}
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__3(void){
_start:
{
uint8_t v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; 
v___x_1511_ = 1;
v___x_1512_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__2));
v___x_1513_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1512_, v___x_1511_);
return v___x_1513_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__4(void){
_start:
{
lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; 
v___x_1514_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6));
v___x_1515_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__3, &l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__3);
v___x_1516_ = lean_string_append(v___x_1515_, v___x_1514_);
return v___x_1516_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__6(void){
_start:
{
uint8_t v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; 
v___x_1519_ = 1;
v___x_1520_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__5));
v___x_1521_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1520_, v___x_1519_);
return v___x_1521_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__7(void){
_start:
{
lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; 
v___x_1522_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__6, &l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__6);
v___x_1523_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__4, &l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__4);
v___x_1524_ = lean_string_append(v___x_1523_, v___x_1522_);
return v___x_1524_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__8(void){
_start:
{
lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; 
v___x_1525_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_1526_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__7, &l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__7);
v___x_1527_ = lean_string_append(v___x_1526_, v___x_1525_);
return v___x_1527_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__9(void){
_start:
{
lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; 
v___x_1528_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__6);
v___x_1529_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__4, &l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__4);
v___x_1530_ = lean_string_append(v___x_1529_, v___x_1528_);
return v___x_1530_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__10(void){
_start:
{
lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; 
v___x_1531_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_1532_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__9, &l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__9);
v___x_1533_ = lean_string_append(v___x_1532_, v___x_1531_);
return v___x_1533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson(lean_object* v_json_1534_){
_start:
{
lean_object* v___x_1535_; lean_object* v___x_1536_; 
v___x_1535_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__0));
lean_inc(v_json_1534_);
v___x_1536_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson_spec__0(v_json_1534_, v___x_1535_);
if (lean_obj_tag(v___x_1536_) == 0)
{
lean_object* v_a_1537_; lean_object* v___x_1539_; uint8_t v_isShared_1540_; uint8_t v_isSharedCheck_1546_; 
lean_dec(v_json_1534_);
v_a_1537_ = lean_ctor_get(v___x_1536_, 0);
v_isSharedCheck_1546_ = !lean_is_exclusive(v___x_1536_);
if (v_isSharedCheck_1546_ == 0)
{
v___x_1539_ = v___x_1536_;
v_isShared_1540_ = v_isSharedCheck_1546_;
goto v_resetjp_1538_;
}
else
{
lean_inc(v_a_1537_);
lean_dec(v___x_1536_);
v___x_1539_ = lean_box(0);
v_isShared_1540_ = v_isSharedCheck_1546_;
goto v_resetjp_1538_;
}
v_resetjp_1538_:
{
lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1544_; 
v___x_1541_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__8, &l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__8);
v___x_1542_ = lean_string_append(v___x_1541_, v_a_1537_);
lean_dec(v_a_1537_);
if (v_isShared_1540_ == 0)
{
lean_ctor_set(v___x_1539_, 0, v___x_1542_);
v___x_1544_ = v___x_1539_;
goto v_reusejp_1543_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v___x_1542_);
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
if (lean_obj_tag(v___x_1536_) == 0)
{
lean_object* v_a_1547_; lean_object* v___x_1549_; uint8_t v_isShared_1550_; uint8_t v_isSharedCheck_1554_; 
lean_dec(v_json_1534_);
v_a_1547_ = lean_ctor_get(v___x_1536_, 0);
v_isSharedCheck_1554_ = !lean_is_exclusive(v___x_1536_);
if (v_isSharedCheck_1554_ == 0)
{
v___x_1549_ = v___x_1536_;
v_isShared_1550_ = v_isSharedCheck_1554_;
goto v_resetjp_1548_;
}
else
{
lean_inc(v_a_1547_);
lean_dec(v___x_1536_);
v___x_1549_ = lean_box(0);
v_isShared_1550_ = v_isSharedCheck_1554_;
goto v_resetjp_1548_;
}
v_resetjp_1548_:
{
lean_object* v___x_1552_; 
if (v_isShared_1550_ == 0)
{
lean_ctor_set_tag(v___x_1549_, 0);
v___x_1552_ = v___x_1549_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v_a_1547_);
v___x_1552_ = v_reuseFailAlloc_1553_;
goto v_reusejp_1551_;
}
v_reusejp_1551_:
{
return v___x_1552_;
}
}
}
else
{
lean_object* v_a_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; 
v_a_1555_ = lean_ctor_get(v___x_1536_, 0);
lean_inc(v_a_1555_);
lean_dec_ref_known(v___x_1536_, 1);
v___x_1556_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__0));
v___x_1557_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson_spec__0(v_json_1534_, v___x_1556_);
if (lean_obj_tag(v___x_1557_) == 0)
{
lean_object* v_a_1558_; lean_object* v___x_1560_; uint8_t v_isShared_1561_; uint8_t v_isSharedCheck_1567_; 
lean_dec(v_a_1555_);
v_a_1558_ = lean_ctor_get(v___x_1557_, 0);
v_isSharedCheck_1567_ = !lean_is_exclusive(v___x_1557_);
if (v_isSharedCheck_1567_ == 0)
{
v___x_1560_ = v___x_1557_;
v_isShared_1561_ = v_isSharedCheck_1567_;
goto v_resetjp_1559_;
}
else
{
lean_inc(v_a_1558_);
lean_dec(v___x_1557_);
v___x_1560_ = lean_box(0);
v_isShared_1561_ = v_isSharedCheck_1567_;
goto v_resetjp_1559_;
}
v_resetjp_1559_:
{
lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1565_; 
v___x_1562_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__10, &l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__10);
v___x_1563_ = lean_string_append(v___x_1562_, v_a_1558_);
lean_dec(v_a_1558_);
if (v_isShared_1561_ == 0)
{
lean_ctor_set(v___x_1560_, 0, v___x_1563_);
v___x_1565_ = v___x_1560_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v___x_1563_);
v___x_1565_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
return v___x_1565_;
}
}
}
else
{
if (lean_obj_tag(v___x_1557_) == 0)
{
lean_object* v_a_1568_; lean_object* v___x_1570_; uint8_t v_isShared_1571_; uint8_t v_isSharedCheck_1575_; 
lean_dec(v_a_1555_);
v_a_1568_ = lean_ctor_get(v___x_1557_, 0);
v_isSharedCheck_1575_ = !lean_is_exclusive(v___x_1557_);
if (v_isSharedCheck_1575_ == 0)
{
v___x_1570_ = v___x_1557_;
v_isShared_1571_ = v_isSharedCheck_1575_;
goto v_resetjp_1569_;
}
else
{
lean_inc(v_a_1568_);
lean_dec(v___x_1557_);
v___x_1570_ = lean_box(0);
v_isShared_1571_ = v_isSharedCheck_1575_;
goto v_resetjp_1569_;
}
v_resetjp_1569_:
{
lean_object* v___x_1573_; 
if (v_isShared_1571_ == 0)
{
lean_ctor_set_tag(v___x_1570_, 0);
v___x_1573_ = v___x_1570_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1574_; 
v_reuseFailAlloc_1574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1574_, 0, v_a_1568_);
v___x_1573_ = v_reuseFailAlloc_1574_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
return v___x_1573_;
}
}
}
else
{
lean_object* v_a_1576_; lean_object* v___x_1578_; uint8_t v_isShared_1579_; uint8_t v_isSharedCheck_1584_; 
v_a_1576_ = lean_ctor_get(v___x_1557_, 0);
v_isSharedCheck_1584_ = !lean_is_exclusive(v___x_1557_);
if (v_isSharedCheck_1584_ == 0)
{
v___x_1578_ = v___x_1557_;
v_isShared_1579_ = v_isSharedCheck_1584_;
goto v_resetjp_1577_;
}
else
{
lean_inc(v_a_1576_);
lean_dec(v___x_1557_);
v___x_1578_ = lean_box(0);
v_isShared_1579_ = v_isSharedCheck_1584_;
goto v_resetjp_1577_;
}
v_resetjp_1577_:
{
lean_object* v___x_1580_; lean_object* v___x_1582_; 
v___x_1580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1580_, 0, v_a_1555_);
lean_ctor_set(v___x_1580_, 1, v_a_1576_);
if (v_isShared_1579_ == 0)
{
lean_ctor_set(v___x_1578_, 0, v___x_1580_);
v___x_1582_ = v___x_1578_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v___x_1580_);
v___x_1582_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
return v___x_1582_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonPlainTermGoal_toJson(lean_object* v_x_1587_){
_start:
{
lean_object* v_goal_1588_; lean_object* v_range_1589_; lean_object* v___x_1591_; uint8_t v_isShared_1592_; uint8_t v_isSharedCheck_1609_; 
v_goal_1588_ = lean_ctor_get(v_x_1587_, 0);
v_range_1589_ = lean_ctor_get(v_x_1587_, 1);
v_isSharedCheck_1609_ = !lean_is_exclusive(v_x_1587_);
if (v_isSharedCheck_1609_ == 0)
{
v___x_1591_ = v_x_1587_;
v_isShared_1592_ = v_isSharedCheck_1609_;
goto v_resetjp_1590_;
}
else
{
lean_inc(v_range_1589_);
lean_inc(v_goal_1588_);
lean_dec(v_x_1587_);
v___x_1591_ = lean_box(0);
v_isShared_1592_ = v_isSharedCheck_1609_;
goto v_resetjp_1590_;
}
v_resetjp_1590_:
{
lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1596_; 
v___x_1593_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPlainTermGoal_fromJson___closed__0));
v___x_1594_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1594_, 0, v_goal_1588_);
if (v_isShared_1592_ == 0)
{
lean_ctor_set(v___x_1591_, 1, v___x_1594_);
lean_ctor_set(v___x_1591_, 0, v___x_1593_);
v___x_1596_ = v___x_1591_;
goto v_reusejp_1595_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v___x_1593_);
lean_ctor_set(v_reuseFailAlloc_1608_, 1, v___x_1594_);
v___x_1596_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1595_;
}
v_reusejp_1595_:
{
lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; 
v___x_1597_ = lean_box(0);
v___x_1598_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1598_, 0, v___x_1596_);
lean_ctor_set(v___x_1598_, 1, v___x_1597_);
v___x_1599_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__0));
v___x_1600_ = l_Lean_Lsp_instToJsonRange_toJson(v_range_1589_);
v___x_1601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1601_, 0, v___x_1599_);
lean_ctor_set(v___x_1601_, 1, v___x_1600_);
v___x_1602_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1602_, 0, v___x_1601_);
lean_ctor_set(v___x_1602_, 1, v___x_1597_);
v___x_1603_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1603_, 0, v___x_1602_);
lean_ctor_set(v___x_1603_, 1, v___x_1597_);
v___x_1604_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1604_, 0, v___x_1598_);
lean_ctor_set(v___x_1604_, 1, v___x_1603_);
v___x_1605_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0));
v___x_1606_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_1604_, v___x_1605_);
v___x_1607_ = l_Lean_Json_mkObj(v___x_1606_);
lean_dec(v___x_1606_);
return v___x_1607_;
}
}
}
}
lean_object* l_Lean_Lsp_instFromJsonModuleHierarchyOptions_fromJson___redArg(){
_start:
{
lean_object* v___x_1615_; 
v___x_1615_ = ((lean_object*)(l_Lean_Lsp_instFromJsonModuleHierarchyOptions_fromJson___redArg___closed__0));
return v___x_1615_;
}
}
LEAN_EXPORT void l_Lean_Lsp_instFromJsonModuleHierarchyOptions_fromJson___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1616_;
v_res_1616_ = l_Lean_Lsp_instFromJsonModuleHierarchyOptions_fromJson___redArg();
stack->m_obj
 = v_res_1616_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonModuleHierarchyOptions_fromJson___redArg___boxed(lean_object* v___dummy_1617_){
_start:
{
lean_object* v_res_1618_; 
v_res_1618_ = l_Lean_Lsp_instFromJsonModuleHierarchyOptions_fromJson___redArg();
return v_res_1618_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonModuleHierarchyOptions_fromJson___closed__0(void){
_start:
{
lean_object* v___x_1619_; 
v___x_1619_ = l_Lean_Lsp_instFromJsonModuleHierarchyOptions_fromJson___redArg();
return v___x_1619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonModuleHierarchyOptions_fromJson(lean_object* v_json_1620_){
_start:
{
lean_object* v___x_1621_; 
v___x_1621_ = lean_obj_once(&l_Lean_Lsp_instFromJsonModuleHierarchyOptions_fromJson___closed__0, &l_Lean_Lsp_instFromJsonModuleHierarchyOptions_fromJson___closed__0_once, _init_l_Lean_Lsp_instFromJsonModuleHierarchyOptions_fromJson___closed__0);
return v___x_1621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonModuleHierarchyOptions_fromJson___boxed(lean_object* v_json_1622_){
_start:
{
lean_object* v_res_1623_; 
v_res_1623_ = l_Lean_Lsp_instFromJsonModuleHierarchyOptions_fromJson(v_json_1622_);
lean_dec(v_json_1622_);
return v_res_1623_;
}
}
lean_object* l_Lean_Lsp_instToJsonModuleHierarchyOptions_toJson___redArg(){
_start:
{
lean_object* v___x_1627_; 
v___x_1627_ = lean_obj_once(&l_Lean_Lsp_instToJsonWaitForILeans_toJson___redArg___closed__1, &l_Lean_Lsp_instToJsonWaitForILeans_toJson___redArg___closed__1_once, _init_l_Lean_Lsp_instToJsonWaitForILeans_toJson___redArg___closed__1);
return v___x_1627_;
}
}
LEAN_EXPORT void l_Lean_Lsp_instToJsonModuleHierarchyOptions_toJson___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1628_;
v_res_1628_ = l_Lean_Lsp_instToJsonModuleHierarchyOptions_toJson___redArg();
stack->m_obj
 = v_res_1628_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonModuleHierarchyOptions_toJson___redArg___boxed(lean_object* v___dummy_1629_){
_start:
{
lean_object* v_res_1630_; 
v_res_1630_ = l_Lean_Lsp_instToJsonModuleHierarchyOptions_toJson___redArg();
return v_res_1630_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonModuleHierarchyOptions_toJson___closed__0(void){
_start:
{
lean_object* v___x_1631_; 
v___x_1631_ = l_Lean_Lsp_instToJsonModuleHierarchyOptions_toJson___redArg();
return v___x_1631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonModuleHierarchyOptions_toJson(lean_object* v_x_1632_){
_start:
{
lean_object* v___x_1633_; 
v___x_1633_ = lean_obj_once(&l_Lean_Lsp_instToJsonModuleHierarchyOptions_toJson___closed__0, &l_Lean_Lsp_instToJsonModuleHierarchyOptions_toJson___closed__0_once, _init_l_Lean_Lsp_instToJsonModuleHierarchyOptions_toJson___closed__0);
return v___x_1633_;
}
}
lean_object* l_Lean_Lsp_instFromJsonHighlightMatchesOptions_fromJson___redArg(){
_start:
{
lean_object* v___x_1639_; 
v___x_1639_ = ((lean_object*)(l_Lean_Lsp_instFromJsonHighlightMatchesOptions_fromJson___redArg___closed__0));
return v___x_1639_;
}
}
LEAN_EXPORT void l_Lean_Lsp_instFromJsonHighlightMatchesOptions_fromJson___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1640_;
v_res_1640_ = l_Lean_Lsp_instFromJsonHighlightMatchesOptions_fromJson___redArg();
stack->m_obj
 = v_res_1640_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonHighlightMatchesOptions_fromJson___redArg___boxed(lean_object* v___dummy_1641_){
_start:
{
lean_object* v_res_1642_; 
v_res_1642_ = l_Lean_Lsp_instFromJsonHighlightMatchesOptions_fromJson___redArg();
return v_res_1642_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonHighlightMatchesOptions_fromJson___closed__0(void){
_start:
{
lean_object* v___x_1643_; 
v___x_1643_ = l_Lean_Lsp_instFromJsonHighlightMatchesOptions_fromJson___redArg();
return v___x_1643_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonHighlightMatchesOptions_fromJson(lean_object* v_json_1644_){
_start:
{
lean_object* v___x_1645_; 
v___x_1645_ = lean_obj_once(&l_Lean_Lsp_instFromJsonHighlightMatchesOptions_fromJson___closed__0, &l_Lean_Lsp_instFromJsonHighlightMatchesOptions_fromJson___closed__0_once, _init_l_Lean_Lsp_instFromJsonHighlightMatchesOptions_fromJson___closed__0);
return v___x_1645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonHighlightMatchesOptions_fromJson___boxed(lean_object* v_json_1646_){
_start:
{
lean_object* v_res_1647_; 
v_res_1647_ = l_Lean_Lsp_instFromJsonHighlightMatchesOptions_fromJson(v_json_1646_);
lean_dec(v_json_1646_);
return v_res_1647_;
}
}
lean_object* l_Lean_Lsp_instToJsonHighlightMatchesOptions_toJson___redArg(){
_start:
{
lean_object* v___x_1651_; 
v___x_1651_ = lean_obj_once(&l_Lean_Lsp_instToJsonWaitForILeans_toJson___redArg___closed__1, &l_Lean_Lsp_instToJsonWaitForILeans_toJson___redArg___closed__1_once, _init_l_Lean_Lsp_instToJsonWaitForILeans_toJson___redArg___closed__1);
return v___x_1651_;
}
}
LEAN_EXPORT void l_Lean_Lsp_instToJsonHighlightMatchesOptions_toJson___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1652_;
v_res_1652_ = l_Lean_Lsp_instToJsonHighlightMatchesOptions_toJson___redArg();
stack->m_obj
 = v_res_1652_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonHighlightMatchesOptions_toJson___redArg___boxed(lean_object* v___dummy_1653_){
_start:
{
lean_object* v_res_1654_; 
v_res_1654_ = l_Lean_Lsp_instToJsonHighlightMatchesOptions_toJson___redArg();
return v_res_1654_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonHighlightMatchesOptions_toJson___closed__0(void){
_start:
{
lean_object* v___x_1655_; 
v___x_1655_ = l_Lean_Lsp_instToJsonHighlightMatchesOptions_toJson___redArg();
return v___x_1655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonHighlightMatchesOptions_toJson(lean_object* v_x_1656_){
_start:
{
lean_object* v___x_1657_; 
v___x_1657_ = lean_obj_once(&l_Lean_Lsp_instToJsonHighlightMatchesOptions_toJson___closed__0, &l_Lean_Lsp_instToJsonHighlightMatchesOptions_toJson___closed__0_once, _init_l_Lean_Lsp_instToJsonHighlightMatchesOptions_toJson___closed__0);
return v___x_1657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__1_spec__2(lean_object* v_x_1662_){
_start:
{
if (lean_obj_tag(v_x_1662_) == 0)
{
lean_object* v___x_1663_; 
v___x_1663_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__1_spec__2___closed__0));
return v___x_1663_;
}
else
{
lean_object* v___x_1664_; 
v___x_1664_ = l_Lean_Lsp_instFromJsonRpcWireFormat_fromJson(v_x_1662_);
if (lean_obj_tag(v___x_1664_) == 0)
{
lean_object* v_a_1665_; lean_object* v___x_1667_; uint8_t v_isShared_1668_; uint8_t v_isSharedCheck_1672_; 
v_a_1665_ = lean_ctor_get(v___x_1664_, 0);
v_isSharedCheck_1672_ = !lean_is_exclusive(v___x_1664_);
if (v_isSharedCheck_1672_ == 0)
{
v___x_1667_ = v___x_1664_;
v_isShared_1668_ = v_isSharedCheck_1672_;
goto v_resetjp_1666_;
}
else
{
lean_inc(v_a_1665_);
lean_dec(v___x_1664_);
v___x_1667_ = lean_box(0);
v_isShared_1668_ = v_isSharedCheck_1672_;
goto v_resetjp_1666_;
}
v_resetjp_1666_:
{
lean_object* v___x_1670_; 
if (v_isShared_1668_ == 0)
{
v___x_1670_ = v___x_1667_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1671_; 
v_reuseFailAlloc_1671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1671_, 0, v_a_1665_);
v___x_1670_ = v_reuseFailAlloc_1671_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
return v___x_1670_;
}
}
}
else
{
lean_object* v_a_1673_; lean_object* v___x_1675_; uint8_t v_isShared_1676_; uint8_t v_isSharedCheck_1681_; 
v_a_1673_ = lean_ctor_get(v___x_1664_, 0);
v_isSharedCheck_1681_ = !lean_is_exclusive(v___x_1664_);
if (v_isSharedCheck_1681_ == 0)
{
v___x_1675_ = v___x_1664_;
v_isShared_1676_ = v_isSharedCheck_1681_;
goto v_resetjp_1674_;
}
else
{
lean_inc(v_a_1673_);
lean_dec(v___x_1664_);
v___x_1675_ = lean_box(0);
v_isShared_1676_ = v_isSharedCheck_1681_;
goto v_resetjp_1674_;
}
v_resetjp_1674_:
{
lean_object* v___x_1677_; lean_object* v___x_1679_; 
v___x_1677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1677_, 0, v_a_1673_);
if (v_isShared_1676_ == 0)
{
lean_ctor_set(v___x_1675_, 0, v___x_1677_);
v___x_1679_ = v___x_1675_;
goto v_reusejp_1678_;
}
else
{
lean_object* v_reuseFailAlloc_1680_; 
v_reuseFailAlloc_1680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1680_, 0, v___x_1677_);
v___x_1679_ = v_reuseFailAlloc_1680_;
goto v_reusejp_1678_;
}
v_reusejp_1678_:
{
return v___x_1679_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__1(lean_object* v_j_1682_, lean_object* v_k_1683_){
_start:
{
lean_object* v___x_1684_; lean_object* v___x_1685_; 
v___x_1684_ = l_Lean_Json_getObjValD(v_j_1682_, v_k_1683_);
v___x_1685_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__1_spec__2(v___x_1684_);
return v___x_1685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__1___boxed(lean_object* v_j_1686_, lean_object* v_k_1687_){
_start:
{
lean_object* v_res_1688_; 
v_res_1688_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__1(v_j_1686_, v_k_1687_);
lean_dec_ref(v_k_1687_);
return v_res_1688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__0_spec__0(lean_object* v_x_1691_){
_start:
{
if (lean_obj_tag(v_x_1691_) == 0)
{
lean_object* v___x_1692_; 
v___x_1692_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__0_spec__0___closed__0));
return v___x_1692_;
}
else
{
lean_object* v___x_1693_; lean_object* v_a_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; 
v___x_1693_ = lean_obj_once(&l_Lean_Lsp_instFromJsonHighlightMatchesOptions_fromJson___closed__0, &l_Lean_Lsp_instFromJsonHighlightMatchesOptions_fromJson___closed__0_once, _init_l_Lean_Lsp_instFromJsonHighlightMatchesOptions_fromJson___closed__0);
v_a_1694_ = lean_ctor_get(v___x_1693_, 0);
lean_inc(v_a_1694_);
v___x_1695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1695_, 0, v_a_1694_);
v___x_1696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1696_, 0, v___x_1695_);
return v___x_1696_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__0_spec__0___boxed(lean_object* v_x_1697_){
_start:
{
lean_object* v_res_1698_; 
v_res_1698_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__0_spec__0(v_x_1697_);
lean_dec(v_x_1697_);
return v_res_1698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__0(lean_object* v_j_1699_, lean_object* v_k_1700_){
_start:
{
lean_object* v___x_1701_; lean_object* v___x_1702_; 
v___x_1701_ = l_Lean_Json_getObjValD(v_j_1699_, v_k_1700_);
v___x_1702_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__0_spec__0(v___x_1701_);
lean_dec(v___x_1701_);
return v___x_1702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__0___boxed(lean_object* v_j_1703_, lean_object* v_k_1704_){
_start:
{
lean_object* v_res_1705_; 
v_res_1705_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__0(v_j_1703_, v_k_1704_);
lean_dec_ref(v_k_1704_);
return v_res_1705_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__3(void){
_start:
{
uint8_t v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; 
v___x_1712_ = 1;
v___x_1713_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__2));
v___x_1714_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1713_, v___x_1712_);
return v___x_1714_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__4(void){
_start:
{
lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; 
v___x_1715_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6));
v___x_1716_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__3, &l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__3);
v___x_1717_ = lean_string_append(v___x_1716_, v___x_1715_);
return v___x_1717_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__7(void){
_start:
{
uint8_t v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; 
v___x_1721_ = 1;
v___x_1722_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__6));
v___x_1723_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1722_, v___x_1721_);
return v___x_1723_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__8(void){
_start:
{
lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; 
v___x_1724_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__7, &l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__7);
v___x_1725_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__4, &l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__4);
v___x_1726_ = lean_string_append(v___x_1725_, v___x_1724_);
return v___x_1726_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__9(void){
_start:
{
lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; 
v___x_1727_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_1728_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__8, &l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__8);
v___x_1729_ = lean_string_append(v___x_1728_, v___x_1727_);
return v___x_1729_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__13(void){
_start:
{
uint8_t v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; 
v___x_1734_ = 1;
v___x_1735_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__12));
v___x_1736_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1735_, v___x_1734_);
return v___x_1736_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__14(void){
_start:
{
lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; 
v___x_1737_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__13, &l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__13);
v___x_1738_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__4, &l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__4);
v___x_1739_ = lean_string_append(v___x_1738_, v___x_1737_);
return v___x_1739_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__15(void){
_start:
{
lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; 
v___x_1740_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_1741_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__14, &l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__14_once, _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__14);
v___x_1742_ = lean_string_append(v___x_1741_, v___x_1740_);
return v___x_1742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonRpcOptions_fromJson(lean_object* v_json_1743_){
_start:
{
lean_object* v___x_1744_; lean_object* v___x_1745_; 
v___x_1744_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__0));
lean_inc(v_json_1743_);
v___x_1745_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__0(v_json_1743_, v___x_1744_);
if (lean_obj_tag(v___x_1745_) == 0)
{
lean_object* v_a_1746_; lean_object* v___x_1748_; uint8_t v_isShared_1749_; uint8_t v_isSharedCheck_1755_; 
lean_dec(v_json_1743_);
v_a_1746_ = lean_ctor_get(v___x_1745_, 0);
v_isSharedCheck_1755_ = !lean_is_exclusive(v___x_1745_);
if (v_isSharedCheck_1755_ == 0)
{
v___x_1748_ = v___x_1745_;
v_isShared_1749_ = v_isSharedCheck_1755_;
goto v_resetjp_1747_;
}
else
{
lean_inc(v_a_1746_);
lean_dec(v___x_1745_);
v___x_1748_ = lean_box(0);
v_isShared_1749_ = v_isSharedCheck_1755_;
goto v_resetjp_1747_;
}
v_resetjp_1747_:
{
lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1753_; 
v___x_1750_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__9, &l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__9);
v___x_1751_ = lean_string_append(v___x_1750_, v_a_1746_);
lean_dec(v_a_1746_);
if (v_isShared_1749_ == 0)
{
lean_ctor_set(v___x_1748_, 0, v___x_1751_);
v___x_1753_ = v___x_1748_;
goto v_reusejp_1752_;
}
else
{
lean_object* v_reuseFailAlloc_1754_; 
v_reuseFailAlloc_1754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1754_, 0, v___x_1751_);
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
if (lean_obj_tag(v___x_1745_) == 0)
{
lean_object* v_a_1756_; lean_object* v___x_1758_; uint8_t v_isShared_1759_; uint8_t v_isSharedCheck_1763_; 
lean_dec(v_json_1743_);
v_a_1756_ = lean_ctor_get(v___x_1745_, 0);
v_isSharedCheck_1763_ = !lean_is_exclusive(v___x_1745_);
if (v_isSharedCheck_1763_ == 0)
{
v___x_1758_ = v___x_1745_;
v_isShared_1759_ = v_isSharedCheck_1763_;
goto v_resetjp_1757_;
}
else
{
lean_inc(v_a_1756_);
lean_dec(v___x_1745_);
v___x_1758_ = lean_box(0);
v_isShared_1759_ = v_isSharedCheck_1763_;
goto v_resetjp_1757_;
}
v_resetjp_1757_:
{
lean_object* v___x_1761_; 
if (v_isShared_1759_ == 0)
{
lean_ctor_set_tag(v___x_1758_, 0);
v___x_1761_ = v___x_1758_;
goto v_reusejp_1760_;
}
else
{
lean_object* v_reuseFailAlloc_1762_; 
v_reuseFailAlloc_1762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1762_, 0, v_a_1756_);
v___x_1761_ = v_reuseFailAlloc_1762_;
goto v_reusejp_1760_;
}
v_reusejp_1760_:
{
return v___x_1761_;
}
}
}
else
{
lean_object* v_a_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; 
v_a_1764_ = lean_ctor_get(v___x_1745_, 0);
lean_inc(v_a_1764_);
lean_dec_ref_known(v___x_1745_, 1);
v___x_1765_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__10));
v___x_1766_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcOptions_fromJson_spec__1(v_json_1743_, v___x_1765_);
if (lean_obj_tag(v___x_1766_) == 0)
{
lean_object* v_a_1767_; lean_object* v___x_1769_; uint8_t v_isShared_1770_; uint8_t v_isSharedCheck_1776_; 
lean_dec(v_a_1764_);
v_a_1767_ = lean_ctor_get(v___x_1766_, 0);
v_isSharedCheck_1776_ = !lean_is_exclusive(v___x_1766_);
if (v_isSharedCheck_1776_ == 0)
{
v___x_1769_ = v___x_1766_;
v_isShared_1770_ = v_isSharedCheck_1776_;
goto v_resetjp_1768_;
}
else
{
lean_inc(v_a_1767_);
lean_dec(v___x_1766_);
v___x_1769_ = lean_box(0);
v_isShared_1770_ = v_isSharedCheck_1776_;
goto v_resetjp_1768_;
}
v_resetjp_1768_:
{
lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1774_; 
v___x_1771_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__15, &l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__15_once, _init_l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__15);
v___x_1772_ = lean_string_append(v___x_1771_, v_a_1767_);
lean_dec(v_a_1767_);
if (v_isShared_1770_ == 0)
{
lean_ctor_set(v___x_1769_, 0, v___x_1772_);
v___x_1774_ = v___x_1769_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1775_; 
v_reuseFailAlloc_1775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1775_, 0, v___x_1772_);
v___x_1774_ = v_reuseFailAlloc_1775_;
goto v_reusejp_1773_;
}
v_reusejp_1773_:
{
return v___x_1774_;
}
}
}
else
{
if (lean_obj_tag(v___x_1766_) == 0)
{
lean_object* v_a_1777_; lean_object* v___x_1779_; uint8_t v_isShared_1780_; uint8_t v_isSharedCheck_1784_; 
lean_dec(v_a_1764_);
v_a_1777_ = lean_ctor_get(v___x_1766_, 0);
v_isSharedCheck_1784_ = !lean_is_exclusive(v___x_1766_);
if (v_isSharedCheck_1784_ == 0)
{
v___x_1779_ = v___x_1766_;
v_isShared_1780_ = v_isSharedCheck_1784_;
goto v_resetjp_1778_;
}
else
{
lean_inc(v_a_1777_);
lean_dec(v___x_1766_);
v___x_1779_ = lean_box(0);
v_isShared_1780_ = v_isSharedCheck_1784_;
goto v_resetjp_1778_;
}
v_resetjp_1778_:
{
lean_object* v___x_1782_; 
if (v_isShared_1780_ == 0)
{
lean_ctor_set_tag(v___x_1779_, 0);
v___x_1782_ = v___x_1779_;
goto v_reusejp_1781_;
}
else
{
lean_object* v_reuseFailAlloc_1783_; 
v_reuseFailAlloc_1783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1783_, 0, v_a_1777_);
v___x_1782_ = v_reuseFailAlloc_1783_;
goto v_reusejp_1781_;
}
v_reusejp_1781_:
{
return v___x_1782_;
}
}
}
else
{
lean_object* v_a_1785_; lean_object* v___x_1787_; uint8_t v_isShared_1788_; uint8_t v_isSharedCheck_1793_; 
v_a_1785_ = lean_ctor_get(v___x_1766_, 0);
v_isSharedCheck_1793_ = !lean_is_exclusive(v___x_1766_);
if (v_isSharedCheck_1793_ == 0)
{
v___x_1787_ = v___x_1766_;
v_isShared_1788_ = v_isSharedCheck_1793_;
goto v_resetjp_1786_;
}
else
{
lean_inc(v_a_1785_);
lean_dec(v___x_1766_);
v___x_1787_ = lean_box(0);
v_isShared_1788_ = v_isSharedCheck_1793_;
goto v_resetjp_1786_;
}
v_resetjp_1786_:
{
lean_object* v___x_1789_; lean_object* v___x_1791_; 
v___x_1789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1789_, 0, v_a_1764_);
lean_ctor_set(v___x_1789_, 1, v_a_1785_);
if (v_isShared_1788_ == 0)
{
lean_ctor_set(v___x_1787_, 0, v___x_1789_);
v___x_1791_ = v___x_1787_;
goto v_reusejp_1790_;
}
else
{
lean_object* v_reuseFailAlloc_1792_; 
v_reuseFailAlloc_1792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1792_, 0, v___x_1789_);
v___x_1791_ = v_reuseFailAlloc_1792_;
goto v_reusejp_1790_;
}
v_reusejp_1790_:
{
return v___x_1791_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonRpcOptions_toJson_spec__0(lean_object* v_k_1796_, lean_object* v_x_1797_){
_start:
{
if (lean_obj_tag(v_x_1797_) == 0)
{
lean_object* v___x_1798_; 
lean_dec_ref(v_k_1796_);
v___x_1798_ = lean_box(0);
return v___x_1798_;
}
else
{
lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; 
v___x_1799_ = lean_obj_once(&l_Lean_Lsp_instToJsonHighlightMatchesOptions_toJson___closed__0, &l_Lean_Lsp_instToJsonHighlightMatchesOptions_toJson___closed__0_once, _init_l_Lean_Lsp_instToJsonHighlightMatchesOptions_toJson___closed__0);
v___x_1800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1800_, 0, v_k_1796_);
lean_ctor_set(v___x_1800_, 1, v___x_1799_);
v___x_1801_ = lean_box(0);
v___x_1802_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1802_, 0, v___x_1800_);
lean_ctor_set(v___x_1802_, 1, v___x_1801_);
return v___x_1802_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonRpcOptions_toJson_spec__0___boxed(lean_object* v_k_1803_, lean_object* v_x_1804_){
_start:
{
lean_object* v_res_1805_; 
v_res_1805_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonRpcOptions_toJson_spec__0(v_k_1803_, v_x_1804_);
lean_dec(v_x_1804_);
return v_res_1805_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonRpcOptions_toJson_spec__1(lean_object* v_k_1806_, lean_object* v_x_1807_){
_start:
{
if (lean_obj_tag(v_x_1807_) == 0)
{
lean_object* v___x_1808_; 
lean_dec_ref(v_k_1806_);
v___x_1808_ = lean_box(0);
return v___x_1808_;
}
else
{
lean_object* v_val_1809_; uint8_t v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; 
v_val_1809_ = lean_ctor_get(v_x_1807_, 0);
v___x_1810_ = lean_unbox(v_val_1809_);
v___x_1811_ = l_Lean_Lsp_instToJsonRpcWireFormat_toJson(v___x_1810_);
v___x_1812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1812_, 0, v_k_1806_);
lean_ctor_set(v___x_1812_, 1, v___x_1811_);
v___x_1813_ = lean_box(0);
v___x_1814_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1814_, 0, v___x_1812_);
lean_ctor_set(v___x_1814_, 1, v___x_1813_);
return v___x_1814_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonRpcOptions_toJson_spec__1___boxed(lean_object* v_k_1815_, lean_object* v_x_1816_){
_start:
{
lean_object* v_res_1817_; 
v_res_1817_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonRpcOptions_toJson_spec__1(v_k_1815_, v_x_1816_);
lean_dec(v_x_1816_);
return v_res_1817_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRpcOptions_toJson(lean_object* v_x_1818_){
_start:
{
lean_object* v_highlightMatchesProvider_x3f_1819_; lean_object* v_rpcWireFormat_x3f_1820_; lean_object* v___x_1822_; uint8_t v_isShared_1823_; uint8_t v_isSharedCheck_1836_; 
v_highlightMatchesProvider_x3f_1819_ = lean_ctor_get(v_x_1818_, 0);
v_rpcWireFormat_x3f_1820_ = lean_ctor_get(v_x_1818_, 1);
v_isSharedCheck_1836_ = !lean_is_exclusive(v_x_1818_);
if (v_isSharedCheck_1836_ == 0)
{
v___x_1822_ = v_x_1818_;
v_isShared_1823_ = v_isSharedCheck_1836_;
goto v_resetjp_1821_;
}
else
{
lean_inc(v_rpcWireFormat_x3f_1820_);
lean_inc(v_highlightMatchesProvider_x3f_1819_);
lean_dec(v_x_1818_);
v___x_1822_ = lean_box(0);
v_isShared_1823_ = v_isSharedCheck_1836_;
goto v_resetjp_1821_;
}
v_resetjp_1821_:
{
lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1830_; 
v___x_1824_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__0));
v___x_1825_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonRpcOptions_toJson_spec__0(v___x_1824_, v_highlightMatchesProvider_x3f_1819_);
lean_dec(v_highlightMatchesProvider_x3f_1819_);
v___x_1826_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcOptions_fromJson___closed__10));
v___x_1827_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonRpcOptions_toJson_spec__1(v___x_1826_, v_rpcWireFormat_x3f_1820_);
lean_dec(v_rpcWireFormat_x3f_1820_);
v___x_1828_ = lean_box(0);
if (v_isShared_1823_ == 0)
{
lean_ctor_set_tag(v___x_1822_, 1);
lean_ctor_set(v___x_1822_, 1, v___x_1828_);
lean_ctor_set(v___x_1822_, 0, v___x_1827_);
v___x_1830_ = v___x_1822_;
goto v_reusejp_1829_;
}
else
{
lean_object* v_reuseFailAlloc_1835_; 
v_reuseFailAlloc_1835_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1835_, 0, v___x_1827_);
lean_ctor_set(v_reuseFailAlloc_1835_, 1, v___x_1828_);
v___x_1830_ = v_reuseFailAlloc_1835_;
goto v_reusejp_1829_;
}
v_reusejp_1829_:
{
lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; 
v___x_1831_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1831_, 0, v___x_1825_);
lean_ctor_set(v___x_1831_, 1, v___x_1830_);
v___x_1832_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0));
v___x_1833_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_1831_, v___x_1832_);
v___x_1834_ = l_Lean_Json_mkObj(v___x_1833_);
lean_dec(v___x_1833_);
return v___x_1834_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModule_fromJson_spec__0_spec__0(lean_object* v_x_1841_){
_start:
{
if (lean_obj_tag(v_x_1841_) == 0)
{
lean_object* v___x_1842_; 
v___x_1842_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModule_fromJson_spec__0_spec__0___closed__0));
return v___x_1842_;
}
else
{
lean_object* v___x_1843_; lean_object* v___x_1844_; 
v___x_1843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1843_, 0, v_x_1841_);
v___x_1844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1844_, 0, v___x_1843_);
return v___x_1844_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModule_fromJson_spec__0(lean_object* v_j_1845_, lean_object* v_k_1846_){
_start:
{
lean_object* v___x_1847_; lean_object* v___x_1848_; 
v___x_1847_ = l_Lean_Json_getObjValD(v_j_1845_, v_k_1846_);
v___x_1848_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModule_fromJson_spec__0_spec__0(v___x_1847_);
return v___x_1848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModule_fromJson_spec__0___boxed(lean_object* v_j_1849_, lean_object* v_k_1850_){
_start:
{
lean_object* v_res_1851_; 
v_res_1851_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModule_fromJson_spec__0(v_j_1849_, v_k_1850_);
lean_dec_ref(v_k_1850_);
return v_res_1851_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__3(void){
_start:
{
uint8_t v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; 
v___x_1858_ = 1;
v___x_1859_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__2));
v___x_1860_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1859_, v___x_1858_);
return v___x_1860_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__4(void){
_start:
{
lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; 
v___x_1861_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6));
v___x_1862_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__3);
v___x_1863_ = lean_string_append(v___x_1862_, v___x_1861_);
return v___x_1863_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__6(void){
_start:
{
uint8_t v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; 
v___x_1866_ = 1;
v___x_1867_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__5));
v___x_1868_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1867_, v___x_1866_);
return v___x_1868_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__7(void){
_start:
{
lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; 
v___x_1869_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__6);
v___x_1870_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__4);
v___x_1871_ = lean_string_append(v___x_1870_, v___x_1869_);
return v___x_1871_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__8(void){
_start:
{
lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; 
v___x_1872_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_1873_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__7);
v___x_1874_ = lean_string_append(v___x_1873_, v___x_1872_);
return v___x_1874_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__9(void){
_start:
{
lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; 
v___x_1875_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__6, &l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__6);
v___x_1876_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__4);
v___x_1877_ = lean_string_append(v___x_1876_, v___x_1875_);
return v___x_1877_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__10(void){
_start:
{
lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; 
v___x_1878_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_1879_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__9, &l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__9);
v___x_1880_ = lean_string_append(v___x_1879_, v___x_1878_);
return v___x_1880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanModule_fromJson(lean_object* v_json_1882_){
_start:
{
lean_object* v___x_1883_; lean_object* v___x_1884_; 
v___x_1883_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__0));
lean_inc(v_json_1882_);
v___x_1884_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson_spec__0(v_json_1882_, v___x_1883_);
if (lean_obj_tag(v___x_1884_) == 0)
{
lean_object* v_a_1885_; lean_object* v___x_1887_; uint8_t v_isShared_1888_; uint8_t v_isSharedCheck_1894_; 
lean_dec(v_json_1882_);
v_a_1885_ = lean_ctor_get(v___x_1884_, 0);
v_isSharedCheck_1894_ = !lean_is_exclusive(v___x_1884_);
if (v_isSharedCheck_1894_ == 0)
{
v___x_1887_ = v___x_1884_;
v_isShared_1888_ = v_isSharedCheck_1894_;
goto v_resetjp_1886_;
}
else
{
lean_inc(v_a_1885_);
lean_dec(v___x_1884_);
v___x_1887_ = lean_box(0);
v_isShared_1888_ = v_isSharedCheck_1894_;
goto v_resetjp_1886_;
}
v_resetjp_1886_:
{
lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1892_; 
v___x_1889_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__8);
v___x_1890_ = lean_string_append(v___x_1889_, v_a_1885_);
lean_dec(v_a_1885_);
if (v_isShared_1888_ == 0)
{
lean_ctor_set(v___x_1887_, 0, v___x_1890_);
v___x_1892_ = v___x_1887_;
goto v_reusejp_1891_;
}
else
{
lean_object* v_reuseFailAlloc_1893_; 
v_reuseFailAlloc_1893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1893_, 0, v___x_1890_);
v___x_1892_ = v_reuseFailAlloc_1893_;
goto v_reusejp_1891_;
}
v_reusejp_1891_:
{
return v___x_1892_;
}
}
}
else
{
if (lean_obj_tag(v___x_1884_) == 0)
{
lean_object* v_a_1895_; lean_object* v___x_1897_; uint8_t v_isShared_1898_; uint8_t v_isSharedCheck_1902_; 
lean_dec(v_json_1882_);
v_a_1895_ = lean_ctor_get(v___x_1884_, 0);
v_isSharedCheck_1902_ = !lean_is_exclusive(v___x_1884_);
if (v_isSharedCheck_1902_ == 0)
{
v___x_1897_ = v___x_1884_;
v_isShared_1898_ = v_isSharedCheck_1902_;
goto v_resetjp_1896_;
}
else
{
lean_inc(v_a_1895_);
lean_dec(v___x_1884_);
v___x_1897_ = lean_box(0);
v_isShared_1898_ = v_isSharedCheck_1902_;
goto v_resetjp_1896_;
}
v_resetjp_1896_:
{
lean_object* v___x_1900_; 
if (v_isShared_1898_ == 0)
{
lean_ctor_set_tag(v___x_1897_, 0);
v___x_1900_ = v___x_1897_;
goto v_reusejp_1899_;
}
else
{
lean_object* v_reuseFailAlloc_1901_; 
v_reuseFailAlloc_1901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1901_, 0, v_a_1895_);
v___x_1900_ = v_reuseFailAlloc_1901_;
goto v_reusejp_1899_;
}
v_reusejp_1899_:
{
return v___x_1900_;
}
}
}
else
{
lean_object* v_a_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; 
v_a_1903_ = lean_ctor_get(v___x_1884_, 0);
lean_inc(v_a_1903_);
lean_dec_ref_known(v___x_1884_, 1);
v___x_1904_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__0));
lean_inc(v_json_1882_);
v___x_1905_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson_spec__0(v_json_1882_, v___x_1904_);
if (lean_obj_tag(v___x_1905_) == 0)
{
lean_object* v_a_1906_; lean_object* v___x_1908_; uint8_t v_isShared_1909_; uint8_t v_isSharedCheck_1915_; 
lean_dec(v_a_1903_);
lean_dec(v_json_1882_);
v_a_1906_ = lean_ctor_get(v___x_1905_, 0);
v_isSharedCheck_1915_ = !lean_is_exclusive(v___x_1905_);
if (v_isSharedCheck_1915_ == 0)
{
v___x_1908_ = v___x_1905_;
v_isShared_1909_ = v_isSharedCheck_1915_;
goto v_resetjp_1907_;
}
else
{
lean_inc(v_a_1906_);
lean_dec(v___x_1905_);
v___x_1908_ = lean_box(0);
v_isShared_1909_ = v_isSharedCheck_1915_;
goto v_resetjp_1907_;
}
v_resetjp_1907_:
{
lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1913_; 
v___x_1910_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__10, &l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__10);
v___x_1911_ = lean_string_append(v___x_1910_, v_a_1906_);
lean_dec(v_a_1906_);
if (v_isShared_1909_ == 0)
{
lean_ctor_set(v___x_1908_, 0, v___x_1911_);
v___x_1913_ = v___x_1908_;
goto v_reusejp_1912_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v___x_1911_);
v___x_1913_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1912_;
}
v_reusejp_1912_:
{
return v___x_1913_;
}
}
}
else
{
if (lean_obj_tag(v___x_1905_) == 0)
{
lean_object* v_a_1916_; lean_object* v___x_1918_; uint8_t v_isShared_1919_; uint8_t v_isSharedCheck_1923_; 
lean_dec(v_a_1903_);
lean_dec(v_json_1882_);
v_a_1916_ = lean_ctor_get(v___x_1905_, 0);
v_isSharedCheck_1923_ = !lean_is_exclusive(v___x_1905_);
if (v_isSharedCheck_1923_ == 0)
{
v___x_1918_ = v___x_1905_;
v_isShared_1919_ = v_isSharedCheck_1923_;
goto v_resetjp_1917_;
}
else
{
lean_inc(v_a_1916_);
lean_dec(v___x_1905_);
v___x_1918_ = lean_box(0);
v_isShared_1919_ = v_isSharedCheck_1923_;
goto v_resetjp_1917_;
}
v_resetjp_1917_:
{
lean_object* v___x_1921_; 
if (v_isShared_1919_ == 0)
{
lean_ctor_set_tag(v___x_1918_, 0);
v___x_1921_ = v___x_1918_;
goto v_reusejp_1920_;
}
else
{
lean_object* v_reuseFailAlloc_1922_; 
v_reuseFailAlloc_1922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1922_, 0, v_a_1916_);
v___x_1921_ = v_reuseFailAlloc_1922_;
goto v_reusejp_1920_;
}
v_reusejp_1920_:
{
return v___x_1921_;
}
}
}
else
{
lean_object* v_a_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v_a_1927_; lean_object* v___x_1929_; uint8_t v_isShared_1930_; uint8_t v_isSharedCheck_1935_; 
v_a_1924_ = lean_ctor_get(v___x_1905_, 0);
lean_inc(v_a_1924_);
lean_dec_ref_known(v___x_1905_, 1);
v___x_1925_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__11));
v___x_1926_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanModule_fromJson_spec__0(v_json_1882_, v___x_1925_);
v_a_1927_ = lean_ctor_get(v___x_1926_, 0);
v_isSharedCheck_1935_ = !lean_is_exclusive(v___x_1926_);
if (v_isSharedCheck_1935_ == 0)
{
v___x_1929_ = v___x_1926_;
v_isShared_1930_ = v_isSharedCheck_1935_;
goto v_resetjp_1928_;
}
else
{
lean_inc(v_a_1927_);
lean_dec(v___x_1926_);
v___x_1929_ = lean_box(0);
v_isShared_1930_ = v_isSharedCheck_1935_;
goto v_resetjp_1928_;
}
v_resetjp_1928_:
{
lean_object* v___x_1931_; lean_object* v___x_1933_; 
v___x_1931_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1931_, 0, v_a_1903_);
lean_ctor_set(v___x_1931_, 1, v_a_1924_);
lean_ctor_set(v___x_1931_, 2, v_a_1927_);
if (v_isShared_1930_ == 0)
{
lean_ctor_set(v___x_1929_, 0, v___x_1931_);
v___x_1933_ = v___x_1929_;
goto v_reusejp_1932_;
}
else
{
lean_object* v_reuseFailAlloc_1934_; 
v_reuseFailAlloc_1934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1934_, 0, v___x_1931_);
v___x_1933_ = v_reuseFailAlloc_1934_;
goto v_reusejp_1932_;
}
v_reusejp_1932_:
{
return v___x_1933_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanModule_toJson_spec__0(lean_object* v_k_1938_, lean_object* v_x_1939_){
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
lean_object* v_val_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; 
v_val_1941_ = lean_ctor_get(v_x_1939_, 0);
lean_inc(v_val_1941_);
v___x_1942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1942_, 0, v_k_1938_);
lean_ctor_set(v___x_1942_, 1, v_val_1941_);
v___x_1943_ = lean_box(0);
v___x_1944_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1944_, 0, v___x_1942_);
lean_ctor_set(v___x_1944_, 1, v___x_1943_);
return v___x_1944_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanModule_toJson_spec__0___boxed(lean_object* v_k_1945_, lean_object* v_x_1946_){
_start:
{
lean_object* v_res_1947_; 
v_res_1947_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanModule_toJson_spec__0(v_k_1945_, v_x_1946_);
lean_dec(v_x_1946_);
return v_res_1947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanModule_toJson(lean_object* v_x_1948_){
_start:
{
lean_object* v_name_1949_; lean_object* v_uri_1950_; lean_object* v_data_x3f_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; 
v_name_1949_ = lean_ctor_get(v_x_1948_, 0);
v_uri_1950_ = lean_ctor_get(v_x_1948_, 1);
v_data_x3f_1951_ = lean_ctor_get(v_x_1948_, 2);
v___x_1952_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__0));
lean_inc_ref(v_name_1949_);
v___x_1953_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1953_, 0, v_name_1949_);
v___x_1954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1954_, 0, v___x_1952_);
lean_ctor_set(v___x_1954_, 1, v___x_1953_);
v___x_1955_ = lean_box(0);
v___x_1956_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1956_, 0, v___x_1954_);
lean_ctor_set(v___x_1956_, 1, v___x_1955_);
v___x_1957_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__0));
lean_inc_ref(v_uri_1950_);
v___x_1958_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1958_, 0, v_uri_1950_);
v___x_1959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1959_, 0, v___x_1957_);
lean_ctor_set(v___x_1959_, 1, v___x_1958_);
v___x_1960_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1960_, 0, v___x_1959_);
lean_ctor_set(v___x_1960_, 1, v___x_1955_);
v___x_1961_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModule_fromJson___closed__11));
v___x_1962_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanModule_toJson_spec__0(v___x_1961_, v_data_x3f_1951_);
v___x_1963_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1963_, 0, v___x_1962_);
lean_ctor_set(v___x_1963_, 1, v___x_1955_);
v___x_1964_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1964_, 0, v___x_1960_);
lean_ctor_set(v___x_1964_, 1, v___x_1963_);
v___x_1965_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1965_, 0, v___x_1956_);
lean_ctor_set(v___x_1965_, 1, v___x_1964_);
v___x_1966_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0));
v___x_1967_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_1965_, v___x_1966_);
v___x_1968_ = l_Lean_Json_mkObj(v___x_1967_);
lean_dec(v___x_1967_);
return v___x_1968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanModule_toJson___boxed(lean_object* v_x_1969_){
_start:
{
lean_object* v_res_1970_; 
v_res_1970_ = l_Lean_Lsp_instToJsonLeanModule_toJson(v_x_1969_);
lean_dec_ref(v_x_1969_);
return v_res_1970_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__2(void){
_start:
{
uint8_t v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; 
v___x_1978_ = 1;
v___x_1979_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__1));
v___x_1980_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1979_, v___x_1978_);
return v___x_1980_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__3(void){
_start:
{
lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; 
v___x_1981_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6));
v___x_1982_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__2, &l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__2);
v___x_1983_ = lean_string_append(v___x_1982_, v___x_1981_);
return v___x_1983_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; 
v___x_1984_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9, &l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9);
v___x_1985_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__3);
v___x_1986_ = lean_string_append(v___x_1985_, v___x_1984_);
return v___x_1986_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__5(void){
_start:
{
lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; 
v___x_1987_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_1988_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__4);
v___x_1989_ = lean_string_append(v___x_1988_, v___x_1987_);
return v___x_1989_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson(lean_object* v_json_1990_){
_start:
{
lean_object* v___x_1991_; lean_object* v___x_1992_; 
v___x_1991_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__0));
v___x_1992_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoalParams_fromJson_spec__0(v_json_1990_, v___x_1991_);
if (lean_obj_tag(v___x_1992_) == 0)
{
lean_object* v_a_1993_; lean_object* v___x_1995_; uint8_t v_isShared_1996_; uint8_t v_isSharedCheck_2002_; 
v_a_1993_ = lean_ctor_get(v___x_1992_, 0);
v_isSharedCheck_2002_ = !lean_is_exclusive(v___x_1992_);
if (v_isSharedCheck_2002_ == 0)
{
v___x_1995_ = v___x_1992_;
v_isShared_1996_ = v_isSharedCheck_2002_;
goto v_resetjp_1994_;
}
else
{
lean_inc(v_a_1993_);
lean_dec(v___x_1992_);
v___x_1995_ = lean_box(0);
v_isShared_1996_ = v_isSharedCheck_2002_;
goto v_resetjp_1994_;
}
v_resetjp_1994_:
{
lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_2000_; 
v___x_1997_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__5, &l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonLeanPrepareModuleHierarchyParams_fromJson___closed__5);
v___x_1998_ = lean_string_append(v___x_1997_, v_a_1993_);
lean_dec(v_a_1993_);
if (v_isShared_1996_ == 0)
{
lean_ctor_set(v___x_1995_, 0, v___x_1998_);
v___x_2000_ = v___x_1995_;
goto v_reusejp_1999_;
}
else
{
lean_object* v_reuseFailAlloc_2001_; 
v_reuseFailAlloc_2001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2001_, 0, v___x_1998_);
v___x_2000_ = v_reuseFailAlloc_2001_;
goto v_reusejp_1999_;
}
v_reusejp_1999_:
{
return v___x_2000_;
}
}
}
else
{
if (lean_obj_tag(v___x_1992_) == 0)
{
lean_object* v_a_2003_; lean_object* v___x_2005_; uint8_t v_isShared_2006_; uint8_t v_isSharedCheck_2010_; 
v_a_2003_ = lean_ctor_get(v___x_1992_, 0);
v_isSharedCheck_2010_ = !lean_is_exclusive(v___x_1992_);
if (v_isSharedCheck_2010_ == 0)
{
v___x_2005_ = v___x_1992_;
v_isShared_2006_ = v_isSharedCheck_2010_;
goto v_resetjp_2004_;
}
else
{
lean_inc(v_a_2003_);
lean_dec(v___x_1992_);
v___x_2005_ = lean_box(0);
v_isShared_2006_ = v_isSharedCheck_2010_;
goto v_resetjp_2004_;
}
v_resetjp_2004_:
{
lean_object* v___x_2008_; 
if (v_isShared_2006_ == 0)
{
lean_ctor_set_tag(v___x_2005_, 0);
v___x_2008_ = v___x_2005_;
goto v_reusejp_2007_;
}
else
{
lean_object* v_reuseFailAlloc_2009_; 
v_reuseFailAlloc_2009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2009_, 0, v_a_2003_);
v___x_2008_ = v_reuseFailAlloc_2009_;
goto v_reusejp_2007_;
}
v_reusejp_2007_:
{
return v___x_2008_;
}
}
}
else
{
lean_object* v_a_2011_; lean_object* v___x_2013_; uint8_t v_isShared_2014_; uint8_t v_isSharedCheck_2018_; 
v_a_2011_ = lean_ctor_get(v___x_1992_, 0);
v_isSharedCheck_2018_ = !lean_is_exclusive(v___x_1992_);
if (v_isSharedCheck_2018_ == 0)
{
v___x_2013_ = v___x_1992_;
v_isShared_2014_ = v_isSharedCheck_2018_;
goto v_resetjp_2012_;
}
else
{
lean_inc(v_a_2011_);
lean_dec(v___x_1992_);
v___x_2013_ = lean_box(0);
v_isShared_2014_ = v_isSharedCheck_2018_;
goto v_resetjp_2012_;
}
v_resetjp_2012_:
{
lean_object* v___x_2016_; 
if (v_isShared_2014_ == 0)
{
v___x_2016_ = v___x_2013_;
goto v_reusejp_2015_;
}
else
{
lean_object* v_reuseFailAlloc_2017_; 
v_reuseFailAlloc_2017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2017_, 0, v_a_2011_);
v___x_2016_ = v_reuseFailAlloc_2017_;
goto v_reusejp_2015_;
}
v_reusejp_2015_:
{
return v___x_2016_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanPrepareModuleHierarchyParams_toJson(lean_object* v_x_2021_){
_start:
{
lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; 
v___x_2022_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__0));
v___x_2023_ = l_Lean_Lsp_instToJsonTextDocumentIdentifier_toJson(v_x_2021_);
v___x_2024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2024_, 0, v___x_2022_);
lean_ctor_set(v___x_2024_, 1, v___x_2023_);
v___x_2025_ = lean_box(0);
v___x_2026_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2026_, 0, v___x_2024_);
lean_ctor_set(v___x_2026_, 1, v___x_2025_);
v___x_2027_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2027_, 0, v___x_2026_);
lean_ctor_set(v___x_2027_, 1, v___x_2025_);
v___x_2028_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0));
v___x_2029_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_2027_, v___x_2028_);
v___x_2030_ = l_Lean_Json_mkObj(v___x_2029_);
lean_dec(v___x_2029_);
return v___x_2030_;
}
}
lean_object* l_Lean_Lsp_LeanImportMetaKind_ctorIdx___impl(uint8_t v_x_2033_){
_start:
{
lean_object* v___x_2034_; lean_object* v___x_2035_; 
v___x_2034_ = lean_box(v_x_2033_);
v___x_2035_ = lean_obj_tag_nat(v___x_2034_);
lean_dec(v___x_2034_);
return v___x_2035_;
}
}
LEAN_EXPORT void l_Lean_Lsp_LeanImportMetaKind_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_2033_ = stack[0].m_num;
lean_object* v_res_2036_;
v_res_2036_ = l_Lean_Lsp_LeanImportMetaKind_ctorIdx___impl(v_x_2033_);
stack->m_obj
 = v_res_2036_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanImportMetaKind_ctorIdx___impl___boxed(lean_object* v_x_2037_){
_start:
{
uint8_t v_x_4__boxed_2038_; lean_object* v_res_2039_; 
v_x_4__boxed_2038_ = lean_unbox(v_x_2037_);
v_res_2039_ = l_Lean_Lsp_LeanImportMetaKind_ctorIdx___impl(v_x_4__boxed_2038_);
return v_res_2039_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanImportMetaKind_ctorElim___redArg(lean_object* v_k_2040_){
_start:
{
lean_inc(v_k_2040_);
return v_k_2040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanImportMetaKind_ctorElim___redArg___boxed(lean_object* v_k_2041_){
_start:
{
lean_object* v_res_2042_; 
v_res_2042_ = l_Lean_Lsp_LeanImportMetaKind_ctorElim___redArg(v_k_2041_);
lean_dec(v_k_2041_);
return v_res_2042_;
}
}
lean_object* l_Lean_Lsp_LeanImportMetaKind_ctorElim(lean_object* v_motive_2043_, lean_object* v_ctorIdx_2044_, uint8_t v_t_2045_, lean_object* v_h_2046_, lean_object* v_k_2047_){
_start:
{
lean_inc(v_k_2047_);
return v_k_2047_;
}
}
LEAN_EXPORT void l_Lean_Lsp_LeanImportMetaKind_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_2044_ = stack[1].m_obj;
uint8_t v_t_2045_ = stack[2].m_num;
lean_object* v_k_2047_ = stack[4].m_obj;
lean_object* v_res_2048_;
v_res_2048_ = l_Lean_Lsp_LeanImportMetaKind_ctorElim(lean_box(0), v_ctorIdx_2044_, v_t_2045_, lean_box(0), v_k_2047_);
stack->m_obj
 = v_res_2048_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanImportMetaKind_ctorElim___boxed(lean_object* v_motive_2049_, lean_object* v_ctorIdx_2050_, lean_object* v_t_2051_, lean_object* v_h_2052_, lean_object* v_k_2053_){
_start:
{
uint8_t v_t_boxed_2054_; lean_object* v_res_2055_; 
v_t_boxed_2054_ = lean_unbox(v_t_2051_);
v_res_2055_ = l_Lean_Lsp_LeanImportMetaKind_ctorElim(v_motive_2049_, v_ctorIdx_2050_, v_t_boxed_2054_, v_h_2052_, v_k_2053_);
lean_dec(v_k_2053_);
lean_dec(v_ctorIdx_2050_);
return v_res_2055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanImportMetaKind_nonMeta_elim___redArg(lean_object* v_nonMeta_2056_){
_start:
{
lean_inc(v_nonMeta_2056_);
return v_nonMeta_2056_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanImportMetaKind_nonMeta_elim___redArg___boxed(lean_object* v_nonMeta_2057_){
_start:
{
lean_object* v_res_2058_; 
v_res_2058_ = l_Lean_Lsp_LeanImportMetaKind_nonMeta_elim___redArg(v_nonMeta_2057_);
lean_dec(v_nonMeta_2057_);
return v_res_2058_;
}
}
lean_object* l_Lean_Lsp_LeanImportMetaKind_nonMeta_elim(lean_object* v_motive_2059_, uint8_t v_t_2060_, lean_object* v_h_2061_, lean_object* v_nonMeta_2062_){
_start:
{
lean_inc(v_nonMeta_2062_);
return v_nonMeta_2062_;
}
}
LEAN_EXPORT void l_Lean_Lsp_LeanImportMetaKind_nonMeta_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_2060_ = stack[1].m_num;
lean_object* v_nonMeta_2062_ = stack[3].m_obj;
lean_object* v_res_2063_;
v_res_2063_ = l_Lean_Lsp_LeanImportMetaKind_nonMeta_elim(lean_box(0), v_t_2060_, lean_box(0), v_nonMeta_2062_);
stack->m_obj
 = v_res_2063_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanImportMetaKind_nonMeta_elim___boxed(lean_object* v_motive_2064_, lean_object* v_t_2065_, lean_object* v_h_2066_, lean_object* v_nonMeta_2067_){
_start:
{
uint8_t v_t_boxed_2068_; lean_object* v_res_2069_; 
v_t_boxed_2068_ = lean_unbox(v_t_2065_);
v_res_2069_ = l_Lean_Lsp_LeanImportMetaKind_nonMeta_elim(v_motive_2064_, v_t_boxed_2068_, v_h_2066_, v_nonMeta_2067_);
lean_dec(v_nonMeta_2067_);
return v_res_2069_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanImportMetaKind_meta_elim___redArg(lean_object* v_meta_2070_){
_start:
{
lean_inc(v_meta_2070_);
return v_meta_2070_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanImportMetaKind_meta_elim___redArg___boxed(lean_object* v_meta_2071_){
_start:
{
lean_object* v_res_2072_; 
v_res_2072_ = l_Lean_Lsp_LeanImportMetaKind_meta_elim___redArg(v_meta_2071_);
lean_dec(v_meta_2071_);
return v_res_2072_;
}
}
lean_object* l_Lean_Lsp_LeanImportMetaKind_meta_elim(lean_object* v_motive_2073_, uint8_t v_t_2074_, lean_object* v_h_2075_, lean_object* v_meta_2076_){
_start:
{
lean_inc(v_meta_2076_);
return v_meta_2076_;
}
}
LEAN_EXPORT void l_Lean_Lsp_LeanImportMetaKind_meta_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_2074_ = stack[1].m_num;
lean_object* v_meta_2076_ = stack[3].m_obj;
lean_object* v_res_2077_;
v_res_2077_ = l_Lean_Lsp_LeanImportMetaKind_meta_elim(lean_box(0), v_t_2074_, lean_box(0), v_meta_2076_);
stack->m_obj
 = v_res_2077_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanImportMetaKind_meta_elim___boxed(lean_object* v_motive_2078_, lean_object* v_t_2079_, lean_object* v_h_2080_, lean_object* v_meta_2081_){
_start:
{
uint8_t v_t_boxed_2082_; lean_object* v_res_2083_; 
v_t_boxed_2082_ = lean_unbox(v_t_2079_);
v_res_2083_ = l_Lean_Lsp_LeanImportMetaKind_meta_elim(v_motive_2078_, v_t_boxed_2082_, v_h_2080_, v_meta_2081_);
lean_dec(v_meta_2081_);
return v_res_2083_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanImportMetaKind_full_elim___redArg(lean_object* v_full_2084_){
_start:
{
lean_inc(v_full_2084_);
return v_full_2084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanImportMetaKind_full_elim___redArg___boxed(lean_object* v_full_2085_){
_start:
{
lean_object* v_res_2086_; 
v_res_2086_ = l_Lean_Lsp_LeanImportMetaKind_full_elim___redArg(v_full_2085_);
lean_dec(v_full_2085_);
return v_res_2086_;
}
}
lean_object* l_Lean_Lsp_LeanImportMetaKind_full_elim(lean_object* v_motive_2087_, uint8_t v_t_2088_, lean_object* v_h_2089_, lean_object* v_full_2090_){
_start:
{
lean_inc(v_full_2090_);
return v_full_2090_;
}
}
LEAN_EXPORT void l_Lean_Lsp_LeanImportMetaKind_full_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_2088_ = stack[1].m_num;
lean_object* v_full_2090_ = stack[3].m_obj;
lean_object* v_res_2091_;
v_res_2091_ = l_Lean_Lsp_LeanImportMetaKind_full_elim(lean_box(0), v_t_2088_, lean_box(0), v_full_2090_);
stack->m_obj
 = v_res_2091_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanImportMetaKind_full_elim___boxed(lean_object* v_motive_2092_, lean_object* v_t_2093_, lean_object* v_h_2094_, lean_object* v_full_2095_){
_start:
{
uint8_t v_t_boxed_2096_; lean_object* v_res_2097_; 
v_t_boxed_2096_ = lean_unbox(v_t_2093_);
v_res_2097_ = l_Lean_Lsp_LeanImportMetaKind_full_elim(v_motive_2092_, v_t_boxed_2096_, v_h_2094_, v_full_2095_);
lean_dec(v_full_2095_);
return v_res_2097_;
}
}
static uint8_t _init_l_Lean_Lsp_instInhabitedLeanImportMetaKind_default(void){
_start:
{
uint8_t v___x_2098_; 
v___x_2098_ = 0;
return v___x_2098_;
}
}
static uint8_t _init_l_Lean_Lsp_instInhabitedLeanImportMetaKind(void){
_start:
{
uint8_t v___x_2099_; 
v___x_2099_ = 0;
return v___x_2099_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson(lean_object* v_json_2116_){
_start:
{
lean_object* v___x_2117_; 
v___x_2117_ = l_Lean_Json_getTag_x3f(v_json_2116_);
if (lean_obj_tag(v___x_2117_) == 0)
{
lean_object* v___x_2118_; 
v___x_2118_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson___closed__0));
return v___x_2118_;
}
else
{
lean_object* v_val_2119_; lean_object* v___x_2120_; uint8_t v___x_2121_; 
v_val_2119_ = lean_ctor_get(v___x_2117_, 0);
lean_inc(v_val_2119_);
lean_dec_ref_known(v___x_2117_, 1);
v___x_2120_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson___closed__1));
v___x_2121_ = lean_string_dec_eq(v_val_2119_, v___x_2120_);
if (v___x_2121_ == 0)
{
lean_object* v___x_2122_; uint8_t v___x_2123_; 
v___x_2122_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson___closed__2));
v___x_2123_ = lean_string_dec_eq(v_val_2119_, v___x_2122_);
if (v___x_2123_ == 0)
{
lean_object* v___x_2124_; uint8_t v___x_2125_; 
v___x_2124_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson___closed__3));
v___x_2125_ = lean_string_dec_eq(v_val_2119_, v___x_2124_);
lean_dec(v_val_2119_);
if (v___x_2125_ == 0)
{
lean_object* v___x_2126_; 
v___x_2126_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson___closed__4));
return v___x_2126_;
}
else
{
lean_object* v___x_2127_; 
v___x_2127_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson___closed__5));
return v___x_2127_;
}
}
else
{
lean_object* v___x_2128_; 
lean_dec(v_val_2119_);
v___x_2128_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson___closed__6));
return v___x_2128_;
}
}
else
{
lean_object* v___x_2129_; 
lean_dec(v_val_2119_);
v___x_2129_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson___closed__7));
return v___x_2129_;
}
}
}
}
lean_object* l_Lean_Lsp_instToJsonLeanImportMetaKind_toJson(uint8_t v_x_2138_){
_start:
{
switch(v_x_2138_)
{
case 0:
{
lean_object* v___x_2139_; 
v___x_2139_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanImportMetaKind_toJson___closed__0));
return v___x_2139_;
}
case 1:
{
lean_object* v___x_2140_; 
v___x_2140_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanImportMetaKind_toJson___closed__1));
return v___x_2140_;
}
default: 
{
lean_object* v___x_2141_; 
v___x_2141_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanImportMetaKind_toJson___closed__2));
return v___x_2141_;
}
}
}
}
LEAN_EXPORT void l_Lean_Lsp_instToJsonLeanImportMetaKind_toJson_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_2138_ = stack[0].m_num;
lean_object* v_res_2142_;
v_res_2142_ = l_Lean_Lsp_instToJsonLeanImportMetaKind_toJson(v_x_2138_);
stack->m_obj
 = v_res_2142_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanImportMetaKind_toJson___boxed(lean_object* v_x_2143_){
_start:
{
uint8_t v_x_64__boxed_2144_; lean_object* v_res_2145_; 
v_x_64__boxed_2144_ = lean_unbox(v_x_2143_);
v_res_2145_ = l_Lean_Lsp_instToJsonLeanImportMetaKind_toJson(v_x_64__boxed_2144_);
return v_res_2145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportKind_fromJson_spec__0(lean_object* v_j_2148_, lean_object* v_k_2149_){
_start:
{
lean_object* v___x_2150_; lean_object* v___x_2151_; 
v___x_2150_ = l_Lean_Json_getObjValD(v_j_2148_, v_k_2149_);
v___x_2151_ = l_Lean_Json_getBool_x3f(v___x_2150_);
lean_dec(v___x_2150_);
return v___x_2151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportKind_fromJson_spec__0___boxed(lean_object* v_j_2152_, lean_object* v_k_2153_){
_start:
{
lean_object* v_res_2154_; 
v_res_2154_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportKind_fromJson_spec__0(v_j_2152_, v_k_2153_);
lean_dec_ref(v_k_2153_);
return v_res_2154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportKind_fromJson_spec__1(lean_object* v_j_2155_, lean_object* v_k_2156_){
_start:
{
lean_object* v___x_2157_; lean_object* v___x_2158_; 
v___x_2157_ = l_Lean_Json_getObjValD(v_j_2155_, v_k_2156_);
v___x_2158_ = l_Lean_Lsp_instFromJsonLeanImportMetaKind_fromJson(v___x_2157_);
return v___x_2158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportKind_fromJson_spec__1___boxed(lean_object* v_j_2159_, lean_object* v_k_2160_){
_start:
{
lean_object* v_res_2161_; 
v_res_2161_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportKind_fromJson_spec__1(v_j_2159_, v_k_2160_);
lean_dec_ref(v_k_2160_);
return v_res_2161_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__3(void){
_start:
{
uint8_t v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; 
v___x_2168_ = 1;
v___x_2169_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__2));
v___x_2170_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2169_, v___x_2168_);
return v___x_2170_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__4(void){
_start:
{
lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; 
v___x_2171_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6));
v___x_2172_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__3);
v___x_2173_ = lean_string_append(v___x_2172_, v___x_2171_);
return v___x_2173_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__6(void){
_start:
{
uint8_t v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; 
v___x_2176_ = 1;
v___x_2177_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__5));
v___x_2178_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2177_, v___x_2176_);
return v___x_2178_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__7(void){
_start:
{
lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; 
v___x_2179_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__6);
v___x_2180_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__4);
v___x_2181_ = lean_string_append(v___x_2180_, v___x_2179_);
return v___x_2181_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__8(void){
_start:
{
lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; 
v___x_2182_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_2183_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__7);
v___x_2184_ = lean_string_append(v___x_2183_, v___x_2182_);
return v___x_2184_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__11(void){
_start:
{
uint8_t v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; 
v___x_2188_ = 1;
v___x_2189_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__10));
v___x_2190_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2189_, v___x_2188_);
return v___x_2190_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__12(void){
_start:
{
lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; 
v___x_2191_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__11, &l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__11);
v___x_2192_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__4);
v___x_2193_ = lean_string_append(v___x_2192_, v___x_2191_);
return v___x_2193_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__13(void){
_start:
{
lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; 
v___x_2194_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_2195_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__12, &l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__12);
v___x_2196_ = lean_string_append(v___x_2195_, v___x_2194_);
return v___x_2196_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__16(void){
_start:
{
uint8_t v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; 
v___x_2200_ = 1;
v___x_2201_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__15));
v___x_2202_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2201_, v___x_2200_);
return v___x_2202_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__17(void){
_start:
{
lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; 
v___x_2203_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__16, &l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__16_once, _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__16);
v___x_2204_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__4);
v___x_2205_ = lean_string_append(v___x_2204_, v___x_2203_);
return v___x_2205_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__18(void){
_start:
{
lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; 
v___x_2206_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_2207_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__17, &l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__17_once, _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__17);
v___x_2208_ = lean_string_append(v___x_2207_, v___x_2206_);
return v___x_2208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanImportKind_fromJson(lean_object* v_json_2209_){
_start:
{
lean_object* v___x_2210_; lean_object* v___x_2211_; 
v___x_2210_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__0));
lean_inc(v_json_2209_);
v___x_2211_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportKind_fromJson_spec__0(v_json_2209_, v___x_2210_);
if (lean_obj_tag(v___x_2211_) == 0)
{
lean_object* v_a_2212_; lean_object* v___x_2214_; uint8_t v_isShared_2215_; uint8_t v_isSharedCheck_2221_; 
lean_dec(v_json_2209_);
v_a_2212_ = lean_ctor_get(v___x_2211_, 0);
v_isSharedCheck_2221_ = !lean_is_exclusive(v___x_2211_);
if (v_isSharedCheck_2221_ == 0)
{
v___x_2214_ = v___x_2211_;
v_isShared_2215_ = v_isSharedCheck_2221_;
goto v_resetjp_2213_;
}
else
{
lean_inc(v_a_2212_);
lean_dec(v___x_2211_);
v___x_2214_ = lean_box(0);
v_isShared_2215_ = v_isSharedCheck_2221_;
goto v_resetjp_2213_;
}
v_resetjp_2213_:
{
lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2219_; 
v___x_2216_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__8);
v___x_2217_ = lean_string_append(v___x_2216_, v_a_2212_);
lean_dec(v_a_2212_);
if (v_isShared_2215_ == 0)
{
lean_ctor_set(v___x_2214_, 0, v___x_2217_);
v___x_2219_ = v___x_2214_;
goto v_reusejp_2218_;
}
else
{
lean_object* v_reuseFailAlloc_2220_; 
v_reuseFailAlloc_2220_ = lean_alloc_ctor(0, 1, 0);
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
else
{
if (lean_obj_tag(v___x_2211_) == 0)
{
lean_object* v_a_2222_; lean_object* v___x_2224_; uint8_t v_isShared_2225_; uint8_t v_isSharedCheck_2229_; 
lean_dec(v_json_2209_);
v_a_2222_ = lean_ctor_get(v___x_2211_, 0);
v_isSharedCheck_2229_ = !lean_is_exclusive(v___x_2211_);
if (v_isSharedCheck_2229_ == 0)
{
v___x_2224_ = v___x_2211_;
v_isShared_2225_ = v_isSharedCheck_2229_;
goto v_resetjp_2223_;
}
else
{
lean_inc(v_a_2222_);
lean_dec(v___x_2211_);
v___x_2224_ = lean_box(0);
v_isShared_2225_ = v_isSharedCheck_2229_;
goto v_resetjp_2223_;
}
v_resetjp_2223_:
{
lean_object* v___x_2227_; 
if (v_isShared_2225_ == 0)
{
lean_ctor_set_tag(v___x_2224_, 0);
v___x_2227_ = v___x_2224_;
goto v_reusejp_2226_;
}
else
{
lean_object* v_reuseFailAlloc_2228_; 
v_reuseFailAlloc_2228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2228_, 0, v_a_2222_);
v___x_2227_ = v_reuseFailAlloc_2228_;
goto v_reusejp_2226_;
}
v_reusejp_2226_:
{
return v___x_2227_;
}
}
}
else
{
lean_object* v_a_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; 
v_a_2230_ = lean_ctor_get(v___x_2211_, 0);
lean_inc(v_a_2230_);
lean_dec_ref_known(v___x_2211_, 1);
v___x_2231_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__9));
lean_inc(v_json_2209_);
v___x_2232_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportKind_fromJson_spec__0(v_json_2209_, v___x_2231_);
if (lean_obj_tag(v___x_2232_) == 0)
{
lean_object* v_a_2233_; lean_object* v___x_2235_; uint8_t v_isShared_2236_; uint8_t v_isSharedCheck_2242_; 
lean_dec(v_a_2230_);
lean_dec(v_json_2209_);
v_a_2233_ = lean_ctor_get(v___x_2232_, 0);
v_isSharedCheck_2242_ = !lean_is_exclusive(v___x_2232_);
if (v_isSharedCheck_2242_ == 0)
{
v___x_2235_ = v___x_2232_;
v_isShared_2236_ = v_isSharedCheck_2242_;
goto v_resetjp_2234_;
}
else
{
lean_inc(v_a_2233_);
lean_dec(v___x_2232_);
v___x_2235_ = lean_box(0);
v_isShared_2236_ = v_isSharedCheck_2242_;
goto v_resetjp_2234_;
}
v_resetjp_2234_:
{
lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2240_; 
v___x_2237_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__13, &l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__13);
v___x_2238_ = lean_string_append(v___x_2237_, v_a_2233_);
lean_dec(v_a_2233_);
if (v_isShared_2236_ == 0)
{
lean_ctor_set(v___x_2235_, 0, v___x_2238_);
v___x_2240_ = v___x_2235_;
goto v_reusejp_2239_;
}
else
{
lean_object* v_reuseFailAlloc_2241_; 
v_reuseFailAlloc_2241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2241_, 0, v___x_2238_);
v___x_2240_ = v_reuseFailAlloc_2241_;
goto v_reusejp_2239_;
}
v_reusejp_2239_:
{
return v___x_2240_;
}
}
}
else
{
if (lean_obj_tag(v___x_2232_) == 0)
{
lean_object* v_a_2243_; lean_object* v___x_2245_; uint8_t v_isShared_2246_; uint8_t v_isSharedCheck_2250_; 
lean_dec(v_a_2230_);
lean_dec(v_json_2209_);
v_a_2243_ = lean_ctor_get(v___x_2232_, 0);
v_isSharedCheck_2250_ = !lean_is_exclusive(v___x_2232_);
if (v_isSharedCheck_2250_ == 0)
{
v___x_2245_ = v___x_2232_;
v_isShared_2246_ = v_isSharedCheck_2250_;
goto v_resetjp_2244_;
}
else
{
lean_inc(v_a_2243_);
lean_dec(v___x_2232_);
v___x_2245_ = lean_box(0);
v_isShared_2246_ = v_isSharedCheck_2250_;
goto v_resetjp_2244_;
}
v_resetjp_2244_:
{
lean_object* v___x_2248_; 
if (v_isShared_2246_ == 0)
{
lean_ctor_set_tag(v___x_2245_, 0);
v___x_2248_ = v___x_2245_;
goto v_reusejp_2247_;
}
else
{
lean_object* v_reuseFailAlloc_2249_; 
v_reuseFailAlloc_2249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2249_, 0, v_a_2243_);
v___x_2248_ = v_reuseFailAlloc_2249_;
goto v_reusejp_2247_;
}
v_reusejp_2247_:
{
return v___x_2248_;
}
}
}
else
{
lean_object* v_a_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; 
v_a_2251_ = lean_ctor_get(v___x_2232_, 0);
lean_inc(v_a_2251_);
lean_dec_ref_known(v___x_2232_, 1);
v___x_2252_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__14));
v___x_2253_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImportKind_fromJson_spec__1(v_json_2209_, v___x_2252_);
if (lean_obj_tag(v___x_2253_) == 0)
{
lean_object* v_a_2254_; lean_object* v___x_2256_; uint8_t v_isShared_2257_; uint8_t v_isSharedCheck_2263_; 
lean_dec(v_a_2251_);
lean_dec(v_a_2230_);
v_a_2254_ = lean_ctor_get(v___x_2253_, 0);
v_isSharedCheck_2263_ = !lean_is_exclusive(v___x_2253_);
if (v_isSharedCheck_2263_ == 0)
{
v___x_2256_ = v___x_2253_;
v_isShared_2257_ = v_isSharedCheck_2263_;
goto v_resetjp_2255_;
}
else
{
lean_inc(v_a_2254_);
lean_dec(v___x_2253_);
v___x_2256_ = lean_box(0);
v_isShared_2257_ = v_isSharedCheck_2263_;
goto v_resetjp_2255_;
}
v_resetjp_2255_:
{
lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2261_; 
v___x_2258_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__18, &l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__18_once, _init_l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__18);
v___x_2259_ = lean_string_append(v___x_2258_, v_a_2254_);
lean_dec(v_a_2254_);
if (v_isShared_2257_ == 0)
{
lean_ctor_set(v___x_2256_, 0, v___x_2259_);
v___x_2261_ = v___x_2256_;
goto v_reusejp_2260_;
}
else
{
lean_object* v_reuseFailAlloc_2262_; 
v_reuseFailAlloc_2262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2262_, 0, v___x_2259_);
v___x_2261_ = v_reuseFailAlloc_2262_;
goto v_reusejp_2260_;
}
v_reusejp_2260_:
{
return v___x_2261_;
}
}
}
else
{
if (lean_obj_tag(v___x_2253_) == 0)
{
lean_object* v_a_2264_; lean_object* v___x_2266_; uint8_t v_isShared_2267_; uint8_t v_isSharedCheck_2271_; 
lean_dec(v_a_2251_);
lean_dec(v_a_2230_);
v_a_2264_ = lean_ctor_get(v___x_2253_, 0);
v_isSharedCheck_2271_ = !lean_is_exclusive(v___x_2253_);
if (v_isSharedCheck_2271_ == 0)
{
v___x_2266_ = v___x_2253_;
v_isShared_2267_ = v_isSharedCheck_2271_;
goto v_resetjp_2265_;
}
else
{
lean_inc(v_a_2264_);
lean_dec(v___x_2253_);
v___x_2266_ = lean_box(0);
v_isShared_2267_ = v_isSharedCheck_2271_;
goto v_resetjp_2265_;
}
v_resetjp_2265_:
{
lean_object* v___x_2269_; 
if (v_isShared_2267_ == 0)
{
lean_ctor_set_tag(v___x_2266_, 0);
v___x_2269_ = v___x_2266_;
goto v_reusejp_2268_;
}
else
{
lean_object* v_reuseFailAlloc_2270_; 
v_reuseFailAlloc_2270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2270_, 0, v_a_2264_);
v___x_2269_ = v_reuseFailAlloc_2270_;
goto v_reusejp_2268_;
}
v_reusejp_2268_:
{
return v___x_2269_;
}
}
}
else
{
lean_object* v_a_2272_; lean_object* v___x_2274_; uint8_t v_isShared_2275_; uint8_t v_isSharedCheck_2283_; 
v_a_2272_ = lean_ctor_get(v___x_2253_, 0);
v_isSharedCheck_2283_ = !lean_is_exclusive(v___x_2253_);
if (v_isSharedCheck_2283_ == 0)
{
v___x_2274_ = v___x_2253_;
v_isShared_2275_ = v_isSharedCheck_2283_;
goto v_resetjp_2273_;
}
else
{
lean_inc(v_a_2272_);
lean_dec(v___x_2253_);
v___x_2274_ = lean_box(0);
v_isShared_2275_ = v_isSharedCheck_2283_;
goto v_resetjp_2273_;
}
v_resetjp_2273_:
{
lean_object* v___x_2276_; uint8_t v___x_2277_; uint8_t v___x_2278_; uint8_t v___x_2279_; lean_object* v___x_2281_; 
v___x_2276_ = lean_alloc_ctor(0, 0, 3);
v___x_2277_ = lean_unbox(v_a_2230_);
lean_dec(v_a_2230_);
lean_ctor_set_uint8(v___x_2276_, 0, v___x_2277_);
v___x_2278_ = lean_unbox(v_a_2251_);
lean_dec(v_a_2251_);
lean_ctor_set_uint8(v___x_2276_, 1, v___x_2278_);
v___x_2279_ = lean_unbox(v_a_2272_);
lean_dec(v_a_2272_);
lean_ctor_set_uint8(v___x_2276_, 2, v___x_2279_);
if (v_isShared_2275_ == 0)
{
lean_ctor_set(v___x_2274_, 0, v___x_2276_);
v___x_2281_ = v___x_2274_;
goto v_reusejp_2280_;
}
else
{
lean_object* v_reuseFailAlloc_2282_; 
v_reuseFailAlloc_2282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2282_, 0, v___x_2276_);
v___x_2281_ = v_reuseFailAlloc_2282_;
goto v_reusejp_2280_;
}
v_reusejp_2280_:
{
return v___x_2281_;
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
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanImportKind_toJson(lean_object* v_x_2286_){
_start:
{
uint8_t v_isPrivate_2287_; uint8_t v_isAll_2288_; uint8_t v_metaKind_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; 
v_isPrivate_2287_ = lean_ctor_get_uint8(v_x_2286_, 0);
v_isAll_2288_ = lean_ctor_get_uint8(v_x_2286_, 1);
v_metaKind_2289_ = lean_ctor_get_uint8(v_x_2286_, 2);
v___x_2290_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__0));
v___x_2291_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2291_, 0, v_isPrivate_2287_);
v___x_2292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2292_, 0, v___x_2290_);
lean_ctor_set(v___x_2292_, 1, v___x_2291_);
v___x_2293_ = lean_box(0);
v___x_2294_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2294_, 0, v___x_2292_);
lean_ctor_set(v___x_2294_, 1, v___x_2293_);
v___x_2295_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__9));
v___x_2296_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2296_, 0, v_isAll_2288_);
v___x_2297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2297_, 0, v___x_2295_);
lean_ctor_set(v___x_2297_, 1, v___x_2296_);
v___x_2298_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2298_, 0, v___x_2297_);
lean_ctor_set(v___x_2298_, 1, v___x_2293_);
v___x_2299_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImportKind_fromJson___closed__14));
v___x_2300_ = l_Lean_Lsp_instToJsonLeanImportMetaKind_toJson(v_metaKind_2289_);
v___x_2301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2301_, 0, v___x_2299_);
lean_ctor_set(v___x_2301_, 1, v___x_2300_);
v___x_2302_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2302_, 0, v___x_2301_);
lean_ctor_set(v___x_2302_, 1, v___x_2293_);
v___x_2303_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2303_, 0, v___x_2302_);
lean_ctor_set(v___x_2303_, 1, v___x_2293_);
v___x_2304_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2304_, 0, v___x_2298_);
lean_ctor_set(v___x_2304_, 1, v___x_2303_);
v___x_2305_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2305_, 0, v___x_2294_);
lean_ctor_set(v___x_2305_, 1, v___x_2304_);
v___x_2306_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0));
v___x_2307_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_2305_, v___x_2306_);
v___x_2308_ = l_Lean_Json_mkObj(v___x_2307_);
lean_dec(v___x_2307_);
return v___x_2308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanImportKind_toJson___boxed(lean_object* v_x_2309_){
_start:
{
lean_object* v_res_2310_; 
v_res_2310_ = l_Lean_Lsp_instToJsonLeanImportKind_toJson(v_x_2309_);
lean_dec_ref(v_x_2309_);
return v_res_2310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImport_fromJson_spec__0(lean_object* v_j_2313_, lean_object* v_k_2314_){
_start:
{
lean_object* v___x_2315_; lean_object* v___x_2316_; 
v___x_2315_ = l_Lean_Json_getObjValD(v_j_2313_, v_k_2314_);
v___x_2316_ = l_Lean_Lsp_instFromJsonLeanModule_fromJson(v___x_2315_);
return v___x_2316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImport_fromJson_spec__0___boxed(lean_object* v_j_2317_, lean_object* v_k_2318_){
_start:
{
lean_object* v_res_2319_; 
v_res_2319_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImport_fromJson_spec__0(v_j_2317_, v_k_2318_);
lean_dec_ref(v_k_2318_);
return v_res_2319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImport_fromJson_spec__1(lean_object* v_j_2320_, lean_object* v_k_2321_){
_start:
{
lean_object* v___x_2322_; lean_object* v___x_2323_; 
v___x_2322_ = l_Lean_Json_getObjValD(v_j_2320_, v_k_2321_);
v___x_2323_ = l_Lean_Lsp_instFromJsonLeanImportKind_fromJson(v___x_2322_);
return v___x_2323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImport_fromJson_spec__1___boxed(lean_object* v_j_2324_, lean_object* v_k_2325_){
_start:
{
lean_object* v_res_2326_; 
v_res_2326_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImport_fromJson_spec__1(v_j_2324_, v_k_2325_);
lean_dec_ref(v_k_2325_);
return v_res_2326_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__3(void){
_start:
{
uint8_t v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; 
v___x_2333_ = 1;
v___x_2334_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__2));
v___x_2335_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2334_, v___x_2333_);
return v___x_2335_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__4(void){
_start:
{
lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; 
v___x_2336_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6));
v___x_2337_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__3);
v___x_2338_ = lean_string_append(v___x_2337_, v___x_2336_);
return v___x_2338_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__6(void){
_start:
{
uint8_t v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; 
v___x_2341_ = 1;
v___x_2342_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__5));
v___x_2343_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2342_, v___x_2341_);
return v___x_2343_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__7(void){
_start:
{
lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; 
v___x_2344_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__6);
v___x_2345_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__4);
v___x_2346_ = lean_string_append(v___x_2345_, v___x_2344_);
return v___x_2346_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__8(void){
_start:
{
lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; 
v___x_2347_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_2348_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__7);
v___x_2349_ = lean_string_append(v___x_2348_, v___x_2347_);
return v___x_2349_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__9(void){
_start:
{
lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; 
v___x_2350_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__11, &l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__11);
v___x_2351_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__4);
v___x_2352_ = lean_string_append(v___x_2351_, v___x_2350_);
return v___x_2352_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__10(void){
_start:
{
lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; 
v___x_2353_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_2354_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__9, &l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__9);
v___x_2355_ = lean_string_append(v___x_2354_, v___x_2353_);
return v___x_2355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanImport_fromJson(lean_object* v_json_2356_){
_start:
{
lean_object* v___x_2357_; lean_object* v___x_2358_; 
v___x_2357_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__0));
lean_inc(v_json_2356_);
v___x_2358_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImport_fromJson_spec__0(v_json_2356_, v___x_2357_);
if (lean_obj_tag(v___x_2358_) == 0)
{
lean_object* v_a_2359_; lean_object* v___x_2361_; uint8_t v_isShared_2362_; uint8_t v_isSharedCheck_2368_; 
lean_dec(v_json_2356_);
v_a_2359_ = lean_ctor_get(v___x_2358_, 0);
v_isSharedCheck_2368_ = !lean_is_exclusive(v___x_2358_);
if (v_isSharedCheck_2368_ == 0)
{
v___x_2361_ = v___x_2358_;
v_isShared_2362_ = v_isSharedCheck_2368_;
goto v_resetjp_2360_;
}
else
{
lean_inc(v_a_2359_);
lean_dec(v___x_2358_);
v___x_2361_ = lean_box(0);
v_isShared_2362_ = v_isSharedCheck_2368_;
goto v_resetjp_2360_;
}
v_resetjp_2360_:
{
lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2366_; 
v___x_2363_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__8);
v___x_2364_ = lean_string_append(v___x_2363_, v_a_2359_);
lean_dec(v_a_2359_);
if (v_isShared_2362_ == 0)
{
lean_ctor_set(v___x_2361_, 0, v___x_2364_);
v___x_2366_ = v___x_2361_;
goto v_reusejp_2365_;
}
else
{
lean_object* v_reuseFailAlloc_2367_; 
v_reuseFailAlloc_2367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2367_, 0, v___x_2364_);
v___x_2366_ = v_reuseFailAlloc_2367_;
goto v_reusejp_2365_;
}
v_reusejp_2365_:
{
return v___x_2366_;
}
}
}
else
{
if (lean_obj_tag(v___x_2358_) == 0)
{
lean_object* v_a_2369_; lean_object* v___x_2371_; uint8_t v_isShared_2372_; uint8_t v_isSharedCheck_2376_; 
lean_dec(v_json_2356_);
v_a_2369_ = lean_ctor_get(v___x_2358_, 0);
v_isSharedCheck_2376_ = !lean_is_exclusive(v___x_2358_);
if (v_isSharedCheck_2376_ == 0)
{
v___x_2371_ = v___x_2358_;
v_isShared_2372_ = v_isSharedCheck_2376_;
goto v_resetjp_2370_;
}
else
{
lean_inc(v_a_2369_);
lean_dec(v___x_2358_);
v___x_2371_ = lean_box(0);
v_isShared_2372_ = v_isSharedCheck_2376_;
goto v_resetjp_2370_;
}
v_resetjp_2370_:
{
lean_object* v___x_2374_; 
if (v_isShared_2372_ == 0)
{
lean_ctor_set_tag(v___x_2371_, 0);
v___x_2374_ = v___x_2371_;
goto v_reusejp_2373_;
}
else
{
lean_object* v_reuseFailAlloc_2375_; 
v_reuseFailAlloc_2375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2375_, 0, v_a_2369_);
v___x_2374_ = v_reuseFailAlloc_2375_;
goto v_reusejp_2373_;
}
v_reusejp_2373_:
{
return v___x_2374_;
}
}
}
else
{
lean_object* v_a_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; 
v_a_2377_ = lean_ctor_get(v___x_2358_, 0);
lean_inc(v_a_2377_);
lean_dec_ref_known(v___x_2358_, 1);
v___x_2378_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__9));
v___x_2379_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImport_fromJson_spec__1(v_json_2356_, v___x_2378_);
if (lean_obj_tag(v___x_2379_) == 0)
{
lean_object* v_a_2380_; lean_object* v___x_2382_; uint8_t v_isShared_2383_; uint8_t v_isSharedCheck_2389_; 
lean_dec(v_a_2377_);
v_a_2380_ = lean_ctor_get(v___x_2379_, 0);
v_isSharedCheck_2389_ = !lean_is_exclusive(v___x_2379_);
if (v_isSharedCheck_2389_ == 0)
{
v___x_2382_ = v___x_2379_;
v_isShared_2383_ = v_isSharedCheck_2389_;
goto v_resetjp_2381_;
}
else
{
lean_inc(v_a_2380_);
lean_dec(v___x_2379_);
v___x_2382_ = lean_box(0);
v_isShared_2383_ = v_isSharedCheck_2389_;
goto v_resetjp_2381_;
}
v_resetjp_2381_:
{
lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2387_; 
v___x_2384_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__10, &l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__10);
v___x_2385_ = lean_string_append(v___x_2384_, v_a_2380_);
lean_dec(v_a_2380_);
if (v_isShared_2383_ == 0)
{
lean_ctor_set(v___x_2382_, 0, v___x_2385_);
v___x_2387_ = v___x_2382_;
goto v_reusejp_2386_;
}
else
{
lean_object* v_reuseFailAlloc_2388_; 
v_reuseFailAlloc_2388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2388_, 0, v___x_2385_);
v___x_2387_ = v_reuseFailAlloc_2388_;
goto v_reusejp_2386_;
}
v_reusejp_2386_:
{
return v___x_2387_;
}
}
}
else
{
if (lean_obj_tag(v___x_2379_) == 0)
{
lean_object* v_a_2390_; lean_object* v___x_2392_; uint8_t v_isShared_2393_; uint8_t v_isSharedCheck_2397_; 
lean_dec(v_a_2377_);
v_a_2390_ = lean_ctor_get(v___x_2379_, 0);
v_isSharedCheck_2397_ = !lean_is_exclusive(v___x_2379_);
if (v_isSharedCheck_2397_ == 0)
{
v___x_2392_ = v___x_2379_;
v_isShared_2393_ = v_isSharedCheck_2397_;
goto v_resetjp_2391_;
}
else
{
lean_inc(v_a_2390_);
lean_dec(v___x_2379_);
v___x_2392_ = lean_box(0);
v_isShared_2393_ = v_isSharedCheck_2397_;
goto v_resetjp_2391_;
}
v_resetjp_2391_:
{
lean_object* v___x_2395_; 
if (v_isShared_2393_ == 0)
{
lean_ctor_set_tag(v___x_2392_, 0);
v___x_2395_ = v___x_2392_;
goto v_reusejp_2394_;
}
else
{
lean_object* v_reuseFailAlloc_2396_; 
v_reuseFailAlloc_2396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2396_, 0, v_a_2390_);
v___x_2395_ = v_reuseFailAlloc_2396_;
goto v_reusejp_2394_;
}
v_reusejp_2394_:
{
return v___x_2395_;
}
}
}
else
{
lean_object* v_a_2398_; lean_object* v___x_2400_; uint8_t v_isShared_2401_; uint8_t v_isSharedCheck_2406_; 
v_a_2398_ = lean_ctor_get(v___x_2379_, 0);
v_isSharedCheck_2406_ = !lean_is_exclusive(v___x_2379_);
if (v_isSharedCheck_2406_ == 0)
{
v___x_2400_ = v___x_2379_;
v_isShared_2401_ = v_isSharedCheck_2406_;
goto v_resetjp_2399_;
}
else
{
lean_inc(v_a_2398_);
lean_dec(v___x_2379_);
v___x_2400_ = lean_box(0);
v_isShared_2401_ = v_isSharedCheck_2406_;
goto v_resetjp_2399_;
}
v_resetjp_2399_:
{
lean_object* v___x_2402_; lean_object* v___x_2404_; 
v___x_2402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2402_, 0, v_a_2377_);
lean_ctor_set(v___x_2402_, 1, v_a_2398_);
if (v_isShared_2401_ == 0)
{
lean_ctor_set(v___x_2400_, 0, v___x_2402_);
v___x_2404_ = v___x_2400_;
goto v_reusejp_2403_;
}
else
{
lean_object* v_reuseFailAlloc_2405_; 
v_reuseFailAlloc_2405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2405_, 0, v___x_2402_);
v___x_2404_ = v_reuseFailAlloc_2405_;
goto v_reusejp_2403_;
}
v_reusejp_2403_:
{
return v___x_2404_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanImport_toJson(lean_object* v_x_2409_){
_start:
{
lean_object* v_module_2410_; lean_object* v_kind_2411_; lean_object* v___x_2413_; uint8_t v_isShared_2414_; uint8_t v_isSharedCheck_2431_; 
v_module_2410_ = lean_ctor_get(v_x_2409_, 0);
v_kind_2411_ = lean_ctor_get(v_x_2409_, 1);
v_isSharedCheck_2431_ = !lean_is_exclusive(v_x_2409_);
if (v_isSharedCheck_2431_ == 0)
{
v___x_2413_ = v_x_2409_;
v_isShared_2414_ = v_isSharedCheck_2431_;
goto v_resetjp_2412_;
}
else
{
lean_inc(v_kind_2411_);
lean_inc(v_module_2410_);
lean_dec(v_x_2409_);
v___x_2413_ = lean_box(0);
v_isShared_2414_ = v_isSharedCheck_2431_;
goto v_resetjp_2412_;
}
v_resetjp_2412_:
{
lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2418_; 
v___x_2415_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__0));
v___x_2416_ = l_Lean_Lsp_instToJsonLeanModule_toJson(v_module_2410_);
lean_dec_ref(v_module_2410_);
if (v_isShared_2414_ == 0)
{
lean_ctor_set(v___x_2413_, 1, v___x_2416_);
lean_ctor_set(v___x_2413_, 0, v___x_2415_);
v___x_2418_ = v___x_2413_;
goto v_reusejp_2417_;
}
else
{
lean_object* v_reuseFailAlloc_2430_; 
v_reuseFailAlloc_2430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2430_, 0, v___x_2415_);
lean_ctor_set(v_reuseFailAlloc_2430_, 1, v___x_2416_);
v___x_2418_ = v_reuseFailAlloc_2430_;
goto v_reusejp_2417_;
}
v_reusejp_2417_:
{
lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; 
v___x_2419_ = lean_box(0);
v___x_2420_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2420_, 0, v___x_2418_);
lean_ctor_set(v___x_2420_, 1, v___x_2419_);
v___x_2421_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressProcessingInfo_fromJson___closed__9));
v___x_2422_ = l_Lean_Lsp_instToJsonLeanImportKind_toJson(v_kind_2411_);
lean_dec_ref(v_kind_2411_);
v___x_2423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2423_, 0, v___x_2421_);
lean_ctor_set(v___x_2423_, 1, v___x_2422_);
v___x_2424_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2424_, 0, v___x_2423_);
lean_ctor_set(v___x_2424_, 1, v___x_2419_);
v___x_2425_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2425_, 0, v___x_2424_);
lean_ctor_set(v___x_2425_, 1, v___x_2419_);
v___x_2426_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2426_, 0, v___x_2420_);
lean_ctor_set(v___x_2426_, 1, v___x_2425_);
v___x_2427_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0));
v___x_2428_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_2426_, v___x_2427_);
v___x_2429_ = l_Lean_Json_mkObj(v___x_2428_);
lean_dec(v___x_2428_);
return v___x_2429_;
}
}
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__2(void){
_start:
{
uint8_t v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; 
v___x_2439_ = 1;
v___x_2440_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__1));
v___x_2441_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2440_, v___x_2439_);
return v___x_2441_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__3(void){
_start:
{
lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; 
v___x_2442_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6));
v___x_2443_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__2, &l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__2);
v___x_2444_ = lean_string_append(v___x_2443_, v___x_2442_);
return v___x_2444_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; 
v___x_2445_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__6);
v___x_2446_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__3);
v___x_2447_ = lean_string_append(v___x_2446_, v___x_2445_);
return v___x_2447_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__5(void){
_start:
{
lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; 
v___x_2448_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_2449_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__4);
v___x_2450_ = lean_string_append(v___x_2449_, v___x_2448_);
return v___x_2450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson(lean_object* v_json_2451_){
_start:
{
lean_object* v___x_2452_; lean_object* v___x_2453_; 
v___x_2452_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__0));
v___x_2453_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImport_fromJson_spec__0(v_json_2451_, v___x_2452_);
if (lean_obj_tag(v___x_2453_) == 0)
{
lean_object* v_a_2454_; lean_object* v___x_2456_; uint8_t v_isShared_2457_; uint8_t v_isSharedCheck_2463_; 
v_a_2454_ = lean_ctor_get(v___x_2453_, 0);
v_isSharedCheck_2463_ = !lean_is_exclusive(v___x_2453_);
if (v_isSharedCheck_2463_ == 0)
{
v___x_2456_ = v___x_2453_;
v_isShared_2457_ = v_isSharedCheck_2463_;
goto v_resetjp_2455_;
}
else
{
lean_inc(v_a_2454_);
lean_dec(v___x_2453_);
v___x_2456_ = lean_box(0);
v_isShared_2457_ = v_isSharedCheck_2463_;
goto v_resetjp_2455_;
}
v_resetjp_2455_:
{
lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2461_; 
v___x_2458_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__5, &l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportsParams_fromJson___closed__5);
v___x_2459_ = lean_string_append(v___x_2458_, v_a_2454_);
lean_dec(v_a_2454_);
if (v_isShared_2457_ == 0)
{
lean_ctor_set(v___x_2456_, 0, v___x_2459_);
v___x_2461_ = v___x_2456_;
goto v_reusejp_2460_;
}
else
{
lean_object* v_reuseFailAlloc_2462_; 
v_reuseFailAlloc_2462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2462_, 0, v___x_2459_);
v___x_2461_ = v_reuseFailAlloc_2462_;
goto v_reusejp_2460_;
}
v_reusejp_2460_:
{
return v___x_2461_;
}
}
}
else
{
if (lean_obj_tag(v___x_2453_) == 0)
{
lean_object* v_a_2464_; lean_object* v___x_2466_; uint8_t v_isShared_2467_; uint8_t v_isSharedCheck_2471_; 
v_a_2464_ = lean_ctor_get(v___x_2453_, 0);
v_isSharedCheck_2471_ = !lean_is_exclusive(v___x_2453_);
if (v_isSharedCheck_2471_ == 0)
{
v___x_2466_ = v___x_2453_;
v_isShared_2467_ = v_isSharedCheck_2471_;
goto v_resetjp_2465_;
}
else
{
lean_inc(v_a_2464_);
lean_dec(v___x_2453_);
v___x_2466_ = lean_box(0);
v_isShared_2467_ = v_isSharedCheck_2471_;
goto v_resetjp_2465_;
}
v_resetjp_2465_:
{
lean_object* v___x_2469_; 
if (v_isShared_2467_ == 0)
{
lean_ctor_set_tag(v___x_2466_, 0);
v___x_2469_ = v___x_2466_;
goto v_reusejp_2468_;
}
else
{
lean_object* v_reuseFailAlloc_2470_; 
v_reuseFailAlloc_2470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2470_, 0, v_a_2464_);
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
lean_object* v_a_2472_; lean_object* v___x_2474_; uint8_t v_isShared_2475_; uint8_t v_isSharedCheck_2479_; 
v_a_2472_ = lean_ctor_get(v___x_2453_, 0);
v_isSharedCheck_2479_ = !lean_is_exclusive(v___x_2453_);
if (v_isSharedCheck_2479_ == 0)
{
v___x_2474_ = v___x_2453_;
v_isShared_2475_ = v_isSharedCheck_2479_;
goto v_resetjp_2473_;
}
else
{
lean_inc(v_a_2472_);
lean_dec(v___x_2453_);
v___x_2474_ = lean_box(0);
v_isShared_2475_ = v_isSharedCheck_2479_;
goto v_resetjp_2473_;
}
v_resetjp_2473_:
{
lean_object* v___x_2477_; 
if (v_isShared_2475_ == 0)
{
v___x_2477_ = v___x_2474_;
goto v_reusejp_2476_;
}
else
{
lean_object* v_reuseFailAlloc_2478_; 
v_reuseFailAlloc_2478_ = lean_alloc_ctor(1, 1, 0);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanModuleHierarchyImportsParams_toJson(lean_object* v_x_2482_){
_start:
{
lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; 
v___x_2483_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__0));
v___x_2484_ = l_Lean_Lsp_instToJsonLeanModule_toJson(v_x_2482_);
v___x_2485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2485_, 0, v___x_2483_);
lean_ctor_set(v___x_2485_, 1, v___x_2484_);
v___x_2486_ = lean_box(0);
v___x_2487_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2487_, 0, v___x_2485_);
lean_ctor_set(v___x_2487_, 1, v___x_2486_);
v___x_2488_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2488_, 0, v___x_2487_);
lean_ctor_set(v___x_2488_, 1, v___x_2486_);
v___x_2489_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0));
v___x_2490_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_2488_, v___x_2489_);
v___x_2491_ = l_Lean_Json_mkObj(v___x_2490_);
lean_dec(v___x_2490_);
return v___x_2491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanModuleHierarchyImportsParams_toJson___boxed(lean_object* v_x_2492_){
_start:
{
lean_object* v_res_2493_; 
v_res_2493_ = l_Lean_Lsp_instToJsonLeanModuleHierarchyImportsParams_toJson(v_x_2492_);
lean_dec_ref(v_x_2492_);
return v_res_2493_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__2(void){
_start:
{
uint8_t v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; 
v___x_2501_ = 1;
v___x_2502_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__1));
v___x_2503_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2502_, v___x_2501_);
return v___x_2503_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__3(void){
_start:
{
lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; 
v___x_2504_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6));
v___x_2505_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__2, &l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__2);
v___x_2506_ = lean_string_append(v___x_2505_, v___x_2504_);
return v___x_2506_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; 
v___x_2507_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__6);
v___x_2508_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__3);
v___x_2509_ = lean_string_append(v___x_2508_, v___x_2507_);
return v___x_2509_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__5(void){
_start:
{
lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; 
v___x_2510_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_2511_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__4);
v___x_2512_ = lean_string_append(v___x_2511_, v___x_2510_);
return v___x_2512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson(lean_object* v_json_2513_){
_start:
{
lean_object* v___x_2514_; lean_object* v___x_2515_; 
v___x_2514_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__0));
v___x_2515_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanImport_fromJson_spec__0(v_json_2513_, v___x_2514_);
if (lean_obj_tag(v___x_2515_) == 0)
{
lean_object* v_a_2516_; lean_object* v___x_2518_; uint8_t v_isShared_2519_; uint8_t v_isSharedCheck_2525_; 
v_a_2516_ = lean_ctor_get(v___x_2515_, 0);
v_isSharedCheck_2525_ = !lean_is_exclusive(v___x_2515_);
if (v_isSharedCheck_2525_ == 0)
{
v___x_2518_ = v___x_2515_;
v_isShared_2519_ = v_isSharedCheck_2525_;
goto v_resetjp_2517_;
}
else
{
lean_inc(v_a_2516_);
lean_dec(v___x_2515_);
v___x_2518_ = lean_box(0);
v_isShared_2519_ = v_isSharedCheck_2525_;
goto v_resetjp_2517_;
}
v_resetjp_2517_:
{
lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2523_; 
v___x_2520_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__5, &l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonLeanModuleHierarchyImportedByParams_fromJson___closed__5);
v___x_2521_ = lean_string_append(v___x_2520_, v_a_2516_);
lean_dec(v_a_2516_);
if (v_isShared_2519_ == 0)
{
lean_ctor_set(v___x_2518_, 0, v___x_2521_);
v___x_2523_ = v___x_2518_;
goto v_reusejp_2522_;
}
else
{
lean_object* v_reuseFailAlloc_2524_; 
v_reuseFailAlloc_2524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2524_, 0, v___x_2521_);
v___x_2523_ = v_reuseFailAlloc_2524_;
goto v_reusejp_2522_;
}
v_reusejp_2522_:
{
return v___x_2523_;
}
}
}
else
{
if (lean_obj_tag(v___x_2515_) == 0)
{
lean_object* v_a_2526_; lean_object* v___x_2528_; uint8_t v_isShared_2529_; uint8_t v_isSharedCheck_2533_; 
v_a_2526_ = lean_ctor_get(v___x_2515_, 0);
v_isSharedCheck_2533_ = !lean_is_exclusive(v___x_2515_);
if (v_isSharedCheck_2533_ == 0)
{
v___x_2528_ = v___x_2515_;
v_isShared_2529_ = v_isSharedCheck_2533_;
goto v_resetjp_2527_;
}
else
{
lean_inc(v_a_2526_);
lean_dec(v___x_2515_);
v___x_2528_ = lean_box(0);
v_isShared_2529_ = v_isSharedCheck_2533_;
goto v_resetjp_2527_;
}
v_resetjp_2527_:
{
lean_object* v___x_2531_; 
if (v_isShared_2529_ == 0)
{
lean_ctor_set_tag(v___x_2528_, 0);
v___x_2531_ = v___x_2528_;
goto v_reusejp_2530_;
}
else
{
lean_object* v_reuseFailAlloc_2532_; 
v_reuseFailAlloc_2532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2532_, 0, v_a_2526_);
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
lean_object* v_a_2534_; lean_object* v___x_2536_; uint8_t v_isShared_2537_; uint8_t v_isSharedCheck_2541_; 
v_a_2534_ = lean_ctor_get(v___x_2515_, 0);
v_isSharedCheck_2541_ = !lean_is_exclusive(v___x_2515_);
if (v_isSharedCheck_2541_ == 0)
{
v___x_2536_ = v___x_2515_;
v_isShared_2537_ = v_isSharedCheck_2541_;
goto v_resetjp_2535_;
}
else
{
lean_inc(v_a_2534_);
lean_dec(v___x_2515_);
v___x_2536_ = lean_box(0);
v_isShared_2537_ = v_isSharedCheck_2541_;
goto v_resetjp_2535_;
}
v_resetjp_2535_:
{
lean_object* v___x_2539_; 
if (v_isShared_2537_ == 0)
{
v___x_2539_ = v___x_2536_;
goto v_reusejp_2538_;
}
else
{
lean_object* v_reuseFailAlloc_2540_; 
v_reuseFailAlloc_2540_ = lean_alloc_ctor(1, 1, 0);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanModuleHierarchyImportedByParams_toJson(lean_object* v_x_2544_){
_start:
{
lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; 
v___x_2545_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanImport_fromJson___closed__0));
v___x_2546_ = l_Lean_Lsp_instToJsonLeanModule_toJson(v_x_2544_);
v___x_2547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2547_, 0, v___x_2545_);
lean_ctor_set(v___x_2547_, 1, v___x_2546_);
v___x_2548_ = lean_box(0);
v___x_2549_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2549_, 0, v___x_2547_);
lean_ctor_set(v___x_2549_, 1, v___x_2548_);
v___x_2550_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2550_, 0, v___x_2549_);
lean_ctor_set(v___x_2550_, 1, v___x_2548_);
v___x_2551_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0));
v___x_2552_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_2550_, v___x_2551_);
v___x_2553_ = l_Lean_Json_mkObj(v___x_2552_);
lean_dec(v___x_2552_);
return v___x_2553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanModuleHierarchyImportedByParams_toJson___boxed(lean_object* v_x_2554_){
_start:
{
lean_object* v_res_2555_; 
v_res_2555_ = l_Lean_Lsp_instToJsonLeanModuleHierarchyImportedByParams_toJson(v_x_2554_);
lean_dec_ref(v_x_2554_);
return v_res_2555_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__2(void){
_start:
{
uint8_t v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; 
v___x_2563_ = 1;
v___x_2564_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__1));
v___x_2565_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2564_, v___x_2563_);
return v___x_2565_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__3(void){
_start:
{
lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; 
v___x_2566_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6));
v___x_2567_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__2, &l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__2);
v___x_2568_ = lean_string_append(v___x_2567_, v___x_2566_);
return v___x_2568_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; 
v___x_2569_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__6, &l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__6);
v___x_2570_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__3);
v___x_2571_ = lean_string_append(v___x_2570_, v___x_2569_);
return v___x_2571_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__5(void){
_start:
{
lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; 
v___x_2572_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_2573_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__4);
v___x_2574_ = lean_string_append(v___x_2573_, v___x_2572_);
return v___x_2574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson(lean_object* v_json_2575_){
_start:
{
lean_object* v___x_2576_; lean_object* v___x_2577_; 
v___x_2576_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__0));
v___x_2577_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson_spec__0(v_json_2575_, v___x_2576_);
if (lean_obj_tag(v___x_2577_) == 0)
{
lean_object* v_a_2578_; lean_object* v___x_2580_; uint8_t v_isShared_2581_; uint8_t v_isSharedCheck_2587_; 
v_a_2578_ = lean_ctor_get(v___x_2577_, 0);
v_isSharedCheck_2587_ = !lean_is_exclusive(v___x_2577_);
if (v_isSharedCheck_2587_ == 0)
{
v___x_2580_ = v___x_2577_;
v_isShared_2581_ = v_isSharedCheck_2587_;
goto v_resetjp_2579_;
}
else
{
lean_inc(v_a_2578_);
lean_dec(v___x_2577_);
v___x_2580_ = lean_box(0);
v_isShared_2581_ = v_isSharedCheck_2587_;
goto v_resetjp_2579_;
}
v_resetjp_2579_:
{
lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2585_; 
v___x_2582_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__5, &l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonRpcConnectParams_fromJson___closed__5);
v___x_2583_ = lean_string_append(v___x_2582_, v_a_2578_);
lean_dec(v_a_2578_);
if (v_isShared_2581_ == 0)
{
lean_ctor_set(v___x_2580_, 0, v___x_2583_);
v___x_2585_ = v___x_2580_;
goto v_reusejp_2584_;
}
else
{
lean_object* v_reuseFailAlloc_2586_; 
v_reuseFailAlloc_2586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2586_, 0, v___x_2583_);
v___x_2585_ = v_reuseFailAlloc_2586_;
goto v_reusejp_2584_;
}
v_reusejp_2584_:
{
return v___x_2585_;
}
}
}
else
{
if (lean_obj_tag(v___x_2577_) == 0)
{
lean_object* v_a_2588_; lean_object* v___x_2590_; uint8_t v_isShared_2591_; uint8_t v_isSharedCheck_2595_; 
v_a_2588_ = lean_ctor_get(v___x_2577_, 0);
v_isSharedCheck_2595_ = !lean_is_exclusive(v___x_2577_);
if (v_isSharedCheck_2595_ == 0)
{
v___x_2590_ = v___x_2577_;
v_isShared_2591_ = v_isSharedCheck_2595_;
goto v_resetjp_2589_;
}
else
{
lean_inc(v_a_2588_);
lean_dec(v___x_2577_);
v___x_2590_ = lean_box(0);
v_isShared_2591_ = v_isSharedCheck_2595_;
goto v_resetjp_2589_;
}
v_resetjp_2589_:
{
lean_object* v___x_2593_; 
if (v_isShared_2591_ == 0)
{
lean_ctor_set_tag(v___x_2590_, 0);
v___x_2593_ = v___x_2590_;
goto v_reusejp_2592_;
}
else
{
lean_object* v_reuseFailAlloc_2594_; 
v_reuseFailAlloc_2594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2594_, 0, v_a_2588_);
v___x_2593_ = v_reuseFailAlloc_2594_;
goto v_reusejp_2592_;
}
v_reusejp_2592_:
{
return v___x_2593_;
}
}
}
else
{
lean_object* v_a_2596_; lean_object* v___x_2598_; uint8_t v_isShared_2599_; uint8_t v_isSharedCheck_2603_; 
v_a_2596_ = lean_ctor_get(v___x_2577_, 0);
v_isSharedCheck_2603_ = !lean_is_exclusive(v___x_2577_);
if (v_isSharedCheck_2603_ == 0)
{
v___x_2598_ = v___x_2577_;
v_isShared_2599_ = v_isSharedCheck_2603_;
goto v_resetjp_2597_;
}
else
{
lean_inc(v_a_2596_);
lean_dec(v___x_2577_);
v___x_2598_ = lean_box(0);
v_isShared_2599_ = v_isSharedCheck_2603_;
goto v_resetjp_2597_;
}
v_resetjp_2597_:
{
lean_object* v___x_2601_; 
if (v_isShared_2599_ == 0)
{
v___x_2601_ = v___x_2598_;
goto v_reusejp_2600_;
}
else
{
lean_object* v_reuseFailAlloc_2602_; 
v_reuseFailAlloc_2602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2602_, 0, v_a_2596_);
v___x_2601_ = v_reuseFailAlloc_2602_;
goto v_reusejp_2600_;
}
v_reusejp_2600_:
{
return v___x_2601_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRpcConnectParams_toJson(lean_object* v_x_2606_){
_start:
{
lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; 
v___x_2607_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__0));
v___x_2608_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2608_, 0, v_x_2606_);
v___x_2609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2609_, 0, v___x_2607_);
lean_ctor_set(v___x_2609_, 1, v___x_2608_);
v___x_2610_ = lean_box(0);
v___x_2611_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2611_, 0, v___x_2609_);
lean_ctor_set(v___x_2611_, 1, v___x_2610_);
v___x_2612_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2612_, 0, v___x_2611_);
lean_ctor_set(v___x_2612_, 1, v___x_2610_);
v___x_2613_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0));
v___x_2614_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_2612_, v___x_2613_);
v___x_2615_ = l_Lean_Json_mkObj(v___x_2614_);
lean_dec(v___x_2614_);
return v___x_2615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcConnected_fromJson_spec__0(lean_object* v_j_2618_, lean_object* v_k_2619_){
_start:
{
lean_object* v___x_2620_; lean_object* v___x_2621_; 
v___x_2620_ = l_Lean_Json_getObjValD(v_j_2618_, v_k_2619_);
v___x_2621_ = l_Lean_UInt64_fromJson_x3f(v___x_2620_);
return v___x_2621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcConnected_fromJson_spec__0___boxed(lean_object* v_j_2622_, lean_object* v_k_2623_){
_start:
{
lean_object* v_res_2624_; 
v_res_2624_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcConnected_fromJson_spec__0(v_j_2622_, v_k_2623_);
lean_dec_ref(v_k_2623_);
return v_res_2624_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__3(void){
_start:
{
uint8_t v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; 
v___x_2631_ = 1;
v___x_2632_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__2));
v___x_2633_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2632_, v___x_2631_);
return v___x_2633_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__4(void){
_start:
{
lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; 
v___x_2634_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6));
v___x_2635_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__3, &l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__3);
v___x_2636_ = lean_string_append(v___x_2635_, v___x_2634_);
return v___x_2636_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__6(void){
_start:
{
uint8_t v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; 
v___x_2639_ = 1;
v___x_2640_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__5));
v___x_2641_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2640_, v___x_2639_);
return v___x_2641_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__7(void){
_start:
{
lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; 
v___x_2642_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__6, &l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__6);
v___x_2643_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__4, &l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__4);
v___x_2644_ = lean_string_append(v___x_2643_, v___x_2642_);
return v___x_2644_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__8(void){
_start:
{
lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; 
v___x_2645_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_2646_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__7, &l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__7);
v___x_2647_ = lean_string_append(v___x_2646_, v___x_2645_);
return v___x_2647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonRpcConnected_fromJson(lean_object* v_json_2648_){
_start:
{
lean_object* v___x_2649_; lean_object* v___x_2650_; 
v___x_2649_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__0));
v___x_2650_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcConnected_fromJson_spec__0(v_json_2648_, v___x_2649_);
if (lean_obj_tag(v___x_2650_) == 0)
{
lean_object* v_a_2651_; lean_object* v___x_2653_; uint8_t v_isShared_2654_; uint8_t v_isSharedCheck_2660_; 
v_a_2651_ = lean_ctor_get(v___x_2650_, 0);
v_isSharedCheck_2660_ = !lean_is_exclusive(v___x_2650_);
if (v_isSharedCheck_2660_ == 0)
{
v___x_2653_ = v___x_2650_;
v_isShared_2654_ = v_isSharedCheck_2660_;
goto v_resetjp_2652_;
}
else
{
lean_inc(v_a_2651_);
lean_dec(v___x_2650_);
v___x_2653_ = lean_box(0);
v_isShared_2654_ = v_isSharedCheck_2660_;
goto v_resetjp_2652_;
}
v_resetjp_2652_:
{
lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2658_; 
v___x_2655_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__8, &l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__8);
v___x_2656_ = lean_string_append(v___x_2655_, v_a_2651_);
lean_dec(v_a_2651_);
if (v_isShared_2654_ == 0)
{
lean_ctor_set(v___x_2653_, 0, v___x_2656_);
v___x_2658_ = v___x_2653_;
goto v_reusejp_2657_;
}
else
{
lean_object* v_reuseFailAlloc_2659_; 
v_reuseFailAlloc_2659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2659_, 0, v___x_2656_);
v___x_2658_ = v_reuseFailAlloc_2659_;
goto v_reusejp_2657_;
}
v_reusejp_2657_:
{
return v___x_2658_;
}
}
}
else
{
if (lean_obj_tag(v___x_2650_) == 0)
{
lean_object* v_a_2661_; lean_object* v___x_2663_; uint8_t v_isShared_2664_; uint8_t v_isSharedCheck_2668_; 
v_a_2661_ = lean_ctor_get(v___x_2650_, 0);
v_isSharedCheck_2668_ = !lean_is_exclusive(v___x_2650_);
if (v_isSharedCheck_2668_ == 0)
{
v___x_2663_ = v___x_2650_;
v_isShared_2664_ = v_isSharedCheck_2668_;
goto v_resetjp_2662_;
}
else
{
lean_inc(v_a_2661_);
lean_dec(v___x_2650_);
v___x_2663_ = lean_box(0);
v_isShared_2664_ = v_isSharedCheck_2668_;
goto v_resetjp_2662_;
}
v_resetjp_2662_:
{
lean_object* v___x_2666_; 
if (v_isShared_2664_ == 0)
{
lean_ctor_set_tag(v___x_2663_, 0);
v___x_2666_ = v___x_2663_;
goto v_reusejp_2665_;
}
else
{
lean_object* v_reuseFailAlloc_2667_; 
v_reuseFailAlloc_2667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2667_, 0, v_a_2661_);
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
lean_object* v_a_2669_; lean_object* v___x_2671_; uint8_t v_isShared_2672_; uint8_t v_isSharedCheck_2676_; 
v_a_2669_ = lean_ctor_get(v___x_2650_, 0);
v_isSharedCheck_2676_ = !lean_is_exclusive(v___x_2650_);
if (v_isSharedCheck_2676_ == 0)
{
v___x_2671_ = v___x_2650_;
v_isShared_2672_ = v_isSharedCheck_2676_;
goto v_resetjp_2670_;
}
else
{
lean_inc(v_a_2669_);
lean_dec(v___x_2650_);
v___x_2671_ = lean_box(0);
v_isShared_2672_ = v_isSharedCheck_2676_;
goto v_resetjp_2670_;
}
v_resetjp_2670_:
{
lean_object* v___x_2674_; 
if (v_isShared_2672_ == 0)
{
v___x_2674_ = v___x_2671_;
goto v_reusejp_2673_;
}
else
{
lean_object* v_reuseFailAlloc_2675_; 
v_reuseFailAlloc_2675_ = lean_alloc_ctor(1, 1, 0);
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
}
}
}
lean_object* l_Lean_Lsp_instToJsonRpcConnected_toJson(uint64_t v_x_2679_){
_start:
{
lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; 
v___x_2680_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__0));
v___x_2681_ = lean_uint64_to_nat(v_x_2679_);
v___x_2682_ = l_Lean_bignumToJson(v___x_2681_);
v___x_2683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2683_, 0, v___x_2680_);
lean_ctor_set(v___x_2683_, 1, v___x_2682_);
v___x_2684_ = lean_box(0);
v___x_2685_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2685_, 0, v___x_2683_);
lean_ctor_set(v___x_2685_, 1, v___x_2684_);
v___x_2686_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2686_, 0, v___x_2685_);
lean_ctor_set(v___x_2686_, 1, v___x_2684_);
v___x_2687_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0));
v___x_2688_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_2686_, v___x_2687_);
v___x_2689_ = l_Lean_Json_mkObj(v___x_2688_);
lean_dec(v___x_2688_);
return v___x_2689_;
}
}
LEAN_EXPORT void l_Lean_Lsp_instToJsonRpcConnected_toJson_0interp(lean_interpreter_value* stack)
{
uint64_t v_x_2679_ = stack[0].m_num;
lean_object* v_res_2690_;
v_res_2690_ = l_Lean_Lsp_instToJsonRpcConnected_toJson(v_x_2679_);
stack->m_obj
 = v_res_2690_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRpcConnected_toJson___boxed(lean_object* v_x_2691_){
_start:
{
uint64_t v_x_30__boxed_2692_; lean_object* v_res_2693_; 
v_x_30__boxed_2692_ = lean_unbox_uint64(v_x_2691_);
lean_dec_ref(v_x_2691_);
v_res_2693_ = l_Lean_Lsp_instToJsonRpcConnected_toJson(v_x_30__boxed_2692_);
return v_res_2693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcCallParams_fromJson_spec__0(lean_object* v_j_2696_, lean_object* v_k_2697_){
_start:
{
lean_object* v___x_2698_; lean_object* v___x_2699_; 
v___x_2698_ = l_Lean_Json_getObjValD(v_j_2696_, v_k_2697_);
v___x_2699_ = l_Lean_Name_fromJson_x3f(v___x_2698_);
return v___x_2699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcCallParams_fromJson_spec__0___boxed(lean_object* v_j_2700_, lean_object* v_k_2701_){
_start:
{
lean_object* v_res_2702_; 
v_res_2702_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcCallParams_fromJson_spec__0(v_j_2700_, v_k_2701_);
lean_dec_ref(v_k_2701_);
return v_res_2702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcCallParams_fromJson_spec__1(lean_object* v_j_2703_, lean_object* v_k_2704_){
_start:
{
lean_object* v___x_2705_; lean_object* v___x_2706_; 
v___x_2705_ = l_Lean_Json_getObjValD(v_j_2703_, v_k_2704_);
v___x_2706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2706_, 0, v___x_2705_);
return v___x_2706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcCallParams_fromJson_spec__1___boxed(lean_object* v_j_2707_, lean_object* v_k_2708_){
_start:
{
lean_object* v_res_2709_; 
v_res_2709_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcCallParams_fromJson_spec__1(v_j_2707_, v_k_2708_);
lean_dec_ref(v_k_2708_);
return v_res_2709_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__2(void){
_start:
{
uint8_t v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; 
v___x_2715_ = 1;
v___x_2716_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__1));
v___x_2717_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2716_, v___x_2715_);
return v___x_2717_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__3(void){
_start:
{
lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; 
v___x_2718_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6));
v___x_2719_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__2, &l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__2);
v___x_2720_ = lean_string_append(v___x_2719_, v___x_2718_);
return v___x_2720_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; 
v___x_2721_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9, &l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__9);
v___x_2722_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__3);
v___x_2723_ = lean_string_append(v___x_2722_, v___x_2721_);
return v___x_2723_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__5(void){
_start:
{
lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; 
v___x_2724_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_2725_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__4);
v___x_2726_ = lean_string_append(v___x_2725_, v___x_2724_);
return v___x_2726_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__6(void){
_start:
{
lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; 
v___x_2727_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__8);
v___x_2728_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__3);
v___x_2729_ = lean_string_append(v___x_2728_, v___x_2727_);
return v___x_2729_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__7(void){
_start:
{
lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; 
v___x_2730_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_2731_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__6, &l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__6);
v___x_2732_ = lean_string_append(v___x_2731_, v___x_2730_);
return v___x_2732_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__8(void){
_start:
{
lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; 
v___x_2733_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__6, &l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__6);
v___x_2734_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__3);
v___x_2735_ = lean_string_append(v___x_2734_, v___x_2733_);
return v___x_2735_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__9(void){
_start:
{
lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; 
v___x_2736_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_2737_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__8);
v___x_2738_ = lean_string_append(v___x_2737_, v___x_2736_);
return v___x_2738_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__12(void){
_start:
{
uint8_t v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; 
v___x_2742_ = 1;
v___x_2743_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__11));
v___x_2744_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2743_, v___x_2742_);
return v___x_2744_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__13(void){
_start:
{
lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; 
v___x_2745_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__12, &l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__12);
v___x_2746_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__3);
v___x_2747_ = lean_string_append(v___x_2746_, v___x_2745_);
return v___x_2747_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__14(void){
_start:
{
lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; 
v___x_2748_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_2749_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__13, &l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__13);
v___x_2750_ = lean_string_append(v___x_2749_, v___x_2748_);
return v___x_2750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonRpcCallParams_fromJson(lean_object* v_json_2752_){
_start:
{
lean_object* v___x_2753_; lean_object* v___x_2754_; 
v___x_2753_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__0));
lean_inc(v_json_2752_);
v___x_2754_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoalParams_fromJson_spec__0(v_json_2752_, v___x_2753_);
if (lean_obj_tag(v___x_2754_) == 0)
{
lean_object* v_a_2755_; lean_object* v___x_2757_; uint8_t v_isShared_2758_; uint8_t v_isSharedCheck_2764_; 
lean_dec(v_json_2752_);
v_a_2755_ = lean_ctor_get(v___x_2754_, 0);
v_isSharedCheck_2764_ = !lean_is_exclusive(v___x_2754_);
if (v_isSharedCheck_2764_ == 0)
{
v___x_2757_ = v___x_2754_;
v_isShared_2758_ = v_isSharedCheck_2764_;
goto v_resetjp_2756_;
}
else
{
lean_inc(v_a_2755_);
lean_dec(v___x_2754_);
v___x_2757_ = lean_box(0);
v_isShared_2758_ = v_isSharedCheck_2764_;
goto v_resetjp_2756_;
}
v_resetjp_2756_:
{
lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2762_; 
v___x_2759_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__5, &l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__5);
v___x_2760_ = lean_string_append(v___x_2759_, v_a_2755_);
lean_dec(v_a_2755_);
if (v_isShared_2758_ == 0)
{
lean_ctor_set(v___x_2757_, 0, v___x_2760_);
v___x_2762_ = v___x_2757_;
goto v_reusejp_2761_;
}
else
{
lean_object* v_reuseFailAlloc_2763_; 
v_reuseFailAlloc_2763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2763_, 0, v___x_2760_);
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
if (lean_obj_tag(v___x_2754_) == 0)
{
lean_object* v_a_2765_; lean_object* v___x_2767_; uint8_t v_isShared_2768_; uint8_t v_isSharedCheck_2772_; 
lean_dec(v_json_2752_);
v_a_2765_ = lean_ctor_get(v___x_2754_, 0);
v_isSharedCheck_2772_ = !lean_is_exclusive(v___x_2754_);
if (v_isSharedCheck_2772_ == 0)
{
v___x_2767_ = v___x_2754_;
v_isShared_2768_ = v_isSharedCheck_2772_;
goto v_resetjp_2766_;
}
else
{
lean_inc(v_a_2765_);
lean_dec(v___x_2754_);
v___x_2767_ = lean_box(0);
v_isShared_2768_ = v_isSharedCheck_2772_;
goto v_resetjp_2766_;
}
v_resetjp_2766_:
{
lean_object* v___x_2770_; 
if (v_isShared_2768_ == 0)
{
lean_ctor_set_tag(v___x_2767_, 0);
v___x_2770_ = v___x_2767_;
goto v_reusejp_2769_;
}
else
{
lean_object* v_reuseFailAlloc_2771_; 
v_reuseFailAlloc_2771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2771_, 0, v_a_2765_);
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
lean_object* v_a_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; 
v_a_2773_ = lean_ctor_get(v___x_2754_, 0);
lean_inc(v_a_2773_);
lean_dec_ref_known(v___x_2754_, 1);
v___x_2774_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__6));
lean_inc(v_json_2752_);
v___x_2775_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPlainGoalParams_fromJson_spec__1(v_json_2752_, v___x_2774_);
if (lean_obj_tag(v___x_2775_) == 0)
{
lean_object* v_a_2776_; lean_object* v___x_2778_; uint8_t v_isShared_2779_; uint8_t v_isSharedCheck_2785_; 
lean_dec(v_a_2773_);
lean_dec(v_json_2752_);
v_a_2776_ = lean_ctor_get(v___x_2775_, 0);
v_isSharedCheck_2785_ = !lean_is_exclusive(v___x_2775_);
if (v_isSharedCheck_2785_ == 0)
{
v___x_2778_ = v___x_2775_;
v_isShared_2779_ = v_isSharedCheck_2785_;
goto v_resetjp_2777_;
}
else
{
lean_inc(v_a_2776_);
lean_dec(v___x_2775_);
v___x_2778_ = lean_box(0);
v_isShared_2779_ = v_isSharedCheck_2785_;
goto v_resetjp_2777_;
}
v_resetjp_2777_:
{
lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2783_; 
v___x_2780_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__7);
v___x_2781_ = lean_string_append(v___x_2780_, v_a_2776_);
lean_dec(v_a_2776_);
if (v_isShared_2779_ == 0)
{
lean_ctor_set(v___x_2778_, 0, v___x_2781_);
v___x_2783_ = v___x_2778_;
goto v_reusejp_2782_;
}
else
{
lean_object* v_reuseFailAlloc_2784_; 
v_reuseFailAlloc_2784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2784_, 0, v___x_2781_);
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
if (lean_obj_tag(v___x_2775_) == 0)
{
lean_object* v_a_2786_; lean_object* v___x_2788_; uint8_t v_isShared_2789_; uint8_t v_isSharedCheck_2793_; 
lean_dec(v_a_2773_);
lean_dec(v_json_2752_);
v_a_2786_ = lean_ctor_get(v___x_2775_, 0);
v_isSharedCheck_2793_ = !lean_is_exclusive(v___x_2775_);
if (v_isSharedCheck_2793_ == 0)
{
v___x_2788_ = v___x_2775_;
v_isShared_2789_ = v_isSharedCheck_2793_;
goto v_resetjp_2787_;
}
else
{
lean_inc(v_a_2786_);
lean_dec(v___x_2775_);
v___x_2788_ = lean_box(0);
v_isShared_2789_ = v_isSharedCheck_2793_;
goto v_resetjp_2787_;
}
v_resetjp_2787_:
{
lean_object* v___x_2791_; 
if (v_isShared_2789_ == 0)
{
lean_ctor_set_tag(v___x_2788_, 0);
v___x_2791_ = v___x_2788_;
goto v_reusejp_2790_;
}
else
{
lean_object* v_reuseFailAlloc_2792_; 
v_reuseFailAlloc_2792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2792_, 0, v_a_2786_);
v___x_2791_ = v_reuseFailAlloc_2792_;
goto v_reusejp_2790_;
}
v_reusejp_2790_:
{
return v___x_2791_;
}
}
}
else
{
lean_object* v_a_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; 
v_a_2794_ = lean_ctor_get(v___x_2775_, 0);
lean_inc(v_a_2794_);
lean_dec_ref_known(v___x_2775_, 1);
v___x_2795_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__0));
lean_inc(v_json_2752_);
v___x_2796_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcConnected_fromJson_spec__0(v_json_2752_, v___x_2795_);
if (lean_obj_tag(v___x_2796_) == 0)
{
lean_object* v_a_2797_; lean_object* v___x_2799_; uint8_t v_isShared_2800_; uint8_t v_isSharedCheck_2806_; 
lean_dec(v_a_2794_);
lean_dec(v_a_2773_);
lean_dec(v_json_2752_);
v_a_2797_ = lean_ctor_get(v___x_2796_, 0);
v_isSharedCheck_2806_ = !lean_is_exclusive(v___x_2796_);
if (v_isSharedCheck_2806_ == 0)
{
v___x_2799_ = v___x_2796_;
v_isShared_2800_ = v_isSharedCheck_2806_;
goto v_resetjp_2798_;
}
else
{
lean_inc(v_a_2797_);
lean_dec(v___x_2796_);
v___x_2799_ = lean_box(0);
v_isShared_2800_ = v_isSharedCheck_2806_;
goto v_resetjp_2798_;
}
v_resetjp_2798_:
{
lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2804_; 
v___x_2801_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__9, &l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__9);
v___x_2802_ = lean_string_append(v___x_2801_, v_a_2797_);
lean_dec(v_a_2797_);
if (v_isShared_2800_ == 0)
{
lean_ctor_set(v___x_2799_, 0, v___x_2802_);
v___x_2804_ = v___x_2799_;
goto v_reusejp_2803_;
}
else
{
lean_object* v_reuseFailAlloc_2805_; 
v_reuseFailAlloc_2805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2805_, 0, v___x_2802_);
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
if (lean_obj_tag(v___x_2796_) == 0)
{
lean_object* v_a_2807_; lean_object* v___x_2809_; uint8_t v_isShared_2810_; uint8_t v_isSharedCheck_2814_; 
lean_dec(v_a_2794_);
lean_dec(v_a_2773_);
lean_dec(v_json_2752_);
v_a_2807_ = lean_ctor_get(v___x_2796_, 0);
v_isSharedCheck_2814_ = !lean_is_exclusive(v___x_2796_);
if (v_isSharedCheck_2814_ == 0)
{
v___x_2809_ = v___x_2796_;
v_isShared_2810_ = v_isSharedCheck_2814_;
goto v_resetjp_2808_;
}
else
{
lean_inc(v_a_2807_);
lean_dec(v___x_2796_);
v___x_2809_ = lean_box(0);
v_isShared_2810_ = v_isSharedCheck_2814_;
goto v_resetjp_2808_;
}
v_resetjp_2808_:
{
lean_object* v___x_2812_; 
if (v_isShared_2810_ == 0)
{
lean_ctor_set_tag(v___x_2809_, 0);
v___x_2812_ = v___x_2809_;
goto v_reusejp_2811_;
}
else
{
lean_object* v_reuseFailAlloc_2813_; 
v_reuseFailAlloc_2813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2813_, 0, v_a_2807_);
v___x_2812_ = v_reuseFailAlloc_2813_;
goto v_reusejp_2811_;
}
v_reusejp_2811_:
{
return v___x_2812_;
}
}
}
else
{
lean_object* v_a_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; 
v_a_2815_ = lean_ctor_get(v___x_2796_, 0);
lean_inc(v_a_2815_);
lean_dec_ref_known(v___x_2796_, 1);
v___x_2816_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__10));
lean_inc(v_json_2752_);
v___x_2817_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcCallParams_fromJson_spec__0(v_json_2752_, v___x_2816_);
if (lean_obj_tag(v___x_2817_) == 0)
{
lean_object* v_a_2818_; lean_object* v___x_2820_; uint8_t v_isShared_2821_; uint8_t v_isSharedCheck_2827_; 
lean_dec(v_a_2815_);
lean_dec(v_a_2794_);
lean_dec(v_a_2773_);
lean_dec(v_json_2752_);
v_a_2818_ = lean_ctor_get(v___x_2817_, 0);
v_isSharedCheck_2827_ = !lean_is_exclusive(v___x_2817_);
if (v_isSharedCheck_2827_ == 0)
{
v___x_2820_ = v___x_2817_;
v_isShared_2821_ = v_isSharedCheck_2827_;
goto v_resetjp_2819_;
}
else
{
lean_inc(v_a_2818_);
lean_dec(v___x_2817_);
v___x_2820_ = lean_box(0);
v_isShared_2821_ = v_isSharedCheck_2827_;
goto v_resetjp_2819_;
}
v_resetjp_2819_:
{
lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2825_; 
v___x_2822_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__14, &l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__14_once, _init_l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__14);
v___x_2823_ = lean_string_append(v___x_2822_, v_a_2818_);
lean_dec(v_a_2818_);
if (v_isShared_2821_ == 0)
{
lean_ctor_set(v___x_2820_, 0, v___x_2823_);
v___x_2825_ = v___x_2820_;
goto v_reusejp_2824_;
}
else
{
lean_object* v_reuseFailAlloc_2826_; 
v_reuseFailAlloc_2826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2826_, 0, v___x_2823_);
v___x_2825_ = v_reuseFailAlloc_2826_;
goto v_reusejp_2824_;
}
v_reusejp_2824_:
{
return v___x_2825_;
}
}
}
else
{
if (lean_obj_tag(v___x_2817_) == 0)
{
lean_object* v_a_2828_; lean_object* v___x_2830_; uint8_t v_isShared_2831_; uint8_t v_isSharedCheck_2835_; 
lean_dec(v_a_2815_);
lean_dec(v_a_2794_);
lean_dec(v_a_2773_);
lean_dec(v_json_2752_);
v_a_2828_ = lean_ctor_get(v___x_2817_, 0);
v_isSharedCheck_2835_ = !lean_is_exclusive(v___x_2817_);
if (v_isSharedCheck_2835_ == 0)
{
v___x_2830_ = v___x_2817_;
v_isShared_2831_ = v_isSharedCheck_2835_;
goto v_resetjp_2829_;
}
else
{
lean_inc(v_a_2828_);
lean_dec(v___x_2817_);
v___x_2830_ = lean_box(0);
v_isShared_2831_ = v_isSharedCheck_2835_;
goto v_resetjp_2829_;
}
v_resetjp_2829_:
{
lean_object* v___x_2833_; 
if (v_isShared_2831_ == 0)
{
lean_ctor_set_tag(v___x_2830_, 0);
v___x_2833_ = v___x_2830_;
goto v_reusejp_2832_;
}
else
{
lean_object* v_reuseFailAlloc_2834_; 
v_reuseFailAlloc_2834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2834_, 0, v_a_2828_);
v___x_2833_ = v_reuseFailAlloc_2834_;
goto v_reusejp_2832_;
}
v_reusejp_2832_:
{
return v___x_2833_;
}
}
}
else
{
lean_object* v_a_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v_a_2839_; lean_object* v___x_2841_; uint8_t v_isShared_2842_; uint8_t v_isSharedCheck_2849_; 
v_a_2836_ = lean_ctor_get(v___x_2817_, 0);
lean_inc(v_a_2836_);
lean_dec_ref_known(v___x_2817_, 1);
v___x_2837_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__15));
v___x_2838_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcCallParams_fromJson_spec__1(v_json_2752_, v___x_2837_);
v_a_2839_ = lean_ctor_get(v___x_2838_, 0);
v_isSharedCheck_2849_ = !lean_is_exclusive(v___x_2838_);
if (v_isSharedCheck_2849_ == 0)
{
v___x_2841_ = v___x_2838_;
v_isShared_2842_ = v_isSharedCheck_2849_;
goto v_resetjp_2840_;
}
else
{
lean_inc(v_a_2839_);
lean_dec(v___x_2838_);
v___x_2841_ = lean_box(0);
v_isShared_2842_ = v_isSharedCheck_2849_;
goto v_resetjp_2840_;
}
v_resetjp_2840_:
{
lean_object* v___x_2843_; lean_object* v___x_2844_; uint64_t v___x_2845_; lean_object* v___x_2847_; 
v___x_2843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2843_, 0, v_a_2773_);
lean_ctor_set(v___x_2843_, 1, v_a_2794_);
v___x_2844_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_2844_, 0, v___x_2843_);
lean_ctor_set(v___x_2844_, 1, v_a_2836_);
lean_ctor_set(v___x_2844_, 2, v_a_2839_);
v___x_2845_ = lean_unbox_uint64(v_a_2815_);
lean_dec(v_a_2815_);
lean_ctor_set_uint64(v___x_2844_, sizeof(void*)*3, v___x_2845_);
if (v_isShared_2842_ == 0)
{
lean_ctor_set(v___x_2841_, 0, v___x_2844_);
v___x_2847_ = v___x_2841_;
goto v_reusejp_2846_;
}
else
{
lean_object* v_reuseFailAlloc_2848_; 
v_reuseFailAlloc_2848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2848_, 0, v___x_2844_);
v___x_2847_ = v_reuseFailAlloc_2848_;
goto v_reusejp_2846_;
}
v_reusejp_2846_:
{
return v___x_2847_;
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
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRpcCallParams_toJson(lean_object* v_x_2852_){
_start:
{
lean_object* v_toTextDocumentPositionParams_2853_; uint64_t v_sessionId_2854_; lean_object* v_method_2855_; lean_object* v_params_2856_; lean_object* v_textDocument_2857_; lean_object* v_position_2858_; lean_object* v___x_2860_; uint8_t v_isShared_2861_; uint8_t v_isSharedCheck_2895_; 
v_toTextDocumentPositionParams_2853_ = lean_ctor_get(v_x_2852_, 0);
lean_inc_ref(v_toTextDocumentPositionParams_2853_);
v_sessionId_2854_ = lean_ctor_get_uint64(v_x_2852_, sizeof(void*)*3);
v_method_2855_ = lean_ctor_get(v_x_2852_, 1);
lean_inc(v_method_2855_);
v_params_2856_ = lean_ctor_get(v_x_2852_, 2);
lean_inc(v_params_2856_);
lean_dec_ref(v_x_2852_);
v_textDocument_2857_ = lean_ctor_get(v_toTextDocumentPositionParams_2853_, 0);
v_position_2858_ = lean_ctor_get(v_toTextDocumentPositionParams_2853_, 1);
v_isSharedCheck_2895_ = !lean_is_exclusive(v_toTextDocumentPositionParams_2853_);
if (v_isSharedCheck_2895_ == 0)
{
v___x_2860_ = v_toTextDocumentPositionParams_2853_;
v_isShared_2861_ = v_isSharedCheck_2895_;
goto v_resetjp_2859_;
}
else
{
lean_inc(v_position_2858_);
lean_inc(v_textDocument_2857_);
lean_dec(v_toTextDocumentPositionParams_2853_);
v___x_2860_ = lean_box(0);
v_isShared_2861_ = v_isSharedCheck_2895_;
goto v_resetjp_2859_;
}
v_resetjp_2859_:
{
lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2865_; 
v___x_2862_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__0));
v___x_2863_ = l_Lean_Lsp_instToJsonTextDocumentIdentifier_toJson(v_textDocument_2857_);
if (v_isShared_2861_ == 0)
{
lean_ctor_set(v___x_2860_, 1, v___x_2863_);
lean_ctor_set(v___x_2860_, 0, v___x_2862_);
v___x_2865_ = v___x_2860_;
goto v_reusejp_2864_;
}
else
{
lean_object* v_reuseFailAlloc_2894_; 
v_reuseFailAlloc_2894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2894_, 0, v___x_2862_);
lean_ctor_set(v_reuseFailAlloc_2894_, 1, v___x_2863_);
v___x_2865_ = v_reuseFailAlloc_2894_;
goto v_reusejp_2864_;
}
v_reusejp_2864_:
{
lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; uint8_t v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; 
v___x_2866_ = lean_box(0);
v___x_2867_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2867_, 0, v___x_2865_);
lean_ctor_set(v___x_2867_, 1, v___x_2866_);
v___x_2868_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPlainGoalParams_fromJson___closed__6));
v___x_2869_ = l_Lean_Lsp_instToJsonPosition_toJson(v_position_2858_);
v___x_2870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2870_, 0, v___x_2868_);
lean_ctor_set(v___x_2870_, 1, v___x_2869_);
v___x_2871_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2871_, 0, v___x_2870_);
lean_ctor_set(v___x_2871_, 1, v___x_2866_);
v___x_2872_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__0));
v___x_2873_ = lean_uint64_to_nat(v_sessionId_2854_);
v___x_2874_ = l_Lean_bignumToJson(v___x_2873_);
v___x_2875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2875_, 0, v___x_2872_);
lean_ctor_set(v___x_2875_, 1, v___x_2874_);
v___x_2876_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2876_, 0, v___x_2875_);
lean_ctor_set(v___x_2876_, 1, v___x_2866_);
v___x_2877_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__10));
v___x_2878_ = 1;
v___x_2879_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_method_2855_, v___x_2878_);
v___x_2880_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2880_, 0, v___x_2879_);
v___x_2881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2881_, 0, v___x_2877_);
lean_ctor_set(v___x_2881_, 1, v___x_2880_);
v___x_2882_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2882_, 0, v___x_2881_);
lean_ctor_set(v___x_2882_, 1, v___x_2866_);
v___x_2883_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcCallParams_fromJson___closed__15));
v___x_2884_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2884_, 0, v___x_2883_);
lean_ctor_set(v___x_2884_, 1, v_params_2856_);
v___x_2885_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2885_, 0, v___x_2884_);
lean_ctor_set(v___x_2885_, 1, v___x_2866_);
v___x_2886_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2886_, 0, v___x_2885_);
lean_ctor_set(v___x_2886_, 1, v___x_2866_);
v___x_2887_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2887_, 0, v___x_2882_);
lean_ctor_set(v___x_2887_, 1, v___x_2886_);
v___x_2888_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2888_, 0, v___x_2876_);
lean_ctor_set(v___x_2888_, 1, v___x_2887_);
v___x_2889_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2889_, 0, v___x_2871_);
lean_ctor_set(v___x_2889_, 1, v___x_2888_);
v___x_2890_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2890_, 0, v___x_2867_);
lean_ctor_set(v___x_2890_, 1, v___x_2889_);
v___x_2891_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0));
v___x_2892_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_2890_, v___x_2891_);
v___x_2893_ = l_Lean_Json_mkObj(v___x_2892_);
lean_dec(v___x_2892_);
return v___x_2893_;
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcReleaseParams_fromJson_spec__0_spec__0_spec__1(size_t v_sz_2898_, size_t v_i_2899_, lean_object* v_bs_2900_){
_start:
{
uint8_t v___x_2901_; 
v___x_2901_ = lean_usize_dec_lt(v_i_2899_, v_sz_2898_);
if (v___x_2901_ == 0)
{
lean_object* v___x_2902_; 
v___x_2902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2902_, 0, v_bs_2900_);
return v___x_2902_;
}
else
{
lean_object* v_v_2903_; lean_object* v___x_2904_; lean_object* v_bs_x27_2905_; size_t v___x_2906_; size_t v___x_2907_; lean_object* v___x_2908_; 
v_v_2903_ = lean_array_uget(v_bs_2900_, v_i_2899_);
v___x_2904_ = lean_unsigned_to_nat(0u);
v_bs_x27_2905_ = lean_array_uset(v_bs_2900_, v_i_2899_, v___x_2904_);
v___x_2906_ = ((size_t)1ULL);
v___x_2907_ = lean_usize_add(v_i_2899_, v___x_2906_);
v___x_2908_ = lean_array_uset(v_bs_x27_2905_, v_i_2899_, v_v_2903_);
v_i_2899_ = v___x_2907_;
v_bs_2900_ = v___x_2908_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcReleaseParams_fromJson_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
size_t v_sz_2898_ = stack[0].m_num;
size_t v_i_2899_ = stack[1].m_num;
lean_object* v_bs_2900_ = stack[2].m_obj;
lean_object* v_res_2910_;
v_res_2910_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcReleaseParams_fromJson_spec__0_spec__0_spec__1(v_sz_2898_, v_i_2899_, v_bs_2900_);
stack->m_obj
 = v_res_2910_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcReleaseParams_fromJson_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_2911_, lean_object* v_i_2912_, lean_object* v_bs_2913_){
_start:
{
size_t v_sz_boxed_2914_; size_t v_i_boxed_2915_; lean_object* v_res_2916_; 
v_sz_boxed_2914_ = lean_unbox_usize(v_sz_2911_);
lean_dec(v_sz_2911_);
v_i_boxed_2915_ = lean_unbox_usize(v_i_2912_);
lean_dec(v_i_2912_);
v_res_2916_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcReleaseParams_fromJson_spec__0_spec__0_spec__1(v_sz_boxed_2914_, v_i_boxed_2915_, v_bs_2913_);
return v_res_2916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcReleaseParams_fromJson_spec__0_spec__0(lean_object* v_x_2917_){
_start:
{
if (lean_obj_tag(v_x_2917_) == 4)
{
lean_object* v_elems_2918_; size_t v_sz_2919_; size_t v___x_2920_; lean_object* v___x_2921_; 
v_elems_2918_ = lean_ctor_get(v_x_2917_, 0);
lean_inc_ref(v_elems_2918_);
lean_dec_ref_known(v_x_2917_, 1);
v_sz_2919_ = lean_array_size(v_elems_2918_);
v___x_2920_ = ((size_t)0ULL);
v___x_2921_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcReleaseParams_fromJson_spec__0_spec__0_spec__1(v_sz_2919_, v___x_2920_, v_elems_2918_);
return v___x_2921_;
}
else
{
lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; 
v___x_2922_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanFileProgressParams_fromJson_spec__1_spec__1___closed__0));
v___x_2923_ = lean_unsigned_to_nat(80u);
v___x_2924_ = l_Lean_Json_pretty(v_x_2917_, v___x_2923_);
v___x_2925_ = lean_string_append(v___x_2922_, v___x_2924_);
lean_dec_ref(v___x_2924_);
v___x_2926_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanFileProgressKind___lam__0___closed__1));
v___x_2927_ = lean_string_append(v___x_2925_, v___x_2926_);
v___x_2928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2928_, 0, v___x_2927_);
return v___x_2928_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcReleaseParams_fromJson_spec__0(lean_object* v_j_2929_, lean_object* v_k_2930_){
_start:
{
lean_object* v___x_2931_; lean_object* v___x_2932_; 
v___x_2931_ = l_Lean_Json_getObjValD(v_j_2929_, v_k_2930_);
v___x_2932_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcReleaseParams_fromJson_spec__0_spec__0(v___x_2931_);
return v___x_2932_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcReleaseParams_fromJson_spec__0___boxed(lean_object* v_j_2933_, lean_object* v_k_2934_){
_start:
{
lean_object* v_res_2935_; 
v_res_2935_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcReleaseParams_fromJson_spec__0(v_j_2933_, v_k_2934_);
lean_dec_ref(v_k_2934_);
return v_res_2935_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__2(void){
_start:
{
uint8_t v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; 
v___x_2941_ = 1;
v___x_2942_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__1));
v___x_2943_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2942_, v___x_2941_);
return v___x_2943_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__3(void){
_start:
{
lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; 
v___x_2944_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6));
v___x_2945_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__2, &l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__2);
v___x_2946_ = lean_string_append(v___x_2945_, v___x_2944_);
return v___x_2946_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; 
v___x_2947_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__6, &l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__6);
v___x_2948_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__3);
v___x_2949_ = lean_string_append(v___x_2948_, v___x_2947_);
return v___x_2949_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__5(void){
_start:
{
lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; 
v___x_2950_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_2951_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__4);
v___x_2952_ = lean_string_append(v___x_2951_, v___x_2950_);
return v___x_2952_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__6(void){
_start:
{
lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; 
v___x_2953_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__6, &l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__6);
v___x_2954_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__3);
v___x_2955_ = lean_string_append(v___x_2954_, v___x_2953_);
return v___x_2955_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__7(void){
_start:
{
lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; 
v___x_2956_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_2957_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__6, &l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__6);
v___x_2958_ = lean_string_append(v___x_2957_, v___x_2956_);
return v___x_2958_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__10(void){
_start:
{
uint8_t v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; 
v___x_2962_ = 1;
v___x_2963_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__9));
v___x_2964_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2963_, v___x_2962_);
return v___x_2964_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__11(void){
_start:
{
lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; 
v___x_2965_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__10, &l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__10);
v___x_2966_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__3);
v___x_2967_ = lean_string_append(v___x_2966_, v___x_2965_);
return v___x_2967_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__12(void){
_start:
{
lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; 
v___x_2968_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_2969_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__11, &l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__11);
v___x_2970_ = lean_string_append(v___x_2969_, v___x_2968_);
return v___x_2970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson(lean_object* v_json_2971_){
_start:
{
lean_object* v___x_2972_; lean_object* v___x_2973_; 
v___x_2972_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__0));
lean_inc(v_json_2971_);
v___x_2973_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson_spec__0(v_json_2971_, v___x_2972_);
if (lean_obj_tag(v___x_2973_) == 0)
{
lean_object* v_a_2974_; lean_object* v___x_2976_; uint8_t v_isShared_2977_; uint8_t v_isSharedCheck_2983_; 
lean_dec(v_json_2971_);
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
v___x_2978_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__5, &l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__5);
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
lean_dec(v_json_2971_);
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
lean_object* v_a_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; 
v_a_2992_ = lean_ctor_get(v___x_2973_, 0);
lean_inc(v_a_2992_);
lean_dec_ref_known(v___x_2973_, 1);
v___x_2993_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__0));
lean_inc(v_json_2971_);
v___x_2994_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcConnected_fromJson_spec__0(v_json_2971_, v___x_2993_);
if (lean_obj_tag(v___x_2994_) == 0)
{
lean_object* v_a_2995_; lean_object* v___x_2997_; uint8_t v_isShared_2998_; uint8_t v_isSharedCheck_3004_; 
lean_dec(v_a_2992_);
lean_dec(v_json_2971_);
v_a_2995_ = lean_ctor_get(v___x_2994_, 0);
v_isSharedCheck_3004_ = !lean_is_exclusive(v___x_2994_);
if (v_isSharedCheck_3004_ == 0)
{
v___x_2997_ = v___x_2994_;
v_isShared_2998_ = v_isSharedCheck_3004_;
goto v_resetjp_2996_;
}
else
{
lean_inc(v_a_2995_);
lean_dec(v___x_2994_);
v___x_2997_ = lean_box(0);
v_isShared_2998_ = v_isSharedCheck_3004_;
goto v_resetjp_2996_;
}
v_resetjp_2996_:
{
lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3002_; 
v___x_2999_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__7);
v___x_3000_ = lean_string_append(v___x_2999_, v_a_2995_);
lean_dec(v_a_2995_);
if (v_isShared_2998_ == 0)
{
lean_ctor_set(v___x_2997_, 0, v___x_3000_);
v___x_3002_ = v___x_2997_;
goto v_reusejp_3001_;
}
else
{
lean_object* v_reuseFailAlloc_3003_; 
v_reuseFailAlloc_3003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3003_, 0, v___x_3000_);
v___x_3002_ = v_reuseFailAlloc_3003_;
goto v_reusejp_3001_;
}
v_reusejp_3001_:
{
return v___x_3002_;
}
}
}
else
{
if (lean_obj_tag(v___x_2994_) == 0)
{
lean_object* v_a_3005_; lean_object* v___x_3007_; uint8_t v_isShared_3008_; uint8_t v_isSharedCheck_3012_; 
lean_dec(v_a_2992_);
lean_dec(v_json_2971_);
v_a_3005_ = lean_ctor_get(v___x_2994_, 0);
v_isSharedCheck_3012_ = !lean_is_exclusive(v___x_2994_);
if (v_isSharedCheck_3012_ == 0)
{
v___x_3007_ = v___x_2994_;
v_isShared_3008_ = v_isSharedCheck_3012_;
goto v_resetjp_3006_;
}
else
{
lean_inc(v_a_3005_);
lean_dec(v___x_2994_);
v___x_3007_ = lean_box(0);
v_isShared_3008_ = v_isSharedCheck_3012_;
goto v_resetjp_3006_;
}
v_resetjp_3006_:
{
lean_object* v___x_3010_; 
if (v_isShared_3008_ == 0)
{
lean_ctor_set_tag(v___x_3007_, 0);
v___x_3010_ = v___x_3007_;
goto v_reusejp_3009_;
}
else
{
lean_object* v_reuseFailAlloc_3011_; 
v_reuseFailAlloc_3011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3011_, 0, v_a_3005_);
v___x_3010_ = v_reuseFailAlloc_3011_;
goto v_reusejp_3009_;
}
v_reusejp_3009_:
{
return v___x_3010_;
}
}
}
else
{
lean_object* v_a_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; 
v_a_3013_ = lean_ctor_get(v___x_2994_, 0);
lean_inc(v_a_3013_);
lean_dec_ref_known(v___x_2994_, 1);
v___x_3014_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__8));
v___x_3015_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcReleaseParams_fromJson_spec__0(v_json_2971_, v___x_3014_);
if (lean_obj_tag(v___x_3015_) == 0)
{
lean_object* v_a_3016_; lean_object* v___x_3018_; uint8_t v_isShared_3019_; uint8_t v_isSharedCheck_3025_; 
lean_dec(v_a_3013_);
lean_dec(v_a_2992_);
v_a_3016_ = lean_ctor_get(v___x_3015_, 0);
v_isSharedCheck_3025_ = !lean_is_exclusive(v___x_3015_);
if (v_isSharedCheck_3025_ == 0)
{
v___x_3018_ = v___x_3015_;
v_isShared_3019_ = v_isSharedCheck_3025_;
goto v_resetjp_3017_;
}
else
{
lean_inc(v_a_3016_);
lean_dec(v___x_3015_);
v___x_3018_ = lean_box(0);
v_isShared_3019_ = v_isSharedCheck_3025_;
goto v_resetjp_3017_;
}
v_resetjp_3017_:
{
lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3023_; 
v___x_3020_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__12, &l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__12);
v___x_3021_ = lean_string_append(v___x_3020_, v_a_3016_);
lean_dec(v_a_3016_);
if (v_isShared_3019_ == 0)
{
lean_ctor_set(v___x_3018_, 0, v___x_3021_);
v___x_3023_ = v___x_3018_;
goto v_reusejp_3022_;
}
else
{
lean_object* v_reuseFailAlloc_3024_; 
v_reuseFailAlloc_3024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3024_, 0, v___x_3021_);
v___x_3023_ = v_reuseFailAlloc_3024_;
goto v_reusejp_3022_;
}
v_reusejp_3022_:
{
return v___x_3023_;
}
}
}
else
{
if (lean_obj_tag(v___x_3015_) == 0)
{
lean_object* v_a_3026_; lean_object* v___x_3028_; uint8_t v_isShared_3029_; uint8_t v_isSharedCheck_3033_; 
lean_dec(v_a_3013_);
lean_dec(v_a_2992_);
v_a_3026_ = lean_ctor_get(v___x_3015_, 0);
v_isSharedCheck_3033_ = !lean_is_exclusive(v___x_3015_);
if (v_isSharedCheck_3033_ == 0)
{
v___x_3028_ = v___x_3015_;
v_isShared_3029_ = v_isSharedCheck_3033_;
goto v_resetjp_3027_;
}
else
{
lean_inc(v_a_3026_);
lean_dec(v___x_3015_);
v___x_3028_ = lean_box(0);
v_isShared_3029_ = v_isSharedCheck_3033_;
goto v_resetjp_3027_;
}
v_resetjp_3027_:
{
lean_object* v___x_3031_; 
if (v_isShared_3029_ == 0)
{
lean_ctor_set_tag(v___x_3028_, 0);
v___x_3031_ = v___x_3028_;
goto v_reusejp_3030_;
}
else
{
lean_object* v_reuseFailAlloc_3032_; 
v_reuseFailAlloc_3032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3032_, 0, v_a_3026_);
v___x_3031_ = v_reuseFailAlloc_3032_;
goto v_reusejp_3030_;
}
v_reusejp_3030_:
{
return v___x_3031_;
}
}
}
else
{
lean_object* v_a_3034_; lean_object* v___x_3036_; uint8_t v_isShared_3037_; uint8_t v_isSharedCheck_3043_; 
v_a_3034_ = lean_ctor_get(v___x_3015_, 0);
v_isSharedCheck_3043_ = !lean_is_exclusive(v___x_3015_);
if (v_isSharedCheck_3043_ == 0)
{
v___x_3036_ = v___x_3015_;
v_isShared_3037_ = v_isSharedCheck_3043_;
goto v_resetjp_3035_;
}
else
{
lean_inc(v_a_3034_);
lean_dec(v___x_3015_);
v___x_3036_ = lean_box(0);
v_isShared_3037_ = v_isSharedCheck_3043_;
goto v_resetjp_3035_;
}
v_resetjp_3035_:
{
lean_object* v___x_3038_; uint64_t v___x_3039_; lean_object* v___x_3041_; 
v___x_3038_ = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(v___x_3038_, 0, v_a_2992_);
lean_ctor_set(v___x_3038_, 1, v_a_3034_);
v___x_3039_ = lean_unbox_uint64(v_a_3013_);
lean_dec(v_a_3013_);
lean_ctor_set_uint64(v___x_3038_, sizeof(void*)*2, v___x_3039_);
if (v_isShared_3037_ == 0)
{
lean_ctor_set(v___x_3036_, 0, v___x_3038_);
v___x_3041_ = v___x_3036_;
goto v_reusejp_3040_;
}
else
{
lean_object* v_reuseFailAlloc_3042_; 
v_reuseFailAlloc_3042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3042_, 0, v___x_3038_);
v___x_3041_ = v_reuseFailAlloc_3042_;
goto v_reusejp_3040_;
}
v_reusejp_3040_:
{
return v___x_3041_;
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
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonRpcReleaseParams_toJson_spec__0_spec__0(size_t v_sz_3046_, size_t v_i_3047_, lean_object* v_bs_3048_){
_start:
{
uint8_t v___x_3049_; 
v___x_3049_ = lean_usize_dec_lt(v_i_3047_, v_sz_3046_);
if (v___x_3049_ == 0)
{
return v_bs_3048_;
}
else
{
lean_object* v_v_3050_; lean_object* v___x_3051_; lean_object* v_bs_x27_3052_; size_t v___x_3053_; size_t v___x_3054_; lean_object* v___x_3055_; 
v_v_3050_ = lean_array_uget(v_bs_3048_, v_i_3047_);
v___x_3051_ = lean_unsigned_to_nat(0u);
v_bs_x27_3052_ = lean_array_uset(v_bs_3048_, v_i_3047_, v___x_3051_);
v___x_3053_ = ((size_t)1ULL);
v___x_3054_ = lean_usize_add(v_i_3047_, v___x_3053_);
v___x_3055_ = lean_array_uset(v_bs_x27_3052_, v_i_3047_, v_v_3050_);
v_i_3047_ = v___x_3054_;
v_bs_3048_ = v___x_3055_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonRpcReleaseParams_toJson_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_3046_ = stack[0].m_num;
size_t v_i_3047_ = stack[1].m_num;
lean_object* v_bs_3048_ = stack[2].m_obj;
lean_object* v_res_3057_;
v_res_3057_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonRpcReleaseParams_toJson_spec__0_spec__0(v_sz_3046_, v_i_3047_, v_bs_3048_);
stack->m_obj
 = v_res_3057_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonRpcReleaseParams_toJson_spec__0_spec__0___boxed(lean_object* v_sz_3058_, lean_object* v_i_3059_, lean_object* v_bs_3060_){
_start:
{
size_t v_sz_boxed_3061_; size_t v_i_boxed_3062_; lean_object* v_res_3063_; 
v_sz_boxed_3061_ = lean_unbox_usize(v_sz_3058_);
lean_dec(v_sz_3058_);
v_i_boxed_3062_ = lean_unbox_usize(v_i_3059_);
lean_dec(v_i_3059_);
v_res_3063_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonRpcReleaseParams_toJson_spec__0_spec__0(v_sz_boxed_3061_, v_i_boxed_3062_, v_bs_3060_);
return v_res_3063_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonRpcReleaseParams_toJson_spec__0(lean_object* v_a_3064_){
_start:
{
size_t v_sz_3065_; size_t v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; 
v_sz_3065_ = lean_array_size(v_a_3064_);
v___x_3066_ = ((size_t)0ULL);
v___x_3067_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonRpcReleaseParams_toJson_spec__0_spec__0(v_sz_3065_, v___x_3066_, v_a_3064_);
v___x_3068_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3068_, 0, v___x_3067_);
return v___x_3068_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRpcReleaseParams_toJson(lean_object* v_x_3069_){
_start:
{
lean_object* v_uri_3070_; uint64_t v_sessionId_3071_; lean_object* v_refs_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; 
v_uri_3070_ = lean_ctor_get(v_x_3069_, 0);
lean_inc_ref(v_uri_3070_);
v_sessionId_3071_ = lean_ctor_get_uint64(v_x_3069_, sizeof(void*)*2);
v_refs_3072_ = lean_ctor_get(v_x_3069_, 1);
lean_inc_ref(v_refs_3072_);
lean_dec_ref(v_x_3069_);
v___x_3073_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__0));
v___x_3074_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3074_, 0, v_uri_3070_);
v___x_3075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3075_, 0, v___x_3073_);
lean_ctor_set(v___x_3075_, 1, v___x_3074_);
v___x_3076_ = lean_box(0);
v___x_3077_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3077_, 0, v___x_3075_);
lean_ctor_set(v___x_3077_, 1, v___x_3076_);
v___x_3078_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__0));
v___x_3079_ = lean_uint64_to_nat(v_sessionId_3071_);
v___x_3080_ = l_Lean_bignumToJson(v___x_3079_);
v___x_3081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3081_, 0, v___x_3078_);
lean_ctor_set(v___x_3081_, 1, v___x_3080_);
v___x_3082_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3082_, 0, v___x_3081_);
lean_ctor_set(v___x_3082_, 1, v___x_3076_);
v___x_3083_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcReleaseParams_fromJson___closed__8));
v___x_3084_ = l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonRpcReleaseParams_toJson_spec__0(v_refs_3072_);
v___x_3085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3085_, 0, v___x_3083_);
lean_ctor_set(v___x_3085_, 1, v___x_3084_);
v___x_3086_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3086_, 0, v___x_3085_);
lean_ctor_set(v___x_3086_, 1, v___x_3076_);
v___x_3087_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3087_, 0, v___x_3086_);
lean_ctor_set(v___x_3087_, 1, v___x_3076_);
v___x_3088_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3088_, 0, v___x_3082_);
lean_ctor_set(v___x_3088_, 1, v___x_3087_);
v___x_3089_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3089_, 0, v___x_3077_);
lean_ctor_set(v___x_3089_, 1, v___x_3088_);
v___x_3090_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0));
v___x_3091_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_3089_, v___x_3090_);
v___x_3092_ = l_Lean_Json_mkObj(v___x_3091_);
lean_dec(v___x_3091_);
return v___x_3092_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__2(void){
_start:
{
uint8_t v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; 
v___x_3100_ = 1;
v___x_3101_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__1));
v___x_3102_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3101_, v___x_3100_);
return v___x_3102_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__3(void){
_start:
{
lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; 
v___x_3103_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6));
v___x_3104_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__2, &l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__2);
v___x_3105_ = lean_string_append(v___x_3104_, v___x_3103_);
return v___x_3105_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; 
v___x_3106_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__6, &l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__6);
v___x_3107_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__3);
v___x_3108_ = lean_string_append(v___x_3107_, v___x_3106_);
return v___x_3108_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__5(void){
_start:
{
lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; 
v___x_3109_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_3110_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__4);
v___x_3111_ = lean_string_append(v___x_3110_, v___x_3109_);
return v___x_3111_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__6(void){
_start:
{
lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; 
v___x_3112_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__6, &l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__6);
v___x_3113_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__3);
v___x_3114_ = lean_string_append(v___x_3113_, v___x_3112_);
return v___x_3114_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__7(void){
_start:
{
lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; 
v___x_3115_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_3116_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__6, &l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__6);
v___x_3117_ = lean_string_append(v___x_3116_, v___x_3115_);
return v___x_3117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson(lean_object* v_json_3118_){
_start:
{
lean_object* v___x_3119_; lean_object* v___x_3120_; 
v___x_3119_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__0));
lean_inc(v_json_3118_);
v___x_3120_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson_spec__0(v_json_3118_, v___x_3119_);
if (lean_obj_tag(v___x_3120_) == 0)
{
lean_object* v_a_3121_; lean_object* v___x_3123_; uint8_t v_isShared_3124_; uint8_t v_isSharedCheck_3130_; 
lean_dec(v_json_3118_);
v_a_3121_ = lean_ctor_get(v___x_3120_, 0);
v_isSharedCheck_3130_ = !lean_is_exclusive(v___x_3120_);
if (v_isSharedCheck_3130_ == 0)
{
v___x_3123_ = v___x_3120_;
v_isShared_3124_ = v_isSharedCheck_3130_;
goto v_resetjp_3122_;
}
else
{
lean_inc(v_a_3121_);
lean_dec(v___x_3120_);
v___x_3123_ = lean_box(0);
v_isShared_3124_ = v_isSharedCheck_3130_;
goto v_resetjp_3122_;
}
v_resetjp_3122_:
{
lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3128_; 
v___x_3125_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__5, &l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__5);
v___x_3126_ = lean_string_append(v___x_3125_, v_a_3121_);
lean_dec(v_a_3121_);
if (v_isShared_3124_ == 0)
{
lean_ctor_set(v___x_3123_, 0, v___x_3126_);
v___x_3128_ = v___x_3123_;
goto v_reusejp_3127_;
}
else
{
lean_object* v_reuseFailAlloc_3129_; 
v_reuseFailAlloc_3129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3129_, 0, v___x_3126_);
v___x_3128_ = v_reuseFailAlloc_3129_;
goto v_reusejp_3127_;
}
v_reusejp_3127_:
{
return v___x_3128_;
}
}
}
else
{
if (lean_obj_tag(v___x_3120_) == 0)
{
lean_object* v_a_3131_; lean_object* v___x_3133_; uint8_t v_isShared_3134_; uint8_t v_isSharedCheck_3138_; 
lean_dec(v_json_3118_);
v_a_3131_ = lean_ctor_get(v___x_3120_, 0);
v_isSharedCheck_3138_ = !lean_is_exclusive(v___x_3120_);
if (v_isSharedCheck_3138_ == 0)
{
v___x_3133_ = v___x_3120_;
v_isShared_3134_ = v_isSharedCheck_3138_;
goto v_resetjp_3132_;
}
else
{
lean_inc(v_a_3131_);
lean_dec(v___x_3120_);
v___x_3133_ = lean_box(0);
v_isShared_3134_ = v_isSharedCheck_3138_;
goto v_resetjp_3132_;
}
v_resetjp_3132_:
{
lean_object* v___x_3136_; 
if (v_isShared_3134_ == 0)
{
lean_ctor_set_tag(v___x_3133_, 0);
v___x_3136_ = v___x_3133_;
goto v_reusejp_3135_;
}
else
{
lean_object* v_reuseFailAlloc_3137_; 
v_reuseFailAlloc_3137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3137_, 0, v_a_3131_);
v___x_3136_ = v_reuseFailAlloc_3137_;
goto v_reusejp_3135_;
}
v_reusejp_3135_:
{
return v___x_3136_;
}
}
}
else
{
lean_object* v_a_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; 
v_a_3139_ = lean_ctor_get(v___x_3120_, 0);
lean_inc(v_a_3139_);
lean_dec_ref_known(v___x_3120_, 1);
v___x_3140_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__0));
v___x_3141_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRpcConnected_fromJson_spec__0(v_json_3118_, v___x_3140_);
if (lean_obj_tag(v___x_3141_) == 0)
{
lean_object* v_a_3142_; lean_object* v___x_3144_; uint8_t v_isShared_3145_; uint8_t v_isSharedCheck_3151_; 
lean_dec(v_a_3139_);
v_a_3142_ = lean_ctor_get(v___x_3141_, 0);
v_isSharedCheck_3151_ = !lean_is_exclusive(v___x_3141_);
if (v_isSharedCheck_3151_ == 0)
{
v___x_3144_ = v___x_3141_;
v_isShared_3145_ = v_isSharedCheck_3151_;
goto v_resetjp_3143_;
}
else
{
lean_inc(v_a_3142_);
lean_dec(v___x_3141_);
v___x_3144_ = lean_box(0);
v_isShared_3145_ = v_isSharedCheck_3151_;
goto v_resetjp_3143_;
}
v_resetjp_3143_:
{
lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3149_; 
v___x_3146_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonRpcKeepAliveParams_fromJson___closed__7);
v___x_3147_ = lean_string_append(v___x_3146_, v_a_3142_);
lean_dec(v_a_3142_);
if (v_isShared_3145_ == 0)
{
lean_ctor_set(v___x_3144_, 0, v___x_3147_);
v___x_3149_ = v___x_3144_;
goto v_reusejp_3148_;
}
else
{
lean_object* v_reuseFailAlloc_3150_; 
v_reuseFailAlloc_3150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3150_, 0, v___x_3147_);
v___x_3149_ = v_reuseFailAlloc_3150_;
goto v_reusejp_3148_;
}
v_reusejp_3148_:
{
return v___x_3149_;
}
}
}
else
{
if (lean_obj_tag(v___x_3141_) == 0)
{
lean_object* v_a_3152_; lean_object* v___x_3154_; uint8_t v_isShared_3155_; uint8_t v_isSharedCheck_3159_; 
lean_dec(v_a_3139_);
v_a_3152_ = lean_ctor_get(v___x_3141_, 0);
v_isSharedCheck_3159_ = !lean_is_exclusive(v___x_3141_);
if (v_isSharedCheck_3159_ == 0)
{
v___x_3154_ = v___x_3141_;
v_isShared_3155_ = v_isSharedCheck_3159_;
goto v_resetjp_3153_;
}
else
{
lean_inc(v_a_3152_);
lean_dec(v___x_3141_);
v___x_3154_ = lean_box(0);
v_isShared_3155_ = v_isSharedCheck_3159_;
goto v_resetjp_3153_;
}
v_resetjp_3153_:
{
lean_object* v___x_3157_; 
if (v_isShared_3155_ == 0)
{
lean_ctor_set_tag(v___x_3154_, 0);
v___x_3157_ = v___x_3154_;
goto v_reusejp_3156_;
}
else
{
lean_object* v_reuseFailAlloc_3158_; 
v_reuseFailAlloc_3158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3158_, 0, v_a_3152_);
v___x_3157_ = v_reuseFailAlloc_3158_;
goto v_reusejp_3156_;
}
v_reusejp_3156_:
{
return v___x_3157_;
}
}
}
else
{
lean_object* v_a_3160_; lean_object* v___x_3162_; uint8_t v_isShared_3163_; uint8_t v_isSharedCheck_3169_; 
v_a_3160_ = lean_ctor_get(v___x_3141_, 0);
v_isSharedCheck_3169_ = !lean_is_exclusive(v___x_3141_);
if (v_isSharedCheck_3169_ == 0)
{
v___x_3162_ = v___x_3141_;
v_isShared_3163_ = v_isSharedCheck_3169_;
goto v_resetjp_3161_;
}
else
{
lean_inc(v_a_3160_);
lean_dec(v___x_3141_);
v___x_3162_ = lean_box(0);
v_isShared_3163_ = v_isSharedCheck_3169_;
goto v_resetjp_3161_;
}
v_resetjp_3161_:
{
lean_object* v___x_3164_; uint64_t v___x_3165_; lean_object* v___x_3167_; 
v___x_3164_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3164_, 0, v_a_3139_);
v___x_3165_ = lean_unbox_uint64(v_a_3160_);
lean_dec(v_a_3160_);
lean_ctor_set_uint64(v___x_3164_, sizeof(void*)*1, v___x_3165_);
if (v_isShared_3163_ == 0)
{
lean_ctor_set(v___x_3162_, 0, v___x_3164_);
v___x_3167_ = v___x_3162_;
goto v_reusejp_3166_;
}
else
{
lean_object* v_reuseFailAlloc_3168_; 
v_reuseFailAlloc_3168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3168_, 0, v___x_3164_);
v___x_3167_ = v_reuseFailAlloc_3168_;
goto v_reusejp_3166_;
}
v_reusejp_3166_:
{
return v___x_3167_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRpcKeepAliveParams_toJson(lean_object* v_x_3172_){
_start:
{
lean_object* v_uri_3173_; uint64_t v_sessionId_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; 
v_uri_3173_ = lean_ctor_get(v_x_3172_, 0);
v_sessionId_3174_ = lean_ctor_get_uint64(v_x_3172_, sizeof(void*)*1);
v___x_3175_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson___closed__0));
lean_inc_ref(v_uri_3173_);
v___x_3176_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3176_, 0, v_uri_3173_);
v___x_3177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3177_, 0, v___x_3175_);
lean_ctor_set(v___x_3177_, 1, v___x_3176_);
v___x_3178_ = lean_box(0);
v___x_3179_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3179_, 0, v___x_3177_);
lean_ctor_set(v___x_3179_, 1, v___x_3178_);
v___x_3180_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcConnected_fromJson___closed__0));
v___x_3181_ = lean_uint64_to_nat(v_sessionId_3174_);
v___x_3182_ = l_Lean_bignumToJson(v___x_3181_);
v___x_3183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3183_, 0, v___x_3180_);
lean_ctor_set(v___x_3183_, 1, v___x_3182_);
v___x_3184_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3184_, 0, v___x_3183_);
lean_ctor_set(v___x_3184_, 1, v___x_3178_);
v___x_3185_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3185_, 0, v___x_3184_);
lean_ctor_set(v___x_3185_, 1, v___x_3178_);
v___x_3186_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3186_, 0, v___x_3179_);
lean_ctor_set(v___x_3186_, 1, v___x_3185_);
v___x_3187_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0));
v___x_3188_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_3186_, v___x_3187_);
v___x_3189_ = l_Lean_Json_mkObj(v___x_3188_);
lean_dec(v___x_3188_);
return v___x_3189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRpcKeepAliveParams_toJson___boxed(lean_object* v_x_3190_){
_start:
{
lean_object* v_res_3191_; 
v_res_3191_ = l_Lean_Lsp_instToJsonRpcKeepAliveParams_toJson(v_x_3190_);
lean_dec_ref(v_x_3190_);
return v_res_3191_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Lsp_instReprLineRange_repr_spec__0(lean_object* v_a_3198_){
_start:
{
lean_object* v___x_3199_; 
v___x_3199_ = lean_nat_to_int(v_a_3198_);
return v___x_3199_;
}
}
static lean_object* _init_l_Lean_Lsp_instReprLineRange_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_3213_; lean_object* v___x_3214_; 
v___x_3213_ = lean_unsigned_to_nat(9u);
v___x_3214_ = lean_nat_to_int(v___x_3213_);
return v___x_3214_;
}
}
static lean_object* _init_l_Lean_Lsp_instReprLineRange_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_3221_; lean_object* v___x_3222_; 
v___x_3221_ = lean_unsigned_to_nat(7u);
v___x_3222_ = lean_nat_to_int(v___x_3221_);
return v___x_3222_;
}
}
static lean_object* _init_l_Lean_Lsp_instReprLineRange_repr___redArg___closed__14(void){
_start:
{
lean_object* v___x_3224_; lean_object* v___x_3225_; 
v___x_3224_ = ((lean_object*)(l_Lean_Lsp_instReprLineRange_repr___redArg___closed__0));
v___x_3225_ = lean_string_length(v___x_3224_);
return v___x_3225_;
}
}
static lean_object* _init_l_Lean_Lsp_instReprLineRange_repr___redArg___closed__15(void){
_start:
{
lean_object* v___x_3226_; lean_object* v___x_3227_; 
v___x_3226_ = lean_obj_once(&l_Lean_Lsp_instReprLineRange_repr___redArg___closed__14, &l_Lean_Lsp_instReprLineRange_repr___redArg___closed__14_once, _init_l_Lean_Lsp_instReprLineRange_repr___redArg___closed__14);
v___x_3227_ = lean_nat_to_int(v___x_3226_);
return v___x_3227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instReprLineRange_repr___redArg(lean_object* v_x_3232_){
_start:
{
lean_object* v_start_3233_; lean_object* v_end_3234_; lean_object* v___x_3236_; uint8_t v_isShared_3237_; uint8_t v_isSharedCheck_3269_; 
v_start_3233_ = lean_ctor_get(v_x_3232_, 0);
v_end_3234_ = lean_ctor_get(v_x_3232_, 1);
v_isSharedCheck_3269_ = !lean_is_exclusive(v_x_3232_);
if (v_isSharedCheck_3269_ == 0)
{
v___x_3236_ = v_x_3232_;
v_isShared_3237_ = v_isSharedCheck_3269_;
goto v_resetjp_3235_;
}
else
{
lean_inc(v_end_3234_);
lean_inc(v_start_3233_);
lean_dec(v_x_3232_);
v___x_3236_ = lean_box(0);
v_isShared_3237_ = v_isSharedCheck_3269_;
goto v_resetjp_3235_;
}
v_resetjp_3235_:
{
lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3244_; 
v___x_3238_ = ((lean_object*)(l_Lean_Lsp_instReprLineRange_repr___redArg___closed__5));
v___x_3239_ = ((lean_object*)(l_Lean_Lsp_instReprLineRange_repr___redArg___closed__6));
v___x_3240_ = lean_obj_once(&l_Lean_Lsp_instReprLineRange_repr___redArg___closed__7, &l_Lean_Lsp_instReprLineRange_repr___redArg___closed__7_once, _init_l_Lean_Lsp_instReprLineRange_repr___redArg___closed__7);
v___x_3241_ = l_Nat_reprFast(v_start_3233_);
v___x_3242_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3242_, 0, v___x_3241_);
if (v_isShared_3237_ == 0)
{
lean_ctor_set_tag(v___x_3236_, 4);
lean_ctor_set(v___x_3236_, 1, v___x_3242_);
lean_ctor_set(v___x_3236_, 0, v___x_3240_);
v___x_3244_ = v___x_3236_;
goto v_reusejp_3243_;
}
else
{
lean_object* v_reuseFailAlloc_3268_; 
v_reuseFailAlloc_3268_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3268_, 0, v___x_3240_);
lean_ctor_set(v_reuseFailAlloc_3268_, 1, v___x_3242_);
v___x_3244_ = v_reuseFailAlloc_3268_;
goto v_reusejp_3243_;
}
v_reusejp_3243_:
{
uint8_t v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; 
v___x_3245_ = 0;
v___x_3246_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3246_, 0, v___x_3244_);
lean_ctor_set_uint8(v___x_3246_, sizeof(void*)*1, v___x_3245_);
v___x_3247_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3247_, 0, v___x_3239_);
lean_ctor_set(v___x_3247_, 1, v___x_3246_);
v___x_3248_ = ((lean_object*)(l_Lean_Lsp_instReprLineRange_repr___redArg___closed__9));
v___x_3249_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3249_, 0, v___x_3247_);
lean_ctor_set(v___x_3249_, 1, v___x_3248_);
v___x_3250_ = lean_box(1);
v___x_3251_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3251_, 0, v___x_3249_);
lean_ctor_set(v___x_3251_, 1, v___x_3250_);
v___x_3252_ = ((lean_object*)(l_Lean_Lsp_instReprLineRange_repr___redArg___closed__11));
v___x_3253_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3253_, 0, v___x_3251_);
lean_ctor_set(v___x_3253_, 1, v___x_3252_);
v___x_3254_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3254_, 0, v___x_3253_);
lean_ctor_set(v___x_3254_, 1, v___x_3238_);
v___x_3255_ = lean_obj_once(&l_Lean_Lsp_instReprLineRange_repr___redArg___closed__12, &l_Lean_Lsp_instReprLineRange_repr___redArg___closed__12_once, _init_l_Lean_Lsp_instReprLineRange_repr___redArg___closed__12);
v___x_3256_ = l_Nat_reprFast(v_end_3234_);
v___x_3257_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3257_, 0, v___x_3256_);
v___x_3258_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3258_, 0, v___x_3255_);
lean_ctor_set(v___x_3258_, 1, v___x_3257_);
v___x_3259_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3259_, 0, v___x_3258_);
lean_ctor_set_uint8(v___x_3259_, sizeof(void*)*1, v___x_3245_);
v___x_3260_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3260_, 0, v___x_3254_);
lean_ctor_set(v___x_3260_, 1, v___x_3259_);
v___x_3261_ = lean_obj_once(&l_Lean_Lsp_instReprLineRange_repr___redArg___closed__15, &l_Lean_Lsp_instReprLineRange_repr___redArg___closed__15_once, _init_l_Lean_Lsp_instReprLineRange_repr___redArg___closed__15);
v___x_3262_ = ((lean_object*)(l_Lean_Lsp_instReprLineRange_repr___redArg___closed__16));
v___x_3263_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3263_, 0, v___x_3262_);
lean_ctor_set(v___x_3263_, 1, v___x_3260_);
v___x_3264_ = ((lean_object*)(l_Lean_Lsp_instReprLineRange_repr___redArg___closed__17));
v___x_3265_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3265_, 0, v___x_3263_);
lean_ctor_set(v___x_3265_, 1, v___x_3264_);
v___x_3266_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3266_, 0, v___x_3261_);
lean_ctor_set(v___x_3266_, 1, v___x_3265_);
v___x_3267_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3267_, 0, v___x_3266_);
lean_ctor_set_uint8(v___x_3267_, sizeof(void*)*1, v___x_3245_);
return v___x_3267_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instReprLineRange_repr(lean_object* v_x_3270_, lean_object* v_prec_3271_){
_start:
{
lean_object* v___x_3272_; 
v___x_3272_ = l_Lean_Lsp_instReprLineRange_repr___redArg(v_x_3270_);
return v___x_3272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instReprLineRange_repr___boxed(lean_object* v_x_3273_, lean_object* v_prec_3274_){
_start:
{
lean_object* v_res_3275_; 
v_res_3275_ = l_Lean_Lsp_instReprLineRange_repr(v_x_3273_, v_prec_3274_);
lean_dec(v_prec_3274_);
return v_res_3275_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__2(void){
_start:
{
uint8_t v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; 
v___x_3283_ = 1;
v___x_3284_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__1));
v___x_3285_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3284_, v___x_3283_);
return v___x_3285_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__3(void){
_start:
{
lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; 
v___x_3286_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__6));
v___x_3287_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__2, &l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__2);
v___x_3288_ = lean_string_append(v___x_3287_, v___x_3286_);
return v___x_3288_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__5(void){
_start:
{
uint8_t v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; 
v___x_3291_ = 1;
v___x_3292_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__4));
v___x_3293_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3292_, v___x_3291_);
return v___x_3293_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__6(void){
_start:
{
lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; 
v___x_3294_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__5, &l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__5);
v___x_3295_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__3);
v___x_3296_ = lean_string_append(v___x_3295_, v___x_3294_);
return v___x_3296_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__7(void){
_start:
{
lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; 
v___x_3297_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_3298_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__6);
v___x_3299_ = lean_string_append(v___x_3298_, v___x_3297_);
return v___x_3299_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__9(void){
_start:
{
uint8_t v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; 
v___x_3302_ = 1;
v___x_3303_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__8));
v___x_3304_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3303_, v___x_3302_);
return v___x_3304_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__10(void){
_start:
{
lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; 
v___x_3305_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__9, &l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__9);
v___x_3306_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__3);
v___x_3307_ = lean_string_append(v___x_3306_, v___x_3305_);
return v___x_3307_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__11(void){
_start:
{
lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; 
v___x_3308_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDidOpenTextDocumentParams_fromJson___closed__11));
v___x_3309_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__10, &l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__10);
v___x_3310_ = lean_string_append(v___x_3309_, v___x_3308_);
return v___x_3310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLineRange_fromJson(lean_object* v_json_3311_){
_start:
{
lean_object* v___x_3312_; lean_object* v___x_3313_; 
v___x_3312_ = ((lean_object*)(l_Lean_Lsp_instReprLineRange_repr___redArg___closed__1));
lean_inc(v_json_3311_);
v___x_3313_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson_spec__1(v_json_3311_, v___x_3312_);
if (lean_obj_tag(v___x_3313_) == 0)
{
lean_object* v_a_3314_; lean_object* v___x_3316_; uint8_t v_isShared_3317_; uint8_t v_isSharedCheck_3323_; 
lean_dec(v_json_3311_);
v_a_3314_ = lean_ctor_get(v___x_3313_, 0);
v_isSharedCheck_3323_ = !lean_is_exclusive(v___x_3313_);
if (v_isSharedCheck_3323_ == 0)
{
v___x_3316_ = v___x_3313_;
v_isShared_3317_ = v_isSharedCheck_3323_;
goto v_resetjp_3315_;
}
else
{
lean_inc(v_a_3314_);
lean_dec(v___x_3313_);
v___x_3316_ = lean_box(0);
v_isShared_3317_ = v_isSharedCheck_3323_;
goto v_resetjp_3315_;
}
v_resetjp_3315_:
{
lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3321_; 
v___x_3318_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__7);
v___x_3319_ = lean_string_append(v___x_3318_, v_a_3314_);
lean_dec(v_a_3314_);
if (v_isShared_3317_ == 0)
{
lean_ctor_set(v___x_3316_, 0, v___x_3319_);
v___x_3321_ = v___x_3316_;
goto v_reusejp_3320_;
}
else
{
lean_object* v_reuseFailAlloc_3322_; 
v_reuseFailAlloc_3322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3322_, 0, v___x_3319_);
v___x_3321_ = v_reuseFailAlloc_3322_;
goto v_reusejp_3320_;
}
v_reusejp_3320_:
{
return v___x_3321_;
}
}
}
else
{
if (lean_obj_tag(v___x_3313_) == 0)
{
lean_object* v_a_3324_; lean_object* v___x_3326_; uint8_t v_isShared_3327_; uint8_t v_isSharedCheck_3331_; 
lean_dec(v_json_3311_);
v_a_3324_ = lean_ctor_get(v___x_3313_, 0);
v_isSharedCheck_3331_ = !lean_is_exclusive(v___x_3313_);
if (v_isSharedCheck_3331_ == 0)
{
v___x_3326_ = v___x_3313_;
v_isShared_3327_ = v_isSharedCheck_3331_;
goto v_resetjp_3325_;
}
else
{
lean_inc(v_a_3324_);
lean_dec(v___x_3313_);
v___x_3326_ = lean_box(0);
v_isShared_3327_ = v_isSharedCheck_3331_;
goto v_resetjp_3325_;
}
v_resetjp_3325_:
{
lean_object* v___x_3329_; 
if (v_isShared_3327_ == 0)
{
lean_ctor_set_tag(v___x_3326_, 0);
v___x_3329_ = v___x_3326_;
goto v_reusejp_3328_;
}
else
{
lean_object* v_reuseFailAlloc_3330_; 
v_reuseFailAlloc_3330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3330_, 0, v_a_3324_);
v___x_3329_ = v_reuseFailAlloc_3330_;
goto v_reusejp_3328_;
}
v_reusejp_3328_:
{
return v___x_3329_;
}
}
}
else
{
lean_object* v_a_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; 
v_a_3332_ = lean_ctor_get(v___x_3313_, 0);
lean_inc(v_a_3332_);
lean_dec_ref_known(v___x_3313_, 1);
v___x_3333_ = ((lean_object*)(l_Lean_Lsp_instReprLineRange_repr___redArg___closed__10));
v___x_3334_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWaitForDiagnosticsParams_fromJson_spec__1(v_json_3311_, v___x_3333_);
if (lean_obj_tag(v___x_3334_) == 0)
{
lean_object* v_a_3335_; lean_object* v___x_3337_; uint8_t v_isShared_3338_; uint8_t v_isSharedCheck_3344_; 
lean_dec(v_a_3332_);
v_a_3335_ = lean_ctor_get(v___x_3334_, 0);
v_isSharedCheck_3344_ = !lean_is_exclusive(v___x_3334_);
if (v_isSharedCheck_3344_ == 0)
{
v___x_3337_ = v___x_3334_;
v_isShared_3338_ = v_isSharedCheck_3344_;
goto v_resetjp_3336_;
}
else
{
lean_inc(v_a_3335_);
lean_dec(v___x_3334_);
v___x_3337_ = lean_box(0);
v_isShared_3338_ = v_isSharedCheck_3344_;
goto v_resetjp_3336_;
}
v_resetjp_3336_:
{
lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3342_; 
v___x_3339_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__11, &l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonLineRange_fromJson___closed__11);
v___x_3340_ = lean_string_append(v___x_3339_, v_a_3335_);
lean_dec(v_a_3335_);
if (v_isShared_3338_ == 0)
{
lean_ctor_set(v___x_3337_, 0, v___x_3340_);
v___x_3342_ = v___x_3337_;
goto v_reusejp_3341_;
}
else
{
lean_object* v_reuseFailAlloc_3343_; 
v_reuseFailAlloc_3343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3343_, 0, v___x_3340_);
v___x_3342_ = v_reuseFailAlloc_3343_;
goto v_reusejp_3341_;
}
v_reusejp_3341_:
{
return v___x_3342_;
}
}
}
else
{
if (lean_obj_tag(v___x_3334_) == 0)
{
lean_object* v_a_3345_; lean_object* v___x_3347_; uint8_t v_isShared_3348_; uint8_t v_isSharedCheck_3352_; 
lean_dec(v_a_3332_);
v_a_3345_ = lean_ctor_get(v___x_3334_, 0);
v_isSharedCheck_3352_ = !lean_is_exclusive(v___x_3334_);
if (v_isSharedCheck_3352_ == 0)
{
v___x_3347_ = v___x_3334_;
v_isShared_3348_ = v_isSharedCheck_3352_;
goto v_resetjp_3346_;
}
else
{
lean_inc(v_a_3345_);
lean_dec(v___x_3334_);
v___x_3347_ = lean_box(0);
v_isShared_3348_ = v_isSharedCheck_3352_;
goto v_resetjp_3346_;
}
v_resetjp_3346_:
{
lean_object* v___x_3350_; 
if (v_isShared_3348_ == 0)
{
lean_ctor_set_tag(v___x_3347_, 0);
v___x_3350_ = v___x_3347_;
goto v_reusejp_3349_;
}
else
{
lean_object* v_reuseFailAlloc_3351_; 
v_reuseFailAlloc_3351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3351_, 0, v_a_3345_);
v___x_3350_ = v_reuseFailAlloc_3351_;
goto v_reusejp_3349_;
}
v_reusejp_3349_:
{
return v___x_3350_;
}
}
}
else
{
lean_object* v_a_3353_; lean_object* v___x_3355_; uint8_t v_isShared_3356_; uint8_t v_isSharedCheck_3361_; 
v_a_3353_ = lean_ctor_get(v___x_3334_, 0);
v_isSharedCheck_3361_ = !lean_is_exclusive(v___x_3334_);
if (v_isSharedCheck_3361_ == 0)
{
v___x_3355_ = v___x_3334_;
v_isShared_3356_ = v_isSharedCheck_3361_;
goto v_resetjp_3354_;
}
else
{
lean_inc(v_a_3353_);
lean_dec(v___x_3334_);
v___x_3355_ = lean_box(0);
v_isShared_3356_ = v_isSharedCheck_3361_;
goto v_resetjp_3354_;
}
v_resetjp_3354_:
{
lean_object* v___x_3357_; lean_object* v___x_3359_; 
v___x_3357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3357_, 0, v_a_3332_);
lean_ctor_set(v___x_3357_, 1, v_a_3353_);
if (v_isShared_3356_ == 0)
{
lean_ctor_set(v___x_3355_, 0, v___x_3357_);
v___x_3359_ = v___x_3355_;
goto v_reusejp_3358_;
}
else
{
lean_object* v_reuseFailAlloc_3360_; 
v_reuseFailAlloc_3360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3360_, 0, v___x_3357_);
v___x_3359_ = v_reuseFailAlloc_3360_;
goto v_reusejp_3358_;
}
v_reusejp_3358_:
{
return v___x_3359_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLineRange_toJson(lean_object* v_x_3364_){
_start:
{
lean_object* v_start_3365_; lean_object* v_end_3366_; lean_object* v___x_3368_; uint8_t v_isShared_3369_; uint8_t v_isSharedCheck_3388_; 
v_start_3365_ = lean_ctor_get(v_x_3364_, 0);
v_end_3366_ = lean_ctor_get(v_x_3364_, 1);
v_isSharedCheck_3388_ = !lean_is_exclusive(v_x_3364_);
if (v_isSharedCheck_3388_ == 0)
{
v___x_3368_ = v_x_3364_;
v_isShared_3369_ = v_isSharedCheck_3388_;
goto v_resetjp_3367_;
}
else
{
lean_inc(v_end_3366_);
lean_inc(v_start_3365_);
lean_dec(v_x_3364_);
v___x_3368_ = lean_box(0);
v_isShared_3369_ = v_isSharedCheck_3388_;
goto v_resetjp_3367_;
}
v_resetjp_3367_:
{
lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3374_; 
v___x_3370_ = ((lean_object*)(l_Lean_Lsp_instReprLineRange_repr___redArg___closed__1));
v___x_3371_ = l_Lean_JsonNumber_fromNat(v_start_3365_);
v___x_3372_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3372_, 0, v___x_3371_);
if (v_isShared_3369_ == 0)
{
lean_ctor_set(v___x_3368_, 1, v___x_3372_);
lean_ctor_set(v___x_3368_, 0, v___x_3370_);
v___x_3374_ = v___x_3368_;
goto v_reusejp_3373_;
}
else
{
lean_object* v_reuseFailAlloc_3387_; 
v_reuseFailAlloc_3387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3387_, 0, v___x_3370_);
lean_ctor_set(v_reuseFailAlloc_3387_, 1, v___x_3372_);
v___x_3374_ = v_reuseFailAlloc_3387_;
goto v_reusejp_3373_;
}
v_reusejp_3373_:
{
lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; 
v___x_3375_ = lean_box(0);
v___x_3376_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3376_, 0, v___x_3374_);
lean_ctor_set(v___x_3376_, 1, v___x_3375_);
v___x_3377_ = ((lean_object*)(l_Lean_Lsp_instReprLineRange_repr___redArg___closed__10));
v___x_3378_ = l_Lean_JsonNumber_fromNat(v_end_3366_);
v___x_3379_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3379_, 0, v___x_3378_);
v___x_3380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3380_, 0, v___x_3377_);
lean_ctor_set(v___x_3380_, 1, v___x_3379_);
v___x_3381_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3381_, 0, v___x_3380_);
lean_ctor_set(v___x_3381_, 1, v___x_3375_);
v___x_3382_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3382_, 0, v___x_3381_);
lean_ctor_set(v___x_3382_, 1, v___x_3375_);
v___x_3383_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3383_, 0, v___x_3376_);
lean_ctor_set(v___x_3383_, 1, v___x_3382_);
v___x_3384_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson___closed__0));
v___x_3385_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLeanDidOpenTextDocumentParams_toJson_spec__1(v___x_3383_, v___x_3384_);
v___x_3386_ = l_Lean_Json_mkObj(v___x_3385_);
lean_dec(v___x_3385_);
return v___x_3386_;
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

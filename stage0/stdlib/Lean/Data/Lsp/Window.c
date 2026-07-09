// Lean compiler output
// Module: Lean.Data.Lsp.Window
// Imports: public import Lean.Data.Json.FromToJson.Basic
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
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_JsonNumber_fromNat(lean_object*);
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
lean_object* l_Lean_Option_toJson___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Option_fromJson_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_error_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_error_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_error_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_error_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_warning_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_warning_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_warning_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_warning_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_info_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_info_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_info_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_info_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_log_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_log_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_log_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_log_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instFromJsonMessageType___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Unknown MessageType ID"};
static const lean_object* l_Lean_Lsp_instFromJsonMessageType___lam__0___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonMessageType___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonMessageType___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonMessageType___lam__0___closed__0_value)}};
static const lean_object* l_Lean_Lsp_instFromJsonMessageType___lam__0___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonMessageType___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonMessageType___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonMessageType___lam__0___closed__2;
static const lean_ctor_object l_Lean_Lsp_instFromJsonMessageType___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l_Lean_Lsp_instFromJsonMessageType___lam__0___closed__3 = (const lean_object*)&l_Lean_Lsp_instFromJsonMessageType___lam__0___closed__3_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonMessageType___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l_Lean_Lsp_instFromJsonMessageType___lam__0___closed__4 = (const lean_object*)&l_Lean_Lsp_instFromJsonMessageType___lam__0___closed__4_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonMessageType___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Lsp_instFromJsonMessageType___lam__0___closed__5 = (const lean_object*)&l_Lean_Lsp_instFromJsonMessageType___lam__0___closed__5_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonMessageType___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Lsp_instFromJsonMessageType___lam__0___closed__6 = (const lean_object*)&l_Lean_Lsp_instFromJsonMessageType___lam__0___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonMessageType___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonMessageType___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonMessageType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonMessageType___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonMessageType___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonMessageType___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonMessageType = (const lean_object*)&l_Lean_Lsp_instFromJsonMessageType___closed__0_value;
static lean_once_cell_t l_Lean_Lsp_instToJsonMessageType___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instToJsonMessageType___lam__0___closed__0;
static lean_once_cell_t l_Lean_Lsp_instToJsonMessageType___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instToJsonMessageType___lam__0___closed__1;
static lean_once_cell_t l_Lean_Lsp_instToJsonMessageType___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instToJsonMessageType___lam__0___closed__2;
static lean_once_cell_t l_Lean_Lsp_instToJsonMessageType___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instToJsonMessageType___lam__0___closed__3;
static lean_once_cell_t l_Lean_Lsp_instToJsonMessageType___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instToJsonMessageType___lam__0___closed__4;
static lean_once_cell_t l_Lean_Lsp_instToJsonMessageType___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instToJsonMessageType___lam__0___closed__5;
static lean_once_cell_t l_Lean_Lsp_instToJsonMessageType___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instToJsonMessageType___lam__0___closed__6;
static lean_once_cell_t l_Lean_Lsp_instToJsonMessageType___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instToJsonMessageType___lam__0___closed__7;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonMessageType___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonMessageType___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonMessageType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonMessageType___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonMessageType___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonMessageType___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonMessageType = (const lean_object*)&l_Lean_Lsp_instToJsonMessageType___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageParams_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageParams_fromJson_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageParams_fromJson_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageParams_fromJson_spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "type"};
static const lean_object* l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__0_value;
static const lean_string_object l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__1_value;
static const lean_string_object l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Lsp"};
static const lean_object* l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__2 = (const lean_object*)&l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__2_value;
static const lean_string_object l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "ShowMessageParams"};
static const lean_object* l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__3 = (const lean_object*)&l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__3_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__4_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__2_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__4_value_aux_1),((lean_object*)&l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__3_value),LEAN_SCALAR_PTR_LITERAL(169, 191, 194, 120, 144, 205, 230, 24)}};
static const lean_object* l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__4 = (const lean_object*)&l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__4_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__5;
static const lean_string_object l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__6 = (const lean_object*)&l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__6_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__7;
static const lean_ctor_object l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(112, 109, 54, 158, 248, 169, 165, 159)}};
static const lean_object* l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__8 = (const lean_object*)&l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__8_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__9;
static lean_once_cell_t l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__10;
static const lean_string_object l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__11 = (const lean_object*)&l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__11_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__12;
static const lean_string_object l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "message"};
static const lean_object* l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__13 = (const lean_object*)&l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__13_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__13_value),LEAN_SCALAR_PTR_LITERAL(149, 62, 76, 216, 222, 7, 163, 13)}};
static const lean_object* l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__14 = (const lean_object*)&l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__14_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__15;
static lean_once_cell_t l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__16;
static lean_once_cell_t l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__17;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonShowMessageParams_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonShowMessageParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonShowMessageParams_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonShowMessageParams___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonShowMessageParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonShowMessageParams = (const lean_object*)&l_Lean_Lsp_instFromJsonShowMessageParams___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonShowMessageParams_toJson_spec__0(lean_object*, lean_object*);
static const lean_array_object l_Lean_Lsp_instToJsonShowMessageParams_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Lsp_instToJsonShowMessageParams_toJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonShowMessageParams_toJson___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonShowMessageParams_toJson(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonShowMessageParams_toJson___boxed(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonShowMessageParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonShowMessageParams_toJson___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonShowMessageParams___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonShowMessageParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonShowMessageParams = (const lean_object*)&l_Lean_Lsp_instToJsonShowMessageParams___closed__0_value;
static const lean_string_object l_Lean_Lsp_instFromJsonMessageActionItem_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "title"};
static const lean_object* l_Lean_Lsp_instFromJsonMessageActionItem_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonMessageActionItem_fromJson___closed__0_value;
static const lean_string_object l_Lean_Lsp_instFromJsonMessageActionItem_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "MessageActionItem"};
static const lean_object* l_Lean_Lsp_instFromJsonMessageActionItem_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonMessageActionItem_fromJson___closed__1_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonMessageActionItem_fromJson___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonMessageActionItem_fromJson___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonMessageActionItem_fromJson___closed__2_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__2_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonMessageActionItem_fromJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonMessageActionItem_fromJson___closed__2_value_aux_1),((lean_object*)&l_Lean_Lsp_instFromJsonMessageActionItem_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(228, 128, 38, 211, 126, 33, 24, 229)}};
static const lean_object* l_Lean_Lsp_instFromJsonMessageActionItem_fromJson___closed__2 = (const lean_object*)&l_Lean_Lsp_instFromJsonMessageActionItem_fromJson___closed__2_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonMessageActionItem_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonMessageActionItem_fromJson___closed__3;
static lean_once_cell_t l_Lean_Lsp_instFromJsonMessageActionItem_fromJson___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonMessageActionItem_fromJson___closed__4;
static const lean_ctor_object l_Lean_Lsp_instFromJsonMessageActionItem_fromJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonMessageActionItem_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(251, 99, 171, 63, 21, 188, 124, 202)}};
static const lean_object* l_Lean_Lsp_instFromJsonMessageActionItem_fromJson___closed__5 = (const lean_object*)&l_Lean_Lsp_instFromJsonMessageActionItem_fromJson___closed__5_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonMessageActionItem_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonMessageActionItem_fromJson___closed__6;
static lean_once_cell_t l_Lean_Lsp_instFromJsonMessageActionItem_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonMessageActionItem_fromJson___closed__7;
static lean_once_cell_t l_Lean_Lsp_instFromJsonMessageActionItem_fromJson___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonMessageActionItem_fromJson___closed__8;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonMessageActionItem_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonMessageActionItem___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonMessageActionItem_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonMessageActionItem___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonMessageActionItem___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonMessageActionItem = (const lean_object*)&l_Lean_Lsp_instFromJsonMessageActionItem___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonMessageActionItem_toJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonMessageActionItem___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonMessageActionItem_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonMessageActionItem___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonMessageActionItem___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonMessageActionItem = (const lean_object*)&l_Lean_Lsp_instToJsonMessageActionItem___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0_spec__1_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "expected JSON array, got '"};
static const lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0_spec__1___closed__0 = (const lean_object*)&l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0_spec__1___closed__0_value;
static const lean_string_object l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0_spec__1___closed__1 = (const lean_object*)&l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0_spec__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0_spec__1(lean_object*);
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "ShowMessageRequestParams"};
static const lean_object* l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__1_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__2_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__1_value_aux_1),((lean_object*)&l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(151, 176, 240, 175, 105, 86, 221, 197)}};
static const lean_object* l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__1_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__2;
static lean_once_cell_t l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__3;
static lean_once_cell_t l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__4;
static lean_once_cell_t l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__5;
static lean_once_cell_t l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__6;
static lean_once_cell_t l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__7;
static const lean_string_object l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "actions"};
static const lean_object* l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__8 = (const lean_object*)&l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__8_value;
static const lean_string_object l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "actions\?"};
static const lean_object* l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__9 = (const lean_object*)&l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__9_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__9_value),LEAN_SCALAR_PTR_LITERAL(223, 135, 214, 230, 197, 178, 71, 91)}};
static const lean_object* l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__10 = (const lean_object*)&l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__10_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__11;
static lean_once_cell_t l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__12;
static lean_once_cell_t l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__13;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonShowMessageRequestParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonShowMessageRequestParams___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonShowMessageRequestParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonShowMessageRequestParams = (const lean_object*)&l_Lean_Lsp_instFromJsonShowMessageRequestParams___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonShowMessageRequestParams_toJson_spec__0_spec__0_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonShowMessageRequestParams_toJson_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonShowMessageRequestParams_toJson_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonShowMessageRequestParams_toJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonShowMessageRequestParams_toJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonShowMessageRequestParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonShowMessageRequestParams_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonShowMessageRequestParams___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonShowMessageRequestParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonShowMessageRequestParams = (const lean_object*)&l_Lean_Lsp_instToJsonShowMessageRequestParams___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonShowMessageResponse___aux__1(lean_object*);
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lean_Lsp_instFromJsonShowMessageResponse_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Lsp_instFromJsonShowMessageResponse_spec__0___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lean_Lsp_instFromJsonShowMessageResponse_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Lsp_instFromJsonShowMessageResponse_spec__0(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonShowMessageResponse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Option_fromJson_x3f___at___00Lean_Lsp_instFromJsonShowMessageResponse_spec__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonShowMessageResponse___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonShowMessageResponse___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonShowMessageResponse = (const lean_object*)&l_Lean_Lsp_instFromJsonShowMessageResponse___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonShowMessageResponse___aux__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_toJson___at___00Lean_Lsp_instToJsonShowMessageResponse_spec__0(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonShowMessageResponse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Option_toJson___at___00Lean_Lsp_instToJsonShowMessageResponse_spec__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonShowMessageResponse___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonShowMessageResponse___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonShowMessageResponse = (const lean_object*)&l_Lean_Lsp_instToJsonShowMessageResponse___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_ctorIdx(uint8_t v_x_1_){
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
case 2:
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
default: 
{
lean_object* v___x_5_; 
v___x_5_ = lean_unsigned_to_nat(3u);
return v___x_5_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_ctorIdx___boxed(lean_object* v_x_6_){
_start:
{
uint8_t v_x_boxed_7_; lean_object* v_res_8_; 
v_x_boxed_7_ = lean_unbox(v_x_6_);
v_res_8_ = l_Lean_Lsp_MessageType_ctorIdx(v_x_boxed_7_);
return v_res_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_toCtorIdx(uint8_t v_x_9_){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = l_Lean_Lsp_MessageType_ctorIdx(v_x_9_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_toCtorIdx___boxed(lean_object* v_x_11_){
_start:
{
uint8_t v_x_4__boxed_12_; lean_object* v_res_13_; 
v_x_4__boxed_12_ = lean_unbox(v_x_11_);
v_res_13_ = l_Lean_Lsp_MessageType_toCtorIdx(v_x_4__boxed_12_);
return v_res_13_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_ctorElim___redArg(lean_object* v_k_14_){
_start:
{
lean_inc(v_k_14_);
return v_k_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_ctorElim___redArg___boxed(lean_object* v_k_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = l_Lean_Lsp_MessageType_ctorElim___redArg(v_k_15_);
lean_dec(v_k_15_);
return v_res_16_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_ctorElim(lean_object* v_motive_17_, lean_object* v_ctorIdx_18_, uint8_t v_t_19_, lean_object* v_h_20_, lean_object* v_k_21_){
_start:
{
lean_inc(v_k_21_);
return v_k_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_ctorElim___boxed(lean_object* v_motive_22_, lean_object* v_ctorIdx_23_, lean_object* v_t_24_, lean_object* v_h_25_, lean_object* v_k_26_){
_start:
{
uint8_t v_t_boxed_27_; lean_object* v_res_28_; 
v_t_boxed_27_ = lean_unbox(v_t_24_);
v_res_28_ = l_Lean_Lsp_MessageType_ctorElim(v_motive_22_, v_ctorIdx_23_, v_t_boxed_27_, v_h_25_, v_k_26_);
lean_dec(v_k_26_);
lean_dec(v_ctorIdx_23_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_error_elim___redArg(lean_object* v_error_29_){
_start:
{
lean_inc(v_error_29_);
return v_error_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_error_elim___redArg___boxed(lean_object* v_error_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = l_Lean_Lsp_MessageType_error_elim___redArg(v_error_30_);
lean_dec(v_error_30_);
return v_res_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_error_elim(lean_object* v_motive_32_, uint8_t v_t_33_, lean_object* v_h_34_, lean_object* v_error_35_){
_start:
{
lean_inc(v_error_35_);
return v_error_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_error_elim___boxed(lean_object* v_motive_36_, lean_object* v_t_37_, lean_object* v_h_38_, lean_object* v_error_39_){
_start:
{
uint8_t v_t_boxed_40_; lean_object* v_res_41_; 
v_t_boxed_40_ = lean_unbox(v_t_37_);
v_res_41_ = l_Lean_Lsp_MessageType_error_elim(v_motive_36_, v_t_boxed_40_, v_h_38_, v_error_39_);
lean_dec(v_error_39_);
return v_res_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_warning_elim___redArg(lean_object* v_warning_42_){
_start:
{
lean_inc(v_warning_42_);
return v_warning_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_warning_elim___redArg___boxed(lean_object* v_warning_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l_Lean_Lsp_MessageType_warning_elim___redArg(v_warning_43_);
lean_dec(v_warning_43_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_warning_elim(lean_object* v_motive_45_, uint8_t v_t_46_, lean_object* v_h_47_, lean_object* v_warning_48_){
_start:
{
lean_inc(v_warning_48_);
return v_warning_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_warning_elim___boxed(lean_object* v_motive_49_, lean_object* v_t_50_, lean_object* v_h_51_, lean_object* v_warning_52_){
_start:
{
uint8_t v_t_boxed_53_; lean_object* v_res_54_; 
v_t_boxed_53_ = lean_unbox(v_t_50_);
v_res_54_ = l_Lean_Lsp_MessageType_warning_elim(v_motive_49_, v_t_boxed_53_, v_h_51_, v_warning_52_);
lean_dec(v_warning_52_);
return v_res_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_info_elim___redArg(lean_object* v_info_55_){
_start:
{
lean_inc(v_info_55_);
return v_info_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_info_elim___redArg___boxed(lean_object* v_info_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = l_Lean_Lsp_MessageType_info_elim___redArg(v_info_56_);
lean_dec(v_info_56_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_info_elim(lean_object* v_motive_58_, uint8_t v_t_59_, lean_object* v_h_60_, lean_object* v_info_61_){
_start:
{
lean_inc(v_info_61_);
return v_info_61_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_info_elim___boxed(lean_object* v_motive_62_, lean_object* v_t_63_, lean_object* v_h_64_, lean_object* v_info_65_){
_start:
{
uint8_t v_t_boxed_66_; lean_object* v_res_67_; 
v_t_boxed_66_ = lean_unbox(v_t_63_);
v_res_67_ = l_Lean_Lsp_MessageType_info_elim(v_motive_62_, v_t_boxed_66_, v_h_64_, v_info_65_);
lean_dec(v_info_65_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_log_elim___redArg(lean_object* v_log_68_){
_start:
{
lean_inc(v_log_68_);
return v_log_68_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_log_elim___redArg___boxed(lean_object* v_log_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = l_Lean_Lsp_MessageType_log_elim___redArg(v_log_69_);
lean_dec(v_log_69_);
return v_res_70_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_log_elim(lean_object* v_motive_71_, uint8_t v_t_72_, lean_object* v_h_73_, lean_object* v_log_74_){
_start:
{
lean_inc(v_log_74_);
return v_log_74_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_log_elim___boxed(lean_object* v_motive_75_, lean_object* v_t_76_, lean_object* v_h_77_, lean_object* v_log_78_){
_start:
{
uint8_t v_t_boxed_79_; lean_object* v_res_80_; 
v_t_boxed_79_ = lean_unbox(v_t_76_);
v_res_80_ = l_Lean_Lsp_MessageType_log_elim(v_motive_75_, v_t_boxed_79_, v_h_77_, v_log_78_);
lean_dec(v_log_78_);
return v_res_80_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonMessageType___lam__0___closed__2(void){
_start:
{
lean_object* v_natZero_84_; lean_object* v_intZero_85_; 
v_natZero_84_ = lean_unsigned_to_nat(0u);
v_intZero_85_ = lean_nat_to_int(v_natZero_84_);
return v_intZero_85_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonMessageType___lam__0(lean_object* v_x_98_){
_start:
{
if (lean_obj_tag(v_x_98_) == 2)
{
lean_object* v_n_101_; lean_object* v_mantissa_102_; lean_object* v_exponent_103_; lean_object* v_natZero_104_; lean_object* v_intZero_105_; uint8_t v_isNeg_106_; 
v_n_101_ = lean_ctor_get(v_x_98_, 0);
v_mantissa_102_ = lean_ctor_get(v_n_101_, 0);
v_exponent_103_ = lean_ctor_get(v_n_101_, 1);
v_natZero_104_ = lean_unsigned_to_nat(0u);
v_intZero_105_ = lean_obj_once(&l_Lean_Lsp_instFromJsonMessageType___lam__0___closed__2, &l_Lean_Lsp_instFromJsonMessageType___lam__0___closed__2_once, _init_l_Lean_Lsp_instFromJsonMessageType___lam__0___closed__2);
v_isNeg_106_ = lean_int_dec_lt(v_mantissa_102_, v_intZero_105_);
if (v_isNeg_106_ == 0)
{
lean_object* v_a_107_; lean_object* v___x_108_; uint8_t v___x_109_; 
v_a_107_ = lean_nat_abs(v_mantissa_102_);
v___x_108_ = lean_unsigned_to_nat(1u);
v___x_109_ = lean_nat_dec_eq(v_a_107_, v___x_108_);
if (v___x_109_ == 0)
{
lean_object* v___x_110_; uint8_t v___x_111_; 
v___x_110_ = lean_unsigned_to_nat(2u);
v___x_111_ = lean_nat_dec_eq(v_a_107_, v___x_110_);
if (v___x_111_ == 0)
{
lean_object* v___x_112_; uint8_t v___x_113_; 
v___x_112_ = lean_unsigned_to_nat(3u);
v___x_113_ = lean_nat_dec_eq(v_a_107_, v___x_112_);
if (v___x_113_ == 0)
{
lean_object* v___x_114_; uint8_t v___x_115_; 
v___x_114_ = lean_unsigned_to_nat(4u);
v___x_115_ = lean_nat_dec_eq(v_a_107_, v___x_114_);
lean_dec(v_a_107_);
if (v___x_115_ == 0)
{
goto v___jp_99_;
}
else
{
uint8_t v___x_116_; 
v___x_116_ = lean_nat_dec_eq(v_exponent_103_, v_natZero_104_);
if (v___x_116_ == 0)
{
goto v___jp_99_;
}
else
{
lean_object* v___x_117_; 
v___x_117_ = ((lean_object*)(l_Lean_Lsp_instFromJsonMessageType___lam__0___closed__3));
return v___x_117_;
}
}
}
else
{
uint8_t v___x_118_; 
lean_dec(v_a_107_);
v___x_118_ = lean_nat_dec_eq(v_exponent_103_, v_natZero_104_);
if (v___x_118_ == 0)
{
goto v___jp_99_;
}
else
{
lean_object* v___x_119_; 
v___x_119_ = ((lean_object*)(l_Lean_Lsp_instFromJsonMessageType___lam__0___closed__4));
return v___x_119_;
}
}
}
else
{
uint8_t v___x_120_; 
lean_dec(v_a_107_);
v___x_120_ = lean_nat_dec_eq(v_exponent_103_, v_natZero_104_);
if (v___x_120_ == 0)
{
goto v___jp_99_;
}
else
{
lean_object* v___x_121_; 
v___x_121_ = ((lean_object*)(l_Lean_Lsp_instFromJsonMessageType___lam__0___closed__5));
return v___x_121_;
}
}
}
else
{
uint8_t v___x_122_; 
lean_dec(v_a_107_);
v___x_122_ = lean_nat_dec_eq(v_exponent_103_, v_natZero_104_);
if (v___x_122_ == 0)
{
goto v___jp_99_;
}
else
{
lean_object* v___x_123_; 
v___x_123_ = ((lean_object*)(l_Lean_Lsp_instFromJsonMessageType___lam__0___closed__6));
return v___x_123_;
}
}
}
else
{
goto v___jp_99_;
}
}
else
{
goto v___jp_99_;
}
v___jp_99_:
{
lean_object* v___x_100_; 
v___x_100_ = ((lean_object*)(l_Lean_Lsp_instFromJsonMessageType___lam__0___closed__1));
return v___x_100_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonMessageType___lam__0___boxed(lean_object* v_x_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = l_Lean_Lsp_instFromJsonMessageType___lam__0(v_x_124_);
lean_dec(v_x_124_);
return v_res_125_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonMessageType___lam__0___closed__0(void){
_start:
{
lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_128_ = lean_unsigned_to_nat(1u);
v___x_129_ = l_Lean_JsonNumber_fromNat(v___x_128_);
return v___x_129_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonMessageType___lam__0___closed__1(void){
_start:
{
lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_130_ = lean_obj_once(&l_Lean_Lsp_instToJsonMessageType___lam__0___closed__0, &l_Lean_Lsp_instToJsonMessageType___lam__0___closed__0_once, _init_l_Lean_Lsp_instToJsonMessageType___lam__0___closed__0);
v___x_131_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_131_, 0, v___x_130_);
return v___x_131_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonMessageType___lam__0___closed__2(void){
_start:
{
lean_object* v___x_132_; lean_object* v___x_133_; 
v___x_132_ = lean_unsigned_to_nat(2u);
v___x_133_ = l_Lean_JsonNumber_fromNat(v___x_132_);
return v___x_133_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonMessageType___lam__0___closed__3(void){
_start:
{
lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_134_ = lean_obj_once(&l_Lean_Lsp_instToJsonMessageType___lam__0___closed__2, &l_Lean_Lsp_instToJsonMessageType___lam__0___closed__2_once, _init_l_Lean_Lsp_instToJsonMessageType___lam__0___closed__2);
v___x_135_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_135_, 0, v___x_134_);
return v___x_135_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonMessageType___lam__0___closed__4(void){
_start:
{
lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_136_ = lean_unsigned_to_nat(3u);
v___x_137_ = l_Lean_JsonNumber_fromNat(v___x_136_);
return v___x_137_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonMessageType___lam__0___closed__5(void){
_start:
{
lean_object* v___x_138_; lean_object* v___x_139_; 
v___x_138_ = lean_obj_once(&l_Lean_Lsp_instToJsonMessageType___lam__0___closed__4, &l_Lean_Lsp_instToJsonMessageType___lam__0___closed__4_once, _init_l_Lean_Lsp_instToJsonMessageType___lam__0___closed__4);
v___x_139_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_139_, 0, v___x_138_);
return v___x_139_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonMessageType___lam__0___closed__6(void){
_start:
{
lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_140_ = lean_unsigned_to_nat(4u);
v___x_141_ = l_Lean_JsonNumber_fromNat(v___x_140_);
return v___x_141_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonMessageType___lam__0___closed__7(void){
_start:
{
lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_142_ = lean_obj_once(&l_Lean_Lsp_instToJsonMessageType___lam__0___closed__6, &l_Lean_Lsp_instToJsonMessageType___lam__0___closed__6_once, _init_l_Lean_Lsp_instToJsonMessageType___lam__0___closed__6);
v___x_143_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_143_, 0, v___x_142_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonMessageType___lam__0(uint8_t v_x_144_){
_start:
{
switch(v_x_144_)
{
case 0:
{
lean_object* v___x_145_; 
v___x_145_ = lean_obj_once(&l_Lean_Lsp_instToJsonMessageType___lam__0___closed__1, &l_Lean_Lsp_instToJsonMessageType___lam__0___closed__1_once, _init_l_Lean_Lsp_instToJsonMessageType___lam__0___closed__1);
return v___x_145_;
}
case 1:
{
lean_object* v___x_146_; 
v___x_146_ = lean_obj_once(&l_Lean_Lsp_instToJsonMessageType___lam__0___closed__3, &l_Lean_Lsp_instToJsonMessageType___lam__0___closed__3_once, _init_l_Lean_Lsp_instToJsonMessageType___lam__0___closed__3);
return v___x_146_;
}
case 2:
{
lean_object* v___x_147_; 
v___x_147_ = lean_obj_once(&l_Lean_Lsp_instToJsonMessageType___lam__0___closed__5, &l_Lean_Lsp_instToJsonMessageType___lam__0___closed__5_once, _init_l_Lean_Lsp_instToJsonMessageType___lam__0___closed__5);
return v___x_147_;
}
default: 
{
lean_object* v___x_148_; 
v___x_148_ = lean_obj_once(&l_Lean_Lsp_instToJsonMessageType___lam__0___closed__7, &l_Lean_Lsp_instToJsonMessageType___lam__0___closed__7_once, _init_l_Lean_Lsp_instToJsonMessageType___lam__0___closed__7);
return v___x_148_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonMessageType___lam__0___boxed(lean_object* v_x_149_){
_start:
{
uint8_t v_x_106__boxed_150_; lean_object* v_res_151_; 
v_x_106__boxed_150_ = lean_unbox(v_x_149_);
v_res_151_ = l_Lean_Lsp_instToJsonMessageType___lam__0(v_x_106__boxed_150_);
return v_res_151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageParams_fromJson_spec__0(lean_object* v_j_154_, lean_object* v_k_155_){
_start:
{
lean_object* v___x_158_; 
v___x_158_ = l_Lean_Json_getObjValD(v_j_154_, v_k_155_);
if (lean_obj_tag(v___x_158_) == 2)
{
lean_object* v_n_159_; lean_object* v_mantissa_160_; lean_object* v_exponent_161_; lean_object* v_natZero_162_; lean_object* v_intZero_163_; uint8_t v_isNeg_164_; 
v_n_159_ = lean_ctor_get(v___x_158_, 0);
lean_inc_ref(v_n_159_);
lean_dec_ref_known(v___x_158_, 1);
v_mantissa_160_ = lean_ctor_get(v_n_159_, 0);
lean_inc(v_mantissa_160_);
v_exponent_161_ = lean_ctor_get(v_n_159_, 1);
lean_inc(v_exponent_161_);
lean_dec_ref(v_n_159_);
v_natZero_162_ = lean_unsigned_to_nat(0u);
v_intZero_163_ = lean_obj_once(&l_Lean_Lsp_instFromJsonMessageType___lam__0___closed__2, &l_Lean_Lsp_instFromJsonMessageType___lam__0___closed__2_once, _init_l_Lean_Lsp_instFromJsonMessageType___lam__0___closed__2);
v_isNeg_164_ = lean_int_dec_lt(v_mantissa_160_, v_intZero_163_);
if (v_isNeg_164_ == 0)
{
lean_object* v_a_165_; lean_object* v___x_166_; uint8_t v___x_167_; 
v_a_165_ = lean_nat_abs(v_mantissa_160_);
lean_dec(v_mantissa_160_);
v___x_166_ = lean_unsigned_to_nat(1u);
v___x_167_ = lean_nat_dec_eq(v_a_165_, v___x_166_);
if (v___x_167_ == 0)
{
lean_object* v___x_168_; uint8_t v___x_169_; 
v___x_168_ = lean_unsigned_to_nat(2u);
v___x_169_ = lean_nat_dec_eq(v_a_165_, v___x_168_);
if (v___x_169_ == 0)
{
lean_object* v___x_170_; uint8_t v___x_171_; 
v___x_170_ = lean_unsigned_to_nat(3u);
v___x_171_ = lean_nat_dec_eq(v_a_165_, v___x_170_);
if (v___x_171_ == 0)
{
lean_object* v___x_172_; uint8_t v___x_173_; 
v___x_172_ = lean_unsigned_to_nat(4u);
v___x_173_ = lean_nat_dec_eq(v_a_165_, v___x_172_);
lean_dec(v_a_165_);
if (v___x_173_ == 0)
{
lean_dec(v_exponent_161_);
goto v___jp_156_;
}
else
{
uint8_t v___x_174_; 
v___x_174_ = lean_nat_dec_eq(v_exponent_161_, v_natZero_162_);
lean_dec(v_exponent_161_);
if (v___x_174_ == 0)
{
goto v___jp_156_;
}
else
{
lean_object* v___x_175_; 
v___x_175_ = ((lean_object*)(l_Lean_Lsp_instFromJsonMessageType___lam__0___closed__3));
return v___x_175_;
}
}
}
else
{
uint8_t v___x_176_; 
lean_dec(v_a_165_);
v___x_176_ = lean_nat_dec_eq(v_exponent_161_, v_natZero_162_);
lean_dec(v_exponent_161_);
if (v___x_176_ == 0)
{
goto v___jp_156_;
}
else
{
lean_object* v___x_177_; 
v___x_177_ = ((lean_object*)(l_Lean_Lsp_instFromJsonMessageType___lam__0___closed__4));
return v___x_177_;
}
}
}
else
{
uint8_t v___x_178_; 
lean_dec(v_a_165_);
v___x_178_ = lean_nat_dec_eq(v_exponent_161_, v_natZero_162_);
lean_dec(v_exponent_161_);
if (v___x_178_ == 0)
{
goto v___jp_156_;
}
else
{
lean_object* v___x_179_; 
v___x_179_ = ((lean_object*)(l_Lean_Lsp_instFromJsonMessageType___lam__0___closed__5));
return v___x_179_;
}
}
}
else
{
uint8_t v___x_180_; 
lean_dec(v_a_165_);
v___x_180_ = lean_nat_dec_eq(v_exponent_161_, v_natZero_162_);
lean_dec(v_exponent_161_);
if (v___x_180_ == 0)
{
goto v___jp_156_;
}
else
{
lean_object* v___x_181_; 
v___x_181_ = ((lean_object*)(l_Lean_Lsp_instFromJsonMessageType___lam__0___closed__6));
return v___x_181_;
}
}
}
else
{
lean_dec(v_exponent_161_);
lean_dec(v_mantissa_160_);
goto v___jp_156_;
}
}
else
{
lean_dec(v___x_158_);
goto v___jp_156_;
}
v___jp_156_:
{
lean_object* v___x_157_; 
v___x_157_ = ((lean_object*)(l_Lean_Lsp_instFromJsonMessageType___lam__0___closed__1));
return v___x_157_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageParams_fromJson_spec__0___boxed(lean_object* v_j_182_, lean_object* v_k_183_){
_start:
{
lean_object* v_res_184_; 
v_res_184_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageParams_fromJson_spec__0(v_j_182_, v_k_183_);
lean_dec_ref(v_k_183_);
return v_res_184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageParams_fromJson_spec__1(lean_object* v_j_185_, lean_object* v_k_186_){
_start:
{
lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_187_ = l_Lean_Json_getObjValD(v_j_185_, v_k_186_);
v___x_188_ = l_Lean_Json_getStr_x3f(v___x_187_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageParams_fromJson_spec__1___boxed(lean_object* v_j_189_, lean_object* v_k_190_){
_start:
{
lean_object* v_res_191_; 
v_res_191_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageParams_fromJson_spec__1(v_j_189_, v_k_190_);
lean_dec_ref(v_k_190_);
return v_res_191_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__5(void){
_start:
{
uint8_t v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_200_ = 1;
v___x_201_ = ((lean_object*)(l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__4));
v___x_202_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_201_, v___x_200_);
return v___x_202_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__7(void){
_start:
{
lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; 
v___x_204_ = ((lean_object*)(l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__6));
v___x_205_ = lean_obj_once(&l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__5, &l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__5);
v___x_206_ = lean_string_append(v___x_205_, v___x_204_);
return v___x_206_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__9(void){
_start:
{
uint8_t v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_209_ = 1;
v___x_210_ = ((lean_object*)(l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__8));
v___x_211_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_210_, v___x_209_);
return v___x_211_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__10(void){
_start:
{
lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; 
v___x_212_ = lean_obj_once(&l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__9, &l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__9);
v___x_213_ = lean_obj_once(&l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__7);
v___x_214_ = lean_string_append(v___x_213_, v___x_212_);
return v___x_214_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__12(void){
_start:
{
lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_216_ = ((lean_object*)(l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__11));
v___x_217_ = lean_obj_once(&l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__10, &l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__10);
v___x_218_ = lean_string_append(v___x_217_, v___x_216_);
return v___x_218_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__15(void){
_start:
{
uint8_t v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_222_ = 1;
v___x_223_ = ((lean_object*)(l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__14));
v___x_224_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_223_, v___x_222_);
return v___x_224_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__16(void){
_start:
{
lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; 
v___x_225_ = lean_obj_once(&l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__15, &l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__15_once, _init_l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__15);
v___x_226_ = lean_obj_once(&l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__7);
v___x_227_ = lean_string_append(v___x_226_, v___x_225_);
return v___x_227_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__17(void){
_start:
{
lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; 
v___x_228_ = ((lean_object*)(l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__11));
v___x_229_ = lean_obj_once(&l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__16, &l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__16_once, _init_l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__16);
v___x_230_ = lean_string_append(v___x_229_, v___x_228_);
return v___x_230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonShowMessageParams_fromJson(lean_object* v_json_231_){
_start:
{
lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_232_ = ((lean_object*)(l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__0));
lean_inc(v_json_231_);
v___x_233_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageParams_fromJson_spec__0(v_json_231_, v___x_232_);
if (lean_obj_tag(v___x_233_) == 0)
{
lean_object* v_a_234_; lean_object* v___x_236_; uint8_t v_isShared_237_; uint8_t v_isSharedCheck_243_; 
lean_dec(v_json_231_);
v_a_234_ = lean_ctor_get(v___x_233_, 0);
v_isSharedCheck_243_ = !lean_is_exclusive(v___x_233_);
if (v_isSharedCheck_243_ == 0)
{
v___x_236_ = v___x_233_;
v_isShared_237_ = v_isSharedCheck_243_;
goto v_resetjp_235_;
}
else
{
lean_inc(v_a_234_);
lean_dec(v___x_233_);
v___x_236_ = lean_box(0);
v_isShared_237_ = v_isSharedCheck_243_;
goto v_resetjp_235_;
}
v_resetjp_235_:
{
lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_241_; 
v___x_238_ = lean_obj_once(&l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__12, &l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__12);
v___x_239_ = lean_string_append(v___x_238_, v_a_234_);
lean_dec(v_a_234_);
if (v_isShared_237_ == 0)
{
lean_ctor_set(v___x_236_, 0, v___x_239_);
v___x_241_ = v___x_236_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v___x_239_);
v___x_241_ = v_reuseFailAlloc_242_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
return v___x_241_;
}
}
}
else
{
if (lean_obj_tag(v___x_233_) == 0)
{
lean_object* v_a_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_251_; 
lean_dec(v_json_231_);
v_a_244_ = lean_ctor_get(v___x_233_, 0);
v_isSharedCheck_251_ = !lean_is_exclusive(v___x_233_);
if (v_isSharedCheck_251_ == 0)
{
v___x_246_ = v___x_233_;
v_isShared_247_ = v_isSharedCheck_251_;
goto v_resetjp_245_;
}
else
{
lean_inc(v_a_244_);
lean_dec(v___x_233_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_251_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
lean_object* v___x_249_; 
if (v_isShared_247_ == 0)
{
lean_ctor_set_tag(v___x_246_, 0);
v___x_249_ = v___x_246_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v_a_244_);
v___x_249_ = v_reuseFailAlloc_250_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
return v___x_249_;
}
}
}
else
{
lean_object* v_a_252_; lean_object* v___x_253_; lean_object* v___x_254_; 
v_a_252_ = lean_ctor_get(v___x_233_, 0);
lean_inc(v_a_252_);
lean_dec_ref_known(v___x_233_, 1);
v___x_253_ = ((lean_object*)(l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__13));
v___x_254_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageParams_fromJson_spec__1(v_json_231_, v___x_253_);
if (lean_obj_tag(v___x_254_) == 0)
{
lean_object* v_a_255_; lean_object* v___x_257_; uint8_t v_isShared_258_; uint8_t v_isSharedCheck_264_; 
lean_dec(v_a_252_);
v_a_255_ = lean_ctor_get(v___x_254_, 0);
v_isSharedCheck_264_ = !lean_is_exclusive(v___x_254_);
if (v_isSharedCheck_264_ == 0)
{
v___x_257_ = v___x_254_;
v_isShared_258_ = v_isSharedCheck_264_;
goto v_resetjp_256_;
}
else
{
lean_inc(v_a_255_);
lean_dec(v___x_254_);
v___x_257_ = lean_box(0);
v_isShared_258_ = v_isSharedCheck_264_;
goto v_resetjp_256_;
}
v_resetjp_256_:
{
lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_262_; 
v___x_259_ = lean_obj_once(&l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__17, &l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__17_once, _init_l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__17);
v___x_260_ = lean_string_append(v___x_259_, v_a_255_);
lean_dec(v_a_255_);
if (v_isShared_258_ == 0)
{
lean_ctor_set(v___x_257_, 0, v___x_260_);
v___x_262_ = v___x_257_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v___x_260_);
v___x_262_ = v_reuseFailAlloc_263_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
return v___x_262_;
}
}
}
else
{
if (lean_obj_tag(v___x_254_) == 0)
{
lean_object* v_a_265_; lean_object* v___x_267_; uint8_t v_isShared_268_; uint8_t v_isSharedCheck_272_; 
lean_dec(v_a_252_);
v_a_265_ = lean_ctor_get(v___x_254_, 0);
v_isSharedCheck_272_ = !lean_is_exclusive(v___x_254_);
if (v_isSharedCheck_272_ == 0)
{
v___x_267_ = v___x_254_;
v_isShared_268_ = v_isSharedCheck_272_;
goto v_resetjp_266_;
}
else
{
lean_inc(v_a_265_);
lean_dec(v___x_254_);
v___x_267_ = lean_box(0);
v_isShared_268_ = v_isSharedCheck_272_;
goto v_resetjp_266_;
}
v_resetjp_266_:
{
lean_object* v___x_270_; 
if (v_isShared_268_ == 0)
{
lean_ctor_set_tag(v___x_267_, 0);
v___x_270_ = v___x_267_;
goto v_reusejp_269_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v_a_265_);
v___x_270_ = v_reuseFailAlloc_271_;
goto v_reusejp_269_;
}
v_reusejp_269_:
{
return v___x_270_;
}
}
}
else
{
lean_object* v_a_273_; lean_object* v___x_275_; uint8_t v_isShared_276_; uint8_t v_isSharedCheck_282_; 
v_a_273_ = lean_ctor_get(v___x_254_, 0);
v_isSharedCheck_282_ = !lean_is_exclusive(v___x_254_);
if (v_isSharedCheck_282_ == 0)
{
v___x_275_ = v___x_254_;
v_isShared_276_ = v_isSharedCheck_282_;
goto v_resetjp_274_;
}
else
{
lean_inc(v_a_273_);
lean_dec(v___x_254_);
v___x_275_ = lean_box(0);
v_isShared_276_ = v_isSharedCheck_282_;
goto v_resetjp_274_;
}
v_resetjp_274_:
{
lean_object* v___x_277_; uint8_t v___x_278_; lean_object* v___x_280_; 
v___x_277_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_277_, 0, v_a_273_);
v___x_278_ = lean_unbox(v_a_252_);
lean_dec(v_a_252_);
lean_ctor_set_uint8(v___x_277_, sizeof(void*)*1, v___x_278_);
if (v_isShared_276_ == 0)
{
lean_ctor_set(v___x_275_, 0, v___x_277_);
v___x_280_ = v___x_275_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v___x_277_);
v___x_280_ = v_reuseFailAlloc_281_;
goto v_reusejp_279_;
}
v_reusejp_279_:
{
return v___x_280_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonShowMessageParams_toJson_spec__0(lean_object* v_a_285_, lean_object* v_a_286_){
_start:
{
if (lean_obj_tag(v_a_285_) == 0)
{
lean_object* v___x_287_; 
v___x_287_ = lean_array_to_list(v_a_286_);
return v___x_287_;
}
else
{
lean_object* v_head_288_; lean_object* v_tail_289_; lean_object* v___x_290_; 
v_head_288_ = lean_ctor_get(v_a_285_, 0);
lean_inc(v_head_288_);
v_tail_289_ = lean_ctor_get(v_a_285_, 1);
lean_inc(v_tail_289_);
lean_dec_ref_known(v_a_285_, 2);
v___x_290_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_286_, v_head_288_);
v_a_285_ = v_tail_289_;
v_a_286_ = v___x_290_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonShowMessageParams_toJson(lean_object* v_x_294_){
_start:
{
uint8_t v_type_295_; lean_object* v_message_296_; lean_object* v___x_297_; lean_object* v___y_299_; 
v_type_295_ = lean_ctor_get_uint8(v_x_294_, sizeof(void*)*1);
v_message_296_ = lean_ctor_get(v_x_294_, 0);
v___x_297_ = ((lean_object*)(l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__0));
switch(v_type_295_)
{
case 0:
{
lean_object* v___x_312_; 
v___x_312_ = lean_obj_once(&l_Lean_Lsp_instToJsonMessageType___lam__0___closed__1, &l_Lean_Lsp_instToJsonMessageType___lam__0___closed__1_once, _init_l_Lean_Lsp_instToJsonMessageType___lam__0___closed__1);
v___y_299_ = v___x_312_;
goto v___jp_298_;
}
case 1:
{
lean_object* v___x_313_; 
v___x_313_ = lean_obj_once(&l_Lean_Lsp_instToJsonMessageType___lam__0___closed__3, &l_Lean_Lsp_instToJsonMessageType___lam__0___closed__3_once, _init_l_Lean_Lsp_instToJsonMessageType___lam__0___closed__3);
v___y_299_ = v___x_313_;
goto v___jp_298_;
}
case 2:
{
lean_object* v___x_314_; 
v___x_314_ = lean_obj_once(&l_Lean_Lsp_instToJsonMessageType___lam__0___closed__5, &l_Lean_Lsp_instToJsonMessageType___lam__0___closed__5_once, _init_l_Lean_Lsp_instToJsonMessageType___lam__0___closed__5);
v___y_299_ = v___x_314_;
goto v___jp_298_;
}
default: 
{
lean_object* v___x_315_; 
v___x_315_ = lean_obj_once(&l_Lean_Lsp_instToJsonMessageType___lam__0___closed__7, &l_Lean_Lsp_instToJsonMessageType___lam__0___closed__7_once, _init_l_Lean_Lsp_instToJsonMessageType___lam__0___closed__7);
v___y_299_ = v___x_315_;
goto v___jp_298_;
}
}
v___jp_298_:
{
lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
lean_inc(v___y_299_);
v___x_300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_300_, 0, v___x_297_);
lean_ctor_set(v___x_300_, 1, v___y_299_);
v___x_301_ = lean_box(0);
v___x_302_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_302_, 0, v___x_300_);
lean_ctor_set(v___x_302_, 1, v___x_301_);
v___x_303_ = ((lean_object*)(l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__13));
lean_inc_ref(v_message_296_);
v___x_304_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_304_, 0, v_message_296_);
v___x_305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_305_, 0, v___x_303_);
lean_ctor_set(v___x_305_, 1, v___x_304_);
v___x_306_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_306_, 0, v___x_305_);
lean_ctor_set(v___x_306_, 1, v___x_301_);
v___x_307_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_307_, 0, v___x_306_);
lean_ctor_set(v___x_307_, 1, v___x_301_);
v___x_308_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_308_, 0, v___x_302_);
lean_ctor_set(v___x_308_, 1, v___x_307_);
v___x_309_ = ((lean_object*)(l_Lean_Lsp_instToJsonShowMessageParams_toJson___closed__0));
v___x_310_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonShowMessageParams_toJson_spec__0(v___x_308_, v___x_309_);
v___x_311_ = l_Lean_Json_mkObj(v___x_310_);
lean_dec(v___x_310_);
return v___x_311_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonShowMessageParams_toJson___boxed(lean_object* v_x_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = l_Lean_Lsp_instToJsonShowMessageParams_toJson(v_x_316_);
lean_dec_ref(v_x_316_);
return v_res_317_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonMessageActionItem_fromJson___closed__3(void){
_start:
{
uint8_t v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_326_ = 1;
v___x_327_ = ((lean_object*)(l_Lean_Lsp_instFromJsonMessageActionItem_fromJson___closed__2));
v___x_328_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_327_, v___x_326_);
return v___x_328_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonMessageActionItem_fromJson___closed__4(void){
_start:
{
lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_329_ = ((lean_object*)(l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__6));
v___x_330_ = lean_obj_once(&l_Lean_Lsp_instFromJsonMessageActionItem_fromJson___closed__3, &l_Lean_Lsp_instFromJsonMessageActionItem_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonMessageActionItem_fromJson___closed__3);
v___x_331_ = lean_string_append(v___x_330_, v___x_329_);
return v___x_331_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonMessageActionItem_fromJson___closed__6(void){
_start:
{
uint8_t v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_334_ = 1;
v___x_335_ = ((lean_object*)(l_Lean_Lsp_instFromJsonMessageActionItem_fromJson___closed__5));
v___x_336_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_335_, v___x_334_);
return v___x_336_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonMessageActionItem_fromJson___closed__7(void){
_start:
{
lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_337_ = lean_obj_once(&l_Lean_Lsp_instFromJsonMessageActionItem_fromJson___closed__6, &l_Lean_Lsp_instFromJsonMessageActionItem_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonMessageActionItem_fromJson___closed__6);
v___x_338_ = lean_obj_once(&l_Lean_Lsp_instFromJsonMessageActionItem_fromJson___closed__4, &l_Lean_Lsp_instFromJsonMessageActionItem_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonMessageActionItem_fromJson___closed__4);
v___x_339_ = lean_string_append(v___x_338_, v___x_337_);
return v___x_339_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonMessageActionItem_fromJson___closed__8(void){
_start:
{
lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_340_ = ((lean_object*)(l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__11));
v___x_341_ = lean_obj_once(&l_Lean_Lsp_instFromJsonMessageActionItem_fromJson___closed__7, &l_Lean_Lsp_instFromJsonMessageActionItem_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonMessageActionItem_fromJson___closed__7);
v___x_342_ = lean_string_append(v___x_341_, v___x_340_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonMessageActionItem_fromJson(lean_object* v_json_343_){
_start:
{
lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_344_ = ((lean_object*)(l_Lean_Lsp_instFromJsonMessageActionItem_fromJson___closed__0));
v___x_345_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageParams_fromJson_spec__1(v_json_343_, v___x_344_);
if (lean_obj_tag(v___x_345_) == 0)
{
lean_object* v_a_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_355_; 
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
v___x_350_ = lean_obj_once(&l_Lean_Lsp_instFromJsonMessageActionItem_fromJson___closed__8, &l_Lean_Lsp_instFromJsonMessageActionItem_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonMessageActionItem_fromJson___closed__8);
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
lean_object* v_a_364_; lean_object* v___x_366_; uint8_t v_isShared_367_; uint8_t v_isSharedCheck_371_; 
v_a_364_ = lean_ctor_get(v___x_345_, 0);
v_isSharedCheck_371_ = !lean_is_exclusive(v___x_345_);
if (v_isSharedCheck_371_ == 0)
{
v___x_366_ = v___x_345_;
v_isShared_367_ = v_isSharedCheck_371_;
goto v_resetjp_365_;
}
else
{
lean_inc(v_a_364_);
lean_dec(v___x_345_);
v___x_366_ = lean_box(0);
v_isShared_367_ = v_isSharedCheck_371_;
goto v_resetjp_365_;
}
v_resetjp_365_:
{
lean_object* v___x_369_; 
if (v_isShared_367_ == 0)
{
v___x_369_ = v___x_366_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v_a_364_);
v___x_369_ = v_reuseFailAlloc_370_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
return v___x_369_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonMessageActionItem_toJson(lean_object* v_x_374_){
_start:
{
lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_375_ = ((lean_object*)(l_Lean_Lsp_instFromJsonMessageActionItem_fromJson___closed__0));
v___x_376_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_376_, 0, v_x_374_);
v___x_377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_377_, 0, v___x_375_);
lean_ctor_set(v___x_377_, 1, v___x_376_);
v___x_378_ = lean_box(0);
v___x_379_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_379_, 0, v___x_377_);
lean_ctor_set(v___x_379_, 1, v___x_378_);
v___x_380_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_380_, 0, v___x_379_);
lean_ctor_set(v___x_380_, 1, v___x_378_);
v___x_381_ = ((lean_object*)(l_Lean_Lsp_instToJsonShowMessageParams_toJson___closed__0));
v___x_382_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonShowMessageParams_toJson_spec__0(v___x_380_, v___x_381_);
v___x_383_ = l_Lean_Json_mkObj(v___x_382_);
lean_dec(v___x_382_);
return v___x_383_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0_spec__1_spec__2(size_t v_sz_386_, size_t v_i_387_, lean_object* v_bs_388_){
_start:
{
uint8_t v___x_389_; 
v___x_389_ = lean_usize_dec_lt(v_i_387_, v_sz_386_);
if (v___x_389_ == 0)
{
lean_object* v___x_390_; 
v___x_390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_390_, 0, v_bs_388_);
return v___x_390_;
}
else
{
lean_object* v_v_391_; lean_object* v___x_392_; 
v_v_391_ = lean_array_uget_borrowed(v_bs_388_, v_i_387_);
lean_inc(v_v_391_);
v___x_392_ = l_Lean_Lsp_instFromJsonMessageActionItem_fromJson(v_v_391_);
if (lean_obj_tag(v___x_392_) == 0)
{
lean_object* v_a_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_400_; 
lean_dec_ref(v_bs_388_);
v_a_393_ = lean_ctor_get(v___x_392_, 0);
v_isSharedCheck_400_ = !lean_is_exclusive(v___x_392_);
if (v_isSharedCheck_400_ == 0)
{
v___x_395_ = v___x_392_;
v_isShared_396_ = v_isSharedCheck_400_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_a_393_);
lean_dec(v___x_392_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_400_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v___x_398_; 
if (v_isShared_396_ == 0)
{
v___x_398_ = v___x_395_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v_a_393_);
v___x_398_ = v_reuseFailAlloc_399_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
return v___x_398_;
}
}
}
else
{
lean_object* v_a_401_; lean_object* v___x_402_; lean_object* v_bs_x27_403_; size_t v___x_404_; size_t v___x_405_; lean_object* v___x_406_; 
v_a_401_ = lean_ctor_get(v___x_392_, 0);
lean_inc(v_a_401_);
lean_dec_ref_known(v___x_392_, 1);
v___x_402_ = lean_unsigned_to_nat(0u);
v_bs_x27_403_ = lean_array_uset(v_bs_388_, v_i_387_, v___x_402_);
v___x_404_ = ((size_t)1ULL);
v___x_405_ = lean_usize_add(v_i_387_, v___x_404_);
v___x_406_ = lean_array_uset(v_bs_x27_403_, v_i_387_, v_a_401_);
v_i_387_ = v___x_405_;
v_bs_388_ = v___x_406_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_sz_408_, lean_object* v_i_409_, lean_object* v_bs_410_){
_start:
{
size_t v_sz_boxed_411_; size_t v_i_boxed_412_; lean_object* v_res_413_; 
v_sz_boxed_411_ = lean_unbox_usize(v_sz_408_);
lean_dec(v_sz_408_);
v_i_boxed_412_ = lean_unbox_usize(v_i_409_);
lean_dec(v_i_409_);
v_res_413_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0_spec__1_spec__2(v_sz_boxed_411_, v_i_boxed_412_, v_bs_410_);
return v_res_413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0_spec__1(lean_object* v_x_416_){
_start:
{
if (lean_obj_tag(v_x_416_) == 4)
{
lean_object* v_elems_417_; size_t v_sz_418_; size_t v___x_419_; lean_object* v___x_420_; 
v_elems_417_ = lean_ctor_get(v_x_416_, 0);
lean_inc_ref(v_elems_417_);
lean_dec_ref_known(v_x_416_, 1);
v_sz_418_ = lean_array_size(v_elems_417_);
v___x_419_ = ((size_t)0ULL);
v___x_420_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0_spec__1_spec__2(v_sz_418_, v___x_419_, v_elems_417_);
return v___x_420_;
}
else
{
lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_421_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0_spec__1___closed__0));
v___x_422_ = lean_unsigned_to_nat(80u);
v___x_423_ = l_Lean_Json_pretty(v_x_416_, v___x_422_);
v___x_424_ = lean_string_append(v___x_421_, v___x_423_);
lean_dec_ref(v___x_423_);
v___x_425_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0_spec__1___closed__1));
v___x_426_ = lean_string_append(v___x_424_, v___x_425_);
v___x_427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_427_, 0, v___x_426_);
return v___x_427_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0(lean_object* v_x_430_){
_start:
{
if (lean_obj_tag(v_x_430_) == 0)
{
lean_object* v___x_431_; 
v___x_431_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0___closed__0));
return v___x_431_;
}
else
{
lean_object* v___x_432_; 
v___x_432_ = l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0_spec__1(v_x_430_);
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
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson_spec__0(lean_object* v_j_450_, lean_object* v_k_451_){
_start:
{
lean_object* v___x_452_; lean_object* v___x_453_; 
v___x_452_ = l_Lean_Json_getObjValD(v_j_450_, v_k_451_);
v___x_453_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0(v___x_452_);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson_spec__0___boxed(lean_object* v_j_454_, lean_object* v_k_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson_spec__0(v_j_454_, v_k_455_);
lean_dec_ref(v_k_455_);
return v_res_456_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__2(void){
_start:
{
uint8_t v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; 
v___x_462_ = 1;
v___x_463_ = ((lean_object*)(l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__1));
v___x_464_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_463_, v___x_462_);
return v___x_464_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__3(void){
_start:
{
lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_465_ = ((lean_object*)(l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__6));
v___x_466_ = lean_obj_once(&l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__2, &l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__2);
v___x_467_ = lean_string_append(v___x_466_, v___x_465_);
return v___x_467_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_468_ = lean_obj_once(&l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__9, &l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__9);
v___x_469_ = lean_obj_once(&l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__3);
v___x_470_ = lean_string_append(v___x_469_, v___x_468_);
return v___x_470_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__5(void){
_start:
{
lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; 
v___x_471_ = ((lean_object*)(l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__11));
v___x_472_ = lean_obj_once(&l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__4);
v___x_473_ = lean_string_append(v___x_472_, v___x_471_);
return v___x_473_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__6(void){
_start:
{
lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_474_ = lean_obj_once(&l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__15, &l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__15_once, _init_l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__15);
v___x_475_ = lean_obj_once(&l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__3);
v___x_476_ = lean_string_append(v___x_475_, v___x_474_);
return v___x_476_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__7(void){
_start:
{
lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; 
v___x_477_ = ((lean_object*)(l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__11));
v___x_478_ = lean_obj_once(&l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__6, &l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__6);
v___x_479_ = lean_string_append(v___x_478_, v___x_477_);
return v___x_479_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__11(void){
_start:
{
uint8_t v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_484_ = 1;
v___x_485_ = ((lean_object*)(l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__10));
v___x_486_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_485_, v___x_484_);
return v___x_486_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__12(void){
_start:
{
lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_487_ = lean_obj_once(&l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__11, &l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__11);
v___x_488_ = lean_obj_once(&l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__3);
v___x_489_ = lean_string_append(v___x_488_, v___x_487_);
return v___x_489_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__13(void){
_start:
{
lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; 
v___x_490_ = ((lean_object*)(l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__11));
v___x_491_ = lean_obj_once(&l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__12, &l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__12);
v___x_492_ = lean_string_append(v___x_491_, v___x_490_);
return v___x_492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson(lean_object* v_json_493_){
_start:
{
lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_494_ = ((lean_object*)(l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__0));
lean_inc(v_json_493_);
v___x_495_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageParams_fromJson_spec__0(v_json_493_, v___x_494_);
if (lean_obj_tag(v___x_495_) == 0)
{
lean_object* v_a_496_; lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_505_; 
lean_dec(v_json_493_);
v_a_496_ = lean_ctor_get(v___x_495_, 0);
v_isSharedCheck_505_ = !lean_is_exclusive(v___x_495_);
if (v_isSharedCheck_505_ == 0)
{
v___x_498_ = v___x_495_;
v_isShared_499_ = v_isSharedCheck_505_;
goto v_resetjp_497_;
}
else
{
lean_inc(v_a_496_);
lean_dec(v___x_495_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_505_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_503_; 
v___x_500_ = lean_obj_once(&l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__5, &l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__5);
v___x_501_ = lean_string_append(v___x_500_, v_a_496_);
lean_dec(v_a_496_);
if (v_isShared_499_ == 0)
{
lean_ctor_set(v___x_498_, 0, v___x_501_);
v___x_503_ = v___x_498_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v___x_501_);
v___x_503_ = v_reuseFailAlloc_504_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
return v___x_503_;
}
}
}
else
{
if (lean_obj_tag(v___x_495_) == 0)
{
lean_object* v_a_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_513_; 
lean_dec(v_json_493_);
v_a_506_ = lean_ctor_get(v___x_495_, 0);
v_isSharedCheck_513_ = !lean_is_exclusive(v___x_495_);
if (v_isSharedCheck_513_ == 0)
{
v___x_508_ = v___x_495_;
v_isShared_509_ = v_isSharedCheck_513_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_a_506_);
lean_dec(v___x_495_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_513_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v___x_511_; 
if (v_isShared_509_ == 0)
{
lean_ctor_set_tag(v___x_508_, 0);
v___x_511_ = v___x_508_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v_a_506_);
v___x_511_ = v_reuseFailAlloc_512_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
return v___x_511_;
}
}
}
else
{
lean_object* v_a_514_; lean_object* v___x_515_; lean_object* v___x_516_; 
v_a_514_ = lean_ctor_get(v___x_495_, 0);
lean_inc(v_a_514_);
lean_dec_ref_known(v___x_495_, 1);
v___x_515_ = ((lean_object*)(l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__13));
lean_inc(v_json_493_);
v___x_516_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageParams_fromJson_spec__1(v_json_493_, v___x_515_);
if (lean_obj_tag(v___x_516_) == 0)
{
lean_object* v_a_517_; lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_526_; 
lean_dec(v_a_514_);
lean_dec(v_json_493_);
v_a_517_ = lean_ctor_get(v___x_516_, 0);
v_isSharedCheck_526_ = !lean_is_exclusive(v___x_516_);
if (v_isSharedCheck_526_ == 0)
{
v___x_519_ = v___x_516_;
v_isShared_520_ = v_isSharedCheck_526_;
goto v_resetjp_518_;
}
else
{
lean_inc(v_a_517_);
lean_dec(v___x_516_);
v___x_519_ = lean_box(0);
v_isShared_520_ = v_isSharedCheck_526_;
goto v_resetjp_518_;
}
v_resetjp_518_:
{
lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_524_; 
v___x_521_ = lean_obj_once(&l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__7);
v___x_522_ = lean_string_append(v___x_521_, v_a_517_);
lean_dec(v_a_517_);
if (v_isShared_520_ == 0)
{
lean_ctor_set(v___x_519_, 0, v___x_522_);
v___x_524_ = v___x_519_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v___x_522_);
v___x_524_ = v_reuseFailAlloc_525_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
return v___x_524_;
}
}
}
else
{
if (lean_obj_tag(v___x_516_) == 0)
{
lean_object* v_a_527_; lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_534_; 
lean_dec(v_a_514_);
lean_dec(v_json_493_);
v_a_527_ = lean_ctor_get(v___x_516_, 0);
v_isSharedCheck_534_ = !lean_is_exclusive(v___x_516_);
if (v_isSharedCheck_534_ == 0)
{
v___x_529_ = v___x_516_;
v_isShared_530_ = v_isSharedCheck_534_;
goto v_resetjp_528_;
}
else
{
lean_inc(v_a_527_);
lean_dec(v___x_516_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_534_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
lean_object* v___x_532_; 
if (v_isShared_530_ == 0)
{
lean_ctor_set_tag(v___x_529_, 0);
v___x_532_ = v___x_529_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v_a_527_);
v___x_532_ = v_reuseFailAlloc_533_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
return v___x_532_;
}
}
}
else
{
lean_object* v_a_535_; lean_object* v___x_536_; lean_object* v___x_537_; 
v_a_535_ = lean_ctor_get(v___x_516_, 0);
lean_inc(v_a_535_);
lean_dec_ref_known(v___x_516_, 1);
v___x_536_ = ((lean_object*)(l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__8));
v___x_537_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson_spec__0(v_json_493_, v___x_536_);
if (lean_obj_tag(v___x_537_) == 0)
{
lean_object* v_a_538_; lean_object* v___x_540_; uint8_t v_isShared_541_; uint8_t v_isSharedCheck_547_; 
lean_dec(v_a_535_);
lean_dec(v_a_514_);
v_a_538_ = lean_ctor_get(v___x_537_, 0);
v_isSharedCheck_547_ = !lean_is_exclusive(v___x_537_);
if (v_isSharedCheck_547_ == 0)
{
v___x_540_ = v___x_537_;
v_isShared_541_ = v_isSharedCheck_547_;
goto v_resetjp_539_;
}
else
{
lean_inc(v_a_538_);
lean_dec(v___x_537_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_547_;
goto v_resetjp_539_;
}
v_resetjp_539_:
{
lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_545_; 
v___x_542_ = lean_obj_once(&l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__13, &l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__13);
v___x_543_ = lean_string_append(v___x_542_, v_a_538_);
lean_dec(v_a_538_);
if (v_isShared_541_ == 0)
{
lean_ctor_set(v___x_540_, 0, v___x_543_);
v___x_545_ = v___x_540_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v___x_543_);
v___x_545_ = v_reuseFailAlloc_546_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
return v___x_545_;
}
}
}
else
{
if (lean_obj_tag(v___x_537_) == 0)
{
lean_object* v_a_548_; lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_555_; 
lean_dec(v_a_535_);
lean_dec(v_a_514_);
v_a_548_ = lean_ctor_get(v___x_537_, 0);
v_isSharedCheck_555_ = !lean_is_exclusive(v___x_537_);
if (v_isSharedCheck_555_ == 0)
{
v___x_550_ = v___x_537_;
v_isShared_551_ = v_isSharedCheck_555_;
goto v_resetjp_549_;
}
else
{
lean_inc(v_a_548_);
lean_dec(v___x_537_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_555_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
lean_object* v___x_553_; 
if (v_isShared_551_ == 0)
{
lean_ctor_set_tag(v___x_550_, 0);
v___x_553_ = v___x_550_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v_a_548_);
v___x_553_ = v_reuseFailAlloc_554_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
return v___x_553_;
}
}
}
else
{
lean_object* v_a_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_565_; 
v_a_556_ = lean_ctor_get(v___x_537_, 0);
v_isSharedCheck_565_ = !lean_is_exclusive(v___x_537_);
if (v_isSharedCheck_565_ == 0)
{
v___x_558_ = v___x_537_;
v_isShared_559_ = v_isSharedCheck_565_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_a_556_);
lean_dec(v___x_537_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_565_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
lean_object* v___x_560_; uint8_t v___x_561_; lean_object* v___x_563_; 
v___x_560_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_560_, 0, v_a_535_);
lean_ctor_set(v___x_560_, 1, v_a_556_);
v___x_561_ = lean_unbox(v_a_514_);
lean_dec(v_a_514_);
lean_ctor_set_uint8(v___x_560_, sizeof(void*)*2, v___x_561_);
if (v_isShared_559_ == 0)
{
lean_ctor_set(v___x_558_, 0, v___x_560_);
v___x_563_ = v___x_558_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v___x_560_);
v___x_563_ = v_reuseFailAlloc_564_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
return v___x_563_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonShowMessageRequestParams_toJson_spec__0_spec__0_spec__1(size_t v_sz_568_, size_t v_i_569_, lean_object* v_bs_570_){
_start:
{
uint8_t v___x_571_; 
v___x_571_ = lean_usize_dec_lt(v_i_569_, v_sz_568_);
if (v___x_571_ == 0)
{
return v_bs_570_;
}
else
{
lean_object* v_v_572_; lean_object* v___x_573_; lean_object* v_bs_x27_574_; lean_object* v___x_575_; size_t v___x_576_; size_t v___x_577_; lean_object* v___x_578_; 
v_v_572_ = lean_array_uget(v_bs_570_, v_i_569_);
v___x_573_ = lean_unsigned_to_nat(0u);
v_bs_x27_574_ = lean_array_uset(v_bs_570_, v_i_569_, v___x_573_);
v___x_575_ = l_Lean_Lsp_instToJsonMessageActionItem_toJson(v_v_572_);
v___x_576_ = ((size_t)1ULL);
v___x_577_ = lean_usize_add(v_i_569_, v___x_576_);
v___x_578_ = lean_array_uset(v_bs_x27_574_, v_i_569_, v___x_575_);
v_i_569_ = v___x_577_;
v_bs_570_ = v___x_578_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonShowMessageRequestParams_toJson_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_580_, lean_object* v_i_581_, lean_object* v_bs_582_){
_start:
{
size_t v_sz_boxed_583_; size_t v_i_boxed_584_; lean_object* v_res_585_; 
v_sz_boxed_583_ = lean_unbox_usize(v_sz_580_);
lean_dec(v_sz_580_);
v_i_boxed_584_ = lean_unbox_usize(v_i_581_);
lean_dec(v_i_581_);
v_res_585_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonShowMessageRequestParams_toJson_spec__0_spec__0_spec__1(v_sz_boxed_583_, v_i_boxed_584_, v_bs_582_);
return v_res_585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonShowMessageRequestParams_toJson_spec__0_spec__0(lean_object* v_a_586_){
_start:
{
size_t v_sz_587_; size_t v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; 
v_sz_587_ = lean_array_size(v_a_586_);
v___x_588_ = ((size_t)0ULL);
v___x_589_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonShowMessageRequestParams_toJson_spec__0_spec__0_spec__1(v_sz_587_, v___x_588_, v_a_586_);
v___x_590_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_590_, 0, v___x_589_);
return v___x_590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonShowMessageRequestParams_toJson_spec__0(lean_object* v_k_591_, lean_object* v_x_592_){
_start:
{
if (lean_obj_tag(v_x_592_) == 0)
{
lean_object* v___x_593_; 
lean_dec_ref(v_k_591_);
v___x_593_ = lean_box(0);
return v___x_593_;
}
else
{
lean_object* v_val_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; 
v_val_594_ = lean_ctor_get(v_x_592_, 0);
lean_inc(v_val_594_);
lean_dec_ref_known(v_x_592_, 1);
v___x_595_ = l_Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonShowMessageRequestParams_toJson_spec__0_spec__0(v_val_594_);
v___x_596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_596_, 0, v_k_591_);
lean_ctor_set(v___x_596_, 1, v___x_595_);
v___x_597_ = lean_box(0);
v___x_598_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_598_, 0, v___x_596_);
lean_ctor_set(v___x_598_, 1, v___x_597_);
return v___x_598_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonShowMessageRequestParams_toJson(lean_object* v_x_599_){
_start:
{
uint8_t v_type_600_; lean_object* v_message_601_; lean_object* v_actions_x3f_602_; lean_object* v___x_603_; lean_object* v___y_605_; 
v_type_600_ = lean_ctor_get_uint8(v_x_599_, sizeof(void*)*2);
v_message_601_ = lean_ctor_get(v_x_599_, 0);
lean_inc_ref(v_message_601_);
v_actions_x3f_602_ = lean_ctor_get(v_x_599_, 1);
lean_inc(v_actions_x3f_602_);
lean_dec_ref(v_x_599_);
v___x_603_ = ((lean_object*)(l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__0));
switch(v_type_600_)
{
case 0:
{
lean_object* v___x_621_; 
v___x_621_ = lean_obj_once(&l_Lean_Lsp_instToJsonMessageType___lam__0___closed__1, &l_Lean_Lsp_instToJsonMessageType___lam__0___closed__1_once, _init_l_Lean_Lsp_instToJsonMessageType___lam__0___closed__1);
v___y_605_ = v___x_621_;
goto v___jp_604_;
}
case 1:
{
lean_object* v___x_622_; 
v___x_622_ = lean_obj_once(&l_Lean_Lsp_instToJsonMessageType___lam__0___closed__3, &l_Lean_Lsp_instToJsonMessageType___lam__0___closed__3_once, _init_l_Lean_Lsp_instToJsonMessageType___lam__0___closed__3);
v___y_605_ = v___x_622_;
goto v___jp_604_;
}
case 2:
{
lean_object* v___x_623_; 
v___x_623_ = lean_obj_once(&l_Lean_Lsp_instToJsonMessageType___lam__0___closed__5, &l_Lean_Lsp_instToJsonMessageType___lam__0___closed__5_once, _init_l_Lean_Lsp_instToJsonMessageType___lam__0___closed__5);
v___y_605_ = v___x_623_;
goto v___jp_604_;
}
default: 
{
lean_object* v___x_624_; 
v___x_624_ = lean_obj_once(&l_Lean_Lsp_instToJsonMessageType___lam__0___closed__7, &l_Lean_Lsp_instToJsonMessageType___lam__0___closed__7_once, _init_l_Lean_Lsp_instToJsonMessageType___lam__0___closed__7);
v___y_605_ = v___x_624_;
goto v___jp_604_;
}
}
v___jp_604_:
{
lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; 
lean_inc(v___y_605_);
v___x_606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_606_, 0, v___x_603_);
lean_ctor_set(v___x_606_, 1, v___y_605_);
v___x_607_ = lean_box(0);
v___x_608_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_608_, 0, v___x_606_);
lean_ctor_set(v___x_608_, 1, v___x_607_);
v___x_609_ = ((lean_object*)(l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__13));
v___x_610_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_610_, 0, v_message_601_);
v___x_611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_611_, 0, v___x_609_);
lean_ctor_set(v___x_611_, 1, v___x_610_);
v___x_612_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_612_, 0, v___x_611_);
lean_ctor_set(v___x_612_, 1, v___x_607_);
v___x_613_ = ((lean_object*)(l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__8));
v___x_614_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonShowMessageRequestParams_toJson_spec__0(v___x_613_, v_actions_x3f_602_);
v___x_615_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_615_, 0, v___x_614_);
lean_ctor_set(v___x_615_, 1, v___x_607_);
v___x_616_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_616_, 0, v___x_612_);
lean_ctor_set(v___x_616_, 1, v___x_615_);
v___x_617_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_617_, 0, v___x_608_);
lean_ctor_set(v___x_617_, 1, v___x_616_);
v___x_618_ = ((lean_object*)(l_Lean_Lsp_instToJsonShowMessageParams_toJson___closed__0));
v___x_619_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonShowMessageParams_toJson_spec__0(v___x_617_, v___x_618_);
v___x_620_ = l_Lean_Json_mkObj(v___x_619_);
lean_dec(v___x_619_);
return v___x_620_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonShowMessageResponse___aux__1(lean_object* v_a_627_){
_start:
{
lean_object* v___x_628_; lean_object* v___x_629_; 
v___x_628_ = ((lean_object*)(l_Lean_Lsp_instFromJsonMessageActionItem___closed__0));
v___x_629_ = l_Lean_Option_fromJson_x3f___redArg(v___x_628_, v_a_627_);
return v___x_629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Lsp_instFromJsonShowMessageResponse_spec__0(lean_object* v_x_632_){
_start:
{
if (lean_obj_tag(v_x_632_) == 0)
{
lean_object* v___x_633_; 
v___x_633_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Lsp_instFromJsonShowMessageResponse_spec__0___closed__0));
return v___x_633_;
}
else
{
lean_object* v___x_634_; 
v___x_634_ = l_Lean_Lsp_instFromJsonMessageActionItem_fromJson(v_x_632_);
if (lean_obj_tag(v___x_634_) == 0)
{
lean_object* v_a_635_; lean_object* v___x_637_; uint8_t v_isShared_638_; uint8_t v_isSharedCheck_642_; 
v_a_635_ = lean_ctor_get(v___x_634_, 0);
v_isSharedCheck_642_ = !lean_is_exclusive(v___x_634_);
if (v_isSharedCheck_642_ == 0)
{
v___x_637_ = v___x_634_;
v_isShared_638_ = v_isSharedCheck_642_;
goto v_resetjp_636_;
}
else
{
lean_inc(v_a_635_);
lean_dec(v___x_634_);
v___x_637_ = lean_box(0);
v_isShared_638_ = v_isSharedCheck_642_;
goto v_resetjp_636_;
}
v_resetjp_636_:
{
lean_object* v___x_640_; 
if (v_isShared_638_ == 0)
{
v___x_640_ = v___x_637_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v_a_635_);
v___x_640_ = v_reuseFailAlloc_641_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
return v___x_640_;
}
}
}
else
{
lean_object* v_a_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_651_; 
v_a_643_ = lean_ctor_get(v___x_634_, 0);
v_isSharedCheck_651_ = !lean_is_exclusive(v___x_634_);
if (v_isSharedCheck_651_ == 0)
{
v___x_645_ = v___x_634_;
v_isShared_646_ = v_isSharedCheck_651_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_a_643_);
lean_dec(v___x_634_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_651_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v___x_647_; lean_object* v___x_649_; 
v___x_647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_647_, 0, v_a_643_);
if (v_isShared_646_ == 0)
{
lean_ctor_set(v___x_645_, 0, v___x_647_);
v___x_649_ = v___x_645_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v___x_647_);
v___x_649_ = v_reuseFailAlloc_650_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
return v___x_649_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonShowMessageResponse___aux__1(lean_object* v_a_654_){
_start:
{
lean_object* v___x_655_; lean_object* v___x_656_; 
v___x_655_ = ((lean_object*)(l_Lean_Lsp_instToJsonMessageActionItem___closed__0));
v___x_656_ = l_Lean_Option_toJson___redArg(v___x_655_, v_a_654_);
return v___x_656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_toJson___at___00Lean_Lsp_instToJsonShowMessageResponse_spec__0(lean_object* v_x_657_){
_start:
{
if (lean_obj_tag(v_x_657_) == 0)
{
lean_object* v___x_658_; 
v___x_658_ = lean_box(0);
return v___x_658_;
}
else
{
lean_object* v_val_659_; lean_object* v___x_660_; 
v_val_659_ = lean_ctor_get(v_x_657_, 0);
lean_inc(v_val_659_);
lean_dec_ref_known(v_x_657_, 1);
v___x_660_ = l_Lean_Lsp_instToJsonMessageActionItem_toJson(v_val_659_);
return v___x_660_;
}
}
}
lean_object* runtime_initialize_Lean_Data_Json_FromToJson_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_Lsp_Window(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Data_Json_FromToJson_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Data_Lsp_Window(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Data_Json_FromToJson_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_Lsp_Window(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_Json_FromToJson_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Lsp_Window(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Data_Lsp_Window(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Data_Lsp_Window(builtin);
}
#ifdef __cplusplus
}
#endif

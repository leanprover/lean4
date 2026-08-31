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
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_ctorElim___redArg(lean_object* v_k_9_){
_start:
{
lean_inc(v_k_9_);
return v_k_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_ctorElim___redArg___boxed(lean_object* v_k_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = l_Lean_Lsp_MessageType_ctorElim___redArg(v_k_10_);
lean_dec(v_k_10_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_ctorElim(lean_object* v_motive_12_, lean_object* v_ctorIdx_13_, uint8_t v_t_14_, lean_object* v_h_15_, lean_object* v_k_16_){
_start:
{
lean_inc(v_k_16_);
return v_k_16_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_ctorElim___boxed(lean_object* v_motive_17_, lean_object* v_ctorIdx_18_, lean_object* v_t_19_, lean_object* v_h_20_, lean_object* v_k_21_){
_start:
{
uint8_t v_t_boxed_22_; lean_object* v_res_23_; 
v_t_boxed_22_ = lean_unbox(v_t_19_);
v_res_23_ = l_Lean_Lsp_MessageType_ctorElim(v_motive_17_, v_ctorIdx_18_, v_t_boxed_22_, v_h_20_, v_k_21_);
lean_dec(v_k_21_);
lean_dec(v_ctorIdx_18_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_error_elim___redArg(lean_object* v_error_24_){
_start:
{
lean_inc(v_error_24_);
return v_error_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_error_elim___redArg___boxed(lean_object* v_error_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Lean_Lsp_MessageType_error_elim___redArg(v_error_25_);
lean_dec(v_error_25_);
return v_res_26_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_error_elim(lean_object* v_motive_27_, uint8_t v_t_28_, lean_object* v_h_29_, lean_object* v_error_30_){
_start:
{
lean_inc(v_error_30_);
return v_error_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_error_elim___boxed(lean_object* v_motive_31_, lean_object* v_t_32_, lean_object* v_h_33_, lean_object* v_error_34_){
_start:
{
uint8_t v_t_boxed_35_; lean_object* v_res_36_; 
v_t_boxed_35_ = lean_unbox(v_t_32_);
v_res_36_ = l_Lean_Lsp_MessageType_error_elim(v_motive_31_, v_t_boxed_35_, v_h_33_, v_error_34_);
lean_dec(v_error_34_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_warning_elim___redArg(lean_object* v_warning_37_){
_start:
{
lean_inc(v_warning_37_);
return v_warning_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_warning_elim___redArg___boxed(lean_object* v_warning_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = l_Lean_Lsp_MessageType_warning_elim___redArg(v_warning_38_);
lean_dec(v_warning_38_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_warning_elim(lean_object* v_motive_40_, uint8_t v_t_41_, lean_object* v_h_42_, lean_object* v_warning_43_){
_start:
{
lean_inc(v_warning_43_);
return v_warning_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_warning_elim___boxed(lean_object* v_motive_44_, lean_object* v_t_45_, lean_object* v_h_46_, lean_object* v_warning_47_){
_start:
{
uint8_t v_t_boxed_48_; lean_object* v_res_49_; 
v_t_boxed_48_ = lean_unbox(v_t_45_);
v_res_49_ = l_Lean_Lsp_MessageType_warning_elim(v_motive_44_, v_t_boxed_48_, v_h_46_, v_warning_47_);
lean_dec(v_warning_47_);
return v_res_49_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_info_elim___redArg(lean_object* v_info_50_){
_start:
{
lean_inc(v_info_50_);
return v_info_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_info_elim___redArg___boxed(lean_object* v_info_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = l_Lean_Lsp_MessageType_info_elim___redArg(v_info_51_);
lean_dec(v_info_51_);
return v_res_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_info_elim(lean_object* v_motive_53_, uint8_t v_t_54_, lean_object* v_h_55_, lean_object* v_info_56_){
_start:
{
lean_inc(v_info_56_);
return v_info_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_info_elim___boxed(lean_object* v_motive_57_, lean_object* v_t_58_, lean_object* v_h_59_, lean_object* v_info_60_){
_start:
{
uint8_t v_t_boxed_61_; lean_object* v_res_62_; 
v_t_boxed_61_ = lean_unbox(v_t_58_);
v_res_62_ = l_Lean_Lsp_MessageType_info_elim(v_motive_57_, v_t_boxed_61_, v_h_59_, v_info_60_);
lean_dec(v_info_60_);
return v_res_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_log_elim___redArg(lean_object* v_log_63_){
_start:
{
lean_inc(v_log_63_);
return v_log_63_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_log_elim___redArg___boxed(lean_object* v_log_64_){
_start:
{
lean_object* v_res_65_; 
v_res_65_ = l_Lean_Lsp_MessageType_log_elim___redArg(v_log_64_);
lean_dec(v_log_64_);
return v_res_65_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_log_elim(lean_object* v_motive_66_, uint8_t v_t_67_, lean_object* v_h_68_, lean_object* v_log_69_){
_start:
{
lean_inc(v_log_69_);
return v_log_69_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_log_elim___boxed(lean_object* v_motive_70_, lean_object* v_t_71_, lean_object* v_h_72_, lean_object* v_log_73_){
_start:
{
uint8_t v_t_boxed_74_; lean_object* v_res_75_; 
v_t_boxed_74_ = lean_unbox(v_t_71_);
v_res_75_ = l_Lean_Lsp_MessageType_log_elim(v_motive_70_, v_t_boxed_74_, v_h_72_, v_log_73_);
lean_dec(v_log_73_);
return v_res_75_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonMessageType___lam__0___closed__2(void){
_start:
{
lean_object* v_natZero_79_; lean_object* v_intZero_80_; 
v_natZero_79_ = lean_unsigned_to_nat(0u);
v_intZero_80_ = lean_nat_to_int(v_natZero_79_);
return v_intZero_80_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonMessageType___lam__0(lean_object* v_x_93_){
_start:
{
if (lean_obj_tag(v_x_93_) == 2)
{
lean_object* v_n_96_; lean_object* v_mantissa_97_; lean_object* v_exponent_98_; lean_object* v_natZero_99_; lean_object* v_intZero_100_; uint8_t v_isNeg_101_; 
v_n_96_ = lean_ctor_get(v_x_93_, 0);
v_mantissa_97_ = lean_ctor_get(v_n_96_, 0);
v_exponent_98_ = lean_ctor_get(v_n_96_, 1);
v_natZero_99_ = lean_unsigned_to_nat(0u);
v_intZero_100_ = lean_obj_once(&l_Lean_Lsp_instFromJsonMessageType___lam__0___closed__2, &l_Lean_Lsp_instFromJsonMessageType___lam__0___closed__2_once, _init_l_Lean_Lsp_instFromJsonMessageType___lam__0___closed__2);
v_isNeg_101_ = lean_int_dec_lt(v_mantissa_97_, v_intZero_100_);
if (v_isNeg_101_ == 0)
{
lean_object* v_a_102_; lean_object* v___x_103_; uint8_t v___x_104_; 
v_a_102_ = lean_nat_abs(v_mantissa_97_);
v___x_103_ = lean_unsigned_to_nat(1u);
v___x_104_ = lean_nat_dec_eq(v_a_102_, v___x_103_);
if (v___x_104_ == 0)
{
lean_object* v___x_105_; uint8_t v___x_106_; 
v___x_105_ = lean_unsigned_to_nat(2u);
v___x_106_ = lean_nat_dec_eq(v_a_102_, v___x_105_);
if (v___x_106_ == 0)
{
lean_object* v___x_107_; uint8_t v___x_108_; 
v___x_107_ = lean_unsigned_to_nat(3u);
v___x_108_ = lean_nat_dec_eq(v_a_102_, v___x_107_);
if (v___x_108_ == 0)
{
lean_object* v___x_109_; uint8_t v___x_110_; 
v___x_109_ = lean_unsigned_to_nat(4u);
v___x_110_ = lean_nat_dec_eq(v_a_102_, v___x_109_);
lean_dec(v_a_102_);
if (v___x_110_ == 0)
{
goto v___jp_94_;
}
else
{
uint8_t v___x_111_; 
v___x_111_ = lean_nat_dec_eq(v_exponent_98_, v_natZero_99_);
if (v___x_111_ == 0)
{
goto v___jp_94_;
}
else
{
lean_object* v___x_112_; 
v___x_112_ = ((lean_object*)(l_Lean_Lsp_instFromJsonMessageType___lam__0___closed__3));
return v___x_112_;
}
}
}
else
{
uint8_t v___x_113_; 
lean_dec(v_a_102_);
v___x_113_ = lean_nat_dec_eq(v_exponent_98_, v_natZero_99_);
if (v___x_113_ == 0)
{
goto v___jp_94_;
}
else
{
lean_object* v___x_114_; 
v___x_114_ = ((lean_object*)(l_Lean_Lsp_instFromJsonMessageType___lam__0___closed__4));
return v___x_114_;
}
}
}
else
{
uint8_t v___x_115_; 
lean_dec(v_a_102_);
v___x_115_ = lean_nat_dec_eq(v_exponent_98_, v_natZero_99_);
if (v___x_115_ == 0)
{
goto v___jp_94_;
}
else
{
lean_object* v___x_116_; 
v___x_116_ = ((lean_object*)(l_Lean_Lsp_instFromJsonMessageType___lam__0___closed__5));
return v___x_116_;
}
}
}
else
{
uint8_t v___x_117_; 
lean_dec(v_a_102_);
v___x_117_ = lean_nat_dec_eq(v_exponent_98_, v_natZero_99_);
if (v___x_117_ == 0)
{
goto v___jp_94_;
}
else
{
lean_object* v___x_118_; 
v___x_118_ = ((lean_object*)(l_Lean_Lsp_instFromJsonMessageType___lam__0___closed__6));
return v___x_118_;
}
}
}
else
{
goto v___jp_94_;
}
}
else
{
goto v___jp_94_;
}
v___jp_94_:
{
lean_object* v___x_95_; 
v___x_95_ = ((lean_object*)(l_Lean_Lsp_instFromJsonMessageType___lam__0___closed__1));
return v___x_95_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonMessageType___lam__0___boxed(lean_object* v_x_119_){
_start:
{
lean_object* v_res_120_; 
v_res_120_ = l_Lean_Lsp_instFromJsonMessageType___lam__0(v_x_119_);
lean_dec(v_x_119_);
return v_res_120_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonMessageType___lam__0___closed__0(void){
_start:
{
lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_123_ = lean_unsigned_to_nat(1u);
v___x_124_ = l_Lean_JsonNumber_fromNat(v___x_123_);
return v___x_124_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonMessageType___lam__0___closed__1(void){
_start:
{
lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_125_ = lean_obj_once(&l_Lean_Lsp_instToJsonMessageType___lam__0___closed__0, &l_Lean_Lsp_instToJsonMessageType___lam__0___closed__0_once, _init_l_Lean_Lsp_instToJsonMessageType___lam__0___closed__0);
v___x_126_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_126_, 0, v___x_125_);
return v___x_126_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonMessageType___lam__0___closed__2(void){
_start:
{
lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_127_ = lean_unsigned_to_nat(2u);
v___x_128_ = l_Lean_JsonNumber_fromNat(v___x_127_);
return v___x_128_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonMessageType___lam__0___closed__3(void){
_start:
{
lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_129_ = lean_obj_once(&l_Lean_Lsp_instToJsonMessageType___lam__0___closed__2, &l_Lean_Lsp_instToJsonMessageType___lam__0___closed__2_once, _init_l_Lean_Lsp_instToJsonMessageType___lam__0___closed__2);
v___x_130_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_130_, 0, v___x_129_);
return v___x_130_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonMessageType___lam__0___closed__4(void){
_start:
{
lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_131_ = lean_unsigned_to_nat(3u);
v___x_132_ = l_Lean_JsonNumber_fromNat(v___x_131_);
return v___x_132_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonMessageType___lam__0___closed__5(void){
_start:
{
lean_object* v___x_133_; lean_object* v___x_134_; 
v___x_133_ = lean_obj_once(&l_Lean_Lsp_instToJsonMessageType___lam__0___closed__4, &l_Lean_Lsp_instToJsonMessageType___lam__0___closed__4_once, _init_l_Lean_Lsp_instToJsonMessageType___lam__0___closed__4);
v___x_134_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_134_, 0, v___x_133_);
return v___x_134_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonMessageType___lam__0___closed__6(void){
_start:
{
lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_135_ = lean_unsigned_to_nat(4u);
v___x_136_ = l_Lean_JsonNumber_fromNat(v___x_135_);
return v___x_136_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonMessageType___lam__0___closed__7(void){
_start:
{
lean_object* v___x_137_; lean_object* v___x_138_; 
v___x_137_ = lean_obj_once(&l_Lean_Lsp_instToJsonMessageType___lam__0___closed__6, &l_Lean_Lsp_instToJsonMessageType___lam__0___closed__6_once, _init_l_Lean_Lsp_instToJsonMessageType___lam__0___closed__6);
v___x_138_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_138_, 0, v___x_137_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonMessageType___lam__0(uint8_t v_x_139_){
_start:
{
switch(v_x_139_)
{
case 0:
{
lean_object* v___x_140_; 
v___x_140_ = lean_obj_once(&l_Lean_Lsp_instToJsonMessageType___lam__0___closed__1, &l_Lean_Lsp_instToJsonMessageType___lam__0___closed__1_once, _init_l_Lean_Lsp_instToJsonMessageType___lam__0___closed__1);
return v___x_140_;
}
case 1:
{
lean_object* v___x_141_; 
v___x_141_ = lean_obj_once(&l_Lean_Lsp_instToJsonMessageType___lam__0___closed__3, &l_Lean_Lsp_instToJsonMessageType___lam__0___closed__3_once, _init_l_Lean_Lsp_instToJsonMessageType___lam__0___closed__3);
return v___x_141_;
}
case 2:
{
lean_object* v___x_142_; 
v___x_142_ = lean_obj_once(&l_Lean_Lsp_instToJsonMessageType___lam__0___closed__5, &l_Lean_Lsp_instToJsonMessageType___lam__0___closed__5_once, _init_l_Lean_Lsp_instToJsonMessageType___lam__0___closed__5);
return v___x_142_;
}
default: 
{
lean_object* v___x_143_; 
v___x_143_ = lean_obj_once(&l_Lean_Lsp_instToJsonMessageType___lam__0___closed__7, &l_Lean_Lsp_instToJsonMessageType___lam__0___closed__7_once, _init_l_Lean_Lsp_instToJsonMessageType___lam__0___closed__7);
return v___x_143_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonMessageType___lam__0___boxed(lean_object* v_x_144_){
_start:
{
uint8_t v_x_106__boxed_145_; lean_object* v_res_146_; 
v_x_106__boxed_145_ = lean_unbox(v_x_144_);
v_res_146_ = l_Lean_Lsp_instToJsonMessageType___lam__0(v_x_106__boxed_145_);
return v_res_146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageParams_fromJson_spec__0(lean_object* v_j_149_, lean_object* v_k_150_){
_start:
{
lean_object* v___x_153_; 
v___x_153_ = l_Lean_Json_getObjValD(v_j_149_, v_k_150_);
if (lean_obj_tag(v___x_153_) == 2)
{
lean_object* v_n_154_; lean_object* v_mantissa_155_; lean_object* v_exponent_156_; lean_object* v_natZero_157_; lean_object* v_intZero_158_; uint8_t v_isNeg_159_; 
v_n_154_ = lean_ctor_get(v___x_153_, 0);
lean_inc_ref(v_n_154_);
lean_dec_ref_known(v___x_153_, 1);
v_mantissa_155_ = lean_ctor_get(v_n_154_, 0);
lean_inc(v_mantissa_155_);
v_exponent_156_ = lean_ctor_get(v_n_154_, 1);
lean_inc(v_exponent_156_);
lean_dec_ref(v_n_154_);
v_natZero_157_ = lean_unsigned_to_nat(0u);
v_intZero_158_ = lean_obj_once(&l_Lean_Lsp_instFromJsonMessageType___lam__0___closed__2, &l_Lean_Lsp_instFromJsonMessageType___lam__0___closed__2_once, _init_l_Lean_Lsp_instFromJsonMessageType___lam__0___closed__2);
v_isNeg_159_ = lean_int_dec_lt(v_mantissa_155_, v_intZero_158_);
if (v_isNeg_159_ == 0)
{
lean_object* v_a_160_; lean_object* v___x_161_; uint8_t v___x_162_; 
v_a_160_ = lean_nat_abs(v_mantissa_155_);
lean_dec(v_mantissa_155_);
v___x_161_ = lean_unsigned_to_nat(1u);
v___x_162_ = lean_nat_dec_eq(v_a_160_, v___x_161_);
if (v___x_162_ == 0)
{
lean_object* v___x_163_; uint8_t v___x_164_; 
v___x_163_ = lean_unsigned_to_nat(2u);
v___x_164_ = lean_nat_dec_eq(v_a_160_, v___x_163_);
if (v___x_164_ == 0)
{
lean_object* v___x_165_; uint8_t v___x_166_; 
v___x_165_ = lean_unsigned_to_nat(3u);
v___x_166_ = lean_nat_dec_eq(v_a_160_, v___x_165_);
if (v___x_166_ == 0)
{
lean_object* v___x_167_; uint8_t v___x_168_; 
v___x_167_ = lean_unsigned_to_nat(4u);
v___x_168_ = lean_nat_dec_eq(v_a_160_, v___x_167_);
lean_dec(v_a_160_);
if (v___x_168_ == 0)
{
lean_dec(v_exponent_156_);
goto v___jp_151_;
}
else
{
uint8_t v___x_169_; 
v___x_169_ = lean_nat_dec_eq(v_exponent_156_, v_natZero_157_);
lean_dec(v_exponent_156_);
if (v___x_169_ == 0)
{
goto v___jp_151_;
}
else
{
lean_object* v___x_170_; 
v___x_170_ = ((lean_object*)(l_Lean_Lsp_instFromJsonMessageType___lam__0___closed__3));
return v___x_170_;
}
}
}
else
{
uint8_t v___x_171_; 
lean_dec(v_a_160_);
v___x_171_ = lean_nat_dec_eq(v_exponent_156_, v_natZero_157_);
lean_dec(v_exponent_156_);
if (v___x_171_ == 0)
{
goto v___jp_151_;
}
else
{
lean_object* v___x_172_; 
v___x_172_ = ((lean_object*)(l_Lean_Lsp_instFromJsonMessageType___lam__0___closed__4));
return v___x_172_;
}
}
}
else
{
uint8_t v___x_173_; 
lean_dec(v_a_160_);
v___x_173_ = lean_nat_dec_eq(v_exponent_156_, v_natZero_157_);
lean_dec(v_exponent_156_);
if (v___x_173_ == 0)
{
goto v___jp_151_;
}
else
{
lean_object* v___x_174_; 
v___x_174_ = ((lean_object*)(l_Lean_Lsp_instFromJsonMessageType___lam__0___closed__5));
return v___x_174_;
}
}
}
else
{
uint8_t v___x_175_; 
lean_dec(v_a_160_);
v___x_175_ = lean_nat_dec_eq(v_exponent_156_, v_natZero_157_);
lean_dec(v_exponent_156_);
if (v___x_175_ == 0)
{
goto v___jp_151_;
}
else
{
lean_object* v___x_176_; 
v___x_176_ = ((lean_object*)(l_Lean_Lsp_instFromJsonMessageType___lam__0___closed__6));
return v___x_176_;
}
}
}
else
{
lean_dec(v_exponent_156_);
lean_dec(v_mantissa_155_);
goto v___jp_151_;
}
}
else
{
lean_dec(v___x_153_);
goto v___jp_151_;
}
v___jp_151_:
{
lean_object* v___x_152_; 
v___x_152_ = ((lean_object*)(l_Lean_Lsp_instFromJsonMessageType___lam__0___closed__1));
return v___x_152_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageParams_fromJson_spec__0___boxed(lean_object* v_j_177_, lean_object* v_k_178_){
_start:
{
lean_object* v_res_179_; 
v_res_179_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageParams_fromJson_spec__0(v_j_177_, v_k_178_);
lean_dec_ref(v_k_178_);
return v_res_179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageParams_fromJson_spec__1(lean_object* v_j_180_, lean_object* v_k_181_){
_start:
{
lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_182_ = l_Lean_Json_getObjValD(v_j_180_, v_k_181_);
v___x_183_ = l_Lean_Json_getStr_x3f(v___x_182_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageParams_fromJson_spec__1___boxed(lean_object* v_j_184_, lean_object* v_k_185_){
_start:
{
lean_object* v_res_186_; 
v_res_186_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageParams_fromJson_spec__1(v_j_184_, v_k_185_);
lean_dec_ref(v_k_185_);
return v_res_186_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__5(void){
_start:
{
uint8_t v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_195_ = 1;
v___x_196_ = ((lean_object*)(l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__4));
v___x_197_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_196_, v___x_195_);
return v___x_197_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__7(void){
_start:
{
lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_199_ = ((lean_object*)(l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__6));
v___x_200_ = lean_obj_once(&l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__5, &l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__5);
v___x_201_ = lean_string_append(v___x_200_, v___x_199_);
return v___x_201_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__9(void){
_start:
{
uint8_t v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; 
v___x_204_ = 1;
v___x_205_ = ((lean_object*)(l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__8));
v___x_206_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_205_, v___x_204_);
return v___x_206_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__10(void){
_start:
{
lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; 
v___x_207_ = lean_obj_once(&l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__9, &l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__9);
v___x_208_ = lean_obj_once(&l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__7);
v___x_209_ = lean_string_append(v___x_208_, v___x_207_);
return v___x_209_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__12(void){
_start:
{
lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; 
v___x_211_ = ((lean_object*)(l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__11));
v___x_212_ = lean_obj_once(&l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__10, &l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__10);
v___x_213_ = lean_string_append(v___x_212_, v___x_211_);
return v___x_213_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__15(void){
_start:
{
uint8_t v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; 
v___x_217_ = 1;
v___x_218_ = ((lean_object*)(l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__14));
v___x_219_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_218_, v___x_217_);
return v___x_219_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__16(void){
_start:
{
lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_220_ = lean_obj_once(&l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__15, &l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__15_once, _init_l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__15);
v___x_221_ = lean_obj_once(&l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__7);
v___x_222_ = lean_string_append(v___x_221_, v___x_220_);
return v___x_222_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__17(void){
_start:
{
lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; 
v___x_223_ = ((lean_object*)(l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__11));
v___x_224_ = lean_obj_once(&l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__16, &l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__16_once, _init_l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__16);
v___x_225_ = lean_string_append(v___x_224_, v___x_223_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonShowMessageParams_fromJson(lean_object* v_json_226_){
_start:
{
lean_object* v___x_227_; lean_object* v___x_228_; 
v___x_227_ = ((lean_object*)(l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__0));
lean_inc(v_json_226_);
v___x_228_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageParams_fromJson_spec__0(v_json_226_, v___x_227_);
if (lean_obj_tag(v___x_228_) == 0)
{
lean_object* v_a_229_; lean_object* v___x_231_; uint8_t v_isShared_232_; uint8_t v_isSharedCheck_238_; 
lean_dec(v_json_226_);
v_a_229_ = lean_ctor_get(v___x_228_, 0);
v_isSharedCheck_238_ = !lean_is_exclusive(v___x_228_);
if (v_isSharedCheck_238_ == 0)
{
v___x_231_ = v___x_228_;
v_isShared_232_ = v_isSharedCheck_238_;
goto v_resetjp_230_;
}
else
{
lean_inc(v_a_229_);
lean_dec(v___x_228_);
v___x_231_ = lean_box(0);
v_isShared_232_ = v_isSharedCheck_238_;
goto v_resetjp_230_;
}
v_resetjp_230_:
{
lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_236_; 
v___x_233_ = lean_obj_once(&l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__12, &l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__12);
v___x_234_ = lean_string_append(v___x_233_, v_a_229_);
lean_dec(v_a_229_);
if (v_isShared_232_ == 0)
{
lean_ctor_set(v___x_231_, 0, v___x_234_);
v___x_236_ = v___x_231_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(0, 1, 0);
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
else
{
if (lean_obj_tag(v___x_228_) == 0)
{
lean_object* v_a_239_; lean_object* v___x_241_; uint8_t v_isShared_242_; uint8_t v_isSharedCheck_246_; 
lean_dec(v_json_226_);
v_a_239_ = lean_ctor_get(v___x_228_, 0);
v_isSharedCheck_246_ = !lean_is_exclusive(v___x_228_);
if (v_isSharedCheck_246_ == 0)
{
v___x_241_ = v___x_228_;
v_isShared_242_ = v_isSharedCheck_246_;
goto v_resetjp_240_;
}
else
{
lean_inc(v_a_239_);
lean_dec(v___x_228_);
v___x_241_ = lean_box(0);
v_isShared_242_ = v_isSharedCheck_246_;
goto v_resetjp_240_;
}
v_resetjp_240_:
{
lean_object* v___x_244_; 
if (v_isShared_242_ == 0)
{
lean_ctor_set_tag(v___x_241_, 0);
v___x_244_ = v___x_241_;
goto v_reusejp_243_;
}
else
{
lean_object* v_reuseFailAlloc_245_; 
v_reuseFailAlloc_245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_245_, 0, v_a_239_);
v___x_244_ = v_reuseFailAlloc_245_;
goto v_reusejp_243_;
}
v_reusejp_243_:
{
return v___x_244_;
}
}
}
else
{
lean_object* v_a_247_; lean_object* v___x_248_; lean_object* v___x_249_; 
v_a_247_ = lean_ctor_get(v___x_228_, 0);
lean_inc(v_a_247_);
lean_dec_ref_known(v___x_228_, 1);
v___x_248_ = ((lean_object*)(l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__13));
v___x_249_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageParams_fromJson_spec__1(v_json_226_, v___x_248_);
if (lean_obj_tag(v___x_249_) == 0)
{
lean_object* v_a_250_; lean_object* v___x_252_; uint8_t v_isShared_253_; uint8_t v_isSharedCheck_259_; 
lean_dec(v_a_247_);
v_a_250_ = lean_ctor_get(v___x_249_, 0);
v_isSharedCheck_259_ = !lean_is_exclusive(v___x_249_);
if (v_isSharedCheck_259_ == 0)
{
v___x_252_ = v___x_249_;
v_isShared_253_ = v_isSharedCheck_259_;
goto v_resetjp_251_;
}
else
{
lean_inc(v_a_250_);
lean_dec(v___x_249_);
v___x_252_ = lean_box(0);
v_isShared_253_ = v_isSharedCheck_259_;
goto v_resetjp_251_;
}
v_resetjp_251_:
{
lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_257_; 
v___x_254_ = lean_obj_once(&l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__17, &l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__17_once, _init_l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__17);
v___x_255_ = lean_string_append(v___x_254_, v_a_250_);
lean_dec(v_a_250_);
if (v_isShared_253_ == 0)
{
lean_ctor_set(v___x_252_, 0, v___x_255_);
v___x_257_ = v___x_252_;
goto v_reusejp_256_;
}
else
{
lean_object* v_reuseFailAlloc_258_; 
v_reuseFailAlloc_258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_258_, 0, v___x_255_);
v___x_257_ = v_reuseFailAlloc_258_;
goto v_reusejp_256_;
}
v_reusejp_256_:
{
return v___x_257_;
}
}
}
else
{
if (lean_obj_tag(v___x_249_) == 0)
{
lean_object* v_a_260_; lean_object* v___x_262_; uint8_t v_isShared_263_; uint8_t v_isSharedCheck_267_; 
lean_dec(v_a_247_);
v_a_260_ = lean_ctor_get(v___x_249_, 0);
v_isSharedCheck_267_ = !lean_is_exclusive(v___x_249_);
if (v_isSharedCheck_267_ == 0)
{
v___x_262_ = v___x_249_;
v_isShared_263_ = v_isSharedCheck_267_;
goto v_resetjp_261_;
}
else
{
lean_inc(v_a_260_);
lean_dec(v___x_249_);
v___x_262_ = lean_box(0);
v_isShared_263_ = v_isSharedCheck_267_;
goto v_resetjp_261_;
}
v_resetjp_261_:
{
lean_object* v___x_265_; 
if (v_isShared_263_ == 0)
{
lean_ctor_set_tag(v___x_262_, 0);
v___x_265_ = v___x_262_;
goto v_reusejp_264_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v_a_260_);
v___x_265_ = v_reuseFailAlloc_266_;
goto v_reusejp_264_;
}
v_reusejp_264_:
{
return v___x_265_;
}
}
}
else
{
lean_object* v_a_268_; lean_object* v___x_270_; uint8_t v_isShared_271_; uint8_t v_isSharedCheck_277_; 
v_a_268_ = lean_ctor_get(v___x_249_, 0);
v_isSharedCheck_277_ = !lean_is_exclusive(v___x_249_);
if (v_isSharedCheck_277_ == 0)
{
v___x_270_ = v___x_249_;
v_isShared_271_ = v_isSharedCheck_277_;
goto v_resetjp_269_;
}
else
{
lean_inc(v_a_268_);
lean_dec(v___x_249_);
v___x_270_ = lean_box(0);
v_isShared_271_ = v_isSharedCheck_277_;
goto v_resetjp_269_;
}
v_resetjp_269_:
{
lean_object* v___x_272_; uint8_t v___x_273_; lean_object* v___x_275_; 
v___x_272_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_272_, 0, v_a_268_);
v___x_273_ = lean_unbox(v_a_247_);
lean_dec(v_a_247_);
lean_ctor_set_uint8(v___x_272_, sizeof(void*)*1, v___x_273_);
if (v_isShared_271_ == 0)
{
lean_ctor_set(v___x_270_, 0, v___x_272_);
v___x_275_ = v___x_270_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v___x_272_);
v___x_275_ = v_reuseFailAlloc_276_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
return v___x_275_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonShowMessageParams_toJson_spec__0(lean_object* v_a_280_, lean_object* v_a_281_){
_start:
{
if (lean_obj_tag(v_a_280_) == 0)
{
lean_object* v___x_282_; 
v___x_282_ = lean_array_to_list(v_a_281_);
return v___x_282_;
}
else
{
lean_object* v_head_283_; lean_object* v_tail_284_; lean_object* v___x_285_; 
v_head_283_ = lean_ctor_get(v_a_280_, 0);
lean_inc(v_head_283_);
v_tail_284_ = lean_ctor_get(v_a_280_, 1);
lean_inc(v_tail_284_);
lean_dec_ref_known(v_a_280_, 2);
v___x_285_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_281_, v_head_283_);
v_a_280_ = v_tail_284_;
v_a_281_ = v___x_285_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonShowMessageParams_toJson(lean_object* v_x_289_){
_start:
{
uint8_t v_type_290_; lean_object* v_message_291_; lean_object* v___x_292_; lean_object* v___y_294_; 
v_type_290_ = lean_ctor_get_uint8(v_x_289_, sizeof(void*)*1);
v_message_291_ = lean_ctor_get(v_x_289_, 0);
v___x_292_ = ((lean_object*)(l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__0));
switch(v_type_290_)
{
case 0:
{
lean_object* v___x_307_; 
v___x_307_ = lean_obj_once(&l_Lean_Lsp_instToJsonMessageType___lam__0___closed__1, &l_Lean_Lsp_instToJsonMessageType___lam__0___closed__1_once, _init_l_Lean_Lsp_instToJsonMessageType___lam__0___closed__1);
v___y_294_ = v___x_307_;
goto v___jp_293_;
}
case 1:
{
lean_object* v___x_308_; 
v___x_308_ = lean_obj_once(&l_Lean_Lsp_instToJsonMessageType___lam__0___closed__3, &l_Lean_Lsp_instToJsonMessageType___lam__0___closed__3_once, _init_l_Lean_Lsp_instToJsonMessageType___lam__0___closed__3);
v___y_294_ = v___x_308_;
goto v___jp_293_;
}
case 2:
{
lean_object* v___x_309_; 
v___x_309_ = lean_obj_once(&l_Lean_Lsp_instToJsonMessageType___lam__0___closed__5, &l_Lean_Lsp_instToJsonMessageType___lam__0___closed__5_once, _init_l_Lean_Lsp_instToJsonMessageType___lam__0___closed__5);
v___y_294_ = v___x_309_;
goto v___jp_293_;
}
default: 
{
lean_object* v___x_310_; 
v___x_310_ = lean_obj_once(&l_Lean_Lsp_instToJsonMessageType___lam__0___closed__7, &l_Lean_Lsp_instToJsonMessageType___lam__0___closed__7_once, _init_l_Lean_Lsp_instToJsonMessageType___lam__0___closed__7);
v___y_294_ = v___x_310_;
goto v___jp_293_;
}
}
v___jp_293_:
{
lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; 
lean_inc(v___y_294_);
v___x_295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_295_, 0, v___x_292_);
lean_ctor_set(v___x_295_, 1, v___y_294_);
v___x_296_ = lean_box(0);
v___x_297_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_297_, 0, v___x_295_);
lean_ctor_set(v___x_297_, 1, v___x_296_);
v___x_298_ = ((lean_object*)(l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__13));
lean_inc_ref(v_message_291_);
v___x_299_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_299_, 0, v_message_291_);
v___x_300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_300_, 0, v___x_298_);
lean_ctor_set(v___x_300_, 1, v___x_299_);
v___x_301_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_301_, 0, v___x_300_);
lean_ctor_set(v___x_301_, 1, v___x_296_);
v___x_302_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_302_, 0, v___x_301_);
lean_ctor_set(v___x_302_, 1, v___x_296_);
v___x_303_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_303_, 0, v___x_297_);
lean_ctor_set(v___x_303_, 1, v___x_302_);
v___x_304_ = ((lean_object*)(l_Lean_Lsp_instToJsonShowMessageParams_toJson___closed__0));
v___x_305_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonShowMessageParams_toJson_spec__0(v___x_303_, v___x_304_);
v___x_306_ = l_Lean_Json_mkObj(v___x_305_);
lean_dec(v___x_305_);
return v___x_306_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonShowMessageParams_toJson___boxed(lean_object* v_x_311_){
_start:
{
lean_object* v_res_312_; 
v_res_312_ = l_Lean_Lsp_instToJsonShowMessageParams_toJson(v_x_311_);
lean_dec_ref(v_x_311_);
return v_res_312_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonMessageActionItem_fromJson___closed__3(void){
_start:
{
uint8_t v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_321_ = 1;
v___x_322_ = ((lean_object*)(l_Lean_Lsp_instFromJsonMessageActionItem_fromJson___closed__2));
v___x_323_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_322_, v___x_321_);
return v___x_323_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonMessageActionItem_fromJson___closed__4(void){
_start:
{
lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; 
v___x_324_ = ((lean_object*)(l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__6));
v___x_325_ = lean_obj_once(&l_Lean_Lsp_instFromJsonMessageActionItem_fromJson___closed__3, &l_Lean_Lsp_instFromJsonMessageActionItem_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonMessageActionItem_fromJson___closed__3);
v___x_326_ = lean_string_append(v___x_325_, v___x_324_);
return v___x_326_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonMessageActionItem_fromJson___closed__6(void){
_start:
{
uint8_t v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_329_ = 1;
v___x_330_ = ((lean_object*)(l_Lean_Lsp_instFromJsonMessageActionItem_fromJson___closed__5));
v___x_331_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_330_, v___x_329_);
return v___x_331_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonMessageActionItem_fromJson___closed__7(void){
_start:
{
lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_332_ = lean_obj_once(&l_Lean_Lsp_instFromJsonMessageActionItem_fromJson___closed__6, &l_Lean_Lsp_instFromJsonMessageActionItem_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonMessageActionItem_fromJson___closed__6);
v___x_333_ = lean_obj_once(&l_Lean_Lsp_instFromJsonMessageActionItem_fromJson___closed__4, &l_Lean_Lsp_instFromJsonMessageActionItem_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonMessageActionItem_fromJson___closed__4);
v___x_334_ = lean_string_append(v___x_333_, v___x_332_);
return v___x_334_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonMessageActionItem_fromJson___closed__8(void){
_start:
{
lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_335_ = ((lean_object*)(l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__11));
v___x_336_ = lean_obj_once(&l_Lean_Lsp_instFromJsonMessageActionItem_fromJson___closed__7, &l_Lean_Lsp_instFromJsonMessageActionItem_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonMessageActionItem_fromJson___closed__7);
v___x_337_ = lean_string_append(v___x_336_, v___x_335_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonMessageActionItem_fromJson(lean_object* v_json_338_){
_start:
{
lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_339_ = ((lean_object*)(l_Lean_Lsp_instFromJsonMessageActionItem_fromJson___closed__0));
v___x_340_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageParams_fromJson_spec__1(v_json_338_, v___x_339_);
if (lean_obj_tag(v___x_340_) == 0)
{
lean_object* v_a_341_; lean_object* v___x_343_; uint8_t v_isShared_344_; uint8_t v_isSharedCheck_350_; 
v_a_341_ = lean_ctor_get(v___x_340_, 0);
v_isSharedCheck_350_ = !lean_is_exclusive(v___x_340_);
if (v_isSharedCheck_350_ == 0)
{
v___x_343_ = v___x_340_;
v_isShared_344_ = v_isSharedCheck_350_;
goto v_resetjp_342_;
}
else
{
lean_inc(v_a_341_);
lean_dec(v___x_340_);
v___x_343_ = lean_box(0);
v_isShared_344_ = v_isSharedCheck_350_;
goto v_resetjp_342_;
}
v_resetjp_342_:
{
lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_348_; 
v___x_345_ = lean_obj_once(&l_Lean_Lsp_instFromJsonMessageActionItem_fromJson___closed__8, &l_Lean_Lsp_instFromJsonMessageActionItem_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonMessageActionItem_fromJson___closed__8);
v___x_346_ = lean_string_append(v___x_345_, v_a_341_);
lean_dec(v_a_341_);
if (v_isShared_344_ == 0)
{
lean_ctor_set(v___x_343_, 0, v___x_346_);
v___x_348_ = v___x_343_;
goto v_reusejp_347_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v___x_346_);
v___x_348_ = v_reuseFailAlloc_349_;
goto v_reusejp_347_;
}
v_reusejp_347_:
{
return v___x_348_;
}
}
}
else
{
if (lean_obj_tag(v___x_340_) == 0)
{
lean_object* v_a_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_358_; 
v_a_351_ = lean_ctor_get(v___x_340_, 0);
v_isSharedCheck_358_ = !lean_is_exclusive(v___x_340_);
if (v_isSharedCheck_358_ == 0)
{
v___x_353_ = v___x_340_;
v_isShared_354_ = v_isSharedCheck_358_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_a_351_);
lean_dec(v___x_340_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_358_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v___x_356_; 
if (v_isShared_354_ == 0)
{
lean_ctor_set_tag(v___x_353_, 0);
v___x_356_ = v___x_353_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v_a_351_);
v___x_356_ = v_reuseFailAlloc_357_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
return v___x_356_;
}
}
}
else
{
lean_object* v_a_359_; lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_366_; 
v_a_359_ = lean_ctor_get(v___x_340_, 0);
v_isSharedCheck_366_ = !lean_is_exclusive(v___x_340_);
if (v_isSharedCheck_366_ == 0)
{
v___x_361_ = v___x_340_;
v_isShared_362_ = v_isSharedCheck_366_;
goto v_resetjp_360_;
}
else
{
lean_inc(v_a_359_);
lean_dec(v___x_340_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_366_;
goto v_resetjp_360_;
}
v_resetjp_360_:
{
lean_object* v___x_364_; 
if (v_isShared_362_ == 0)
{
v___x_364_ = v___x_361_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v_a_359_);
v___x_364_ = v_reuseFailAlloc_365_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
return v___x_364_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonMessageActionItem_toJson(lean_object* v_x_369_){
_start:
{
lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; 
v___x_370_ = ((lean_object*)(l_Lean_Lsp_instFromJsonMessageActionItem_fromJson___closed__0));
v___x_371_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_371_, 0, v_x_369_);
v___x_372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_372_, 0, v___x_370_);
lean_ctor_set(v___x_372_, 1, v___x_371_);
v___x_373_ = lean_box(0);
v___x_374_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_374_, 0, v___x_372_);
lean_ctor_set(v___x_374_, 1, v___x_373_);
v___x_375_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_375_, 0, v___x_374_);
lean_ctor_set(v___x_375_, 1, v___x_373_);
v___x_376_ = ((lean_object*)(l_Lean_Lsp_instToJsonShowMessageParams_toJson___closed__0));
v___x_377_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonShowMessageParams_toJson_spec__0(v___x_375_, v___x_376_);
v___x_378_ = l_Lean_Json_mkObj(v___x_377_);
lean_dec(v___x_377_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0_spec__1_spec__2(size_t v_sz_381_, size_t v_i_382_, lean_object* v_bs_383_){
_start:
{
uint8_t v___x_384_; 
v___x_384_ = lean_usize_dec_lt(v_i_382_, v_sz_381_);
if (v___x_384_ == 0)
{
lean_object* v___x_385_; 
v___x_385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_385_, 0, v_bs_383_);
return v___x_385_;
}
else
{
lean_object* v_v_386_; lean_object* v___x_387_; 
v_v_386_ = lean_array_uget_borrowed(v_bs_383_, v_i_382_);
lean_inc(v_v_386_);
v___x_387_ = l_Lean_Lsp_instFromJsonMessageActionItem_fromJson(v_v_386_);
if (lean_obj_tag(v___x_387_) == 0)
{
lean_object* v_a_388_; lean_object* v___x_390_; uint8_t v_isShared_391_; uint8_t v_isSharedCheck_395_; 
lean_dec_ref(v_bs_383_);
v_a_388_ = lean_ctor_get(v___x_387_, 0);
v_isSharedCheck_395_ = !lean_is_exclusive(v___x_387_);
if (v_isSharedCheck_395_ == 0)
{
v___x_390_ = v___x_387_;
v_isShared_391_ = v_isSharedCheck_395_;
goto v_resetjp_389_;
}
else
{
lean_inc(v_a_388_);
lean_dec(v___x_387_);
v___x_390_ = lean_box(0);
v_isShared_391_ = v_isSharedCheck_395_;
goto v_resetjp_389_;
}
v_resetjp_389_:
{
lean_object* v___x_393_; 
if (v_isShared_391_ == 0)
{
v___x_393_ = v___x_390_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v_a_388_);
v___x_393_ = v_reuseFailAlloc_394_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
return v___x_393_;
}
}
}
else
{
lean_object* v_a_396_; lean_object* v___x_397_; lean_object* v_bs_x27_398_; size_t v___x_399_; size_t v___x_400_; lean_object* v___x_401_; 
v_a_396_ = lean_ctor_get(v___x_387_, 0);
lean_inc(v_a_396_);
lean_dec_ref_known(v___x_387_, 1);
v___x_397_ = lean_unsigned_to_nat(0u);
v_bs_x27_398_ = lean_array_uset(v_bs_383_, v_i_382_, v___x_397_);
v___x_399_ = ((size_t)1ULL);
v___x_400_ = lean_usize_add(v_i_382_, v___x_399_);
v___x_401_ = lean_array_uset(v_bs_x27_398_, v_i_382_, v_a_396_);
v_i_382_ = v___x_400_;
v_bs_383_ = v___x_401_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_sz_403_, lean_object* v_i_404_, lean_object* v_bs_405_){
_start:
{
size_t v_sz_boxed_406_; size_t v_i_boxed_407_; lean_object* v_res_408_; 
v_sz_boxed_406_ = lean_unbox_usize(v_sz_403_);
lean_dec(v_sz_403_);
v_i_boxed_407_ = lean_unbox_usize(v_i_404_);
lean_dec(v_i_404_);
v_res_408_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0_spec__1_spec__2(v_sz_boxed_406_, v_i_boxed_407_, v_bs_405_);
return v_res_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0_spec__1(lean_object* v_x_411_){
_start:
{
if (lean_obj_tag(v_x_411_) == 4)
{
lean_object* v_elems_412_; size_t v_sz_413_; size_t v___x_414_; lean_object* v___x_415_; 
v_elems_412_ = lean_ctor_get(v_x_411_, 0);
lean_inc_ref(v_elems_412_);
lean_dec_ref_known(v_x_411_, 1);
v_sz_413_ = lean_array_size(v_elems_412_);
v___x_414_ = ((size_t)0ULL);
v___x_415_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0_spec__1_spec__2(v_sz_413_, v___x_414_, v_elems_412_);
return v___x_415_;
}
else
{
lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_416_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0_spec__1___closed__0));
v___x_417_ = lean_unsigned_to_nat(80u);
v___x_418_ = l_Lean_Json_pretty(v_x_411_, v___x_417_);
v___x_419_ = lean_string_append(v___x_416_, v___x_418_);
lean_dec_ref(v___x_418_);
v___x_420_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0_spec__1___closed__1));
v___x_421_ = lean_string_append(v___x_419_, v___x_420_);
v___x_422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_422_, 0, v___x_421_);
return v___x_422_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0(lean_object* v_x_425_){
_start:
{
if (lean_obj_tag(v_x_425_) == 0)
{
lean_object* v___x_426_; 
v___x_426_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0___closed__0));
return v___x_426_;
}
else
{
lean_object* v___x_427_; 
v___x_427_ = l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0_spec__1(v_x_425_);
if (lean_obj_tag(v___x_427_) == 0)
{
lean_object* v_a_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_435_; 
v_a_428_ = lean_ctor_get(v___x_427_, 0);
v_isSharedCheck_435_ = !lean_is_exclusive(v___x_427_);
if (v_isSharedCheck_435_ == 0)
{
v___x_430_ = v___x_427_;
v_isShared_431_ = v_isSharedCheck_435_;
goto v_resetjp_429_;
}
else
{
lean_inc(v_a_428_);
lean_dec(v___x_427_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_435_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
lean_object* v___x_433_; 
if (v_isShared_431_ == 0)
{
v___x_433_ = v___x_430_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v_a_428_);
v___x_433_ = v_reuseFailAlloc_434_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
return v___x_433_;
}
}
}
else
{
lean_object* v_a_436_; lean_object* v___x_438_; uint8_t v_isShared_439_; uint8_t v_isSharedCheck_444_; 
v_a_436_ = lean_ctor_get(v___x_427_, 0);
v_isSharedCheck_444_ = !lean_is_exclusive(v___x_427_);
if (v_isSharedCheck_444_ == 0)
{
v___x_438_ = v___x_427_;
v_isShared_439_ = v_isSharedCheck_444_;
goto v_resetjp_437_;
}
else
{
lean_inc(v_a_436_);
lean_dec(v___x_427_);
v___x_438_ = lean_box(0);
v_isShared_439_ = v_isSharedCheck_444_;
goto v_resetjp_437_;
}
v_resetjp_437_:
{
lean_object* v___x_440_; lean_object* v___x_442_; 
v___x_440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_440_, 0, v_a_436_);
if (v_isShared_439_ == 0)
{
lean_ctor_set(v___x_438_, 0, v___x_440_);
v___x_442_ = v___x_438_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v___x_440_);
v___x_442_ = v_reuseFailAlloc_443_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
return v___x_442_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson_spec__0(lean_object* v_j_445_, lean_object* v_k_446_){
_start:
{
lean_object* v___x_447_; lean_object* v___x_448_; 
v___x_447_ = l_Lean_Json_getObjValD(v_j_445_, v_k_446_);
v___x_448_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0(v___x_447_);
return v___x_448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson_spec__0___boxed(lean_object* v_j_449_, lean_object* v_k_450_){
_start:
{
lean_object* v_res_451_; 
v_res_451_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson_spec__0(v_j_449_, v_k_450_);
lean_dec_ref(v_k_450_);
return v_res_451_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__2(void){
_start:
{
uint8_t v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_457_ = 1;
v___x_458_ = ((lean_object*)(l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__1));
v___x_459_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_458_, v___x_457_);
return v___x_459_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__3(void){
_start:
{
lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_460_ = ((lean_object*)(l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__6));
v___x_461_ = lean_obj_once(&l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__2, &l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__2);
v___x_462_ = lean_string_append(v___x_461_, v___x_460_);
return v___x_462_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_463_ = lean_obj_once(&l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__9, &l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__9);
v___x_464_ = lean_obj_once(&l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__3);
v___x_465_ = lean_string_append(v___x_464_, v___x_463_);
return v___x_465_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__5(void){
_start:
{
lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; 
v___x_466_ = ((lean_object*)(l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__11));
v___x_467_ = lean_obj_once(&l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__4);
v___x_468_ = lean_string_append(v___x_467_, v___x_466_);
return v___x_468_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__6(void){
_start:
{
lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_469_ = lean_obj_once(&l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__15, &l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__15_once, _init_l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__15);
v___x_470_ = lean_obj_once(&l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__3);
v___x_471_ = lean_string_append(v___x_470_, v___x_469_);
return v___x_471_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__7(void){
_start:
{
lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_472_ = ((lean_object*)(l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__11));
v___x_473_ = lean_obj_once(&l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__6, &l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__6);
v___x_474_ = lean_string_append(v___x_473_, v___x_472_);
return v___x_474_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__11(void){
_start:
{
uint8_t v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_479_ = 1;
v___x_480_ = ((lean_object*)(l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__10));
v___x_481_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_480_, v___x_479_);
return v___x_481_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__12(void){
_start:
{
lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_482_ = lean_obj_once(&l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__11, &l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__11);
v___x_483_ = lean_obj_once(&l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__3);
v___x_484_ = lean_string_append(v___x_483_, v___x_482_);
return v___x_484_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__13(void){
_start:
{
lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; 
v___x_485_ = ((lean_object*)(l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__11));
v___x_486_ = lean_obj_once(&l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__12, &l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__12);
v___x_487_ = lean_string_append(v___x_486_, v___x_485_);
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson(lean_object* v_json_488_){
_start:
{
lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_489_ = ((lean_object*)(l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__0));
lean_inc(v_json_488_);
v___x_490_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageParams_fromJson_spec__0(v_json_488_, v___x_489_);
if (lean_obj_tag(v___x_490_) == 0)
{
lean_object* v_a_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_500_; 
lean_dec(v_json_488_);
v_a_491_ = lean_ctor_get(v___x_490_, 0);
v_isSharedCheck_500_ = !lean_is_exclusive(v___x_490_);
if (v_isSharedCheck_500_ == 0)
{
v___x_493_ = v___x_490_;
v_isShared_494_ = v_isSharedCheck_500_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_a_491_);
lean_dec(v___x_490_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_500_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_498_; 
v___x_495_ = lean_obj_once(&l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__5, &l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__5);
v___x_496_ = lean_string_append(v___x_495_, v_a_491_);
lean_dec(v_a_491_);
if (v_isShared_494_ == 0)
{
lean_ctor_set(v___x_493_, 0, v___x_496_);
v___x_498_ = v___x_493_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v___x_496_);
v___x_498_ = v_reuseFailAlloc_499_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
return v___x_498_;
}
}
}
else
{
if (lean_obj_tag(v___x_490_) == 0)
{
lean_object* v_a_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_508_; 
lean_dec(v_json_488_);
v_a_501_ = lean_ctor_get(v___x_490_, 0);
v_isSharedCheck_508_ = !lean_is_exclusive(v___x_490_);
if (v_isSharedCheck_508_ == 0)
{
v___x_503_ = v___x_490_;
v_isShared_504_ = v_isSharedCheck_508_;
goto v_resetjp_502_;
}
else
{
lean_inc(v_a_501_);
lean_dec(v___x_490_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_508_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
lean_object* v___x_506_; 
if (v_isShared_504_ == 0)
{
lean_ctor_set_tag(v___x_503_, 0);
v___x_506_ = v___x_503_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v_a_501_);
v___x_506_ = v_reuseFailAlloc_507_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
return v___x_506_;
}
}
}
else
{
lean_object* v_a_509_; lean_object* v___x_510_; lean_object* v___x_511_; 
v_a_509_ = lean_ctor_get(v___x_490_, 0);
lean_inc(v_a_509_);
lean_dec_ref_known(v___x_490_, 1);
v___x_510_ = ((lean_object*)(l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__13));
lean_inc(v_json_488_);
v___x_511_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageParams_fromJson_spec__1(v_json_488_, v___x_510_);
if (lean_obj_tag(v___x_511_) == 0)
{
lean_object* v_a_512_; lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_521_; 
lean_dec(v_a_509_);
lean_dec(v_json_488_);
v_a_512_ = lean_ctor_get(v___x_511_, 0);
v_isSharedCheck_521_ = !lean_is_exclusive(v___x_511_);
if (v_isSharedCheck_521_ == 0)
{
v___x_514_ = v___x_511_;
v_isShared_515_ = v_isSharedCheck_521_;
goto v_resetjp_513_;
}
else
{
lean_inc(v_a_512_);
lean_dec(v___x_511_);
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_521_;
goto v_resetjp_513_;
}
v_resetjp_513_:
{
lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_519_; 
v___x_516_ = lean_obj_once(&l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__7);
v___x_517_ = lean_string_append(v___x_516_, v_a_512_);
lean_dec(v_a_512_);
if (v_isShared_515_ == 0)
{
lean_ctor_set(v___x_514_, 0, v___x_517_);
v___x_519_ = v___x_514_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v___x_517_);
v___x_519_ = v_reuseFailAlloc_520_;
goto v_reusejp_518_;
}
v_reusejp_518_:
{
return v___x_519_;
}
}
}
else
{
if (lean_obj_tag(v___x_511_) == 0)
{
lean_object* v_a_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_529_; 
lean_dec(v_a_509_);
lean_dec(v_json_488_);
v_a_522_ = lean_ctor_get(v___x_511_, 0);
v_isSharedCheck_529_ = !lean_is_exclusive(v___x_511_);
if (v_isSharedCheck_529_ == 0)
{
v___x_524_ = v___x_511_;
v_isShared_525_ = v_isSharedCheck_529_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_a_522_);
lean_dec(v___x_511_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_529_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
lean_object* v___x_527_; 
if (v_isShared_525_ == 0)
{
lean_ctor_set_tag(v___x_524_, 0);
v___x_527_ = v___x_524_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v_a_522_);
v___x_527_ = v_reuseFailAlloc_528_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
return v___x_527_;
}
}
}
else
{
lean_object* v_a_530_; lean_object* v___x_531_; lean_object* v___x_532_; 
v_a_530_ = lean_ctor_get(v___x_511_, 0);
lean_inc(v_a_530_);
lean_dec_ref_known(v___x_511_, 1);
v___x_531_ = ((lean_object*)(l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__8));
v___x_532_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson_spec__0(v_json_488_, v___x_531_);
if (lean_obj_tag(v___x_532_) == 0)
{
lean_object* v_a_533_; lean_object* v___x_535_; uint8_t v_isShared_536_; uint8_t v_isSharedCheck_542_; 
lean_dec(v_a_530_);
lean_dec(v_a_509_);
v_a_533_ = lean_ctor_get(v___x_532_, 0);
v_isSharedCheck_542_ = !lean_is_exclusive(v___x_532_);
if (v_isSharedCheck_542_ == 0)
{
v___x_535_ = v___x_532_;
v_isShared_536_ = v_isSharedCheck_542_;
goto v_resetjp_534_;
}
else
{
lean_inc(v_a_533_);
lean_dec(v___x_532_);
v___x_535_ = lean_box(0);
v_isShared_536_ = v_isSharedCheck_542_;
goto v_resetjp_534_;
}
v_resetjp_534_:
{
lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_540_; 
v___x_537_ = lean_obj_once(&l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__13, &l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__13);
v___x_538_ = lean_string_append(v___x_537_, v_a_533_);
lean_dec(v_a_533_);
if (v_isShared_536_ == 0)
{
lean_ctor_set(v___x_535_, 0, v___x_538_);
v___x_540_ = v___x_535_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v___x_538_);
v___x_540_ = v_reuseFailAlloc_541_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
return v___x_540_;
}
}
}
else
{
if (lean_obj_tag(v___x_532_) == 0)
{
lean_object* v_a_543_; lean_object* v___x_545_; uint8_t v_isShared_546_; uint8_t v_isSharedCheck_550_; 
lean_dec(v_a_530_);
lean_dec(v_a_509_);
v_a_543_ = lean_ctor_get(v___x_532_, 0);
v_isSharedCheck_550_ = !lean_is_exclusive(v___x_532_);
if (v_isSharedCheck_550_ == 0)
{
v___x_545_ = v___x_532_;
v_isShared_546_ = v_isSharedCheck_550_;
goto v_resetjp_544_;
}
else
{
lean_inc(v_a_543_);
lean_dec(v___x_532_);
v___x_545_ = lean_box(0);
v_isShared_546_ = v_isSharedCheck_550_;
goto v_resetjp_544_;
}
v_resetjp_544_:
{
lean_object* v___x_548_; 
if (v_isShared_546_ == 0)
{
lean_ctor_set_tag(v___x_545_, 0);
v___x_548_ = v___x_545_;
goto v_reusejp_547_;
}
else
{
lean_object* v_reuseFailAlloc_549_; 
v_reuseFailAlloc_549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_549_, 0, v_a_543_);
v___x_548_ = v_reuseFailAlloc_549_;
goto v_reusejp_547_;
}
v_reusejp_547_:
{
return v___x_548_;
}
}
}
else
{
lean_object* v_a_551_; lean_object* v___x_553_; uint8_t v_isShared_554_; uint8_t v_isSharedCheck_560_; 
v_a_551_ = lean_ctor_get(v___x_532_, 0);
v_isSharedCheck_560_ = !lean_is_exclusive(v___x_532_);
if (v_isSharedCheck_560_ == 0)
{
v___x_553_ = v___x_532_;
v_isShared_554_ = v_isSharedCheck_560_;
goto v_resetjp_552_;
}
else
{
lean_inc(v_a_551_);
lean_dec(v___x_532_);
v___x_553_ = lean_box(0);
v_isShared_554_ = v_isSharedCheck_560_;
goto v_resetjp_552_;
}
v_resetjp_552_:
{
lean_object* v___x_555_; uint8_t v___x_556_; lean_object* v___x_558_; 
v___x_555_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_555_, 0, v_a_530_);
lean_ctor_set(v___x_555_, 1, v_a_551_);
v___x_556_ = lean_unbox(v_a_509_);
lean_dec(v_a_509_);
lean_ctor_set_uint8(v___x_555_, sizeof(void*)*2, v___x_556_);
if (v_isShared_554_ == 0)
{
lean_ctor_set(v___x_553_, 0, v___x_555_);
v___x_558_ = v___x_553_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v___x_555_);
v___x_558_ = v_reuseFailAlloc_559_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
return v___x_558_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonShowMessageRequestParams_toJson_spec__0_spec__0_spec__1(size_t v_sz_563_, size_t v_i_564_, lean_object* v_bs_565_){
_start:
{
uint8_t v___x_566_; 
v___x_566_ = lean_usize_dec_lt(v_i_564_, v_sz_563_);
if (v___x_566_ == 0)
{
return v_bs_565_;
}
else
{
lean_object* v_v_567_; lean_object* v___x_568_; lean_object* v_bs_x27_569_; lean_object* v___x_570_; size_t v___x_571_; size_t v___x_572_; lean_object* v___x_573_; 
v_v_567_ = lean_array_uget(v_bs_565_, v_i_564_);
v___x_568_ = lean_unsigned_to_nat(0u);
v_bs_x27_569_ = lean_array_uset(v_bs_565_, v_i_564_, v___x_568_);
v___x_570_ = l_Lean_Lsp_instToJsonMessageActionItem_toJson(v_v_567_);
v___x_571_ = ((size_t)1ULL);
v___x_572_ = lean_usize_add(v_i_564_, v___x_571_);
v___x_573_ = lean_array_uset(v_bs_x27_569_, v_i_564_, v___x_570_);
v_i_564_ = v___x_572_;
v_bs_565_ = v___x_573_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonShowMessageRequestParams_toJson_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_575_, lean_object* v_i_576_, lean_object* v_bs_577_){
_start:
{
size_t v_sz_boxed_578_; size_t v_i_boxed_579_; lean_object* v_res_580_; 
v_sz_boxed_578_ = lean_unbox_usize(v_sz_575_);
lean_dec(v_sz_575_);
v_i_boxed_579_ = lean_unbox_usize(v_i_576_);
lean_dec(v_i_576_);
v_res_580_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonShowMessageRequestParams_toJson_spec__0_spec__0_spec__1(v_sz_boxed_578_, v_i_boxed_579_, v_bs_577_);
return v_res_580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonShowMessageRequestParams_toJson_spec__0_spec__0(lean_object* v_a_581_){
_start:
{
size_t v_sz_582_; size_t v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; 
v_sz_582_ = lean_array_size(v_a_581_);
v___x_583_ = ((size_t)0ULL);
v___x_584_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonShowMessageRequestParams_toJson_spec__0_spec__0_spec__1(v_sz_582_, v___x_583_, v_a_581_);
v___x_585_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_585_, 0, v___x_584_);
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonShowMessageRequestParams_toJson_spec__0(lean_object* v_k_586_, lean_object* v_x_587_){
_start:
{
if (lean_obj_tag(v_x_587_) == 0)
{
lean_object* v___x_588_; 
lean_dec_ref(v_k_586_);
v___x_588_ = lean_box(0);
return v___x_588_;
}
else
{
lean_object* v_val_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; 
v_val_589_ = lean_ctor_get(v_x_587_, 0);
lean_inc(v_val_589_);
lean_dec_ref_known(v_x_587_, 1);
v___x_590_ = l_Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonShowMessageRequestParams_toJson_spec__0_spec__0(v_val_589_);
v___x_591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_591_, 0, v_k_586_);
lean_ctor_set(v___x_591_, 1, v___x_590_);
v___x_592_ = lean_box(0);
v___x_593_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_593_, 0, v___x_591_);
lean_ctor_set(v___x_593_, 1, v___x_592_);
return v___x_593_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonShowMessageRequestParams_toJson(lean_object* v_x_594_){
_start:
{
uint8_t v_type_595_; lean_object* v_message_596_; lean_object* v_actions_x3f_597_; lean_object* v___x_598_; lean_object* v___y_600_; 
v_type_595_ = lean_ctor_get_uint8(v_x_594_, sizeof(void*)*2);
v_message_596_ = lean_ctor_get(v_x_594_, 0);
lean_inc_ref(v_message_596_);
v_actions_x3f_597_ = lean_ctor_get(v_x_594_, 1);
lean_inc(v_actions_x3f_597_);
lean_dec_ref(v_x_594_);
v___x_598_ = ((lean_object*)(l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__0));
switch(v_type_595_)
{
case 0:
{
lean_object* v___x_616_; 
v___x_616_ = lean_obj_once(&l_Lean_Lsp_instToJsonMessageType___lam__0___closed__1, &l_Lean_Lsp_instToJsonMessageType___lam__0___closed__1_once, _init_l_Lean_Lsp_instToJsonMessageType___lam__0___closed__1);
v___y_600_ = v___x_616_;
goto v___jp_599_;
}
case 1:
{
lean_object* v___x_617_; 
v___x_617_ = lean_obj_once(&l_Lean_Lsp_instToJsonMessageType___lam__0___closed__3, &l_Lean_Lsp_instToJsonMessageType___lam__0___closed__3_once, _init_l_Lean_Lsp_instToJsonMessageType___lam__0___closed__3);
v___y_600_ = v___x_617_;
goto v___jp_599_;
}
case 2:
{
lean_object* v___x_618_; 
v___x_618_ = lean_obj_once(&l_Lean_Lsp_instToJsonMessageType___lam__0___closed__5, &l_Lean_Lsp_instToJsonMessageType___lam__0___closed__5_once, _init_l_Lean_Lsp_instToJsonMessageType___lam__0___closed__5);
v___y_600_ = v___x_618_;
goto v___jp_599_;
}
default: 
{
lean_object* v___x_619_; 
v___x_619_ = lean_obj_once(&l_Lean_Lsp_instToJsonMessageType___lam__0___closed__7, &l_Lean_Lsp_instToJsonMessageType___lam__0___closed__7_once, _init_l_Lean_Lsp_instToJsonMessageType___lam__0___closed__7);
v___y_600_ = v___x_619_;
goto v___jp_599_;
}
}
v___jp_599_:
{
lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; 
lean_inc(v___y_600_);
v___x_601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_601_, 0, v___x_598_);
lean_ctor_set(v___x_601_, 1, v___y_600_);
v___x_602_ = lean_box(0);
v___x_603_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_603_, 0, v___x_601_);
lean_ctor_set(v___x_603_, 1, v___x_602_);
v___x_604_ = ((lean_object*)(l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__13));
v___x_605_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_605_, 0, v_message_596_);
v___x_606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_606_, 0, v___x_604_);
lean_ctor_set(v___x_606_, 1, v___x_605_);
v___x_607_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_607_, 0, v___x_606_);
lean_ctor_set(v___x_607_, 1, v___x_602_);
v___x_608_ = ((lean_object*)(l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__8));
v___x_609_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonShowMessageRequestParams_toJson_spec__0(v___x_608_, v_actions_x3f_597_);
v___x_610_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_610_, 0, v___x_609_);
lean_ctor_set(v___x_610_, 1, v___x_602_);
v___x_611_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_611_, 0, v___x_607_);
lean_ctor_set(v___x_611_, 1, v___x_610_);
v___x_612_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_612_, 0, v___x_603_);
lean_ctor_set(v___x_612_, 1, v___x_611_);
v___x_613_ = ((lean_object*)(l_Lean_Lsp_instToJsonShowMessageParams_toJson___closed__0));
v___x_614_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonShowMessageParams_toJson_spec__0(v___x_612_, v___x_613_);
v___x_615_ = l_Lean_Json_mkObj(v___x_614_);
lean_dec(v___x_614_);
return v___x_615_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonShowMessageResponse___aux__1(lean_object* v_a_622_){
_start:
{
lean_object* v___x_623_; lean_object* v___x_624_; 
v___x_623_ = ((lean_object*)(l_Lean_Lsp_instFromJsonMessageActionItem___closed__0));
v___x_624_ = l_Lean_Option_fromJson_x3f___redArg(v___x_623_, v_a_622_);
return v___x_624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Lsp_instFromJsonShowMessageResponse_spec__0(lean_object* v_x_627_){
_start:
{
if (lean_obj_tag(v_x_627_) == 0)
{
lean_object* v___x_628_; 
v___x_628_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Lsp_instFromJsonShowMessageResponse_spec__0___closed__0));
return v___x_628_;
}
else
{
lean_object* v___x_629_; 
v___x_629_ = l_Lean_Lsp_instFromJsonMessageActionItem_fromJson(v_x_627_);
if (lean_obj_tag(v___x_629_) == 0)
{
lean_object* v_a_630_; lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_637_; 
v_a_630_ = lean_ctor_get(v___x_629_, 0);
v_isSharedCheck_637_ = !lean_is_exclusive(v___x_629_);
if (v_isSharedCheck_637_ == 0)
{
v___x_632_ = v___x_629_;
v_isShared_633_ = v_isSharedCheck_637_;
goto v_resetjp_631_;
}
else
{
lean_inc(v_a_630_);
lean_dec(v___x_629_);
v___x_632_ = lean_box(0);
v_isShared_633_ = v_isSharedCheck_637_;
goto v_resetjp_631_;
}
v_resetjp_631_:
{
lean_object* v___x_635_; 
if (v_isShared_633_ == 0)
{
v___x_635_ = v___x_632_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v_a_630_);
v___x_635_ = v_reuseFailAlloc_636_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
return v___x_635_;
}
}
}
else
{
lean_object* v_a_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_646_; 
v_a_638_ = lean_ctor_get(v___x_629_, 0);
v_isSharedCheck_646_ = !lean_is_exclusive(v___x_629_);
if (v_isSharedCheck_646_ == 0)
{
v___x_640_ = v___x_629_;
v_isShared_641_ = v_isSharedCheck_646_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_a_638_);
lean_dec(v___x_629_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_646_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
lean_object* v___x_642_; lean_object* v___x_644_; 
v___x_642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_642_, 0, v_a_638_);
if (v_isShared_641_ == 0)
{
lean_ctor_set(v___x_640_, 0, v___x_642_);
v___x_644_ = v___x_640_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v___x_642_);
v___x_644_ = v_reuseFailAlloc_645_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
return v___x_644_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonShowMessageResponse___aux__1(lean_object* v_a_649_){
_start:
{
lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_650_ = ((lean_object*)(l_Lean_Lsp_instToJsonMessageActionItem___closed__0));
v___x_651_ = l_Lean_Option_toJson___redArg(v___x_650_, v_a_649_);
return v___x_651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_toJson___at___00Lean_Lsp_instToJsonShowMessageResponse_spec__0(lean_object* v_x_652_){
_start:
{
if (lean_obj_tag(v_x_652_) == 0)
{
lean_object* v___x_653_; 
v___x_653_ = lean_box(0);
return v___x_653_;
}
else
{
lean_object* v_val_654_; lean_object* v___x_655_; 
v_val_654_ = lean_ctor_get(v_x_652_, 0);
lean_inc(v_val_654_);
lean_dec_ref_known(v_x_652_, 1);
v___x_655_ = l_Lean_Lsp_instToJsonMessageActionItem_toJson(v_val_654_);
return v___x_655_;
}
}
}
lean_object* runtime_initialize_Lean_Data_Json_FromToJson_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_Lsp_Window(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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

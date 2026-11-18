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
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* l_Lean_Option_toJson___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Option_fromJson_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_ctorIdx___impl(uint8_t v_x_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(v_x_1_);
v___x_3_ = lean_obj_tag_nat(v___x_2_);
lean_dec(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_ctorIdx___impl___boxed(lean_object* v_x_4_){
_start:
{
uint8_t v_x_4__boxed_5_; lean_object* v_res_6_; 
v_x_4__boxed_5_ = lean_unbox(v_x_4_);
v_res_6_ = l_Lean_Lsp_MessageType_ctorIdx___impl(v_x_4__boxed_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_ctorElim___redArg(lean_object* v_k_7_){
_start:
{
lean_inc(v_k_7_);
return v_k_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_ctorElim___redArg___boxed(lean_object* v_k_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Lean_Lsp_MessageType_ctorElim___redArg(v_k_8_);
lean_dec(v_k_8_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_ctorElim(lean_object* v_motive_10_, lean_object* v_ctorIdx_11_, uint8_t v_t_12_, lean_object* v_h_13_, lean_object* v_k_14_){
_start:
{
lean_inc(v_k_14_);
return v_k_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_ctorElim___boxed(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, lean_object* v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
uint8_t v_t_boxed_20_; lean_object* v_res_21_; 
v_t_boxed_20_ = lean_unbox(v_t_17_);
v_res_21_ = l_Lean_Lsp_MessageType_ctorElim(v_motive_15_, v_ctorIdx_16_, v_t_boxed_20_, v_h_18_, v_k_19_);
lean_dec(v_k_19_);
lean_dec(v_ctorIdx_16_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_error_elim___redArg(lean_object* v_error_22_){
_start:
{
lean_inc(v_error_22_);
return v_error_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_error_elim___redArg___boxed(lean_object* v_error_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Lean_Lsp_MessageType_error_elim___redArg(v_error_23_);
lean_dec(v_error_23_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_error_elim(lean_object* v_motive_25_, uint8_t v_t_26_, lean_object* v_h_27_, lean_object* v_error_28_){
_start:
{
lean_inc(v_error_28_);
return v_error_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_error_elim___boxed(lean_object* v_motive_29_, lean_object* v_t_30_, lean_object* v_h_31_, lean_object* v_error_32_){
_start:
{
uint8_t v_t_boxed_33_; lean_object* v_res_34_; 
v_t_boxed_33_ = lean_unbox(v_t_30_);
v_res_34_ = l_Lean_Lsp_MessageType_error_elim(v_motive_29_, v_t_boxed_33_, v_h_31_, v_error_32_);
lean_dec(v_error_32_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_warning_elim___redArg(lean_object* v_warning_35_){
_start:
{
lean_inc(v_warning_35_);
return v_warning_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_warning_elim___redArg___boxed(lean_object* v_warning_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Lean_Lsp_MessageType_warning_elim___redArg(v_warning_36_);
lean_dec(v_warning_36_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_warning_elim(lean_object* v_motive_38_, uint8_t v_t_39_, lean_object* v_h_40_, lean_object* v_warning_41_){
_start:
{
lean_inc(v_warning_41_);
return v_warning_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_warning_elim___boxed(lean_object* v_motive_42_, lean_object* v_t_43_, lean_object* v_h_44_, lean_object* v_warning_45_){
_start:
{
uint8_t v_t_boxed_46_; lean_object* v_res_47_; 
v_t_boxed_46_ = lean_unbox(v_t_43_);
v_res_47_ = l_Lean_Lsp_MessageType_warning_elim(v_motive_42_, v_t_boxed_46_, v_h_44_, v_warning_45_);
lean_dec(v_warning_45_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_info_elim___redArg(lean_object* v_info_48_){
_start:
{
lean_inc(v_info_48_);
return v_info_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_info_elim___redArg___boxed(lean_object* v_info_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_Lean_Lsp_MessageType_info_elim___redArg(v_info_49_);
lean_dec(v_info_49_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_info_elim(lean_object* v_motive_51_, uint8_t v_t_52_, lean_object* v_h_53_, lean_object* v_info_54_){
_start:
{
lean_inc(v_info_54_);
return v_info_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_info_elim___boxed(lean_object* v_motive_55_, lean_object* v_t_56_, lean_object* v_h_57_, lean_object* v_info_58_){
_start:
{
uint8_t v_t_boxed_59_; lean_object* v_res_60_; 
v_t_boxed_59_ = lean_unbox(v_t_56_);
v_res_60_ = l_Lean_Lsp_MessageType_info_elim(v_motive_55_, v_t_boxed_59_, v_h_57_, v_info_58_);
lean_dec(v_info_58_);
return v_res_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_log_elim___redArg(lean_object* v_log_61_){
_start:
{
lean_inc(v_log_61_);
return v_log_61_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_log_elim___redArg___boxed(lean_object* v_log_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = l_Lean_Lsp_MessageType_log_elim___redArg(v_log_62_);
lean_dec(v_log_62_);
return v_res_63_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_log_elim(lean_object* v_motive_64_, uint8_t v_t_65_, lean_object* v_h_66_, lean_object* v_log_67_){
_start:
{
lean_inc(v_log_67_);
return v_log_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_log_elim___boxed(lean_object* v_motive_68_, lean_object* v_t_69_, lean_object* v_h_70_, lean_object* v_log_71_){
_start:
{
uint8_t v_t_boxed_72_; lean_object* v_res_73_; 
v_t_boxed_72_ = lean_unbox(v_t_69_);
v_res_73_ = l_Lean_Lsp_MessageType_log_elim(v_motive_68_, v_t_boxed_72_, v_h_70_, v_log_71_);
lean_dec(v_log_71_);
return v_res_73_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonMessageType___lam__0___closed__2(void){
_start:
{
lean_object* v_natZero_77_; lean_object* v_intZero_78_; 
v_natZero_77_ = lean_unsigned_to_nat(0u);
v_intZero_78_ = lean_nat_to_int(v_natZero_77_);
return v_intZero_78_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonMessageType___lam__0(lean_object* v_x_91_){
_start:
{
if (lean_obj_tag(v_x_91_) == 2)
{
lean_object* v_n_94_; lean_object* v_mantissa_95_; lean_object* v_exponent_96_; lean_object* v_natZero_97_; lean_object* v_intZero_98_; uint8_t v_isNeg_99_; 
v_n_94_ = lean_ctor_get(v_x_91_, 0);
v_mantissa_95_ = lean_ctor_get(v_n_94_, 0);
v_exponent_96_ = lean_ctor_get(v_n_94_, 1);
v_natZero_97_ = lean_unsigned_to_nat(0u);
v_intZero_98_ = lean_obj_once(&l_Lean_Lsp_instFromJsonMessageType___lam__0___closed__2, &l_Lean_Lsp_instFromJsonMessageType___lam__0___closed__2_once, _init_l_Lean_Lsp_instFromJsonMessageType___lam__0___closed__2);
v_isNeg_99_ = lean_int_dec_lt(v_mantissa_95_, v_intZero_98_);
if (v_isNeg_99_ == 0)
{
lean_object* v_a_100_; lean_object* v___x_101_; uint8_t v___x_102_; 
v_a_100_ = lean_nat_abs(v_mantissa_95_);
v___x_101_ = lean_unsigned_to_nat(1u);
v___x_102_ = lean_nat_dec_eq(v_a_100_, v___x_101_);
if (v___x_102_ == 0)
{
lean_object* v___x_103_; uint8_t v___x_104_; 
v___x_103_ = lean_unsigned_to_nat(2u);
v___x_104_ = lean_nat_dec_eq(v_a_100_, v___x_103_);
if (v___x_104_ == 0)
{
lean_object* v___x_105_; uint8_t v___x_106_; 
v___x_105_ = lean_unsigned_to_nat(3u);
v___x_106_ = lean_nat_dec_eq(v_a_100_, v___x_105_);
if (v___x_106_ == 0)
{
lean_object* v___x_107_; uint8_t v___x_108_; 
v___x_107_ = lean_unsigned_to_nat(4u);
v___x_108_ = lean_nat_dec_eq(v_a_100_, v___x_107_);
lean_dec(v_a_100_);
if (v___x_108_ == 0)
{
goto v___jp_92_;
}
else
{
uint8_t v___x_109_; 
v___x_109_ = lean_nat_dec_eq(v_exponent_96_, v_natZero_97_);
if (v___x_109_ == 0)
{
goto v___jp_92_;
}
else
{
lean_object* v___x_110_; 
v___x_110_ = ((lean_object*)(l_Lean_Lsp_instFromJsonMessageType___lam__0___closed__3));
return v___x_110_;
}
}
}
else
{
uint8_t v___x_111_; 
lean_dec(v_a_100_);
v___x_111_ = lean_nat_dec_eq(v_exponent_96_, v_natZero_97_);
if (v___x_111_ == 0)
{
goto v___jp_92_;
}
else
{
lean_object* v___x_112_; 
v___x_112_ = ((lean_object*)(l_Lean_Lsp_instFromJsonMessageType___lam__0___closed__4));
return v___x_112_;
}
}
}
else
{
uint8_t v___x_113_; 
lean_dec(v_a_100_);
v___x_113_ = lean_nat_dec_eq(v_exponent_96_, v_natZero_97_);
if (v___x_113_ == 0)
{
goto v___jp_92_;
}
else
{
lean_object* v___x_114_; 
v___x_114_ = ((lean_object*)(l_Lean_Lsp_instFromJsonMessageType___lam__0___closed__5));
return v___x_114_;
}
}
}
else
{
uint8_t v___x_115_; 
lean_dec(v_a_100_);
v___x_115_ = lean_nat_dec_eq(v_exponent_96_, v_natZero_97_);
if (v___x_115_ == 0)
{
goto v___jp_92_;
}
else
{
lean_object* v___x_116_; 
v___x_116_ = ((lean_object*)(l_Lean_Lsp_instFromJsonMessageType___lam__0___closed__6));
return v___x_116_;
}
}
}
else
{
goto v___jp_92_;
}
}
else
{
goto v___jp_92_;
}
v___jp_92_:
{
lean_object* v___x_93_; 
v___x_93_ = ((lean_object*)(l_Lean_Lsp_instFromJsonMessageType___lam__0___closed__1));
return v___x_93_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonMessageType___lam__0___boxed(lean_object* v_x_117_){
_start:
{
lean_object* v_res_118_; 
v_res_118_ = l_Lean_Lsp_instFromJsonMessageType___lam__0(v_x_117_);
lean_dec(v_x_117_);
return v_res_118_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonMessageType___lam__0___closed__0(void){
_start:
{
lean_object* v___x_121_; lean_object* v___x_122_; 
v___x_121_ = lean_unsigned_to_nat(1u);
v___x_122_ = l_Lean_JsonNumber_fromNat(v___x_121_);
return v___x_122_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonMessageType___lam__0___closed__1(void){
_start:
{
lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_123_ = lean_obj_once(&l_Lean_Lsp_instToJsonMessageType___lam__0___closed__0, &l_Lean_Lsp_instToJsonMessageType___lam__0___closed__0_once, _init_l_Lean_Lsp_instToJsonMessageType___lam__0___closed__0);
v___x_124_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_124_, 0, v___x_123_);
return v___x_124_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonMessageType___lam__0___closed__2(void){
_start:
{
lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_125_ = lean_unsigned_to_nat(2u);
v___x_126_ = l_Lean_JsonNumber_fromNat(v___x_125_);
return v___x_126_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonMessageType___lam__0___closed__3(void){
_start:
{
lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_127_ = lean_obj_once(&l_Lean_Lsp_instToJsonMessageType___lam__0___closed__2, &l_Lean_Lsp_instToJsonMessageType___lam__0___closed__2_once, _init_l_Lean_Lsp_instToJsonMessageType___lam__0___closed__2);
v___x_128_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_128_, 0, v___x_127_);
return v___x_128_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonMessageType___lam__0___closed__4(void){
_start:
{
lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_129_ = lean_unsigned_to_nat(3u);
v___x_130_ = l_Lean_JsonNumber_fromNat(v___x_129_);
return v___x_130_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonMessageType___lam__0___closed__5(void){
_start:
{
lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_131_ = lean_obj_once(&l_Lean_Lsp_instToJsonMessageType___lam__0___closed__4, &l_Lean_Lsp_instToJsonMessageType___lam__0___closed__4_once, _init_l_Lean_Lsp_instToJsonMessageType___lam__0___closed__4);
v___x_132_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_132_, 0, v___x_131_);
return v___x_132_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonMessageType___lam__0___closed__6(void){
_start:
{
lean_object* v___x_133_; lean_object* v___x_134_; 
v___x_133_ = lean_unsigned_to_nat(4u);
v___x_134_ = l_Lean_JsonNumber_fromNat(v___x_133_);
return v___x_134_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonMessageType___lam__0___closed__7(void){
_start:
{
lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_135_ = lean_obj_once(&l_Lean_Lsp_instToJsonMessageType___lam__0___closed__6, &l_Lean_Lsp_instToJsonMessageType___lam__0___closed__6_once, _init_l_Lean_Lsp_instToJsonMessageType___lam__0___closed__6);
v___x_136_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_136_, 0, v___x_135_);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonMessageType___lam__0(uint8_t v_x_137_){
_start:
{
switch(v_x_137_)
{
case 0:
{
lean_object* v___x_138_; 
v___x_138_ = lean_obj_once(&l_Lean_Lsp_instToJsonMessageType___lam__0___closed__1, &l_Lean_Lsp_instToJsonMessageType___lam__0___closed__1_once, _init_l_Lean_Lsp_instToJsonMessageType___lam__0___closed__1);
return v___x_138_;
}
case 1:
{
lean_object* v___x_139_; 
v___x_139_ = lean_obj_once(&l_Lean_Lsp_instToJsonMessageType___lam__0___closed__3, &l_Lean_Lsp_instToJsonMessageType___lam__0___closed__3_once, _init_l_Lean_Lsp_instToJsonMessageType___lam__0___closed__3);
return v___x_139_;
}
case 2:
{
lean_object* v___x_140_; 
v___x_140_ = lean_obj_once(&l_Lean_Lsp_instToJsonMessageType___lam__0___closed__5, &l_Lean_Lsp_instToJsonMessageType___lam__0___closed__5_once, _init_l_Lean_Lsp_instToJsonMessageType___lam__0___closed__5);
return v___x_140_;
}
default: 
{
lean_object* v___x_141_; 
v___x_141_ = lean_obj_once(&l_Lean_Lsp_instToJsonMessageType___lam__0___closed__7, &l_Lean_Lsp_instToJsonMessageType___lam__0___closed__7_once, _init_l_Lean_Lsp_instToJsonMessageType___lam__0___closed__7);
return v___x_141_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonMessageType___lam__0___boxed(lean_object* v_x_142_){
_start:
{
uint8_t v_x_106__boxed_143_; lean_object* v_res_144_; 
v_x_106__boxed_143_ = lean_unbox(v_x_142_);
v_res_144_ = l_Lean_Lsp_instToJsonMessageType___lam__0(v_x_106__boxed_143_);
return v_res_144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageParams_fromJson_spec__0(lean_object* v_j_147_, lean_object* v_k_148_){
_start:
{
lean_object* v___x_151_; 
v___x_151_ = l_Lean_Json_getObjValD(v_j_147_, v_k_148_);
if (lean_obj_tag(v___x_151_) == 2)
{
lean_object* v_n_152_; lean_object* v_mantissa_153_; lean_object* v_exponent_154_; lean_object* v_natZero_155_; lean_object* v_intZero_156_; uint8_t v_isNeg_157_; 
v_n_152_ = lean_ctor_get(v___x_151_, 0);
lean_inc_ref(v_n_152_);
lean_dec_ref_known(v___x_151_, 1);
v_mantissa_153_ = lean_ctor_get(v_n_152_, 0);
lean_inc(v_mantissa_153_);
v_exponent_154_ = lean_ctor_get(v_n_152_, 1);
lean_inc(v_exponent_154_);
lean_dec_ref(v_n_152_);
v_natZero_155_ = lean_unsigned_to_nat(0u);
v_intZero_156_ = lean_obj_once(&l_Lean_Lsp_instFromJsonMessageType___lam__0___closed__2, &l_Lean_Lsp_instFromJsonMessageType___lam__0___closed__2_once, _init_l_Lean_Lsp_instFromJsonMessageType___lam__0___closed__2);
v_isNeg_157_ = lean_int_dec_lt(v_mantissa_153_, v_intZero_156_);
if (v_isNeg_157_ == 0)
{
lean_object* v_a_158_; lean_object* v___x_159_; uint8_t v___x_160_; 
v_a_158_ = lean_nat_abs(v_mantissa_153_);
lean_dec(v_mantissa_153_);
v___x_159_ = lean_unsigned_to_nat(1u);
v___x_160_ = lean_nat_dec_eq(v_a_158_, v___x_159_);
if (v___x_160_ == 0)
{
lean_object* v___x_161_; uint8_t v___x_162_; 
v___x_161_ = lean_unsigned_to_nat(2u);
v___x_162_ = lean_nat_dec_eq(v_a_158_, v___x_161_);
if (v___x_162_ == 0)
{
lean_object* v___x_163_; uint8_t v___x_164_; 
v___x_163_ = lean_unsigned_to_nat(3u);
v___x_164_ = lean_nat_dec_eq(v_a_158_, v___x_163_);
if (v___x_164_ == 0)
{
lean_object* v___x_165_; uint8_t v___x_166_; 
v___x_165_ = lean_unsigned_to_nat(4u);
v___x_166_ = lean_nat_dec_eq(v_a_158_, v___x_165_);
lean_dec(v_a_158_);
if (v___x_166_ == 0)
{
lean_dec(v_exponent_154_);
goto v___jp_149_;
}
else
{
uint8_t v___x_167_; 
v___x_167_ = lean_nat_dec_eq(v_exponent_154_, v_natZero_155_);
lean_dec(v_exponent_154_);
if (v___x_167_ == 0)
{
goto v___jp_149_;
}
else
{
lean_object* v___x_168_; 
v___x_168_ = ((lean_object*)(l_Lean_Lsp_instFromJsonMessageType___lam__0___closed__3));
return v___x_168_;
}
}
}
else
{
uint8_t v___x_169_; 
lean_dec(v_a_158_);
v___x_169_ = lean_nat_dec_eq(v_exponent_154_, v_natZero_155_);
lean_dec(v_exponent_154_);
if (v___x_169_ == 0)
{
goto v___jp_149_;
}
else
{
lean_object* v___x_170_; 
v___x_170_ = ((lean_object*)(l_Lean_Lsp_instFromJsonMessageType___lam__0___closed__4));
return v___x_170_;
}
}
}
else
{
uint8_t v___x_171_; 
lean_dec(v_a_158_);
v___x_171_ = lean_nat_dec_eq(v_exponent_154_, v_natZero_155_);
lean_dec(v_exponent_154_);
if (v___x_171_ == 0)
{
goto v___jp_149_;
}
else
{
lean_object* v___x_172_; 
v___x_172_ = ((lean_object*)(l_Lean_Lsp_instFromJsonMessageType___lam__0___closed__5));
return v___x_172_;
}
}
}
else
{
uint8_t v___x_173_; 
lean_dec(v_a_158_);
v___x_173_ = lean_nat_dec_eq(v_exponent_154_, v_natZero_155_);
lean_dec(v_exponent_154_);
if (v___x_173_ == 0)
{
goto v___jp_149_;
}
else
{
lean_object* v___x_174_; 
v___x_174_ = ((lean_object*)(l_Lean_Lsp_instFromJsonMessageType___lam__0___closed__6));
return v___x_174_;
}
}
}
else
{
lean_dec(v_exponent_154_);
lean_dec(v_mantissa_153_);
goto v___jp_149_;
}
}
else
{
lean_dec(v___x_151_);
goto v___jp_149_;
}
v___jp_149_:
{
lean_object* v___x_150_; 
v___x_150_ = ((lean_object*)(l_Lean_Lsp_instFromJsonMessageType___lam__0___closed__1));
return v___x_150_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageParams_fromJson_spec__0___boxed(lean_object* v_j_175_, lean_object* v_k_176_){
_start:
{
lean_object* v_res_177_; 
v_res_177_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageParams_fromJson_spec__0(v_j_175_, v_k_176_);
lean_dec_ref(v_k_176_);
return v_res_177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageParams_fromJson_spec__1(lean_object* v_j_178_, lean_object* v_k_179_){
_start:
{
lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_180_ = l_Lean_Json_getObjValD(v_j_178_, v_k_179_);
v___x_181_ = l_Lean_Json_getStr_x3f(v___x_180_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageParams_fromJson_spec__1___boxed(lean_object* v_j_182_, lean_object* v_k_183_){
_start:
{
lean_object* v_res_184_; 
v_res_184_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageParams_fromJson_spec__1(v_j_182_, v_k_183_);
lean_dec_ref(v_k_183_);
return v_res_184_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__5(void){
_start:
{
uint8_t v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_193_ = 1;
v___x_194_ = ((lean_object*)(l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__4));
v___x_195_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_194_, v___x_193_);
return v___x_195_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__7(void){
_start:
{
lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; 
v___x_197_ = ((lean_object*)(l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__6));
v___x_198_ = lean_obj_once(&l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__5, &l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__5);
v___x_199_ = lean_string_append(v___x_198_, v___x_197_);
return v___x_199_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__9(void){
_start:
{
uint8_t v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_202_ = 1;
v___x_203_ = ((lean_object*)(l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__8));
v___x_204_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_203_, v___x_202_);
return v___x_204_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__10(void){
_start:
{
lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; 
v___x_205_ = lean_obj_once(&l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__9, &l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__9);
v___x_206_ = lean_obj_once(&l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__7);
v___x_207_ = lean_string_append(v___x_206_, v___x_205_);
return v___x_207_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__12(void){
_start:
{
lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_209_ = ((lean_object*)(l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__11));
v___x_210_ = lean_obj_once(&l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__10, &l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__10);
v___x_211_ = lean_string_append(v___x_210_, v___x_209_);
return v___x_211_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__15(void){
_start:
{
uint8_t v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_215_ = 1;
v___x_216_ = ((lean_object*)(l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__14));
v___x_217_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_216_, v___x_215_);
return v___x_217_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__16(void){
_start:
{
lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_218_ = lean_obj_once(&l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__15, &l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__15_once, _init_l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__15);
v___x_219_ = lean_obj_once(&l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__7);
v___x_220_ = lean_string_append(v___x_219_, v___x_218_);
return v___x_220_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__17(void){
_start:
{
lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_221_ = ((lean_object*)(l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__11));
v___x_222_ = lean_obj_once(&l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__16, &l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__16_once, _init_l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__16);
v___x_223_ = lean_string_append(v___x_222_, v___x_221_);
return v___x_223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonShowMessageParams_fromJson(lean_object* v_json_224_){
_start:
{
lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_225_ = ((lean_object*)(l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__0));
lean_inc(v_json_224_);
v___x_226_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageParams_fromJson_spec__0(v_json_224_, v___x_225_);
if (lean_obj_tag(v___x_226_) == 0)
{
lean_object* v_a_227_; lean_object* v___x_229_; uint8_t v_isShared_230_; uint8_t v_isSharedCheck_236_; 
lean_dec(v_json_224_);
v_a_227_ = lean_ctor_get(v___x_226_, 0);
v_isSharedCheck_236_ = !lean_is_exclusive(v___x_226_);
if (v_isSharedCheck_236_ == 0)
{
v___x_229_ = v___x_226_;
v_isShared_230_ = v_isSharedCheck_236_;
goto v_resetjp_228_;
}
else
{
lean_inc(v_a_227_);
lean_dec(v___x_226_);
v___x_229_ = lean_box(0);
v_isShared_230_ = v_isSharedCheck_236_;
goto v_resetjp_228_;
}
v_resetjp_228_:
{
lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_234_; 
v___x_231_ = lean_obj_once(&l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__12, &l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__12);
v___x_232_ = lean_string_append(v___x_231_, v_a_227_);
lean_dec(v_a_227_);
if (v_isShared_230_ == 0)
{
lean_ctor_set(v___x_229_, 0, v___x_232_);
v___x_234_ = v___x_229_;
goto v_reusejp_233_;
}
else
{
lean_object* v_reuseFailAlloc_235_; 
v_reuseFailAlloc_235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_235_, 0, v___x_232_);
v___x_234_ = v_reuseFailAlloc_235_;
goto v_reusejp_233_;
}
v_reusejp_233_:
{
return v___x_234_;
}
}
}
else
{
lean_object* v_a_237_; lean_object* v___x_238_; lean_object* v___x_239_; 
v_a_237_ = lean_ctor_get(v___x_226_, 0);
lean_inc(v_a_237_);
lean_dec_ref_known(v___x_226_, 1);
v___x_238_ = ((lean_object*)(l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__13));
v___x_239_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageParams_fromJson_spec__1(v_json_224_, v___x_238_);
if (lean_obj_tag(v___x_239_) == 0)
{
lean_object* v_a_240_; lean_object* v___x_242_; uint8_t v_isShared_243_; uint8_t v_isSharedCheck_249_; 
lean_dec(v_a_237_);
v_a_240_ = lean_ctor_get(v___x_239_, 0);
v_isSharedCheck_249_ = !lean_is_exclusive(v___x_239_);
if (v_isSharedCheck_249_ == 0)
{
v___x_242_ = v___x_239_;
v_isShared_243_ = v_isSharedCheck_249_;
goto v_resetjp_241_;
}
else
{
lean_inc(v_a_240_);
lean_dec(v___x_239_);
v___x_242_ = lean_box(0);
v_isShared_243_ = v_isSharedCheck_249_;
goto v_resetjp_241_;
}
v_resetjp_241_:
{
lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_247_; 
v___x_244_ = lean_obj_once(&l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__17, &l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__17_once, _init_l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__17);
v___x_245_ = lean_string_append(v___x_244_, v_a_240_);
lean_dec(v_a_240_);
if (v_isShared_243_ == 0)
{
lean_ctor_set(v___x_242_, 0, v___x_245_);
v___x_247_ = v___x_242_;
goto v_reusejp_246_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v___x_245_);
v___x_247_ = v_reuseFailAlloc_248_;
goto v_reusejp_246_;
}
v_reusejp_246_:
{
return v___x_247_;
}
}
}
else
{
lean_object* v_a_250_; lean_object* v___x_252_; uint8_t v_isShared_253_; uint8_t v_isSharedCheck_259_; 
v_a_250_ = lean_ctor_get(v___x_239_, 0);
v_isSharedCheck_259_ = !lean_is_exclusive(v___x_239_);
if (v_isSharedCheck_259_ == 0)
{
v___x_252_ = v___x_239_;
v_isShared_253_ = v_isSharedCheck_259_;
goto v_resetjp_251_;
}
else
{
lean_inc(v_a_250_);
lean_dec(v___x_239_);
v___x_252_ = lean_box(0);
v_isShared_253_ = v_isSharedCheck_259_;
goto v_resetjp_251_;
}
v_resetjp_251_:
{
lean_object* v___x_254_; uint8_t v___x_255_; lean_object* v___x_257_; 
v___x_254_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_254_, 0, v_a_250_);
v___x_255_ = lean_unbox(v_a_237_);
lean_dec(v_a_237_);
lean_ctor_set_uint8(v___x_254_, sizeof(void*)*1, v___x_255_);
if (v_isShared_253_ == 0)
{
lean_ctor_set(v___x_252_, 0, v___x_254_);
v___x_257_ = v___x_252_;
goto v_reusejp_256_;
}
else
{
lean_object* v_reuseFailAlloc_258_; 
v_reuseFailAlloc_258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_258_, 0, v___x_254_);
v___x_257_ = v_reuseFailAlloc_258_;
goto v_reusejp_256_;
}
v_reusejp_256_:
{
return v___x_257_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonShowMessageParams_toJson_spec__0(lean_object* v_a_262_, lean_object* v_a_263_){
_start:
{
if (lean_obj_tag(v_a_262_) == 0)
{
lean_object* v___x_264_; 
v___x_264_ = lean_array_to_list(v_a_263_);
return v___x_264_;
}
else
{
lean_object* v_head_265_; lean_object* v_tail_266_; lean_object* v___x_267_; 
v_head_265_ = lean_ctor_get(v_a_262_, 0);
lean_inc(v_head_265_);
v_tail_266_ = lean_ctor_get(v_a_262_, 1);
lean_inc(v_tail_266_);
lean_dec_ref_known(v_a_262_, 2);
v___x_267_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_263_, v_head_265_);
v_a_262_ = v_tail_266_;
v_a_263_ = v___x_267_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonShowMessageParams_toJson(lean_object* v_x_271_){
_start:
{
uint8_t v_type_272_; lean_object* v_message_273_; lean_object* v___x_274_; lean_object* v___y_276_; 
v_type_272_ = lean_ctor_get_uint8(v_x_271_, sizeof(void*)*1);
v_message_273_ = lean_ctor_get(v_x_271_, 0);
v___x_274_ = ((lean_object*)(l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__0));
switch(v_type_272_)
{
case 0:
{
lean_object* v___x_289_; 
v___x_289_ = lean_obj_once(&l_Lean_Lsp_instToJsonMessageType___lam__0___closed__1, &l_Lean_Lsp_instToJsonMessageType___lam__0___closed__1_once, _init_l_Lean_Lsp_instToJsonMessageType___lam__0___closed__1);
v___y_276_ = v___x_289_;
goto v___jp_275_;
}
case 1:
{
lean_object* v___x_290_; 
v___x_290_ = lean_obj_once(&l_Lean_Lsp_instToJsonMessageType___lam__0___closed__3, &l_Lean_Lsp_instToJsonMessageType___lam__0___closed__3_once, _init_l_Lean_Lsp_instToJsonMessageType___lam__0___closed__3);
v___y_276_ = v___x_290_;
goto v___jp_275_;
}
case 2:
{
lean_object* v___x_291_; 
v___x_291_ = lean_obj_once(&l_Lean_Lsp_instToJsonMessageType___lam__0___closed__5, &l_Lean_Lsp_instToJsonMessageType___lam__0___closed__5_once, _init_l_Lean_Lsp_instToJsonMessageType___lam__0___closed__5);
v___y_276_ = v___x_291_;
goto v___jp_275_;
}
default: 
{
lean_object* v___x_292_; 
v___x_292_ = lean_obj_once(&l_Lean_Lsp_instToJsonMessageType___lam__0___closed__7, &l_Lean_Lsp_instToJsonMessageType___lam__0___closed__7_once, _init_l_Lean_Lsp_instToJsonMessageType___lam__0___closed__7);
v___y_276_ = v___x_292_;
goto v___jp_275_;
}
}
v___jp_275_:
{
lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; 
lean_inc(v___y_276_);
v___x_277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_277_, 0, v___x_274_);
lean_ctor_set(v___x_277_, 1, v___y_276_);
v___x_278_ = lean_box(0);
v___x_279_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_279_, 0, v___x_277_);
lean_ctor_set(v___x_279_, 1, v___x_278_);
v___x_280_ = ((lean_object*)(l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__13));
lean_inc_ref(v_message_273_);
v___x_281_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_281_, 0, v_message_273_);
v___x_282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_282_, 0, v___x_280_);
lean_ctor_set(v___x_282_, 1, v___x_281_);
v___x_283_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_283_, 0, v___x_282_);
lean_ctor_set(v___x_283_, 1, v___x_278_);
v___x_284_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_284_, 0, v___x_283_);
lean_ctor_set(v___x_284_, 1, v___x_278_);
v___x_285_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_285_, 0, v___x_279_);
lean_ctor_set(v___x_285_, 1, v___x_284_);
v___x_286_ = ((lean_object*)(l_Lean_Lsp_instToJsonShowMessageParams_toJson___closed__0));
v___x_287_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonShowMessageParams_toJson_spec__0(v___x_285_, v___x_286_);
v___x_288_ = l_Lean_Json_mkObj(v___x_287_);
lean_dec(v___x_287_);
return v___x_288_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonShowMessageParams_toJson___boxed(lean_object* v_x_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l_Lean_Lsp_instToJsonShowMessageParams_toJson(v_x_293_);
lean_dec_ref(v_x_293_);
return v_res_294_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonMessageActionItem_fromJson___closed__3(void){
_start:
{
uint8_t v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_303_ = 1;
v___x_304_ = ((lean_object*)(l_Lean_Lsp_instFromJsonMessageActionItem_fromJson___closed__2));
v___x_305_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_304_, v___x_303_);
return v___x_305_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonMessageActionItem_fromJson___closed__4(void){
_start:
{
lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_306_ = ((lean_object*)(l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__6));
v___x_307_ = lean_obj_once(&l_Lean_Lsp_instFromJsonMessageActionItem_fromJson___closed__3, &l_Lean_Lsp_instFromJsonMessageActionItem_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonMessageActionItem_fromJson___closed__3);
v___x_308_ = lean_string_append(v___x_307_, v___x_306_);
return v___x_308_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonMessageActionItem_fromJson___closed__6(void){
_start:
{
uint8_t v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_311_ = 1;
v___x_312_ = ((lean_object*)(l_Lean_Lsp_instFromJsonMessageActionItem_fromJson___closed__5));
v___x_313_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_312_, v___x_311_);
return v___x_313_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonMessageActionItem_fromJson___closed__7(void){
_start:
{
lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_314_ = lean_obj_once(&l_Lean_Lsp_instFromJsonMessageActionItem_fromJson___closed__6, &l_Lean_Lsp_instFromJsonMessageActionItem_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonMessageActionItem_fromJson___closed__6);
v___x_315_ = lean_obj_once(&l_Lean_Lsp_instFromJsonMessageActionItem_fromJson___closed__4, &l_Lean_Lsp_instFromJsonMessageActionItem_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonMessageActionItem_fromJson___closed__4);
v___x_316_ = lean_string_append(v___x_315_, v___x_314_);
return v___x_316_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonMessageActionItem_fromJson___closed__8(void){
_start:
{
lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_317_ = ((lean_object*)(l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__11));
v___x_318_ = lean_obj_once(&l_Lean_Lsp_instFromJsonMessageActionItem_fromJson___closed__7, &l_Lean_Lsp_instFromJsonMessageActionItem_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonMessageActionItem_fromJson___closed__7);
v___x_319_ = lean_string_append(v___x_318_, v___x_317_);
return v___x_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonMessageActionItem_fromJson(lean_object* v_json_320_){
_start:
{
lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_321_ = ((lean_object*)(l_Lean_Lsp_instFromJsonMessageActionItem_fromJson___closed__0));
v___x_322_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageParams_fromJson_spec__1(v_json_320_, v___x_321_);
if (lean_obj_tag(v___x_322_) == 0)
{
lean_object* v_a_323_; lean_object* v___x_325_; uint8_t v_isShared_326_; uint8_t v_isSharedCheck_332_; 
v_a_323_ = lean_ctor_get(v___x_322_, 0);
v_isSharedCheck_332_ = !lean_is_exclusive(v___x_322_);
if (v_isSharedCheck_332_ == 0)
{
v___x_325_ = v___x_322_;
v_isShared_326_ = v_isSharedCheck_332_;
goto v_resetjp_324_;
}
else
{
lean_inc(v_a_323_);
lean_dec(v___x_322_);
v___x_325_ = lean_box(0);
v_isShared_326_ = v_isSharedCheck_332_;
goto v_resetjp_324_;
}
v_resetjp_324_:
{
lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_330_; 
v___x_327_ = lean_obj_once(&l_Lean_Lsp_instFromJsonMessageActionItem_fromJson___closed__8, &l_Lean_Lsp_instFromJsonMessageActionItem_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonMessageActionItem_fromJson___closed__8);
v___x_328_ = lean_string_append(v___x_327_, v_a_323_);
lean_dec(v_a_323_);
if (v_isShared_326_ == 0)
{
lean_ctor_set(v___x_325_, 0, v___x_328_);
v___x_330_ = v___x_325_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v___x_328_);
v___x_330_ = v_reuseFailAlloc_331_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
return v___x_330_;
}
}
}
else
{
lean_object* v_a_333_; lean_object* v___x_335_; uint8_t v_isShared_336_; uint8_t v_isSharedCheck_340_; 
v_a_333_ = lean_ctor_get(v___x_322_, 0);
v_isSharedCheck_340_ = !lean_is_exclusive(v___x_322_);
if (v_isSharedCheck_340_ == 0)
{
v___x_335_ = v___x_322_;
v_isShared_336_ = v_isSharedCheck_340_;
goto v_resetjp_334_;
}
else
{
lean_inc(v_a_333_);
lean_dec(v___x_322_);
v___x_335_ = lean_box(0);
v_isShared_336_ = v_isSharedCheck_340_;
goto v_resetjp_334_;
}
v_resetjp_334_:
{
lean_object* v___x_338_; 
if (v_isShared_336_ == 0)
{
v___x_338_ = v___x_335_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v_a_333_);
v___x_338_ = v_reuseFailAlloc_339_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
return v___x_338_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonMessageActionItem_toJson(lean_object* v_x_343_){
_start:
{
lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
v___x_344_ = ((lean_object*)(l_Lean_Lsp_instFromJsonMessageActionItem_fromJson___closed__0));
v___x_345_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_345_, 0, v_x_343_);
v___x_346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_346_, 0, v___x_344_);
lean_ctor_set(v___x_346_, 1, v___x_345_);
v___x_347_ = lean_box(0);
v___x_348_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_348_, 0, v___x_346_);
lean_ctor_set(v___x_348_, 1, v___x_347_);
v___x_349_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_349_, 0, v___x_348_);
lean_ctor_set(v___x_349_, 1, v___x_347_);
v___x_350_ = ((lean_object*)(l_Lean_Lsp_instToJsonShowMessageParams_toJson___closed__0));
v___x_351_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonShowMessageParams_toJson_spec__0(v___x_349_, v___x_350_);
v___x_352_ = l_Lean_Json_mkObj(v___x_351_);
lean_dec(v___x_351_);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0_spec__1_spec__2(size_t v_sz_355_, size_t v_i_356_, lean_object* v_bs_357_){
_start:
{
uint8_t v___x_358_; 
v___x_358_ = lean_usize_dec_lt(v_i_356_, v_sz_355_);
if (v___x_358_ == 0)
{
lean_object* v___x_359_; 
v___x_359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_359_, 0, v_bs_357_);
return v___x_359_;
}
else
{
lean_object* v_v_360_; lean_object* v___x_361_; 
v_v_360_ = lean_array_uget_borrowed(v_bs_357_, v_i_356_);
lean_inc(v_v_360_);
v___x_361_ = l_Lean_Lsp_instFromJsonMessageActionItem_fromJson(v_v_360_);
if (lean_obj_tag(v___x_361_) == 0)
{
lean_object* v_a_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_369_; 
lean_dec_ref(v_bs_357_);
v_a_362_ = lean_ctor_get(v___x_361_, 0);
v_isSharedCheck_369_ = !lean_is_exclusive(v___x_361_);
if (v_isSharedCheck_369_ == 0)
{
v___x_364_ = v___x_361_;
v_isShared_365_ = v_isSharedCheck_369_;
goto v_resetjp_363_;
}
else
{
lean_inc(v_a_362_);
lean_dec(v___x_361_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_369_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
lean_object* v___x_367_; 
if (v_isShared_365_ == 0)
{
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
lean_object* v_a_370_; lean_object* v___x_371_; lean_object* v_bs_x27_372_; size_t v___x_373_; size_t v___x_374_; lean_object* v___x_375_; 
v_a_370_ = lean_ctor_get(v___x_361_, 0);
lean_inc(v_a_370_);
lean_dec_ref_known(v___x_361_, 1);
v___x_371_ = lean_unsigned_to_nat(0u);
v_bs_x27_372_ = lean_array_uset(v_bs_357_, v_i_356_, v___x_371_);
v___x_373_ = ((size_t)1ULL);
v___x_374_ = lean_usize_add(v_i_356_, v___x_373_);
v___x_375_ = lean_array_uset(v_bs_x27_372_, v_i_356_, v_a_370_);
v_i_356_ = v___x_374_;
v_bs_357_ = v___x_375_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_sz_377_, lean_object* v_i_378_, lean_object* v_bs_379_){
_start:
{
size_t v_sz_boxed_380_; size_t v_i_boxed_381_; lean_object* v_res_382_; 
v_sz_boxed_380_ = lean_unbox_usize(v_sz_377_);
lean_dec(v_sz_377_);
v_i_boxed_381_ = lean_unbox_usize(v_i_378_);
lean_dec(v_i_378_);
v_res_382_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0_spec__1_spec__2(v_sz_boxed_380_, v_i_boxed_381_, v_bs_379_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0_spec__1(lean_object* v_x_385_){
_start:
{
if (lean_obj_tag(v_x_385_) == 4)
{
lean_object* v_elems_386_; size_t v_sz_387_; size_t v___x_388_; lean_object* v___x_389_; 
v_elems_386_ = lean_ctor_get(v_x_385_, 0);
lean_inc_ref(v_elems_386_);
lean_dec_ref_known(v_x_385_, 1);
v_sz_387_ = lean_array_size(v_elems_386_);
v___x_388_ = ((size_t)0ULL);
v___x_389_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0_spec__1_spec__2(v_sz_387_, v___x_388_, v_elems_386_);
return v___x_389_;
}
else
{
lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; 
v___x_390_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0_spec__1___closed__0));
v___x_391_ = lean_unsigned_to_nat(80u);
v___x_392_ = l_Lean_Json_pretty(v_x_385_, v___x_391_);
v___x_393_ = lean_string_append(v___x_390_, v___x_392_);
lean_dec_ref(v___x_392_);
v___x_394_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0_spec__1___closed__1));
v___x_395_ = lean_string_append(v___x_393_, v___x_394_);
v___x_396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_396_, 0, v___x_395_);
return v___x_396_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0(lean_object* v_x_399_){
_start:
{
if (lean_obj_tag(v_x_399_) == 0)
{
lean_object* v___x_400_; 
v___x_400_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0___closed__0));
return v___x_400_;
}
else
{
lean_object* v___x_401_; 
v___x_401_ = l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0_spec__1(v_x_399_);
if (lean_obj_tag(v___x_401_) == 0)
{
lean_object* v_a_402_; lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_409_; 
v_a_402_ = lean_ctor_get(v___x_401_, 0);
v_isSharedCheck_409_ = !lean_is_exclusive(v___x_401_);
if (v_isSharedCheck_409_ == 0)
{
v___x_404_ = v___x_401_;
v_isShared_405_ = v_isSharedCheck_409_;
goto v_resetjp_403_;
}
else
{
lean_inc(v_a_402_);
lean_dec(v___x_401_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_409_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
lean_object* v___x_407_; 
if (v_isShared_405_ == 0)
{
v___x_407_ = v___x_404_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v_a_402_);
v___x_407_ = v_reuseFailAlloc_408_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
return v___x_407_;
}
}
}
else
{
lean_object* v_a_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_418_; 
v_a_410_ = lean_ctor_get(v___x_401_, 0);
v_isSharedCheck_418_ = !lean_is_exclusive(v___x_401_);
if (v_isSharedCheck_418_ == 0)
{
v___x_412_ = v___x_401_;
v_isShared_413_ = v_isSharedCheck_418_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_a_410_);
lean_dec(v___x_401_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_418_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
lean_object* v___x_414_; lean_object* v___x_416_; 
v___x_414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_414_, 0, v_a_410_);
if (v_isShared_413_ == 0)
{
lean_ctor_set(v___x_412_, 0, v___x_414_);
v___x_416_ = v___x_412_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v___x_414_);
v___x_416_ = v_reuseFailAlloc_417_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
return v___x_416_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson_spec__0(lean_object* v_j_419_, lean_object* v_k_420_){
_start:
{
lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_421_ = l_Lean_Json_getObjValD(v_j_419_, v_k_420_);
v___x_422_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0(v___x_421_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson_spec__0___boxed(lean_object* v_j_423_, lean_object* v_k_424_){
_start:
{
lean_object* v_res_425_; 
v_res_425_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson_spec__0(v_j_423_, v_k_424_);
lean_dec_ref(v_k_424_);
return v_res_425_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__2(void){
_start:
{
uint8_t v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_431_ = 1;
v___x_432_ = ((lean_object*)(l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__1));
v___x_433_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_432_, v___x_431_);
return v___x_433_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__3(void){
_start:
{
lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_434_ = ((lean_object*)(l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__6));
v___x_435_ = lean_obj_once(&l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__2, &l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__2);
v___x_436_ = lean_string_append(v___x_435_, v___x_434_);
return v___x_436_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_437_ = lean_obj_once(&l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__9, &l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__9);
v___x_438_ = lean_obj_once(&l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__3);
v___x_439_ = lean_string_append(v___x_438_, v___x_437_);
return v___x_439_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__5(void){
_start:
{
lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_440_ = ((lean_object*)(l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__11));
v___x_441_ = lean_obj_once(&l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__4);
v___x_442_ = lean_string_append(v___x_441_, v___x_440_);
return v___x_442_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__6(void){
_start:
{
lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_443_ = lean_obj_once(&l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__15, &l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__15_once, _init_l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__15);
v___x_444_ = lean_obj_once(&l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__3);
v___x_445_ = lean_string_append(v___x_444_, v___x_443_);
return v___x_445_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__7(void){
_start:
{
lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; 
v___x_446_ = ((lean_object*)(l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__11));
v___x_447_ = lean_obj_once(&l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__6, &l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__6);
v___x_448_ = lean_string_append(v___x_447_, v___x_446_);
return v___x_448_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__11(void){
_start:
{
uint8_t v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; 
v___x_453_ = 1;
v___x_454_ = ((lean_object*)(l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__10));
v___x_455_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_454_, v___x_453_);
return v___x_455_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__12(void){
_start:
{
lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; 
v___x_456_ = lean_obj_once(&l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__11, &l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__11);
v___x_457_ = lean_obj_once(&l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__3);
v___x_458_ = lean_string_append(v___x_457_, v___x_456_);
return v___x_458_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__13(void){
_start:
{
lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; 
v___x_459_ = ((lean_object*)(l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__11));
v___x_460_ = lean_obj_once(&l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__12, &l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__12);
v___x_461_ = lean_string_append(v___x_460_, v___x_459_);
return v___x_461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson(lean_object* v_json_462_){
_start:
{
lean_object* v___x_463_; lean_object* v___x_464_; 
v___x_463_ = ((lean_object*)(l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__0));
lean_inc(v_json_462_);
v___x_464_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageParams_fromJson_spec__0(v_json_462_, v___x_463_);
if (lean_obj_tag(v___x_464_) == 0)
{
lean_object* v_a_465_; lean_object* v___x_467_; uint8_t v_isShared_468_; uint8_t v_isSharedCheck_474_; 
lean_dec(v_json_462_);
v_a_465_ = lean_ctor_get(v___x_464_, 0);
v_isSharedCheck_474_ = !lean_is_exclusive(v___x_464_);
if (v_isSharedCheck_474_ == 0)
{
v___x_467_ = v___x_464_;
v_isShared_468_ = v_isSharedCheck_474_;
goto v_resetjp_466_;
}
else
{
lean_inc(v_a_465_);
lean_dec(v___x_464_);
v___x_467_ = lean_box(0);
v_isShared_468_ = v_isSharedCheck_474_;
goto v_resetjp_466_;
}
v_resetjp_466_:
{
lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_472_; 
v___x_469_ = lean_obj_once(&l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__5, &l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__5);
v___x_470_ = lean_string_append(v___x_469_, v_a_465_);
lean_dec(v_a_465_);
if (v_isShared_468_ == 0)
{
lean_ctor_set(v___x_467_, 0, v___x_470_);
v___x_472_ = v___x_467_;
goto v_reusejp_471_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v___x_470_);
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
lean_object* v_a_475_; lean_object* v___x_476_; lean_object* v___x_477_; 
v_a_475_ = lean_ctor_get(v___x_464_, 0);
lean_inc(v_a_475_);
lean_dec_ref_known(v___x_464_, 1);
v___x_476_ = ((lean_object*)(l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__13));
lean_inc(v_json_462_);
v___x_477_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageParams_fromJson_spec__1(v_json_462_, v___x_476_);
if (lean_obj_tag(v___x_477_) == 0)
{
lean_object* v_a_478_; lean_object* v___x_480_; uint8_t v_isShared_481_; uint8_t v_isSharedCheck_487_; 
lean_dec(v_a_475_);
lean_dec(v_json_462_);
v_a_478_ = lean_ctor_get(v___x_477_, 0);
v_isSharedCheck_487_ = !lean_is_exclusive(v___x_477_);
if (v_isSharedCheck_487_ == 0)
{
v___x_480_ = v___x_477_;
v_isShared_481_ = v_isSharedCheck_487_;
goto v_resetjp_479_;
}
else
{
lean_inc(v_a_478_);
lean_dec(v___x_477_);
v___x_480_ = lean_box(0);
v_isShared_481_ = v_isSharedCheck_487_;
goto v_resetjp_479_;
}
v_resetjp_479_:
{
lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_485_; 
v___x_482_ = lean_obj_once(&l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__7);
v___x_483_ = lean_string_append(v___x_482_, v_a_478_);
lean_dec(v_a_478_);
if (v_isShared_481_ == 0)
{
lean_ctor_set(v___x_480_, 0, v___x_483_);
v___x_485_ = v___x_480_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v___x_483_);
v___x_485_ = v_reuseFailAlloc_486_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
return v___x_485_;
}
}
}
else
{
lean_object* v_a_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
v_a_488_ = lean_ctor_get(v___x_477_, 0);
lean_inc(v_a_488_);
lean_dec_ref_known(v___x_477_, 1);
v___x_489_ = ((lean_object*)(l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__8));
v___x_490_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson_spec__0(v_json_462_, v___x_489_);
if (lean_obj_tag(v___x_490_) == 0)
{
lean_object* v_a_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_500_; 
lean_dec(v_a_488_);
lean_dec(v_a_475_);
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
v___x_495_ = lean_obj_once(&l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__13, &l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__13);
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
lean_object* v_a_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_510_; 
v_a_501_ = lean_ctor_get(v___x_490_, 0);
v_isSharedCheck_510_ = !lean_is_exclusive(v___x_490_);
if (v_isSharedCheck_510_ == 0)
{
v___x_503_ = v___x_490_;
v_isShared_504_ = v_isSharedCheck_510_;
goto v_resetjp_502_;
}
else
{
lean_inc(v_a_501_);
lean_dec(v___x_490_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_510_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
lean_object* v___x_505_; uint8_t v___x_506_; lean_object* v___x_508_; 
v___x_505_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_505_, 0, v_a_488_);
lean_ctor_set(v___x_505_, 1, v_a_501_);
v___x_506_ = lean_unbox(v_a_475_);
lean_dec(v_a_475_);
lean_ctor_set_uint8(v___x_505_, sizeof(void*)*2, v___x_506_);
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 0, v___x_505_);
v___x_508_ = v___x_503_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v___x_505_);
v___x_508_ = v_reuseFailAlloc_509_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
return v___x_508_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonShowMessageRequestParams_toJson_spec__0_spec__0_spec__1(size_t v_sz_513_, size_t v_i_514_, lean_object* v_bs_515_){
_start:
{
uint8_t v___x_516_; 
v___x_516_ = lean_usize_dec_lt(v_i_514_, v_sz_513_);
if (v___x_516_ == 0)
{
return v_bs_515_;
}
else
{
lean_object* v_v_517_; lean_object* v___x_518_; lean_object* v_bs_x27_519_; lean_object* v___x_520_; size_t v___x_521_; size_t v___x_522_; lean_object* v___x_523_; 
v_v_517_ = lean_array_uget(v_bs_515_, v_i_514_);
v___x_518_ = lean_unsigned_to_nat(0u);
v_bs_x27_519_ = lean_array_uset(v_bs_515_, v_i_514_, v___x_518_);
v___x_520_ = l_Lean_Lsp_instToJsonMessageActionItem_toJson(v_v_517_);
v___x_521_ = ((size_t)1ULL);
v___x_522_ = lean_usize_add(v_i_514_, v___x_521_);
v___x_523_ = lean_array_uset(v_bs_x27_519_, v_i_514_, v___x_520_);
v_i_514_ = v___x_522_;
v_bs_515_ = v___x_523_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonShowMessageRequestParams_toJson_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_525_, lean_object* v_i_526_, lean_object* v_bs_527_){
_start:
{
size_t v_sz_boxed_528_; size_t v_i_boxed_529_; lean_object* v_res_530_; 
v_sz_boxed_528_ = lean_unbox_usize(v_sz_525_);
lean_dec(v_sz_525_);
v_i_boxed_529_ = lean_unbox_usize(v_i_526_);
lean_dec(v_i_526_);
v_res_530_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonShowMessageRequestParams_toJson_spec__0_spec__0_spec__1(v_sz_boxed_528_, v_i_boxed_529_, v_bs_527_);
return v_res_530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonShowMessageRequestParams_toJson_spec__0_spec__0(lean_object* v_a_531_){
_start:
{
size_t v_sz_532_; size_t v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; 
v_sz_532_ = lean_array_size(v_a_531_);
v___x_533_ = ((size_t)0ULL);
v___x_534_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonShowMessageRequestParams_toJson_spec__0_spec__0_spec__1(v_sz_532_, v___x_533_, v_a_531_);
v___x_535_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_535_, 0, v___x_534_);
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonShowMessageRequestParams_toJson_spec__0(lean_object* v_k_536_, lean_object* v_x_537_){
_start:
{
if (lean_obj_tag(v_x_537_) == 0)
{
lean_object* v___x_538_; 
lean_dec_ref(v_k_536_);
v___x_538_ = lean_box(0);
return v___x_538_;
}
else
{
lean_object* v_val_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; 
v_val_539_ = lean_ctor_get(v_x_537_, 0);
lean_inc(v_val_539_);
lean_dec_ref_known(v_x_537_, 1);
v___x_540_ = l_Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonShowMessageRequestParams_toJson_spec__0_spec__0(v_val_539_);
v___x_541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_541_, 0, v_k_536_);
lean_ctor_set(v___x_541_, 1, v___x_540_);
v___x_542_ = lean_box(0);
v___x_543_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_543_, 0, v___x_541_);
lean_ctor_set(v___x_543_, 1, v___x_542_);
return v___x_543_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonShowMessageRequestParams_toJson(lean_object* v_x_544_){
_start:
{
uint8_t v_type_545_; lean_object* v_message_546_; lean_object* v_actions_x3f_547_; lean_object* v___x_548_; lean_object* v___y_550_; 
v_type_545_ = lean_ctor_get_uint8(v_x_544_, sizeof(void*)*2);
v_message_546_ = lean_ctor_get(v_x_544_, 0);
lean_inc_ref(v_message_546_);
v_actions_x3f_547_ = lean_ctor_get(v_x_544_, 1);
lean_inc(v_actions_x3f_547_);
lean_dec_ref(v_x_544_);
v___x_548_ = ((lean_object*)(l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__0));
switch(v_type_545_)
{
case 0:
{
lean_object* v___x_566_; 
v___x_566_ = lean_obj_once(&l_Lean_Lsp_instToJsonMessageType___lam__0___closed__1, &l_Lean_Lsp_instToJsonMessageType___lam__0___closed__1_once, _init_l_Lean_Lsp_instToJsonMessageType___lam__0___closed__1);
v___y_550_ = v___x_566_;
goto v___jp_549_;
}
case 1:
{
lean_object* v___x_567_; 
v___x_567_ = lean_obj_once(&l_Lean_Lsp_instToJsonMessageType___lam__0___closed__3, &l_Lean_Lsp_instToJsonMessageType___lam__0___closed__3_once, _init_l_Lean_Lsp_instToJsonMessageType___lam__0___closed__3);
v___y_550_ = v___x_567_;
goto v___jp_549_;
}
case 2:
{
lean_object* v___x_568_; 
v___x_568_ = lean_obj_once(&l_Lean_Lsp_instToJsonMessageType___lam__0___closed__5, &l_Lean_Lsp_instToJsonMessageType___lam__0___closed__5_once, _init_l_Lean_Lsp_instToJsonMessageType___lam__0___closed__5);
v___y_550_ = v___x_568_;
goto v___jp_549_;
}
default: 
{
lean_object* v___x_569_; 
v___x_569_ = lean_obj_once(&l_Lean_Lsp_instToJsonMessageType___lam__0___closed__7, &l_Lean_Lsp_instToJsonMessageType___lam__0___closed__7_once, _init_l_Lean_Lsp_instToJsonMessageType___lam__0___closed__7);
v___y_550_ = v___x_569_;
goto v___jp_549_;
}
}
v___jp_549_:
{
lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; 
lean_inc(v___y_550_);
v___x_551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_551_, 0, v___x_548_);
lean_ctor_set(v___x_551_, 1, v___y_550_);
v___x_552_ = lean_box(0);
v___x_553_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_553_, 0, v___x_551_);
lean_ctor_set(v___x_553_, 1, v___x_552_);
v___x_554_ = ((lean_object*)(l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__13));
v___x_555_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_555_, 0, v_message_546_);
v___x_556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_556_, 0, v___x_554_);
lean_ctor_set(v___x_556_, 1, v___x_555_);
v___x_557_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_557_, 0, v___x_556_);
lean_ctor_set(v___x_557_, 1, v___x_552_);
v___x_558_ = ((lean_object*)(l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__8));
v___x_559_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonShowMessageRequestParams_toJson_spec__0(v___x_558_, v_actions_x3f_547_);
v___x_560_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_560_, 0, v___x_559_);
lean_ctor_set(v___x_560_, 1, v___x_552_);
v___x_561_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_561_, 0, v___x_557_);
lean_ctor_set(v___x_561_, 1, v___x_560_);
v___x_562_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_562_, 0, v___x_553_);
lean_ctor_set(v___x_562_, 1, v___x_561_);
v___x_563_ = ((lean_object*)(l_Lean_Lsp_instToJsonShowMessageParams_toJson___closed__0));
v___x_564_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonShowMessageParams_toJson_spec__0(v___x_562_, v___x_563_);
v___x_565_ = l_Lean_Json_mkObj(v___x_564_);
lean_dec(v___x_564_);
return v___x_565_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonShowMessageResponse___aux__1(lean_object* v_a_572_){
_start:
{
lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_573_ = ((lean_object*)(l_Lean_Lsp_instFromJsonMessageActionItem___closed__0));
v___x_574_ = l_Lean_Option_fromJson_x3f___redArg(v___x_573_, v_a_572_);
return v___x_574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Lsp_instFromJsonShowMessageResponse_spec__0(lean_object* v_x_577_){
_start:
{
if (lean_obj_tag(v_x_577_) == 0)
{
lean_object* v___x_578_; 
v___x_578_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Lsp_instFromJsonShowMessageResponse_spec__0___closed__0));
return v___x_578_;
}
else
{
lean_object* v___x_579_; 
v___x_579_ = l_Lean_Lsp_instFromJsonMessageActionItem_fromJson(v_x_577_);
if (lean_obj_tag(v___x_579_) == 0)
{
lean_object* v_a_580_; lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_587_; 
v_a_580_ = lean_ctor_get(v___x_579_, 0);
v_isSharedCheck_587_ = !lean_is_exclusive(v___x_579_);
if (v_isSharedCheck_587_ == 0)
{
v___x_582_ = v___x_579_;
v_isShared_583_ = v_isSharedCheck_587_;
goto v_resetjp_581_;
}
else
{
lean_inc(v_a_580_);
lean_dec(v___x_579_);
v___x_582_ = lean_box(0);
v_isShared_583_ = v_isSharedCheck_587_;
goto v_resetjp_581_;
}
v_resetjp_581_:
{
lean_object* v___x_585_; 
if (v_isShared_583_ == 0)
{
v___x_585_ = v___x_582_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v_a_580_);
v___x_585_ = v_reuseFailAlloc_586_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
return v___x_585_;
}
}
}
else
{
lean_object* v_a_588_; lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_596_; 
v_a_588_ = lean_ctor_get(v___x_579_, 0);
v_isSharedCheck_596_ = !lean_is_exclusive(v___x_579_);
if (v_isSharedCheck_596_ == 0)
{
v___x_590_ = v___x_579_;
v_isShared_591_ = v_isSharedCheck_596_;
goto v_resetjp_589_;
}
else
{
lean_inc(v_a_588_);
lean_dec(v___x_579_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_596_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
lean_object* v___x_592_; lean_object* v___x_594_; 
v___x_592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_592_, 0, v_a_588_);
if (v_isShared_591_ == 0)
{
lean_ctor_set(v___x_590_, 0, v___x_592_);
v___x_594_ = v___x_590_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v___x_592_);
v___x_594_ = v_reuseFailAlloc_595_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
return v___x_594_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonShowMessageResponse___aux__1(lean_object* v_a_599_){
_start:
{
lean_object* v___x_600_; lean_object* v___x_601_; 
v___x_600_ = ((lean_object*)(l_Lean_Lsp_instToJsonMessageActionItem___closed__0));
v___x_601_ = l_Lean_Option_toJson___redArg(v___x_600_, v_a_599_);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_toJson___at___00Lean_Lsp_instToJsonShowMessageResponse_spec__0(lean_object* v_x_602_){
_start:
{
if (lean_obj_tag(v_x_602_) == 0)
{
lean_object* v___x_603_; 
v___x_603_ = lean_box(0);
return v___x_603_;
}
else
{
lean_object* v_val_604_; lean_object* v___x_605_; 
v_val_604_ = lean_ctor_get(v_x_602_, 0);
lean_inc(v_val_604_);
lean_dec_ref_known(v_x_602_, 1);
v___x_605_ = l_Lean_Lsp_instToJsonMessageActionItem_toJson(v_val_604_);
return v___x_605_;
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

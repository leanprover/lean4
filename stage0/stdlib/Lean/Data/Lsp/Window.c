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
lean_object* l_Lean_Lsp_MessageType_ctorIdx___impl(uint8_t v_x_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(v_x_1_);
v___x_3_ = lean_obj_tag_nat(v___x_2_);
lean_dec(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT void l_Lean_Lsp_MessageType_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_1_ = stack[0].m_num;
lean_object* v_res_4_;
v_res_4_ = l_Lean_Lsp_MessageType_ctorIdx___impl(v_x_1_);
stack->m_obj
 = v_res_4_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_ctorIdx___impl___boxed(lean_object* v_x_5_){
_start:
{
uint8_t v_x_4__boxed_6_; lean_object* v_res_7_; 
v_x_4__boxed_6_ = lean_unbox(v_x_5_);
v_res_7_ = l_Lean_Lsp_MessageType_ctorIdx___impl(v_x_4__boxed_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_ctorElim___redArg(lean_object* v_k_8_){
_start:
{
lean_inc(v_k_8_);
return v_k_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_ctorElim___redArg___boxed(lean_object* v_k_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Lean_Lsp_MessageType_ctorElim___redArg(v_k_9_);
lean_dec(v_k_9_);
return v_res_10_;
}
}
lean_object* l_Lean_Lsp_MessageType_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, uint8_t v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_inc(v_k_15_);
return v_k_15_;
}
}
LEAN_EXPORT void l_Lean_Lsp_MessageType_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_12_ = stack[1].m_obj;
uint8_t v_t_13_ = stack[2].m_num;
lean_object* v_k_15_ = stack[4].m_obj;
lean_object* v_res_16_;
v_res_16_ = l_Lean_Lsp_MessageType_ctorElim(lean_box(0), v_ctorIdx_12_, v_t_13_, lean_box(0), v_k_15_);
stack->m_obj
 = v_res_16_;
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
lean_object* l_Lean_Lsp_MessageType_error_elim(lean_object* v_motive_27_, uint8_t v_t_28_, lean_object* v_h_29_, lean_object* v_error_30_){
_start:
{
lean_inc(v_error_30_);
return v_error_30_;
}
}
LEAN_EXPORT void l_Lean_Lsp_MessageType_error_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_28_ = stack[1].m_num;
lean_object* v_error_30_ = stack[3].m_obj;
lean_object* v_res_31_;
v_res_31_ = l_Lean_Lsp_MessageType_error_elim(lean_box(0), v_t_28_, lean_box(0), v_error_30_);
stack->m_obj
 = v_res_31_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_error_elim___boxed(lean_object* v_motive_32_, lean_object* v_t_33_, lean_object* v_h_34_, lean_object* v_error_35_){
_start:
{
uint8_t v_t_boxed_36_; lean_object* v_res_37_; 
v_t_boxed_36_ = lean_unbox(v_t_33_);
v_res_37_ = l_Lean_Lsp_MessageType_error_elim(v_motive_32_, v_t_boxed_36_, v_h_34_, v_error_35_);
lean_dec(v_error_35_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_warning_elim___redArg(lean_object* v_warning_38_){
_start:
{
lean_inc(v_warning_38_);
return v_warning_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_warning_elim___redArg___boxed(lean_object* v_warning_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Lean_Lsp_MessageType_warning_elim___redArg(v_warning_39_);
lean_dec(v_warning_39_);
return v_res_40_;
}
}
lean_object* l_Lean_Lsp_MessageType_warning_elim(lean_object* v_motive_41_, uint8_t v_t_42_, lean_object* v_h_43_, lean_object* v_warning_44_){
_start:
{
lean_inc(v_warning_44_);
return v_warning_44_;
}
}
LEAN_EXPORT void l_Lean_Lsp_MessageType_warning_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_42_ = stack[1].m_num;
lean_object* v_warning_44_ = stack[3].m_obj;
lean_object* v_res_45_;
v_res_45_ = l_Lean_Lsp_MessageType_warning_elim(lean_box(0), v_t_42_, lean_box(0), v_warning_44_);
stack->m_obj
 = v_res_45_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_warning_elim___boxed(lean_object* v_motive_46_, lean_object* v_t_47_, lean_object* v_h_48_, lean_object* v_warning_49_){
_start:
{
uint8_t v_t_boxed_50_; lean_object* v_res_51_; 
v_t_boxed_50_ = lean_unbox(v_t_47_);
v_res_51_ = l_Lean_Lsp_MessageType_warning_elim(v_motive_46_, v_t_boxed_50_, v_h_48_, v_warning_49_);
lean_dec(v_warning_49_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_info_elim___redArg(lean_object* v_info_52_){
_start:
{
lean_inc(v_info_52_);
return v_info_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_info_elim___redArg___boxed(lean_object* v_info_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l_Lean_Lsp_MessageType_info_elim___redArg(v_info_53_);
lean_dec(v_info_53_);
return v_res_54_;
}
}
lean_object* l_Lean_Lsp_MessageType_info_elim(lean_object* v_motive_55_, uint8_t v_t_56_, lean_object* v_h_57_, lean_object* v_info_58_){
_start:
{
lean_inc(v_info_58_);
return v_info_58_;
}
}
LEAN_EXPORT void l_Lean_Lsp_MessageType_info_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_56_ = stack[1].m_num;
lean_object* v_info_58_ = stack[3].m_obj;
lean_object* v_res_59_;
v_res_59_ = l_Lean_Lsp_MessageType_info_elim(lean_box(0), v_t_56_, lean_box(0), v_info_58_);
stack->m_obj
 = v_res_59_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_info_elim___boxed(lean_object* v_motive_60_, lean_object* v_t_61_, lean_object* v_h_62_, lean_object* v_info_63_){
_start:
{
uint8_t v_t_boxed_64_; lean_object* v_res_65_; 
v_t_boxed_64_ = lean_unbox(v_t_61_);
v_res_65_ = l_Lean_Lsp_MessageType_info_elim(v_motive_60_, v_t_boxed_64_, v_h_62_, v_info_63_);
lean_dec(v_info_63_);
return v_res_65_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_log_elim___redArg(lean_object* v_log_66_){
_start:
{
lean_inc(v_log_66_);
return v_log_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_log_elim___redArg___boxed(lean_object* v_log_67_){
_start:
{
lean_object* v_res_68_; 
v_res_68_ = l_Lean_Lsp_MessageType_log_elim___redArg(v_log_67_);
lean_dec(v_log_67_);
return v_res_68_;
}
}
lean_object* l_Lean_Lsp_MessageType_log_elim(lean_object* v_motive_69_, uint8_t v_t_70_, lean_object* v_h_71_, lean_object* v_log_72_){
_start:
{
lean_inc(v_log_72_);
return v_log_72_;
}
}
LEAN_EXPORT void l_Lean_Lsp_MessageType_log_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_70_ = stack[1].m_num;
lean_object* v_log_72_ = stack[3].m_obj;
lean_object* v_res_73_;
v_res_73_ = l_Lean_Lsp_MessageType_log_elim(lean_box(0), v_t_70_, lean_box(0), v_log_72_);
stack->m_obj
 = v_res_73_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MessageType_log_elim___boxed(lean_object* v_motive_74_, lean_object* v_t_75_, lean_object* v_h_76_, lean_object* v_log_77_){
_start:
{
uint8_t v_t_boxed_78_; lean_object* v_res_79_; 
v_t_boxed_78_ = lean_unbox(v_t_75_);
v_res_79_ = l_Lean_Lsp_MessageType_log_elim(v_motive_74_, v_t_boxed_78_, v_h_76_, v_log_77_);
lean_dec(v_log_77_);
return v_res_79_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonMessageType___lam__0___closed__2(void){
_start:
{
lean_object* v_natZero_83_; lean_object* v_intZero_84_; 
v_natZero_83_ = lean_unsigned_to_nat(0u);
v_intZero_84_ = lean_nat_to_int(v_natZero_83_);
return v_intZero_84_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonMessageType___lam__0(lean_object* v_x_97_){
_start:
{
if (lean_obj_tag(v_x_97_) == 2)
{
lean_object* v_n_100_; lean_object* v_mantissa_101_; lean_object* v_exponent_102_; lean_object* v_natZero_103_; lean_object* v_intZero_104_; uint8_t v_isNeg_105_; 
v_n_100_ = lean_ctor_get(v_x_97_, 0);
v_mantissa_101_ = lean_ctor_get(v_n_100_, 0);
v_exponent_102_ = lean_ctor_get(v_n_100_, 1);
v_natZero_103_ = lean_unsigned_to_nat(0u);
v_intZero_104_ = lean_obj_once(&l_Lean_Lsp_instFromJsonMessageType___lam__0___closed__2, &l_Lean_Lsp_instFromJsonMessageType___lam__0___closed__2_once, _init_l_Lean_Lsp_instFromJsonMessageType___lam__0___closed__2);
v_isNeg_105_ = lean_int_dec_lt(v_mantissa_101_, v_intZero_104_);
if (v_isNeg_105_ == 0)
{
lean_object* v_a_106_; lean_object* v___x_107_; uint8_t v___x_108_; 
v_a_106_ = lean_nat_abs(v_mantissa_101_);
v___x_107_ = lean_unsigned_to_nat(1u);
v___x_108_ = lean_nat_dec_eq(v_a_106_, v___x_107_);
if (v___x_108_ == 0)
{
lean_object* v___x_109_; uint8_t v___x_110_; 
v___x_109_ = lean_unsigned_to_nat(2u);
v___x_110_ = lean_nat_dec_eq(v_a_106_, v___x_109_);
if (v___x_110_ == 0)
{
lean_object* v___x_111_; uint8_t v___x_112_; 
v___x_111_ = lean_unsigned_to_nat(3u);
v___x_112_ = lean_nat_dec_eq(v_a_106_, v___x_111_);
if (v___x_112_ == 0)
{
lean_object* v___x_113_; uint8_t v___x_114_; 
v___x_113_ = lean_unsigned_to_nat(4u);
v___x_114_ = lean_nat_dec_eq(v_a_106_, v___x_113_);
lean_dec(v_a_106_);
if (v___x_114_ == 0)
{
goto v___jp_98_;
}
else
{
uint8_t v___x_115_; 
v___x_115_ = lean_nat_dec_eq(v_exponent_102_, v_natZero_103_);
if (v___x_115_ == 0)
{
goto v___jp_98_;
}
else
{
lean_object* v___x_116_; 
v___x_116_ = ((lean_object*)(l_Lean_Lsp_instFromJsonMessageType___lam__0___closed__3));
return v___x_116_;
}
}
}
else
{
uint8_t v___x_117_; 
lean_dec(v_a_106_);
v___x_117_ = lean_nat_dec_eq(v_exponent_102_, v_natZero_103_);
if (v___x_117_ == 0)
{
goto v___jp_98_;
}
else
{
lean_object* v___x_118_; 
v___x_118_ = ((lean_object*)(l_Lean_Lsp_instFromJsonMessageType___lam__0___closed__4));
return v___x_118_;
}
}
}
else
{
uint8_t v___x_119_; 
lean_dec(v_a_106_);
v___x_119_ = lean_nat_dec_eq(v_exponent_102_, v_natZero_103_);
if (v___x_119_ == 0)
{
goto v___jp_98_;
}
else
{
lean_object* v___x_120_; 
v___x_120_ = ((lean_object*)(l_Lean_Lsp_instFromJsonMessageType___lam__0___closed__5));
return v___x_120_;
}
}
}
else
{
uint8_t v___x_121_; 
lean_dec(v_a_106_);
v___x_121_ = lean_nat_dec_eq(v_exponent_102_, v_natZero_103_);
if (v___x_121_ == 0)
{
goto v___jp_98_;
}
else
{
lean_object* v___x_122_; 
v___x_122_ = ((lean_object*)(l_Lean_Lsp_instFromJsonMessageType___lam__0___closed__6));
return v___x_122_;
}
}
}
else
{
goto v___jp_98_;
}
}
else
{
goto v___jp_98_;
}
v___jp_98_:
{
lean_object* v___x_99_; 
v___x_99_ = ((lean_object*)(l_Lean_Lsp_instFromJsonMessageType___lam__0___closed__1));
return v___x_99_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonMessageType___lam__0___boxed(lean_object* v_x_123_){
_start:
{
lean_object* v_res_124_; 
v_res_124_ = l_Lean_Lsp_instFromJsonMessageType___lam__0(v_x_123_);
lean_dec(v_x_123_);
return v_res_124_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonMessageType___lam__0___closed__0(void){
_start:
{
lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_127_ = lean_unsigned_to_nat(1u);
v___x_128_ = l_Lean_JsonNumber_fromNat(v___x_127_);
return v___x_128_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonMessageType___lam__0___closed__1(void){
_start:
{
lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_129_ = lean_obj_once(&l_Lean_Lsp_instToJsonMessageType___lam__0___closed__0, &l_Lean_Lsp_instToJsonMessageType___lam__0___closed__0_once, _init_l_Lean_Lsp_instToJsonMessageType___lam__0___closed__0);
v___x_130_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_130_, 0, v___x_129_);
return v___x_130_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonMessageType___lam__0___closed__2(void){
_start:
{
lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_131_ = lean_unsigned_to_nat(2u);
v___x_132_ = l_Lean_JsonNumber_fromNat(v___x_131_);
return v___x_132_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonMessageType___lam__0___closed__3(void){
_start:
{
lean_object* v___x_133_; lean_object* v___x_134_; 
v___x_133_ = lean_obj_once(&l_Lean_Lsp_instToJsonMessageType___lam__0___closed__2, &l_Lean_Lsp_instToJsonMessageType___lam__0___closed__2_once, _init_l_Lean_Lsp_instToJsonMessageType___lam__0___closed__2);
v___x_134_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_134_, 0, v___x_133_);
return v___x_134_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonMessageType___lam__0___closed__4(void){
_start:
{
lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_135_ = lean_unsigned_to_nat(3u);
v___x_136_ = l_Lean_JsonNumber_fromNat(v___x_135_);
return v___x_136_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonMessageType___lam__0___closed__5(void){
_start:
{
lean_object* v___x_137_; lean_object* v___x_138_; 
v___x_137_ = lean_obj_once(&l_Lean_Lsp_instToJsonMessageType___lam__0___closed__4, &l_Lean_Lsp_instToJsonMessageType___lam__0___closed__4_once, _init_l_Lean_Lsp_instToJsonMessageType___lam__0___closed__4);
v___x_138_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_138_, 0, v___x_137_);
return v___x_138_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonMessageType___lam__0___closed__6(void){
_start:
{
lean_object* v___x_139_; lean_object* v___x_140_; 
v___x_139_ = lean_unsigned_to_nat(4u);
v___x_140_ = l_Lean_JsonNumber_fromNat(v___x_139_);
return v___x_140_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonMessageType___lam__0___closed__7(void){
_start:
{
lean_object* v___x_141_; lean_object* v___x_142_; 
v___x_141_ = lean_obj_once(&l_Lean_Lsp_instToJsonMessageType___lam__0___closed__6, &l_Lean_Lsp_instToJsonMessageType___lam__0___closed__6_once, _init_l_Lean_Lsp_instToJsonMessageType___lam__0___closed__6);
v___x_142_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_142_, 0, v___x_141_);
return v___x_142_;
}
}
lean_object* l_Lean_Lsp_instToJsonMessageType___lam__0(uint8_t v_x_143_){
_start:
{
switch(v_x_143_)
{
case 0:
{
lean_object* v___x_144_; 
v___x_144_ = lean_obj_once(&l_Lean_Lsp_instToJsonMessageType___lam__0___closed__1, &l_Lean_Lsp_instToJsonMessageType___lam__0___closed__1_once, _init_l_Lean_Lsp_instToJsonMessageType___lam__0___closed__1);
return v___x_144_;
}
case 1:
{
lean_object* v___x_145_; 
v___x_145_ = lean_obj_once(&l_Lean_Lsp_instToJsonMessageType___lam__0___closed__3, &l_Lean_Lsp_instToJsonMessageType___lam__0___closed__3_once, _init_l_Lean_Lsp_instToJsonMessageType___lam__0___closed__3);
return v___x_145_;
}
case 2:
{
lean_object* v___x_146_; 
v___x_146_ = lean_obj_once(&l_Lean_Lsp_instToJsonMessageType___lam__0___closed__5, &l_Lean_Lsp_instToJsonMessageType___lam__0___closed__5_once, _init_l_Lean_Lsp_instToJsonMessageType___lam__0___closed__5);
return v___x_146_;
}
default: 
{
lean_object* v___x_147_; 
v___x_147_ = lean_obj_once(&l_Lean_Lsp_instToJsonMessageType___lam__0___closed__7, &l_Lean_Lsp_instToJsonMessageType___lam__0___closed__7_once, _init_l_Lean_Lsp_instToJsonMessageType___lam__0___closed__7);
return v___x_147_;
}
}
}
}
LEAN_EXPORT void l_Lean_Lsp_instToJsonMessageType___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_143_ = stack[0].m_num;
lean_object* v_res_148_;
v_res_148_ = l_Lean_Lsp_instToJsonMessageType___lam__0(v_x_143_);
stack->m_obj
 = v_res_148_;
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
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0_spec__1_spec__2(size_t v_sz_386_, size_t v_i_387_, lean_object* v_bs_388_){
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
size_t v_sz_386_ = stack[0].m_num;
size_t v_i_387_ = stack[1].m_num;
lean_object* v_bs_388_ = stack[2].m_obj;
lean_object* v_res_408_;
v_res_408_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0_spec__1_spec__2(v_sz_386_, v_i_387_, v_bs_388_);
stack->m_obj
 = v_res_408_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_sz_409_, lean_object* v_i_410_, lean_object* v_bs_411_){
_start:
{
size_t v_sz_boxed_412_; size_t v_i_boxed_413_; lean_object* v_res_414_; 
v_sz_boxed_412_ = lean_unbox_usize(v_sz_409_);
lean_dec(v_sz_409_);
v_i_boxed_413_ = lean_unbox_usize(v_i_410_);
lean_dec(v_i_410_);
v_res_414_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0_spec__1_spec__2(v_sz_boxed_412_, v_i_boxed_413_, v_bs_411_);
return v_res_414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0_spec__1(lean_object* v_x_417_){
_start:
{
if (lean_obj_tag(v_x_417_) == 4)
{
lean_object* v_elems_418_; size_t v_sz_419_; size_t v___x_420_; lean_object* v___x_421_; 
v_elems_418_ = lean_ctor_get(v_x_417_, 0);
lean_inc_ref(v_elems_418_);
lean_dec_ref_known(v_x_417_, 1);
v_sz_419_ = lean_array_size(v_elems_418_);
v___x_420_ = ((size_t)0ULL);
v___x_421_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0_spec__1_spec__2(v_sz_419_, v___x_420_, v_elems_418_);
return v___x_421_;
}
else
{
lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_422_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0_spec__1___closed__0));
v___x_423_ = lean_unsigned_to_nat(80u);
v___x_424_ = l_Lean_Json_pretty(v_x_417_, v___x_423_);
v___x_425_ = lean_string_append(v___x_422_, v___x_424_);
lean_dec_ref(v___x_424_);
v___x_426_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0_spec__1___closed__1));
v___x_427_ = lean_string_append(v___x_425_, v___x_426_);
v___x_428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_428_, 0, v___x_427_);
return v___x_428_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0(lean_object* v_x_431_){
_start:
{
if (lean_obj_tag(v_x_431_) == 0)
{
lean_object* v___x_432_; 
v___x_432_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0___closed__0));
return v___x_432_;
}
else
{
lean_object* v___x_433_; 
v___x_433_ = l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0_spec__1(v_x_431_);
if (lean_obj_tag(v___x_433_) == 0)
{
lean_object* v_a_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_441_; 
v_a_434_ = lean_ctor_get(v___x_433_, 0);
v_isSharedCheck_441_ = !lean_is_exclusive(v___x_433_);
if (v_isSharedCheck_441_ == 0)
{
v___x_436_ = v___x_433_;
v_isShared_437_ = v_isSharedCheck_441_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_a_434_);
lean_dec(v___x_433_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_441_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
lean_object* v___x_439_; 
if (v_isShared_437_ == 0)
{
v___x_439_ = v___x_436_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v_a_434_);
v___x_439_ = v_reuseFailAlloc_440_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
return v___x_439_;
}
}
}
else
{
lean_object* v_a_442_; lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_450_; 
v_a_442_ = lean_ctor_get(v___x_433_, 0);
v_isSharedCheck_450_ = !lean_is_exclusive(v___x_433_);
if (v_isSharedCheck_450_ == 0)
{
v___x_444_ = v___x_433_;
v_isShared_445_ = v_isSharedCheck_450_;
goto v_resetjp_443_;
}
else
{
lean_inc(v_a_442_);
lean_dec(v___x_433_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_450_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
lean_object* v___x_446_; lean_object* v___x_448_; 
v___x_446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_446_, 0, v_a_442_);
if (v_isShared_445_ == 0)
{
lean_ctor_set(v___x_444_, 0, v___x_446_);
v___x_448_ = v___x_444_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_449_; 
v_reuseFailAlloc_449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_449_, 0, v___x_446_);
v___x_448_ = v_reuseFailAlloc_449_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
return v___x_448_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson_spec__0(lean_object* v_j_451_, lean_object* v_k_452_){
_start:
{
lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_453_ = l_Lean_Json_getObjValD(v_j_451_, v_k_452_);
v___x_454_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0(v___x_453_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson_spec__0___boxed(lean_object* v_j_455_, lean_object* v_k_456_){
_start:
{
lean_object* v_res_457_; 
v_res_457_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson_spec__0(v_j_455_, v_k_456_);
lean_dec_ref(v_k_456_);
return v_res_457_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__2(void){
_start:
{
uint8_t v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_463_ = 1;
v___x_464_ = ((lean_object*)(l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__1));
v___x_465_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_464_, v___x_463_);
return v___x_465_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__3(void){
_start:
{
lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; 
v___x_466_ = ((lean_object*)(l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__6));
v___x_467_ = lean_obj_once(&l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__2, &l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__2);
v___x_468_ = lean_string_append(v___x_467_, v___x_466_);
return v___x_468_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_469_ = lean_obj_once(&l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__9, &l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__9);
v___x_470_ = lean_obj_once(&l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__3);
v___x_471_ = lean_string_append(v___x_470_, v___x_469_);
return v___x_471_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__5(void){
_start:
{
lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_472_ = ((lean_object*)(l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__11));
v___x_473_ = lean_obj_once(&l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__4);
v___x_474_ = lean_string_append(v___x_473_, v___x_472_);
return v___x_474_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__6(void){
_start:
{
lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_475_ = lean_obj_once(&l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__15, &l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__15_once, _init_l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__15);
v___x_476_ = lean_obj_once(&l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__3);
v___x_477_ = lean_string_append(v___x_476_, v___x_475_);
return v___x_477_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__7(void){
_start:
{
lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_478_ = ((lean_object*)(l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__11));
v___x_479_ = lean_obj_once(&l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__6, &l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__6);
v___x_480_ = lean_string_append(v___x_479_, v___x_478_);
return v___x_480_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__11(void){
_start:
{
uint8_t v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; 
v___x_485_ = 1;
v___x_486_ = ((lean_object*)(l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__10));
v___x_487_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_486_, v___x_485_);
return v___x_487_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__12(void){
_start:
{
lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_488_ = lean_obj_once(&l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__11, &l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__11);
v___x_489_ = lean_obj_once(&l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__3);
v___x_490_ = lean_string_append(v___x_489_, v___x_488_);
return v___x_490_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__13(void){
_start:
{
lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_491_ = ((lean_object*)(l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__11));
v___x_492_ = lean_obj_once(&l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__12, &l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__12);
v___x_493_ = lean_string_append(v___x_492_, v___x_491_);
return v___x_493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson(lean_object* v_json_494_){
_start:
{
lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_495_ = ((lean_object*)(l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__0));
lean_inc(v_json_494_);
v___x_496_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageParams_fromJson_spec__0(v_json_494_, v___x_495_);
if (lean_obj_tag(v___x_496_) == 0)
{
lean_object* v_a_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_506_; 
lean_dec(v_json_494_);
v_a_497_ = lean_ctor_get(v___x_496_, 0);
v_isSharedCheck_506_ = !lean_is_exclusive(v___x_496_);
if (v_isSharedCheck_506_ == 0)
{
v___x_499_ = v___x_496_;
v_isShared_500_ = v_isSharedCheck_506_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_a_497_);
lean_dec(v___x_496_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_506_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_504_; 
v___x_501_ = lean_obj_once(&l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__5, &l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__5);
v___x_502_ = lean_string_append(v___x_501_, v_a_497_);
lean_dec(v_a_497_);
if (v_isShared_500_ == 0)
{
lean_ctor_set(v___x_499_, 0, v___x_502_);
v___x_504_ = v___x_499_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v___x_502_);
v___x_504_ = v_reuseFailAlloc_505_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
return v___x_504_;
}
}
}
else
{
if (lean_obj_tag(v___x_496_) == 0)
{
lean_object* v_a_507_; lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_514_; 
lean_dec(v_json_494_);
v_a_507_ = lean_ctor_get(v___x_496_, 0);
v_isSharedCheck_514_ = !lean_is_exclusive(v___x_496_);
if (v_isSharedCheck_514_ == 0)
{
v___x_509_ = v___x_496_;
v_isShared_510_ = v_isSharedCheck_514_;
goto v_resetjp_508_;
}
else
{
lean_inc(v_a_507_);
lean_dec(v___x_496_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_514_;
goto v_resetjp_508_;
}
v_resetjp_508_:
{
lean_object* v___x_512_; 
if (v_isShared_510_ == 0)
{
lean_ctor_set_tag(v___x_509_, 0);
v___x_512_ = v___x_509_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v_a_507_);
v___x_512_ = v_reuseFailAlloc_513_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
return v___x_512_;
}
}
}
else
{
lean_object* v_a_515_; lean_object* v___x_516_; lean_object* v___x_517_; 
v_a_515_ = lean_ctor_get(v___x_496_, 0);
lean_inc(v_a_515_);
lean_dec_ref_known(v___x_496_, 1);
v___x_516_ = ((lean_object*)(l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__13));
lean_inc(v_json_494_);
v___x_517_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageParams_fromJson_spec__1(v_json_494_, v___x_516_);
if (lean_obj_tag(v___x_517_) == 0)
{
lean_object* v_a_518_; lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_527_; 
lean_dec(v_a_515_);
lean_dec(v_json_494_);
v_a_518_ = lean_ctor_get(v___x_517_, 0);
v_isSharedCheck_527_ = !lean_is_exclusive(v___x_517_);
if (v_isSharedCheck_527_ == 0)
{
v___x_520_ = v___x_517_;
v_isShared_521_ = v_isSharedCheck_527_;
goto v_resetjp_519_;
}
else
{
lean_inc(v_a_518_);
lean_dec(v___x_517_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_527_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_525_; 
v___x_522_ = lean_obj_once(&l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__7);
v___x_523_ = lean_string_append(v___x_522_, v_a_518_);
lean_dec(v_a_518_);
if (v_isShared_521_ == 0)
{
lean_ctor_set(v___x_520_, 0, v___x_523_);
v___x_525_ = v___x_520_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v___x_523_);
v___x_525_ = v_reuseFailAlloc_526_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
return v___x_525_;
}
}
}
else
{
if (lean_obj_tag(v___x_517_) == 0)
{
lean_object* v_a_528_; lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_535_; 
lean_dec(v_a_515_);
lean_dec(v_json_494_);
v_a_528_ = lean_ctor_get(v___x_517_, 0);
v_isSharedCheck_535_ = !lean_is_exclusive(v___x_517_);
if (v_isSharedCheck_535_ == 0)
{
v___x_530_ = v___x_517_;
v_isShared_531_ = v_isSharedCheck_535_;
goto v_resetjp_529_;
}
else
{
lean_inc(v_a_528_);
lean_dec(v___x_517_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_535_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
lean_object* v___x_533_; 
if (v_isShared_531_ == 0)
{
lean_ctor_set_tag(v___x_530_, 0);
v___x_533_ = v___x_530_;
goto v_reusejp_532_;
}
else
{
lean_object* v_reuseFailAlloc_534_; 
v_reuseFailAlloc_534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_534_, 0, v_a_528_);
v___x_533_ = v_reuseFailAlloc_534_;
goto v_reusejp_532_;
}
v_reusejp_532_:
{
return v___x_533_;
}
}
}
else
{
lean_object* v_a_536_; lean_object* v___x_537_; lean_object* v___x_538_; 
v_a_536_ = lean_ctor_get(v___x_517_, 0);
lean_inc(v_a_536_);
lean_dec_ref_known(v___x_517_, 1);
v___x_537_ = ((lean_object*)(l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__8));
v___x_538_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson_spec__0(v_json_494_, v___x_537_);
if (lean_obj_tag(v___x_538_) == 0)
{
lean_object* v_a_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_548_; 
lean_dec(v_a_536_);
lean_dec(v_a_515_);
v_a_539_ = lean_ctor_get(v___x_538_, 0);
v_isSharedCheck_548_ = !lean_is_exclusive(v___x_538_);
if (v_isSharedCheck_548_ == 0)
{
v___x_541_ = v___x_538_;
v_isShared_542_ = v_isSharedCheck_548_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_a_539_);
lean_dec(v___x_538_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_548_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_546_; 
v___x_543_ = lean_obj_once(&l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__13, &l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__13);
v___x_544_ = lean_string_append(v___x_543_, v_a_539_);
lean_dec(v_a_539_);
if (v_isShared_542_ == 0)
{
lean_ctor_set(v___x_541_, 0, v___x_544_);
v___x_546_ = v___x_541_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v___x_544_);
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
if (lean_obj_tag(v___x_538_) == 0)
{
lean_object* v_a_549_; lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_556_; 
lean_dec(v_a_536_);
lean_dec(v_a_515_);
v_a_549_ = lean_ctor_get(v___x_538_, 0);
v_isSharedCheck_556_ = !lean_is_exclusive(v___x_538_);
if (v_isSharedCheck_556_ == 0)
{
v___x_551_ = v___x_538_;
v_isShared_552_ = v_isSharedCheck_556_;
goto v_resetjp_550_;
}
else
{
lean_inc(v_a_549_);
lean_dec(v___x_538_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_556_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
lean_object* v___x_554_; 
if (v_isShared_552_ == 0)
{
lean_ctor_set_tag(v___x_551_, 0);
v___x_554_ = v___x_551_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v_a_549_);
v___x_554_ = v_reuseFailAlloc_555_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
return v___x_554_;
}
}
}
else
{
lean_object* v_a_557_; lean_object* v___x_559_; uint8_t v_isShared_560_; uint8_t v_isSharedCheck_566_; 
v_a_557_ = lean_ctor_get(v___x_538_, 0);
v_isSharedCheck_566_ = !lean_is_exclusive(v___x_538_);
if (v_isSharedCheck_566_ == 0)
{
v___x_559_ = v___x_538_;
v_isShared_560_ = v_isSharedCheck_566_;
goto v_resetjp_558_;
}
else
{
lean_inc(v_a_557_);
lean_dec(v___x_538_);
v___x_559_ = lean_box(0);
v_isShared_560_ = v_isSharedCheck_566_;
goto v_resetjp_558_;
}
v_resetjp_558_:
{
lean_object* v___x_561_; uint8_t v___x_562_; lean_object* v___x_564_; 
v___x_561_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_561_, 0, v_a_536_);
lean_ctor_set(v___x_561_, 1, v_a_557_);
v___x_562_ = lean_unbox(v_a_515_);
lean_dec(v_a_515_);
lean_ctor_set_uint8(v___x_561_, sizeof(void*)*2, v___x_562_);
if (v_isShared_560_ == 0)
{
lean_ctor_set(v___x_559_, 0, v___x_561_);
v___x_564_ = v___x_559_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v___x_561_);
v___x_564_ = v_reuseFailAlloc_565_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
return v___x_564_;
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
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonShowMessageRequestParams_toJson_spec__0_spec__0_spec__1(size_t v_sz_569_, size_t v_i_570_, lean_object* v_bs_571_){
_start:
{
uint8_t v___x_572_; 
v___x_572_ = lean_usize_dec_lt(v_i_570_, v_sz_569_);
if (v___x_572_ == 0)
{
return v_bs_571_;
}
else
{
lean_object* v_v_573_; lean_object* v___x_574_; lean_object* v_bs_x27_575_; lean_object* v___x_576_; size_t v___x_577_; size_t v___x_578_; lean_object* v___x_579_; 
v_v_573_ = lean_array_uget(v_bs_571_, v_i_570_);
v___x_574_ = lean_unsigned_to_nat(0u);
v_bs_x27_575_ = lean_array_uset(v_bs_571_, v_i_570_, v___x_574_);
v___x_576_ = l_Lean_Lsp_instToJsonMessageActionItem_toJson(v_v_573_);
v___x_577_ = ((size_t)1ULL);
v___x_578_ = lean_usize_add(v_i_570_, v___x_577_);
v___x_579_ = lean_array_uset(v_bs_x27_575_, v_i_570_, v___x_576_);
v_i_570_ = v___x_578_;
v_bs_571_ = v___x_579_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonShowMessageRequestParams_toJson_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
size_t v_sz_569_ = stack[0].m_num;
size_t v_i_570_ = stack[1].m_num;
lean_object* v_bs_571_ = stack[2].m_obj;
lean_object* v_res_581_;
v_res_581_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonShowMessageRequestParams_toJson_spec__0_spec__0_spec__1(v_sz_569_, v_i_570_, v_bs_571_);
stack->m_obj
 = v_res_581_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonShowMessageRequestParams_toJson_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_582_, lean_object* v_i_583_, lean_object* v_bs_584_){
_start:
{
size_t v_sz_boxed_585_; size_t v_i_boxed_586_; lean_object* v_res_587_; 
v_sz_boxed_585_ = lean_unbox_usize(v_sz_582_);
lean_dec(v_sz_582_);
v_i_boxed_586_ = lean_unbox_usize(v_i_583_);
lean_dec(v_i_583_);
v_res_587_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonShowMessageRequestParams_toJson_spec__0_spec__0_spec__1(v_sz_boxed_585_, v_i_boxed_586_, v_bs_584_);
return v_res_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonShowMessageRequestParams_toJson_spec__0_spec__0(lean_object* v_a_588_){
_start:
{
size_t v_sz_589_; size_t v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; 
v_sz_589_ = lean_array_size(v_a_588_);
v___x_590_ = ((size_t)0ULL);
v___x_591_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonShowMessageRequestParams_toJson_spec__0_spec__0_spec__1(v_sz_589_, v___x_590_, v_a_588_);
v___x_592_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_592_, 0, v___x_591_);
return v___x_592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonShowMessageRequestParams_toJson_spec__0(lean_object* v_k_593_, lean_object* v_x_594_){
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
lean_object* v_val_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; 
v_val_596_ = lean_ctor_get(v_x_594_, 0);
lean_inc(v_val_596_);
lean_dec_ref_known(v_x_594_, 1);
v___x_597_ = l_Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonShowMessageRequestParams_toJson_spec__0_spec__0(v_val_596_);
v___x_598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_598_, 0, v_k_593_);
lean_ctor_set(v___x_598_, 1, v___x_597_);
v___x_599_ = lean_box(0);
v___x_600_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_600_, 0, v___x_598_);
lean_ctor_set(v___x_600_, 1, v___x_599_);
return v___x_600_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonShowMessageRequestParams_toJson(lean_object* v_x_601_){
_start:
{
uint8_t v_type_602_; lean_object* v_message_603_; lean_object* v_actions_x3f_604_; lean_object* v___x_605_; lean_object* v___y_607_; 
v_type_602_ = lean_ctor_get_uint8(v_x_601_, sizeof(void*)*2);
v_message_603_ = lean_ctor_get(v_x_601_, 0);
lean_inc_ref(v_message_603_);
v_actions_x3f_604_ = lean_ctor_get(v_x_601_, 1);
lean_inc(v_actions_x3f_604_);
lean_dec_ref(v_x_601_);
v___x_605_ = ((lean_object*)(l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__0));
switch(v_type_602_)
{
case 0:
{
lean_object* v___x_623_; 
v___x_623_ = lean_obj_once(&l_Lean_Lsp_instToJsonMessageType___lam__0___closed__1, &l_Lean_Lsp_instToJsonMessageType___lam__0___closed__1_once, _init_l_Lean_Lsp_instToJsonMessageType___lam__0___closed__1);
v___y_607_ = v___x_623_;
goto v___jp_606_;
}
case 1:
{
lean_object* v___x_624_; 
v___x_624_ = lean_obj_once(&l_Lean_Lsp_instToJsonMessageType___lam__0___closed__3, &l_Lean_Lsp_instToJsonMessageType___lam__0___closed__3_once, _init_l_Lean_Lsp_instToJsonMessageType___lam__0___closed__3);
v___y_607_ = v___x_624_;
goto v___jp_606_;
}
case 2:
{
lean_object* v___x_625_; 
v___x_625_ = lean_obj_once(&l_Lean_Lsp_instToJsonMessageType___lam__0___closed__5, &l_Lean_Lsp_instToJsonMessageType___lam__0___closed__5_once, _init_l_Lean_Lsp_instToJsonMessageType___lam__0___closed__5);
v___y_607_ = v___x_625_;
goto v___jp_606_;
}
default: 
{
lean_object* v___x_626_; 
v___x_626_ = lean_obj_once(&l_Lean_Lsp_instToJsonMessageType___lam__0___closed__7, &l_Lean_Lsp_instToJsonMessageType___lam__0___closed__7_once, _init_l_Lean_Lsp_instToJsonMessageType___lam__0___closed__7);
v___y_607_ = v___x_626_;
goto v___jp_606_;
}
}
v___jp_606_:
{
lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; 
lean_inc(v___y_607_);
v___x_608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_608_, 0, v___x_605_);
lean_ctor_set(v___x_608_, 1, v___y_607_);
v___x_609_ = lean_box(0);
v___x_610_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_610_, 0, v___x_608_);
lean_ctor_set(v___x_610_, 1, v___x_609_);
v___x_611_ = ((lean_object*)(l_Lean_Lsp_instFromJsonShowMessageParams_fromJson___closed__13));
v___x_612_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_612_, 0, v_message_603_);
v___x_613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_613_, 0, v___x_611_);
lean_ctor_set(v___x_613_, 1, v___x_612_);
v___x_614_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_614_, 0, v___x_613_);
lean_ctor_set(v___x_614_, 1, v___x_609_);
v___x_615_ = ((lean_object*)(l_Lean_Lsp_instFromJsonShowMessageRequestParams_fromJson___closed__8));
v___x_616_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonShowMessageRequestParams_toJson_spec__0(v___x_615_, v_actions_x3f_604_);
v___x_617_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_617_, 0, v___x_616_);
lean_ctor_set(v___x_617_, 1, v___x_609_);
v___x_618_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_618_, 0, v___x_614_);
lean_ctor_set(v___x_618_, 1, v___x_617_);
v___x_619_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_619_, 0, v___x_610_);
lean_ctor_set(v___x_619_, 1, v___x_618_);
v___x_620_ = ((lean_object*)(l_Lean_Lsp_instToJsonShowMessageParams_toJson___closed__0));
v___x_621_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonShowMessageParams_toJson_spec__0(v___x_619_, v___x_620_);
v___x_622_ = l_Lean_Json_mkObj(v___x_621_);
lean_dec(v___x_621_);
return v___x_622_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonShowMessageResponse___aux__1(lean_object* v_a_629_){
_start:
{
lean_object* v___x_630_; lean_object* v___x_631_; 
v___x_630_ = ((lean_object*)(l_Lean_Lsp_instFromJsonMessageActionItem___closed__0));
v___x_631_ = l_Lean_Option_fromJson_x3f___redArg(v___x_630_, v_a_629_);
return v___x_631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Lsp_instFromJsonShowMessageResponse_spec__0(lean_object* v_x_634_){
_start:
{
if (lean_obj_tag(v_x_634_) == 0)
{
lean_object* v___x_635_; 
v___x_635_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Lsp_instFromJsonShowMessageResponse_spec__0___closed__0));
return v___x_635_;
}
else
{
lean_object* v___x_636_; 
v___x_636_ = l_Lean_Lsp_instFromJsonMessageActionItem_fromJson(v_x_634_);
if (lean_obj_tag(v___x_636_) == 0)
{
lean_object* v_a_637_; lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_644_; 
v_a_637_ = lean_ctor_get(v___x_636_, 0);
v_isSharedCheck_644_ = !lean_is_exclusive(v___x_636_);
if (v_isSharedCheck_644_ == 0)
{
v___x_639_ = v___x_636_;
v_isShared_640_ = v_isSharedCheck_644_;
goto v_resetjp_638_;
}
else
{
lean_inc(v_a_637_);
lean_dec(v___x_636_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_644_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
lean_object* v___x_642_; 
if (v_isShared_640_ == 0)
{
v___x_642_ = v___x_639_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v_a_637_);
v___x_642_ = v_reuseFailAlloc_643_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
return v___x_642_;
}
}
}
else
{
lean_object* v_a_645_; lean_object* v___x_647_; uint8_t v_isShared_648_; uint8_t v_isSharedCheck_653_; 
v_a_645_ = lean_ctor_get(v___x_636_, 0);
v_isSharedCheck_653_ = !lean_is_exclusive(v___x_636_);
if (v_isSharedCheck_653_ == 0)
{
v___x_647_ = v___x_636_;
v_isShared_648_ = v_isSharedCheck_653_;
goto v_resetjp_646_;
}
else
{
lean_inc(v_a_645_);
lean_dec(v___x_636_);
v___x_647_ = lean_box(0);
v_isShared_648_ = v_isSharedCheck_653_;
goto v_resetjp_646_;
}
v_resetjp_646_:
{
lean_object* v___x_649_; lean_object* v___x_651_; 
v___x_649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_649_, 0, v_a_645_);
if (v_isShared_648_ == 0)
{
lean_ctor_set(v___x_647_, 0, v___x_649_);
v___x_651_ = v___x_647_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v___x_649_);
v___x_651_ = v_reuseFailAlloc_652_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
return v___x_651_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonShowMessageResponse___aux__1(lean_object* v_a_656_){
_start:
{
lean_object* v___x_657_; lean_object* v___x_658_; 
v___x_657_ = ((lean_object*)(l_Lean_Lsp_instToJsonMessageActionItem___closed__0));
v___x_658_ = l_Lean_Option_toJson___redArg(v___x_657_, v_a_656_);
return v___x_658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_toJson___at___00Lean_Lsp_instToJsonShowMessageResponse_spec__0(lean_object* v_x_659_){
_start:
{
if (lean_obj_tag(v_x_659_) == 0)
{
lean_object* v___x_660_; 
v___x_660_ = lean_box(0);
return v___x_660_;
}
else
{
lean_object* v_val_661_; lean_object* v___x_662_; 
v_val_661_ = lean_ctor_get(v_x_659_, 0);
lean_inc(v_val_661_);
lean_dec_ref_known(v_x_659_, 1);
v___x_662_ = l_Lean_Lsp_instToJsonMessageActionItem_toJson(v_val_661_);
return v___x_662_;
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

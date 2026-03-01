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
LEAN_EXPORT lean_object* l_MessageType_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_MessageType_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_MessageType_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_MessageType_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_MessageType_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MessageType_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_MessageType_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MessageType_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MessageType_error_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MessageType_error_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_MessageType_error_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MessageType_error_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MessageType_warning_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MessageType_warning_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_MessageType_warning_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MessageType_warning_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MessageType_info_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MessageType_info_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_MessageType_info_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MessageType_info_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MessageType_log_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MessageType_log_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_MessageType_log_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MessageType_log_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_instFromJsonMessageType___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Unknown MessageType ID"};
static const lean_object* l_instFromJsonMessageType___lam__0___closed__0 = (const lean_object*)&l_instFromJsonMessageType___lam__0___closed__0_value;
static const lean_ctor_object l_instFromJsonMessageType___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_instFromJsonMessageType___lam__0___closed__0_value)}};
static const lean_object* l_instFromJsonMessageType___lam__0___closed__1 = (const lean_object*)&l_instFromJsonMessageType___lam__0___closed__1_value;
lean_object* lean_nat_to_int(lean_object*);
static lean_once_cell_t l_instFromJsonMessageType___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_instFromJsonMessageType___lam__0___closed__2;
static const lean_ctor_object l_instFromJsonMessageType___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l_instFromJsonMessageType___lam__0___closed__3 = (const lean_object*)&l_instFromJsonMessageType___lam__0___closed__3_value;
static const lean_ctor_object l_instFromJsonMessageType___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l_instFromJsonMessageType___lam__0___closed__4 = (const lean_object*)&l_instFromJsonMessageType___lam__0___closed__4_value;
static const lean_ctor_object l_instFromJsonMessageType___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_instFromJsonMessageType___lam__0___closed__5 = (const lean_object*)&l_instFromJsonMessageType___lam__0___closed__5_value;
static const lean_ctor_object l_instFromJsonMessageType___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_instFromJsonMessageType___lam__0___closed__6 = (const lean_object*)&l_instFromJsonMessageType___lam__0___closed__6_value;
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instFromJsonMessageType___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_instFromJsonMessageType___lam__0___boxed(lean_object*);
static const lean_closure_object l_instFromJsonMessageType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instFromJsonMessageType___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instFromJsonMessageType___closed__0 = (const lean_object*)&l_instFromJsonMessageType___closed__0_value;
LEAN_EXPORT const lean_object* l_instFromJsonMessageType = (const lean_object*)&l_instFromJsonMessageType___closed__0_value;
lean_object* l_Lean_JsonNumber_fromNat(lean_object*);
static lean_once_cell_t l_instToJsonMessageType___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_instToJsonMessageType___lam__0___closed__0;
static lean_once_cell_t l_instToJsonMessageType___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_instToJsonMessageType___lam__0___closed__1;
static lean_once_cell_t l_instToJsonMessageType___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_instToJsonMessageType___lam__0___closed__2;
static lean_once_cell_t l_instToJsonMessageType___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_instToJsonMessageType___lam__0___closed__3;
static lean_once_cell_t l_instToJsonMessageType___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_instToJsonMessageType___lam__0___closed__4;
static lean_once_cell_t l_instToJsonMessageType___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_instToJsonMessageType___lam__0___closed__5;
static lean_once_cell_t l_instToJsonMessageType___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_instToJsonMessageType___lam__0___closed__6;
static lean_once_cell_t l_instToJsonMessageType___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_instToJsonMessageType___lam__0___closed__7;
LEAN_EXPORT lean_object* l_instToJsonMessageType___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_instToJsonMessageType___lam__0___boxed(lean_object*);
static const lean_closure_object l_instToJsonMessageType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instToJsonMessageType___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instToJsonMessageType___closed__0 = (const lean_object*)&l_instToJsonMessageType___closed__0_value;
LEAN_EXPORT const lean_object* l_instToJsonMessageType = (const lean_object*)&l_instToJsonMessageType___closed__0_value;
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageParams_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageParams_fromJson_spec__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageParams_fromJson_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageParams_fromJson_spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l_instFromJsonShowMessageParams_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "type"};
static const lean_object* l_instFromJsonShowMessageParams_fromJson___closed__0 = (const lean_object*)&l_instFromJsonShowMessageParams_fromJson___closed__0_value;
static const lean_string_object l_instFromJsonShowMessageParams_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "ShowMessageParams"};
static const lean_object* l_instFromJsonShowMessageParams_fromJson___closed__1 = (const lean_object*)&l_instFromJsonShowMessageParams_fromJson___closed__1_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_instFromJsonShowMessageParams_fromJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_instFromJsonShowMessageParams_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(28, 246, 128, 63, 249, 10, 125, 27)}};
static const lean_object* l_instFromJsonShowMessageParams_fromJson___closed__2 = (const lean_object*)&l_instFromJsonShowMessageParams_fromJson___closed__2_value;
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
static lean_once_cell_t l_instFromJsonShowMessageParams_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_instFromJsonShowMessageParams_fromJson___closed__3;
static const lean_string_object l_instFromJsonShowMessageParams_fromJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_instFromJsonShowMessageParams_fromJson___closed__4 = (const lean_object*)&l_instFromJsonShowMessageParams_fromJson___closed__4_value;
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_once_cell_t l_instFromJsonShowMessageParams_fromJson___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_instFromJsonShowMessageParams_fromJson___closed__5;
static const lean_ctor_object l_instFromJsonShowMessageParams_fromJson___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_instFromJsonShowMessageParams_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(112, 109, 54, 158, 248, 169, 165, 159)}};
static const lean_object* l_instFromJsonShowMessageParams_fromJson___closed__6 = (const lean_object*)&l_instFromJsonShowMessageParams_fromJson___closed__6_value;
static lean_once_cell_t l_instFromJsonShowMessageParams_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_instFromJsonShowMessageParams_fromJson___closed__7;
static lean_once_cell_t l_instFromJsonShowMessageParams_fromJson___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_instFromJsonShowMessageParams_fromJson___closed__8;
static const lean_string_object l_instFromJsonShowMessageParams_fromJson___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l_instFromJsonShowMessageParams_fromJson___closed__9 = (const lean_object*)&l_instFromJsonShowMessageParams_fromJson___closed__9_value;
static lean_once_cell_t l_instFromJsonShowMessageParams_fromJson___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_instFromJsonShowMessageParams_fromJson___closed__10;
static const lean_string_object l_instFromJsonShowMessageParams_fromJson___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "message"};
static const lean_object* l_instFromJsonShowMessageParams_fromJson___closed__11 = (const lean_object*)&l_instFromJsonShowMessageParams_fromJson___closed__11_value;
static const lean_ctor_object l_instFromJsonShowMessageParams_fromJson___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_instFromJsonShowMessageParams_fromJson___closed__11_value),LEAN_SCALAR_PTR_LITERAL(149, 62, 76, 216, 222, 7, 163, 13)}};
static const lean_object* l_instFromJsonShowMessageParams_fromJson___closed__12 = (const lean_object*)&l_instFromJsonShowMessageParams_fromJson___closed__12_value;
static lean_once_cell_t l_instFromJsonShowMessageParams_fromJson___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_instFromJsonShowMessageParams_fromJson___closed__13;
static lean_once_cell_t l_instFromJsonShowMessageParams_fromJson___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_instFromJsonShowMessageParams_fromJson___closed__14;
static lean_once_cell_t l_instFromJsonShowMessageParams_fromJson___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_instFromJsonShowMessageParams_fromJson___closed__15;
LEAN_EXPORT lean_object* l_instFromJsonShowMessageParams_fromJson(lean_object*);
static const lean_closure_object l_instFromJsonShowMessageParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instFromJsonShowMessageParams_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instFromJsonShowMessageParams___closed__0 = (const lean_object*)&l_instFromJsonShowMessageParams___closed__0_value;
LEAN_EXPORT const lean_object* l_instFromJsonShowMessageParams = (const lean_object*)&l_instFromJsonShowMessageParams___closed__0_value;
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00instToJsonShowMessageParams_toJson_spec__0(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static const lean_array_object l_instToJsonShowMessageParams_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_instToJsonShowMessageParams_toJson___closed__0 = (const lean_object*)&l_instToJsonShowMessageParams_toJson___closed__0_value;
lean_object* l_Lean_Json_mkObj(lean_object*);
LEAN_EXPORT lean_object* l_instToJsonShowMessageParams_toJson(lean_object*);
LEAN_EXPORT lean_object* l_instToJsonShowMessageParams_toJson___boxed(lean_object*);
static const lean_closure_object l_instToJsonShowMessageParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instToJsonShowMessageParams_toJson___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instToJsonShowMessageParams___closed__0 = (const lean_object*)&l_instToJsonShowMessageParams___closed__0_value;
LEAN_EXPORT const lean_object* l_instToJsonShowMessageParams = (const lean_object*)&l_instToJsonShowMessageParams___closed__0_value;
static const lean_string_object l_instFromJsonMessageActionItem_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "title"};
static const lean_object* l_instFromJsonMessageActionItem_fromJson___closed__0 = (const lean_object*)&l_instFromJsonMessageActionItem_fromJson___closed__0_value;
static const lean_string_object l_instFromJsonMessageActionItem_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "MessageActionItem"};
static const lean_object* l_instFromJsonMessageActionItem_fromJson___closed__1 = (const lean_object*)&l_instFromJsonMessageActionItem_fromJson___closed__1_value;
static const lean_ctor_object l_instFromJsonMessageActionItem_fromJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_instFromJsonMessageActionItem_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(129, 210, 242, 19, 9, 167, 252, 53)}};
static const lean_object* l_instFromJsonMessageActionItem_fromJson___closed__2 = (const lean_object*)&l_instFromJsonMessageActionItem_fromJson___closed__2_value;
static lean_once_cell_t l_instFromJsonMessageActionItem_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_instFromJsonMessageActionItem_fromJson___closed__3;
static lean_once_cell_t l_instFromJsonMessageActionItem_fromJson___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_instFromJsonMessageActionItem_fromJson___closed__4;
static const lean_ctor_object l_instFromJsonMessageActionItem_fromJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_instFromJsonMessageActionItem_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(251, 99, 171, 63, 21, 188, 124, 202)}};
static const lean_object* l_instFromJsonMessageActionItem_fromJson___closed__5 = (const lean_object*)&l_instFromJsonMessageActionItem_fromJson___closed__5_value;
static lean_once_cell_t l_instFromJsonMessageActionItem_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_instFromJsonMessageActionItem_fromJson___closed__6;
static lean_once_cell_t l_instFromJsonMessageActionItem_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_instFromJsonMessageActionItem_fromJson___closed__7;
static lean_once_cell_t l_instFromJsonMessageActionItem_fromJson___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_instFromJsonMessageActionItem_fromJson___closed__8;
LEAN_EXPORT lean_object* l_instFromJsonMessageActionItem_fromJson(lean_object*);
static const lean_closure_object l_instFromJsonMessageActionItem___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instFromJsonMessageActionItem_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instFromJsonMessageActionItem___closed__0 = (const lean_object*)&l_instFromJsonMessageActionItem___closed__0_value;
LEAN_EXPORT const lean_object* l_instFromJsonMessageActionItem = (const lean_object*)&l_instFromJsonMessageActionItem___closed__0_value;
LEAN_EXPORT lean_object* l_instToJsonMessageActionItem_toJson(lean_object*);
static const lean_closure_object l_instToJsonMessageActionItem___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instToJsonMessageActionItem_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instToJsonMessageActionItem___closed__0 = (const lean_object*)&l_instToJsonMessageActionItem___closed__0_value;
LEAN_EXPORT const lean_object* l_instToJsonMessageActionItem = (const lean_object*)&l_instToJsonMessageActionItem___closed__0_value;
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0_spec__1_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "expected JSON array, got '"};
static const lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0_spec__1___closed__0 = (const lean_object*)&l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0_spec__1___closed__0_value;
static const lean_string_object l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0_spec__1___closed__1 = (const lean_object*)&l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0_spec__1___closed__1_value;
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0_spec__1(lean_object*);
static const lean_ctor_object l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageRequestParams_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageRequestParams_fromJson_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_instFromJsonShowMessageRequestParams_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "ShowMessageRequestParams"};
static const lean_object* l_instFromJsonShowMessageRequestParams_fromJson___closed__0 = (const lean_object*)&l_instFromJsonShowMessageRequestParams_fromJson___closed__0_value;
static const lean_ctor_object l_instFromJsonShowMessageRequestParams_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_instFromJsonShowMessageRequestParams_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(122, 156, 137, 100, 100, 44, 217, 216)}};
static const lean_object* l_instFromJsonShowMessageRequestParams_fromJson___closed__1 = (const lean_object*)&l_instFromJsonShowMessageRequestParams_fromJson___closed__1_value;
static lean_once_cell_t l_instFromJsonShowMessageRequestParams_fromJson___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_instFromJsonShowMessageRequestParams_fromJson___closed__2;
static lean_once_cell_t l_instFromJsonShowMessageRequestParams_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_instFromJsonShowMessageRequestParams_fromJson___closed__3;
static lean_once_cell_t l_instFromJsonShowMessageRequestParams_fromJson___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_instFromJsonShowMessageRequestParams_fromJson___closed__4;
static lean_once_cell_t l_instFromJsonShowMessageRequestParams_fromJson___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_instFromJsonShowMessageRequestParams_fromJson___closed__5;
static lean_once_cell_t l_instFromJsonShowMessageRequestParams_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_instFromJsonShowMessageRequestParams_fromJson___closed__6;
static lean_once_cell_t l_instFromJsonShowMessageRequestParams_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_instFromJsonShowMessageRequestParams_fromJson___closed__7;
static const lean_string_object l_instFromJsonShowMessageRequestParams_fromJson___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "actions"};
static const lean_object* l_instFromJsonShowMessageRequestParams_fromJson___closed__8 = (const lean_object*)&l_instFromJsonShowMessageRequestParams_fromJson___closed__8_value;
static const lean_string_object l_instFromJsonShowMessageRequestParams_fromJson___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "actions\?"};
static const lean_object* l_instFromJsonShowMessageRequestParams_fromJson___closed__9 = (const lean_object*)&l_instFromJsonShowMessageRequestParams_fromJson___closed__9_value;
static const lean_ctor_object l_instFromJsonShowMessageRequestParams_fromJson___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_instFromJsonShowMessageRequestParams_fromJson___closed__9_value),LEAN_SCALAR_PTR_LITERAL(223, 135, 214, 230, 197, 178, 71, 91)}};
static const lean_object* l_instFromJsonShowMessageRequestParams_fromJson___closed__10 = (const lean_object*)&l_instFromJsonShowMessageRequestParams_fromJson___closed__10_value;
static lean_once_cell_t l_instFromJsonShowMessageRequestParams_fromJson___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_instFromJsonShowMessageRequestParams_fromJson___closed__11;
static lean_once_cell_t l_instFromJsonShowMessageRequestParams_fromJson___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_instFromJsonShowMessageRequestParams_fromJson___closed__12;
static lean_once_cell_t l_instFromJsonShowMessageRequestParams_fromJson___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_instFromJsonShowMessageRequestParams_fromJson___closed__13;
LEAN_EXPORT lean_object* l_instFromJsonShowMessageRequestParams_fromJson(lean_object*);
static const lean_closure_object l_instFromJsonShowMessageRequestParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instFromJsonShowMessageRequestParams_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instFromJsonShowMessageRequestParams___closed__0 = (const lean_object*)&l_instFromJsonShowMessageRequestParams___closed__0_value;
LEAN_EXPORT const lean_object* l_instFromJsonShowMessageRequestParams = (const lean_object*)&l_instFromJsonShowMessageRequestParams___closed__0_value;
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00instToJsonShowMessageRequestParams_toJson_spec__0_spec__0_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00instToJsonShowMessageRequestParams_toJson_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Json_opt___at___00instToJsonShowMessageRequestParams_toJson_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00instToJsonShowMessageRequestParams_toJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToJsonShowMessageRequestParams_toJson(lean_object*);
static const lean_closure_object l_instToJsonShowMessageRequestParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instToJsonShowMessageRequestParams_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instToJsonShowMessageRequestParams___closed__0 = (const lean_object*)&l_instToJsonShowMessageRequestParams___closed__0_value;
LEAN_EXPORT const lean_object* l_instToJsonShowMessageRequestParams = (const lean_object*)&l_instToJsonShowMessageRequestParams___closed__0_value;
lean_object* l_Option_fromJson_x3f(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_instFromJsonShowMessageResponse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Option_fromJson_x3f, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_instFromJsonMessageActionItem___closed__0_value)} };
static const lean_object* l_instFromJsonShowMessageResponse___closed__0 = (const lean_object*)&l_instFromJsonShowMessageResponse___closed__0_value;
LEAN_EXPORT const lean_object* l_instFromJsonShowMessageResponse = (const lean_object*)&l_instFromJsonShowMessageResponse___closed__0_value;
lean_object* l_Option_toJson(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_instToJsonShowMessageResponse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Option_toJson, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_instToJsonMessageActionItem___closed__0_value)} };
static const lean_object* l_instToJsonShowMessageResponse___closed__0 = (const lean_object*)&l_instToJsonShowMessageResponse___closed__0_value;
LEAN_EXPORT const lean_object* l_instToJsonShowMessageResponse = (const lean_object*)&l_instToJsonShowMessageResponse___closed__0_value;
LEAN_EXPORT lean_object* l_MessageType_ctorIdx(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
case 2:
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
default: 
{
lean_object* x_5; 
x_5 = lean_unsigned_to_nat(3u);
return x_5;
}
}
}
}
LEAN_EXPORT lean_object* l_MessageType_ctorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_MessageType_ctorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_MessageType_toCtorIdx(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_MessageType_ctorIdx(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_MessageType_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_MessageType_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_MessageType_ctorElim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_MessageType_ctorElim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_MessageType_ctorElim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_MessageType_ctorElim(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_inc(x_5);
return x_5;
}
}
LEAN_EXPORT lean_object* l_MessageType_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
x_7 = l_MessageType_ctorElim(x_1, x_2, x_6, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_MessageType_error_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_MessageType_error_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_MessageType_error_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_MessageType_error_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_MessageType_error_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_MessageType_error_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_MessageType_warning_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_MessageType_warning_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_MessageType_warning_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_MessageType_warning_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_MessageType_warning_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_MessageType_warning_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_MessageType_info_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_MessageType_info_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_MessageType_info_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_MessageType_info_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_MessageType_info_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_MessageType_info_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_MessageType_log_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_MessageType_log_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_MessageType_log_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_MessageType_log_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_MessageType_log_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_MessageType_log_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
static lean_object* _init_l_instFromJsonMessageType___lam__0___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instFromJsonMessageType___lam__0(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 2)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_ctor_get(x_4, 1);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_obj_once(&l_instFromJsonMessageType___lam__0___closed__2, &l_instFromJsonMessageType___lam__0___closed__2_once, _init_l_instFromJsonMessageType___lam__0___closed__2);
x_9 = lean_int_dec_lt(x_5, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_nat_abs(x_5);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_dec_eq(x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_unsigned_to_nat(2u);
x_14 = lean_nat_dec_eq(x_10, x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_unsigned_to_nat(3u);
x_16 = lean_nat_dec_eq(x_10, x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_unsigned_to_nat(4u);
x_18 = lean_nat_dec_eq(x_10, x_17);
lean_dec(x_10);
if (x_18 == 0)
{
goto block_3;
}
else
{
uint8_t x_19; 
x_19 = lean_nat_dec_eq(x_6, x_7);
if (x_19 == 0)
{
goto block_3;
}
else
{
lean_object* x_20; 
x_20 = ((lean_object*)(l_instFromJsonMessageType___lam__0___closed__3));
return x_20;
}
}
}
else
{
uint8_t x_21; 
lean_dec(x_10);
x_21 = lean_nat_dec_eq(x_6, x_7);
if (x_21 == 0)
{
goto block_3;
}
else
{
lean_object* x_22; 
x_22 = ((lean_object*)(l_instFromJsonMessageType___lam__0___closed__4));
return x_22;
}
}
}
else
{
uint8_t x_23; 
lean_dec(x_10);
x_23 = lean_nat_dec_eq(x_6, x_7);
if (x_23 == 0)
{
goto block_3;
}
else
{
lean_object* x_24; 
x_24 = ((lean_object*)(l_instFromJsonMessageType___lam__0___closed__5));
return x_24;
}
}
}
else
{
uint8_t x_25; 
lean_dec(x_10);
x_25 = lean_nat_dec_eq(x_6, x_7);
if (x_25 == 0)
{
goto block_3;
}
else
{
lean_object* x_26; 
x_26 = ((lean_object*)(l_instFromJsonMessageType___lam__0___closed__6));
return x_26;
}
}
}
else
{
goto block_3;
}
}
else
{
goto block_3;
}
block_3:
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_instFromJsonMessageType___lam__0___closed__1));
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_instFromJsonMessageType___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_instFromJsonMessageType___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_instToJsonMessageType___lam__0___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = l_Lean_JsonNumber_fromNat(x_1);
return x_2;
}
}
static lean_object* _init_l_instToJsonMessageType___lam__0___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_instToJsonMessageType___lam__0___closed__0, &l_instToJsonMessageType___lam__0___closed__0_once, _init_l_instToJsonMessageType___lam__0___closed__0);
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_instToJsonMessageType___lam__0___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = l_Lean_JsonNumber_fromNat(x_1);
return x_2;
}
}
static lean_object* _init_l_instToJsonMessageType___lam__0___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_instToJsonMessageType___lam__0___closed__2, &l_instToJsonMessageType___lam__0___closed__2_once, _init_l_instToJsonMessageType___lam__0___closed__2);
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_instToJsonMessageType___lam__0___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = l_Lean_JsonNumber_fromNat(x_1);
return x_2;
}
}
static lean_object* _init_l_instToJsonMessageType___lam__0___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_instToJsonMessageType___lam__0___closed__4, &l_instToJsonMessageType___lam__0___closed__4_once, _init_l_instToJsonMessageType___lam__0___closed__4);
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_instToJsonMessageType___lam__0___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = l_Lean_JsonNumber_fromNat(x_1);
return x_2;
}
}
static lean_object* _init_l_instToJsonMessageType___lam__0___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_instToJsonMessageType___lam__0___closed__6, &l_instToJsonMessageType___lam__0___closed__6_once, _init_l_instToJsonMessageType___lam__0___closed__6);
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instToJsonMessageType___lam__0(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = lean_obj_once(&l_instToJsonMessageType___lam__0___closed__1, &l_instToJsonMessageType___lam__0___closed__1_once, _init_l_instToJsonMessageType___lam__0___closed__1);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_obj_once(&l_instToJsonMessageType___lam__0___closed__3, &l_instToJsonMessageType___lam__0___closed__3_once, _init_l_instToJsonMessageType___lam__0___closed__3);
return x_3;
}
case 2:
{
lean_object* x_4; 
x_4 = lean_obj_once(&l_instToJsonMessageType___lam__0___closed__5, &l_instToJsonMessageType___lam__0___closed__5_once, _init_l_instToJsonMessageType___lam__0___closed__5);
return x_4;
}
default: 
{
lean_object* x_5; 
x_5 = lean_obj_once(&l_instToJsonMessageType___lam__0___closed__7, &l_instToJsonMessageType___lam__0___closed__7_once, _init_l_instToJsonMessageType___lam__0___closed__7);
return x_5;
}
}
}
}
LEAN_EXPORT lean_object* l_instToJsonMessageType___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_instToJsonMessageType___lam__0(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageParams_fromJson_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Json_getObjValD(x_1, x_2);
if (lean_obj_tag(x_5) == 2)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_6);
lean_dec_ref(x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_obj_once(&l_instFromJsonMessageType___lam__0___closed__2, &l_instFromJsonMessageType___lam__0___closed__2_once, _init_l_instFromJsonMessageType___lam__0___closed__2);
x_11 = lean_int_dec_lt(x_7, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_nat_abs(x_7);
lean_dec(x_7);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_dec_eq(x_12, x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_unsigned_to_nat(2u);
x_16 = lean_nat_dec_eq(x_12, x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_unsigned_to_nat(3u);
x_18 = lean_nat_dec_eq(x_12, x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_unsigned_to_nat(4u);
x_20 = lean_nat_dec_eq(x_12, x_19);
lean_dec(x_12);
if (x_20 == 0)
{
lean_dec(x_8);
goto block_4;
}
else
{
uint8_t x_21; 
x_21 = lean_nat_dec_eq(x_8, x_9);
lean_dec(x_8);
if (x_21 == 0)
{
goto block_4;
}
else
{
lean_object* x_22; 
x_22 = ((lean_object*)(l_instFromJsonMessageType___lam__0___closed__3));
return x_22;
}
}
}
else
{
uint8_t x_23; 
lean_dec(x_12);
x_23 = lean_nat_dec_eq(x_8, x_9);
lean_dec(x_8);
if (x_23 == 0)
{
goto block_4;
}
else
{
lean_object* x_24; 
x_24 = ((lean_object*)(l_instFromJsonMessageType___lam__0___closed__4));
return x_24;
}
}
}
else
{
uint8_t x_25; 
lean_dec(x_12);
x_25 = lean_nat_dec_eq(x_8, x_9);
lean_dec(x_8);
if (x_25 == 0)
{
goto block_4;
}
else
{
lean_object* x_26; 
x_26 = ((lean_object*)(l_instFromJsonMessageType___lam__0___closed__5));
return x_26;
}
}
}
else
{
uint8_t x_27; 
lean_dec(x_12);
x_27 = lean_nat_dec_eq(x_8, x_9);
lean_dec(x_8);
if (x_27 == 0)
{
goto block_4;
}
else
{
lean_object* x_28; 
x_28 = ((lean_object*)(l_instFromJsonMessageType___lam__0___closed__6));
return x_28;
}
}
}
else
{
lean_dec(x_8);
lean_dec(x_7);
goto block_4;
}
}
else
{
lean_dec(x_5);
goto block_4;
}
block_4:
{
lean_object* x_3; 
x_3 = ((lean_object*)(l_instFromJsonMessageType___lam__0___closed__1));
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageParams_fromJson_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageParams_fromJson_spec__0(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageParams_fromJson_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l_Lean_Json_getStr_x3f(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageParams_fromJson_spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageParams_fromJson_spec__1(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
static lean_object* _init_l_instFromJsonShowMessageParams_fromJson___closed__3(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_instFromJsonShowMessageParams_fromJson___closed__2));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_instFromJsonShowMessageParams_fromJson___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_instFromJsonShowMessageParams_fromJson___closed__4));
x_2 = lean_obj_once(&l_instFromJsonShowMessageParams_fromJson___closed__3, &l_instFromJsonShowMessageParams_fromJson___closed__3_once, _init_l_instFromJsonShowMessageParams_fromJson___closed__3);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_instFromJsonShowMessageParams_fromJson___closed__7(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_instFromJsonShowMessageParams_fromJson___closed__6));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_instFromJsonShowMessageParams_fromJson___closed__8(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_instFromJsonShowMessageParams_fromJson___closed__7, &l_instFromJsonShowMessageParams_fromJson___closed__7_once, _init_l_instFromJsonShowMessageParams_fromJson___closed__7);
x_2 = lean_obj_once(&l_instFromJsonShowMessageParams_fromJson___closed__5, &l_instFromJsonShowMessageParams_fromJson___closed__5_once, _init_l_instFromJsonShowMessageParams_fromJson___closed__5);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_instFromJsonShowMessageParams_fromJson___closed__10(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_instFromJsonShowMessageParams_fromJson___closed__9));
x_2 = lean_obj_once(&l_instFromJsonShowMessageParams_fromJson___closed__8, &l_instFromJsonShowMessageParams_fromJson___closed__8_once, _init_l_instFromJsonShowMessageParams_fromJson___closed__8);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_instFromJsonShowMessageParams_fromJson___closed__13(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_instFromJsonShowMessageParams_fromJson___closed__12));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_instFromJsonShowMessageParams_fromJson___closed__14(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_instFromJsonShowMessageParams_fromJson___closed__13, &l_instFromJsonShowMessageParams_fromJson___closed__13_once, _init_l_instFromJsonShowMessageParams_fromJson___closed__13);
x_2 = lean_obj_once(&l_instFromJsonShowMessageParams_fromJson___closed__5, &l_instFromJsonShowMessageParams_fromJson___closed__5_once, _init_l_instFromJsonShowMessageParams_fromJson___closed__5);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_instFromJsonShowMessageParams_fromJson___closed__15(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_instFromJsonShowMessageParams_fromJson___closed__9));
x_2 = lean_obj_once(&l_instFromJsonShowMessageParams_fromJson___closed__14, &l_instFromJsonShowMessageParams_fromJson___closed__14_once, _init_l_instFromJsonShowMessageParams_fromJson___closed__14);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instFromJsonShowMessageParams_fromJson(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = ((lean_object*)(l_instFromJsonShowMessageParams_fromJson___closed__0));
lean_inc(x_1);
x_3 = l_Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageParams_fromJson_spec__0(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_13; 
lean_dec(x_1);
x_4 = lean_ctor_get(x_3, 0);
x_13 = !lean_is_exclusive(x_3);
if (x_13 == 0)
{
x_5 = x_3;
x_6 = x_13;
goto block_12;
}
else
{
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = x_13;
goto block_12;
}
block_12:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_obj_once(&l_instFromJsonShowMessageParams_fromJson___closed__10, &l_instFromJsonShowMessageParams_fromJson___closed__10_once, _init_l_instFromJsonShowMessageParams_fromJson___closed__10);
x_8 = lean_string_append(x_7, x_4);
lean_dec(x_4);
if (x_6 == 0)
{
lean_ctor_set(x_5, 0, x_8);
x_9 = x_5;
goto block_10;
}
else
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_8);
x_9 = x_11;
goto block_10;
}
block_10:
{
return x_9;
}
}
}
else
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_21; 
lean_dec(x_1);
x_14 = lean_ctor_get(x_3, 0);
x_21 = !lean_is_exclusive(x_3);
if (x_21 == 0)
{
x_15 = x_3;
x_16 = x_21;
goto block_20;
}
else
{
lean_inc(x_14);
lean_dec(x_3);
x_15 = lean_box(0);
x_16 = x_21;
goto block_20;
}
block_20:
{
lean_object* x_17; 
if (x_16 == 0)
{
lean_ctor_set_tag(x_15, 0);
x_17 = x_15;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_14);
x_17 = x_19;
goto block_18;
}
block_18:
{
return x_17;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_3, 0);
lean_inc(x_22);
lean_dec_ref(x_3);
x_23 = ((lean_object*)(l_instFromJsonShowMessageParams_fromJson___closed__11));
x_24 = l_Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageParams_fromJson_spec__1(x_1, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_34; 
lean_dec(x_22);
x_25 = lean_ctor_get(x_24, 0);
x_34 = !lean_is_exclusive(x_24);
if (x_34 == 0)
{
x_26 = x_24;
x_27 = x_34;
goto block_33;
}
else
{
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_box(0);
x_27 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_obj_once(&l_instFromJsonShowMessageParams_fromJson___closed__15, &l_instFromJsonShowMessageParams_fromJson___closed__15_once, _init_l_instFromJsonShowMessageParams_fromJson___closed__15);
x_29 = lean_string_append(x_28, x_25);
lean_dec(x_25);
if (x_27 == 0)
{
lean_ctor_set(x_26, 0, x_29);
x_30 = x_26;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_29);
x_30 = x_32;
goto block_31;
}
block_31:
{
return x_30;
}
}
}
else
{
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_42; 
lean_dec(x_22);
x_35 = lean_ctor_get(x_24, 0);
x_42 = !lean_is_exclusive(x_24);
if (x_42 == 0)
{
x_36 = x_24;
x_37 = x_42;
goto block_41;
}
else
{
lean_inc(x_35);
lean_dec(x_24);
x_36 = lean_box(0);
x_37 = x_42;
goto block_41;
}
block_41:
{
lean_object* x_38; 
if (x_37 == 0)
{
lean_ctor_set_tag(x_36, 0);
x_38 = x_36;
goto block_39;
}
else
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_35);
x_38 = x_40;
goto block_39;
}
block_39:
{
return x_38;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; uint8_t x_52; 
x_43 = lean_ctor_get(x_24, 0);
x_52 = !lean_is_exclusive(x_24);
if (x_52 == 0)
{
x_44 = x_24;
x_45 = x_52;
goto block_51;
}
else
{
lean_inc(x_43);
lean_dec(x_24);
x_44 = lean_box(0);
x_45 = x_52;
goto block_51;
}
block_51:
{
lean_object* x_46; uint8_t x_47; lean_object* x_48; 
x_46 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_46, 0, x_43);
x_47 = lean_unbox(x_22);
lean_dec(x_22);
lean_ctor_set_uint8(x_46, sizeof(void*)*1, x_47);
if (x_45 == 0)
{
lean_ctor_set(x_44, 0, x_46);
x_48 = x_44;
goto block_49;
}
else
{
lean_object* x_50; 
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_46);
x_48 = x_50;
goto block_49;
}
block_49:
{
return x_48;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00instToJsonShowMessageParams_toJson_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_array_to_list(x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = l_List_foldl___at___00Array_appendList_spec__0___redArg(x_2, x_4);
x_1 = x_5;
x_2 = x_6;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_instToJsonShowMessageParams_toJson(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_3 = lean_ctor_get(x_1, 0);
x_4 = ((lean_object*)(l_instFromJsonShowMessageParams_fromJson___closed__0));
switch (x_2) {
case 0:
{
lean_object* x_19; 
x_19 = lean_obj_once(&l_instToJsonMessageType___lam__0___closed__1, &l_instToJsonMessageType___lam__0___closed__1_once, _init_l_instToJsonMessageType___lam__0___closed__1);
x_5 = x_19;
goto block_18;
}
case 1:
{
lean_object* x_20; 
x_20 = lean_obj_once(&l_instToJsonMessageType___lam__0___closed__3, &l_instToJsonMessageType___lam__0___closed__3_once, _init_l_instToJsonMessageType___lam__0___closed__3);
x_5 = x_20;
goto block_18;
}
case 2:
{
lean_object* x_21; 
x_21 = lean_obj_once(&l_instToJsonMessageType___lam__0___closed__5, &l_instToJsonMessageType___lam__0___closed__5_once, _init_l_instToJsonMessageType___lam__0___closed__5);
x_5 = x_21;
goto block_18;
}
default: 
{
lean_object* x_22; 
x_22 = lean_obj_once(&l_instToJsonMessageType___lam__0___closed__7, &l_instToJsonMessageType___lam__0___closed__7_once, _init_l_instToJsonMessageType___lam__0___closed__7);
x_5 = x_22;
goto block_18;
}
}
block_18:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
x_9 = ((lean_object*)(l_instFromJsonShowMessageParams_fromJson___closed__11));
lean_inc_ref(x_3);
x_10 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_10, 0, x_3);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_7);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_7);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_13);
x_15 = ((lean_object*)(l_instToJsonShowMessageParams_toJson___closed__0));
x_16 = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00instToJsonShowMessageParams_toJson_spec__0(x_14, x_15);
x_17 = l_Lean_Json_mkObj(x_16);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_instToJsonShowMessageParams_toJson___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_instToJsonShowMessageParams_toJson(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l_instFromJsonMessageActionItem_fromJson___closed__3(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_instFromJsonMessageActionItem_fromJson___closed__2));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_instFromJsonMessageActionItem_fromJson___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_instFromJsonShowMessageParams_fromJson___closed__4));
x_2 = lean_obj_once(&l_instFromJsonMessageActionItem_fromJson___closed__3, &l_instFromJsonMessageActionItem_fromJson___closed__3_once, _init_l_instFromJsonMessageActionItem_fromJson___closed__3);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_instFromJsonMessageActionItem_fromJson___closed__6(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_instFromJsonMessageActionItem_fromJson___closed__5));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_instFromJsonMessageActionItem_fromJson___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_instFromJsonMessageActionItem_fromJson___closed__6, &l_instFromJsonMessageActionItem_fromJson___closed__6_once, _init_l_instFromJsonMessageActionItem_fromJson___closed__6);
x_2 = lean_obj_once(&l_instFromJsonMessageActionItem_fromJson___closed__4, &l_instFromJsonMessageActionItem_fromJson___closed__4_once, _init_l_instFromJsonMessageActionItem_fromJson___closed__4);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_instFromJsonMessageActionItem_fromJson___closed__8(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_instFromJsonShowMessageParams_fromJson___closed__9));
x_2 = lean_obj_once(&l_instFromJsonMessageActionItem_fromJson___closed__7, &l_instFromJsonMessageActionItem_fromJson___closed__7_once, _init_l_instFromJsonMessageActionItem_fromJson___closed__7);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instFromJsonMessageActionItem_fromJson(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = ((lean_object*)(l_instFromJsonMessageActionItem_fromJson___closed__0));
x_3 = l_Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageParams_fromJson_spec__1(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_13; 
x_4 = lean_ctor_get(x_3, 0);
x_13 = !lean_is_exclusive(x_3);
if (x_13 == 0)
{
x_5 = x_3;
x_6 = x_13;
goto block_12;
}
else
{
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = x_13;
goto block_12;
}
block_12:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_obj_once(&l_instFromJsonMessageActionItem_fromJson___closed__8, &l_instFromJsonMessageActionItem_fromJson___closed__8_once, _init_l_instFromJsonMessageActionItem_fromJson___closed__8);
x_8 = lean_string_append(x_7, x_4);
lean_dec(x_4);
if (x_6 == 0)
{
lean_ctor_set(x_5, 0, x_8);
x_9 = x_5;
goto block_10;
}
else
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_8);
x_9 = x_11;
goto block_10;
}
block_10:
{
return x_9;
}
}
}
else
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_21; 
x_14 = lean_ctor_get(x_3, 0);
x_21 = !lean_is_exclusive(x_3);
if (x_21 == 0)
{
x_15 = x_3;
x_16 = x_21;
goto block_20;
}
else
{
lean_inc(x_14);
lean_dec(x_3);
x_15 = lean_box(0);
x_16 = x_21;
goto block_20;
}
block_20:
{
lean_object* x_17; 
if (x_16 == 0)
{
lean_ctor_set_tag(x_15, 0);
x_17 = x_15;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_14);
x_17 = x_19;
goto block_18;
}
block_18:
{
return x_17;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_29; 
x_22 = lean_ctor_get(x_3, 0);
x_29 = !lean_is_exclusive(x_3);
if (x_29 == 0)
{
x_23 = x_3;
x_24 = x_29;
goto block_28;
}
else
{
lean_inc(x_22);
lean_dec(x_3);
x_23 = lean_box(0);
x_24 = x_29;
goto block_28;
}
block_28:
{
lean_object* x_25; 
if (x_24 == 0)
{
x_25 = x_23;
goto block_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_22);
x_25 = x_27;
goto block_26;
}
block_26:
{
return x_25;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_instToJsonMessageActionItem_toJson(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_2 = ((lean_object*)(l_instFromJsonMessageActionItem_fromJson___closed__0));
x_3 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_3, 0, x_1);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
x_8 = ((lean_object*)(l_instToJsonShowMessageParams_toJson___closed__0));
x_9 = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00instToJsonShowMessageParams_toJson_spec__0(x_7, x_8);
x_10 = l_Lean_Json_mkObj(x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0_spec__1_spec__2(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_array_uget_borrowed(x_3, x_2);
lean_inc(x_6);
x_7 = l_instFromJsonMessageActionItem_fromJson(x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_15; 
lean_dec_ref(x_3);
x_8 = lean_ctor_get(x_7, 0);
x_15 = !lean_is_exclusive(x_7);
if (x_15 == 0)
{
x_9 = x_7;
x_10 = x_15;
goto block_14;
}
else
{
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_box(0);
x_10 = x_15;
goto block_14;
}
block_14:
{
lean_object* x_11; 
if (x_10 == 0)
{
x_11 = x_9;
goto block_12;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_8);
x_11 = x_13;
goto block_12;
}
block_12:
{
return x_11;
}
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_7, 0);
lean_inc(x_16);
lean_dec_ref(x_7);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_array_uset(x_3, x_2, x_17);
x_19 = 1;
x_20 = lean_usize_add(x_2, x_19);
x_21 = lean_array_uset(x_18, x_2, x_16);
x_2 = x_20;
x_3 = x_21;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0_spec__1_spec__2(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0_spec__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_2; size_t x_3; size_t x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_2);
lean_dec_ref(x_1);
x_3 = lean_array_size(x_2);
x_4 = 0;
x_5 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0_spec__1_spec__2(x_3, x_4, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = ((lean_object*)(l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0_spec__1___closed__0));
x_7 = lean_unsigned_to_nat(80u);
x_8 = l_Lean_Json_pretty(x_1, x_7);
x_9 = lean_string_append(x_6, x_8);
lean_dec_ref(x_8);
x_10 = ((lean_object*)(l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0_spec__1___closed__1));
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0___closed__0));
return x_2;
}
else
{
lean_object* x_3; 
x_3 = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0_spec__1(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_11; 
x_4 = lean_ctor_get(x_3, 0);
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
x_5 = x_3;
x_6 = x_11;
goto block_10;
}
else
{
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = x_11;
goto block_10;
}
block_10:
{
lean_object* x_7; 
if (x_6 == 0)
{
x_7 = x_5;
goto block_8;
}
else
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_4);
x_7 = x_9;
goto block_8;
}
block_8:
{
return x_7;
}
}
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_20; 
x_12 = lean_ctor_get(x_3, 0);
x_20 = !lean_is_exclusive(x_3);
if (x_20 == 0)
{
x_13 = x_3;
x_14 = x_20;
goto block_19;
}
else
{
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_box(0);
x_14 = x_20;
goto block_19;
}
block_19:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_12);
if (x_14 == 0)
{
lean_ctor_set(x_13, 0, x_15);
x_16 = x_13;
goto block_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_15);
x_16 = x_18;
goto block_17;
}
block_17:
{
return x_16;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageRequestParams_fromJson_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageRequestParams_fromJson_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageRequestParams_fromJson_spec__0(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
static lean_object* _init_l_instFromJsonShowMessageRequestParams_fromJson___closed__2(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_instFromJsonShowMessageRequestParams_fromJson___closed__1));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_instFromJsonShowMessageRequestParams_fromJson___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_instFromJsonShowMessageParams_fromJson___closed__4));
x_2 = lean_obj_once(&l_instFromJsonShowMessageRequestParams_fromJson___closed__2, &l_instFromJsonShowMessageRequestParams_fromJson___closed__2_once, _init_l_instFromJsonShowMessageRequestParams_fromJson___closed__2);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_instFromJsonShowMessageRequestParams_fromJson___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_instFromJsonShowMessageParams_fromJson___closed__7, &l_instFromJsonShowMessageParams_fromJson___closed__7_once, _init_l_instFromJsonShowMessageParams_fromJson___closed__7);
x_2 = lean_obj_once(&l_instFromJsonShowMessageRequestParams_fromJson___closed__3, &l_instFromJsonShowMessageRequestParams_fromJson___closed__3_once, _init_l_instFromJsonShowMessageRequestParams_fromJson___closed__3);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_instFromJsonShowMessageRequestParams_fromJson___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_instFromJsonShowMessageParams_fromJson___closed__9));
x_2 = lean_obj_once(&l_instFromJsonShowMessageRequestParams_fromJson___closed__4, &l_instFromJsonShowMessageRequestParams_fromJson___closed__4_once, _init_l_instFromJsonShowMessageRequestParams_fromJson___closed__4);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_instFromJsonShowMessageRequestParams_fromJson___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_instFromJsonShowMessageParams_fromJson___closed__13, &l_instFromJsonShowMessageParams_fromJson___closed__13_once, _init_l_instFromJsonShowMessageParams_fromJson___closed__13);
x_2 = lean_obj_once(&l_instFromJsonShowMessageRequestParams_fromJson___closed__3, &l_instFromJsonShowMessageRequestParams_fromJson___closed__3_once, _init_l_instFromJsonShowMessageRequestParams_fromJson___closed__3);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_instFromJsonShowMessageRequestParams_fromJson___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_instFromJsonShowMessageParams_fromJson___closed__9));
x_2 = lean_obj_once(&l_instFromJsonShowMessageRequestParams_fromJson___closed__6, &l_instFromJsonShowMessageRequestParams_fromJson___closed__6_once, _init_l_instFromJsonShowMessageRequestParams_fromJson___closed__6);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_instFromJsonShowMessageRequestParams_fromJson___closed__11(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_instFromJsonShowMessageRequestParams_fromJson___closed__10));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_instFromJsonShowMessageRequestParams_fromJson___closed__12(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_instFromJsonShowMessageRequestParams_fromJson___closed__11, &l_instFromJsonShowMessageRequestParams_fromJson___closed__11_once, _init_l_instFromJsonShowMessageRequestParams_fromJson___closed__11);
x_2 = lean_obj_once(&l_instFromJsonShowMessageRequestParams_fromJson___closed__3, &l_instFromJsonShowMessageRequestParams_fromJson___closed__3_once, _init_l_instFromJsonShowMessageRequestParams_fromJson___closed__3);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_instFromJsonShowMessageRequestParams_fromJson___closed__13(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_instFromJsonShowMessageParams_fromJson___closed__9));
x_2 = lean_obj_once(&l_instFromJsonShowMessageRequestParams_fromJson___closed__12, &l_instFromJsonShowMessageRequestParams_fromJson___closed__12_once, _init_l_instFromJsonShowMessageRequestParams_fromJson___closed__12);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instFromJsonShowMessageRequestParams_fromJson(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = ((lean_object*)(l_instFromJsonShowMessageParams_fromJson___closed__0));
lean_inc(x_1);
x_3 = l_Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageParams_fromJson_spec__0(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_13; 
lean_dec(x_1);
x_4 = lean_ctor_get(x_3, 0);
x_13 = !lean_is_exclusive(x_3);
if (x_13 == 0)
{
x_5 = x_3;
x_6 = x_13;
goto block_12;
}
else
{
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = x_13;
goto block_12;
}
block_12:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_obj_once(&l_instFromJsonShowMessageRequestParams_fromJson___closed__5, &l_instFromJsonShowMessageRequestParams_fromJson___closed__5_once, _init_l_instFromJsonShowMessageRequestParams_fromJson___closed__5);
x_8 = lean_string_append(x_7, x_4);
lean_dec(x_4);
if (x_6 == 0)
{
lean_ctor_set(x_5, 0, x_8);
x_9 = x_5;
goto block_10;
}
else
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_8);
x_9 = x_11;
goto block_10;
}
block_10:
{
return x_9;
}
}
}
else
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_21; 
lean_dec(x_1);
x_14 = lean_ctor_get(x_3, 0);
x_21 = !lean_is_exclusive(x_3);
if (x_21 == 0)
{
x_15 = x_3;
x_16 = x_21;
goto block_20;
}
else
{
lean_inc(x_14);
lean_dec(x_3);
x_15 = lean_box(0);
x_16 = x_21;
goto block_20;
}
block_20:
{
lean_object* x_17; 
if (x_16 == 0)
{
lean_ctor_set_tag(x_15, 0);
x_17 = x_15;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_14);
x_17 = x_19;
goto block_18;
}
block_18:
{
return x_17;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_3, 0);
lean_inc(x_22);
lean_dec_ref(x_3);
x_23 = ((lean_object*)(l_instFromJsonShowMessageParams_fromJson___closed__11));
lean_inc(x_1);
x_24 = l_Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageParams_fromJson_spec__1(x_1, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_34; 
lean_dec(x_22);
lean_dec(x_1);
x_25 = lean_ctor_get(x_24, 0);
x_34 = !lean_is_exclusive(x_24);
if (x_34 == 0)
{
x_26 = x_24;
x_27 = x_34;
goto block_33;
}
else
{
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_box(0);
x_27 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_obj_once(&l_instFromJsonShowMessageRequestParams_fromJson___closed__7, &l_instFromJsonShowMessageRequestParams_fromJson___closed__7_once, _init_l_instFromJsonShowMessageRequestParams_fromJson___closed__7);
x_29 = lean_string_append(x_28, x_25);
lean_dec(x_25);
if (x_27 == 0)
{
lean_ctor_set(x_26, 0, x_29);
x_30 = x_26;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_29);
x_30 = x_32;
goto block_31;
}
block_31:
{
return x_30;
}
}
}
else
{
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_42; 
lean_dec(x_22);
lean_dec(x_1);
x_35 = lean_ctor_get(x_24, 0);
x_42 = !lean_is_exclusive(x_24);
if (x_42 == 0)
{
x_36 = x_24;
x_37 = x_42;
goto block_41;
}
else
{
lean_inc(x_35);
lean_dec(x_24);
x_36 = lean_box(0);
x_37 = x_42;
goto block_41;
}
block_41:
{
lean_object* x_38; 
if (x_37 == 0)
{
lean_ctor_set_tag(x_36, 0);
x_38 = x_36;
goto block_39;
}
else
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_35);
x_38 = x_40;
goto block_39;
}
block_39:
{
return x_38;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_24, 0);
lean_inc(x_43);
lean_dec_ref(x_24);
x_44 = ((lean_object*)(l_instFromJsonShowMessageRequestParams_fromJson___closed__8));
x_45 = l_Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageRequestParams_fromJson_spec__0(x_1, x_44);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_55; 
lean_dec(x_43);
lean_dec(x_22);
x_46 = lean_ctor_get(x_45, 0);
x_55 = !lean_is_exclusive(x_45);
if (x_55 == 0)
{
x_47 = x_45;
x_48 = x_55;
goto block_54;
}
else
{
lean_inc(x_46);
lean_dec(x_45);
x_47 = lean_box(0);
x_48 = x_55;
goto block_54;
}
block_54:
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_obj_once(&l_instFromJsonShowMessageRequestParams_fromJson___closed__13, &l_instFromJsonShowMessageRequestParams_fromJson___closed__13_once, _init_l_instFromJsonShowMessageRequestParams_fromJson___closed__13);
x_50 = lean_string_append(x_49, x_46);
lean_dec(x_46);
if (x_48 == 0)
{
lean_ctor_set(x_47, 0, x_50);
x_51 = x_47;
goto block_52;
}
else
{
lean_object* x_53; 
x_53 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_53, 0, x_50);
x_51 = x_53;
goto block_52;
}
block_52:
{
return x_51;
}
}
}
else
{
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; uint8_t x_63; 
lean_dec(x_43);
lean_dec(x_22);
x_56 = lean_ctor_get(x_45, 0);
x_63 = !lean_is_exclusive(x_45);
if (x_63 == 0)
{
x_57 = x_45;
x_58 = x_63;
goto block_62;
}
else
{
lean_inc(x_56);
lean_dec(x_45);
x_57 = lean_box(0);
x_58 = x_63;
goto block_62;
}
block_62:
{
lean_object* x_59; 
if (x_58 == 0)
{
lean_ctor_set_tag(x_57, 0);
x_59 = x_57;
goto block_60;
}
else
{
lean_object* x_61; 
x_61 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_61, 0, x_56);
x_59 = x_61;
goto block_60;
}
block_60:
{
return x_59;
}
}
}
else
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; uint8_t x_73; 
x_64 = lean_ctor_get(x_45, 0);
x_73 = !lean_is_exclusive(x_45);
if (x_73 == 0)
{
x_65 = x_45;
x_66 = x_73;
goto block_72;
}
else
{
lean_inc(x_64);
lean_dec(x_45);
x_65 = lean_box(0);
x_66 = x_73;
goto block_72;
}
block_72:
{
lean_object* x_67; uint8_t x_68; lean_object* x_69; 
x_67 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_67, 0, x_43);
lean_ctor_set(x_67, 1, x_64);
x_68 = lean_unbox(x_22);
lean_dec(x_22);
lean_ctor_set_uint8(x_67, sizeof(void*)*2, x_68);
if (x_66 == 0)
{
lean_ctor_set(x_65, 0, x_67);
x_69 = x_65;
goto block_70;
}
else
{
lean_object* x_71; 
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_67);
x_69 = x_71;
goto block_70;
}
block_70:
{
return x_69;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00instToJsonShowMessageRequestParams_toJson_spec__0_spec__0_spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l_instToJsonMessageActionItem_toJson(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00instToJsonShowMessageRequestParams_toJson_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00instToJsonShowMessageRequestParams_toJson_spec__0_spec__0_spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Json_opt___at___00instToJsonShowMessageRequestParams_toJson_spec__0_spec__0(lean_object* x_1) {
_start:
{
size_t x_2; size_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_array_size(x_1);
x_3 = 0;
x_4 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00instToJsonShowMessageRequestParams_toJson_spec__0_spec__0_spec__1(x_2, x_3, x_1);
x_5 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00instToJsonShowMessageRequestParams_toJson_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec_ref(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = l_Array_toJson___at___00Lean_Json_opt___at___00instToJsonShowMessageRequestParams_toJson_spec__0_spec__0(x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_instToJsonShowMessageRequestParams_toJson(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = ((lean_object*)(l_instFromJsonShowMessageParams_fromJson___closed__0));
switch (x_2) {
case 0:
{
lean_object* x_23; 
x_23 = lean_obj_once(&l_instToJsonMessageType___lam__0___closed__1, &l_instToJsonMessageType___lam__0___closed__1_once, _init_l_instToJsonMessageType___lam__0___closed__1);
x_6 = x_23;
goto block_22;
}
case 1:
{
lean_object* x_24; 
x_24 = lean_obj_once(&l_instToJsonMessageType___lam__0___closed__3, &l_instToJsonMessageType___lam__0___closed__3_once, _init_l_instToJsonMessageType___lam__0___closed__3);
x_6 = x_24;
goto block_22;
}
case 2:
{
lean_object* x_25; 
x_25 = lean_obj_once(&l_instToJsonMessageType___lam__0___closed__5, &l_instToJsonMessageType___lam__0___closed__5_once, _init_l_instToJsonMessageType___lam__0___closed__5);
x_6 = x_25;
goto block_22;
}
default: 
{
lean_object* x_26; 
x_26 = lean_obj_once(&l_instToJsonMessageType___lam__0___closed__7, &l_instToJsonMessageType___lam__0___closed__7_once, _init_l_instToJsonMessageType___lam__0___closed__7);
x_6 = x_26;
goto block_22;
}
}
block_22:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = ((lean_object*)(l_instFromJsonShowMessageParams_fromJson___closed__11));
x_11 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_11, 0, x_3);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_8);
x_14 = ((lean_object*)(l_instFromJsonShowMessageRequestParams_fromJson___closed__8));
x_15 = l_Lean_Json_opt___at___00instToJsonShowMessageRequestParams_toJson_spec__0(x_14, x_4);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_8);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_13);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_9);
lean_ctor_set(x_18, 1, x_17);
x_19 = ((lean_object*)(l_instToJsonShowMessageParams_toJson___closed__0));
x_20 = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00instToJsonShowMessageParams_toJson_spec__0(x_18, x_19);
x_21 = l_Lean_Json_mkObj(x_20);
return x_21;
}
}
}
lean_object* runtime_initialize_Lean_Data_Json_FromToJson_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_Lsp_Window(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Data_Json_FromToJson_Basic(builtin)
;
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
res = initialize_Lean_Data_Json_FromToJson_Basic(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Lsp_Window(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Data_Lsp_Window(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Data_Lsp_Window(builtin);
}
#ifdef __cplusplus
}
#endif

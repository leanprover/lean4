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
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_JsonNumber_fromNat(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
lean_object* l_Option_toJson(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Option_fromJson_x3f(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_instFromJsonMessageType___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_instFromJsonMessageType___lam__0___boxed(lean_object*);
static const lean_closure_object l_instFromJsonMessageType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instFromJsonMessageType___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instFromJsonMessageType___closed__0 = (const lean_object*)&l_instFromJsonMessageType___closed__0_value;
LEAN_EXPORT const lean_object* l_instFromJsonMessageType = (const lean_object*)&l_instFromJsonMessageType___closed__0_value;
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
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageParams_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageParams_fromJson_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageParams_fromJson_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageParams_fromJson_spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l_instFromJsonShowMessageParams_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "type"};
static const lean_object* l_instFromJsonShowMessageParams_fromJson___closed__0 = (const lean_object*)&l_instFromJsonShowMessageParams_fromJson___closed__0_value;
static const lean_string_object l_instFromJsonShowMessageParams_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "ShowMessageParams"};
static const lean_object* l_instFromJsonShowMessageParams_fromJson___closed__1 = (const lean_object*)&l_instFromJsonShowMessageParams_fromJson___closed__1_value;
static const lean_ctor_object l_instFromJsonShowMessageParams_fromJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_instFromJsonShowMessageParams_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(28, 246, 128, 63, 249, 10, 125, 27)}};
static const lean_object* l_instFromJsonShowMessageParams_fromJson___closed__2 = (const lean_object*)&l_instFromJsonShowMessageParams_fromJson___closed__2_value;
static lean_once_cell_t l_instFromJsonShowMessageParams_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_instFromJsonShowMessageParams_fromJson___closed__3;
static const lean_string_object l_instFromJsonShowMessageParams_fromJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_instFromJsonShowMessageParams_fromJson___closed__4 = (const lean_object*)&l_instFromJsonShowMessageParams_fromJson___closed__4_value;
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
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00instToJsonShowMessageParams_toJson_spec__0(lean_object*, lean_object*);
static const lean_array_object l_instToJsonShowMessageParams_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_instToJsonShowMessageParams_toJson___closed__0 = (const lean_object*)&l_instToJsonShowMessageParams_toJson___closed__0_value;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0_spec__1_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "expected JSON array, got '"};
static const lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0_spec__1___closed__0 = (const lean_object*)&l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0_spec__1___closed__0_value;
static const lean_string_object l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0_spec__1___closed__1 = (const lean_object*)&l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0_spec__1___closed__1_value;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00instToJsonShowMessageRequestParams_toJson_spec__0_spec__0_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00instToJsonShowMessageRequestParams_toJson_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Json_opt___at___00instToJsonShowMessageRequestParams_toJson_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00instToJsonShowMessageRequestParams_toJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToJsonShowMessageRequestParams_toJson(lean_object*);
static const lean_closure_object l_instToJsonShowMessageRequestParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instToJsonShowMessageRequestParams_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instToJsonShowMessageRequestParams___closed__0 = (const lean_object*)&l_instToJsonShowMessageRequestParams___closed__0_value;
LEAN_EXPORT const lean_object* l_instToJsonShowMessageRequestParams = (const lean_object*)&l_instToJsonShowMessageRequestParams___closed__0_value;
static const lean_closure_object l_instFromJsonShowMessageResponse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Option_fromJson_x3f, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_instFromJsonMessageActionItem___closed__0_value)} };
static const lean_object* l_instFromJsonShowMessageResponse___closed__0 = (const lean_object*)&l_instFromJsonShowMessageResponse___closed__0_value;
LEAN_EXPORT const lean_object* l_instFromJsonShowMessageResponse = (const lean_object*)&l_instFromJsonShowMessageResponse___closed__0_value;
static const lean_closure_object l_instToJsonShowMessageResponse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Option_toJson, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_instToJsonMessageActionItem___closed__0_value)} };
static const lean_object* l_instToJsonShowMessageResponse___closed__0 = (const lean_object*)&l_instToJsonShowMessageResponse___closed__0_value;
LEAN_EXPORT const lean_object* l_instToJsonShowMessageResponse = (const lean_object*)&l_instToJsonShowMessageResponse___closed__0_value;
LEAN_EXPORT lean_object* l_MessageType_ctorIdx(uint8_t v_x_1_){
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
LEAN_EXPORT lean_object* l_MessageType_ctorIdx___boxed(lean_object* v_x_6_){
_start:
{
uint8_t v_x_boxed_7_; lean_object* v_res_8_; 
v_x_boxed_7_ = lean_unbox(v_x_6_);
v_res_8_ = l_MessageType_ctorIdx(v_x_boxed_7_);
return v_res_8_;
}
}
LEAN_EXPORT lean_object* l_MessageType_toCtorIdx(uint8_t v_x_9_){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = l_MessageType_ctorIdx(v_x_9_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l_MessageType_toCtorIdx___boxed(lean_object* v_x_11_){
_start:
{
uint8_t v_x_4__boxed_12_; lean_object* v_res_13_; 
v_x_4__boxed_12_ = lean_unbox(v_x_11_);
v_res_13_ = l_MessageType_toCtorIdx(v_x_4__boxed_12_);
return v_res_13_;
}
}
LEAN_EXPORT lean_object* l_MessageType_ctorElim___redArg(lean_object* v_k_14_){
_start:
{
lean_inc(v_k_14_);
return v_k_14_;
}
}
LEAN_EXPORT lean_object* l_MessageType_ctorElim___redArg___boxed(lean_object* v_k_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = l_MessageType_ctorElim___redArg(v_k_15_);
lean_dec(v_k_15_);
return v_res_16_;
}
}
LEAN_EXPORT lean_object* l_MessageType_ctorElim(lean_object* v_motive_17_, lean_object* v_ctorIdx_18_, uint8_t v_t_19_, lean_object* v_h_20_, lean_object* v_k_21_){
_start:
{
lean_inc(v_k_21_);
return v_k_21_;
}
}
LEAN_EXPORT lean_object* l_MessageType_ctorElim___boxed(lean_object* v_motive_22_, lean_object* v_ctorIdx_23_, lean_object* v_t_24_, lean_object* v_h_25_, lean_object* v_k_26_){
_start:
{
uint8_t v_t_boxed_27_; lean_object* v_res_28_; 
v_t_boxed_27_ = lean_unbox(v_t_24_);
v_res_28_ = l_MessageType_ctorElim(v_motive_22_, v_ctorIdx_23_, v_t_boxed_27_, v_h_25_, v_k_26_);
lean_dec(v_k_26_);
lean_dec(v_ctorIdx_23_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* l_MessageType_error_elim___redArg(lean_object* v_error_29_){
_start:
{
lean_inc(v_error_29_);
return v_error_29_;
}
}
LEAN_EXPORT lean_object* l_MessageType_error_elim___redArg___boxed(lean_object* v_error_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = l_MessageType_error_elim___redArg(v_error_30_);
lean_dec(v_error_30_);
return v_res_31_;
}
}
LEAN_EXPORT lean_object* l_MessageType_error_elim(lean_object* v_motive_32_, uint8_t v_t_33_, lean_object* v_h_34_, lean_object* v_error_35_){
_start:
{
lean_inc(v_error_35_);
return v_error_35_;
}
}
LEAN_EXPORT lean_object* l_MessageType_error_elim___boxed(lean_object* v_motive_36_, lean_object* v_t_37_, lean_object* v_h_38_, lean_object* v_error_39_){
_start:
{
uint8_t v_t_boxed_40_; lean_object* v_res_41_; 
v_t_boxed_40_ = lean_unbox(v_t_37_);
v_res_41_ = l_MessageType_error_elim(v_motive_36_, v_t_boxed_40_, v_h_38_, v_error_39_);
lean_dec(v_error_39_);
return v_res_41_;
}
}
LEAN_EXPORT lean_object* l_MessageType_warning_elim___redArg(lean_object* v_warning_42_){
_start:
{
lean_inc(v_warning_42_);
return v_warning_42_;
}
}
LEAN_EXPORT lean_object* l_MessageType_warning_elim___redArg___boxed(lean_object* v_warning_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l_MessageType_warning_elim___redArg(v_warning_43_);
lean_dec(v_warning_43_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* l_MessageType_warning_elim(lean_object* v_motive_45_, uint8_t v_t_46_, lean_object* v_h_47_, lean_object* v_warning_48_){
_start:
{
lean_inc(v_warning_48_);
return v_warning_48_;
}
}
LEAN_EXPORT lean_object* l_MessageType_warning_elim___boxed(lean_object* v_motive_49_, lean_object* v_t_50_, lean_object* v_h_51_, lean_object* v_warning_52_){
_start:
{
uint8_t v_t_boxed_53_; lean_object* v_res_54_; 
v_t_boxed_53_ = lean_unbox(v_t_50_);
v_res_54_ = l_MessageType_warning_elim(v_motive_49_, v_t_boxed_53_, v_h_51_, v_warning_52_);
lean_dec(v_warning_52_);
return v_res_54_;
}
}
LEAN_EXPORT lean_object* l_MessageType_info_elim___redArg(lean_object* v_info_55_){
_start:
{
lean_inc(v_info_55_);
return v_info_55_;
}
}
LEAN_EXPORT lean_object* l_MessageType_info_elim___redArg___boxed(lean_object* v_info_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = l_MessageType_info_elim___redArg(v_info_56_);
lean_dec(v_info_56_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* l_MessageType_info_elim(lean_object* v_motive_58_, uint8_t v_t_59_, lean_object* v_h_60_, lean_object* v_info_61_){
_start:
{
lean_inc(v_info_61_);
return v_info_61_;
}
}
LEAN_EXPORT lean_object* l_MessageType_info_elim___boxed(lean_object* v_motive_62_, lean_object* v_t_63_, lean_object* v_h_64_, lean_object* v_info_65_){
_start:
{
uint8_t v_t_boxed_66_; lean_object* v_res_67_; 
v_t_boxed_66_ = lean_unbox(v_t_63_);
v_res_67_ = l_MessageType_info_elim(v_motive_62_, v_t_boxed_66_, v_h_64_, v_info_65_);
lean_dec(v_info_65_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l_MessageType_log_elim___redArg(lean_object* v_log_68_){
_start:
{
lean_inc(v_log_68_);
return v_log_68_;
}
}
LEAN_EXPORT lean_object* l_MessageType_log_elim___redArg___boxed(lean_object* v_log_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = l_MessageType_log_elim___redArg(v_log_69_);
lean_dec(v_log_69_);
return v_res_70_;
}
}
LEAN_EXPORT lean_object* l_MessageType_log_elim(lean_object* v_motive_71_, uint8_t v_t_72_, lean_object* v_h_73_, lean_object* v_log_74_){
_start:
{
lean_inc(v_log_74_);
return v_log_74_;
}
}
LEAN_EXPORT lean_object* l_MessageType_log_elim___boxed(lean_object* v_motive_75_, lean_object* v_t_76_, lean_object* v_h_77_, lean_object* v_log_78_){
_start:
{
uint8_t v_t_boxed_79_; lean_object* v_res_80_; 
v_t_boxed_79_ = lean_unbox(v_t_76_);
v_res_80_ = l_MessageType_log_elim(v_motive_75_, v_t_boxed_79_, v_h_77_, v_log_78_);
lean_dec(v_log_78_);
return v_res_80_;
}
}
static lean_object* _init_l_instFromJsonMessageType___lam__0___closed__2(void){
_start:
{
lean_object* v_natZero_84_; lean_object* v_intZero_85_; 
v_natZero_84_ = lean_unsigned_to_nat(0u);
v_intZero_85_ = lean_nat_to_int(v_natZero_84_);
return v_intZero_85_;
}
}
LEAN_EXPORT lean_object* l_instFromJsonMessageType___lam__0(lean_object* v_x_98_){
_start:
{
if (lean_obj_tag(v_x_98_) == 2)
{
lean_object* v_n_101_; lean_object* v_mantissa_102_; lean_object* v_exponent_103_; lean_object* v_natZero_104_; lean_object* v_intZero_105_; uint8_t v_isNeg_106_; 
v_n_101_ = lean_ctor_get(v_x_98_, 0);
v_mantissa_102_ = lean_ctor_get(v_n_101_, 0);
v_exponent_103_ = lean_ctor_get(v_n_101_, 1);
v_natZero_104_ = lean_unsigned_to_nat(0u);
v_intZero_105_ = lean_obj_once(&l_instFromJsonMessageType___lam__0___closed__2, &l_instFromJsonMessageType___lam__0___closed__2_once, _init_l_instFromJsonMessageType___lam__0___closed__2);
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
v___x_117_ = ((lean_object*)(l_instFromJsonMessageType___lam__0___closed__3));
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
v___x_119_ = ((lean_object*)(l_instFromJsonMessageType___lam__0___closed__4));
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
v___x_121_ = ((lean_object*)(l_instFromJsonMessageType___lam__0___closed__5));
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
v___x_123_ = ((lean_object*)(l_instFromJsonMessageType___lam__0___closed__6));
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
v___x_100_ = ((lean_object*)(l_instFromJsonMessageType___lam__0___closed__1));
return v___x_100_;
}
}
}
LEAN_EXPORT lean_object* l_instFromJsonMessageType___lam__0___boxed(lean_object* v_x_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = l_instFromJsonMessageType___lam__0(v_x_124_);
lean_dec(v_x_124_);
return v_res_125_;
}
}
static lean_object* _init_l_instToJsonMessageType___lam__0___closed__0(void){
_start:
{
lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_128_ = lean_unsigned_to_nat(1u);
v___x_129_ = l_Lean_JsonNumber_fromNat(v___x_128_);
return v___x_129_;
}
}
static lean_object* _init_l_instToJsonMessageType___lam__0___closed__1(void){
_start:
{
lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_130_ = lean_obj_once(&l_instToJsonMessageType___lam__0___closed__0, &l_instToJsonMessageType___lam__0___closed__0_once, _init_l_instToJsonMessageType___lam__0___closed__0);
v___x_131_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_131_, 0, v___x_130_);
return v___x_131_;
}
}
static lean_object* _init_l_instToJsonMessageType___lam__0___closed__2(void){
_start:
{
lean_object* v___x_132_; lean_object* v___x_133_; 
v___x_132_ = lean_unsigned_to_nat(2u);
v___x_133_ = l_Lean_JsonNumber_fromNat(v___x_132_);
return v___x_133_;
}
}
static lean_object* _init_l_instToJsonMessageType___lam__0___closed__3(void){
_start:
{
lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_134_ = lean_obj_once(&l_instToJsonMessageType___lam__0___closed__2, &l_instToJsonMessageType___lam__0___closed__2_once, _init_l_instToJsonMessageType___lam__0___closed__2);
v___x_135_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_135_, 0, v___x_134_);
return v___x_135_;
}
}
static lean_object* _init_l_instToJsonMessageType___lam__0___closed__4(void){
_start:
{
lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_136_ = lean_unsigned_to_nat(3u);
v___x_137_ = l_Lean_JsonNumber_fromNat(v___x_136_);
return v___x_137_;
}
}
static lean_object* _init_l_instToJsonMessageType___lam__0___closed__5(void){
_start:
{
lean_object* v___x_138_; lean_object* v___x_139_; 
v___x_138_ = lean_obj_once(&l_instToJsonMessageType___lam__0___closed__4, &l_instToJsonMessageType___lam__0___closed__4_once, _init_l_instToJsonMessageType___lam__0___closed__4);
v___x_139_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_139_, 0, v___x_138_);
return v___x_139_;
}
}
static lean_object* _init_l_instToJsonMessageType___lam__0___closed__6(void){
_start:
{
lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_140_ = lean_unsigned_to_nat(4u);
v___x_141_ = l_Lean_JsonNumber_fromNat(v___x_140_);
return v___x_141_;
}
}
static lean_object* _init_l_instToJsonMessageType___lam__0___closed__7(void){
_start:
{
lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_142_ = lean_obj_once(&l_instToJsonMessageType___lam__0___closed__6, &l_instToJsonMessageType___lam__0___closed__6_once, _init_l_instToJsonMessageType___lam__0___closed__6);
v___x_143_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_143_, 0, v___x_142_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l_instToJsonMessageType___lam__0(uint8_t v_x_144_){
_start:
{
switch(v_x_144_)
{
case 0:
{
lean_object* v___x_145_; 
v___x_145_ = lean_obj_once(&l_instToJsonMessageType___lam__0___closed__1, &l_instToJsonMessageType___lam__0___closed__1_once, _init_l_instToJsonMessageType___lam__0___closed__1);
return v___x_145_;
}
case 1:
{
lean_object* v___x_146_; 
v___x_146_ = lean_obj_once(&l_instToJsonMessageType___lam__0___closed__3, &l_instToJsonMessageType___lam__0___closed__3_once, _init_l_instToJsonMessageType___lam__0___closed__3);
return v___x_146_;
}
case 2:
{
lean_object* v___x_147_; 
v___x_147_ = lean_obj_once(&l_instToJsonMessageType___lam__0___closed__5, &l_instToJsonMessageType___lam__0___closed__5_once, _init_l_instToJsonMessageType___lam__0___closed__5);
return v___x_147_;
}
default: 
{
lean_object* v___x_148_; 
v___x_148_ = lean_obj_once(&l_instToJsonMessageType___lam__0___closed__7, &l_instToJsonMessageType___lam__0___closed__7_once, _init_l_instToJsonMessageType___lam__0___closed__7);
return v___x_148_;
}
}
}
}
LEAN_EXPORT lean_object* l_instToJsonMessageType___lam__0___boxed(lean_object* v_x_149_){
_start:
{
uint8_t v_x_106__boxed_150_; lean_object* v_res_151_; 
v_x_106__boxed_150_ = lean_unbox(v_x_149_);
v_res_151_ = l_instToJsonMessageType___lam__0(v_x_106__boxed_150_);
return v_res_151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageParams_fromJson_spec__0(lean_object* v_j_154_, lean_object* v_k_155_){
_start:
{
lean_object* v___x_158_; 
v___x_158_ = l_Lean_Json_getObjValD(v_j_154_, v_k_155_);
if (lean_obj_tag(v___x_158_) == 2)
{
lean_object* v_n_159_; lean_object* v_mantissa_160_; lean_object* v_exponent_161_; lean_object* v_natZero_162_; lean_object* v_intZero_163_; uint8_t v_isNeg_164_; 
v_n_159_ = lean_ctor_get(v___x_158_, 0);
lean_inc_ref(v_n_159_);
lean_dec_ref(v___x_158_);
v_mantissa_160_ = lean_ctor_get(v_n_159_, 0);
lean_inc(v_mantissa_160_);
v_exponent_161_ = lean_ctor_get(v_n_159_, 1);
lean_inc(v_exponent_161_);
lean_dec_ref(v_n_159_);
v_natZero_162_ = lean_unsigned_to_nat(0u);
v_intZero_163_ = lean_obj_once(&l_instFromJsonMessageType___lam__0___closed__2, &l_instFromJsonMessageType___lam__0___closed__2_once, _init_l_instFromJsonMessageType___lam__0___closed__2);
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
v___x_175_ = ((lean_object*)(l_instFromJsonMessageType___lam__0___closed__3));
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
v___x_177_ = ((lean_object*)(l_instFromJsonMessageType___lam__0___closed__4));
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
v___x_179_ = ((lean_object*)(l_instFromJsonMessageType___lam__0___closed__5));
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
v___x_181_ = ((lean_object*)(l_instFromJsonMessageType___lam__0___closed__6));
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
v___x_157_ = ((lean_object*)(l_instFromJsonMessageType___lam__0___closed__1));
return v___x_157_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageParams_fromJson_spec__0___boxed(lean_object* v_j_182_, lean_object* v_k_183_){
_start:
{
lean_object* v_res_184_; 
v_res_184_ = l_Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageParams_fromJson_spec__0(v_j_182_, v_k_183_);
lean_dec_ref(v_k_183_);
return v_res_184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageParams_fromJson_spec__1(lean_object* v_j_185_, lean_object* v_k_186_){
_start:
{
lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_187_ = l_Lean_Json_getObjValD(v_j_185_, v_k_186_);
v___x_188_ = l_Lean_Json_getStr_x3f(v___x_187_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageParams_fromJson_spec__1___boxed(lean_object* v_j_189_, lean_object* v_k_190_){
_start:
{
lean_object* v_res_191_; 
v_res_191_ = l_Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageParams_fromJson_spec__1(v_j_189_, v_k_190_);
lean_dec_ref(v_k_190_);
return v_res_191_;
}
}
static lean_object* _init_l_instFromJsonShowMessageParams_fromJson___closed__3(void){
_start:
{
uint8_t v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_196_ = 1;
v___x_197_ = ((lean_object*)(l_instFromJsonShowMessageParams_fromJson___closed__2));
v___x_198_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_197_, v___x_196_);
return v___x_198_;
}
}
static lean_object* _init_l_instFromJsonShowMessageParams_fromJson___closed__5(void){
_start:
{
lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_200_ = ((lean_object*)(l_instFromJsonShowMessageParams_fromJson___closed__4));
v___x_201_ = lean_obj_once(&l_instFromJsonShowMessageParams_fromJson___closed__3, &l_instFromJsonShowMessageParams_fromJson___closed__3_once, _init_l_instFromJsonShowMessageParams_fromJson___closed__3);
v___x_202_ = lean_string_append(v___x_201_, v___x_200_);
return v___x_202_;
}
}
static lean_object* _init_l_instFromJsonShowMessageParams_fromJson___closed__7(void){
_start:
{
uint8_t v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; 
v___x_205_ = 1;
v___x_206_ = ((lean_object*)(l_instFromJsonShowMessageParams_fromJson___closed__6));
v___x_207_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_206_, v___x_205_);
return v___x_207_;
}
}
static lean_object* _init_l_instFromJsonShowMessageParams_fromJson___closed__8(void){
_start:
{
lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_208_ = lean_obj_once(&l_instFromJsonShowMessageParams_fromJson___closed__7, &l_instFromJsonShowMessageParams_fromJson___closed__7_once, _init_l_instFromJsonShowMessageParams_fromJson___closed__7);
v___x_209_ = lean_obj_once(&l_instFromJsonShowMessageParams_fromJson___closed__5, &l_instFromJsonShowMessageParams_fromJson___closed__5_once, _init_l_instFromJsonShowMessageParams_fromJson___closed__5);
v___x_210_ = lean_string_append(v___x_209_, v___x_208_);
return v___x_210_;
}
}
static lean_object* _init_l_instFromJsonShowMessageParams_fromJson___closed__10(void){
_start:
{
lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; 
v___x_212_ = ((lean_object*)(l_instFromJsonShowMessageParams_fromJson___closed__9));
v___x_213_ = lean_obj_once(&l_instFromJsonShowMessageParams_fromJson___closed__8, &l_instFromJsonShowMessageParams_fromJson___closed__8_once, _init_l_instFromJsonShowMessageParams_fromJson___closed__8);
v___x_214_ = lean_string_append(v___x_213_, v___x_212_);
return v___x_214_;
}
}
static lean_object* _init_l_instFromJsonShowMessageParams_fromJson___closed__13(void){
_start:
{
uint8_t v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_218_ = 1;
v___x_219_ = ((lean_object*)(l_instFromJsonShowMessageParams_fromJson___closed__12));
v___x_220_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_219_, v___x_218_);
return v___x_220_;
}
}
static lean_object* _init_l_instFromJsonShowMessageParams_fromJson___closed__14(void){
_start:
{
lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_221_ = lean_obj_once(&l_instFromJsonShowMessageParams_fromJson___closed__13, &l_instFromJsonShowMessageParams_fromJson___closed__13_once, _init_l_instFromJsonShowMessageParams_fromJson___closed__13);
v___x_222_ = lean_obj_once(&l_instFromJsonShowMessageParams_fromJson___closed__5, &l_instFromJsonShowMessageParams_fromJson___closed__5_once, _init_l_instFromJsonShowMessageParams_fromJson___closed__5);
v___x_223_ = lean_string_append(v___x_222_, v___x_221_);
return v___x_223_;
}
}
static lean_object* _init_l_instFromJsonShowMessageParams_fromJson___closed__15(void){
_start:
{
lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_224_ = ((lean_object*)(l_instFromJsonShowMessageParams_fromJson___closed__9));
v___x_225_ = lean_obj_once(&l_instFromJsonShowMessageParams_fromJson___closed__14, &l_instFromJsonShowMessageParams_fromJson___closed__14_once, _init_l_instFromJsonShowMessageParams_fromJson___closed__14);
v___x_226_ = lean_string_append(v___x_225_, v___x_224_);
return v___x_226_;
}
}
LEAN_EXPORT lean_object* l_instFromJsonShowMessageParams_fromJson(lean_object* v_json_227_){
_start:
{
lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_228_ = ((lean_object*)(l_instFromJsonShowMessageParams_fromJson___closed__0));
lean_inc(v_json_227_);
v___x_229_ = l_Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageParams_fromJson_spec__0(v_json_227_, v___x_228_);
if (lean_obj_tag(v___x_229_) == 0)
{
lean_object* v_a_230_; lean_object* v___x_232_; uint8_t v_isShared_233_; uint8_t v_isSharedCheck_239_; 
lean_dec(v_json_227_);
v_a_230_ = lean_ctor_get(v___x_229_, 0);
v_isSharedCheck_239_ = !lean_is_exclusive(v___x_229_);
if (v_isSharedCheck_239_ == 0)
{
v___x_232_ = v___x_229_;
v_isShared_233_ = v_isSharedCheck_239_;
goto v_resetjp_231_;
}
else
{
lean_inc(v_a_230_);
lean_dec(v___x_229_);
v___x_232_ = lean_box(0);
v_isShared_233_ = v_isSharedCheck_239_;
goto v_resetjp_231_;
}
v_resetjp_231_:
{
lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_237_; 
v___x_234_ = lean_obj_once(&l_instFromJsonShowMessageParams_fromJson___closed__10, &l_instFromJsonShowMessageParams_fromJson___closed__10_once, _init_l_instFromJsonShowMessageParams_fromJson___closed__10);
v___x_235_ = lean_string_append(v___x_234_, v_a_230_);
lean_dec(v_a_230_);
if (v_isShared_233_ == 0)
{
lean_ctor_set(v___x_232_, 0, v___x_235_);
v___x_237_ = v___x_232_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(0, 1, 0);
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
else
{
if (lean_obj_tag(v___x_229_) == 0)
{
lean_object* v_a_240_; lean_object* v___x_242_; uint8_t v_isShared_243_; uint8_t v_isSharedCheck_247_; 
lean_dec(v_json_227_);
v_a_240_ = lean_ctor_get(v___x_229_, 0);
v_isSharedCheck_247_ = !lean_is_exclusive(v___x_229_);
if (v_isSharedCheck_247_ == 0)
{
v___x_242_ = v___x_229_;
v_isShared_243_ = v_isSharedCheck_247_;
goto v_resetjp_241_;
}
else
{
lean_inc(v_a_240_);
lean_dec(v___x_229_);
v___x_242_ = lean_box(0);
v_isShared_243_ = v_isSharedCheck_247_;
goto v_resetjp_241_;
}
v_resetjp_241_:
{
lean_object* v___x_245_; 
if (v_isShared_243_ == 0)
{
lean_ctor_set_tag(v___x_242_, 0);
v___x_245_ = v___x_242_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_246_; 
v_reuseFailAlloc_246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_246_, 0, v_a_240_);
v___x_245_ = v_reuseFailAlloc_246_;
goto v_reusejp_244_;
}
v_reusejp_244_:
{
return v___x_245_;
}
}
}
else
{
lean_object* v_a_248_; lean_object* v___x_249_; lean_object* v___x_250_; 
v_a_248_ = lean_ctor_get(v___x_229_, 0);
lean_inc(v_a_248_);
lean_dec_ref(v___x_229_);
v___x_249_ = ((lean_object*)(l_instFromJsonShowMessageParams_fromJson___closed__11));
v___x_250_ = l_Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageParams_fromJson_spec__1(v_json_227_, v___x_249_);
if (lean_obj_tag(v___x_250_) == 0)
{
lean_object* v_a_251_; lean_object* v___x_253_; uint8_t v_isShared_254_; uint8_t v_isSharedCheck_260_; 
lean_dec(v_a_248_);
v_a_251_ = lean_ctor_get(v___x_250_, 0);
v_isSharedCheck_260_ = !lean_is_exclusive(v___x_250_);
if (v_isSharedCheck_260_ == 0)
{
v___x_253_ = v___x_250_;
v_isShared_254_ = v_isSharedCheck_260_;
goto v_resetjp_252_;
}
else
{
lean_inc(v_a_251_);
lean_dec(v___x_250_);
v___x_253_ = lean_box(0);
v_isShared_254_ = v_isSharedCheck_260_;
goto v_resetjp_252_;
}
v_resetjp_252_:
{
lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_258_; 
v___x_255_ = lean_obj_once(&l_instFromJsonShowMessageParams_fromJson___closed__15, &l_instFromJsonShowMessageParams_fromJson___closed__15_once, _init_l_instFromJsonShowMessageParams_fromJson___closed__15);
v___x_256_ = lean_string_append(v___x_255_, v_a_251_);
lean_dec(v_a_251_);
if (v_isShared_254_ == 0)
{
lean_ctor_set(v___x_253_, 0, v___x_256_);
v___x_258_ = v___x_253_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v___x_256_);
v___x_258_ = v_reuseFailAlloc_259_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
return v___x_258_;
}
}
}
else
{
if (lean_obj_tag(v___x_250_) == 0)
{
lean_object* v_a_261_; lean_object* v___x_263_; uint8_t v_isShared_264_; uint8_t v_isSharedCheck_268_; 
lean_dec(v_a_248_);
v_a_261_ = lean_ctor_get(v___x_250_, 0);
v_isSharedCheck_268_ = !lean_is_exclusive(v___x_250_);
if (v_isSharedCheck_268_ == 0)
{
v___x_263_ = v___x_250_;
v_isShared_264_ = v_isSharedCheck_268_;
goto v_resetjp_262_;
}
else
{
lean_inc(v_a_261_);
lean_dec(v___x_250_);
v___x_263_ = lean_box(0);
v_isShared_264_ = v_isSharedCheck_268_;
goto v_resetjp_262_;
}
v_resetjp_262_:
{
lean_object* v___x_266_; 
if (v_isShared_264_ == 0)
{
lean_ctor_set_tag(v___x_263_, 0);
v___x_266_ = v___x_263_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_267_; 
v_reuseFailAlloc_267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_267_, 0, v_a_261_);
v___x_266_ = v_reuseFailAlloc_267_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
return v___x_266_;
}
}
}
else
{
lean_object* v_a_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_278_; 
v_a_269_ = lean_ctor_get(v___x_250_, 0);
v_isSharedCheck_278_ = !lean_is_exclusive(v___x_250_);
if (v_isSharedCheck_278_ == 0)
{
v___x_271_ = v___x_250_;
v_isShared_272_ = v_isSharedCheck_278_;
goto v_resetjp_270_;
}
else
{
lean_inc(v_a_269_);
lean_dec(v___x_250_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_278_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
lean_object* v___x_273_; uint8_t v___x_274_; lean_object* v___x_276_; 
v___x_273_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_273_, 0, v_a_269_);
v___x_274_ = lean_unbox(v_a_248_);
lean_dec(v_a_248_);
lean_ctor_set_uint8(v___x_273_, sizeof(void*)*1, v___x_274_);
if (v_isShared_272_ == 0)
{
lean_ctor_set(v___x_271_, 0, v___x_273_);
v___x_276_ = v___x_271_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v___x_273_);
v___x_276_ = v_reuseFailAlloc_277_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
return v___x_276_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00instToJsonShowMessageParams_toJson_spec__0(lean_object* v_a_281_, lean_object* v_a_282_){
_start:
{
if (lean_obj_tag(v_a_281_) == 0)
{
lean_object* v___x_283_; 
v___x_283_ = lean_array_to_list(v_a_282_);
return v___x_283_;
}
else
{
lean_object* v_head_284_; lean_object* v_tail_285_; lean_object* v___x_286_; 
v_head_284_ = lean_ctor_get(v_a_281_, 0);
lean_inc(v_head_284_);
v_tail_285_ = lean_ctor_get(v_a_281_, 1);
lean_inc(v_tail_285_);
lean_dec_ref(v_a_281_);
v___x_286_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_282_, v_head_284_);
v_a_281_ = v_tail_285_;
v_a_282_ = v___x_286_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_instToJsonShowMessageParams_toJson(lean_object* v_x_290_){
_start:
{
uint8_t v_type_291_; lean_object* v_message_292_; lean_object* v___x_293_; lean_object* v___y_295_; 
v_type_291_ = lean_ctor_get_uint8(v_x_290_, sizeof(void*)*1);
v_message_292_ = lean_ctor_get(v_x_290_, 0);
v___x_293_ = ((lean_object*)(l_instFromJsonShowMessageParams_fromJson___closed__0));
switch(v_type_291_)
{
case 0:
{
lean_object* v___x_308_; 
v___x_308_ = lean_obj_once(&l_instToJsonMessageType___lam__0___closed__1, &l_instToJsonMessageType___lam__0___closed__1_once, _init_l_instToJsonMessageType___lam__0___closed__1);
v___y_295_ = v___x_308_;
goto v___jp_294_;
}
case 1:
{
lean_object* v___x_309_; 
v___x_309_ = lean_obj_once(&l_instToJsonMessageType___lam__0___closed__3, &l_instToJsonMessageType___lam__0___closed__3_once, _init_l_instToJsonMessageType___lam__0___closed__3);
v___y_295_ = v___x_309_;
goto v___jp_294_;
}
case 2:
{
lean_object* v___x_310_; 
v___x_310_ = lean_obj_once(&l_instToJsonMessageType___lam__0___closed__5, &l_instToJsonMessageType___lam__0___closed__5_once, _init_l_instToJsonMessageType___lam__0___closed__5);
v___y_295_ = v___x_310_;
goto v___jp_294_;
}
default: 
{
lean_object* v___x_311_; 
v___x_311_ = lean_obj_once(&l_instToJsonMessageType___lam__0___closed__7, &l_instToJsonMessageType___lam__0___closed__7_once, _init_l_instToJsonMessageType___lam__0___closed__7);
v___y_295_ = v___x_311_;
goto v___jp_294_;
}
}
v___jp_294_:
{
lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_296_, 0, v___x_293_);
lean_ctor_set(v___x_296_, 1, v___y_295_);
v___x_297_ = lean_box(0);
v___x_298_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_298_, 0, v___x_296_);
lean_ctor_set(v___x_298_, 1, v___x_297_);
v___x_299_ = ((lean_object*)(l_instFromJsonShowMessageParams_fromJson___closed__11));
lean_inc_ref(v_message_292_);
v___x_300_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_300_, 0, v_message_292_);
v___x_301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_301_, 0, v___x_299_);
lean_ctor_set(v___x_301_, 1, v___x_300_);
v___x_302_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_302_, 0, v___x_301_);
lean_ctor_set(v___x_302_, 1, v___x_297_);
v___x_303_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_303_, 0, v___x_302_);
lean_ctor_set(v___x_303_, 1, v___x_297_);
v___x_304_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_304_, 0, v___x_298_);
lean_ctor_set(v___x_304_, 1, v___x_303_);
v___x_305_ = ((lean_object*)(l_instToJsonShowMessageParams_toJson___closed__0));
v___x_306_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00instToJsonShowMessageParams_toJson_spec__0(v___x_304_, v___x_305_);
v___x_307_ = l_Lean_Json_mkObj(v___x_306_);
return v___x_307_;
}
}
}
LEAN_EXPORT lean_object* l_instToJsonShowMessageParams_toJson___boxed(lean_object* v_x_312_){
_start:
{
lean_object* v_res_313_; 
v_res_313_ = l_instToJsonShowMessageParams_toJson(v_x_312_);
lean_dec_ref(v_x_312_);
return v_res_313_;
}
}
static lean_object* _init_l_instFromJsonMessageActionItem_fromJson___closed__3(void){
_start:
{
uint8_t v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_320_ = 1;
v___x_321_ = ((lean_object*)(l_instFromJsonMessageActionItem_fromJson___closed__2));
v___x_322_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_321_, v___x_320_);
return v___x_322_;
}
}
static lean_object* _init_l_instFromJsonMessageActionItem_fromJson___closed__4(void){
_start:
{
lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_323_ = ((lean_object*)(l_instFromJsonShowMessageParams_fromJson___closed__4));
v___x_324_ = lean_obj_once(&l_instFromJsonMessageActionItem_fromJson___closed__3, &l_instFromJsonMessageActionItem_fromJson___closed__3_once, _init_l_instFromJsonMessageActionItem_fromJson___closed__3);
v___x_325_ = lean_string_append(v___x_324_, v___x_323_);
return v___x_325_;
}
}
static lean_object* _init_l_instFromJsonMessageActionItem_fromJson___closed__6(void){
_start:
{
uint8_t v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_328_ = 1;
v___x_329_ = ((lean_object*)(l_instFromJsonMessageActionItem_fromJson___closed__5));
v___x_330_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_329_, v___x_328_);
return v___x_330_;
}
}
static lean_object* _init_l_instFromJsonMessageActionItem_fromJson___closed__7(void){
_start:
{
lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_331_ = lean_obj_once(&l_instFromJsonMessageActionItem_fromJson___closed__6, &l_instFromJsonMessageActionItem_fromJson___closed__6_once, _init_l_instFromJsonMessageActionItem_fromJson___closed__6);
v___x_332_ = lean_obj_once(&l_instFromJsonMessageActionItem_fromJson___closed__4, &l_instFromJsonMessageActionItem_fromJson___closed__4_once, _init_l_instFromJsonMessageActionItem_fromJson___closed__4);
v___x_333_ = lean_string_append(v___x_332_, v___x_331_);
return v___x_333_;
}
}
static lean_object* _init_l_instFromJsonMessageActionItem_fromJson___closed__8(void){
_start:
{
lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_334_ = ((lean_object*)(l_instFromJsonShowMessageParams_fromJson___closed__9));
v___x_335_ = lean_obj_once(&l_instFromJsonMessageActionItem_fromJson___closed__7, &l_instFromJsonMessageActionItem_fromJson___closed__7_once, _init_l_instFromJsonMessageActionItem_fromJson___closed__7);
v___x_336_ = lean_string_append(v___x_335_, v___x_334_);
return v___x_336_;
}
}
LEAN_EXPORT lean_object* l_instFromJsonMessageActionItem_fromJson(lean_object* v_json_337_){
_start:
{
lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_338_ = ((lean_object*)(l_instFromJsonMessageActionItem_fromJson___closed__0));
v___x_339_ = l_Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageParams_fromJson_spec__1(v_json_337_, v___x_338_);
if (lean_obj_tag(v___x_339_) == 0)
{
lean_object* v_a_340_; lean_object* v___x_342_; uint8_t v_isShared_343_; uint8_t v_isSharedCheck_349_; 
v_a_340_ = lean_ctor_get(v___x_339_, 0);
v_isSharedCheck_349_ = !lean_is_exclusive(v___x_339_);
if (v_isSharedCheck_349_ == 0)
{
v___x_342_ = v___x_339_;
v_isShared_343_ = v_isSharedCheck_349_;
goto v_resetjp_341_;
}
else
{
lean_inc(v_a_340_);
lean_dec(v___x_339_);
v___x_342_ = lean_box(0);
v_isShared_343_ = v_isSharedCheck_349_;
goto v_resetjp_341_;
}
v_resetjp_341_:
{
lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_347_; 
v___x_344_ = lean_obj_once(&l_instFromJsonMessageActionItem_fromJson___closed__8, &l_instFromJsonMessageActionItem_fromJson___closed__8_once, _init_l_instFromJsonMessageActionItem_fromJson___closed__8);
v___x_345_ = lean_string_append(v___x_344_, v_a_340_);
lean_dec(v_a_340_);
if (v_isShared_343_ == 0)
{
lean_ctor_set(v___x_342_, 0, v___x_345_);
v___x_347_ = v___x_342_;
goto v_reusejp_346_;
}
else
{
lean_object* v_reuseFailAlloc_348_; 
v_reuseFailAlloc_348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_348_, 0, v___x_345_);
v___x_347_ = v_reuseFailAlloc_348_;
goto v_reusejp_346_;
}
v_reusejp_346_:
{
return v___x_347_;
}
}
}
else
{
if (lean_obj_tag(v___x_339_) == 0)
{
lean_object* v_a_350_; lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_357_; 
v_a_350_ = lean_ctor_get(v___x_339_, 0);
v_isSharedCheck_357_ = !lean_is_exclusive(v___x_339_);
if (v_isSharedCheck_357_ == 0)
{
v___x_352_ = v___x_339_;
v_isShared_353_ = v_isSharedCheck_357_;
goto v_resetjp_351_;
}
else
{
lean_inc(v_a_350_);
lean_dec(v___x_339_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_357_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
lean_object* v___x_355_; 
if (v_isShared_353_ == 0)
{
lean_ctor_set_tag(v___x_352_, 0);
v___x_355_ = v___x_352_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v_a_350_);
v___x_355_ = v_reuseFailAlloc_356_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
return v___x_355_;
}
}
}
else
{
lean_object* v_a_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_365_; 
v_a_358_ = lean_ctor_get(v___x_339_, 0);
v_isSharedCheck_365_ = !lean_is_exclusive(v___x_339_);
if (v_isSharedCheck_365_ == 0)
{
v___x_360_ = v___x_339_;
v_isShared_361_ = v_isSharedCheck_365_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_a_358_);
lean_dec(v___x_339_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_365_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
lean_object* v___x_363_; 
if (v_isShared_361_ == 0)
{
v___x_363_ = v___x_360_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v_a_358_);
v___x_363_ = v_reuseFailAlloc_364_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
return v___x_363_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_instToJsonMessageActionItem_toJson(lean_object* v_x_368_){
_start:
{
lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_369_ = ((lean_object*)(l_instFromJsonMessageActionItem_fromJson___closed__0));
v___x_370_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_370_, 0, v_x_368_);
v___x_371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_371_, 0, v___x_369_);
lean_ctor_set(v___x_371_, 1, v___x_370_);
v___x_372_ = lean_box(0);
v___x_373_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_373_, 0, v___x_371_);
lean_ctor_set(v___x_373_, 1, v___x_372_);
v___x_374_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_374_, 0, v___x_373_);
lean_ctor_set(v___x_374_, 1, v___x_372_);
v___x_375_ = ((lean_object*)(l_instToJsonShowMessageParams_toJson___closed__0));
v___x_376_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00instToJsonShowMessageParams_toJson_spec__0(v___x_374_, v___x_375_);
v___x_377_ = l_Lean_Json_mkObj(v___x_376_);
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0_spec__1_spec__2(size_t v_sz_380_, size_t v_i_381_, lean_object* v_bs_382_){
_start:
{
uint8_t v___x_383_; 
v___x_383_ = lean_usize_dec_lt(v_i_381_, v_sz_380_);
if (v___x_383_ == 0)
{
lean_object* v___x_384_; 
v___x_384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_384_, 0, v_bs_382_);
return v___x_384_;
}
else
{
lean_object* v_v_385_; lean_object* v___x_386_; 
v_v_385_ = lean_array_uget_borrowed(v_bs_382_, v_i_381_);
lean_inc(v_v_385_);
v___x_386_ = l_instFromJsonMessageActionItem_fromJson(v_v_385_);
if (lean_obj_tag(v___x_386_) == 0)
{
lean_object* v_a_387_; lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_394_; 
lean_dec_ref(v_bs_382_);
v_a_387_ = lean_ctor_get(v___x_386_, 0);
v_isSharedCheck_394_ = !lean_is_exclusive(v___x_386_);
if (v_isSharedCheck_394_ == 0)
{
v___x_389_ = v___x_386_;
v_isShared_390_ = v_isSharedCheck_394_;
goto v_resetjp_388_;
}
else
{
lean_inc(v_a_387_);
lean_dec(v___x_386_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_394_;
goto v_resetjp_388_;
}
v_resetjp_388_:
{
lean_object* v___x_392_; 
if (v_isShared_390_ == 0)
{
v___x_392_ = v___x_389_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_393_; 
v_reuseFailAlloc_393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v_a_387_);
v___x_392_ = v_reuseFailAlloc_393_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
return v___x_392_;
}
}
}
else
{
lean_object* v_a_395_; lean_object* v___x_396_; lean_object* v_bs_x27_397_; size_t v___x_398_; size_t v___x_399_; lean_object* v___x_400_; 
v_a_395_ = lean_ctor_get(v___x_386_, 0);
lean_inc(v_a_395_);
lean_dec_ref(v___x_386_);
v___x_396_ = lean_unsigned_to_nat(0u);
v_bs_x27_397_ = lean_array_uset(v_bs_382_, v_i_381_, v___x_396_);
v___x_398_ = ((size_t)1ULL);
v___x_399_ = lean_usize_add(v_i_381_, v___x_398_);
v___x_400_ = lean_array_uset(v_bs_x27_397_, v_i_381_, v_a_395_);
v_i_381_ = v___x_399_;
v_bs_382_ = v___x_400_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_sz_402_, lean_object* v_i_403_, lean_object* v_bs_404_){
_start:
{
size_t v_sz_boxed_405_; size_t v_i_boxed_406_; lean_object* v_res_407_; 
v_sz_boxed_405_ = lean_unbox_usize(v_sz_402_);
lean_dec(v_sz_402_);
v_i_boxed_406_ = lean_unbox_usize(v_i_403_);
lean_dec(v_i_403_);
v_res_407_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0_spec__1_spec__2(v_sz_boxed_405_, v_i_boxed_406_, v_bs_404_);
return v_res_407_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0_spec__1(lean_object* v_x_410_){
_start:
{
if (lean_obj_tag(v_x_410_) == 4)
{
lean_object* v_elems_411_; size_t v_sz_412_; size_t v___x_413_; lean_object* v___x_414_; 
v_elems_411_ = lean_ctor_get(v_x_410_, 0);
lean_inc_ref(v_elems_411_);
lean_dec_ref(v_x_410_);
v_sz_412_ = lean_array_size(v_elems_411_);
v___x_413_ = ((size_t)0ULL);
v___x_414_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0_spec__1_spec__2(v_sz_412_, v___x_413_, v_elems_411_);
return v___x_414_;
}
else
{
lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_415_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0_spec__1___closed__0));
v___x_416_ = lean_unsigned_to_nat(80u);
v___x_417_ = l_Lean_Json_pretty(v_x_410_, v___x_416_);
v___x_418_ = lean_string_append(v___x_415_, v___x_417_);
lean_dec_ref(v___x_417_);
v___x_419_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0_spec__1___closed__1));
v___x_420_ = lean_string_append(v___x_418_, v___x_419_);
v___x_421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_421_, 0, v___x_420_);
return v___x_421_;
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0(lean_object* v_x_424_){
_start:
{
if (lean_obj_tag(v_x_424_) == 0)
{
lean_object* v___x_425_; 
v___x_425_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0___closed__0));
return v___x_425_;
}
else
{
lean_object* v___x_426_; 
v___x_426_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0_spec__1(v_x_424_);
if (lean_obj_tag(v___x_426_) == 0)
{
lean_object* v_a_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_434_; 
v_a_427_ = lean_ctor_get(v___x_426_, 0);
v_isSharedCheck_434_ = !lean_is_exclusive(v___x_426_);
if (v_isSharedCheck_434_ == 0)
{
v___x_429_ = v___x_426_;
v_isShared_430_ = v_isSharedCheck_434_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_a_427_);
lean_dec(v___x_426_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_434_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
lean_object* v___x_432_; 
if (v_isShared_430_ == 0)
{
v___x_432_ = v___x_429_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v_a_427_);
v___x_432_ = v_reuseFailAlloc_433_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
return v___x_432_;
}
}
}
else
{
lean_object* v_a_435_; lean_object* v___x_437_; uint8_t v_isShared_438_; uint8_t v_isSharedCheck_443_; 
v_a_435_ = lean_ctor_get(v___x_426_, 0);
v_isSharedCheck_443_ = !lean_is_exclusive(v___x_426_);
if (v_isSharedCheck_443_ == 0)
{
v___x_437_ = v___x_426_;
v_isShared_438_ = v_isSharedCheck_443_;
goto v_resetjp_436_;
}
else
{
lean_inc(v_a_435_);
lean_dec(v___x_426_);
v___x_437_ = lean_box(0);
v_isShared_438_ = v_isSharedCheck_443_;
goto v_resetjp_436_;
}
v_resetjp_436_:
{
lean_object* v___x_439_; lean_object* v___x_441_; 
v___x_439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_439_, 0, v_a_435_);
if (v_isShared_438_ == 0)
{
lean_ctor_set(v___x_437_, 0, v___x_439_);
v___x_441_ = v___x_437_;
goto v_reusejp_440_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v___x_439_);
v___x_441_ = v_reuseFailAlloc_442_;
goto v_reusejp_440_;
}
v_reusejp_440_:
{
return v___x_441_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageRequestParams_fromJson_spec__0(lean_object* v_j_444_, lean_object* v_k_445_){
_start:
{
lean_object* v___x_446_; lean_object* v___x_447_; 
v___x_446_ = l_Lean_Json_getObjValD(v_j_444_, v_k_445_);
v___x_447_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageRequestParams_fromJson_spec__0_spec__0(v___x_446_);
return v___x_447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageRequestParams_fromJson_spec__0___boxed(lean_object* v_j_448_, lean_object* v_k_449_){
_start:
{
lean_object* v_res_450_; 
v_res_450_ = l_Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageRequestParams_fromJson_spec__0(v_j_448_, v_k_449_);
lean_dec_ref(v_k_449_);
return v_res_450_;
}
}
static lean_object* _init_l_instFromJsonShowMessageRequestParams_fromJson___closed__2(void){
_start:
{
uint8_t v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_454_ = 1;
v___x_455_ = ((lean_object*)(l_instFromJsonShowMessageRequestParams_fromJson___closed__1));
v___x_456_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_455_, v___x_454_);
return v___x_456_;
}
}
static lean_object* _init_l_instFromJsonShowMessageRequestParams_fromJson___closed__3(void){
_start:
{
lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_457_ = ((lean_object*)(l_instFromJsonShowMessageParams_fromJson___closed__4));
v___x_458_ = lean_obj_once(&l_instFromJsonShowMessageRequestParams_fromJson___closed__2, &l_instFromJsonShowMessageRequestParams_fromJson___closed__2_once, _init_l_instFromJsonShowMessageRequestParams_fromJson___closed__2);
v___x_459_ = lean_string_append(v___x_458_, v___x_457_);
return v___x_459_;
}
}
static lean_object* _init_l_instFromJsonShowMessageRequestParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_460_ = lean_obj_once(&l_instFromJsonShowMessageParams_fromJson___closed__7, &l_instFromJsonShowMessageParams_fromJson___closed__7_once, _init_l_instFromJsonShowMessageParams_fromJson___closed__7);
v___x_461_ = lean_obj_once(&l_instFromJsonShowMessageRequestParams_fromJson___closed__3, &l_instFromJsonShowMessageRequestParams_fromJson___closed__3_once, _init_l_instFromJsonShowMessageRequestParams_fromJson___closed__3);
v___x_462_ = lean_string_append(v___x_461_, v___x_460_);
return v___x_462_;
}
}
static lean_object* _init_l_instFromJsonShowMessageRequestParams_fromJson___closed__5(void){
_start:
{
lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_463_ = ((lean_object*)(l_instFromJsonShowMessageParams_fromJson___closed__9));
v___x_464_ = lean_obj_once(&l_instFromJsonShowMessageRequestParams_fromJson___closed__4, &l_instFromJsonShowMessageRequestParams_fromJson___closed__4_once, _init_l_instFromJsonShowMessageRequestParams_fromJson___closed__4);
v___x_465_ = lean_string_append(v___x_464_, v___x_463_);
return v___x_465_;
}
}
static lean_object* _init_l_instFromJsonShowMessageRequestParams_fromJson___closed__6(void){
_start:
{
lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; 
v___x_466_ = lean_obj_once(&l_instFromJsonShowMessageParams_fromJson___closed__13, &l_instFromJsonShowMessageParams_fromJson___closed__13_once, _init_l_instFromJsonShowMessageParams_fromJson___closed__13);
v___x_467_ = lean_obj_once(&l_instFromJsonShowMessageRequestParams_fromJson___closed__3, &l_instFromJsonShowMessageRequestParams_fromJson___closed__3_once, _init_l_instFromJsonShowMessageRequestParams_fromJson___closed__3);
v___x_468_ = lean_string_append(v___x_467_, v___x_466_);
return v___x_468_;
}
}
static lean_object* _init_l_instFromJsonShowMessageRequestParams_fromJson___closed__7(void){
_start:
{
lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_469_ = ((lean_object*)(l_instFromJsonShowMessageParams_fromJson___closed__9));
v___x_470_ = lean_obj_once(&l_instFromJsonShowMessageRequestParams_fromJson___closed__6, &l_instFromJsonShowMessageRequestParams_fromJson___closed__6_once, _init_l_instFromJsonShowMessageRequestParams_fromJson___closed__6);
v___x_471_ = lean_string_append(v___x_470_, v___x_469_);
return v___x_471_;
}
}
static lean_object* _init_l_instFromJsonShowMessageRequestParams_fromJson___closed__11(void){
_start:
{
uint8_t v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_476_ = 1;
v___x_477_ = ((lean_object*)(l_instFromJsonShowMessageRequestParams_fromJson___closed__10));
v___x_478_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_477_, v___x_476_);
return v___x_478_;
}
}
static lean_object* _init_l_instFromJsonShowMessageRequestParams_fromJson___closed__12(void){
_start:
{
lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_479_ = lean_obj_once(&l_instFromJsonShowMessageRequestParams_fromJson___closed__11, &l_instFromJsonShowMessageRequestParams_fromJson___closed__11_once, _init_l_instFromJsonShowMessageRequestParams_fromJson___closed__11);
v___x_480_ = lean_obj_once(&l_instFromJsonShowMessageRequestParams_fromJson___closed__3, &l_instFromJsonShowMessageRequestParams_fromJson___closed__3_once, _init_l_instFromJsonShowMessageRequestParams_fromJson___closed__3);
v___x_481_ = lean_string_append(v___x_480_, v___x_479_);
return v___x_481_;
}
}
static lean_object* _init_l_instFromJsonShowMessageRequestParams_fromJson___closed__13(void){
_start:
{
lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_482_ = ((lean_object*)(l_instFromJsonShowMessageParams_fromJson___closed__9));
v___x_483_ = lean_obj_once(&l_instFromJsonShowMessageRequestParams_fromJson___closed__12, &l_instFromJsonShowMessageRequestParams_fromJson___closed__12_once, _init_l_instFromJsonShowMessageRequestParams_fromJson___closed__12);
v___x_484_ = lean_string_append(v___x_483_, v___x_482_);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l_instFromJsonShowMessageRequestParams_fromJson(lean_object* v_json_485_){
_start:
{
lean_object* v___x_486_; lean_object* v___x_487_; 
v___x_486_ = ((lean_object*)(l_instFromJsonShowMessageParams_fromJson___closed__0));
lean_inc(v_json_485_);
v___x_487_ = l_Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageParams_fromJson_spec__0(v_json_485_, v___x_486_);
if (lean_obj_tag(v___x_487_) == 0)
{
lean_object* v_a_488_; lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_497_; 
lean_dec(v_json_485_);
v_a_488_ = lean_ctor_get(v___x_487_, 0);
v_isSharedCheck_497_ = !lean_is_exclusive(v___x_487_);
if (v_isSharedCheck_497_ == 0)
{
v___x_490_ = v___x_487_;
v_isShared_491_ = v_isSharedCheck_497_;
goto v_resetjp_489_;
}
else
{
lean_inc(v_a_488_);
lean_dec(v___x_487_);
v___x_490_ = lean_box(0);
v_isShared_491_ = v_isSharedCheck_497_;
goto v_resetjp_489_;
}
v_resetjp_489_:
{
lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_495_; 
v___x_492_ = lean_obj_once(&l_instFromJsonShowMessageRequestParams_fromJson___closed__5, &l_instFromJsonShowMessageRequestParams_fromJson___closed__5_once, _init_l_instFromJsonShowMessageRequestParams_fromJson___closed__5);
v___x_493_ = lean_string_append(v___x_492_, v_a_488_);
lean_dec(v_a_488_);
if (v_isShared_491_ == 0)
{
lean_ctor_set(v___x_490_, 0, v___x_493_);
v___x_495_ = v___x_490_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v___x_493_);
v___x_495_ = v_reuseFailAlloc_496_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
return v___x_495_;
}
}
}
else
{
if (lean_obj_tag(v___x_487_) == 0)
{
lean_object* v_a_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_505_; 
lean_dec(v_json_485_);
v_a_498_ = lean_ctor_get(v___x_487_, 0);
v_isSharedCheck_505_ = !lean_is_exclusive(v___x_487_);
if (v_isSharedCheck_505_ == 0)
{
v___x_500_ = v___x_487_;
v_isShared_501_ = v_isSharedCheck_505_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_a_498_);
lean_dec(v___x_487_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_505_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
lean_object* v___x_503_; 
if (v_isShared_501_ == 0)
{
lean_ctor_set_tag(v___x_500_, 0);
v___x_503_ = v___x_500_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v_a_498_);
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
lean_object* v_a_506_; lean_object* v___x_507_; lean_object* v___x_508_; 
v_a_506_ = lean_ctor_get(v___x_487_, 0);
lean_inc(v_a_506_);
lean_dec_ref(v___x_487_);
v___x_507_ = ((lean_object*)(l_instFromJsonShowMessageParams_fromJson___closed__11));
lean_inc(v_json_485_);
v___x_508_ = l_Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageParams_fromJson_spec__1(v_json_485_, v___x_507_);
if (lean_obj_tag(v___x_508_) == 0)
{
lean_object* v_a_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_518_; 
lean_dec(v_a_506_);
lean_dec(v_json_485_);
v_a_509_ = lean_ctor_get(v___x_508_, 0);
v_isSharedCheck_518_ = !lean_is_exclusive(v___x_508_);
if (v_isSharedCheck_518_ == 0)
{
v___x_511_ = v___x_508_;
v_isShared_512_ = v_isSharedCheck_518_;
goto v_resetjp_510_;
}
else
{
lean_inc(v_a_509_);
lean_dec(v___x_508_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_518_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_516_; 
v___x_513_ = lean_obj_once(&l_instFromJsonShowMessageRequestParams_fromJson___closed__7, &l_instFromJsonShowMessageRequestParams_fromJson___closed__7_once, _init_l_instFromJsonShowMessageRequestParams_fromJson___closed__7);
v___x_514_ = lean_string_append(v___x_513_, v_a_509_);
lean_dec(v_a_509_);
if (v_isShared_512_ == 0)
{
lean_ctor_set(v___x_511_, 0, v___x_514_);
v___x_516_ = v___x_511_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v___x_514_);
v___x_516_ = v_reuseFailAlloc_517_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
return v___x_516_;
}
}
}
else
{
if (lean_obj_tag(v___x_508_) == 0)
{
lean_object* v_a_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_526_; 
lean_dec(v_a_506_);
lean_dec(v_json_485_);
v_a_519_ = lean_ctor_get(v___x_508_, 0);
v_isSharedCheck_526_ = !lean_is_exclusive(v___x_508_);
if (v_isSharedCheck_526_ == 0)
{
v___x_521_ = v___x_508_;
v_isShared_522_ = v_isSharedCheck_526_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_a_519_);
lean_dec(v___x_508_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_526_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v___x_524_; 
if (v_isShared_522_ == 0)
{
lean_ctor_set_tag(v___x_521_, 0);
v___x_524_ = v___x_521_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v_a_519_);
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
lean_object* v_a_527_; lean_object* v___x_528_; lean_object* v___x_529_; 
v_a_527_ = lean_ctor_get(v___x_508_, 0);
lean_inc(v_a_527_);
lean_dec_ref(v___x_508_);
v___x_528_ = ((lean_object*)(l_instFromJsonShowMessageRequestParams_fromJson___closed__8));
v___x_529_ = l_Lean_Json_getObjValAs_x3f___at___00instFromJsonShowMessageRequestParams_fromJson_spec__0(v_json_485_, v___x_528_);
if (lean_obj_tag(v___x_529_) == 0)
{
lean_object* v_a_530_; lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_539_; 
lean_dec(v_a_527_);
lean_dec(v_a_506_);
v_a_530_ = lean_ctor_get(v___x_529_, 0);
v_isSharedCheck_539_ = !lean_is_exclusive(v___x_529_);
if (v_isSharedCheck_539_ == 0)
{
v___x_532_ = v___x_529_;
v_isShared_533_ = v_isSharedCheck_539_;
goto v_resetjp_531_;
}
else
{
lean_inc(v_a_530_);
lean_dec(v___x_529_);
v___x_532_ = lean_box(0);
v_isShared_533_ = v_isSharedCheck_539_;
goto v_resetjp_531_;
}
v_resetjp_531_:
{
lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_537_; 
v___x_534_ = lean_obj_once(&l_instFromJsonShowMessageRequestParams_fromJson___closed__13, &l_instFromJsonShowMessageRequestParams_fromJson___closed__13_once, _init_l_instFromJsonShowMessageRequestParams_fromJson___closed__13);
v___x_535_ = lean_string_append(v___x_534_, v_a_530_);
lean_dec(v_a_530_);
if (v_isShared_533_ == 0)
{
lean_ctor_set(v___x_532_, 0, v___x_535_);
v___x_537_ = v___x_532_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v___x_535_);
v___x_537_ = v_reuseFailAlloc_538_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
return v___x_537_;
}
}
}
else
{
if (lean_obj_tag(v___x_529_) == 0)
{
lean_object* v_a_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_547_; 
lean_dec(v_a_527_);
lean_dec(v_a_506_);
v_a_540_ = lean_ctor_get(v___x_529_, 0);
v_isSharedCheck_547_ = !lean_is_exclusive(v___x_529_);
if (v_isSharedCheck_547_ == 0)
{
v___x_542_ = v___x_529_;
v_isShared_543_ = v_isSharedCheck_547_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_a_540_);
lean_dec(v___x_529_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_547_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
lean_object* v___x_545_; 
if (v_isShared_543_ == 0)
{
lean_ctor_set_tag(v___x_542_, 0);
v___x_545_ = v___x_542_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v_a_540_);
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
lean_object* v_a_548_; lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_557_; 
v_a_548_ = lean_ctor_get(v___x_529_, 0);
v_isSharedCheck_557_ = !lean_is_exclusive(v___x_529_);
if (v_isSharedCheck_557_ == 0)
{
v___x_550_ = v___x_529_;
v_isShared_551_ = v_isSharedCheck_557_;
goto v_resetjp_549_;
}
else
{
lean_inc(v_a_548_);
lean_dec(v___x_529_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_557_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
lean_object* v___x_552_; uint8_t v___x_553_; lean_object* v___x_555_; 
v___x_552_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_552_, 0, v_a_527_);
lean_ctor_set(v___x_552_, 1, v_a_548_);
v___x_553_ = lean_unbox(v_a_506_);
lean_dec(v_a_506_);
lean_ctor_set_uint8(v___x_552_, sizeof(void*)*2, v___x_553_);
if (v_isShared_551_ == 0)
{
lean_ctor_set(v___x_550_, 0, v___x_552_);
v___x_555_ = v___x_550_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v___x_552_);
v___x_555_ = v_reuseFailAlloc_556_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
return v___x_555_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00instToJsonShowMessageRequestParams_toJson_spec__0_spec__0_spec__1(size_t v_sz_560_, size_t v_i_561_, lean_object* v_bs_562_){
_start:
{
uint8_t v___x_563_; 
v___x_563_ = lean_usize_dec_lt(v_i_561_, v_sz_560_);
if (v___x_563_ == 0)
{
return v_bs_562_;
}
else
{
lean_object* v_v_564_; lean_object* v___x_565_; lean_object* v_bs_x27_566_; lean_object* v___x_567_; size_t v___x_568_; size_t v___x_569_; lean_object* v___x_570_; 
v_v_564_ = lean_array_uget(v_bs_562_, v_i_561_);
v___x_565_ = lean_unsigned_to_nat(0u);
v_bs_x27_566_ = lean_array_uset(v_bs_562_, v_i_561_, v___x_565_);
v___x_567_ = l_instToJsonMessageActionItem_toJson(v_v_564_);
v___x_568_ = ((size_t)1ULL);
v___x_569_ = lean_usize_add(v_i_561_, v___x_568_);
v___x_570_ = lean_array_uset(v_bs_x27_566_, v_i_561_, v___x_567_);
v_i_561_ = v___x_569_;
v_bs_562_ = v___x_570_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00instToJsonShowMessageRequestParams_toJson_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_572_, lean_object* v_i_573_, lean_object* v_bs_574_){
_start:
{
size_t v_sz_boxed_575_; size_t v_i_boxed_576_; lean_object* v_res_577_; 
v_sz_boxed_575_ = lean_unbox_usize(v_sz_572_);
lean_dec(v_sz_572_);
v_i_boxed_576_ = lean_unbox_usize(v_i_573_);
lean_dec(v_i_573_);
v_res_577_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00instToJsonShowMessageRequestParams_toJson_spec__0_spec__0_spec__1(v_sz_boxed_575_, v_i_boxed_576_, v_bs_574_);
return v_res_577_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Json_opt___at___00instToJsonShowMessageRequestParams_toJson_spec__0_spec__0(lean_object* v_a_578_){
_start:
{
size_t v_sz_579_; size_t v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; 
v_sz_579_ = lean_array_size(v_a_578_);
v___x_580_ = ((size_t)0ULL);
v___x_581_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00instToJsonShowMessageRequestParams_toJson_spec__0_spec__0_spec__1(v_sz_579_, v___x_580_, v_a_578_);
v___x_582_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_582_, 0, v___x_581_);
return v___x_582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00instToJsonShowMessageRequestParams_toJson_spec__0(lean_object* v_k_583_, lean_object* v_x_584_){
_start:
{
if (lean_obj_tag(v_x_584_) == 0)
{
lean_object* v___x_585_; 
lean_dec_ref(v_k_583_);
v___x_585_ = lean_box(0);
return v___x_585_;
}
else
{
lean_object* v_val_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; 
v_val_586_ = lean_ctor_get(v_x_584_, 0);
lean_inc(v_val_586_);
lean_dec_ref(v_x_584_);
v___x_587_ = l_Array_toJson___at___00Lean_Json_opt___at___00instToJsonShowMessageRequestParams_toJson_spec__0_spec__0(v_val_586_);
v___x_588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_588_, 0, v_k_583_);
lean_ctor_set(v___x_588_, 1, v___x_587_);
v___x_589_ = lean_box(0);
v___x_590_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_590_, 0, v___x_588_);
lean_ctor_set(v___x_590_, 1, v___x_589_);
return v___x_590_;
}
}
}
LEAN_EXPORT lean_object* l_instToJsonShowMessageRequestParams_toJson(lean_object* v_x_591_){
_start:
{
uint8_t v_type_592_; lean_object* v_message_593_; lean_object* v_actions_x3f_594_; lean_object* v___x_595_; lean_object* v___y_597_; 
v_type_592_ = lean_ctor_get_uint8(v_x_591_, sizeof(void*)*2);
v_message_593_ = lean_ctor_get(v_x_591_, 0);
lean_inc_ref(v_message_593_);
v_actions_x3f_594_ = lean_ctor_get(v_x_591_, 1);
lean_inc(v_actions_x3f_594_);
lean_dec_ref(v_x_591_);
v___x_595_ = ((lean_object*)(l_instFromJsonShowMessageParams_fromJson___closed__0));
switch(v_type_592_)
{
case 0:
{
lean_object* v___x_613_; 
v___x_613_ = lean_obj_once(&l_instToJsonMessageType___lam__0___closed__1, &l_instToJsonMessageType___lam__0___closed__1_once, _init_l_instToJsonMessageType___lam__0___closed__1);
v___y_597_ = v___x_613_;
goto v___jp_596_;
}
case 1:
{
lean_object* v___x_614_; 
v___x_614_ = lean_obj_once(&l_instToJsonMessageType___lam__0___closed__3, &l_instToJsonMessageType___lam__0___closed__3_once, _init_l_instToJsonMessageType___lam__0___closed__3);
v___y_597_ = v___x_614_;
goto v___jp_596_;
}
case 2:
{
lean_object* v___x_615_; 
v___x_615_ = lean_obj_once(&l_instToJsonMessageType___lam__0___closed__5, &l_instToJsonMessageType___lam__0___closed__5_once, _init_l_instToJsonMessageType___lam__0___closed__5);
v___y_597_ = v___x_615_;
goto v___jp_596_;
}
default: 
{
lean_object* v___x_616_; 
v___x_616_ = lean_obj_once(&l_instToJsonMessageType___lam__0___closed__7, &l_instToJsonMessageType___lam__0___closed__7_once, _init_l_instToJsonMessageType___lam__0___closed__7);
v___y_597_ = v___x_616_;
goto v___jp_596_;
}
}
v___jp_596_:
{
lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_598_, 0, v___x_595_);
lean_ctor_set(v___x_598_, 1, v___y_597_);
v___x_599_ = lean_box(0);
v___x_600_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_600_, 0, v___x_598_);
lean_ctor_set(v___x_600_, 1, v___x_599_);
v___x_601_ = ((lean_object*)(l_instFromJsonShowMessageParams_fromJson___closed__11));
v___x_602_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_602_, 0, v_message_593_);
v___x_603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_603_, 0, v___x_601_);
lean_ctor_set(v___x_603_, 1, v___x_602_);
v___x_604_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_604_, 0, v___x_603_);
lean_ctor_set(v___x_604_, 1, v___x_599_);
v___x_605_ = ((lean_object*)(l_instFromJsonShowMessageRequestParams_fromJson___closed__8));
v___x_606_ = l_Lean_Json_opt___at___00instToJsonShowMessageRequestParams_toJson_spec__0(v___x_605_, v_actions_x3f_594_);
v___x_607_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_607_, 0, v___x_606_);
lean_ctor_set(v___x_607_, 1, v___x_599_);
v___x_608_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_608_, 0, v___x_604_);
lean_ctor_set(v___x_608_, 1, v___x_607_);
v___x_609_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_609_, 0, v___x_600_);
lean_ctor_set(v___x_609_, 1, v___x_608_);
v___x_610_ = ((lean_object*)(l_instToJsonShowMessageParams_toJson___closed__0));
v___x_611_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00instToJsonShowMessageParams_toJson_spec__0(v___x_609_, v___x_610_);
v___x_612_ = l_Lean_Json_mkObj(v___x_611_);
return v___x_612_;
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

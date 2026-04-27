// Lean compiler output
// Module: Lean.Data.Lsp.Client
// Imports: public import Lean.Data.Lsp.Basic
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
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
LEAN_EXPORT lean_object* l_Option_toJson___at___00Lean_Lsp_instToJsonRegistration_toJson_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Option_toJson___at___00Lean_Lsp_instToJsonRegistration_toJson_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonRegistration_toJson_spec__1(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instToJsonRegistration_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "id"};
static const lean_object* l_Lean_Lsp_instToJsonRegistration_toJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonRegistration_toJson___closed__0_value;
static const lean_string_object l_Lean_Lsp_instToJsonRegistration_toJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "method"};
static const lean_object* l_Lean_Lsp_instToJsonRegistration_toJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instToJsonRegistration_toJson___closed__1_value;
static const lean_string_object l_Lean_Lsp_instToJsonRegistration_toJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "registerOptions"};
static const lean_object* l_Lean_Lsp_instToJsonRegistration_toJson___closed__2 = (const lean_object*)&l_Lean_Lsp_instToJsonRegistration_toJson___closed__2_value;
static const lean_array_object l_Lean_Lsp_instToJsonRegistration_toJson___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Lsp_instToJsonRegistration_toJson___closed__3 = (const lean_object*)&l_Lean_Lsp_instToJsonRegistration_toJson___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRegistration_toJson(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRegistration_toJson___boxed(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonRegistration___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonRegistration_toJson___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonRegistration___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonRegistration___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonRegistration = (const lean_object*)&l_Lean_Lsp_instToJsonRegistration___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistration_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistration_fromJson_spec__0___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistration_fromJson_spec__1_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistration_fromJson_spec__1_spec__1___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistration_fromJson_spec__1_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistration_fromJson_spec__1_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistration_fromJson_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistration_fromJson_spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__0_value;
static const lean_string_object l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Lsp"};
static const lean_object* l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__1_value;
static const lean_string_object l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Registration"};
static const lean_object* l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__2 = (const lean_object*)&l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__2_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__3_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__3_value_aux_1),((lean_object*)&l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__2_value),LEAN_SCALAR_PTR_LITERAL(135, 10, 199, 89, 218, 159, 192, 129)}};
static const lean_object* l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__3 = (const lean_object*)&l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__3_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__4;
static const lean_string_object l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__5 = (const lean_object*)&l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__5_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__6;
static const lean_ctor_object l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instToJsonRegistration_toJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 78, 141, 85, 50, 255, 216, 83)}};
static const lean_object* l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__7 = (const lean_object*)&l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__7_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__8;
static lean_once_cell_t l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__9;
static const lean_string_object l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__10 = (const lean_object*)&l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__10_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__11;
static const lean_ctor_object l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instToJsonRegistration_toJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(50, 27, 204, 235, 104, 139, 101, 144)}};
static const lean_object* l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__12 = (const lean_object*)&l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__12_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__13;
static lean_once_cell_t l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__14;
static lean_once_cell_t l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__15;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonRegistration_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonRegistration___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonRegistration_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonRegistration___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonRegistration___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonRegistration = (const lean_object*)&l_Lean_Lsp_instFromJsonRegistration___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonRegistrationParams_toJson_spec__0_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonRegistrationParams_toJson_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Lsp_instToJsonRegistrationParams_toJson_spec__0(lean_object*);
static const lean_string_object l_Lean_Lsp_instToJsonRegistrationParams_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "registrations"};
static const lean_object* l_Lean_Lsp_instToJsonRegistrationParams_toJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonRegistrationParams_toJson___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRegistrationParams_toJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonRegistrationParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonRegistrationParams_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonRegistrationParams___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonRegistrationParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonRegistrationParams = (const lean_object*)&l_Lean_Lsp_instToJsonRegistrationParams___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistrationParams_fromJson_spec__0_spec__0_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistrationParams_fromJson_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistrationParams_fromJson_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "expected JSON array, got '"};
static const lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistrationParams_fromJson_spec__0_spec__0___closed__0 = (const lean_object*)&l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistrationParams_fromJson_spec__0_spec__0___closed__0_value;
static const lean_string_object l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistrationParams_fromJson_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistrationParams_fromJson_spec__0_spec__0___closed__1 = (const lean_object*)&l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistrationParams_fromJson_spec__0_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistrationParams_fromJson_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistrationParams_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistrationParams_fromJson_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "RegistrationParams"};
static const lean_object* l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__1_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__1_value_aux_1),((lean_object*)&l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(133, 115, 49, 52, 217, 222, 249, 239)}};
static const lean_object* l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__1_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__2;
static lean_once_cell_t l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__3;
static const lean_ctor_object l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instToJsonRegistrationParams_toJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(93, 246, 51, 33, 74, 200, 15, 48)}};
static const lean_object* l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__4 = (const lean_object*)&l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__4_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__5;
static lean_once_cell_t l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__6;
static lean_once_cell_t l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__7;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonRegistrationParams_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonRegistrationParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonRegistrationParams_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonRegistrationParams___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonRegistrationParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonRegistrationParams = (const lean_object*)&l_Lean_Lsp_instFromJsonRegistrationParams___closed__0_value;
LEAN_EXPORT lean_object* l_Option_toJson___at___00Lean_Lsp_instToJsonRegistration_toJson_spec__0(lean_object* v_x_1_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
else
{
lean_object* v_val_3_; 
v_val_3_ = lean_ctor_get(v_x_1_, 0);
lean_inc(v_val_3_);
return v_val_3_;
}
}
}
LEAN_EXPORT lean_object* l_Option_toJson___at___00Lean_Lsp_instToJsonRegistration_toJson_spec__0___boxed(lean_object* v_x_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = l_Option_toJson___at___00Lean_Lsp_instToJsonRegistration_toJson_spec__0(v_x_4_);
lean_dec(v_x_4_);
return v_res_5_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonRegistration_toJson_spec__1(lean_object* v_a_6_, lean_object* v_a_7_){
_start:
{
if (lean_obj_tag(v_a_6_) == 0)
{
lean_object* v___x_8_; 
v___x_8_ = lean_array_to_list(v_a_7_);
return v___x_8_;
}
else
{
lean_object* v_head_9_; lean_object* v_tail_10_; lean_object* v___x_11_; 
v_head_9_ = lean_ctor_get(v_a_6_, 0);
lean_inc(v_head_9_);
v_tail_10_ = lean_ctor_get(v_a_6_, 1);
lean_inc(v_tail_10_);
lean_dec_ref(v_a_6_);
v___x_11_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_7_, v_head_9_);
v_a_6_ = v_tail_10_;
v_a_7_ = v___x_11_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRegistration_toJson(lean_object* v_x_18_){
_start:
{
lean_object* v_id_19_; lean_object* v_method_20_; lean_object* v_registerOptions_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; 
v_id_19_ = lean_ctor_get(v_x_18_, 0);
v_method_20_ = lean_ctor_get(v_x_18_, 1);
v_registerOptions_21_ = lean_ctor_get(v_x_18_, 2);
v___x_22_ = ((lean_object*)(l_Lean_Lsp_instToJsonRegistration_toJson___closed__0));
lean_inc_ref(v_id_19_);
v___x_23_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_23_, 0, v_id_19_);
v___x_24_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_24_, 0, v___x_22_);
lean_ctor_set(v___x_24_, 1, v___x_23_);
v___x_25_ = lean_box(0);
v___x_26_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_26_, 0, v___x_24_);
lean_ctor_set(v___x_26_, 1, v___x_25_);
v___x_27_ = ((lean_object*)(l_Lean_Lsp_instToJsonRegistration_toJson___closed__1));
lean_inc_ref(v_method_20_);
v___x_28_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_28_, 0, v_method_20_);
v___x_29_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_29_, 0, v___x_27_);
lean_ctor_set(v___x_29_, 1, v___x_28_);
v___x_30_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_30_, 0, v___x_29_);
lean_ctor_set(v___x_30_, 1, v___x_25_);
v___x_31_ = ((lean_object*)(l_Lean_Lsp_instToJsonRegistration_toJson___closed__2));
v___x_32_ = l_Option_toJson___at___00Lean_Lsp_instToJsonRegistration_toJson_spec__0(v_registerOptions_21_);
v___x_33_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_33_, 0, v___x_31_);
lean_ctor_set(v___x_33_, 1, v___x_32_);
v___x_34_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_34_, 0, v___x_33_);
lean_ctor_set(v___x_34_, 1, v___x_25_);
v___x_35_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_35_, 0, v___x_34_);
lean_ctor_set(v___x_35_, 1, v___x_25_);
v___x_36_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_36_, 0, v___x_30_);
lean_ctor_set(v___x_36_, 1, v___x_35_);
v___x_37_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_37_, 0, v___x_26_);
lean_ctor_set(v___x_37_, 1, v___x_36_);
v___x_38_ = ((lean_object*)(l_Lean_Lsp_instToJsonRegistration_toJson___closed__3));
v___x_39_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonRegistration_toJson_spec__1(v___x_37_, v___x_38_);
v___x_40_ = l_Lean_Json_mkObj(v___x_39_);
lean_dec(v___x_39_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRegistration_toJson___boxed(lean_object* v_x_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = l_Lean_Lsp_instToJsonRegistration_toJson(v_x_41_);
lean_dec_ref(v_x_41_);
return v_res_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistration_fromJson_spec__0(lean_object* v_j_45_, lean_object* v_k_46_){
_start:
{
lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_47_ = l_Lean_Json_getObjValD(v_j_45_, v_k_46_);
v___x_48_ = l_Lean_Json_getStr_x3f(v___x_47_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistration_fromJson_spec__0___boxed(lean_object* v_j_49_, lean_object* v_k_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistration_fromJson_spec__0(v_j_49_, v_k_50_);
lean_dec_ref(v_k_50_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistration_fromJson_spec__1_spec__1(lean_object* v_x_54_){
_start:
{
if (lean_obj_tag(v_x_54_) == 0)
{
lean_object* v___x_55_; 
v___x_55_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistration_fromJson_spec__1_spec__1___closed__0));
return v___x_55_;
}
else
{
lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_56_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_56_, 0, v_x_54_);
v___x_57_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_57_, 0, v___x_56_);
return v___x_57_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistration_fromJson_spec__1(lean_object* v_j_58_, lean_object* v_k_59_){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_60_ = l_Lean_Json_getObjValD(v_j_58_, v_k_59_);
v___x_61_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistration_fromJson_spec__1_spec__1(v___x_60_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistration_fromJson_spec__1___boxed(lean_object* v_j_62_, lean_object* v_k_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistration_fromJson_spec__1(v_j_62_, v_k_63_);
lean_dec_ref(v_k_63_);
return v_res_64_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__4(void){
_start:
{
uint8_t v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_72_ = 1;
v___x_73_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__3));
v___x_74_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_73_, v___x_72_);
return v___x_74_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__6(void){
_start:
{
lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_76_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__5));
v___x_77_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__4, &l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__4);
v___x_78_ = lean_string_append(v___x_77_, v___x_76_);
return v___x_78_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__8(void){
_start:
{
uint8_t v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; 
v___x_81_ = 1;
v___x_82_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__7));
v___x_83_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_82_, v___x_81_);
return v___x_83_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__9(void){
_start:
{
lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_84_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__8, &l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__8);
v___x_85_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__6, &l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__6);
v___x_86_ = lean_string_append(v___x_85_, v___x_84_);
return v___x_86_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__11(void){
_start:
{
lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_88_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__10));
v___x_89_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__9, &l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__9);
v___x_90_ = lean_string_append(v___x_89_, v___x_88_);
return v___x_90_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__13(void){
_start:
{
uint8_t v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_93_ = 1;
v___x_94_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__12));
v___x_95_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_94_, v___x_93_);
return v___x_95_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__14(void){
_start:
{
lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_96_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__13, &l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__13);
v___x_97_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__6, &l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__6);
v___x_98_ = lean_string_append(v___x_97_, v___x_96_);
return v___x_98_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__15(void){
_start:
{
lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_99_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__10));
v___x_100_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__14, &l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__14_once, _init_l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__14);
v___x_101_ = lean_string_append(v___x_100_, v___x_99_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonRegistration_fromJson(lean_object* v_json_102_){
_start:
{
lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_103_ = ((lean_object*)(l_Lean_Lsp_instToJsonRegistration_toJson___closed__0));
lean_inc(v_json_102_);
v___x_104_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistration_fromJson_spec__0(v_json_102_, v___x_103_);
if (lean_obj_tag(v___x_104_) == 0)
{
lean_object* v_a_105_; lean_object* v___x_107_; uint8_t v_isShared_108_; uint8_t v_isSharedCheck_114_; 
lean_dec(v_json_102_);
v_a_105_ = lean_ctor_get(v___x_104_, 0);
v_isSharedCheck_114_ = !lean_is_exclusive(v___x_104_);
if (v_isSharedCheck_114_ == 0)
{
v___x_107_ = v___x_104_;
v_isShared_108_ = v_isSharedCheck_114_;
goto v_resetjp_106_;
}
else
{
lean_inc(v_a_105_);
lean_dec(v___x_104_);
v___x_107_ = lean_box(0);
v_isShared_108_ = v_isSharedCheck_114_;
goto v_resetjp_106_;
}
v_resetjp_106_:
{
lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_112_; 
v___x_109_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__11, &l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__11);
v___x_110_ = lean_string_append(v___x_109_, v_a_105_);
lean_dec(v_a_105_);
if (v_isShared_108_ == 0)
{
lean_ctor_set(v___x_107_, 0, v___x_110_);
v___x_112_ = v___x_107_;
goto v_reusejp_111_;
}
else
{
lean_object* v_reuseFailAlloc_113_; 
v_reuseFailAlloc_113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_113_, 0, v___x_110_);
v___x_112_ = v_reuseFailAlloc_113_;
goto v_reusejp_111_;
}
v_reusejp_111_:
{
return v___x_112_;
}
}
}
else
{
if (lean_obj_tag(v___x_104_) == 0)
{
lean_object* v_a_115_; lean_object* v___x_117_; uint8_t v_isShared_118_; uint8_t v_isSharedCheck_122_; 
lean_dec(v_json_102_);
v_a_115_ = lean_ctor_get(v___x_104_, 0);
v_isSharedCheck_122_ = !lean_is_exclusive(v___x_104_);
if (v_isSharedCheck_122_ == 0)
{
v___x_117_ = v___x_104_;
v_isShared_118_ = v_isSharedCheck_122_;
goto v_resetjp_116_;
}
else
{
lean_inc(v_a_115_);
lean_dec(v___x_104_);
v___x_117_ = lean_box(0);
v_isShared_118_ = v_isSharedCheck_122_;
goto v_resetjp_116_;
}
v_resetjp_116_:
{
lean_object* v___x_120_; 
if (v_isShared_118_ == 0)
{
lean_ctor_set_tag(v___x_117_, 0);
v___x_120_ = v___x_117_;
goto v_reusejp_119_;
}
else
{
lean_object* v_reuseFailAlloc_121_; 
v_reuseFailAlloc_121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_121_, 0, v_a_115_);
v___x_120_ = v_reuseFailAlloc_121_;
goto v_reusejp_119_;
}
v_reusejp_119_:
{
return v___x_120_;
}
}
}
else
{
lean_object* v_a_123_; lean_object* v___x_124_; lean_object* v___x_125_; 
v_a_123_ = lean_ctor_get(v___x_104_, 0);
lean_inc(v_a_123_);
lean_dec_ref(v___x_104_);
v___x_124_ = ((lean_object*)(l_Lean_Lsp_instToJsonRegistration_toJson___closed__1));
lean_inc(v_json_102_);
v___x_125_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistration_fromJson_spec__0(v_json_102_, v___x_124_);
if (lean_obj_tag(v___x_125_) == 0)
{
lean_object* v_a_126_; lean_object* v___x_128_; uint8_t v_isShared_129_; uint8_t v_isSharedCheck_135_; 
lean_dec(v_a_123_);
lean_dec(v_json_102_);
v_a_126_ = lean_ctor_get(v___x_125_, 0);
v_isSharedCheck_135_ = !lean_is_exclusive(v___x_125_);
if (v_isSharedCheck_135_ == 0)
{
v___x_128_ = v___x_125_;
v_isShared_129_ = v_isSharedCheck_135_;
goto v_resetjp_127_;
}
else
{
lean_inc(v_a_126_);
lean_dec(v___x_125_);
v___x_128_ = lean_box(0);
v_isShared_129_ = v_isSharedCheck_135_;
goto v_resetjp_127_;
}
v_resetjp_127_:
{
lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_133_; 
v___x_130_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__15, &l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__15_once, _init_l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__15);
v___x_131_ = lean_string_append(v___x_130_, v_a_126_);
lean_dec(v_a_126_);
if (v_isShared_129_ == 0)
{
lean_ctor_set(v___x_128_, 0, v___x_131_);
v___x_133_ = v___x_128_;
goto v_reusejp_132_;
}
else
{
lean_object* v_reuseFailAlloc_134_; 
v_reuseFailAlloc_134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_134_, 0, v___x_131_);
v___x_133_ = v_reuseFailAlloc_134_;
goto v_reusejp_132_;
}
v_reusejp_132_:
{
return v___x_133_;
}
}
}
else
{
if (lean_obj_tag(v___x_125_) == 0)
{
lean_object* v_a_136_; lean_object* v___x_138_; uint8_t v_isShared_139_; uint8_t v_isSharedCheck_143_; 
lean_dec(v_a_123_);
lean_dec(v_json_102_);
v_a_136_ = lean_ctor_get(v___x_125_, 0);
v_isSharedCheck_143_ = !lean_is_exclusive(v___x_125_);
if (v_isSharedCheck_143_ == 0)
{
v___x_138_ = v___x_125_;
v_isShared_139_ = v_isSharedCheck_143_;
goto v_resetjp_137_;
}
else
{
lean_inc(v_a_136_);
lean_dec(v___x_125_);
v___x_138_ = lean_box(0);
v_isShared_139_ = v_isSharedCheck_143_;
goto v_resetjp_137_;
}
v_resetjp_137_:
{
lean_object* v___x_141_; 
if (v_isShared_139_ == 0)
{
lean_ctor_set_tag(v___x_138_, 0);
v___x_141_ = v___x_138_;
goto v_reusejp_140_;
}
else
{
lean_object* v_reuseFailAlloc_142_; 
v_reuseFailAlloc_142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_142_, 0, v_a_136_);
v___x_141_ = v_reuseFailAlloc_142_;
goto v_reusejp_140_;
}
v_reusejp_140_:
{
return v___x_141_;
}
}
}
else
{
lean_object* v_a_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v_a_147_; lean_object* v___x_149_; uint8_t v_isShared_150_; uint8_t v_isSharedCheck_155_; 
v_a_144_ = lean_ctor_get(v___x_125_, 0);
lean_inc(v_a_144_);
lean_dec_ref(v___x_125_);
v___x_145_ = ((lean_object*)(l_Lean_Lsp_instToJsonRegistration_toJson___closed__2));
v___x_146_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistration_fromJson_spec__1(v_json_102_, v___x_145_);
v_a_147_ = lean_ctor_get(v___x_146_, 0);
v_isSharedCheck_155_ = !lean_is_exclusive(v___x_146_);
if (v_isSharedCheck_155_ == 0)
{
v___x_149_ = v___x_146_;
v_isShared_150_ = v_isSharedCheck_155_;
goto v_resetjp_148_;
}
else
{
lean_inc(v_a_147_);
lean_dec(v___x_146_);
v___x_149_ = lean_box(0);
v_isShared_150_ = v_isSharedCheck_155_;
goto v_resetjp_148_;
}
v_resetjp_148_:
{
lean_object* v___x_151_; lean_object* v___x_153_; 
v___x_151_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_151_, 0, v_a_123_);
lean_ctor_set(v___x_151_, 1, v_a_144_);
lean_ctor_set(v___x_151_, 2, v_a_147_);
if (v_isShared_150_ == 0)
{
lean_ctor_set(v___x_149_, 0, v___x_151_);
v___x_153_ = v___x_149_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v___x_151_);
v___x_153_ = v_reuseFailAlloc_154_;
goto v_reusejp_152_;
}
v_reusejp_152_:
{
return v___x_153_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonRegistrationParams_toJson_spec__0_spec__0(size_t v_sz_158_, size_t v_i_159_, lean_object* v_bs_160_){
_start:
{
uint8_t v___x_161_; 
v___x_161_ = lean_usize_dec_lt(v_i_159_, v_sz_158_);
if (v___x_161_ == 0)
{
return v_bs_160_;
}
else
{
lean_object* v_v_162_; lean_object* v___x_163_; lean_object* v_bs_x27_164_; lean_object* v___x_165_; size_t v___x_166_; size_t v___x_167_; lean_object* v___x_168_; 
v_v_162_ = lean_array_uget(v_bs_160_, v_i_159_);
v___x_163_ = lean_unsigned_to_nat(0u);
v_bs_x27_164_ = lean_array_uset(v_bs_160_, v_i_159_, v___x_163_);
v___x_165_ = l_Lean_Lsp_instToJsonRegistration_toJson(v_v_162_);
lean_dec(v_v_162_);
v___x_166_ = ((size_t)1ULL);
v___x_167_ = lean_usize_add(v_i_159_, v___x_166_);
v___x_168_ = lean_array_uset(v_bs_x27_164_, v_i_159_, v___x_165_);
v_i_159_ = v___x_167_;
v_bs_160_ = v___x_168_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonRegistrationParams_toJson_spec__0_spec__0___boxed(lean_object* v_sz_170_, lean_object* v_i_171_, lean_object* v_bs_172_){
_start:
{
size_t v_sz_boxed_173_; size_t v_i_boxed_174_; lean_object* v_res_175_; 
v_sz_boxed_173_ = lean_unbox_usize(v_sz_170_);
lean_dec(v_sz_170_);
v_i_boxed_174_ = lean_unbox_usize(v_i_171_);
lean_dec(v_i_171_);
v_res_175_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonRegistrationParams_toJson_spec__0_spec__0(v_sz_boxed_173_, v_i_boxed_174_, v_bs_172_);
return v_res_175_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Lsp_instToJsonRegistrationParams_toJson_spec__0(lean_object* v_a_176_){
_start:
{
size_t v_sz_177_; size_t v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
v_sz_177_ = lean_array_size(v_a_176_);
v___x_178_ = ((size_t)0ULL);
v___x_179_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonRegistrationParams_toJson_spec__0_spec__0(v_sz_177_, v___x_178_, v_a_176_);
v___x_180_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_180_, 0, v___x_179_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRegistrationParams_toJson(lean_object* v_x_182_){
_start:
{
lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_183_ = ((lean_object*)(l_Lean_Lsp_instToJsonRegistrationParams_toJson___closed__0));
v___x_184_ = l_Array_toJson___at___00Lean_Lsp_instToJsonRegistrationParams_toJson_spec__0(v_x_182_);
v___x_185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_185_, 0, v___x_183_);
lean_ctor_set(v___x_185_, 1, v___x_184_);
v___x_186_ = lean_box(0);
v___x_187_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_187_, 0, v___x_185_);
lean_ctor_set(v___x_187_, 1, v___x_186_);
v___x_188_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_188_, 0, v___x_187_);
lean_ctor_set(v___x_188_, 1, v___x_186_);
v___x_189_ = ((lean_object*)(l_Lean_Lsp_instToJsonRegistration_toJson___closed__3));
v___x_190_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonRegistration_toJson_spec__1(v___x_188_, v___x_189_);
v___x_191_ = l_Lean_Json_mkObj(v___x_190_);
lean_dec(v___x_190_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistrationParams_fromJson_spec__0_spec__0_spec__1(size_t v_sz_194_, size_t v_i_195_, lean_object* v_bs_196_){
_start:
{
uint8_t v___x_197_; 
v___x_197_ = lean_usize_dec_lt(v_i_195_, v_sz_194_);
if (v___x_197_ == 0)
{
lean_object* v___x_198_; 
v___x_198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_198_, 0, v_bs_196_);
return v___x_198_;
}
else
{
lean_object* v_v_199_; lean_object* v___x_200_; 
v_v_199_ = lean_array_uget_borrowed(v_bs_196_, v_i_195_);
lean_inc(v_v_199_);
v___x_200_ = l_Lean_Lsp_instFromJsonRegistration_fromJson(v_v_199_);
if (lean_obj_tag(v___x_200_) == 0)
{
lean_object* v_a_201_; lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_208_; 
lean_dec_ref(v_bs_196_);
v_a_201_ = lean_ctor_get(v___x_200_, 0);
v_isSharedCheck_208_ = !lean_is_exclusive(v___x_200_);
if (v_isSharedCheck_208_ == 0)
{
v___x_203_ = v___x_200_;
v_isShared_204_ = v_isSharedCheck_208_;
goto v_resetjp_202_;
}
else
{
lean_inc(v_a_201_);
lean_dec(v___x_200_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_208_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
lean_object* v___x_206_; 
if (v_isShared_204_ == 0)
{
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
lean_object* v_a_209_; lean_object* v___x_210_; lean_object* v_bs_x27_211_; size_t v___x_212_; size_t v___x_213_; lean_object* v___x_214_; 
v_a_209_ = lean_ctor_get(v___x_200_, 0);
lean_inc(v_a_209_);
lean_dec_ref(v___x_200_);
v___x_210_ = lean_unsigned_to_nat(0u);
v_bs_x27_211_ = lean_array_uset(v_bs_196_, v_i_195_, v___x_210_);
v___x_212_ = ((size_t)1ULL);
v___x_213_ = lean_usize_add(v_i_195_, v___x_212_);
v___x_214_ = lean_array_uset(v_bs_x27_211_, v_i_195_, v_a_209_);
v_i_195_ = v___x_213_;
v_bs_196_ = v___x_214_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistrationParams_fromJson_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_216_, lean_object* v_i_217_, lean_object* v_bs_218_){
_start:
{
size_t v_sz_boxed_219_; size_t v_i_boxed_220_; lean_object* v_res_221_; 
v_sz_boxed_219_ = lean_unbox_usize(v_sz_216_);
lean_dec(v_sz_216_);
v_i_boxed_220_ = lean_unbox_usize(v_i_217_);
lean_dec(v_i_217_);
v_res_221_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistrationParams_fromJson_spec__0_spec__0_spec__1(v_sz_boxed_219_, v_i_boxed_220_, v_bs_218_);
return v_res_221_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistrationParams_fromJson_spec__0_spec__0(lean_object* v_x_224_){
_start:
{
if (lean_obj_tag(v_x_224_) == 4)
{
lean_object* v_elems_225_; size_t v_sz_226_; size_t v___x_227_; lean_object* v___x_228_; 
v_elems_225_ = lean_ctor_get(v_x_224_, 0);
lean_inc_ref(v_elems_225_);
lean_dec_ref(v_x_224_);
v_sz_226_ = lean_array_size(v_elems_225_);
v___x_227_ = ((size_t)0ULL);
v___x_228_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistrationParams_fromJson_spec__0_spec__0_spec__1(v_sz_226_, v___x_227_, v_elems_225_);
return v___x_228_;
}
else
{
lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_229_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistrationParams_fromJson_spec__0_spec__0___closed__0));
v___x_230_ = lean_unsigned_to_nat(80u);
v___x_231_ = l_Lean_Json_pretty(v_x_224_, v___x_230_);
v___x_232_ = lean_string_append(v___x_229_, v___x_231_);
lean_dec_ref(v___x_231_);
v___x_233_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistrationParams_fromJson_spec__0_spec__0___closed__1));
v___x_234_ = lean_string_append(v___x_232_, v___x_233_);
v___x_235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_235_, 0, v___x_234_);
return v___x_235_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistrationParams_fromJson_spec__0(lean_object* v_j_236_, lean_object* v_k_237_){
_start:
{
lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_238_ = l_Lean_Json_getObjValD(v_j_236_, v_k_237_);
v___x_239_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistrationParams_fromJson_spec__0_spec__0(v___x_238_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistrationParams_fromJson_spec__0___boxed(lean_object* v_j_240_, lean_object* v_k_241_){
_start:
{
lean_object* v_res_242_; 
v_res_242_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistrationParams_fromJson_spec__0(v_j_240_, v_k_241_);
lean_dec_ref(v_k_241_);
return v_res_242_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__2(void){
_start:
{
uint8_t v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; 
v___x_248_ = 1;
v___x_249_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__1));
v___x_250_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_249_, v___x_248_);
return v___x_250_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__3(void){
_start:
{
lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_251_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__5));
v___x_252_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__2, &l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__2);
v___x_253_ = lean_string_append(v___x_252_, v___x_251_);
return v___x_253_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__5(void){
_start:
{
uint8_t v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_256_ = 1;
v___x_257_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__4));
v___x_258_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_257_, v___x_256_);
return v___x_258_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__6(void){
_start:
{
lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; 
v___x_259_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__5, &l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__5);
v___x_260_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__3);
v___x_261_ = lean_string_append(v___x_260_, v___x_259_);
return v___x_261_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__7(void){
_start:
{
lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_262_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__10));
v___x_263_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__6, &l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__6);
v___x_264_ = lean_string_append(v___x_263_, v___x_262_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonRegistrationParams_fromJson(lean_object* v_json_265_){
_start:
{
lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_266_ = ((lean_object*)(l_Lean_Lsp_instToJsonRegistrationParams_toJson___closed__0));
v___x_267_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistrationParams_fromJson_spec__0(v_json_265_, v___x_266_);
if (lean_obj_tag(v___x_267_) == 0)
{
lean_object* v_a_268_; lean_object* v___x_270_; uint8_t v_isShared_271_; uint8_t v_isSharedCheck_277_; 
v_a_268_ = lean_ctor_get(v___x_267_, 0);
v_isSharedCheck_277_ = !lean_is_exclusive(v___x_267_);
if (v_isSharedCheck_277_ == 0)
{
v___x_270_ = v___x_267_;
v_isShared_271_ = v_isSharedCheck_277_;
goto v_resetjp_269_;
}
else
{
lean_inc(v_a_268_);
lean_dec(v___x_267_);
v___x_270_ = lean_box(0);
v_isShared_271_ = v_isSharedCheck_277_;
goto v_resetjp_269_;
}
v_resetjp_269_:
{
lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_275_; 
v___x_272_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__7);
v___x_273_ = lean_string_append(v___x_272_, v_a_268_);
lean_dec(v_a_268_);
if (v_isShared_271_ == 0)
{
lean_ctor_set(v___x_270_, 0, v___x_273_);
v___x_275_ = v___x_270_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v___x_273_);
v___x_275_ = v_reuseFailAlloc_276_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
return v___x_275_;
}
}
}
else
{
if (lean_obj_tag(v___x_267_) == 0)
{
lean_object* v_a_278_; lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_285_; 
v_a_278_ = lean_ctor_get(v___x_267_, 0);
v_isSharedCheck_285_ = !lean_is_exclusive(v___x_267_);
if (v_isSharedCheck_285_ == 0)
{
v___x_280_ = v___x_267_;
v_isShared_281_ = v_isSharedCheck_285_;
goto v_resetjp_279_;
}
else
{
lean_inc(v_a_278_);
lean_dec(v___x_267_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_285_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
lean_object* v___x_283_; 
if (v_isShared_281_ == 0)
{
lean_ctor_set_tag(v___x_280_, 0);
v___x_283_ = v___x_280_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v_a_278_);
v___x_283_ = v_reuseFailAlloc_284_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
return v___x_283_;
}
}
}
else
{
lean_object* v_a_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_293_; 
v_a_286_ = lean_ctor_get(v___x_267_, 0);
v_isSharedCheck_293_ = !lean_is_exclusive(v___x_267_);
if (v_isSharedCheck_293_ == 0)
{
v___x_288_ = v___x_267_;
v_isShared_289_ = v_isSharedCheck_293_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_a_286_);
lean_dec(v___x_267_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_293_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v___x_291_; 
if (v_isShared_289_ == 0)
{
v___x_291_ = v___x_288_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v_a_286_);
v___x_291_ = v_reuseFailAlloc_292_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
return v___x_291_;
}
}
}
}
}
}
lean_object* runtime_initialize_Lean_Data_Lsp_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_Lsp_Client(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Data_Lsp_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Data_Lsp_Client(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Data_Lsp_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_Lsp_Client(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_Lsp_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Lsp_Client(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Data_Lsp_Client(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Data_Lsp_Client(builtin);
}
#ifdef __cplusplus
}
#endif

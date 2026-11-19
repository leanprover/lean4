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
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_toJson___at___00Lean_Lsp_instToJsonRegistration_toJson_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_toJson___at___00Lean_Lsp_instToJsonRegistration_toJson_spec__0___boxed(lean_object*);
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
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistration_fromJson_spec__1_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistration_fromJson_spec__1_spec__1___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistration_fromJson_spec__1_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistration_fromJson_spec__1_spec__1(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonRegistrationParams_toJson_spec__0_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonRegistrationParams_toJson_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonRegistrationParams_toJson_spec__0(lean_object*);
static const lean_string_object l_Lean_Lsp_instToJsonRegistrationParams_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "registrations"};
static const lean_object* l_Lean_Lsp_instToJsonRegistrationParams_toJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonRegistrationParams_toJson___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRegistrationParams_toJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonRegistrationParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonRegistrationParams_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonRegistrationParams___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonRegistrationParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonRegistrationParams = (const lean_object*)&l_Lean_Lsp_instToJsonRegistrationParams___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistrationParams_fromJson_spec__0_spec__0_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistrationParams_fromJson_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistrationParams_fromJson_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "expected JSON array, got '"};
static const lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistrationParams_fromJson_spec__0_spec__0___closed__0 = (const lean_object*)&l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistrationParams_fromJson_spec__0_spec__0___closed__0_value;
static const lean_string_object l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistrationParams_fromJson_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistrationParams_fromJson_spec__0_spec__0___closed__1 = (const lean_object*)&l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistrationParams_fromJson_spec__0_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistrationParams_fromJson_spec__0_spec__0(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Option_toJson___at___00Lean_Lsp_instToJsonRegistration_toJson_spec__0(lean_object* v_x_1_){
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
LEAN_EXPORT lean_object* l_Lean_Option_toJson___at___00Lean_Lsp_instToJsonRegistration_toJson_spec__0___boxed(lean_object* v_x_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = l_Lean_Option_toJson___at___00Lean_Lsp_instToJsonRegistration_toJson_spec__0(v_x_4_);
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
lean_dec_ref_known(v_a_6_, 2);
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
v___x_32_ = l_Lean_Option_toJson___at___00Lean_Lsp_instToJsonRegistration_toJson_spec__0(v_registerOptions_21_);
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
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistration_fromJson_spec__1_spec__1(lean_object* v_x_54_){
_start:
{
if (lean_obj_tag(v_x_54_) == 0)
{
lean_object* v___x_55_; 
v___x_55_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistration_fromJson_spec__1_spec__1___closed__0));
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
v___x_61_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistration_fromJson_spec__1_spec__1(v___x_60_);
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
lean_object* v_a_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
v_a_115_ = lean_ctor_get(v___x_104_, 0);
lean_inc(v_a_115_);
lean_dec_ref_known(v___x_104_, 1);
v___x_116_ = ((lean_object*)(l_Lean_Lsp_instToJsonRegistration_toJson___closed__1));
lean_inc(v_json_102_);
v___x_117_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistration_fromJson_spec__0(v_json_102_, v___x_116_);
if (lean_obj_tag(v___x_117_) == 0)
{
lean_object* v_a_118_; lean_object* v___x_120_; uint8_t v_isShared_121_; uint8_t v_isSharedCheck_127_; 
lean_dec(v_a_115_);
lean_dec(v_json_102_);
v_a_118_ = lean_ctor_get(v___x_117_, 0);
v_isSharedCheck_127_ = !lean_is_exclusive(v___x_117_);
if (v_isSharedCheck_127_ == 0)
{
v___x_120_ = v___x_117_;
v_isShared_121_ = v_isSharedCheck_127_;
goto v_resetjp_119_;
}
else
{
lean_inc(v_a_118_);
lean_dec(v___x_117_);
v___x_120_ = lean_box(0);
v_isShared_121_ = v_isSharedCheck_127_;
goto v_resetjp_119_;
}
v_resetjp_119_:
{
lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_125_; 
v___x_122_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__15, &l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__15_once, _init_l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__15);
v___x_123_ = lean_string_append(v___x_122_, v_a_118_);
lean_dec(v_a_118_);
if (v_isShared_121_ == 0)
{
lean_ctor_set(v___x_120_, 0, v___x_123_);
v___x_125_ = v___x_120_;
goto v_reusejp_124_;
}
else
{
lean_object* v_reuseFailAlloc_126_; 
v_reuseFailAlloc_126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_126_, 0, v___x_123_);
v___x_125_ = v_reuseFailAlloc_126_;
goto v_reusejp_124_;
}
v_reusejp_124_:
{
return v___x_125_;
}
}
}
else
{
lean_object* v_a_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v_a_131_; lean_object* v___x_133_; uint8_t v_isShared_134_; uint8_t v_isSharedCheck_139_; 
v_a_128_ = lean_ctor_get(v___x_117_, 0);
lean_inc(v_a_128_);
lean_dec_ref_known(v___x_117_, 1);
v___x_129_ = ((lean_object*)(l_Lean_Lsp_instToJsonRegistration_toJson___closed__2));
v___x_130_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistration_fromJson_spec__1(v_json_102_, v___x_129_);
v_a_131_ = lean_ctor_get(v___x_130_, 0);
v_isSharedCheck_139_ = !lean_is_exclusive(v___x_130_);
if (v_isSharedCheck_139_ == 0)
{
v___x_133_ = v___x_130_;
v_isShared_134_ = v_isSharedCheck_139_;
goto v_resetjp_132_;
}
else
{
lean_inc(v_a_131_);
lean_dec(v___x_130_);
v___x_133_ = lean_box(0);
v_isShared_134_ = v_isSharedCheck_139_;
goto v_resetjp_132_;
}
v_resetjp_132_:
{
lean_object* v___x_135_; lean_object* v___x_137_; 
v___x_135_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_135_, 0, v_a_115_);
lean_ctor_set(v___x_135_, 1, v_a_128_);
lean_ctor_set(v___x_135_, 2, v_a_131_);
if (v_isShared_134_ == 0)
{
lean_ctor_set(v___x_133_, 0, v___x_135_);
v___x_137_ = v___x_133_;
goto v_reusejp_136_;
}
else
{
lean_object* v_reuseFailAlloc_138_; 
v_reuseFailAlloc_138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_138_, 0, v___x_135_);
v___x_137_ = v_reuseFailAlloc_138_;
goto v_reusejp_136_;
}
v_reusejp_136_:
{
return v___x_137_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonRegistrationParams_toJson_spec__0_spec__0(size_t v_sz_142_, size_t v_i_143_, lean_object* v_bs_144_){
_start:
{
uint8_t v___x_145_; 
v___x_145_ = lean_usize_dec_lt(v_i_143_, v_sz_142_);
if (v___x_145_ == 0)
{
return v_bs_144_;
}
else
{
lean_object* v_v_146_; lean_object* v___x_147_; lean_object* v_bs_x27_148_; lean_object* v___x_149_; size_t v___x_150_; size_t v___x_151_; lean_object* v___x_152_; 
v_v_146_ = lean_array_uget(v_bs_144_, v_i_143_);
v___x_147_ = lean_unsigned_to_nat(0u);
v_bs_x27_148_ = lean_array_uset(v_bs_144_, v_i_143_, v___x_147_);
v___x_149_ = l_Lean_Lsp_instToJsonRegistration_toJson(v_v_146_);
lean_dec(v_v_146_);
v___x_150_ = ((size_t)1ULL);
v___x_151_ = lean_usize_add(v_i_143_, v___x_150_);
v___x_152_ = lean_array_uset(v_bs_x27_148_, v_i_143_, v___x_149_);
v_i_143_ = v___x_151_;
v_bs_144_ = v___x_152_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonRegistrationParams_toJson_spec__0_spec__0___boxed(lean_object* v_sz_154_, lean_object* v_i_155_, lean_object* v_bs_156_){
_start:
{
size_t v_sz_boxed_157_; size_t v_i_boxed_158_; lean_object* v_res_159_; 
v_sz_boxed_157_ = lean_unbox_usize(v_sz_154_);
lean_dec(v_sz_154_);
v_i_boxed_158_ = lean_unbox_usize(v_i_155_);
lean_dec(v_i_155_);
v_res_159_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonRegistrationParams_toJson_spec__0_spec__0(v_sz_boxed_157_, v_i_boxed_158_, v_bs_156_);
return v_res_159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonRegistrationParams_toJson_spec__0(lean_object* v_a_160_){
_start:
{
size_t v_sz_161_; size_t v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
v_sz_161_ = lean_array_size(v_a_160_);
v___x_162_ = ((size_t)0ULL);
v___x_163_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonRegistrationParams_toJson_spec__0_spec__0(v_sz_161_, v___x_162_, v_a_160_);
v___x_164_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_164_, 0, v___x_163_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRegistrationParams_toJson(lean_object* v_x_166_){
_start:
{
lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_167_ = ((lean_object*)(l_Lean_Lsp_instToJsonRegistrationParams_toJson___closed__0));
v___x_168_ = l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonRegistrationParams_toJson_spec__0(v_x_166_);
v___x_169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_169_, 0, v___x_167_);
lean_ctor_set(v___x_169_, 1, v___x_168_);
v___x_170_ = lean_box(0);
v___x_171_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_171_, 0, v___x_169_);
lean_ctor_set(v___x_171_, 1, v___x_170_);
v___x_172_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_172_, 0, v___x_171_);
lean_ctor_set(v___x_172_, 1, v___x_170_);
v___x_173_ = ((lean_object*)(l_Lean_Lsp_instToJsonRegistration_toJson___closed__3));
v___x_174_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonRegistration_toJson_spec__1(v___x_172_, v___x_173_);
v___x_175_ = l_Lean_Json_mkObj(v___x_174_);
lean_dec(v___x_174_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistrationParams_fromJson_spec__0_spec__0_spec__1(size_t v_sz_178_, size_t v_i_179_, lean_object* v_bs_180_){
_start:
{
uint8_t v___x_181_; 
v___x_181_ = lean_usize_dec_lt(v_i_179_, v_sz_178_);
if (v___x_181_ == 0)
{
lean_object* v___x_182_; 
v___x_182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_182_, 0, v_bs_180_);
return v___x_182_;
}
else
{
lean_object* v_v_183_; lean_object* v___x_184_; 
v_v_183_ = lean_array_uget_borrowed(v_bs_180_, v_i_179_);
lean_inc(v_v_183_);
v___x_184_ = l_Lean_Lsp_instFromJsonRegistration_fromJson(v_v_183_);
if (lean_obj_tag(v___x_184_) == 0)
{
lean_object* v_a_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_192_; 
lean_dec_ref(v_bs_180_);
v_a_185_ = lean_ctor_get(v___x_184_, 0);
v_isSharedCheck_192_ = !lean_is_exclusive(v___x_184_);
if (v_isSharedCheck_192_ == 0)
{
v___x_187_ = v___x_184_;
v_isShared_188_ = v_isSharedCheck_192_;
goto v_resetjp_186_;
}
else
{
lean_inc(v_a_185_);
lean_dec(v___x_184_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_192_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
lean_object* v___x_190_; 
if (v_isShared_188_ == 0)
{
v___x_190_ = v___x_187_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v_a_185_);
v___x_190_ = v_reuseFailAlloc_191_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
return v___x_190_;
}
}
}
else
{
lean_object* v_a_193_; lean_object* v___x_194_; lean_object* v_bs_x27_195_; size_t v___x_196_; size_t v___x_197_; lean_object* v___x_198_; 
v_a_193_ = lean_ctor_get(v___x_184_, 0);
lean_inc(v_a_193_);
lean_dec_ref_known(v___x_184_, 1);
v___x_194_ = lean_unsigned_to_nat(0u);
v_bs_x27_195_ = lean_array_uset(v_bs_180_, v_i_179_, v___x_194_);
v___x_196_ = ((size_t)1ULL);
v___x_197_ = lean_usize_add(v_i_179_, v___x_196_);
v___x_198_ = lean_array_uset(v_bs_x27_195_, v_i_179_, v_a_193_);
v_i_179_ = v___x_197_;
v_bs_180_ = v___x_198_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistrationParams_fromJson_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_200_, lean_object* v_i_201_, lean_object* v_bs_202_){
_start:
{
size_t v_sz_boxed_203_; size_t v_i_boxed_204_; lean_object* v_res_205_; 
v_sz_boxed_203_ = lean_unbox_usize(v_sz_200_);
lean_dec(v_sz_200_);
v_i_boxed_204_ = lean_unbox_usize(v_i_201_);
lean_dec(v_i_201_);
v_res_205_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistrationParams_fromJson_spec__0_spec__0_spec__1(v_sz_boxed_203_, v_i_boxed_204_, v_bs_202_);
return v_res_205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistrationParams_fromJson_spec__0_spec__0(lean_object* v_x_208_){
_start:
{
if (lean_obj_tag(v_x_208_) == 4)
{
lean_object* v_elems_209_; size_t v_sz_210_; size_t v___x_211_; lean_object* v___x_212_; 
v_elems_209_ = lean_ctor_get(v_x_208_, 0);
lean_inc_ref(v_elems_209_);
lean_dec_ref_known(v_x_208_, 1);
v_sz_210_ = lean_array_size(v_elems_209_);
v___x_211_ = ((size_t)0ULL);
v___x_212_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistrationParams_fromJson_spec__0_spec__0_spec__1(v_sz_210_, v___x_211_, v_elems_209_);
return v___x_212_;
}
else
{
lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; 
v___x_213_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistrationParams_fromJson_spec__0_spec__0___closed__0));
v___x_214_ = lean_unsigned_to_nat(80u);
v___x_215_ = l_Lean_Json_pretty(v_x_208_, v___x_214_);
v___x_216_ = lean_string_append(v___x_213_, v___x_215_);
lean_dec_ref(v___x_215_);
v___x_217_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistrationParams_fromJson_spec__0_spec__0___closed__1));
v___x_218_ = lean_string_append(v___x_216_, v___x_217_);
v___x_219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_219_, 0, v___x_218_);
return v___x_219_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistrationParams_fromJson_spec__0(lean_object* v_j_220_, lean_object* v_k_221_){
_start:
{
lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_222_ = l_Lean_Json_getObjValD(v_j_220_, v_k_221_);
v___x_223_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistrationParams_fromJson_spec__0_spec__0(v___x_222_);
return v___x_223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistrationParams_fromJson_spec__0___boxed(lean_object* v_j_224_, lean_object* v_k_225_){
_start:
{
lean_object* v_res_226_; 
v_res_226_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistrationParams_fromJson_spec__0(v_j_224_, v_k_225_);
lean_dec_ref(v_k_225_);
return v_res_226_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__2(void){
_start:
{
uint8_t v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_232_ = 1;
v___x_233_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__1));
v___x_234_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_233_, v___x_232_);
return v___x_234_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__3(void){
_start:
{
lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_235_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__5));
v___x_236_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__2, &l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__2);
v___x_237_ = lean_string_append(v___x_236_, v___x_235_);
return v___x_237_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__5(void){
_start:
{
uint8_t v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; 
v___x_240_ = 1;
v___x_241_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__4));
v___x_242_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_241_, v___x_240_);
return v___x_242_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__6(void){
_start:
{
lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; 
v___x_243_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__5, &l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__5);
v___x_244_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__3);
v___x_245_ = lean_string_append(v___x_244_, v___x_243_);
return v___x_245_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__7(void){
_start:
{
lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_246_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRegistration_fromJson___closed__10));
v___x_247_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__6, &l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__6);
v___x_248_ = lean_string_append(v___x_247_, v___x_246_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonRegistrationParams_fromJson(lean_object* v_json_249_){
_start:
{
lean_object* v___x_250_; lean_object* v___x_251_; 
v___x_250_ = ((lean_object*)(l_Lean_Lsp_instToJsonRegistrationParams_toJson___closed__0));
v___x_251_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRegistrationParams_fromJson_spec__0(v_json_249_, v___x_250_);
if (lean_obj_tag(v___x_251_) == 0)
{
lean_object* v_a_252_; lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_261_; 
v_a_252_ = lean_ctor_get(v___x_251_, 0);
v_isSharedCheck_261_ = !lean_is_exclusive(v___x_251_);
if (v_isSharedCheck_261_ == 0)
{
v___x_254_ = v___x_251_;
v_isShared_255_ = v_isSharedCheck_261_;
goto v_resetjp_253_;
}
else
{
lean_inc(v_a_252_);
lean_dec(v___x_251_);
v___x_254_ = lean_box(0);
v_isShared_255_ = v_isSharedCheck_261_;
goto v_resetjp_253_;
}
v_resetjp_253_:
{
lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_259_; 
v___x_256_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonRegistrationParams_fromJson___closed__7);
v___x_257_ = lean_string_append(v___x_256_, v_a_252_);
lean_dec(v_a_252_);
if (v_isShared_255_ == 0)
{
lean_ctor_set(v___x_254_, 0, v___x_257_);
v___x_259_ = v___x_254_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v___x_257_);
v___x_259_ = v_reuseFailAlloc_260_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
return v___x_259_;
}
}
}
else
{
lean_object* v_a_262_; lean_object* v___x_264_; uint8_t v_isShared_265_; uint8_t v_isSharedCheck_269_; 
v_a_262_ = lean_ctor_get(v___x_251_, 0);
v_isSharedCheck_269_ = !lean_is_exclusive(v___x_251_);
if (v_isSharedCheck_269_ == 0)
{
v___x_264_ = v___x_251_;
v_isShared_265_ = v_isSharedCheck_269_;
goto v_resetjp_263_;
}
else
{
lean_inc(v_a_262_);
lean_dec(v___x_251_);
v___x_264_ = lean_box(0);
v_isShared_265_ = v_isSharedCheck_269_;
goto v_resetjp_263_;
}
v_resetjp_263_:
{
lean_object* v___x_267_; 
if (v_isShared_265_ == 0)
{
v___x_267_ = v___x_264_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v_a_262_);
v___x_267_ = v_reuseFailAlloc_268_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
return v___x_267_;
}
}
}
}
}
lean_object* runtime_initialize_Lean_Data_Lsp_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_Lsp_Client(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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

// Lean compiler output
// Module: Lean.ErrorExplanation
// Imports: public import Lean.Message public import Lean.EnvExtension public import Lean.DocString.Links meta import Lean.Message
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
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg(lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
lean_object* l_Lean_instFromJsonMessageSeverity_fromJson(lean_object*);
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
lean_object* l_Lean_MessageSeverity_toString(uint8_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_foldl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_instToJsonMessageSeverity_toJson(uint8_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__1___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__2_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__2_spec__2___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__2_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__2_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__2___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "summary"};
static const lean_object* l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__0 = (const lean_object*)&l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__0_value;
static const lean_string_object l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__1 = (const lean_object*)&l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__1_value;
static const lean_string_object l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "ErrorExplanation"};
static const lean_object* l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__2 = (const lean_object*)&l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__2_value;
static const lean_string_object l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Metadata"};
static const lean_object* l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__3 = (const lean_object*)&l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__3_value;
static const lean_ctor_object l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__4_value_aux_0),((lean_object*)&l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__2_value),LEAN_SCALAR_PTR_LITERAL(228, 124, 72, 60, 38, 86, 32, 253)}};
static const lean_ctor_object l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__4_value_aux_1),((lean_object*)&l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__3_value),LEAN_SCALAR_PTR_LITERAL(228, 194, 107, 149, 38, 116, 86, 230)}};
static const lean_object* l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__4 = (const lean_object*)&l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__4_value;
static lean_once_cell_t l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__5;
static const lean_string_object l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__6 = (const lean_object*)&l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__6_value;
static lean_once_cell_t l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__7;
static const lean_ctor_object l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(118, 113, 57, 223, 239, 104, 46, 80)}};
static const lean_object* l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__8 = (const lean_object*)&l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__8_value;
static lean_once_cell_t l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__9;
static lean_once_cell_t l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__10;
static const lean_string_object l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__11 = (const lean_object*)&l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__11_value;
static lean_once_cell_t l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__12;
static const lean_string_object l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "sinceVersion"};
static const lean_object* l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__13 = (const lean_object*)&l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__13_value;
static const lean_ctor_object l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__13_value),LEAN_SCALAR_PTR_LITERAL(22, 91, 83, 204, 74, 158, 30, 114)}};
static const lean_object* l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__14 = (const lean_object*)&l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__14_value;
static lean_once_cell_t l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__15;
static lean_once_cell_t l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__16;
static lean_once_cell_t l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__17;
static const lean_string_object l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "severity"};
static const lean_object* l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__18 = (const lean_object*)&l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__18_value;
static const lean_ctor_object l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__18_value),LEAN_SCALAR_PTR_LITERAL(220, 87, 21, 107, 78, 188, 130, 35)}};
static const lean_object* l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__19 = (const lean_object*)&l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__19_value;
static lean_once_cell_t l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__20;
static lean_once_cell_t l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__21;
static lean_once_cell_t l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__22;
static const lean_string_object l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "removedVersion"};
static const lean_object* l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__23 = (const lean_object*)&l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__23_value;
static const lean_string_object l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "removedVersion\?"};
static const lean_object* l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__24 = (const lean_object*)&l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__24_value;
static const lean_ctor_object l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__24_value),LEAN_SCALAR_PTR_LITERAL(189, 225, 119, 213, 100, 129, 15, 193)}};
static const lean_object* l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__25 = (const lean_object*)&l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__25_value;
static lean_once_cell_t l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__26;
static lean_once_cell_t l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__27;
static lean_once_cell_t l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__28;
LEAN_EXPORT lean_object* l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson(lean_object*);
static const lean_closure_object l_Lean_ErrorExplanation_instFromJsonMetadata___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ErrorExplanation_instFromJsonMetadata___closed__0 = (const lean_object*)&l_Lean_ErrorExplanation_instFromJsonMetadata___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_ErrorExplanation_instFromJsonMetadata = (const lean_object*)&l_Lean_ErrorExplanation_instFromJsonMetadata___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_ErrorExplanation_instToJsonMetadata_toJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_ErrorExplanation_instToJsonMetadata_toJson_spec__1(lean_object*, lean_object*);
static const lean_array_object l_Lean_ErrorExplanation_instToJsonMetadata_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_ErrorExplanation_instToJsonMetadata_toJson___closed__0 = (const lean_object*)&l_Lean_ErrorExplanation_instToJsonMetadata_toJson___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_ErrorExplanation_instToJsonMetadata_toJson(lean_object*);
static const lean_closure_object l_Lean_ErrorExplanation_instToJsonMetadata___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_ErrorExplanation_instToJsonMetadata_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ErrorExplanation_instToJsonMetadata___closed__0 = (const lean_object*)&l_Lean_ErrorExplanation_instToJsonMetadata___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_ErrorExplanation_instToJsonMetadata = (const lean_object*)&l_Lean_ErrorExplanation_instToJsonMetadata___closed__0_value;
static const lean_string_object l_Lean_ErrorExplanation_summaryWithSeverity___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Lean_ErrorExplanation_summaryWithSeverity___closed__0 = (const lean_object*)&l_Lean_ErrorExplanation_summaryWithSeverity___closed__0_value;
static const lean_string_object l_Lean_ErrorExplanation_summaryWithSeverity___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ") "};
static const lean_object* l_Lean_ErrorExplanation_summaryWithSeverity___closed__1 = (const lean_object*)&l_Lean_ErrorExplanation_summaryWithSeverity___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_ErrorExplanation_summaryWithSeverity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ErrorExplanation_summaryWithSeverity___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ErrorExplanation_0__Lean_initFn___lam__0_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ErrorExplanation_0__Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ErrorExplanation_0__Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ErrorExplanation_0__Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ErrorExplanation_0__Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ErrorExplanation_0__Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ErrorExplanation_0__Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ErrorExplanation_0__Lean_initFn___lam__1_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ErrorExplanation_0__Lean_initFn___lam__1_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ErrorExplanation_0__Lean_initFn___lam__2_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_(lean_object*);
static const lean_closure_object l___private_Lean_ErrorExplanation_0__Lean_initFn___closed__0_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_ErrorExplanation_0__Lean_initFn___lam__0_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ErrorExplanation_0__Lean_initFn___closed__0_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ErrorExplanation_0__Lean_initFn___closed__0_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_ErrorExplanation_0__Lean_initFn___closed__1_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_ErrorExplanation_0__Lean_initFn___lam__1_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ErrorExplanation_0__Lean_initFn___closed__1_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ErrorExplanation_0__Lean_initFn___closed__1_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_ErrorExplanation_0__Lean_initFn___closed__2_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_ErrorExplanation_0__Lean_initFn___lam__2_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ErrorExplanation_0__Lean_initFn___closed__2_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ErrorExplanation_0__Lean_initFn___closed__2_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_ErrorExplanation_0__Lean_initFn___closed__3_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "errorExplanationExt"};
static const lean_object* l___private_Lean_ErrorExplanation_0__Lean_initFn___closed__3_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ErrorExplanation_0__Lean_initFn___closed__3_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ErrorExplanation_0__Lean_initFn___closed__4_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_ErrorExplanation_0__Lean_initFn___closed__4_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ErrorExplanation_0__Lean_initFn___closed__4_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_ErrorExplanation_0__Lean_initFn___closed__3_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(132, 33, 219, 37, 109, 235, 253, 255)}};
static const lean_object* l___private_Lean_ErrorExplanation_0__Lean_initFn___closed__4_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ErrorExplanation_0__Lean_initFn___closed__4_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ErrorExplanation_0__Lean_initFn___closed__5_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 0, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_ErrorExplanation_0__Lean_initFn___closed__4_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ErrorExplanation_0__Lean_initFn___closed__0_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ErrorExplanation_0__Lean_initFn___closed__1_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ErrorExplanation_0__Lean_initFn___closed__2_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_ErrorExplanation_0__Lean_initFn___closed__5_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ErrorExplanation_0__Lean_initFn___closed__5_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_ErrorExplanation_0__Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_ErrorExplanation_0__Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_errorExplanationExt;
LEAN_EXPORT lean_object* l_Lean_getErrorExplanation_x3f___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getErrorExplanation_x3f___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getErrorExplanation_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getErrorExplanation_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getErrorExplanationRaw_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getErrorExplanationRaw_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasErrorExplanation___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasErrorExplanation___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasErrorExplanation___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasErrorExplanation(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_getErrorExplanations___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getErrorExplanations___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getErrorExplanations___redArg___lam__1(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_getErrorExplanations___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_getErrorExplanations___redArg___lam__2___closed__0 = (const lean_object*)&l_Lean_getErrorExplanations___redArg___lam__2___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_getErrorExplanations___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_getErrorExplanations___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_getErrorExplanations___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_getErrorExplanations___redArg___closed__0 = (const lean_object*)&l_Lean_getErrorExplanations___redArg___closed__0_value;
static const lean_closure_object l_Lean_getErrorExplanations___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_getErrorExplanations___redArg___lam__1, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_getErrorExplanations___redArg___closed__1 = (const lean_object*)&l_Lean_getErrorExplanations___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_getErrorExplanations___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getErrorExplanations(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1___redArg___lam__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanationsRaw_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanationsRaw_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getErrorExplanationsRaw(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanationsRaw_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanationsRaw_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getErrorExplanationsSorted___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getErrorExplanationsSorted(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__0(lean_object* v_j_1_, lean_object* v_k_2_){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_3_ = l_Lean_Json_getObjValD(v_j_1_, v_k_2_);
v___x_4_ = l_Lean_Json_getStr_x3f(v___x_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__0___boxed(lean_object* v_j_5_, lean_object* v_k_6_){
_start:
{
lean_object* v_res_7_; 
v_res_7_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__0(v_j_5_, v_k_6_);
lean_dec_ref(v_k_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__1(lean_object* v_j_8_, lean_object* v_k_9_){
_start:
{
lean_object* v___x_10_; lean_object* v___x_11_; 
v___x_10_ = l_Lean_Json_getObjValD(v_j_8_, v_k_9_);
v___x_11_ = l_Lean_instFromJsonMessageSeverity_fromJson(v___x_10_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__1___boxed(lean_object* v_j_12_, lean_object* v_k_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__1(v_j_12_, v_k_13_);
lean_dec_ref(v_k_13_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__2_spec__2(lean_object* v_x_17_){
_start:
{
if (lean_obj_tag(v_x_17_) == 0)
{
lean_object* v___x_18_; 
v___x_18_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__2_spec__2___closed__0));
return v___x_18_;
}
else
{
lean_object* v___x_19_; 
v___x_19_ = l_Lean_Json_getStr_x3f(v_x_17_);
if (lean_obj_tag(v___x_19_) == 0)
{
lean_object* v_a_20_; lean_object* v___x_22_; uint8_t v_isShared_23_; uint8_t v_isSharedCheck_27_; 
v_a_20_ = lean_ctor_get(v___x_19_, 0);
v_isSharedCheck_27_ = !lean_is_exclusive(v___x_19_);
if (v_isSharedCheck_27_ == 0)
{
v___x_22_ = v___x_19_;
v_isShared_23_ = v_isSharedCheck_27_;
goto v_resetjp_21_;
}
else
{
lean_inc(v_a_20_);
lean_dec(v___x_19_);
v___x_22_ = lean_box(0);
v_isShared_23_ = v_isSharedCheck_27_;
goto v_resetjp_21_;
}
v_resetjp_21_:
{
lean_object* v___x_25_; 
if (v_isShared_23_ == 0)
{
v___x_25_ = v___x_22_;
goto v_reusejp_24_;
}
else
{
lean_object* v_reuseFailAlloc_26_; 
v_reuseFailAlloc_26_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_26_, 0, v_a_20_);
v___x_25_ = v_reuseFailAlloc_26_;
goto v_reusejp_24_;
}
v_reusejp_24_:
{
return v___x_25_;
}
}
}
else
{
lean_object* v_a_28_; lean_object* v___x_30_; uint8_t v_isShared_31_; uint8_t v_isSharedCheck_36_; 
v_a_28_ = lean_ctor_get(v___x_19_, 0);
v_isSharedCheck_36_ = !lean_is_exclusive(v___x_19_);
if (v_isSharedCheck_36_ == 0)
{
v___x_30_ = v___x_19_;
v_isShared_31_ = v_isSharedCheck_36_;
goto v_resetjp_29_;
}
else
{
lean_inc(v_a_28_);
lean_dec(v___x_19_);
v___x_30_ = lean_box(0);
v_isShared_31_ = v_isSharedCheck_36_;
goto v_resetjp_29_;
}
v_resetjp_29_:
{
lean_object* v___x_32_; lean_object* v___x_34_; 
v___x_32_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_32_, 0, v_a_28_);
if (v_isShared_31_ == 0)
{
lean_ctor_set(v___x_30_, 0, v___x_32_);
v___x_34_ = v___x_30_;
goto v_reusejp_33_;
}
else
{
lean_object* v_reuseFailAlloc_35_; 
v_reuseFailAlloc_35_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_35_, 0, v___x_32_);
v___x_34_ = v_reuseFailAlloc_35_;
goto v_reusejp_33_;
}
v_reusejp_33_:
{
return v___x_34_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__2(lean_object* v_j_37_, lean_object* v_k_38_){
_start:
{
lean_object* v___x_39_; lean_object* v___x_40_; 
v___x_39_ = l_Lean_Json_getObjValD(v_j_37_, v_k_38_);
v___x_40_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__2_spec__2(v___x_39_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__2___boxed(lean_object* v_j_41_, lean_object* v_k_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__2(v_j_41_, v_k_42_);
lean_dec_ref(v_k_42_);
return v_res_43_;
}
}
static lean_object* _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__5(void){
_start:
{
uint8_t v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_52_ = 1;
v___x_53_ = ((lean_object*)(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__4));
v___x_54_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_53_, v___x_52_);
return v___x_54_;
}
}
static lean_object* _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__7(void){
_start:
{
lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_56_ = ((lean_object*)(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__6));
v___x_57_ = lean_obj_once(&l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__5, &l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__5_once, _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__5);
v___x_58_ = lean_string_append(v___x_57_, v___x_56_);
return v___x_58_;
}
}
static lean_object* _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__9(void){
_start:
{
uint8_t v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_61_ = 1;
v___x_62_ = ((lean_object*)(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__8));
v___x_63_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_62_, v___x_61_);
return v___x_63_;
}
}
static lean_object* _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__10(void){
_start:
{
lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_64_ = lean_obj_once(&l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__9, &l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__9_once, _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__9);
v___x_65_ = lean_obj_once(&l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__7, &l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__7_once, _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__7);
v___x_66_ = lean_string_append(v___x_65_, v___x_64_);
return v___x_66_;
}
}
static lean_object* _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__12(void){
_start:
{
lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_68_ = ((lean_object*)(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__11));
v___x_69_ = lean_obj_once(&l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__10, &l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__10_once, _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__10);
v___x_70_ = lean_string_append(v___x_69_, v___x_68_);
return v___x_70_;
}
}
static lean_object* _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__15(void){
_start:
{
uint8_t v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_74_ = 1;
v___x_75_ = ((lean_object*)(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__14));
v___x_76_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_75_, v___x_74_);
return v___x_76_;
}
}
static lean_object* _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__16(void){
_start:
{
lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_77_ = lean_obj_once(&l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__15, &l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__15_once, _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__15);
v___x_78_ = lean_obj_once(&l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__7, &l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__7_once, _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__7);
v___x_79_ = lean_string_append(v___x_78_, v___x_77_);
return v___x_79_;
}
}
static lean_object* _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__17(void){
_start:
{
lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_80_ = ((lean_object*)(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__11));
v___x_81_ = lean_obj_once(&l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__16, &l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__16_once, _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__16);
v___x_82_ = lean_string_append(v___x_81_, v___x_80_);
return v___x_82_;
}
}
static lean_object* _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__20(void){
_start:
{
uint8_t v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_86_ = 1;
v___x_87_ = ((lean_object*)(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__19));
v___x_88_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_87_, v___x_86_);
return v___x_88_;
}
}
static lean_object* _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__21(void){
_start:
{
lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_89_ = lean_obj_once(&l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__20, &l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__20_once, _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__20);
v___x_90_ = lean_obj_once(&l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__7, &l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__7_once, _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__7);
v___x_91_ = lean_string_append(v___x_90_, v___x_89_);
return v___x_91_;
}
}
static lean_object* _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__22(void){
_start:
{
lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_92_ = ((lean_object*)(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__11));
v___x_93_ = lean_obj_once(&l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__21, &l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__21_once, _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__21);
v___x_94_ = lean_string_append(v___x_93_, v___x_92_);
return v___x_94_;
}
}
static lean_object* _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__26(void){
_start:
{
uint8_t v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_99_ = 1;
v___x_100_ = ((lean_object*)(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__25));
v___x_101_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_100_, v___x_99_);
return v___x_101_;
}
}
static lean_object* _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__27(void){
_start:
{
lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_102_ = lean_obj_once(&l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__26, &l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__26_once, _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__26);
v___x_103_ = lean_obj_once(&l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__7, &l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__7_once, _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__7);
v___x_104_ = lean_string_append(v___x_103_, v___x_102_);
return v___x_104_;
}
}
static lean_object* _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__28(void){
_start:
{
lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_105_ = ((lean_object*)(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__11));
v___x_106_ = lean_obj_once(&l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__27, &l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__27_once, _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__27);
v___x_107_ = lean_string_append(v___x_106_, v___x_105_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson(lean_object* v_json_108_){
_start:
{
lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_109_ = ((lean_object*)(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__0));
lean_inc(v_json_108_);
v___x_110_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__0(v_json_108_, v___x_109_);
if (lean_obj_tag(v___x_110_) == 0)
{
lean_object* v_a_111_; lean_object* v___x_113_; uint8_t v_isShared_114_; uint8_t v_isSharedCheck_120_; 
lean_dec(v_json_108_);
v_a_111_ = lean_ctor_get(v___x_110_, 0);
v_isSharedCheck_120_ = !lean_is_exclusive(v___x_110_);
if (v_isSharedCheck_120_ == 0)
{
v___x_113_ = v___x_110_;
v_isShared_114_ = v_isSharedCheck_120_;
goto v_resetjp_112_;
}
else
{
lean_inc(v_a_111_);
lean_dec(v___x_110_);
v___x_113_ = lean_box(0);
v_isShared_114_ = v_isSharedCheck_120_;
goto v_resetjp_112_;
}
v_resetjp_112_:
{
lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_118_; 
v___x_115_ = lean_obj_once(&l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__12, &l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__12_once, _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__12);
v___x_116_ = lean_string_append(v___x_115_, v_a_111_);
lean_dec(v_a_111_);
if (v_isShared_114_ == 0)
{
lean_ctor_set(v___x_113_, 0, v___x_116_);
v___x_118_ = v___x_113_;
goto v_reusejp_117_;
}
else
{
lean_object* v_reuseFailAlloc_119_; 
v_reuseFailAlloc_119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_119_, 0, v___x_116_);
v___x_118_ = v_reuseFailAlloc_119_;
goto v_reusejp_117_;
}
v_reusejp_117_:
{
return v___x_118_;
}
}
}
else
{
if (lean_obj_tag(v___x_110_) == 0)
{
lean_object* v_a_121_; lean_object* v___x_123_; uint8_t v_isShared_124_; uint8_t v_isSharedCheck_128_; 
lean_dec(v_json_108_);
v_a_121_ = lean_ctor_get(v___x_110_, 0);
v_isSharedCheck_128_ = !lean_is_exclusive(v___x_110_);
if (v_isSharedCheck_128_ == 0)
{
v___x_123_ = v___x_110_;
v_isShared_124_ = v_isSharedCheck_128_;
goto v_resetjp_122_;
}
else
{
lean_inc(v_a_121_);
lean_dec(v___x_110_);
v___x_123_ = lean_box(0);
v_isShared_124_ = v_isSharedCheck_128_;
goto v_resetjp_122_;
}
v_resetjp_122_:
{
lean_object* v___x_126_; 
if (v_isShared_124_ == 0)
{
lean_ctor_set_tag(v___x_123_, 0);
v___x_126_ = v___x_123_;
goto v_reusejp_125_;
}
else
{
lean_object* v_reuseFailAlloc_127_; 
v_reuseFailAlloc_127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_127_, 0, v_a_121_);
v___x_126_ = v_reuseFailAlloc_127_;
goto v_reusejp_125_;
}
v_reusejp_125_:
{
return v___x_126_;
}
}
}
else
{
lean_object* v_a_129_; lean_object* v___x_130_; lean_object* v___x_131_; 
v_a_129_ = lean_ctor_get(v___x_110_, 0);
lean_inc(v_a_129_);
lean_dec_ref(v___x_110_);
v___x_130_ = ((lean_object*)(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__13));
lean_inc(v_json_108_);
v___x_131_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__0(v_json_108_, v___x_130_);
if (lean_obj_tag(v___x_131_) == 0)
{
lean_object* v_a_132_; lean_object* v___x_134_; uint8_t v_isShared_135_; uint8_t v_isSharedCheck_141_; 
lean_dec(v_a_129_);
lean_dec(v_json_108_);
v_a_132_ = lean_ctor_get(v___x_131_, 0);
v_isSharedCheck_141_ = !lean_is_exclusive(v___x_131_);
if (v_isSharedCheck_141_ == 0)
{
v___x_134_ = v___x_131_;
v_isShared_135_ = v_isSharedCheck_141_;
goto v_resetjp_133_;
}
else
{
lean_inc(v_a_132_);
lean_dec(v___x_131_);
v___x_134_ = lean_box(0);
v_isShared_135_ = v_isSharedCheck_141_;
goto v_resetjp_133_;
}
v_resetjp_133_:
{
lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_139_; 
v___x_136_ = lean_obj_once(&l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__17, &l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__17_once, _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__17);
v___x_137_ = lean_string_append(v___x_136_, v_a_132_);
lean_dec(v_a_132_);
if (v_isShared_135_ == 0)
{
lean_ctor_set(v___x_134_, 0, v___x_137_);
v___x_139_ = v___x_134_;
goto v_reusejp_138_;
}
else
{
lean_object* v_reuseFailAlloc_140_; 
v_reuseFailAlloc_140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_140_, 0, v___x_137_);
v___x_139_ = v_reuseFailAlloc_140_;
goto v_reusejp_138_;
}
v_reusejp_138_:
{
return v___x_139_;
}
}
}
else
{
if (lean_obj_tag(v___x_131_) == 0)
{
lean_object* v_a_142_; lean_object* v___x_144_; uint8_t v_isShared_145_; uint8_t v_isSharedCheck_149_; 
lean_dec(v_a_129_);
lean_dec(v_json_108_);
v_a_142_ = lean_ctor_get(v___x_131_, 0);
v_isSharedCheck_149_ = !lean_is_exclusive(v___x_131_);
if (v_isSharedCheck_149_ == 0)
{
v___x_144_ = v___x_131_;
v_isShared_145_ = v_isSharedCheck_149_;
goto v_resetjp_143_;
}
else
{
lean_inc(v_a_142_);
lean_dec(v___x_131_);
v___x_144_ = lean_box(0);
v_isShared_145_ = v_isSharedCheck_149_;
goto v_resetjp_143_;
}
v_resetjp_143_:
{
lean_object* v___x_147_; 
if (v_isShared_145_ == 0)
{
lean_ctor_set_tag(v___x_144_, 0);
v___x_147_ = v___x_144_;
goto v_reusejp_146_;
}
else
{
lean_object* v_reuseFailAlloc_148_; 
v_reuseFailAlloc_148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_148_, 0, v_a_142_);
v___x_147_ = v_reuseFailAlloc_148_;
goto v_reusejp_146_;
}
v_reusejp_146_:
{
return v___x_147_;
}
}
}
else
{
lean_object* v_a_150_; lean_object* v___x_151_; lean_object* v___x_152_; 
v_a_150_ = lean_ctor_get(v___x_131_, 0);
lean_inc(v_a_150_);
lean_dec_ref(v___x_131_);
v___x_151_ = ((lean_object*)(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__18));
lean_inc(v_json_108_);
v___x_152_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__1(v_json_108_, v___x_151_);
if (lean_obj_tag(v___x_152_) == 0)
{
lean_object* v_a_153_; lean_object* v___x_155_; uint8_t v_isShared_156_; uint8_t v_isSharedCheck_162_; 
lean_dec(v_a_150_);
lean_dec(v_a_129_);
lean_dec(v_json_108_);
v_a_153_ = lean_ctor_get(v___x_152_, 0);
v_isSharedCheck_162_ = !lean_is_exclusive(v___x_152_);
if (v_isSharedCheck_162_ == 0)
{
v___x_155_ = v___x_152_;
v_isShared_156_ = v_isSharedCheck_162_;
goto v_resetjp_154_;
}
else
{
lean_inc(v_a_153_);
lean_dec(v___x_152_);
v___x_155_ = lean_box(0);
v_isShared_156_ = v_isSharedCheck_162_;
goto v_resetjp_154_;
}
v_resetjp_154_:
{
lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_160_; 
v___x_157_ = lean_obj_once(&l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__22, &l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__22_once, _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__22);
v___x_158_ = lean_string_append(v___x_157_, v_a_153_);
lean_dec(v_a_153_);
if (v_isShared_156_ == 0)
{
lean_ctor_set(v___x_155_, 0, v___x_158_);
v___x_160_ = v___x_155_;
goto v_reusejp_159_;
}
else
{
lean_object* v_reuseFailAlloc_161_; 
v_reuseFailAlloc_161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_161_, 0, v___x_158_);
v___x_160_ = v_reuseFailAlloc_161_;
goto v_reusejp_159_;
}
v_reusejp_159_:
{
return v___x_160_;
}
}
}
else
{
if (lean_obj_tag(v___x_152_) == 0)
{
lean_object* v_a_163_; lean_object* v___x_165_; uint8_t v_isShared_166_; uint8_t v_isSharedCheck_170_; 
lean_dec(v_a_150_);
lean_dec(v_a_129_);
lean_dec(v_json_108_);
v_a_163_ = lean_ctor_get(v___x_152_, 0);
v_isSharedCheck_170_ = !lean_is_exclusive(v___x_152_);
if (v_isSharedCheck_170_ == 0)
{
v___x_165_ = v___x_152_;
v_isShared_166_ = v_isSharedCheck_170_;
goto v_resetjp_164_;
}
else
{
lean_inc(v_a_163_);
lean_dec(v___x_152_);
v___x_165_ = lean_box(0);
v_isShared_166_ = v_isSharedCheck_170_;
goto v_resetjp_164_;
}
v_resetjp_164_:
{
lean_object* v___x_168_; 
if (v_isShared_166_ == 0)
{
lean_ctor_set_tag(v___x_165_, 0);
v___x_168_ = v___x_165_;
goto v_reusejp_167_;
}
else
{
lean_object* v_reuseFailAlloc_169_; 
v_reuseFailAlloc_169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_169_, 0, v_a_163_);
v___x_168_ = v_reuseFailAlloc_169_;
goto v_reusejp_167_;
}
v_reusejp_167_:
{
return v___x_168_;
}
}
}
else
{
lean_object* v_a_171_; lean_object* v___x_172_; lean_object* v___x_173_; 
v_a_171_ = lean_ctor_get(v___x_152_, 0);
lean_inc(v_a_171_);
lean_dec_ref(v___x_152_);
v___x_172_ = ((lean_object*)(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__23));
v___x_173_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__2(v_json_108_, v___x_172_);
if (lean_obj_tag(v___x_173_) == 0)
{
lean_object* v_a_174_; lean_object* v___x_176_; uint8_t v_isShared_177_; uint8_t v_isSharedCheck_183_; 
lean_dec(v_a_171_);
lean_dec(v_a_150_);
lean_dec(v_a_129_);
v_a_174_ = lean_ctor_get(v___x_173_, 0);
v_isSharedCheck_183_ = !lean_is_exclusive(v___x_173_);
if (v_isSharedCheck_183_ == 0)
{
v___x_176_ = v___x_173_;
v_isShared_177_ = v_isSharedCheck_183_;
goto v_resetjp_175_;
}
else
{
lean_inc(v_a_174_);
lean_dec(v___x_173_);
v___x_176_ = lean_box(0);
v_isShared_177_ = v_isSharedCheck_183_;
goto v_resetjp_175_;
}
v_resetjp_175_:
{
lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_181_; 
v___x_178_ = lean_obj_once(&l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__28, &l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__28_once, _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__28);
v___x_179_ = lean_string_append(v___x_178_, v_a_174_);
lean_dec(v_a_174_);
if (v_isShared_177_ == 0)
{
lean_ctor_set(v___x_176_, 0, v___x_179_);
v___x_181_ = v___x_176_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_182_; 
v_reuseFailAlloc_182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_182_, 0, v___x_179_);
v___x_181_ = v_reuseFailAlloc_182_;
goto v_reusejp_180_;
}
v_reusejp_180_:
{
return v___x_181_;
}
}
}
else
{
if (lean_obj_tag(v___x_173_) == 0)
{
lean_object* v_a_184_; lean_object* v___x_186_; uint8_t v_isShared_187_; uint8_t v_isSharedCheck_191_; 
lean_dec(v_a_171_);
lean_dec(v_a_150_);
lean_dec(v_a_129_);
v_a_184_ = lean_ctor_get(v___x_173_, 0);
v_isSharedCheck_191_ = !lean_is_exclusive(v___x_173_);
if (v_isSharedCheck_191_ == 0)
{
v___x_186_ = v___x_173_;
v_isShared_187_ = v_isSharedCheck_191_;
goto v_resetjp_185_;
}
else
{
lean_inc(v_a_184_);
lean_dec(v___x_173_);
v___x_186_ = lean_box(0);
v_isShared_187_ = v_isSharedCheck_191_;
goto v_resetjp_185_;
}
v_resetjp_185_:
{
lean_object* v___x_189_; 
if (v_isShared_187_ == 0)
{
lean_ctor_set_tag(v___x_186_, 0);
v___x_189_ = v___x_186_;
goto v_reusejp_188_;
}
else
{
lean_object* v_reuseFailAlloc_190_; 
v_reuseFailAlloc_190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_190_, 0, v_a_184_);
v___x_189_ = v_reuseFailAlloc_190_;
goto v_reusejp_188_;
}
v_reusejp_188_:
{
return v___x_189_;
}
}
}
else
{
lean_object* v_a_192_; lean_object* v___x_194_; uint8_t v_isShared_195_; uint8_t v_isSharedCheck_201_; 
v_a_192_ = lean_ctor_get(v___x_173_, 0);
v_isSharedCheck_201_ = !lean_is_exclusive(v___x_173_);
if (v_isSharedCheck_201_ == 0)
{
v___x_194_ = v___x_173_;
v_isShared_195_ = v_isSharedCheck_201_;
goto v_resetjp_193_;
}
else
{
lean_inc(v_a_192_);
lean_dec(v___x_173_);
v___x_194_ = lean_box(0);
v_isShared_195_ = v_isSharedCheck_201_;
goto v_resetjp_193_;
}
v_resetjp_193_:
{
lean_object* v___x_196_; uint8_t v___x_197_; lean_object* v___x_199_; 
v___x_196_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_196_, 0, v_a_129_);
lean_ctor_set(v___x_196_, 1, v_a_150_);
lean_ctor_set(v___x_196_, 2, v_a_192_);
v___x_197_ = lean_unbox(v_a_171_);
lean_dec(v_a_171_);
lean_ctor_set_uint8(v___x_196_, sizeof(void*)*3, v___x_197_);
if (v_isShared_195_ == 0)
{
lean_ctor_set(v___x_194_, 0, v___x_196_);
v___x_199_ = v___x_194_;
goto v_reusejp_198_;
}
else
{
lean_object* v_reuseFailAlloc_200_; 
v_reuseFailAlloc_200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_200_, 0, v___x_196_);
v___x_199_ = v_reuseFailAlloc_200_;
goto v_reusejp_198_;
}
v_reusejp_198_:
{
return v___x_199_;
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
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_ErrorExplanation_instToJsonMetadata_toJson_spec__0(lean_object* v_k_204_, lean_object* v_x_205_){
_start:
{
if (lean_obj_tag(v_x_205_) == 0)
{
lean_object* v___x_206_; 
lean_dec_ref(v_k_204_);
v___x_206_ = lean_box(0);
return v___x_206_;
}
else
{
lean_object* v_val_207_; lean_object* v___x_209_; uint8_t v_isShared_210_; uint8_t v_isSharedCheck_217_; 
v_val_207_ = lean_ctor_get(v_x_205_, 0);
v_isSharedCheck_217_ = !lean_is_exclusive(v_x_205_);
if (v_isSharedCheck_217_ == 0)
{
v___x_209_ = v_x_205_;
v_isShared_210_ = v_isSharedCheck_217_;
goto v_resetjp_208_;
}
else
{
lean_inc(v_val_207_);
lean_dec(v_x_205_);
v___x_209_ = lean_box(0);
v_isShared_210_ = v_isSharedCheck_217_;
goto v_resetjp_208_;
}
v_resetjp_208_:
{
lean_object* v___x_212_; 
if (v_isShared_210_ == 0)
{
lean_ctor_set_tag(v___x_209_, 3);
v___x_212_ = v___x_209_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_216_; 
v_reuseFailAlloc_216_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_216_, 0, v_val_207_);
v___x_212_ = v_reuseFailAlloc_216_;
goto v_reusejp_211_;
}
v_reusejp_211_:
{
lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
v___x_213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_213_, 0, v_k_204_);
lean_ctor_set(v___x_213_, 1, v___x_212_);
v___x_214_ = lean_box(0);
v___x_215_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_215_, 0, v___x_213_);
lean_ctor_set(v___x_215_, 1, v___x_214_);
return v___x_215_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_ErrorExplanation_instToJsonMetadata_toJson_spec__1(lean_object* v_a_218_, lean_object* v_a_219_){
_start:
{
if (lean_obj_tag(v_a_218_) == 0)
{
lean_object* v___x_220_; 
v___x_220_ = lean_array_to_list(v_a_219_);
return v___x_220_;
}
else
{
lean_object* v_head_221_; lean_object* v_tail_222_; lean_object* v___x_223_; 
v_head_221_ = lean_ctor_get(v_a_218_, 0);
lean_inc(v_head_221_);
v_tail_222_ = lean_ctor_get(v_a_218_, 1);
lean_inc(v_tail_222_);
lean_dec_ref(v_a_218_);
v___x_223_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_219_, v_head_221_);
v_a_218_ = v_tail_222_;
v_a_219_ = v___x_223_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ErrorExplanation_instToJsonMetadata_toJson(lean_object* v_x_227_){
_start:
{
lean_object* v_summary_228_; lean_object* v_sinceVersion_229_; uint8_t v_severity_230_; lean_object* v_removedVersion_x3f_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
v_summary_228_ = lean_ctor_get(v_x_227_, 0);
lean_inc_ref(v_summary_228_);
v_sinceVersion_229_ = lean_ctor_get(v_x_227_, 1);
lean_inc_ref(v_sinceVersion_229_);
v_severity_230_ = lean_ctor_get_uint8(v_x_227_, sizeof(void*)*3);
v_removedVersion_x3f_231_ = lean_ctor_get(v_x_227_, 2);
lean_inc(v_removedVersion_x3f_231_);
lean_dec_ref(v_x_227_);
v___x_232_ = ((lean_object*)(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__0));
v___x_233_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_233_, 0, v_summary_228_);
v___x_234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_234_, 0, v___x_232_);
lean_ctor_set(v___x_234_, 1, v___x_233_);
v___x_235_ = lean_box(0);
v___x_236_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_236_, 0, v___x_234_);
lean_ctor_set(v___x_236_, 1, v___x_235_);
v___x_237_ = ((lean_object*)(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__13));
v___x_238_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_238_, 0, v_sinceVersion_229_);
v___x_239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_239_, 0, v___x_237_);
lean_ctor_set(v___x_239_, 1, v___x_238_);
v___x_240_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_240_, 0, v___x_239_);
lean_ctor_set(v___x_240_, 1, v___x_235_);
v___x_241_ = ((lean_object*)(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__18));
v___x_242_ = l_Lean_instToJsonMessageSeverity_toJson(v_severity_230_);
v___x_243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_243_, 0, v___x_241_);
lean_ctor_set(v___x_243_, 1, v___x_242_);
v___x_244_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_244_, 0, v___x_243_);
lean_ctor_set(v___x_244_, 1, v___x_235_);
v___x_245_ = ((lean_object*)(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__23));
v___x_246_ = l_Lean_Json_opt___at___00Lean_ErrorExplanation_instToJsonMetadata_toJson_spec__0(v___x_245_, v_removedVersion_x3f_231_);
v___x_247_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_247_, 0, v___x_246_);
lean_ctor_set(v___x_247_, 1, v___x_235_);
v___x_248_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_248_, 0, v___x_244_);
lean_ctor_set(v___x_248_, 1, v___x_247_);
v___x_249_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_249_, 0, v___x_240_);
lean_ctor_set(v___x_249_, 1, v___x_248_);
v___x_250_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_250_, 0, v___x_236_);
lean_ctor_set(v___x_250_, 1, v___x_249_);
v___x_251_ = ((lean_object*)(l_Lean_ErrorExplanation_instToJsonMetadata_toJson___closed__0));
v___x_252_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_ErrorExplanation_instToJsonMetadata_toJson_spec__1(v___x_250_, v___x_251_);
v___x_253_ = l_Lean_Json_mkObj(v___x_252_);
return v___x_253_;
}
}
LEAN_EXPORT lean_object* l_Lean_ErrorExplanation_summaryWithSeverity(lean_object* v_explan_258_){
_start:
{
lean_object* v_metadata_259_; lean_object* v_summary_260_; uint8_t v_severity_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
v_metadata_259_ = lean_ctor_get(v_explan_258_, 1);
v_summary_260_ = lean_ctor_get(v_metadata_259_, 0);
v_severity_261_ = lean_ctor_get_uint8(v_metadata_259_, sizeof(void*)*3);
v___x_262_ = ((lean_object*)(l_Lean_ErrorExplanation_summaryWithSeverity___closed__0));
v___x_263_ = l_Lean_MessageSeverity_toString(v_severity_261_);
v___x_264_ = lean_string_append(v___x_262_, v___x_263_);
lean_dec_ref(v___x_263_);
v___x_265_ = ((lean_object*)(l_Lean_ErrorExplanation_summaryWithSeverity___closed__1));
v___x_266_ = lean_string_append(v___x_264_, v___x_265_);
v___x_267_ = lean_string_append(v___x_266_, v_summary_260_);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* l_Lean_ErrorExplanation_summaryWithSeverity___boxed(lean_object* v_explan_268_){
_start:
{
lean_object* v_res_269_; 
v_res_269_ = l_Lean_ErrorExplanation_summaryWithSeverity(v_explan_268_);
lean_dec_ref(v_explan_268_);
return v_res_269_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ErrorExplanation_0__Lean_initFn___lam__0_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_(lean_object* v_s_270_, lean_object* v_x_271_){
_start:
{
lean_object* v_fst_272_; lean_object* v_snd_273_; lean_object* v___x_274_; 
v_fst_272_ = lean_ctor_get(v_x_271_, 0);
lean_inc(v_fst_272_);
v_snd_273_ = lean_ctor_get(v_x_271_, 1);
lean_inc(v_snd_273_);
lean_dec_ref(v_x_271_);
v___x_274_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_272_, v_snd_273_, v_s_270_);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ErrorExplanation_0__Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_as_275_, size_t v_i_276_, size_t v_stop_277_, lean_object* v_b_278_){
_start:
{
uint8_t v___x_279_; 
v___x_279_ = lean_usize_dec_eq(v_i_276_, v_stop_277_);
if (v___x_279_ == 0)
{
lean_object* v___x_280_; lean_object* v_fst_281_; lean_object* v_snd_282_; lean_object* v___x_283_; size_t v___x_284_; size_t v___x_285_; 
v___x_280_ = lean_array_uget_borrowed(v_as_275_, v_i_276_);
v_fst_281_ = lean_ctor_get(v___x_280_, 0);
v_snd_282_ = lean_ctor_get(v___x_280_, 1);
lean_inc(v_snd_282_);
lean_inc(v_fst_281_);
v___x_283_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_281_, v_snd_282_, v_b_278_);
v___x_284_ = ((size_t)1ULL);
v___x_285_ = lean_usize_add(v_i_276_, v___x_284_);
v_i_276_ = v___x_285_;
v_b_278_ = v___x_283_;
goto _start;
}
else
{
return v_b_278_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ErrorExplanation_0__Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_as_287_, lean_object* v_i_288_, lean_object* v_stop_289_, lean_object* v_b_290_){
_start:
{
size_t v_i_boxed_291_; size_t v_stop_boxed_292_; lean_object* v_res_293_; 
v_i_boxed_291_ = lean_unbox_usize(v_i_288_);
lean_dec(v_i_288_);
v_stop_boxed_292_ = lean_unbox_usize(v_stop_289_);
lean_dec(v_stop_289_);
v_res_293_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ErrorExplanation_0__Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__spec__0_spec__0(v_as_287_, v_i_boxed_291_, v_stop_boxed_292_, v_b_290_);
lean_dec_ref(v_as_287_);
return v_res_293_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ErrorExplanation_0__Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__spec__0(lean_object* v_as_294_, size_t v_i_295_, size_t v_stop_296_, lean_object* v_b_297_){
_start:
{
uint8_t v___x_298_; 
v___x_298_ = lean_usize_dec_eq(v_i_295_, v_stop_296_);
if (v___x_298_ == 0)
{
lean_object* v___x_299_; lean_object* v_fst_300_; lean_object* v_snd_301_; lean_object* v___x_302_; size_t v___x_303_; size_t v___x_304_; lean_object* v___x_305_; 
v___x_299_ = lean_array_uget_borrowed(v_as_294_, v_i_295_);
v_fst_300_ = lean_ctor_get(v___x_299_, 0);
v_snd_301_ = lean_ctor_get(v___x_299_, 1);
lean_inc(v_snd_301_);
lean_inc(v_fst_300_);
v___x_302_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_300_, v_snd_301_, v_b_297_);
v___x_303_ = ((size_t)1ULL);
v___x_304_ = lean_usize_add(v_i_295_, v___x_303_);
v___x_305_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ErrorExplanation_0__Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__spec__0_spec__0(v_as_294_, v___x_304_, v_stop_296_, v___x_302_);
return v___x_305_;
}
else
{
return v_b_297_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ErrorExplanation_0__Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__spec__0___boxed(lean_object* v_as_306_, lean_object* v_i_307_, lean_object* v_stop_308_, lean_object* v_b_309_){
_start:
{
size_t v_i_boxed_310_; size_t v_stop_boxed_311_; lean_object* v_res_312_; 
v_i_boxed_310_ = lean_unbox_usize(v_i_307_);
lean_dec(v_i_307_);
v_stop_boxed_311_ = lean_unbox_usize(v_stop_308_);
lean_dec(v_stop_308_);
v_res_312_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ErrorExplanation_0__Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__spec__0(v_as_306_, v_i_boxed_310_, v_stop_boxed_311_, v_b_309_);
lean_dec_ref(v_as_306_);
return v_res_312_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ErrorExplanation_0__Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__spec__1(lean_object* v_as_313_, size_t v_i_314_, size_t v_stop_315_, lean_object* v_b_316_){
_start:
{
lean_object* v___y_318_; uint8_t v___x_322_; 
v___x_322_ = lean_usize_dec_eq(v_i_314_, v_stop_315_);
if (v___x_322_ == 0)
{
lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; uint8_t v___x_326_; 
v___x_323_ = lean_array_uget_borrowed(v_as_313_, v_i_314_);
v___x_324_ = lean_unsigned_to_nat(0u);
v___x_325_ = lean_array_get_size(v___x_323_);
v___x_326_ = lean_nat_dec_lt(v___x_324_, v___x_325_);
if (v___x_326_ == 0)
{
v___y_318_ = v_b_316_;
goto v___jp_317_;
}
else
{
uint8_t v___x_327_; 
v___x_327_ = lean_nat_dec_le(v___x_325_, v___x_325_);
if (v___x_327_ == 0)
{
if (v___x_326_ == 0)
{
v___y_318_ = v_b_316_;
goto v___jp_317_;
}
else
{
size_t v___x_328_; size_t v___x_329_; lean_object* v___x_330_; 
v___x_328_ = ((size_t)0ULL);
v___x_329_ = lean_usize_of_nat(v___x_325_);
v___x_330_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ErrorExplanation_0__Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__spec__0(v___x_323_, v___x_328_, v___x_329_, v_b_316_);
v___y_318_ = v___x_330_;
goto v___jp_317_;
}
}
else
{
size_t v___x_331_; size_t v___x_332_; lean_object* v___x_333_; 
v___x_331_ = ((size_t)0ULL);
v___x_332_ = lean_usize_of_nat(v___x_325_);
v___x_333_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ErrorExplanation_0__Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__spec__0(v___x_323_, v___x_331_, v___x_332_, v_b_316_);
v___y_318_ = v___x_333_;
goto v___jp_317_;
}
}
}
else
{
return v_b_316_;
}
v___jp_317_:
{
size_t v___x_319_; size_t v___x_320_; 
v___x_319_ = ((size_t)1ULL);
v___x_320_ = lean_usize_add(v_i_314_, v___x_319_);
v_i_314_ = v___x_320_;
v_b_316_ = v___y_318_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ErrorExplanation_0__Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__spec__1___boxed(lean_object* v_as_334_, lean_object* v_i_335_, lean_object* v_stop_336_, lean_object* v_b_337_){
_start:
{
size_t v_i_boxed_338_; size_t v_stop_boxed_339_; lean_object* v_res_340_; 
v_i_boxed_338_ = lean_unbox_usize(v_i_335_);
lean_dec(v_i_335_);
v_stop_boxed_339_ = lean_unbox_usize(v_stop_336_);
lean_dec(v_stop_336_);
v_res_340_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ErrorExplanation_0__Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__spec__1(v_as_334_, v_i_boxed_338_, v_stop_boxed_339_, v_b_337_);
lean_dec_ref(v_as_334_);
return v_res_340_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ErrorExplanation_0__Lean_initFn___lam__1_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_(lean_object* v_ess_341_){
_start:
{
lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; uint8_t v___x_345_; 
v___x_342_ = lean_box(1);
v___x_343_ = lean_unsigned_to_nat(0u);
v___x_344_ = lean_array_get_size(v_ess_341_);
v___x_345_ = lean_nat_dec_lt(v___x_343_, v___x_344_);
if (v___x_345_ == 0)
{
return v___x_342_;
}
else
{
uint8_t v___x_346_; 
v___x_346_ = lean_nat_dec_le(v___x_344_, v___x_344_);
if (v___x_346_ == 0)
{
if (v___x_345_ == 0)
{
return v___x_342_;
}
else
{
size_t v___x_347_; size_t v___x_348_; lean_object* v___x_349_; 
v___x_347_ = ((size_t)0ULL);
v___x_348_ = lean_usize_of_nat(v___x_344_);
v___x_349_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ErrorExplanation_0__Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__spec__1(v_ess_341_, v___x_347_, v___x_348_, v___x_342_);
return v___x_349_;
}
}
else
{
size_t v___x_350_; size_t v___x_351_; lean_object* v___x_352_; 
v___x_350_ = ((size_t)0ULL);
v___x_351_ = lean_usize_of_nat(v___x_344_);
v___x_352_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ErrorExplanation_0__Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__spec__1(v_ess_341_, v___x_350_, v___x_351_, v___x_342_);
return v___x_352_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ErrorExplanation_0__Lean_initFn___lam__1_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2____boxed(lean_object* v_ess_353_){
_start:
{
lean_object* v_res_354_; 
v_res_354_ = l___private_Lean_ErrorExplanation_0__Lean_initFn___lam__1_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_(v_ess_353_);
lean_dec_ref(v_ess_353_);
return v_res_354_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ErrorExplanation_0__Lean_initFn___lam__2_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_(lean_object* v_es_355_){
_start:
{
lean_object* v___x_356_; 
v___x_356_ = lean_array_mk(v_es_355_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ErrorExplanation_0__Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_372_ = ((lean_object*)(l___private_Lean_ErrorExplanation_0__Lean_initFn___closed__5_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_));
v___x_373_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_372_);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ErrorExplanation_0__Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2____boxed(lean_object* v_a_374_){
_start:
{
lean_object* v_res_375_; 
v_res_375_ = l___private_Lean_ErrorExplanation_0__Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_();
return v_res_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanation_x3f___redArg___lam__0(lean_object* v___x_376_, lean_object* v_name_377_, lean_object* v_toPure_378_, lean_object* v_____do__lift_379_){
_start:
{
lean_object* v___x_380_; lean_object* v_toEnvExtension_381_; lean_object* v_asyncMode_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; 
v___x_380_ = l_Lean_errorExplanationExt;
v_toEnvExtension_381_ = lean_ctor_get(v___x_380_, 0);
v_asyncMode_382_ = lean_ctor_get(v_toEnvExtension_381_, 2);
v___x_383_ = lean_box(0);
v___x_384_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_376_, v___x_380_, v_____do__lift_379_, v_asyncMode_382_, v___x_383_);
v___x_385_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_384_, v_name_377_);
lean_dec(v___x_384_);
v___x_386_ = lean_apply_2(v_toPure_378_, lean_box(0), v___x_385_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanation_x3f___redArg___lam__0___boxed(lean_object* v___x_387_, lean_object* v_name_388_, lean_object* v_toPure_389_, lean_object* v_____do__lift_390_){
_start:
{
lean_object* v_res_391_; 
v_res_391_ = l_Lean_getErrorExplanation_x3f___redArg___lam__0(v___x_387_, v_name_388_, v_toPure_389_, v_____do__lift_390_);
lean_dec(v_name_388_);
return v_res_391_;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanation_x3f___redArg(lean_object* v_inst_392_, lean_object* v_inst_393_, lean_object* v_name_394_){
_start:
{
lean_object* v_toApplicative_395_; lean_object* v_toBind_396_; lean_object* v_getEnv_397_; lean_object* v_toPure_398_; lean_object* v___x_399_; lean_object* v___f_400_; lean_object* v___x_401_; 
v_toApplicative_395_ = lean_ctor_get(v_inst_392_, 0);
lean_inc_ref(v_toApplicative_395_);
v_toBind_396_ = lean_ctor_get(v_inst_392_, 1);
lean_inc(v_toBind_396_);
lean_dec_ref(v_inst_392_);
v_getEnv_397_ = lean_ctor_get(v_inst_393_, 0);
lean_inc(v_getEnv_397_);
lean_dec_ref(v_inst_393_);
v_toPure_398_ = lean_ctor_get(v_toApplicative_395_, 1);
lean_inc(v_toPure_398_);
lean_dec_ref(v_toApplicative_395_);
v___x_399_ = lean_box(1);
v___f_400_ = lean_alloc_closure((void*)(l_Lean_getErrorExplanation_x3f___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_400_, 0, v___x_399_);
lean_closure_set(v___f_400_, 1, v_name_394_);
lean_closure_set(v___f_400_, 2, v_toPure_398_);
v___x_401_ = lean_apply_4(v_toBind_396_, lean_box(0), lean_box(0), v_getEnv_397_, v___f_400_);
return v___x_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanation_x3f(lean_object* v_m_402_, lean_object* v_inst_403_, lean_object* v_inst_404_, lean_object* v_name_405_){
_start:
{
lean_object* v___x_406_; 
v___x_406_ = l_Lean_getErrorExplanation_x3f___redArg(v_inst_403_, v_inst_404_, v_name_405_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanationRaw_x3f(lean_object* v_env_407_, lean_object* v_name_408_){
_start:
{
lean_object* v___x_409_; lean_object* v_toEnvExtension_410_; lean_object* v_asyncMode_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; 
v___x_409_ = l_Lean_errorExplanationExt;
v_toEnvExtension_410_ = lean_ctor_get(v___x_409_, 0);
v_asyncMode_411_ = lean_ctor_get(v_toEnvExtension_410_, 2);
v___x_412_ = lean_box(1);
v___x_413_ = lean_box(0);
v___x_414_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_412_, v___x_409_, v_env_407_, v_asyncMode_411_, v___x_413_);
v___x_415_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_414_, v_name_408_);
lean_dec(v___x_414_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanationRaw_x3f___boxed(lean_object* v_env_416_, lean_object* v_name_417_){
_start:
{
lean_object* v_res_418_; 
v_res_418_ = l_Lean_getErrorExplanationRaw_x3f(v_env_416_, v_name_417_);
lean_dec(v_name_417_);
return v_res_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasErrorExplanation___redArg___lam__0(lean_object* v___x_419_, lean_object* v_name_420_, lean_object* v_toPure_421_, lean_object* v_____do__lift_422_){
_start:
{
lean_object* v___x_423_; lean_object* v_toEnvExtension_424_; lean_object* v_asyncMode_425_; lean_object* v___x_426_; lean_object* v___x_427_; uint8_t v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_423_ = l_Lean_errorExplanationExt;
v_toEnvExtension_424_ = lean_ctor_get(v___x_423_, 0);
v_asyncMode_425_ = lean_ctor_get(v_toEnvExtension_424_, 2);
v___x_426_ = lean_box(0);
v___x_427_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_419_, v___x_423_, v_____do__lift_422_, v_asyncMode_425_, v___x_426_);
v___x_428_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_name_420_, v___x_427_);
lean_dec(v___x_427_);
v___x_429_ = lean_box(v___x_428_);
v___x_430_ = lean_apply_2(v_toPure_421_, lean_box(0), v___x_429_);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasErrorExplanation___redArg___lam__0___boxed(lean_object* v___x_431_, lean_object* v_name_432_, lean_object* v_toPure_433_, lean_object* v_____do__lift_434_){
_start:
{
lean_object* v_res_435_; 
v_res_435_ = l_Lean_hasErrorExplanation___redArg___lam__0(v___x_431_, v_name_432_, v_toPure_433_, v_____do__lift_434_);
lean_dec(v_name_432_);
return v_res_435_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasErrorExplanation___redArg(lean_object* v_inst_436_, lean_object* v_inst_437_, lean_object* v_name_438_){
_start:
{
lean_object* v_toApplicative_439_; lean_object* v_toBind_440_; lean_object* v_getEnv_441_; lean_object* v_toPure_442_; lean_object* v___x_443_; lean_object* v___f_444_; lean_object* v___x_445_; 
v_toApplicative_439_ = lean_ctor_get(v_inst_436_, 0);
lean_inc_ref(v_toApplicative_439_);
v_toBind_440_ = lean_ctor_get(v_inst_436_, 1);
lean_inc(v_toBind_440_);
lean_dec_ref(v_inst_436_);
v_getEnv_441_ = lean_ctor_get(v_inst_437_, 0);
lean_inc(v_getEnv_441_);
lean_dec_ref(v_inst_437_);
v_toPure_442_ = lean_ctor_get(v_toApplicative_439_, 1);
lean_inc(v_toPure_442_);
lean_dec_ref(v_toApplicative_439_);
v___x_443_ = lean_box(1);
v___f_444_ = lean_alloc_closure((void*)(l_Lean_hasErrorExplanation___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_444_, 0, v___x_443_);
lean_closure_set(v___f_444_, 1, v_name_438_);
lean_closure_set(v___f_444_, 2, v_toPure_442_);
v___x_445_ = lean_apply_4(v_toBind_440_, lean_box(0), lean_box(0), v_getEnv_441_, v___f_444_);
return v___x_445_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasErrorExplanation(lean_object* v_m_446_, lean_object* v_inst_447_, lean_object* v_inst_448_, lean_object* v_name_449_){
_start:
{
lean_object* v___x_450_; 
v___x_450_ = l_Lean_hasErrorExplanation___redArg(v_inst_447_, v_inst_448_, v_name_449_);
return v___x_450_;
}
}
LEAN_EXPORT uint8_t l_Lean_getErrorExplanations___redArg___lam__0(lean_object* v_e_451_, lean_object* v_e_x27_452_){
_start:
{
lean_object* v_fst_453_; lean_object* v_fst_454_; uint8_t v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; uint8_t v___x_458_; 
v_fst_453_ = lean_ctor_get(v_e_451_, 0);
lean_inc(v_fst_453_);
lean_dec_ref(v_e_451_);
v_fst_454_ = lean_ctor_get(v_e_x27_452_, 0);
lean_inc(v_fst_454_);
lean_dec_ref(v_e_x27_452_);
v___x_455_ = 1;
v___x_456_ = l_Lean_Name_toString(v_fst_453_, v___x_455_);
v___x_457_ = l_Lean_Name_toString(v_fst_454_, v___x_455_);
v___x_458_ = lean_string_dec_lt(v___x_456_, v___x_457_);
lean_dec_ref(v___x_457_);
lean_dec_ref(v___x_456_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanations___redArg___lam__0___boxed(lean_object* v_e_459_, lean_object* v_e_x27_460_){
_start:
{
uint8_t v_res_461_; lean_object* v_r_462_; 
v_res_461_ = l_Lean_getErrorExplanations___redArg___lam__0(v_e_459_, v_e_x27_460_);
v_r_462_ = lean_box(v_res_461_);
return v_r_462_;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanations___redArg___lam__1(lean_object* v_acc_463_, lean_object* v_k_464_, lean_object* v_v_465_){
_start:
{
lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_466_, 0, v_k_464_);
lean_ctor_set(v___x_466_, 1, v_v_465_);
v___x_467_ = lean_array_push(v_acc_463_, v___x_466_);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanations___redArg___lam__2(lean_object* v___x_470_, lean_object* v___f_471_, lean_object* v___f_472_, lean_object* v_toPure_473_, lean_object* v_____do__lift_474_){
_start:
{
lean_object* v___x_475_; lean_object* v_toEnvExtension_476_; lean_object* v_asyncMode_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___y_485_; lean_object* v___y_486_; uint8_t v___x_489_; 
v___x_475_ = l_Lean_errorExplanationExt;
v_toEnvExtension_476_ = lean_ctor_get(v___x_475_, 0);
v_asyncMode_477_ = lean_ctor_get(v_toEnvExtension_476_, 2);
v___x_478_ = lean_box(0);
v___x_479_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_470_, v___x_475_, v_____do__lift_474_, v_asyncMode_477_, v___x_478_);
v___x_480_ = lean_unsigned_to_nat(0u);
v___x_481_ = ((lean_object*)(l_Lean_getErrorExplanations___redArg___lam__2___closed__0));
v___x_482_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_471_, v___x_481_, v___x_479_);
v___x_483_ = lean_array_get_size(v___x_482_);
v___x_489_ = lean_nat_dec_eq(v___x_483_, v___x_480_);
if (v___x_489_ == 0)
{
lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___y_493_; uint8_t v___x_495_; 
v___x_490_ = lean_unsigned_to_nat(1u);
v___x_491_ = lean_nat_sub(v___x_483_, v___x_490_);
v___x_495_ = lean_nat_dec_le(v___x_480_, v___x_491_);
if (v___x_495_ == 0)
{
lean_inc(v___x_491_);
v___y_493_ = v___x_491_;
goto v___jp_492_;
}
else
{
v___y_493_ = v___x_480_;
goto v___jp_492_;
}
v___jp_492_:
{
uint8_t v___x_494_; 
v___x_494_ = lean_nat_dec_le(v___y_493_, v___x_491_);
if (v___x_494_ == 0)
{
lean_dec(v___x_491_);
lean_inc(v___y_493_);
v___y_485_ = v___y_493_;
v___y_486_ = v___y_493_;
goto v___jp_484_;
}
else
{
v___y_485_ = v___y_493_;
v___y_486_ = v___x_491_;
goto v___jp_484_;
}
}
}
else
{
lean_object* v___x_496_; 
lean_dec_ref(v___f_472_);
v___x_496_ = lean_apply_2(v_toPure_473_, lean_box(0), v___x_482_);
return v___x_496_;
}
v___jp_484_:
{
lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_487_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___f_472_, v___x_483_, v___x_482_, v___y_485_, v___y_486_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___y_486_);
v___x_488_ = lean_apply_2(v_toPure_473_, lean_box(0), v___x_487_);
return v___x_488_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanations___redArg(lean_object* v_inst_499_, lean_object* v_inst_500_){
_start:
{
lean_object* v_toApplicative_501_; lean_object* v_toBind_502_; lean_object* v_getEnv_503_; lean_object* v_toPure_504_; lean_object* v___f_505_; lean_object* v___f_506_; lean_object* v___x_507_; lean_object* v___f_508_; lean_object* v___x_509_; 
v_toApplicative_501_ = lean_ctor_get(v_inst_499_, 0);
lean_inc_ref(v_toApplicative_501_);
v_toBind_502_ = lean_ctor_get(v_inst_499_, 1);
lean_inc(v_toBind_502_);
lean_dec_ref(v_inst_499_);
v_getEnv_503_ = lean_ctor_get(v_inst_500_, 0);
lean_inc(v_getEnv_503_);
lean_dec_ref(v_inst_500_);
v_toPure_504_ = lean_ctor_get(v_toApplicative_501_, 1);
lean_inc(v_toPure_504_);
lean_dec_ref(v_toApplicative_501_);
v___f_505_ = ((lean_object*)(l_Lean_getErrorExplanations___redArg___closed__0));
v___f_506_ = ((lean_object*)(l_Lean_getErrorExplanations___redArg___closed__1));
v___x_507_ = lean_box(1);
v___f_508_ = lean_alloc_closure((void*)(l_Lean_getErrorExplanations___redArg___lam__2), 5, 4);
lean_closure_set(v___f_508_, 0, v___x_507_);
lean_closure_set(v___f_508_, 1, v___f_506_);
lean_closure_set(v___f_508_, 2, v___f_505_);
lean_closure_set(v___f_508_, 3, v_toPure_504_);
v___x_509_ = lean_apply_4(v_toBind_502_, lean_box(0), lean_box(0), v_getEnv_503_, v___f_508_);
return v___x_509_;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanations(lean_object* v_m_510_, lean_object* v_inst_511_, lean_object* v_inst_512_){
_start:
{
lean_object* v___x_513_; 
v___x_513_ = l_Lean_getErrorExplanations___redArg(v_inst_511_, v_inst_512_);
return v___x_513_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1___redArg___lam__0(uint8_t v___x_514_, lean_object* v_e_515_, lean_object* v_e_x27_516_){
_start:
{
lean_object* v_fst_517_; lean_object* v_fst_518_; lean_object* v___x_519_; lean_object* v___x_520_; uint8_t v___x_521_; 
v_fst_517_ = lean_ctor_get(v_e_515_, 0);
lean_inc(v_fst_517_);
lean_dec_ref(v_e_515_);
v_fst_518_ = lean_ctor_get(v_e_x27_516_, 0);
lean_inc(v_fst_518_);
lean_dec_ref(v_e_x27_516_);
v___x_519_ = l_Lean_Name_toString(v_fst_517_, v___x_514_);
v___x_520_ = l_Lean_Name_toString(v_fst_518_, v___x_514_);
v___x_521_ = lean_string_dec_lt(v___x_519_, v___x_520_);
lean_dec_ref(v___x_520_);
lean_dec_ref(v___x_519_);
return v___x_521_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1___redArg___lam__0___boxed(lean_object* v___x_522_, lean_object* v_e_523_, lean_object* v_e_x27_524_){
_start:
{
uint8_t v___x_263__boxed_525_; uint8_t v_res_526_; lean_object* v_r_527_; 
v___x_263__boxed_525_ = lean_unbox(v___x_522_);
v_res_526_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1___redArg___lam__0(v___x_263__boxed_525_, v_e_523_, v_e_x27_524_);
v_r_527_ = lean_box(v_res_526_);
return v_r_527_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1___redArg(lean_object* v_as_528_, lean_object* v_lo_529_, lean_object* v_hi_530_){
_start:
{
uint8_t v___x_531_; 
v___x_531_ = lean_nat_dec_lt(v_lo_529_, v_hi_530_);
if (v___x_531_ == 0)
{
lean_dec(v_lo_529_);
return v_as_528_;
}
else
{
lean_object* v___x_532_; lean_object* v___f_533_; lean_object* v___x_534_; lean_object* v_fst_535_; lean_object* v_snd_536_; uint8_t v___x_537_; 
v___x_532_ = lean_box(v___x_531_);
v___f_533_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_533_, 0, v___x_532_);
lean_inc(v_lo_529_);
v___x_534_ = l_Array_qpartition___redArg(v_as_528_, v___f_533_, v_lo_529_, v_hi_530_);
v_fst_535_ = lean_ctor_get(v___x_534_, 0);
lean_inc(v_fst_535_);
v_snd_536_ = lean_ctor_get(v___x_534_, 1);
lean_inc(v_snd_536_);
lean_dec_ref(v___x_534_);
v___x_537_ = lean_nat_dec_le(v_hi_530_, v_fst_535_);
if (v___x_537_ == 0)
{
lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_538_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1___redArg(v_snd_536_, v_lo_529_, v_fst_535_);
v___x_539_ = lean_unsigned_to_nat(1u);
v___x_540_ = lean_nat_add(v_fst_535_, v___x_539_);
lean_dec(v_fst_535_);
v_as_528_ = v___x_538_;
v_lo_529_ = v___x_540_;
goto _start;
}
else
{
lean_dec(v_fst_535_);
lean_dec(v_lo_529_);
return v_snd_536_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1___redArg___boxed(lean_object* v_as_542_, lean_object* v_lo_543_, lean_object* v_hi_544_){
_start:
{
lean_object* v_res_545_; 
v_res_545_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1___redArg(v_as_542_, v_lo_543_, v_hi_544_);
lean_dec(v_hi_544_);
return v_res_545_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanationsRaw_spec__0_spec__0(lean_object* v_init_546_, lean_object* v_x_547_){
_start:
{
if (lean_obj_tag(v_x_547_) == 0)
{
lean_object* v_k_548_; lean_object* v_v_549_; lean_object* v_l_550_; lean_object* v_r_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; 
v_k_548_ = lean_ctor_get(v_x_547_, 1);
v_v_549_ = lean_ctor_get(v_x_547_, 2);
v_l_550_ = lean_ctor_get(v_x_547_, 3);
v_r_551_ = lean_ctor_get(v_x_547_, 4);
v___x_552_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanationsRaw_spec__0_spec__0(v_init_546_, v_l_550_);
lean_inc(v_v_549_);
lean_inc(v_k_548_);
v___x_553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_553_, 0, v_k_548_);
lean_ctor_set(v___x_553_, 1, v_v_549_);
v___x_554_ = lean_array_push(v___x_552_, v___x_553_);
v_init_546_ = v___x_554_;
v_x_547_ = v_r_551_;
goto _start;
}
else
{
return v_init_546_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanationsRaw_spec__0_spec__0___boxed(lean_object* v_init_556_, lean_object* v_x_557_){
_start:
{
lean_object* v_res_558_; 
v_res_558_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanationsRaw_spec__0_spec__0(v_init_556_, v_x_557_);
lean_dec(v_x_557_);
return v_res_558_;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanationsRaw(lean_object* v_env_559_){
_start:
{
lean_object* v___x_560_; lean_object* v_toEnvExtension_561_; lean_object* v_asyncMode_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; uint8_t v___x_570_; 
v___x_560_ = l_Lean_errorExplanationExt;
v_toEnvExtension_561_ = lean_ctor_get(v___x_560_, 0);
v_asyncMode_562_ = lean_ctor_get(v_toEnvExtension_561_, 2);
v___x_563_ = lean_box(1);
v___x_564_ = lean_box(0);
v___x_565_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_563_, v___x_560_, v_env_559_, v_asyncMode_562_, v___x_564_);
v___x_566_ = lean_unsigned_to_nat(0u);
v___x_567_ = ((lean_object*)(l_Lean_getErrorExplanations___redArg___lam__2___closed__0));
v___x_568_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanationsRaw_spec__0_spec__0(v___x_567_, v___x_565_);
lean_dec(v___x_565_);
v___x_569_ = lean_array_get_size(v___x_568_);
v___x_570_ = lean_nat_dec_eq(v___x_569_, v___x_566_);
if (v___x_570_ == 0)
{
lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___y_574_; uint8_t v___x_578_; 
v___x_571_ = lean_unsigned_to_nat(1u);
v___x_572_ = lean_nat_sub(v___x_569_, v___x_571_);
v___x_578_ = lean_nat_dec_le(v___x_566_, v___x_572_);
if (v___x_578_ == 0)
{
lean_inc(v___x_572_);
v___y_574_ = v___x_572_;
goto v___jp_573_;
}
else
{
v___y_574_ = v___x_566_;
goto v___jp_573_;
}
v___jp_573_:
{
uint8_t v___x_575_; 
v___x_575_ = lean_nat_dec_le(v___y_574_, v___x_572_);
if (v___x_575_ == 0)
{
lean_object* v___x_576_; 
lean_dec(v___x_572_);
lean_inc(v___y_574_);
v___x_576_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1___redArg(v___x_568_, v___y_574_, v___y_574_);
lean_dec(v___y_574_);
return v___x_576_;
}
else
{
lean_object* v___x_577_; 
v___x_577_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1___redArg(v___x_568_, v___y_574_, v___x_572_);
lean_dec(v___x_572_);
return v___x_577_;
}
}
}
else
{
return v___x_568_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanationsRaw_spec__0(lean_object* v_init_579_, lean_object* v_t_580_){
_start:
{
lean_object* v___x_581_; 
v___x_581_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanationsRaw_spec__0_spec__0(v_init_579_, v_t_580_);
return v___x_581_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanationsRaw_spec__0___boxed(lean_object* v_init_582_, lean_object* v_t_583_){
_start:
{
lean_object* v_res_584_; 
v_res_584_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanationsRaw_spec__0(v_init_582_, v_t_583_);
lean_dec(v_t_583_);
return v_res_584_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1(lean_object* v_n_585_, lean_object* v_as_586_, lean_object* v_lo_587_, lean_object* v_hi_588_, lean_object* v_w_589_, lean_object* v_hlo_590_, lean_object* v_hhi_591_){
_start:
{
lean_object* v___x_592_; 
v___x_592_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1___redArg(v_as_586_, v_lo_587_, v_hi_588_);
return v___x_592_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1___boxed(lean_object* v_n_593_, lean_object* v_as_594_, lean_object* v_lo_595_, lean_object* v_hi_596_, lean_object* v_w_597_, lean_object* v_hlo_598_, lean_object* v_hhi_599_){
_start:
{
lean_object* v_res_600_; 
v_res_600_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1(v_n_593_, v_as_594_, v_lo_595_, v_hi_596_, v_w_597_, v_hlo_598_, v_hhi_599_);
lean_dec(v_hi_596_);
lean_dec(v_n_593_);
return v_res_600_;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanationsSorted___redArg(lean_object* v_inst_601_, lean_object* v_inst_602_){
_start:
{
lean_object* v___x_603_; 
v___x_603_ = l_Lean_getErrorExplanations___redArg(v_inst_601_, v_inst_602_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanationsSorted(lean_object* v_m_604_, lean_object* v_inst_605_, lean_object* v_inst_606_){
_start:
{
lean_object* v___x_607_; 
v___x_607_ = l_Lean_getErrorExplanations___redArg(v_inst_605_, v_inst_606_);
return v___x_607_;
}
}
lean_object* runtime_initialize_Lean_Message(uint8_t builtin);
lean_object* runtime_initialize_Lean_EnvExtension(uint8_t builtin);
lean_object* runtime_initialize_Lean_DocString_Links(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_ErrorExplanation(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Message(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_EnvExtension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_DocString_Links(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_ErrorExplanation_0__Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_errorExplanationExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_errorExplanationExt);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lean_Message(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_ErrorExplanation(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lean_Message(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Message(uint8_t builtin);
lean_object* initialize_Lean_EnvExtension(uint8_t builtin);
lean_object* initialize_Lean_DocString_Links(uint8_t builtin);
lean_object* initialize_Lean_Message(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_ErrorExplanation(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Message(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_EnvExtension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_DocString_Links(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Message(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_ErrorExplanation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_ErrorExplanation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_ErrorExplanation(builtin);
}
#ifdef __cplusplus
}
#endif

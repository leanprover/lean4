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
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg(lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
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
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__2_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__2_spec__2___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__2_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__2_spec__2(lean_object*);
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
static const lean_ctor_object l___private_Lean_ErrorExplanation_0__Lean_initFn___closed__5_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 8, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_ErrorExplanation_0__Lean_initFn___closed__4_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ErrorExplanation_0__Lean_initFn___closed__0_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ErrorExplanation_0__Lean_initFn___closed__1_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ErrorExplanation_0__Lean_initFn___closed__2_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1___redArg___lam__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanationsRaw_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanationsRaw_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getErrorExplanationsRaw(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanationsRaw_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanationsRaw_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__2_spec__2(lean_object* v_x_17_){
_start:
{
if (lean_obj_tag(v_x_17_) == 0)
{
lean_object* v___x_18_; 
v___x_18_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__2_spec__2___closed__0));
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
v___x_40_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__2_spec__2(v___x_39_);
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
lean_object* v_a_121_; lean_object* v___x_122_; lean_object* v___x_123_; 
v_a_121_ = lean_ctor_get(v___x_110_, 0);
lean_inc(v_a_121_);
lean_dec_ref_known(v___x_110_, 1);
v___x_122_ = ((lean_object*)(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__13));
lean_inc(v_json_108_);
v___x_123_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__0(v_json_108_, v___x_122_);
if (lean_obj_tag(v___x_123_) == 0)
{
lean_object* v_a_124_; lean_object* v___x_126_; uint8_t v_isShared_127_; uint8_t v_isSharedCheck_133_; 
lean_dec(v_a_121_);
lean_dec(v_json_108_);
v_a_124_ = lean_ctor_get(v___x_123_, 0);
v_isSharedCheck_133_ = !lean_is_exclusive(v___x_123_);
if (v_isSharedCheck_133_ == 0)
{
v___x_126_ = v___x_123_;
v_isShared_127_ = v_isSharedCheck_133_;
goto v_resetjp_125_;
}
else
{
lean_inc(v_a_124_);
lean_dec(v___x_123_);
v___x_126_ = lean_box(0);
v_isShared_127_ = v_isSharedCheck_133_;
goto v_resetjp_125_;
}
v_resetjp_125_:
{
lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_131_; 
v___x_128_ = lean_obj_once(&l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__17, &l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__17_once, _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__17);
v___x_129_ = lean_string_append(v___x_128_, v_a_124_);
lean_dec(v_a_124_);
if (v_isShared_127_ == 0)
{
lean_ctor_set(v___x_126_, 0, v___x_129_);
v___x_131_ = v___x_126_;
goto v_reusejp_130_;
}
else
{
lean_object* v_reuseFailAlloc_132_; 
v_reuseFailAlloc_132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_132_, 0, v___x_129_);
v___x_131_ = v_reuseFailAlloc_132_;
goto v_reusejp_130_;
}
v_reusejp_130_:
{
return v___x_131_;
}
}
}
else
{
lean_object* v_a_134_; lean_object* v___x_135_; lean_object* v___x_136_; 
v_a_134_ = lean_ctor_get(v___x_123_, 0);
lean_inc(v_a_134_);
lean_dec_ref_known(v___x_123_, 1);
v___x_135_ = ((lean_object*)(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__18));
lean_inc(v_json_108_);
v___x_136_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__1(v_json_108_, v___x_135_);
if (lean_obj_tag(v___x_136_) == 0)
{
lean_object* v_a_137_; lean_object* v___x_139_; uint8_t v_isShared_140_; uint8_t v_isSharedCheck_146_; 
lean_dec(v_a_134_);
lean_dec(v_a_121_);
lean_dec(v_json_108_);
v_a_137_ = lean_ctor_get(v___x_136_, 0);
v_isSharedCheck_146_ = !lean_is_exclusive(v___x_136_);
if (v_isSharedCheck_146_ == 0)
{
v___x_139_ = v___x_136_;
v_isShared_140_ = v_isSharedCheck_146_;
goto v_resetjp_138_;
}
else
{
lean_inc(v_a_137_);
lean_dec(v___x_136_);
v___x_139_ = lean_box(0);
v_isShared_140_ = v_isSharedCheck_146_;
goto v_resetjp_138_;
}
v_resetjp_138_:
{
lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_144_; 
v___x_141_ = lean_obj_once(&l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__22, &l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__22_once, _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__22);
v___x_142_ = lean_string_append(v___x_141_, v_a_137_);
lean_dec(v_a_137_);
if (v_isShared_140_ == 0)
{
lean_ctor_set(v___x_139_, 0, v___x_142_);
v___x_144_ = v___x_139_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_147_; lean_object* v___x_148_; lean_object* v___x_149_; 
v_a_147_ = lean_ctor_get(v___x_136_, 0);
lean_inc(v_a_147_);
lean_dec_ref_known(v___x_136_, 1);
v___x_148_ = ((lean_object*)(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__23));
v___x_149_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__2(v_json_108_, v___x_148_);
if (lean_obj_tag(v___x_149_) == 0)
{
lean_object* v_a_150_; lean_object* v___x_152_; uint8_t v_isShared_153_; uint8_t v_isSharedCheck_159_; 
lean_dec(v_a_147_);
lean_dec(v_a_134_);
lean_dec(v_a_121_);
v_a_150_ = lean_ctor_get(v___x_149_, 0);
v_isSharedCheck_159_ = !lean_is_exclusive(v___x_149_);
if (v_isSharedCheck_159_ == 0)
{
v___x_152_ = v___x_149_;
v_isShared_153_ = v_isSharedCheck_159_;
goto v_resetjp_151_;
}
else
{
lean_inc(v_a_150_);
lean_dec(v___x_149_);
v___x_152_ = lean_box(0);
v_isShared_153_ = v_isSharedCheck_159_;
goto v_resetjp_151_;
}
v_resetjp_151_:
{
lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_157_; 
v___x_154_ = lean_obj_once(&l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__28, &l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__28_once, _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__28);
v___x_155_ = lean_string_append(v___x_154_, v_a_150_);
lean_dec(v_a_150_);
if (v_isShared_153_ == 0)
{
lean_ctor_set(v___x_152_, 0, v___x_155_);
v___x_157_ = v___x_152_;
goto v_reusejp_156_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v___x_155_);
v___x_157_ = v_reuseFailAlloc_158_;
goto v_reusejp_156_;
}
v_reusejp_156_:
{
return v___x_157_;
}
}
}
else
{
lean_object* v_a_160_; lean_object* v___x_162_; uint8_t v_isShared_163_; uint8_t v_isSharedCheck_169_; 
v_a_160_ = lean_ctor_get(v___x_149_, 0);
v_isSharedCheck_169_ = !lean_is_exclusive(v___x_149_);
if (v_isSharedCheck_169_ == 0)
{
v___x_162_ = v___x_149_;
v_isShared_163_ = v_isSharedCheck_169_;
goto v_resetjp_161_;
}
else
{
lean_inc(v_a_160_);
lean_dec(v___x_149_);
v___x_162_ = lean_box(0);
v_isShared_163_ = v_isSharedCheck_169_;
goto v_resetjp_161_;
}
v_resetjp_161_:
{
lean_object* v___x_164_; uint8_t v___x_165_; lean_object* v___x_167_; 
v___x_164_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_164_, 0, v_a_121_);
lean_ctor_set(v___x_164_, 1, v_a_134_);
lean_ctor_set(v___x_164_, 2, v_a_160_);
v___x_165_ = lean_unbox(v_a_147_);
lean_dec(v_a_147_);
lean_ctor_set_uint8(v___x_164_, sizeof(void*)*3, v___x_165_);
if (v_isShared_163_ == 0)
{
lean_ctor_set(v___x_162_, 0, v___x_164_);
v___x_167_ = v___x_162_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v___x_164_);
v___x_167_ = v_reuseFailAlloc_168_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
return v___x_167_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_ErrorExplanation_instToJsonMetadata_toJson_spec__0(lean_object* v_k_172_, lean_object* v_x_173_){
_start:
{
if (lean_obj_tag(v_x_173_) == 0)
{
lean_object* v___x_174_; 
lean_dec_ref(v_k_172_);
v___x_174_ = lean_box(0);
return v___x_174_;
}
else
{
lean_object* v_val_175_; lean_object* v___x_177_; uint8_t v_isShared_178_; uint8_t v_isSharedCheck_185_; 
v_val_175_ = lean_ctor_get(v_x_173_, 0);
v_isSharedCheck_185_ = !lean_is_exclusive(v_x_173_);
if (v_isSharedCheck_185_ == 0)
{
v___x_177_ = v_x_173_;
v_isShared_178_ = v_isSharedCheck_185_;
goto v_resetjp_176_;
}
else
{
lean_inc(v_val_175_);
lean_dec(v_x_173_);
v___x_177_ = lean_box(0);
v_isShared_178_ = v_isSharedCheck_185_;
goto v_resetjp_176_;
}
v_resetjp_176_:
{
lean_object* v___x_180_; 
if (v_isShared_178_ == 0)
{
lean_ctor_set_tag(v___x_177_, 3);
v___x_180_ = v___x_177_;
goto v_reusejp_179_;
}
else
{
lean_object* v_reuseFailAlloc_184_; 
v_reuseFailAlloc_184_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_184_, 0, v_val_175_);
v___x_180_ = v_reuseFailAlloc_184_;
goto v_reusejp_179_;
}
v_reusejp_179_:
{
lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_181_, 0, v_k_172_);
lean_ctor_set(v___x_181_, 1, v___x_180_);
v___x_182_ = lean_box(0);
v___x_183_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_183_, 0, v___x_181_);
lean_ctor_set(v___x_183_, 1, v___x_182_);
return v___x_183_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_ErrorExplanation_instToJsonMetadata_toJson_spec__1(lean_object* v_a_186_, lean_object* v_a_187_){
_start:
{
if (lean_obj_tag(v_a_186_) == 0)
{
lean_object* v___x_188_; 
v___x_188_ = lean_array_to_list(v_a_187_);
return v___x_188_;
}
else
{
lean_object* v_head_189_; lean_object* v_tail_190_; lean_object* v___x_191_; 
v_head_189_ = lean_ctor_get(v_a_186_, 0);
lean_inc(v_head_189_);
v_tail_190_ = lean_ctor_get(v_a_186_, 1);
lean_inc(v_tail_190_);
lean_dec_ref_known(v_a_186_, 2);
v___x_191_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_187_, v_head_189_);
v_a_186_ = v_tail_190_;
v_a_187_ = v___x_191_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ErrorExplanation_instToJsonMetadata_toJson(lean_object* v_x_195_){
_start:
{
lean_object* v_summary_196_; lean_object* v_sinceVersion_197_; uint8_t v_severity_198_; lean_object* v_removedVersion_x3f_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; 
v_summary_196_ = lean_ctor_get(v_x_195_, 0);
lean_inc_ref(v_summary_196_);
v_sinceVersion_197_ = lean_ctor_get(v_x_195_, 1);
lean_inc_ref(v_sinceVersion_197_);
v_severity_198_ = lean_ctor_get_uint8(v_x_195_, sizeof(void*)*3);
v_removedVersion_x3f_199_ = lean_ctor_get(v_x_195_, 2);
lean_inc(v_removedVersion_x3f_199_);
lean_dec_ref(v_x_195_);
v___x_200_ = ((lean_object*)(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__0));
v___x_201_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_201_, 0, v_summary_196_);
v___x_202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_202_, 0, v___x_200_);
lean_ctor_set(v___x_202_, 1, v___x_201_);
v___x_203_ = lean_box(0);
v___x_204_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_204_, 0, v___x_202_);
lean_ctor_set(v___x_204_, 1, v___x_203_);
v___x_205_ = ((lean_object*)(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__13));
v___x_206_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_206_, 0, v_sinceVersion_197_);
v___x_207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_207_, 0, v___x_205_);
lean_ctor_set(v___x_207_, 1, v___x_206_);
v___x_208_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_208_, 0, v___x_207_);
lean_ctor_set(v___x_208_, 1, v___x_203_);
v___x_209_ = ((lean_object*)(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__18));
v___x_210_ = l_Lean_instToJsonMessageSeverity_toJson(v_severity_198_);
v___x_211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_211_, 0, v___x_209_);
lean_ctor_set(v___x_211_, 1, v___x_210_);
v___x_212_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_212_, 0, v___x_211_);
lean_ctor_set(v___x_212_, 1, v___x_203_);
v___x_213_ = ((lean_object*)(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__23));
v___x_214_ = l_Lean_Json_opt___at___00Lean_ErrorExplanation_instToJsonMetadata_toJson_spec__0(v___x_213_, v_removedVersion_x3f_199_);
v___x_215_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_215_, 0, v___x_214_);
lean_ctor_set(v___x_215_, 1, v___x_203_);
v___x_216_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_216_, 0, v___x_212_);
lean_ctor_set(v___x_216_, 1, v___x_215_);
v___x_217_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_217_, 0, v___x_208_);
lean_ctor_set(v___x_217_, 1, v___x_216_);
v___x_218_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_218_, 0, v___x_204_);
lean_ctor_set(v___x_218_, 1, v___x_217_);
v___x_219_ = ((lean_object*)(l_Lean_ErrorExplanation_instToJsonMetadata_toJson___closed__0));
v___x_220_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_ErrorExplanation_instToJsonMetadata_toJson_spec__1(v___x_218_, v___x_219_);
v___x_221_ = l_Lean_Json_mkObj(v___x_220_);
lean_dec(v___x_220_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l_Lean_ErrorExplanation_summaryWithSeverity(lean_object* v_explan_226_){
_start:
{
lean_object* v_metadata_227_; lean_object* v_summary_228_; uint8_t v_severity_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; 
v_metadata_227_ = lean_ctor_get(v_explan_226_, 1);
v_summary_228_ = lean_ctor_get(v_metadata_227_, 0);
v_severity_229_ = lean_ctor_get_uint8(v_metadata_227_, sizeof(void*)*3);
v___x_230_ = ((lean_object*)(l_Lean_ErrorExplanation_summaryWithSeverity___closed__0));
v___x_231_ = l_Lean_MessageSeverity_toString(v_severity_229_);
v___x_232_ = lean_string_append(v___x_230_, v___x_231_);
lean_dec_ref(v___x_231_);
v___x_233_ = ((lean_object*)(l_Lean_ErrorExplanation_summaryWithSeverity___closed__1));
v___x_234_ = lean_string_append(v___x_232_, v___x_233_);
v___x_235_ = lean_string_append(v___x_234_, v_summary_228_);
return v___x_235_;
}
}
LEAN_EXPORT lean_object* l_Lean_ErrorExplanation_summaryWithSeverity___boxed(lean_object* v_explan_236_){
_start:
{
lean_object* v_res_237_; 
v_res_237_ = l_Lean_ErrorExplanation_summaryWithSeverity(v_explan_236_);
lean_dec_ref(v_explan_236_);
return v_res_237_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ErrorExplanation_0__Lean_initFn___lam__0_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_(lean_object* v_s_238_, lean_object* v_x_239_){
_start:
{
lean_object* v_fst_240_; lean_object* v_snd_241_; lean_object* v___x_242_; 
v_fst_240_ = lean_ctor_get(v_x_239_, 0);
lean_inc(v_fst_240_);
v_snd_241_ = lean_ctor_get(v_x_239_, 1);
lean_inc(v_snd_241_);
lean_dec_ref(v_x_239_);
v___x_242_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_240_, v_snd_241_, v_s_238_);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ErrorExplanation_0__Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_as_243_, size_t v_i_244_, size_t v_stop_245_, lean_object* v_b_246_){
_start:
{
uint8_t v___x_247_; 
v___x_247_ = lean_usize_dec_eq(v_i_244_, v_stop_245_);
if (v___x_247_ == 0)
{
lean_object* v___x_248_; lean_object* v_fst_249_; lean_object* v_snd_250_; lean_object* v___x_251_; size_t v___x_252_; size_t v___x_253_; 
v___x_248_ = lean_array_uget_borrowed(v_as_243_, v_i_244_);
v_fst_249_ = lean_ctor_get(v___x_248_, 0);
v_snd_250_ = lean_ctor_get(v___x_248_, 1);
lean_inc(v_snd_250_);
lean_inc(v_fst_249_);
v___x_251_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_249_, v_snd_250_, v_b_246_);
v___x_252_ = ((size_t)1ULL);
v___x_253_ = lean_usize_add(v_i_244_, v___x_252_);
v_i_244_ = v___x_253_;
v_b_246_ = v___x_251_;
goto _start;
}
else
{
return v_b_246_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ErrorExplanation_0__Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_as_255_, lean_object* v_i_256_, lean_object* v_stop_257_, lean_object* v_b_258_){
_start:
{
size_t v_i_boxed_259_; size_t v_stop_boxed_260_; lean_object* v_res_261_; 
v_i_boxed_259_ = lean_unbox_usize(v_i_256_);
lean_dec(v_i_256_);
v_stop_boxed_260_ = lean_unbox_usize(v_stop_257_);
lean_dec(v_stop_257_);
v_res_261_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ErrorExplanation_0__Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__spec__0_spec__0(v_as_255_, v_i_boxed_259_, v_stop_boxed_260_, v_b_258_);
lean_dec_ref(v_as_255_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ErrorExplanation_0__Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__spec__0(lean_object* v_as_262_, size_t v_i_263_, size_t v_stop_264_, lean_object* v_b_265_){
_start:
{
uint8_t v___x_266_; 
v___x_266_ = lean_usize_dec_eq(v_i_263_, v_stop_264_);
if (v___x_266_ == 0)
{
lean_object* v___x_267_; lean_object* v_fst_268_; lean_object* v_snd_269_; lean_object* v___x_270_; size_t v___x_271_; size_t v___x_272_; lean_object* v___x_273_; 
v___x_267_ = lean_array_uget_borrowed(v_as_262_, v_i_263_);
v_fst_268_ = lean_ctor_get(v___x_267_, 0);
v_snd_269_ = lean_ctor_get(v___x_267_, 1);
lean_inc(v_snd_269_);
lean_inc(v_fst_268_);
v___x_270_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_268_, v_snd_269_, v_b_265_);
v___x_271_ = ((size_t)1ULL);
v___x_272_ = lean_usize_add(v_i_263_, v___x_271_);
v___x_273_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ErrorExplanation_0__Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__spec__0_spec__0(v_as_262_, v___x_272_, v_stop_264_, v___x_270_);
return v___x_273_;
}
else
{
return v_b_265_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ErrorExplanation_0__Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__spec__0___boxed(lean_object* v_as_274_, lean_object* v_i_275_, lean_object* v_stop_276_, lean_object* v_b_277_){
_start:
{
size_t v_i_boxed_278_; size_t v_stop_boxed_279_; lean_object* v_res_280_; 
v_i_boxed_278_ = lean_unbox_usize(v_i_275_);
lean_dec(v_i_275_);
v_stop_boxed_279_ = lean_unbox_usize(v_stop_276_);
lean_dec(v_stop_276_);
v_res_280_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ErrorExplanation_0__Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__spec__0(v_as_274_, v_i_boxed_278_, v_stop_boxed_279_, v_b_277_);
lean_dec_ref(v_as_274_);
return v_res_280_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ErrorExplanation_0__Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__spec__1(lean_object* v_as_281_, size_t v_i_282_, size_t v_stop_283_, lean_object* v_b_284_){
_start:
{
lean_object* v___y_286_; uint8_t v___x_290_; 
v___x_290_ = lean_usize_dec_eq(v_i_282_, v_stop_283_);
if (v___x_290_ == 0)
{
lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; uint8_t v___x_294_; 
v___x_291_ = lean_array_uget_borrowed(v_as_281_, v_i_282_);
v___x_292_ = lean_unsigned_to_nat(0u);
v___x_293_ = lean_array_get_size(v___x_291_);
v___x_294_ = lean_nat_dec_lt(v___x_292_, v___x_293_);
if (v___x_294_ == 0)
{
v___y_286_ = v_b_284_;
goto v___jp_285_;
}
else
{
size_t v___x_295_; size_t v___x_296_; lean_object* v___x_297_; 
v___x_295_ = ((size_t)0ULL);
v___x_296_ = lean_usize_of_nat(v___x_293_);
v___x_297_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ErrorExplanation_0__Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__spec__0(v___x_291_, v___x_295_, v___x_296_, v_b_284_);
v___y_286_ = v___x_297_;
goto v___jp_285_;
}
}
else
{
return v_b_284_;
}
v___jp_285_:
{
size_t v___x_287_; size_t v___x_288_; 
v___x_287_ = ((size_t)1ULL);
v___x_288_ = lean_usize_add(v_i_282_, v___x_287_);
v_i_282_ = v___x_288_;
v_b_284_ = v___y_286_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ErrorExplanation_0__Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__spec__1___boxed(lean_object* v_as_298_, lean_object* v_i_299_, lean_object* v_stop_300_, lean_object* v_b_301_){
_start:
{
size_t v_i_boxed_302_; size_t v_stop_boxed_303_; lean_object* v_res_304_; 
v_i_boxed_302_ = lean_unbox_usize(v_i_299_);
lean_dec(v_i_299_);
v_stop_boxed_303_ = lean_unbox_usize(v_stop_300_);
lean_dec(v_stop_300_);
v_res_304_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ErrorExplanation_0__Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__spec__1(v_as_298_, v_i_boxed_302_, v_stop_boxed_303_, v_b_301_);
lean_dec_ref(v_as_298_);
return v_res_304_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ErrorExplanation_0__Lean_initFn___lam__1_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_(lean_object* v_ess_305_){
_start:
{
lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; uint8_t v___x_309_; 
v___x_306_ = lean_box(1);
v___x_307_ = lean_unsigned_to_nat(0u);
v___x_308_ = lean_array_get_size(v_ess_305_);
v___x_309_ = lean_nat_dec_lt(v___x_307_, v___x_308_);
if (v___x_309_ == 0)
{
return v___x_306_;
}
else
{
size_t v___x_310_; size_t v___x_311_; lean_object* v___x_312_; 
v___x_310_ = ((size_t)0ULL);
v___x_311_ = lean_usize_of_nat(v___x_308_);
v___x_312_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ErrorExplanation_0__Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__spec__1(v_ess_305_, v___x_310_, v___x_311_, v___x_306_);
return v___x_312_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ErrorExplanation_0__Lean_initFn___lam__1_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2____boxed(lean_object* v_ess_313_){
_start:
{
lean_object* v_res_314_; 
v_res_314_ = l___private_Lean_ErrorExplanation_0__Lean_initFn___lam__1_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_(v_ess_313_);
lean_dec_ref(v_ess_313_);
return v_res_314_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ErrorExplanation_0__Lean_initFn___lam__2_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_(lean_object* v_es_315_){
_start:
{
lean_object* v___x_316_; 
v___x_316_ = lean_array_mk(v_es_315_);
return v___x_316_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ErrorExplanation_0__Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_333_ = ((lean_object*)(l___private_Lean_ErrorExplanation_0__Lean_initFn___closed__5_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_));
v___x_334_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_333_);
return v___x_334_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ErrorExplanation_0__Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2____boxed(lean_object* v_a_335_){
_start:
{
lean_object* v_res_336_; 
v_res_336_ = l___private_Lean_ErrorExplanation_0__Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_();
return v_res_336_;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanation_x3f___redArg___lam__0(lean_object* v___x_337_, lean_object* v_name_338_, lean_object* v_toPure_339_, lean_object* v_____do__lift_340_){
_start:
{
lean_object* v___x_341_; lean_object* v_toEnvExtension_342_; lean_object* v_asyncMode_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_341_ = l_Lean_errorExplanationExt;
v_toEnvExtension_342_ = lean_ctor_get(v___x_341_, 0);
v_asyncMode_343_ = lean_ctor_get(v_toEnvExtension_342_, 2);
v___x_344_ = lean_box(0);
v___x_345_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_337_, v___x_341_, v_____do__lift_340_, v_asyncMode_343_, v___x_344_);
v___x_346_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_345_, v_name_338_);
lean_dec(v___x_345_);
v___x_347_ = lean_apply_2(v_toPure_339_, lean_box(0), v___x_346_);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanation_x3f___redArg___lam__0___boxed(lean_object* v___x_348_, lean_object* v_name_349_, lean_object* v_toPure_350_, lean_object* v_____do__lift_351_){
_start:
{
lean_object* v_res_352_; 
v_res_352_ = l_Lean_getErrorExplanation_x3f___redArg___lam__0(v___x_348_, v_name_349_, v_toPure_350_, v_____do__lift_351_);
lean_dec(v_name_349_);
return v_res_352_;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanation_x3f___redArg(lean_object* v_inst_353_, lean_object* v_inst_354_, lean_object* v_name_355_){
_start:
{
lean_object* v_toApplicative_356_; lean_object* v_toBind_357_; lean_object* v_getEnv_358_; lean_object* v_toPure_359_; lean_object* v___x_360_; lean_object* v___f_361_; lean_object* v___x_362_; 
v_toApplicative_356_ = lean_ctor_get(v_inst_353_, 0);
lean_inc_ref(v_toApplicative_356_);
v_toBind_357_ = lean_ctor_get(v_inst_353_, 1);
lean_inc(v_toBind_357_);
lean_dec_ref(v_inst_353_);
v_getEnv_358_ = lean_ctor_get(v_inst_354_, 0);
lean_inc(v_getEnv_358_);
lean_dec_ref(v_inst_354_);
v_toPure_359_ = lean_ctor_get(v_toApplicative_356_, 1);
lean_inc(v_toPure_359_);
lean_dec_ref(v_toApplicative_356_);
v___x_360_ = lean_box(1);
v___f_361_ = lean_alloc_closure((void*)(l_Lean_getErrorExplanation_x3f___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_361_, 0, v___x_360_);
lean_closure_set(v___f_361_, 1, v_name_355_);
lean_closure_set(v___f_361_, 2, v_toPure_359_);
v___x_362_ = lean_apply_4(v_toBind_357_, lean_box(0), lean_box(0), v_getEnv_358_, v___f_361_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanation_x3f(lean_object* v_m_363_, lean_object* v_inst_364_, lean_object* v_inst_365_, lean_object* v_name_366_){
_start:
{
lean_object* v___x_367_; 
v___x_367_ = l_Lean_getErrorExplanation_x3f___redArg(v_inst_364_, v_inst_365_, v_name_366_);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanationRaw_x3f(lean_object* v_env_368_, lean_object* v_name_369_){
_start:
{
lean_object* v___x_370_; lean_object* v_toEnvExtension_371_; lean_object* v_asyncMode_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_370_ = l_Lean_errorExplanationExt;
v_toEnvExtension_371_ = lean_ctor_get(v___x_370_, 0);
v_asyncMode_372_ = lean_ctor_get(v_toEnvExtension_371_, 2);
v___x_373_ = lean_box(1);
v___x_374_ = lean_box(0);
v___x_375_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_373_, v___x_370_, v_env_368_, v_asyncMode_372_, v___x_374_);
v___x_376_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_375_, v_name_369_);
lean_dec(v___x_375_);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanationRaw_x3f___boxed(lean_object* v_env_377_, lean_object* v_name_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l_Lean_getErrorExplanationRaw_x3f(v_env_377_, v_name_378_);
lean_dec(v_name_378_);
return v_res_379_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasErrorExplanation___redArg___lam__0(lean_object* v___x_380_, lean_object* v_name_381_, lean_object* v_toPure_382_, lean_object* v_____do__lift_383_){
_start:
{
lean_object* v___x_384_; lean_object* v_toEnvExtension_385_; lean_object* v_asyncMode_386_; lean_object* v___x_387_; lean_object* v___x_388_; uint8_t v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; 
v___x_384_ = l_Lean_errorExplanationExt;
v_toEnvExtension_385_ = lean_ctor_get(v___x_384_, 0);
v_asyncMode_386_ = lean_ctor_get(v_toEnvExtension_385_, 2);
v___x_387_ = lean_box(0);
v___x_388_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_380_, v___x_384_, v_____do__lift_383_, v_asyncMode_386_, v___x_387_);
v___x_389_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_name_381_, v___x_388_);
lean_dec(v___x_388_);
v___x_390_ = lean_box(v___x_389_);
v___x_391_ = lean_apply_2(v_toPure_382_, lean_box(0), v___x_390_);
return v___x_391_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasErrorExplanation___redArg___lam__0___boxed(lean_object* v___x_392_, lean_object* v_name_393_, lean_object* v_toPure_394_, lean_object* v_____do__lift_395_){
_start:
{
lean_object* v_res_396_; 
v_res_396_ = l_Lean_hasErrorExplanation___redArg___lam__0(v___x_392_, v_name_393_, v_toPure_394_, v_____do__lift_395_);
lean_dec(v_name_393_);
return v_res_396_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasErrorExplanation___redArg(lean_object* v_inst_397_, lean_object* v_inst_398_, lean_object* v_name_399_){
_start:
{
lean_object* v_toApplicative_400_; lean_object* v_toBind_401_; lean_object* v_getEnv_402_; lean_object* v_toPure_403_; lean_object* v___x_404_; lean_object* v___f_405_; lean_object* v___x_406_; 
v_toApplicative_400_ = lean_ctor_get(v_inst_397_, 0);
lean_inc_ref(v_toApplicative_400_);
v_toBind_401_ = lean_ctor_get(v_inst_397_, 1);
lean_inc(v_toBind_401_);
lean_dec_ref(v_inst_397_);
v_getEnv_402_ = lean_ctor_get(v_inst_398_, 0);
lean_inc(v_getEnv_402_);
lean_dec_ref(v_inst_398_);
v_toPure_403_ = lean_ctor_get(v_toApplicative_400_, 1);
lean_inc(v_toPure_403_);
lean_dec_ref(v_toApplicative_400_);
v___x_404_ = lean_box(1);
v___f_405_ = lean_alloc_closure((void*)(l_Lean_hasErrorExplanation___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_405_, 0, v___x_404_);
lean_closure_set(v___f_405_, 1, v_name_399_);
lean_closure_set(v___f_405_, 2, v_toPure_403_);
v___x_406_ = lean_apply_4(v_toBind_401_, lean_box(0), lean_box(0), v_getEnv_402_, v___f_405_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasErrorExplanation(lean_object* v_m_407_, lean_object* v_inst_408_, lean_object* v_inst_409_, lean_object* v_name_410_){
_start:
{
lean_object* v___x_411_; 
v___x_411_ = l_Lean_hasErrorExplanation___redArg(v_inst_408_, v_inst_409_, v_name_410_);
return v___x_411_;
}
}
LEAN_EXPORT uint8_t l_Lean_getErrorExplanations___redArg___lam__0(lean_object* v_e_412_, lean_object* v_e_x27_413_){
_start:
{
lean_object* v_fst_414_; lean_object* v_fst_415_; uint8_t v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; uint8_t v___x_419_; 
v_fst_414_ = lean_ctor_get(v_e_412_, 0);
lean_inc(v_fst_414_);
lean_dec_ref(v_e_412_);
v_fst_415_ = lean_ctor_get(v_e_x27_413_, 0);
lean_inc(v_fst_415_);
lean_dec_ref(v_e_x27_413_);
v___x_416_ = 1;
v___x_417_ = l_Lean_Name_toString(v_fst_414_, v___x_416_);
v___x_418_ = l_Lean_Name_toString(v_fst_415_, v___x_416_);
v___x_419_ = lean_string_dec_lt(v___x_417_, v___x_418_);
lean_dec_ref(v___x_418_);
lean_dec_ref(v___x_417_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanations___redArg___lam__0___boxed(lean_object* v_e_420_, lean_object* v_e_x27_421_){
_start:
{
uint8_t v_res_422_; lean_object* v_r_423_; 
v_res_422_ = l_Lean_getErrorExplanations___redArg___lam__0(v_e_420_, v_e_x27_421_);
v_r_423_ = lean_box(v_res_422_);
return v_r_423_;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanations___redArg___lam__1(lean_object* v_acc_424_, lean_object* v_k_425_, lean_object* v_v_426_){
_start:
{
lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_427_, 0, v_k_425_);
lean_ctor_set(v___x_427_, 1, v_v_426_);
v___x_428_ = lean_array_push(v_acc_424_, v___x_427_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanations___redArg___lam__2(lean_object* v___x_431_, lean_object* v___f_432_, lean_object* v___f_433_, lean_object* v_toPure_434_, lean_object* v_____do__lift_435_){
_start:
{
lean_object* v___x_436_; lean_object* v_toEnvExtension_437_; lean_object* v_asyncMode_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___y_446_; lean_object* v___y_447_; uint8_t v___x_450_; 
v___x_436_ = l_Lean_errorExplanationExt;
v_toEnvExtension_437_ = lean_ctor_get(v___x_436_, 0);
v_asyncMode_438_ = lean_ctor_get(v_toEnvExtension_437_, 2);
v___x_439_ = lean_box(0);
v___x_440_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_431_, v___x_436_, v_____do__lift_435_, v_asyncMode_438_, v___x_439_);
v___x_441_ = lean_unsigned_to_nat(0u);
v___x_442_ = ((lean_object*)(l_Lean_getErrorExplanations___redArg___lam__2___closed__0));
v___x_443_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_432_, v___x_442_, v___x_440_);
v___x_444_ = lean_array_get_size(v___x_443_);
v___x_450_ = lean_nat_dec_eq(v___x_444_, v___x_441_);
if (v___x_450_ == 0)
{
lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___y_454_; uint8_t v___x_456_; 
v___x_451_ = lean_unsigned_to_nat(1u);
v___x_452_ = lean_nat_sub(v___x_444_, v___x_451_);
v___x_456_ = lean_nat_dec_le(v___x_441_, v___x_452_);
if (v___x_456_ == 0)
{
lean_inc(v___x_452_);
v___y_454_ = v___x_452_;
goto v___jp_453_;
}
else
{
v___y_454_ = v___x_441_;
goto v___jp_453_;
}
v___jp_453_:
{
uint8_t v___x_455_; 
v___x_455_ = lean_nat_dec_le(v___y_454_, v___x_452_);
if (v___x_455_ == 0)
{
lean_dec(v___x_452_);
lean_inc(v___y_454_);
v___y_446_ = v___y_454_;
v___y_447_ = v___y_454_;
goto v___jp_445_;
}
else
{
v___y_446_ = v___y_454_;
v___y_447_ = v___x_452_;
goto v___jp_445_;
}
}
}
else
{
lean_object* v___x_457_; 
lean_dec_ref(v___f_433_);
v___x_457_ = lean_apply_2(v_toPure_434_, lean_box(0), v___x_443_);
return v___x_457_;
}
v___jp_445_:
{
lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_448_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___f_433_, v___x_444_, v___x_443_, v___y_446_, v___y_447_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___y_447_);
v___x_449_ = lean_apply_2(v_toPure_434_, lean_box(0), v___x_448_);
return v___x_449_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanations___redArg(lean_object* v_inst_460_, lean_object* v_inst_461_){
_start:
{
lean_object* v_toApplicative_462_; lean_object* v_toBind_463_; lean_object* v_getEnv_464_; lean_object* v_toPure_465_; lean_object* v___f_466_; lean_object* v___f_467_; lean_object* v___x_468_; lean_object* v___f_469_; lean_object* v___x_470_; 
v_toApplicative_462_ = lean_ctor_get(v_inst_460_, 0);
lean_inc_ref(v_toApplicative_462_);
v_toBind_463_ = lean_ctor_get(v_inst_460_, 1);
lean_inc(v_toBind_463_);
lean_dec_ref(v_inst_460_);
v_getEnv_464_ = lean_ctor_get(v_inst_461_, 0);
lean_inc(v_getEnv_464_);
lean_dec_ref(v_inst_461_);
v_toPure_465_ = lean_ctor_get(v_toApplicative_462_, 1);
lean_inc(v_toPure_465_);
lean_dec_ref(v_toApplicative_462_);
v___f_466_ = ((lean_object*)(l_Lean_getErrorExplanations___redArg___closed__0));
v___f_467_ = ((lean_object*)(l_Lean_getErrorExplanations___redArg___closed__1));
v___x_468_ = lean_box(1);
v___f_469_ = lean_alloc_closure((void*)(l_Lean_getErrorExplanations___redArg___lam__2), 5, 4);
lean_closure_set(v___f_469_, 0, v___x_468_);
lean_closure_set(v___f_469_, 1, v___f_467_);
lean_closure_set(v___f_469_, 2, v___f_466_);
lean_closure_set(v___f_469_, 3, v_toPure_465_);
v___x_470_ = lean_apply_4(v_toBind_463_, lean_box(0), lean_box(0), v_getEnv_464_, v___f_469_);
return v___x_470_;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanations(lean_object* v_m_471_, lean_object* v_inst_472_, lean_object* v_inst_473_){
_start:
{
lean_object* v___x_474_; 
v___x_474_ = l_Lean_getErrorExplanations___redArg(v_inst_472_, v_inst_473_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1_spec__2___redArg(lean_object* v_hi_475_, lean_object* v_pivot_476_, lean_object* v_as_477_, lean_object* v_i_478_, lean_object* v_k_479_){
_start:
{
uint8_t v___x_480_; 
v___x_480_ = lean_nat_dec_lt(v_k_479_, v_hi_475_);
if (v___x_480_ == 0)
{
lean_object* v___x_481_; lean_object* v___x_482_; 
lean_dec(v_k_479_);
lean_dec_ref(v_pivot_476_);
v___x_481_ = lean_array_fswap(v_as_477_, v_i_478_, v_hi_475_);
v___x_482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_482_, 0, v_i_478_);
lean_ctor_set(v___x_482_, 1, v___x_481_);
return v___x_482_;
}
else
{
lean_object* v___x_483_; lean_object* v_fst_484_; lean_object* v_fst_485_; lean_object* v___x_486_; lean_object* v___x_487_; uint8_t v___x_488_; 
v___x_483_ = lean_array_fget_borrowed(v_as_477_, v_k_479_);
v_fst_484_ = lean_ctor_get(v___x_483_, 0);
v_fst_485_ = lean_ctor_get(v_pivot_476_, 0);
lean_inc(v_fst_484_);
v___x_486_ = l_Lean_Name_toString(v_fst_484_, v___x_480_);
lean_inc(v_fst_485_);
v___x_487_ = l_Lean_Name_toString(v_fst_485_, v___x_480_);
v___x_488_ = lean_string_dec_lt(v___x_486_, v___x_487_);
lean_dec_ref(v___x_487_);
lean_dec_ref(v___x_486_);
if (v___x_488_ == 0)
{
lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_489_ = lean_unsigned_to_nat(1u);
v___x_490_ = lean_nat_add(v_k_479_, v___x_489_);
lean_dec(v_k_479_);
v_k_479_ = v___x_490_;
goto _start;
}
else
{
lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_492_ = lean_array_fswap(v_as_477_, v_i_478_, v_k_479_);
v___x_493_ = lean_unsigned_to_nat(1u);
v___x_494_ = lean_nat_add(v_i_478_, v___x_493_);
lean_dec(v_i_478_);
v___x_495_ = lean_nat_add(v_k_479_, v___x_493_);
lean_dec(v_k_479_);
v_as_477_ = v___x_492_;
v_i_478_ = v___x_494_;
v_k_479_ = v___x_495_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1_spec__2___redArg___boxed(lean_object* v_hi_497_, lean_object* v_pivot_498_, lean_object* v_as_499_, lean_object* v_i_500_, lean_object* v_k_501_){
_start:
{
lean_object* v_res_502_; 
v_res_502_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1_spec__2___redArg(v_hi_497_, v_pivot_498_, v_as_499_, v_i_500_, v_k_501_);
lean_dec(v_hi_497_);
return v_res_502_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1___redArg___lam__0(uint8_t v___x_503_, lean_object* v_e_504_, lean_object* v_e_x27_505_){
_start:
{
lean_object* v_fst_506_; lean_object* v_fst_507_; lean_object* v___x_508_; lean_object* v___x_509_; uint8_t v___x_510_; 
v_fst_506_ = lean_ctor_get(v_e_504_, 0);
lean_inc(v_fst_506_);
lean_dec_ref(v_e_504_);
v_fst_507_ = lean_ctor_get(v_e_x27_505_, 0);
lean_inc(v_fst_507_);
lean_dec_ref(v_e_x27_505_);
v___x_508_ = l_Lean_Name_toString(v_fst_506_, v___x_503_);
v___x_509_ = l_Lean_Name_toString(v_fst_507_, v___x_503_);
v___x_510_ = lean_string_dec_lt(v___x_508_, v___x_509_);
lean_dec_ref(v___x_509_);
lean_dec_ref(v___x_508_);
return v___x_510_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1___redArg___lam__0___boxed(lean_object* v___x_511_, lean_object* v_e_512_, lean_object* v_e_x27_513_){
_start:
{
uint8_t v___x_412__boxed_514_; uint8_t v_res_515_; lean_object* v_r_516_; 
v___x_412__boxed_514_ = lean_unbox(v___x_511_);
v_res_515_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1___redArg___lam__0(v___x_412__boxed_514_, v_e_512_, v_e_x27_513_);
v_r_516_ = lean_box(v_res_515_);
return v_r_516_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1___redArg(lean_object* v_n_517_, lean_object* v_as_518_, lean_object* v_lo_519_, lean_object* v_hi_520_){
_start:
{
lean_object* v___y_522_; uint8_t v___x_532_; 
v___x_532_ = lean_nat_dec_lt(v_lo_519_, v_hi_520_);
if (v___x_532_ == 0)
{
lean_dec(v_lo_519_);
return v_as_518_;
}
else
{
lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v_mid_535_; lean_object* v___y_537_; lean_object* v___y_543_; lean_object* v___x_548_; lean_object* v___x_549_; uint8_t v___x_550_; 
v___x_533_ = lean_nat_add(v_lo_519_, v_hi_520_);
v___x_534_ = lean_unsigned_to_nat(1u);
v_mid_535_ = lean_nat_shiftr(v___x_533_, v___x_534_);
lean_dec(v___x_533_);
v___x_548_ = lean_array_fget_borrowed(v_as_518_, v_mid_535_);
v___x_549_ = lean_array_fget_borrowed(v_as_518_, v_lo_519_);
lean_inc(v___x_549_);
lean_inc(v___x_548_);
v___x_550_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1___redArg___lam__0(v___x_532_, v___x_548_, v___x_549_);
if (v___x_550_ == 0)
{
v___y_543_ = v_as_518_;
goto v___jp_542_;
}
else
{
lean_object* v___x_551_; 
v___x_551_ = lean_array_fswap(v_as_518_, v_lo_519_, v_mid_535_);
v___y_543_ = v___x_551_;
goto v___jp_542_;
}
v___jp_536_:
{
lean_object* v___x_538_; lean_object* v___x_539_; uint8_t v___x_540_; 
v___x_538_ = lean_array_fget_borrowed(v___y_537_, v_mid_535_);
v___x_539_ = lean_array_fget_borrowed(v___y_537_, v_hi_520_);
lean_inc(v___x_539_);
lean_inc(v___x_538_);
v___x_540_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1___redArg___lam__0(v___x_532_, v___x_538_, v___x_539_);
if (v___x_540_ == 0)
{
lean_dec(v_mid_535_);
v___y_522_ = v___y_537_;
goto v___jp_521_;
}
else
{
lean_object* v___x_541_; 
v___x_541_ = lean_array_fswap(v___y_537_, v_mid_535_, v_hi_520_);
lean_dec(v_mid_535_);
v___y_522_ = v___x_541_;
goto v___jp_521_;
}
}
v___jp_542_:
{
lean_object* v___x_544_; lean_object* v___x_545_; uint8_t v___x_546_; 
v___x_544_ = lean_array_fget_borrowed(v___y_543_, v_hi_520_);
v___x_545_ = lean_array_fget_borrowed(v___y_543_, v_lo_519_);
lean_inc(v___x_545_);
lean_inc(v___x_544_);
v___x_546_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1___redArg___lam__0(v___x_532_, v___x_544_, v___x_545_);
if (v___x_546_ == 0)
{
v___y_537_ = v___y_543_;
goto v___jp_536_;
}
else
{
lean_object* v___x_547_; 
v___x_547_ = lean_array_fswap(v___y_543_, v_lo_519_, v_hi_520_);
v___y_537_ = v___x_547_;
goto v___jp_536_;
}
}
}
v___jp_521_:
{
lean_object* v_pivot_523_; lean_object* v___x_524_; lean_object* v_fst_525_; lean_object* v_snd_526_; uint8_t v___x_527_; 
v_pivot_523_ = lean_array_fget(v___y_522_, v_hi_520_);
lean_inc_n(v_lo_519_, 2);
v___x_524_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1_spec__2___redArg(v_hi_520_, v_pivot_523_, v___y_522_, v_lo_519_, v_lo_519_);
v_fst_525_ = lean_ctor_get(v___x_524_, 0);
lean_inc(v_fst_525_);
v_snd_526_ = lean_ctor_get(v___x_524_, 1);
lean_inc(v_snd_526_);
lean_dec_ref(v___x_524_);
v___x_527_ = lean_nat_dec_le(v_hi_520_, v_fst_525_);
if (v___x_527_ == 0)
{
lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_528_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1___redArg(v_n_517_, v_snd_526_, v_lo_519_, v_fst_525_);
v___x_529_ = lean_unsigned_to_nat(1u);
v___x_530_ = lean_nat_add(v_fst_525_, v___x_529_);
lean_dec(v_fst_525_);
v_as_518_ = v___x_528_;
v_lo_519_ = v___x_530_;
goto _start;
}
else
{
lean_dec(v_fst_525_);
lean_dec(v_lo_519_);
return v_snd_526_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1___redArg___boxed(lean_object* v_n_552_, lean_object* v_as_553_, lean_object* v_lo_554_, lean_object* v_hi_555_){
_start:
{
lean_object* v_res_556_; 
v_res_556_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1___redArg(v_n_552_, v_as_553_, v_lo_554_, v_hi_555_);
lean_dec(v_hi_555_);
lean_dec(v_n_552_);
return v_res_556_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanationsRaw_spec__0_spec__0(lean_object* v_init_557_, lean_object* v_x_558_){
_start:
{
if (lean_obj_tag(v_x_558_) == 0)
{
lean_object* v_k_559_; lean_object* v_v_560_; lean_object* v_l_561_; lean_object* v_r_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; 
v_k_559_ = lean_ctor_get(v_x_558_, 1);
v_v_560_ = lean_ctor_get(v_x_558_, 2);
v_l_561_ = lean_ctor_get(v_x_558_, 3);
v_r_562_ = lean_ctor_get(v_x_558_, 4);
v___x_563_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanationsRaw_spec__0_spec__0(v_init_557_, v_l_561_);
lean_inc(v_v_560_);
lean_inc(v_k_559_);
v___x_564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_564_, 0, v_k_559_);
lean_ctor_set(v___x_564_, 1, v_v_560_);
v___x_565_ = lean_array_push(v___x_563_, v___x_564_);
v_init_557_ = v___x_565_;
v_x_558_ = v_r_562_;
goto _start;
}
else
{
return v_init_557_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanationsRaw_spec__0_spec__0___boxed(lean_object* v_init_567_, lean_object* v_x_568_){
_start:
{
lean_object* v_res_569_; 
v_res_569_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanationsRaw_spec__0_spec__0(v_init_567_, v_x_568_);
lean_dec(v_x_568_);
return v_res_569_;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanationsRaw(lean_object* v_env_570_){
_start:
{
lean_object* v___x_571_; lean_object* v_toEnvExtension_572_; lean_object* v_asyncMode_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; uint8_t v___x_581_; 
v___x_571_ = l_Lean_errorExplanationExt;
v_toEnvExtension_572_ = lean_ctor_get(v___x_571_, 0);
v_asyncMode_573_ = lean_ctor_get(v_toEnvExtension_572_, 2);
v___x_574_ = lean_box(1);
v___x_575_ = lean_box(0);
v___x_576_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_574_, v___x_571_, v_env_570_, v_asyncMode_573_, v___x_575_);
v___x_577_ = lean_unsigned_to_nat(0u);
v___x_578_ = ((lean_object*)(l_Lean_getErrorExplanations___redArg___lam__2___closed__0));
v___x_579_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanationsRaw_spec__0_spec__0(v___x_578_, v___x_576_);
lean_dec(v___x_576_);
v___x_580_ = lean_array_get_size(v___x_579_);
v___x_581_ = lean_nat_dec_eq(v___x_580_, v___x_577_);
if (v___x_581_ == 0)
{
lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___y_585_; uint8_t v___x_589_; 
v___x_582_ = lean_unsigned_to_nat(1u);
v___x_583_ = lean_nat_sub(v___x_580_, v___x_582_);
v___x_589_ = lean_nat_dec_le(v___x_577_, v___x_583_);
if (v___x_589_ == 0)
{
lean_inc(v___x_583_);
v___y_585_ = v___x_583_;
goto v___jp_584_;
}
else
{
v___y_585_ = v___x_577_;
goto v___jp_584_;
}
v___jp_584_:
{
uint8_t v___x_586_; 
v___x_586_ = lean_nat_dec_le(v___y_585_, v___x_583_);
if (v___x_586_ == 0)
{
lean_object* v___x_587_; 
lean_dec(v___x_583_);
lean_inc(v___y_585_);
v___x_587_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1___redArg(v___x_580_, v___x_579_, v___y_585_, v___y_585_);
lean_dec(v___y_585_);
return v___x_587_;
}
else
{
lean_object* v___x_588_; 
v___x_588_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1___redArg(v___x_580_, v___x_579_, v___y_585_, v___x_583_);
lean_dec(v___x_583_);
return v___x_588_;
}
}
}
else
{
return v___x_579_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanationsRaw_spec__0(lean_object* v_init_590_, lean_object* v_t_591_){
_start:
{
lean_object* v___x_592_; 
v___x_592_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanationsRaw_spec__0_spec__0(v_init_590_, v_t_591_);
return v___x_592_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanationsRaw_spec__0___boxed(lean_object* v_init_593_, lean_object* v_t_594_){
_start:
{
lean_object* v_res_595_; 
v_res_595_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanationsRaw_spec__0(v_init_593_, v_t_594_);
lean_dec(v_t_594_);
return v_res_595_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1(lean_object* v_n_596_, lean_object* v_as_597_, lean_object* v_lo_598_, lean_object* v_hi_599_, lean_object* v_w_600_, lean_object* v_hlo_601_, lean_object* v_hhi_602_){
_start:
{
lean_object* v___x_603_; 
v___x_603_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1___redArg(v_n_596_, v_as_597_, v_lo_598_, v_hi_599_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1___boxed(lean_object* v_n_604_, lean_object* v_as_605_, lean_object* v_lo_606_, lean_object* v_hi_607_, lean_object* v_w_608_, lean_object* v_hlo_609_, lean_object* v_hhi_610_){
_start:
{
lean_object* v_res_611_; 
v_res_611_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1(v_n_604_, v_as_605_, v_lo_606_, v_hi_607_, v_w_608_, v_hlo_609_, v_hhi_610_);
lean_dec(v_hi_607_);
lean_dec(v_n_604_);
return v_res_611_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1_spec__2(lean_object* v_n_612_, lean_object* v_lo_613_, lean_object* v_hi_614_, lean_object* v_hhi_615_, lean_object* v_pivot_616_, lean_object* v_as_617_, lean_object* v_i_618_, lean_object* v_k_619_, lean_object* v_ilo_620_, lean_object* v_ik_621_, lean_object* v_w_622_){
_start:
{
lean_object* v___x_623_; 
v___x_623_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1_spec__2___redArg(v_hi_614_, v_pivot_616_, v_as_617_, v_i_618_, v_k_619_);
return v___x_623_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1_spec__2___boxed(lean_object* v_n_624_, lean_object* v_lo_625_, lean_object* v_hi_626_, lean_object* v_hhi_627_, lean_object* v_pivot_628_, lean_object* v_as_629_, lean_object* v_i_630_, lean_object* v_k_631_, lean_object* v_ilo_632_, lean_object* v_ik_633_, lean_object* v_w_634_){
_start:
{
lean_object* v_res_635_; 
v_res_635_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1_spec__2(v_n_624_, v_lo_625_, v_hi_626_, v_hhi_627_, v_pivot_628_, v_as_629_, v_i_630_, v_k_631_, v_ilo_632_, v_ik_633_, v_w_634_);
lean_dec(v_hi_626_);
lean_dec(v_lo_625_);
lean_dec(v_n_624_);
return v_res_635_;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanationsSorted___redArg(lean_object* v_inst_636_, lean_object* v_inst_637_){
_start:
{
lean_object* v___x_638_; 
v___x_638_ = l_Lean_getErrorExplanations___redArg(v_inst_636_, v_inst_637_);
return v___x_638_;
}
}
LEAN_EXPORT lean_object* l_Lean_getErrorExplanationsSorted(lean_object* v_m_639_, lean_object* v_inst_640_, lean_object* v_inst_641_){
_start:
{
lean_object* v___x_642_; 
v___x_642_ = l_Lean_getErrorExplanations___redArg(v_inst_640_, v_inst_641_);
return v___x_642_;
}
}
lean_object* runtime_initialize_Lean_Message(uint8_t builtin);
lean_object* runtime_initialize_Lean_EnvExtension(uint8_t builtin);
lean_object* runtime_initialize_Lean_DocString_Links(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_ErrorExplanation(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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

// Lean compiler output
// Module: Lean.Util.Profiler
// Imports: public import Lean.Util.Trace import Init.Data.Range.Polymorphic.Iterators
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
double lean_uint64_to_float(uint64_t);
static lean_once_cell_t l_Lean_Firefox_instInhabitedMilliseconds_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_Firefox_instInhabitedMilliseconds_default___closed__0;
LEAN_EXPORT double l_Lean_Firefox_instInhabitedMilliseconds_default;
LEAN_EXPORT double l_Lean_Firefox_instInhabitedMilliseconds;
double lean_float_of_nat(lean_object*);
static lean_once_cell_t l_Lean_Firefox_instCoeFloatMilliseconds___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_Firefox_instCoeFloatMilliseconds___lam__0___closed__0;
double lean_float_mul(double, double);
LEAN_EXPORT double l_Lean_Firefox_instCoeFloatMilliseconds___lam__0(double);
LEAN_EXPORT lean_object* l_Lean_Firefox_instCoeFloatMilliseconds___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Firefox_instCoeFloatMilliseconds___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Firefox_instCoeFloatMilliseconds___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Firefox_instCoeFloatMilliseconds___closed__0 = (const lean_object*)&l_Lean_Firefox_instCoeFloatMilliseconds___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Firefox_instCoeFloatMilliseconds = (const lean_object*)&l_Lean_Firefox_instCoeFloatMilliseconds___closed__0_value;
lean_object* l_Float_ofScientific___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Firefox_instOfScientificMilliseconds___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Float_ofScientific___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Firefox_instOfScientificMilliseconds___closed__0 = (const lean_object*)&l_Lean_Firefox_instOfScientificMilliseconds___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Firefox_instOfScientificMilliseconds = (const lean_object*)&l_Lean_Firefox_instOfScientificMilliseconds___closed__0_value;
lean_object* l_Float_toJson___boxed(lean_object*);
static const lean_closure_object l_Lean_Firefox_instToJsonMilliseconds___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Float_toJson___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Firefox_instToJsonMilliseconds___closed__0 = (const lean_object*)&l_Lean_Firefox_instToJsonMilliseconds___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Firefox_instToJsonMilliseconds = (const lean_object*)&l_Lean_Firefox_instToJsonMilliseconds___closed__0_value;
lean_object* l_Float_fromJson_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Firefox_instFromJsonMilliseconds___lam__0(lean_object*);
static const lean_closure_object l_Lean_Firefox_instFromJsonMilliseconds___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Firefox_instFromJsonMilliseconds___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Firefox_instFromJsonMilliseconds___closed__0 = (const lean_object*)&l_Lean_Firefox_instFromJsonMilliseconds___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Firefox_instFromJsonMilliseconds = (const lean_object*)&l_Lean_Firefox_instFromJsonMilliseconds___closed__0_value;
lean_object* l_Float_add___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Firefox_instAddMilliseconds___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Float_add___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Firefox_instAddMilliseconds___closed__0 = (const lean_object*)&l_Lean_Firefox_instAddMilliseconds___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Firefox_instAddMilliseconds = (const lean_object*)&l_Lean_Firefox_instAddMilliseconds___closed__0_value;
static lean_once_cell_t l_Lean_Firefox_instCoeFloatMicroseconds___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_Firefox_instCoeFloatMicroseconds___lam__0___closed__0;
LEAN_EXPORT double l_Lean_Firefox_instCoeFloatMicroseconds___lam__0(double);
LEAN_EXPORT lean_object* l_Lean_Firefox_instCoeFloatMicroseconds___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Firefox_instCoeFloatMicroseconds___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Firefox_instCoeFloatMicroseconds___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Firefox_instCoeFloatMicroseconds___closed__0 = (const lean_object*)&l_Lean_Firefox_instCoeFloatMicroseconds___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Firefox_instCoeFloatMicroseconds = (const lean_object*)&l_Lean_Firefox_instCoeFloatMicroseconds___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Firefox_instOfScientificMicroseconds = (const lean_object*)&l_Lean_Firefox_instOfScientificMilliseconds___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Firefox_instToJsonMicroseconds = (const lean_object*)&l_Lean_Firefox_instToJsonMilliseconds___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Firefox_instFromJsonMicroseconds = (const lean_object*)&l_Lean_Firefox_instFromJsonMilliseconds___closed__0_value;
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
lean_object* l_Lean_Name_fromJson_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__1___boxed(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__2_spec__2_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__2_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__2_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "expected JSON array, got '"};
static const lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__2_spec__2___closed__0 = (const lean_object*)&l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__2_spec__2___closed__0_value;
static const lean_string_object l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__2_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__2_spec__2___closed__1 = (const lean_object*)&l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__2_spec__2___closed__1_value;
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__2_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__2___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Firefox_instFromJsonCategory_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "name"};
static const lean_object* l_Lean_Firefox_instFromJsonCategory_fromJson___closed__0 = (const lean_object*)&l_Lean_Firefox_instFromJsonCategory_fromJson___closed__0_value;
static const lean_string_object l_Lean_Firefox_instFromJsonCategory_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Firefox_instFromJsonCategory_fromJson___closed__1 = (const lean_object*)&l_Lean_Firefox_instFromJsonCategory_fromJson___closed__1_value;
static const lean_string_object l_Lean_Firefox_instFromJsonCategory_fromJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Firefox"};
static const lean_object* l_Lean_Firefox_instFromJsonCategory_fromJson___closed__2 = (const lean_object*)&l_Lean_Firefox_instFromJsonCategory_fromJson___closed__2_value;
static const lean_string_object l_Lean_Firefox_instFromJsonCategory_fromJson___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Category"};
static const lean_object* l_Lean_Firefox_instFromJsonCategory_fromJson___closed__3 = (const lean_object*)&l_Lean_Firefox_instFromJsonCategory_fromJson___closed__3_value;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Firefox_instFromJsonCategory_fromJson___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Firefox_instFromJsonCategory_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Firefox_instFromJsonCategory_fromJson___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Firefox_instFromJsonCategory_fromJson___closed__4_value_aux_0),((lean_object*)&l_Lean_Firefox_instFromJsonCategory_fromJson___closed__2_value),LEAN_SCALAR_PTR_LITERAL(1, 221, 142, 98, 103, 73, 209, 133)}};
static const lean_ctor_object l_Lean_Firefox_instFromJsonCategory_fromJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Firefox_instFromJsonCategory_fromJson___closed__4_value_aux_1),((lean_object*)&l_Lean_Firefox_instFromJsonCategory_fromJson___closed__3_value),LEAN_SCALAR_PTR_LITERAL(218, 120, 30, 24, 139, 24, 153, 254)}};
static const lean_object* l_Lean_Firefox_instFromJsonCategory_fromJson___closed__4 = (const lean_object*)&l_Lean_Firefox_instFromJsonCategory_fromJson___closed__4_value;
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
static lean_once_cell_t l_Lean_Firefox_instFromJsonCategory_fromJson___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonCategory_fromJson___closed__5;
static const lean_string_object l_Lean_Firefox_instFromJsonCategory_fromJson___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lean_Firefox_instFromJsonCategory_fromJson___closed__6 = (const lean_object*)&l_Lean_Firefox_instFromJsonCategory_fromJson___closed__6_value;
static lean_once_cell_t l_Lean_Firefox_instFromJsonCategory_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonCategory_fromJson___closed__7;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_Lean_Firefox_instFromJsonCategory_fromJson___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Firefox_instFromJsonCategory_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(84, 246, 234, 130, 97, 205, 144, 82)}};
static const lean_object* l_Lean_Firefox_instFromJsonCategory_fromJson___closed__8 = (const lean_object*)&l_Lean_Firefox_instFromJsonCategory_fromJson___closed__8_value;
static lean_once_cell_t l_Lean_Firefox_instFromJsonCategory_fromJson___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonCategory_fromJson___closed__9;
static lean_once_cell_t l_Lean_Firefox_instFromJsonCategory_fromJson___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonCategory_fromJson___closed__10;
static const lean_string_object l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11 = (const lean_object*)&l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11_value;
static lean_once_cell_t l_Lean_Firefox_instFromJsonCategory_fromJson___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonCategory_fromJson___closed__12;
static const lean_string_object l_Lean_Firefox_instFromJsonCategory_fromJson___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "color"};
static const lean_object* l_Lean_Firefox_instFromJsonCategory_fromJson___closed__13 = (const lean_object*)&l_Lean_Firefox_instFromJsonCategory_fromJson___closed__13_value;
static const lean_ctor_object l_Lean_Firefox_instFromJsonCategory_fromJson___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Firefox_instFromJsonCategory_fromJson___closed__13_value),LEAN_SCALAR_PTR_LITERAL(203, 195, 165, 168, 25, 61, 235, 188)}};
static const lean_object* l_Lean_Firefox_instFromJsonCategory_fromJson___closed__14 = (const lean_object*)&l_Lean_Firefox_instFromJsonCategory_fromJson___closed__14_value;
static lean_once_cell_t l_Lean_Firefox_instFromJsonCategory_fromJson___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonCategory_fromJson___closed__15;
static lean_once_cell_t l_Lean_Firefox_instFromJsonCategory_fromJson___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonCategory_fromJson___closed__16;
static lean_once_cell_t l_Lean_Firefox_instFromJsonCategory_fromJson___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonCategory_fromJson___closed__17;
static const lean_string_object l_Lean_Firefox_instFromJsonCategory_fromJson___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "subcategories"};
static const lean_object* l_Lean_Firefox_instFromJsonCategory_fromJson___closed__18 = (const lean_object*)&l_Lean_Firefox_instFromJsonCategory_fromJson___closed__18_value;
static const lean_ctor_object l_Lean_Firefox_instFromJsonCategory_fromJson___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Firefox_instFromJsonCategory_fromJson___closed__18_value),LEAN_SCALAR_PTR_LITERAL(185, 42, 176, 165, 28, 119, 142, 51)}};
static const lean_object* l_Lean_Firefox_instFromJsonCategory_fromJson___closed__19 = (const lean_object*)&l_Lean_Firefox_instFromJsonCategory_fromJson___closed__19_value;
static lean_once_cell_t l_Lean_Firefox_instFromJsonCategory_fromJson___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonCategory_fromJson___closed__20;
static lean_once_cell_t l_Lean_Firefox_instFromJsonCategory_fromJson___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonCategory_fromJson___closed__21;
static lean_once_cell_t l_Lean_Firefox_instFromJsonCategory_fromJson___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonCategory_fromJson___closed__22;
LEAN_EXPORT lean_object* l_Lean_Firefox_instFromJsonCategory_fromJson(lean_object*);
static const lean_closure_object l_Lean_Firefox_instFromJsonCategory___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Firefox_instFromJsonCategory_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Firefox_instFromJsonCategory___closed__0 = (const lean_object*)&l_Lean_Firefox_instFromJsonCategory___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Firefox_instFromJsonCategory = (const lean_object*)&l_Lean_Firefox_instFromJsonCategory___closed__0_value;
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Firefox_instToJsonCategory_toJson_spec__0_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Firefox_instToJsonCategory_toJson_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Firefox_instToJsonCategory_toJson_spec__0(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Firefox_instToJsonCategory_toJson_spec__1(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static const lean_array_object l_Lean_Firefox_instToJsonCategory_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Firefox_instToJsonCategory_toJson___closed__0 = (const lean_object*)&l_Lean_Firefox_instToJsonCategory_toJson___closed__0_value;
lean_object* l_Lean_Json_mkObj(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Firefox_instToJsonCategory_toJson(lean_object*);
static const lean_closure_object l_Lean_Firefox_instToJsonCategory___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Firefox_instToJsonCategory_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Firefox_instToJsonCategory___closed__0 = (const lean_object*)&l_Lean_Firefox_instToJsonCategory___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Firefox_instToJsonCategory = (const lean_object*)&l_Lean_Firefox_instToJsonCategory___closed__0_value;
static const lean_string_object l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "time"};
static const lean_object* l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__0 = (const lean_object*)&l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__0_value;
static const lean_string_object l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "SampleUnits"};
static const lean_object* l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__1 = (const lean_object*)&l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__1_value;
static const lean_ctor_object l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Firefox_instFromJsonCategory_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__2_value_aux_0),((lean_object*)&l_Lean_Firefox_instFromJsonCategory_fromJson___closed__2_value),LEAN_SCALAR_PTR_LITERAL(1, 221, 142, 98, 103, 73, 209, 133)}};
static const lean_ctor_object l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__2_value_aux_1),((lean_object*)&l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(97, 0, 104, 60, 59, 103, 69, 138)}};
static const lean_object* l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__2 = (const lean_object*)&l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__2_value;
static lean_once_cell_t l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__3;
static lean_once_cell_t l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__4;
static const lean_ctor_object l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(56, 112, 168, 204, 144, 87, 251, 76)}};
static const lean_object* l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__5 = (const lean_object*)&l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__5_value;
static lean_once_cell_t l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__6;
static lean_once_cell_t l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__7;
static lean_once_cell_t l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__8;
static const lean_string_object l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "eventDelay"};
static const lean_object* l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__9 = (const lean_object*)&l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__9_value;
static const lean_ctor_object l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__9_value),LEAN_SCALAR_PTR_LITERAL(54, 151, 14, 109, 104, 160, 110, 2)}};
static const lean_object* l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__10 = (const lean_object*)&l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__10_value;
static lean_once_cell_t l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__11;
static lean_once_cell_t l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__12;
static lean_once_cell_t l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__13;
static const lean_string_object l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "threadCPUDelta"};
static const lean_object* l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__14 = (const lean_object*)&l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__14_value;
static const lean_ctor_object l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__14_value),LEAN_SCALAR_PTR_LITERAL(51, 96, 195, 43, 254, 127, 7, 124)}};
static const lean_object* l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__15 = (const lean_object*)&l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__15_value;
static lean_once_cell_t l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__16;
static lean_once_cell_t l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__17;
static lean_once_cell_t l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__18;
LEAN_EXPORT lean_object* l_Lean_Firefox_instFromJsonSampleUnits_fromJson(lean_object*);
static const lean_closure_object l_Lean_Firefox_instFromJsonSampleUnits___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Firefox_instFromJsonSampleUnits_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Firefox_instFromJsonSampleUnits___closed__0 = (const lean_object*)&l_Lean_Firefox_instFromJsonSampleUnits___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Firefox_instFromJsonSampleUnits = (const lean_object*)&l_Lean_Firefox_instFromJsonSampleUnits___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Firefox_instToJsonSampleUnits_toJson(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Firefox_instToJsonSampleUnits_toJson___boxed(lean_object*);
static const lean_closure_object l_Lean_Firefox_instToJsonSampleUnits___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Firefox_instToJsonSampleUnits_toJson___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Firefox_instToJsonSampleUnits___closed__0 = (const lean_object*)&l_Lean_Firefox_instToJsonSampleUnits___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Firefox_instToJsonSampleUnits = (const lean_object*)&l_Lean_Firefox_instToJsonSampleUnits___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Json_getNat_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__1_spec__1_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__1_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__1_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__3_spec__4_spec__7(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__3_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__3_spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__3___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "interval"};
static const lean_object* l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__0 = (const lean_object*)&l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__0_value;
static const lean_string_object l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "ProfileMeta"};
static const lean_object* l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__1 = (const lean_object*)&l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__1_value;
static const lean_ctor_object l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Firefox_instFromJsonCategory_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__2_value_aux_0),((lean_object*)&l_Lean_Firefox_instFromJsonCategory_fromJson___closed__2_value),LEAN_SCALAR_PTR_LITERAL(1, 221, 142, 98, 103, 73, 209, 133)}};
static const lean_ctor_object l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__2_value_aux_1),((lean_object*)&l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(148, 18, 28, 145, 40, 39, 105, 36)}};
static const lean_object* l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__2 = (const lean_object*)&l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__2_value;
static lean_once_cell_t l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__3;
static lean_once_cell_t l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__4;
static const lean_ctor_object l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(21, 2, 108, 181, 46, 130, 183, 240)}};
static const lean_object* l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__5 = (const lean_object*)&l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__5_value;
static lean_once_cell_t l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__6;
static lean_once_cell_t l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__7;
static lean_once_cell_t l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__8;
static const lean_string_object l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "startTime"};
static const lean_object* l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__9 = (const lean_object*)&l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__9_value;
static const lean_ctor_object l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__9_value),LEAN_SCALAR_PTR_LITERAL(130, 175, 170, 8, 182, 39, 106, 12)}};
static const lean_object* l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__10 = (const lean_object*)&l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__10_value;
static lean_once_cell_t l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__11;
static lean_once_cell_t l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__12;
static lean_once_cell_t l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__13;
static const lean_string_object l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "categories"};
static const lean_object* l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__14 = (const lean_object*)&l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__14_value;
static const lean_ctor_object l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__14_value),LEAN_SCALAR_PTR_LITERAL(193, 246, 48, 243, 86, 12, 99, 82)}};
static const lean_object* l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__15 = (const lean_object*)&l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__15_value;
static lean_once_cell_t l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__16;
static lean_once_cell_t l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__17;
static lean_once_cell_t l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__18;
static const lean_string_object l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "processType"};
static const lean_object* l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__19 = (const lean_object*)&l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__19_value;
static const lean_ctor_object l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__19_value),LEAN_SCALAR_PTR_LITERAL(137, 102, 121, 51, 14, 126, 128, 169)}};
static const lean_object* l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__20 = (const lean_object*)&l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__20_value;
static lean_once_cell_t l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__21;
static lean_once_cell_t l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__22;
static lean_once_cell_t l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__23;
static const lean_string_object l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "product"};
static const lean_object* l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__24 = (const lean_object*)&l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__24_value;
static const lean_ctor_object l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__24_value),LEAN_SCALAR_PTR_LITERAL(237, 49, 235, 171, 3, 189, 139, 77)}};
static const lean_object* l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__25 = (const lean_object*)&l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__25_value;
static lean_once_cell_t l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__26;
static lean_once_cell_t l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__27;
static lean_once_cell_t l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__28;
static const lean_string_object l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "preprocessedProfileVersion"};
static const lean_object* l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__29 = (const lean_object*)&l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__29_value;
static const lean_ctor_object l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__29_value),LEAN_SCALAR_PTR_LITERAL(22, 49, 187, 208, 115, 222, 145, 76)}};
static const lean_object* l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__30 = (const lean_object*)&l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__30_value;
static lean_once_cell_t l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__31;
static lean_once_cell_t l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__32;
static lean_once_cell_t l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__33;
static const lean_string_object l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "markerSchema"};
static const lean_object* l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__34 = (const lean_object*)&l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__34_value;
static const lean_ctor_object l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__34_value),LEAN_SCALAR_PTR_LITERAL(28, 255, 227, 193, 2, 100, 254, 75)}};
static const lean_object* l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__35 = (const lean_object*)&l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__35_value;
static lean_once_cell_t l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__36;
static lean_once_cell_t l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__37;
static lean_once_cell_t l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__38_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__38;
static const lean_string_object l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "sampleUnits"};
static const lean_object* l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__39 = (const lean_object*)&l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__39_value;
static const lean_ctor_object l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__39_value),LEAN_SCALAR_PTR_LITERAL(7, 111, 95, 112, 159, 182, 115, 44)}};
static const lean_object* l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__40 = (const lean_object*)&l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__40_value;
static lean_once_cell_t l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__41_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__41;
static lean_once_cell_t l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__42_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__42;
static lean_once_cell_t l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__43_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__43;
LEAN_EXPORT lean_object* l_Lean_Firefox_instFromJsonProfileMeta_fromJson(lean_object*);
static const lean_closure_object l_Lean_Firefox_instFromJsonProfileMeta___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Firefox_instFromJsonProfileMeta_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Firefox_instFromJsonProfileMeta___closed__0 = (const lean_object*)&l_Lean_Firefox_instFromJsonProfileMeta___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Firefox_instFromJsonProfileMeta = (const lean_object*)&l_Lean_Firefox_instFromJsonProfileMeta___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Firefox_instToJsonProfileMeta_toJson_spec__1_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Firefox_instToJsonProfileMeta_toJson_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Firefox_instToJsonProfileMeta_toJson_spec__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Firefox_instToJsonProfileMeta_toJson_spec__0_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Firefox_instToJsonProfileMeta_toJson_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Firefox_instToJsonProfileMeta_toJson_spec__0(lean_object*);
lean_object* l_Float_toJson(double);
lean_object* l_Lean_JsonNumber_fromNat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Firefox_instToJsonProfileMeta_toJson(lean_object*);
static const lean_closure_object l_Lean_Firefox_instToJsonProfileMeta___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Firefox_instToJsonProfileMeta_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Firefox_instToJsonProfileMeta___closed__0 = (const lean_object*)&l_Lean_Firefox_instToJsonProfileMeta___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Firefox_instToJsonProfileMeta = (const lean_object*)&l_Lean_Firefox_instToJsonProfileMeta___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonStackTable_fromJson_spec__0_spec__0_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonStackTable_fromJson_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonStackTable_fromJson_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonStackTable_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonStackTable_fromJson_spec__0___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Option_fromJson_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonStackTable_fromJson_spec__1_spec__2_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonStackTable_fromJson_spec__1_spec__2_spec__4___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonStackTable_fromJson_spec__1_spec__2_spec__4___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonStackTable_fromJson_spec__1_spec__2_spec__4(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonStackTable_fromJson_spec__1_spec__2_spec__5(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonStackTable_fromJson_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonStackTable_fromJson_spec__1_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonStackTable_fromJson_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonStackTable_fromJson_spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "frame"};
static const lean_object* l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__0 = (const lean_object*)&l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__0_value;
static const lean_string_object l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "StackTable"};
static const lean_object* l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__1 = (const lean_object*)&l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__1_value;
static const lean_ctor_object l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Firefox_instFromJsonCategory_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__2_value_aux_0),((lean_object*)&l_Lean_Firefox_instFromJsonCategory_fromJson___closed__2_value),LEAN_SCALAR_PTR_LITERAL(1, 221, 142, 98, 103, 73, 209, 133)}};
static const lean_ctor_object l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__2_value_aux_1),((lean_object*)&l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(158, 161, 145, 27, 82, 18, 188, 76)}};
static const lean_object* l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__2 = (const lean_object*)&l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__2_value;
static lean_once_cell_t l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__3;
static lean_once_cell_t l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__4;
static const lean_ctor_object l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(106, 118, 70, 30, 4, 236, 86, 167)}};
static const lean_object* l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__5 = (const lean_object*)&l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__5_value;
static lean_once_cell_t l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__6;
static lean_once_cell_t l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__7;
static lean_once_cell_t l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__8;
static const lean_string_object l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "category"};
static const lean_object* l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__9 = (const lean_object*)&l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__9_value;
static const lean_ctor_object l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__9_value),LEAN_SCALAR_PTR_LITERAL(76, 206, 219, 5, 172, 192, 191, 198)}};
static const lean_object* l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__10 = (const lean_object*)&l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__10_value;
static lean_once_cell_t l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__11;
static lean_once_cell_t l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__12;
static lean_once_cell_t l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__13;
static const lean_string_object l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "subcategory"};
static const lean_object* l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__14 = (const lean_object*)&l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__14_value;
static const lean_ctor_object l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__14_value),LEAN_SCALAR_PTR_LITERAL(19, 41, 37, 173, 49, 225, 74, 139)}};
static const lean_object* l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__15 = (const lean_object*)&l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__15_value;
static lean_once_cell_t l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__16;
static lean_once_cell_t l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__17;
static lean_once_cell_t l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__18;
static const lean_string_object l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "prefix"};
static const lean_object* l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__19 = (const lean_object*)&l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__19_value;
static const lean_ctor_object l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__19_value),LEAN_SCALAR_PTR_LITERAL(230, 205, 224, 142, 140, 162, 83, 182)}};
static const lean_object* l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__20 = (const lean_object*)&l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__20_value;
static lean_once_cell_t l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__21;
static lean_once_cell_t l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__22;
static lean_once_cell_t l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__23;
static const lean_string_object l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "length"};
static const lean_object* l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__24 = (const lean_object*)&l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__24_value;
static const lean_ctor_object l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__24_value),LEAN_SCALAR_PTR_LITERAL(69, 96, 6, 102, 8, 206, 152, 82)}};
static const lean_object* l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__25 = (const lean_object*)&l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__25_value;
static lean_once_cell_t l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__26;
static lean_once_cell_t l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__27;
static lean_once_cell_t l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__28;
LEAN_EXPORT lean_object* l_Lean_Firefox_instFromJsonStackTable_fromJson(lean_object*);
static const lean_closure_object l_Lean_Firefox_instFromJsonStackTable___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Firefox_instFromJsonStackTable_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Firefox_instFromJsonStackTable___closed__0 = (const lean_object*)&l_Lean_Firefox_instFromJsonStackTable___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Firefox_instFromJsonStackTable = (const lean_object*)&l_Lean_Firefox_instFromJsonStackTable___closed__0_value;
LEAN_EXPORT lean_object* l_Option_toJson___at___00Array_toJson___at___00Lean_Firefox_instToJsonStackTable_toJson_spec__1_spec__2(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Firefox_instToJsonStackTable_toJson_spec__1_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Firefox_instToJsonStackTable_toJson_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Firefox_instToJsonStackTable_toJson_spec__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Firefox_instToJsonStackTable_toJson_spec__0_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Firefox_instToJsonStackTable_toJson_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Firefox_instToJsonStackTable_toJson_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Firefox_instToJsonStackTable_toJson(lean_object*);
static const lean_closure_object l_Lean_Firefox_instToJsonStackTable___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Firefox_instToJsonStackTable_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Firefox_instToJsonStackTable___closed__0 = (const lean_object*)&l_Lean_Firefox_instToJsonStackTable___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Firefox_instToJsonStackTable = (const lean_object*)&l_Lean_Firefox_instToJsonStackTable___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonSamplesTable_fromJson_spec__0_spec__0_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonSamplesTable_fromJson_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonSamplesTable_fromJson_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonSamplesTable_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonSamplesTable_fromJson_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonSamplesTable_fromJson_spec__1_spec__2_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonSamplesTable_fromJson_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonSamplesTable_fromJson_spec__1_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonSamplesTable_fromJson_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonSamplesTable_fromJson_spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "stack"};
static const lean_object* l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__0 = (const lean_object*)&l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__0_value;
static const lean_string_object l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "SamplesTable"};
static const lean_object* l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__1 = (const lean_object*)&l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__1_value;
static const lean_ctor_object l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Firefox_instFromJsonCategory_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__2_value_aux_0),((lean_object*)&l_Lean_Firefox_instFromJsonCategory_fromJson___closed__2_value),LEAN_SCALAR_PTR_LITERAL(1, 221, 142, 98, 103, 73, 209, 133)}};
static const lean_ctor_object l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__2_value_aux_1),((lean_object*)&l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(215, 187, 138, 176, 228, 207, 154, 117)}};
static const lean_object* l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__2 = (const lean_object*)&l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__2_value;
static lean_once_cell_t l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__3;
static lean_once_cell_t l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__4;
static const lean_ctor_object l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(208, 89, 157, 61, 238, 50, 135, 16)}};
static const lean_object* l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__5 = (const lean_object*)&l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__5_value;
static lean_once_cell_t l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__6;
static lean_once_cell_t l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__7;
static lean_once_cell_t l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__8;
static lean_once_cell_t l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__9;
static lean_once_cell_t l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__10;
static const lean_string_object l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "weight"};
static const lean_object* l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__11 = (const lean_object*)&l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__11_value;
static const lean_ctor_object l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__11_value),LEAN_SCALAR_PTR_LITERAL(10, 75, 125, 35, 37, 138, 19, 132)}};
static const lean_object* l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__12 = (const lean_object*)&l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__12_value;
static lean_once_cell_t l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__13;
static lean_once_cell_t l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__14;
static lean_once_cell_t l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__15;
static const lean_string_object l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "weightType"};
static const lean_object* l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__16 = (const lean_object*)&l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__16_value;
static const lean_ctor_object l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__16_value),LEAN_SCALAR_PTR_LITERAL(21, 163, 213, 144, 102, 150, 168, 101)}};
static const lean_object* l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__17 = (const lean_object*)&l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__17_value;
static lean_once_cell_t l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__18;
static lean_once_cell_t l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__19;
static lean_once_cell_t l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__20;
static lean_once_cell_t l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__21;
static lean_once_cell_t l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__22;
static lean_once_cell_t l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__23;
static lean_once_cell_t l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__24;
LEAN_EXPORT lean_object* l_Lean_Firefox_instFromJsonSamplesTable_fromJson(lean_object*);
static const lean_closure_object l_Lean_Firefox_instFromJsonSamplesTable___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Firefox_instFromJsonSamplesTable_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Firefox_instFromJsonSamplesTable___closed__0 = (const lean_object*)&l_Lean_Firefox_instFromJsonSamplesTable___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Firefox_instFromJsonSamplesTable = (const lean_object*)&l_Lean_Firefox_instFromJsonSamplesTable___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Firefox_instToJsonSamplesTable_toJson_spec__1_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Firefox_instToJsonSamplesTable_toJson_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Firefox_instToJsonSamplesTable_toJson_spec__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Firefox_instToJsonSamplesTable_toJson_spec__0_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Firefox_instToJsonSamplesTable_toJson_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Firefox_instToJsonSamplesTable_toJson_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Firefox_instToJsonSamplesTable_toJson(lean_object*);
static const lean_closure_object l_Lean_Firefox_instToJsonSamplesTable___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Firefox_instToJsonSamplesTable_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Firefox_instToJsonSamplesTable___closed__0 = (const lean_object*)&l_Lean_Firefox_instToJsonSamplesTable___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Firefox_instToJsonSamplesTable = (const lean_object*)&l_Lean_Firefox_instToJsonSamplesTable___closed__0_value;
lean_object* l_Lean_Json_getInt_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonFuncTable_fromJson_spec__0_spec__0_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonFuncTable_fromJson_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonFuncTable_fromJson_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonFuncTable_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonFuncTable_fromJson_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "FuncTable"};
static const lean_object* l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__0 = (const lean_object*)&l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__0_value;
static const lean_ctor_object l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Firefox_instFromJsonCategory_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__1_value_aux_0),((lean_object*)&l_Lean_Firefox_instFromJsonCategory_fromJson___closed__2_value),LEAN_SCALAR_PTR_LITERAL(1, 221, 142, 98, 103, 73, 209, 133)}};
static const lean_ctor_object l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__1_value_aux_1),((lean_object*)&l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 233, 34, 52, 182, 124, 102, 23)}};
static const lean_object* l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__1 = (const lean_object*)&l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__1_value;
static lean_once_cell_t l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__2;
static lean_once_cell_t l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__3;
static lean_once_cell_t l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__4;
static lean_once_cell_t l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__5;
static const lean_string_object l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "isJS"};
static const lean_object* l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__6 = (const lean_object*)&l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__6_value;
static const lean_ctor_object l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__6_value),LEAN_SCALAR_PTR_LITERAL(130, 83, 250, 199, 244, 244, 102, 159)}};
static const lean_object* l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__7 = (const lean_object*)&l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__7_value;
static lean_once_cell_t l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__8;
static lean_once_cell_t l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__9;
static lean_once_cell_t l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__10;
static const lean_string_object l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "relevantForJS"};
static const lean_object* l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__11 = (const lean_object*)&l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__11_value;
static const lean_ctor_object l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__11_value),LEAN_SCALAR_PTR_LITERAL(64, 11, 154, 43, 140, 238, 177, 24)}};
static const lean_object* l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__12 = (const lean_object*)&l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__12_value;
static lean_once_cell_t l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__13;
static lean_once_cell_t l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__14;
static lean_once_cell_t l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__15;
static const lean_string_object l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "resource"};
static const lean_object* l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__16 = (const lean_object*)&l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__16_value;
static const lean_ctor_object l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__16_value),LEAN_SCALAR_PTR_LITERAL(162, 161, 163, 104, 166, 98, 163, 194)}};
static const lean_object* l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__17 = (const lean_object*)&l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__17_value;
static lean_once_cell_t l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__18;
static lean_once_cell_t l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__19;
static lean_once_cell_t l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__20;
static const lean_string_object l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "fileName"};
static const lean_object* l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__21 = (const lean_object*)&l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__21_value;
static const lean_ctor_object l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__21_value),LEAN_SCALAR_PTR_LITERAL(67, 201, 140, 230, 1, 55, 95, 217)}};
static const lean_object* l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__22 = (const lean_object*)&l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__22_value;
static lean_once_cell_t l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__23;
static lean_once_cell_t l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__24;
static lean_once_cell_t l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__25;
static const lean_string_object l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "lineNumber"};
static const lean_object* l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__26 = (const lean_object*)&l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__26_value;
static const lean_ctor_object l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__26_value),LEAN_SCALAR_PTR_LITERAL(183, 13, 154, 50, 174, 163, 169, 40)}};
static const lean_object* l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__27 = (const lean_object*)&l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__27_value;
static lean_once_cell_t l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__28;
static lean_once_cell_t l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__29;
static lean_once_cell_t l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__30;
static const lean_string_object l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "columnNumber"};
static const lean_object* l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__31 = (const lean_object*)&l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__31_value;
static const lean_ctor_object l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__31_value),LEAN_SCALAR_PTR_LITERAL(120, 32, 111, 252, 150, 51, 74, 187)}};
static const lean_object* l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__32 = (const lean_object*)&l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__32_value;
static lean_once_cell_t l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__33;
static lean_once_cell_t l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__34;
static lean_once_cell_t l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__35;
static lean_once_cell_t l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__36;
static lean_once_cell_t l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__37;
LEAN_EXPORT lean_object* l_Lean_Firefox_instFromJsonFuncTable_fromJson(lean_object*);
static const lean_closure_object l_Lean_Firefox_instFromJsonFuncTable___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Firefox_instFromJsonFuncTable_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Firefox_instFromJsonFuncTable___closed__0 = (const lean_object*)&l_Lean_Firefox_instFromJsonFuncTable___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Firefox_instFromJsonFuncTable = (const lean_object*)&l_Lean_Firefox_instFromJsonFuncTable___closed__0_value;
lean_object* l_Lean_JsonNumber_fromInt(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Firefox_instToJsonFuncTable_toJson_spec__0_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Firefox_instToJsonFuncTable_toJson_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Firefox_instToJsonFuncTable_toJson_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Firefox_instToJsonFuncTable_toJson(lean_object*);
static const lean_closure_object l_Lean_Firefox_instToJsonFuncTable___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Firefox_instToJsonFuncTable_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Firefox_instToJsonFuncTable___closed__0 = (const lean_object*)&l_Lean_Firefox_instToJsonFuncTable___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Firefox_instToJsonFuncTable = (const lean_object*)&l_Lean_Firefox_instToJsonFuncTable___closed__0_value;
static const lean_ctor_object l_Option_fromJson_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonFrameTable_fromJson_spec__0_spec__0_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonFrameTable_fromJson_spec__0_spec__0_spec__1___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonFrameTable_fromJson_spec__0_spec__0_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonFrameTable_fromJson_spec__0_spec__0_spec__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonFrameTable_fromJson_spec__0_spec__0_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonFrameTable_fromJson_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonFrameTable_fromJson_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonFrameTable_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonFrameTable_fromJson_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "address"};
static const lean_object* l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__0 = (const lean_object*)&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__0_value;
static const lean_string_object l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "FrameTable"};
static const lean_object* l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__1 = (const lean_object*)&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__1_value;
static const lean_ctor_object l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Firefox_instFromJsonCategory_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__2_value_aux_0),((lean_object*)&l_Lean_Firefox_instFromJsonCategory_fromJson___closed__2_value),LEAN_SCALAR_PTR_LITERAL(1, 221, 142, 98, 103, 73, 209, 133)}};
static const lean_ctor_object l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__2_value_aux_1),((lean_object*)&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(65, 156, 69, 76, 30, 113, 79, 38)}};
static const lean_object* l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__2 = (const lean_object*)&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__2_value;
static lean_once_cell_t l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__3;
static lean_once_cell_t l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__4;
static const lean_ctor_object l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(99, 127, 29, 74, 107, 134, 8, 23)}};
static const lean_object* l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__5 = (const lean_object*)&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__5_value;
static lean_once_cell_t l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__6;
static lean_once_cell_t l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__7;
static lean_once_cell_t l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__8;
static const lean_string_object l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "inlineDepth"};
static const lean_object* l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__9 = (const lean_object*)&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__9_value;
static const lean_ctor_object l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__9_value),LEAN_SCALAR_PTR_LITERAL(185, 130, 4, 176, 140, 3, 27, 251)}};
static const lean_object* l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__10 = (const lean_object*)&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__10_value;
static lean_once_cell_t l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__11;
static lean_once_cell_t l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__12;
static lean_once_cell_t l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__13;
static lean_once_cell_t l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__14;
static lean_once_cell_t l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__15;
static lean_once_cell_t l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__16;
static lean_once_cell_t l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__17;
static const lean_string_object l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "func"};
static const lean_object* l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__18 = (const lean_object*)&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__18_value;
static const lean_ctor_object l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__18_value),LEAN_SCALAR_PTR_LITERAL(126, 207, 36, 56, 147, 187, 96, 81)}};
static const lean_object* l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__19 = (const lean_object*)&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__19_value;
static lean_once_cell_t l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__20;
static lean_once_cell_t l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__21;
static lean_once_cell_t l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__22;
static const lean_string_object l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "nativeSymbol"};
static const lean_object* l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__23 = (const lean_object*)&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__23_value;
static const lean_ctor_object l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__23_value),LEAN_SCALAR_PTR_LITERAL(84, 184, 220, 224, 193, 85, 192, 101)}};
static const lean_object* l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__24 = (const lean_object*)&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__24_value;
static lean_once_cell_t l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__25;
static lean_once_cell_t l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__26;
static lean_once_cell_t l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__27;
static const lean_string_object l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "innerWindowID"};
static const lean_object* l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__28 = (const lean_object*)&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__28_value;
static const lean_ctor_object l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__28_value),LEAN_SCALAR_PTR_LITERAL(97, 40, 5, 206, 248, 148, 179, 42)}};
static const lean_object* l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__29 = (const lean_object*)&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__29_value;
static lean_once_cell_t l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__30;
static lean_once_cell_t l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__31;
static lean_once_cell_t l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__32;
static const lean_string_object l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "implementation"};
static const lean_object* l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__33 = (const lean_object*)&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__33_value;
static const lean_ctor_object l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__33_value),LEAN_SCALAR_PTR_LITERAL(186, 135, 102, 9, 143, 52, 86, 15)}};
static const lean_object* l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__34 = (const lean_object*)&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__34_value;
static lean_once_cell_t l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__35;
static lean_once_cell_t l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__36;
static lean_once_cell_t l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__37;
static const lean_string_object l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "line"};
static const lean_object* l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__38 = (const lean_object*)&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__38_value;
static const lean_ctor_object l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__38_value),LEAN_SCALAR_PTR_LITERAL(45, 20, 170, 234, 25, 144, 248, 101)}};
static const lean_object* l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__39 = (const lean_object*)&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__39_value;
static lean_once_cell_t l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__40_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__40;
static lean_once_cell_t l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__41_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__41;
static lean_once_cell_t l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__42_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__42;
static const lean_string_object l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "column"};
static const lean_object* l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__43 = (const lean_object*)&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__43_value;
static const lean_ctor_object l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__43_value),LEAN_SCALAR_PTR_LITERAL(177, 41, 36, 97, 84, 61, 112, 119)}};
static const lean_object* l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__44 = (const lean_object*)&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__44_value;
static lean_once_cell_t l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__45_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__45;
static lean_once_cell_t l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__46_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__46;
static lean_once_cell_t l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__47_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__47;
static lean_once_cell_t l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__48_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__48;
static lean_once_cell_t l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__49_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__49;
LEAN_EXPORT lean_object* l_Lean_Firefox_instFromJsonFrameTable_fromJson(lean_object*);
static const lean_closure_object l_Lean_Firefox_instFromJsonFrameTable___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Firefox_instFromJsonFrameTable_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Firefox_instFromJsonFrameTable___closed__0 = (const lean_object*)&l_Lean_Firefox_instFromJsonFrameTable___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Firefox_instFromJsonFrameTable = (const lean_object*)&l_Lean_Firefox_instFromJsonFrameTable___closed__0_value;
LEAN_EXPORT lean_object* l_Option_toJson___at___00Array_toJson___at___00Lean_Firefox_instToJsonFrameTable_toJson_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Option_toJson___at___00Array_toJson___at___00Lean_Firefox_instToJsonFrameTable_toJson_spec__0_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Firefox_instToJsonFrameTable_toJson_spec__0_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Firefox_instToJsonFrameTable_toJson_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Firefox_instToJsonFrameTable_toJson_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Firefox_instToJsonFrameTable_toJson(lean_object*);
static const lean_closure_object l_Lean_Firefox_instToJsonFrameTable___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Firefox_instToJsonFrameTable_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Firefox_instToJsonFrameTable___closed__0 = (const lean_object*)&l_Lean_Firefox_instToJsonFrameTable___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Firefox_instToJsonFrameTable = (const lean_object*)&l_Lean_Firefox_instToJsonFrameTable___closed__0_value;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static const lean_array_object l_Lean_Firefox_instInhabitedFrameTable_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Firefox_instInhabitedFrameTable_default___closed__0 = (const lean_object*)&l_Lean_Firefox_instInhabitedFrameTable_default___closed__0_value;
static lean_once_cell_t l_Lean_Firefox_instInhabitedFrameTable_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instInhabitedFrameTable_default___closed__1;
LEAN_EXPORT lean_object* l_Lean_Firefox_instInhabitedFrameTable_default;
LEAN_EXPORT lean_object* l_Lean_Firefox_instInhabitedFrameTable;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Firefox_FrameTable_push(lean_object*, lean_object*);
static const lean_string_object l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "data"};
static const lean_object* l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__0 = (const lean_object*)&l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__0_value;
static const lean_string_object l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "RawMarkerTable"};
static const lean_object* l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__1 = (const lean_object*)&l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__1_value;
static const lean_ctor_object l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Firefox_instFromJsonCategory_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__2_value_aux_0),((lean_object*)&l_Lean_Firefox_instFromJsonCategory_fromJson___closed__2_value),LEAN_SCALAR_PTR_LITERAL(1, 221, 142, 98, 103, 73, 209, 133)}};
static const lean_ctor_object l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__2_value_aux_1),((lean_object*)&l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(217, 129, 183, 157, 11, 43, 22, 62)}};
static const lean_object* l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__2 = (const lean_object*)&l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__2_value;
static lean_once_cell_t l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__3;
static lean_once_cell_t l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__4;
static const lean_ctor_object l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(157, 185, 242, 82, 251, 25, 14, 198)}};
static const lean_object* l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__5 = (const lean_object*)&l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__5_value;
static lean_once_cell_t l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__6;
static lean_once_cell_t l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__7;
static lean_once_cell_t l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__8;
static lean_once_cell_t l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__9;
static lean_once_cell_t l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__10;
static lean_once_cell_t l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__11;
static lean_once_cell_t l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__12;
LEAN_EXPORT lean_object* l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson(lean_object*);
static const lean_closure_object l_Lean_Firefox_instFromJsonRawMarkerTable___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Firefox_instFromJsonRawMarkerTable___closed__0 = (const lean_object*)&l_Lean_Firefox_instFromJsonRawMarkerTable___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Firefox_instFromJsonRawMarkerTable = (const lean_object*)&l_Lean_Firefox_instFromJsonRawMarkerTable___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Firefox_instToJsonRawMarkerTable_toJson(lean_object*);
static const lean_closure_object l_Lean_Firefox_instToJsonRawMarkerTable___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Firefox_instToJsonRawMarkerTable_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Firefox_instToJsonRawMarkerTable___closed__0 = (const lean_object*)&l_Lean_Firefox_instToJsonRawMarkerTable___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Firefox_instToJsonRawMarkerTable = (const lean_object*)&l_Lean_Firefox_instToJsonRawMarkerTable___closed__0_value;
static const lean_string_object l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "type"};
static const lean_object* l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__0 = (const lean_object*)&l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__0_value;
static const lean_string_object l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "ResourceTable"};
static const lean_object* l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__1 = (const lean_object*)&l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__1_value;
static const lean_ctor_object l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Firefox_instFromJsonCategory_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__2_value_aux_0),((lean_object*)&l_Lean_Firefox_instFromJsonCategory_fromJson___closed__2_value),LEAN_SCALAR_PTR_LITERAL(1, 221, 142, 98, 103, 73, 209, 133)}};
static const lean_ctor_object l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__2_value_aux_1),((lean_object*)&l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(247, 23, 36, 141, 162, 189, 23, 177)}};
static const lean_object* l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__2 = (const lean_object*)&l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__2_value;
static lean_once_cell_t l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__3;
static lean_once_cell_t l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__4;
static const lean_ctor_object l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(112, 109, 54, 158, 248, 169, 165, 159)}};
static const lean_object* l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__5 = (const lean_object*)&l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__5_value;
static lean_once_cell_t l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__6;
static lean_once_cell_t l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__7;
static lean_once_cell_t l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__8;
static lean_once_cell_t l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__9;
static lean_once_cell_t l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__10;
LEAN_EXPORT lean_object* l_Lean_Firefox_instFromJsonResourceTable_fromJson(lean_object*);
static const lean_closure_object l_Lean_Firefox_instFromJsonResourceTable___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Firefox_instFromJsonResourceTable_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Firefox_instFromJsonResourceTable___closed__0 = (const lean_object*)&l_Lean_Firefox_instFromJsonResourceTable___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Firefox_instFromJsonResourceTable = (const lean_object*)&l_Lean_Firefox_instFromJsonResourceTable___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Firefox_instToJsonResourceTable_toJson(lean_object*);
static const lean_closure_object l_Lean_Firefox_instToJsonResourceTable___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Firefox_instToJsonResourceTable_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Firefox_instToJsonResourceTable___closed__0 = (const lean_object*)&l_Lean_Firefox_instToJsonResourceTable___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Firefox_instToJsonResourceTable = (const lean_object*)&l_Lean_Firefox_instToJsonResourceTable___closed__0_value;
lean_object* l_Lean_Json_getBool_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonThread_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonThread_fromJson_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonThread_fromJson_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonThread_fromJson_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonThread_fromJson_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonThread_fromJson_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonThread_fromJson_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonThread_fromJson_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonThread_fromJson_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonThread_fromJson_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonThread_fromJson_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonThread_fromJson_spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonThread_fromJson_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonThread_fromJson_spec__6___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Firefox_instFromJsonThread_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Thread"};
static const lean_object* l_Lean_Firefox_instFromJsonThread_fromJson___closed__0 = (const lean_object*)&l_Lean_Firefox_instFromJsonThread_fromJson___closed__0_value;
static const lean_ctor_object l_Lean_Firefox_instFromJsonThread_fromJson___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Firefox_instFromJsonCategory_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Firefox_instFromJsonThread_fromJson___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Firefox_instFromJsonThread_fromJson___closed__1_value_aux_0),((lean_object*)&l_Lean_Firefox_instFromJsonCategory_fromJson___closed__2_value),LEAN_SCALAR_PTR_LITERAL(1, 221, 142, 98, 103, 73, 209, 133)}};
static const lean_ctor_object l_Lean_Firefox_instFromJsonThread_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Firefox_instFromJsonThread_fromJson___closed__1_value_aux_1),((lean_object*)&l_Lean_Firefox_instFromJsonThread_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 102, 6, 129, 193, 205, 127, 161)}};
static const lean_object* l_Lean_Firefox_instFromJsonThread_fromJson___closed__1 = (const lean_object*)&l_Lean_Firefox_instFromJsonThread_fromJson___closed__1_value;
static lean_once_cell_t l_Lean_Firefox_instFromJsonThread_fromJson___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonThread_fromJson___closed__2;
static lean_once_cell_t l_Lean_Firefox_instFromJsonThread_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonThread_fromJson___closed__3;
static lean_once_cell_t l_Lean_Firefox_instFromJsonThread_fromJson___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonThread_fromJson___closed__4;
static lean_once_cell_t l_Lean_Firefox_instFromJsonThread_fromJson___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonThread_fromJson___closed__5;
static lean_once_cell_t l_Lean_Firefox_instFromJsonThread_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonThread_fromJson___closed__6;
static lean_once_cell_t l_Lean_Firefox_instFromJsonThread_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonThread_fromJson___closed__7;
static const lean_string_object l_Lean_Firefox_instFromJsonThread_fromJson___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "isMainThread"};
static const lean_object* l_Lean_Firefox_instFromJsonThread_fromJson___closed__8 = (const lean_object*)&l_Lean_Firefox_instFromJsonThread_fromJson___closed__8_value;
static const lean_ctor_object l_Lean_Firefox_instFromJsonThread_fromJson___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Firefox_instFromJsonThread_fromJson___closed__8_value),LEAN_SCALAR_PTR_LITERAL(111, 97, 248, 33, 147, 201, 64, 71)}};
static const lean_object* l_Lean_Firefox_instFromJsonThread_fromJson___closed__9 = (const lean_object*)&l_Lean_Firefox_instFromJsonThread_fromJson___closed__9_value;
static lean_once_cell_t l_Lean_Firefox_instFromJsonThread_fromJson___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonThread_fromJson___closed__10;
static lean_once_cell_t l_Lean_Firefox_instFromJsonThread_fromJson___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonThread_fromJson___closed__11;
static lean_once_cell_t l_Lean_Firefox_instFromJsonThread_fromJson___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonThread_fromJson___closed__12;
static const lean_string_object l_Lean_Firefox_instFromJsonThread_fromJson___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "samples"};
static const lean_object* l_Lean_Firefox_instFromJsonThread_fromJson___closed__13 = (const lean_object*)&l_Lean_Firefox_instFromJsonThread_fromJson___closed__13_value;
static const lean_ctor_object l_Lean_Firefox_instFromJsonThread_fromJson___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Firefox_instFromJsonThread_fromJson___closed__13_value),LEAN_SCALAR_PTR_LITERAL(126, 40, 150, 76, 5, 209, 190, 90)}};
static const lean_object* l_Lean_Firefox_instFromJsonThread_fromJson___closed__14 = (const lean_object*)&l_Lean_Firefox_instFromJsonThread_fromJson___closed__14_value;
static lean_once_cell_t l_Lean_Firefox_instFromJsonThread_fromJson___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonThread_fromJson___closed__15;
static lean_once_cell_t l_Lean_Firefox_instFromJsonThread_fromJson___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonThread_fromJson___closed__16;
static lean_once_cell_t l_Lean_Firefox_instFromJsonThread_fromJson___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonThread_fromJson___closed__17;
static const lean_string_object l_Lean_Firefox_instFromJsonThread_fromJson___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "markers"};
static const lean_object* l_Lean_Firefox_instFromJsonThread_fromJson___closed__18 = (const lean_object*)&l_Lean_Firefox_instFromJsonThread_fromJson___closed__18_value;
static const lean_ctor_object l_Lean_Firefox_instFromJsonThread_fromJson___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Firefox_instFromJsonThread_fromJson___closed__18_value),LEAN_SCALAR_PTR_LITERAL(131, 132, 127, 199, 77, 56, 4, 153)}};
static const lean_object* l_Lean_Firefox_instFromJsonThread_fromJson___closed__19 = (const lean_object*)&l_Lean_Firefox_instFromJsonThread_fromJson___closed__19_value;
static lean_once_cell_t l_Lean_Firefox_instFromJsonThread_fromJson___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonThread_fromJson___closed__20;
static lean_once_cell_t l_Lean_Firefox_instFromJsonThread_fromJson___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonThread_fromJson___closed__21;
static lean_once_cell_t l_Lean_Firefox_instFromJsonThread_fromJson___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonThread_fromJson___closed__22;
static const lean_string_object l_Lean_Firefox_instFromJsonThread_fromJson___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "stackTable"};
static const lean_object* l_Lean_Firefox_instFromJsonThread_fromJson___closed__23 = (const lean_object*)&l_Lean_Firefox_instFromJsonThread_fromJson___closed__23_value;
static const lean_ctor_object l_Lean_Firefox_instFromJsonThread_fromJson___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Firefox_instFromJsonThread_fromJson___closed__23_value),LEAN_SCALAR_PTR_LITERAL(43, 131, 212, 86, 108, 53, 35, 9)}};
static const lean_object* l_Lean_Firefox_instFromJsonThread_fromJson___closed__24 = (const lean_object*)&l_Lean_Firefox_instFromJsonThread_fromJson___closed__24_value;
static lean_once_cell_t l_Lean_Firefox_instFromJsonThread_fromJson___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonThread_fromJson___closed__25;
static lean_once_cell_t l_Lean_Firefox_instFromJsonThread_fromJson___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonThread_fromJson___closed__26;
static lean_once_cell_t l_Lean_Firefox_instFromJsonThread_fromJson___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonThread_fromJson___closed__27;
static const lean_string_object l_Lean_Firefox_instFromJsonThread_fromJson___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "frameTable"};
static const lean_object* l_Lean_Firefox_instFromJsonThread_fromJson___closed__28 = (const lean_object*)&l_Lean_Firefox_instFromJsonThread_fromJson___closed__28_value;
static const lean_ctor_object l_Lean_Firefox_instFromJsonThread_fromJson___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Firefox_instFromJsonThread_fromJson___closed__28_value),LEAN_SCALAR_PTR_LITERAL(220, 91, 176, 170, 52, 10, 14, 104)}};
static const lean_object* l_Lean_Firefox_instFromJsonThread_fromJson___closed__29 = (const lean_object*)&l_Lean_Firefox_instFromJsonThread_fromJson___closed__29_value;
static lean_once_cell_t l_Lean_Firefox_instFromJsonThread_fromJson___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonThread_fromJson___closed__30;
static lean_once_cell_t l_Lean_Firefox_instFromJsonThread_fromJson___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonThread_fromJson___closed__31;
static lean_once_cell_t l_Lean_Firefox_instFromJsonThread_fromJson___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonThread_fromJson___closed__32;
static const lean_string_object l_Lean_Firefox_instFromJsonThread_fromJson___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "resourceTable"};
static const lean_object* l_Lean_Firefox_instFromJsonThread_fromJson___closed__33 = (const lean_object*)&l_Lean_Firefox_instFromJsonThread_fromJson___closed__33_value;
static const lean_ctor_object l_Lean_Firefox_instFromJsonThread_fromJson___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Firefox_instFromJsonThread_fromJson___closed__33_value),LEAN_SCALAR_PTR_LITERAL(254, 105, 116, 50, 84, 52, 124, 155)}};
static const lean_object* l_Lean_Firefox_instFromJsonThread_fromJson___closed__34 = (const lean_object*)&l_Lean_Firefox_instFromJsonThread_fromJson___closed__34_value;
static lean_once_cell_t l_Lean_Firefox_instFromJsonThread_fromJson___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonThread_fromJson___closed__35;
static lean_once_cell_t l_Lean_Firefox_instFromJsonThread_fromJson___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonThread_fromJson___closed__36;
static lean_once_cell_t l_Lean_Firefox_instFromJsonThread_fromJson___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonThread_fromJson___closed__37;
static const lean_string_object l_Lean_Firefox_instFromJsonThread_fromJson___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "nativeSymbols"};
static const lean_object* l_Lean_Firefox_instFromJsonThread_fromJson___closed__38 = (const lean_object*)&l_Lean_Firefox_instFromJsonThread_fromJson___closed__38_value;
static const lean_ctor_object l_Lean_Firefox_instFromJsonThread_fromJson___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Firefox_instFromJsonThread_fromJson___closed__38_value),LEAN_SCALAR_PTR_LITERAL(136, 149, 38, 186, 185, 69, 38, 51)}};
static const lean_object* l_Lean_Firefox_instFromJsonThread_fromJson___closed__39 = (const lean_object*)&l_Lean_Firefox_instFromJsonThread_fromJson___closed__39_value;
static lean_once_cell_t l_Lean_Firefox_instFromJsonThread_fromJson___closed__40_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonThread_fromJson___closed__40;
static lean_once_cell_t l_Lean_Firefox_instFromJsonThread_fromJson___closed__41_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonThread_fromJson___closed__41;
static lean_once_cell_t l_Lean_Firefox_instFromJsonThread_fromJson___closed__42_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonThread_fromJson___closed__42;
static const lean_string_object l_Lean_Firefox_instFromJsonThread_fromJson___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "stringArray"};
static const lean_object* l_Lean_Firefox_instFromJsonThread_fromJson___closed__43 = (const lean_object*)&l_Lean_Firefox_instFromJsonThread_fromJson___closed__43_value;
static const lean_ctor_object l_Lean_Firefox_instFromJsonThread_fromJson___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Firefox_instFromJsonThread_fromJson___closed__43_value),LEAN_SCALAR_PTR_LITERAL(148, 127, 137, 97, 195, 143, 28, 68)}};
static const lean_object* l_Lean_Firefox_instFromJsonThread_fromJson___closed__44 = (const lean_object*)&l_Lean_Firefox_instFromJsonThread_fromJson___closed__44_value;
static lean_once_cell_t l_Lean_Firefox_instFromJsonThread_fromJson___closed__45_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonThread_fromJson___closed__45;
static lean_once_cell_t l_Lean_Firefox_instFromJsonThread_fromJson___closed__46_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonThread_fromJson___closed__46;
static lean_once_cell_t l_Lean_Firefox_instFromJsonThread_fromJson___closed__47_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonThread_fromJson___closed__47;
static const lean_string_object l_Lean_Firefox_instFromJsonThread_fromJson___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "funcTable"};
static const lean_object* l_Lean_Firefox_instFromJsonThread_fromJson___closed__48 = (const lean_object*)&l_Lean_Firefox_instFromJsonThread_fromJson___closed__48_value;
static const lean_ctor_object l_Lean_Firefox_instFromJsonThread_fromJson___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Firefox_instFromJsonThread_fromJson___closed__48_value),LEAN_SCALAR_PTR_LITERAL(140, 176, 103, 103, 70, 114, 135, 204)}};
static const lean_object* l_Lean_Firefox_instFromJsonThread_fromJson___closed__49 = (const lean_object*)&l_Lean_Firefox_instFromJsonThread_fromJson___closed__49_value;
static lean_once_cell_t l_Lean_Firefox_instFromJsonThread_fromJson___closed__50_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonThread_fromJson___closed__50;
static lean_once_cell_t l_Lean_Firefox_instFromJsonThread_fromJson___closed__51_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonThread_fromJson___closed__51;
static lean_once_cell_t l_Lean_Firefox_instFromJsonThread_fromJson___closed__52_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonThread_fromJson___closed__52;
LEAN_EXPORT lean_object* l_Lean_Firefox_instFromJsonThread_fromJson(lean_object*);
static const lean_closure_object l_Lean_Firefox_instFromJsonThread___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Firefox_instFromJsonThread_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Firefox_instFromJsonThread___closed__0 = (const lean_object*)&l_Lean_Firefox_instFromJsonThread___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Firefox_instFromJsonThread = (const lean_object*)&l_Lean_Firefox_instFromJsonThread___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Firefox_instToJsonThread_toJson(lean_object*);
static const lean_closure_object l_Lean_Firefox_instToJsonThread___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Firefox_instToJsonThread_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Firefox_instToJsonThread___closed__0 = (const lean_object*)&l_Lean_Firefox_instToJsonThread___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Firefox_instToJsonThread = (const lean_object*)&l_Lean_Firefox_instToJsonThread___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfile_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfile_fromJson_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfile_fromJson_spec__1_spec__1_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfile_fromJson_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfile_fromJson_spec__1_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfile_fromJson_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfile_fromJson_spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Firefox_instFromJsonProfile_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l_Lean_Firefox_instFromJsonProfile_fromJson___closed__0 = (const lean_object*)&l_Lean_Firefox_instFromJsonProfile_fromJson___closed__0_value;
static const lean_string_object l_Lean_Firefox_instFromJsonProfile_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Profile"};
static const lean_object* l_Lean_Firefox_instFromJsonProfile_fromJson___closed__1 = (const lean_object*)&l_Lean_Firefox_instFromJsonProfile_fromJson___closed__1_value;
static const lean_ctor_object l_Lean_Firefox_instFromJsonProfile_fromJson___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Firefox_instFromJsonCategory_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Firefox_instFromJsonProfile_fromJson___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Firefox_instFromJsonProfile_fromJson___closed__2_value_aux_0),((lean_object*)&l_Lean_Firefox_instFromJsonCategory_fromJson___closed__2_value),LEAN_SCALAR_PTR_LITERAL(1, 221, 142, 98, 103, 73, 209, 133)}};
static const lean_ctor_object l_Lean_Firefox_instFromJsonProfile_fromJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Firefox_instFromJsonProfile_fromJson___closed__2_value_aux_1),((lean_object*)&l_Lean_Firefox_instFromJsonProfile_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(154, 231, 246, 101, 43, 72, 102, 2)}};
static const lean_object* l_Lean_Firefox_instFromJsonProfile_fromJson___closed__2 = (const lean_object*)&l_Lean_Firefox_instFromJsonProfile_fromJson___closed__2_value;
static lean_once_cell_t l_Lean_Firefox_instFromJsonProfile_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonProfile_fromJson___closed__3;
static lean_once_cell_t l_Lean_Firefox_instFromJsonProfile_fromJson___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonProfile_fromJson___closed__4;
static const lean_ctor_object l_Lean_Firefox_instFromJsonProfile_fromJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Firefox_instFromJsonProfile_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(245, 159, 21, 79, 192, 127, 97, 20)}};
static const lean_object* l_Lean_Firefox_instFromJsonProfile_fromJson___closed__5 = (const lean_object*)&l_Lean_Firefox_instFromJsonProfile_fromJson___closed__5_value;
static lean_once_cell_t l_Lean_Firefox_instFromJsonProfile_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonProfile_fromJson___closed__6;
static lean_once_cell_t l_Lean_Firefox_instFromJsonProfile_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonProfile_fromJson___closed__7;
static lean_once_cell_t l_Lean_Firefox_instFromJsonProfile_fromJson___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonProfile_fromJson___closed__8;
static const lean_string_object l_Lean_Firefox_instFromJsonProfile_fromJson___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "libs"};
static const lean_object* l_Lean_Firefox_instFromJsonProfile_fromJson___closed__9 = (const lean_object*)&l_Lean_Firefox_instFromJsonProfile_fromJson___closed__9_value;
static const lean_ctor_object l_Lean_Firefox_instFromJsonProfile_fromJson___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Firefox_instFromJsonProfile_fromJson___closed__9_value),LEAN_SCALAR_PTR_LITERAL(49, 117, 173, 12, 162, 111, 95, 96)}};
static const lean_object* l_Lean_Firefox_instFromJsonProfile_fromJson___closed__10 = (const lean_object*)&l_Lean_Firefox_instFromJsonProfile_fromJson___closed__10_value;
static lean_once_cell_t l_Lean_Firefox_instFromJsonProfile_fromJson___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonProfile_fromJson___closed__11;
static lean_once_cell_t l_Lean_Firefox_instFromJsonProfile_fromJson___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonProfile_fromJson___closed__12;
static lean_once_cell_t l_Lean_Firefox_instFromJsonProfile_fromJson___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonProfile_fromJson___closed__13;
static const lean_string_object l_Lean_Firefox_instFromJsonProfile_fromJson___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "threads"};
static const lean_object* l_Lean_Firefox_instFromJsonProfile_fromJson___closed__14 = (const lean_object*)&l_Lean_Firefox_instFromJsonProfile_fromJson___closed__14_value;
static const lean_ctor_object l_Lean_Firefox_instFromJsonProfile_fromJson___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Firefox_instFromJsonProfile_fromJson___closed__14_value),LEAN_SCALAR_PTR_LITERAL(201, 78, 72, 66, 196, 97, 111, 153)}};
static const lean_object* l_Lean_Firefox_instFromJsonProfile_fromJson___closed__15 = (const lean_object*)&l_Lean_Firefox_instFromJsonProfile_fromJson___closed__15_value;
static lean_once_cell_t l_Lean_Firefox_instFromJsonProfile_fromJson___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonProfile_fromJson___closed__16;
static lean_once_cell_t l_Lean_Firefox_instFromJsonProfile_fromJson___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonProfile_fromJson___closed__17;
static lean_once_cell_t l_Lean_Firefox_instFromJsonProfile_fromJson___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonProfile_fromJson___closed__18;
LEAN_EXPORT lean_object* l_Lean_Firefox_instFromJsonProfile_fromJson(lean_object*);
static const lean_closure_object l_Lean_Firefox_instFromJsonProfile___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Firefox_instFromJsonProfile_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Firefox_instFromJsonProfile___closed__0 = (const lean_object*)&l_Lean_Firefox_instFromJsonProfile___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Firefox_instFromJsonProfile = (const lean_object*)&l_Lean_Firefox_instFromJsonProfile___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Firefox_instToJsonProfile_toJson_spec__0_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Firefox_instToJsonProfile_toJson_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Firefox_instToJsonProfile_toJson_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Firefox_instToJsonProfile_toJson(lean_object*);
static const lean_closure_object l_Lean_Firefox_instToJsonProfile___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Firefox_instToJsonProfile_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Firefox_instToJsonProfile___closed__0 = (const lean_object*)&l_Lean_Firefox_instToJsonProfile___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Firefox_instToJsonProfile = (const lean_object*)&l_Lean_Firefox_instToJsonProfile___closed__0_value;
static const lean_string_object l_Lean_Firefox_categories___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Other"};
static const lean_object* l_Lean_Firefox_categories___closed__0 = (const lean_object*)&l_Lean_Firefox_categories___closed__0_value;
static const lean_ctor_object l_Lean_Firefox_categories___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Firefox_categories___closed__0_value),LEAN_SCALAR_PTR_LITERAL(118, 176, 148, 210, 57, 145, 59, 135)}};
static const lean_object* l_Lean_Firefox_categories___closed__1 = (const lean_object*)&l_Lean_Firefox_categories___closed__1_value;
static const lean_string_object l_Lean_Firefox_categories___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "gray"};
static const lean_object* l_Lean_Firefox_categories___closed__2 = (const lean_object*)&l_Lean_Firefox_categories___closed__2_value;
static const lean_array_object l_Lean_Firefox_categories___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Firefox_categories___closed__3 = (const lean_object*)&l_Lean_Firefox_categories___closed__3_value;
static const lean_ctor_object l_Lean_Firefox_categories___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Firefox_categories___closed__1_value),((lean_object*)&l_Lean_Firefox_categories___closed__2_value),((lean_object*)&l_Lean_Firefox_categories___closed__3_value)}};
static const lean_object* l_Lean_Firefox_categories___closed__4 = (const lean_object*)&l_Lean_Firefox_categories___closed__4_value;
static const lean_string_object l_Lean_Firefox_categories___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Firefox_categories___closed__5 = (const lean_object*)&l_Lean_Firefox_categories___closed__5_value;
static const lean_string_object l_Lean_Firefox_categories___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "async"};
static const lean_object* l_Lean_Firefox_categories___closed__6 = (const lean_object*)&l_Lean_Firefox_categories___closed__6_value;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Firefox_categories___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Firefox_categories___closed__5_value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l_Lean_Firefox_categories___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Firefox_categories___closed__7_value_aux_0),((lean_object*)&l_Lean_Firefox_categories___closed__6_value),LEAN_SCALAR_PTR_LITERAL(6, 0, 36, 68, 138, 2, 151, 20)}};
static const lean_object* l_Lean_Firefox_categories___closed__7 = (const lean_object*)&l_Lean_Firefox_categories___closed__7_value;
static const lean_ctor_object l_Lean_Firefox_categories___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Firefox_categories___closed__7_value),((lean_object*)&l_Lean_Firefox_categories___closed__2_value),((lean_object*)&l_Lean_Firefox_categories___closed__3_value)}};
static const lean_object* l_Lean_Firefox_categories___closed__8 = (const lean_object*)&l_Lean_Firefox_categories___closed__8_value;
static const lean_string_object l_Lean_Firefox_categories___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "block"};
static const lean_object* l_Lean_Firefox_categories___closed__9 = (const lean_object*)&l_Lean_Firefox_categories___closed__9_value;
static const lean_ctor_object l_Lean_Firefox_categories___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Firefox_categories___closed__5_value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l_Lean_Firefox_categories___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Firefox_categories___closed__10_value_aux_0),((lean_object*)&l_Lean_Firefox_categories___closed__9_value),LEAN_SCALAR_PTR_LITERAL(93, 203, 205, 48, 20, 104, 179, 229)}};
static const lean_object* l_Lean_Firefox_categories___closed__10 = (const lean_object*)&l_Lean_Firefox_categories___closed__10_value;
static const lean_string_object l_Lean_Firefox_categories___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "brown"};
static const lean_object* l_Lean_Firefox_categories___closed__11 = (const lean_object*)&l_Lean_Firefox_categories___closed__11_value;
static const lean_ctor_object l_Lean_Firefox_categories___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Firefox_categories___closed__10_value),((lean_object*)&l_Lean_Firefox_categories___closed__11_value),((lean_object*)&l_Lean_Firefox_categories___closed__3_value)}};
static const lean_object* l_Lean_Firefox_categories___closed__12 = (const lean_object*)&l_Lean_Firefox_categories___closed__12_value;
static const lean_ctor_object l_Lean_Firefox_categories___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Firefox_categories___closed__5_value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_object* l_Lean_Firefox_categories___closed__13 = (const lean_object*)&l_Lean_Firefox_categories___closed__13_value;
static const lean_string_object l_Lean_Firefox_categories___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "red"};
static const lean_object* l_Lean_Firefox_categories___closed__14 = (const lean_object*)&l_Lean_Firefox_categories___closed__14_value;
static const lean_ctor_object l_Lean_Firefox_categories___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Firefox_categories___closed__13_value),((lean_object*)&l_Lean_Firefox_categories___closed__14_value),((lean_object*)&l_Lean_Firefox_categories___closed__3_value)}};
static const lean_object* l_Lean_Firefox_categories___closed__15 = (const lean_object*)&l_Lean_Firefox_categories___closed__15_value;
static const lean_string_object l_Lean_Firefox_categories___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_Firefox_categories___closed__16 = (const lean_object*)&l_Lean_Firefox_categories___closed__16_value;
static const lean_ctor_object l_Lean_Firefox_categories___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Firefox_categories___closed__16_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_object* l_Lean_Firefox_categories___closed__17 = (const lean_object*)&l_Lean_Firefox_categories___closed__17_value;
static const lean_string_object l_Lean_Firefox_categories___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "yellow"};
static const lean_object* l_Lean_Firefox_categories___closed__18 = (const lean_object*)&l_Lean_Firefox_categories___closed__18_value;
static const lean_ctor_object l_Lean_Firefox_categories___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Firefox_categories___closed__17_value),((lean_object*)&l_Lean_Firefox_categories___closed__18_value),((lean_object*)&l_Lean_Firefox_categories___closed__3_value)}};
static const lean_object* l_Lean_Firefox_categories___closed__19 = (const lean_object*)&l_Lean_Firefox_categories___closed__19_value;
static const lean_string_object l_Lean_Firefox_categories___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Kernel"};
static const lean_object* l_Lean_Firefox_categories___closed__20 = (const lean_object*)&l_Lean_Firefox_categories___closed__20_value;
static const lean_ctor_object l_Lean_Firefox_categories___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Firefox_categories___closed__20_value),LEAN_SCALAR_PTR_LITERAL(213, 59, 86, 63, 192, 192, 9, 44)}};
static const lean_object* l_Lean_Firefox_categories___closed__21 = (const lean_object*)&l_Lean_Firefox_categories___closed__21_value;
static const lean_string_object l_Lean_Firefox_categories___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "green"};
static const lean_object* l_Lean_Firefox_categories___closed__22 = (const lean_object*)&l_Lean_Firefox_categories___closed__22_value;
static const lean_ctor_object l_Lean_Firefox_categories___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Firefox_categories___closed__21_value),((lean_object*)&l_Lean_Firefox_categories___closed__22_value),((lean_object*)&l_Lean_Firefox_categories___closed__3_value)}};
static const lean_object* l_Lean_Firefox_categories___closed__23 = (const lean_object*)&l_Lean_Firefox_categories___closed__23_value;
static const lean_array_object l_Lean_Firefox_categories___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*6, .m_other = 0, .m_tag = 246}, .m_size = 6, .m_capacity = 6, .m_data = {((lean_object*)&l_Lean_Firefox_categories___closed__4_value),((lean_object*)&l_Lean_Firefox_categories___closed__8_value),((lean_object*)&l_Lean_Firefox_categories___closed__12_value),((lean_object*)&l_Lean_Firefox_categories___closed__15_value),((lean_object*)&l_Lean_Firefox_categories___closed__19_value),((lean_object*)&l_Lean_Firefox_categories___closed__23_value)}};
static const lean_object* l_Lean_Firefox_categories___closed__24 = (const lean_object*)&l_Lean_Firefox_categories___closed__24_value;
LEAN_EXPORT const lean_object* l_Lean_Firefox_categories = (const lean_object*)&l_Lean_Firefox_categories___closed__24_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_getFirstStart_x3f_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_getFirstStart_x3f_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_getFirstStart_x3f_spec__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Util_Profiler_0__Lean_Firefox_getFirstStart_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Profiler_0__Lean_Firefox_getFirstStart_x3f___closed__0;
uint8_t lean_float_beq(double, double);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_getFirstStart_x3f_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Profiler_0__Lean_Firefox_getFirstStart_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_getFirstStart_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Profiler_0__Lean_Firefox_getFirstStart_x3f___boxed(lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go___lam__0___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__3_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__3_spec__7___redArg___boxed(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__1_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__2_spec__5___redArg(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__2_spec__4_spec__6_spec__11___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__2_spec__4_spec__6___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__2_spec__4___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__2_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__2___redArg(lean_object*, lean_object*, lean_object*);
uint64_t lean_string_hash(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__6_spec__16_spec__20_spec__23___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__6_spec__16_spec__20___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__6_spec__16___redArg(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__6_spec__17___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__6_spec__15___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__6_spec__15___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__5_spec__13___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__5_spec__13___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__4_spec__10_spec__13_spec__17___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__4_spec__10_spec__13___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__4_spec__10___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__4_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__4_spec__9___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__4_spec__11___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__4___redArg(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "tracing-ms"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__0___closed__0_value;
double l_Float_ofScientific(lean_object*, uint8_t, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go___boxed__const__1;
lean_object* lean_nat_to_int(lean_object*);
static lean_once_cell_t l___private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go___closed__1;
lean_object* lean_int_neg(lean_object*);
static lean_once_cell_t l___private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go___closed__2;
static const lean_array_object l___private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go___closed__3 = (const lean_object*)&l___private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go___closed__3_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
double lean_float_sub(double, double);
lean_object* l_Array_findIdx_x3f_loop___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_format(lean_object*, lean_object*);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__2_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__3_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__4_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__4_spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__4_spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__4_spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__5_spec__13(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__5_spec__13___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__6_spec__15(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__6_spec__15___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__6_spec__16(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__6_spec__17(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__2_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__4_spec__10_spec__13(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__6_spec__16_spec__20(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__2_spec__4_spec__6_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__4_spec__10_spec__13_spec__17(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__6_spec__16_spec__20_spec__23(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Profiler_0__Lean_Firefox_addTrace(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Profiler_0__Lean_Firefox_addTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Firefox_Thread_new___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "default"};
static const lean_object* l_Lean_Firefox_Thread_new___closed__0 = (const lean_object*)&l_Lean_Firefox_Thread_new___closed__0_value;
static const lean_array_object l_Lean_Firefox_Thread_new___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Firefox_Thread_new___closed__1 = (const lean_object*)&l_Lean_Firefox_Thread_new___closed__1_value;
static lean_once_cell_t l_Lean_Firefox_Thread_new___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_Thread_new___closed__2;
static lean_once_cell_t l_Lean_Firefox_Thread_new___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_Thread_new___closed__3;
static lean_once_cell_t l_Lean_Firefox_Thread_new___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_Thread_new___closed__4;
static const lean_ctor_object l_Lean_Firefox_Thread_new___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Firefox_Thread_new___closed__1_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Firefox_Thread_new___closed__5 = (const lean_object*)&l_Lean_Firefox_Thread_new___closed__5_value;
static lean_once_cell_t l_Lean_Firefox_Thread_new___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_Thread_new___closed__6;
LEAN_EXPORT lean_object* l_Lean_Firefox_Thread_new(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Firefox_Profile_export_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Firefox_Profile_export_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lean_Firefox_Profile_export___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Firefox_Profile_export___lam__0___boxed(lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__4___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Firefox_Profile_export_spec__5(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Firefox_Profile_export_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_float_decLt(double, double);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__6___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__6___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
LEAN_EXPORT double l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__6___redArg___lam__0(lean_object*, double, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__6___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__6___redArg___closed__0___boxed__const__1;
static lean_once_cell_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__6___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__6___redArg___closed__0;
static lean_once_cell_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__6___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__6___redArg___closed__1;
lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_trace_profiler_output_pp;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Firefox_Profile_export_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Firefox_Profile_export_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "runFrontend"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__7___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__7___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__7___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__7___closed__0_value),LEAN_SCALAR_PTR_LITERAL(29, 26, 219, 1, 125, 130, 35, 132)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__7___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__7___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__7___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__7___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__7___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__7___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__7___closed__2_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__7___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__7___closed__3_value;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__7___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__7___closed__4;
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__7___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__7___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__7___closed__5_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__7___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__7___closed__6;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__7___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__7___closed__7;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__7(lean_object*, double, double, lean_object*, size_t, size_t, lean_object*);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_uint64_to_nat(uint64_t);
lean_object* l_Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__2___redArg(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*);
static const lean_array_object l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__4___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__4___redArg___lam__0___closed__0 = (const lean_object*)&l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__4___redArg___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__4___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__4___redArg(lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__3_spec__14_spec__16___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__3_spec__14___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0___redArg(lean_object*, lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__1___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0___redArg___closed__0;
static lean_once_cell_t l_Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0___redArg___boxed(lean_object*, lean_object*);
uint8_t lean_uint64_dec_lt(uint64_t, uint64_t);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__9___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__9___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__9___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__9___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__9___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__9___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__9___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Firefox_Profile_export_spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Firefox_Profile_export_spec__10___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Firefox_Profile_export_spec__11(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Firefox_Profile_export_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__8(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__8___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Firefox_Profile_export___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Firefox_Profile_export___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Firefox_Profile_export___closed__0 = (const lean_object*)&l_Lean_Firefox_Profile_export___closed__0_value;
static lean_once_cell_t l_Lean_Firefox_Profile_export___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_Firefox_Profile_export___closed__1;
static const lean_string_object l_Lean_Firefox_Profile_export___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_Firefox_Profile_export___closed__2 = (const lean_object*)&l_Lean_Firefox_Profile_export___closed__2_value;
static const lean_string_object l_Lean_Firefox_Profile_export___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ms"};
static const lean_object* l_Lean_Firefox_Profile_export___closed__3 = (const lean_object*)&l_Lean_Firefox_Profile_export___closed__3_value;
static const lean_string_object l_Lean_Firefox_Profile_export___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 2, .m_data = "µs"};
static const lean_object* l_Lean_Firefox_Profile_export___closed__4 = (const lean_object*)&l_Lean_Firefox_Profile_export___closed__4_value;
static lean_once_cell_t l_Lean_Firefox_Profile_export___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_Profile_export___closed__5;
lean_object* lean_io_mono_nanos_now();
double lean_float_div(double, double);
LEAN_EXPORT lean_object* l_Lean_Firefox_Profile_export(lean_object*, double, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Firefox_Profile_export___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0(lean_object*, lean_object*, lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__2(lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__4(lean_object*, lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__3_spec__14(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__3_spec__14_spec__16(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Profiler_0__Lean_Firefox_collideThreads_getStrIdx(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Profiler_0__Lean_Firefox_collideThreads_collideStacks(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Profiler_0__Lean_Firefox_collideThreads_collideStacks___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_collideThreads_collideSamples_spec__0___redArg___boxed__const__1;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_collideThreads_collideSamples_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
double lean_float_add(double, double);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_collideThreads_collideSamples_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Profiler_0__Lean_Firefox_collideThreads_collideSamples(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Profiler_0__Lean_Firefox_collideThreads_collideSamples___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_collideThreads_collideSamples_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_collideThreads_collideSamples_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Profiler_0__Lean_Firefox_collideThreads(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Profiler_0__Lean_Firefox_collideThreads___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_collide_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_collide_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Firefox_Profile_collide_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Firefox_Profile_collide_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Firefox_Profile_collide_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Firefox_Profile_collide_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Firefox_Profile_collide___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "collided"};
static const lean_object* l_Lean_Firefox_Profile_collide___closed__0 = (const lean_object*)&l_Lean_Firefox_Profile_collide___closed__0_value;
static lean_once_cell_t l_Lean_Firefox_Profile_collide___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_Profile_collide___closed__1;
static lean_once_cell_t l_Lean_Firefox_Profile_collide___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_Profile_collide___closed__2;
static lean_once_cell_t l_Lean_Firefox_Profile_collide___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_Profile_collide___closed__3;
static const lean_array_object l_Lean_Firefox_Profile_collide___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Firefox_Profile_collide___closed__4 = (const lean_object*)&l_Lean_Firefox_Profile_collide___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Firefox_Profile_collide(lean_object*);
static double _init_l_Lean_Firefox_instInhabitedMilliseconds_default___closed__0(void) {
_start:
{
uint64_t x_1; double x_2; 
x_1 = 0;
x_2 = lean_uint64_to_float(x_1);
return x_2;
}
}
static double _init_l_Lean_Firefox_instInhabitedMilliseconds_default(void) {
_start:
{
double x_1; 
x_1 = lean_float_once(&l_Lean_Firefox_instInhabitedMilliseconds_default___closed__0, &l_Lean_Firefox_instInhabitedMilliseconds_default___closed__0_once, _init_l_Lean_Firefox_instInhabitedMilliseconds_default___closed__0);
return x_1;
}
}
static double _init_l_Lean_Firefox_instInhabitedMilliseconds(void) {
_start:
{
double x_1; 
x_1 = l_Lean_Firefox_instInhabitedMilliseconds_default;
return x_1;
}
}
static double _init_l_Lean_Firefox_instCoeFloatMilliseconds___lam__0___closed__0(void) {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(1000u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT double l_Lean_Firefox_instCoeFloatMilliseconds___lam__0(double x_1) {
_start:
{
double x_2; double x_3; 
x_2 = lean_float_once(&l_Lean_Firefox_instCoeFloatMilliseconds___lam__0___closed__0, &l_Lean_Firefox_instCoeFloatMilliseconds___lam__0___closed__0_once, _init_l_Lean_Firefox_instCoeFloatMilliseconds___lam__0___closed__0);
x_3 = lean_float_mul(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Firefox_instCoeFloatMilliseconds___lam__0___boxed(lean_object* x_1) {
_start:
{
double x_2; double x_3; lean_object* x_4; 
x_2 = lean_unbox_float(x_1);
lean_dec_ref(x_1);
x_3 = l_Lean_Firefox_instCoeFloatMilliseconds___lam__0(x_2);
x_4 = lean_box_float(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Firefox_instFromJsonMilliseconds___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Float_fromJson_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_10; 
x_3 = lean_ctor_get(x_2, 0);
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
x_4 = x_2;
x_5 = x_10;
goto block_9;
}
else
{
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = x_10;
goto block_9;
}
block_9:
{
lean_object* x_6; 
if (x_5 == 0)
{
x_6 = x_4;
goto block_7;
}
else
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_3);
x_6 = x_8;
goto block_7;
}
block_7:
{
return x_6;
}
}
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_18; 
x_11 = lean_ctor_get(x_2, 0);
x_18 = !lean_is_exclusive(x_2);
if (x_18 == 0)
{
x_12 = x_2;
x_13 = x_18;
goto block_17;
}
else
{
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_box(0);
x_13 = x_18;
goto block_17;
}
block_17:
{
lean_object* x_14; 
if (x_13 == 0)
{
x_14 = x_12;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_11);
x_14 = x_16;
goto block_15;
}
block_15:
{
return x_14;
}
}
}
}
}
static double _init_l_Lean_Firefox_instCoeFloatMicroseconds___lam__0___closed__0(void) {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(1000000u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT double l_Lean_Firefox_instCoeFloatMicroseconds___lam__0(double x_1) {
_start:
{
double x_2; double x_3; 
x_2 = lean_float_once(&l_Lean_Firefox_instCoeFloatMicroseconds___lam__0___closed__0, &l_Lean_Firefox_instCoeFloatMicroseconds___lam__0___closed__0_once, _init_l_Lean_Firefox_instCoeFloatMicroseconds___lam__0___closed__0);
x_3 = lean_float_mul(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Firefox_instCoeFloatMicroseconds___lam__0___boxed(lean_object* x_1) {
_start:
{
double x_2; double x_3; lean_object* x_4; 
x_2 = lean_unbox_float(x_1);
lean_dec_ref(x_1);
x_3 = l_Lean_Firefox_instCoeFloatMicroseconds___lam__0(x_2);
x_4 = lean_box_float(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l_Lean_Name_fromJson_x3f(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__0(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l_Lean_Json_getStr_x3f(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__1(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__2_spec__2_spec__3(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_7 = l_Lean_Json_getStr_x3f(x_6);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__2_spec__2_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__2_spec__2_spec__3(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__2_spec__2(lean_object* x_1) {
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
x_5 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__2_spec__2_spec__3(x_3, x_4, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__2_spec__2___closed__0));
x_7 = lean_unsigned_to_nat(80u);
x_8 = l_Lean_Json_pretty(x_1, x_7);
x_9 = lean_string_append(x_6, x_8);
lean_dec_ref(x_8);
x_10 = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__2_spec__2___closed__1));
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__2_spec__2(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__2(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonCategory_fromJson___closed__5(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__4));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonCategory_fromJson___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__6));
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonCategory_fromJson___closed__5, &l_Lean_Firefox_instFromJsonCategory_fromJson___closed__5_once, _init_l_Lean_Firefox_instFromJsonCategory_fromJson___closed__5);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonCategory_fromJson___closed__9(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__8));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonCategory_fromJson___closed__10(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Firefox_instFromJsonCategory_fromJson___closed__9, &l_Lean_Firefox_instFromJsonCategory_fromJson___closed__9_once, _init_l_Lean_Firefox_instFromJsonCategory_fromJson___closed__9);
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonCategory_fromJson___closed__7, &l_Lean_Firefox_instFromJsonCategory_fromJson___closed__7_once, _init_l_Lean_Firefox_instFromJsonCategory_fromJson___closed__7);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonCategory_fromJson___closed__12(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonCategory_fromJson___closed__10, &l_Lean_Firefox_instFromJsonCategory_fromJson___closed__10_once, _init_l_Lean_Firefox_instFromJsonCategory_fromJson___closed__10);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonCategory_fromJson___closed__15(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__14));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonCategory_fromJson___closed__16(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Firefox_instFromJsonCategory_fromJson___closed__15, &l_Lean_Firefox_instFromJsonCategory_fromJson___closed__15_once, _init_l_Lean_Firefox_instFromJsonCategory_fromJson___closed__15);
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonCategory_fromJson___closed__7, &l_Lean_Firefox_instFromJsonCategory_fromJson___closed__7_once, _init_l_Lean_Firefox_instFromJsonCategory_fromJson___closed__7);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonCategory_fromJson___closed__17(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonCategory_fromJson___closed__16, &l_Lean_Firefox_instFromJsonCategory_fromJson___closed__16_once, _init_l_Lean_Firefox_instFromJsonCategory_fromJson___closed__16);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonCategory_fromJson___closed__20(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__19));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonCategory_fromJson___closed__21(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Firefox_instFromJsonCategory_fromJson___closed__20, &l_Lean_Firefox_instFromJsonCategory_fromJson___closed__20_once, _init_l_Lean_Firefox_instFromJsonCategory_fromJson___closed__20);
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonCategory_fromJson___closed__7, &l_Lean_Firefox_instFromJsonCategory_fromJson___closed__7_once, _init_l_Lean_Firefox_instFromJsonCategory_fromJson___closed__7);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonCategory_fromJson___closed__22(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonCategory_fromJson___closed__21, &l_Lean_Firefox_instFromJsonCategory_fromJson___closed__21_once, _init_l_Lean_Firefox_instFromJsonCategory_fromJson___closed__21);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Firefox_instFromJsonCategory_fromJson(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__0));
lean_inc(x_1);
x_3 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__0(x_1, x_2);
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
x_7 = lean_obj_once(&l_Lean_Firefox_instFromJsonCategory_fromJson___closed__12, &l_Lean_Firefox_instFromJsonCategory_fromJson___closed__12_once, _init_l_Lean_Firefox_instFromJsonCategory_fromJson___closed__12);
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
x_23 = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__13));
lean_inc(x_1);
x_24 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__1(x_1, x_23);
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
x_28 = lean_obj_once(&l_Lean_Firefox_instFromJsonCategory_fromJson___closed__17, &l_Lean_Firefox_instFromJsonCategory_fromJson___closed__17_once, _init_l_Lean_Firefox_instFromJsonCategory_fromJson___closed__17);
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
x_44 = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__18));
x_45 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__2(x_1, x_44);
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
x_49 = lean_obj_once(&l_Lean_Firefox_instFromJsonCategory_fromJson___closed__22, &l_Lean_Firefox_instFromJsonCategory_fromJson___closed__22_once, _init_l_Lean_Firefox_instFromJsonCategory_fromJson___closed__22);
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
lean_object* x_64; lean_object* x_65; uint8_t x_66; uint8_t x_72; 
x_64 = lean_ctor_get(x_45, 0);
x_72 = !lean_is_exclusive(x_45);
if (x_72 == 0)
{
x_65 = x_45;
x_66 = x_72;
goto block_71;
}
else
{
lean_inc(x_64);
lean_dec(x_45);
x_65 = lean_box(0);
x_66 = x_72;
goto block_71;
}
block_71:
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_67, 0, x_22);
lean_ctor_set(x_67, 1, x_43);
lean_ctor_set(x_67, 2, x_64);
if (x_66 == 0)
{
lean_ctor_set(x_65, 0, x_67);
x_68 = x_65;
goto block_69;
}
else
{
lean_object* x_70; 
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_67);
x_68 = x_70;
goto block_69;
}
block_69:
{
return x_68;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Firefox_instToJsonCategory_toJson_spec__0_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_8 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_8, 0, x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Firefox_instToJsonCategory_toJson_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Firefox_instToJsonCategory_toJson_spec__0_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Firefox_instToJsonCategory_toJson_spec__0(lean_object* x_1) {
_start:
{
size_t x_2; size_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_array_size(x_1);
x_3 = 0;
x_4 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Firefox_instToJsonCategory_toJson_spec__0_spec__0(x_2, x_3, x_1);
x_5 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Firefox_instToJsonCategory_toJson_spec__1(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Firefox_instToJsonCategory_toJson(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_4);
lean_dec_ref(x_1);
x_5 = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__0));
x_6 = 1;
x_7 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_6);
x_8 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__13));
x_13 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_13, 0, x_3);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_10);
x_16 = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__18));
x_17 = l_Array_toJson___at___00Lean_Firefox_instToJsonCategory_toJson_spec__0(x_4);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_10);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_10);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_15);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_11);
lean_ctor_set(x_22, 1, x_21);
x_23 = ((lean_object*)(l_Lean_Firefox_instToJsonCategory_toJson___closed__0));
x_24 = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Firefox_instToJsonCategory_toJson_spec__1(x_22, x_23);
x_25 = l_Lean_Json_mkObj(x_24);
return x_25;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__3(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__2));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__6));
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__3, &l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__3_once, _init_l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__3);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__6(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__5));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__6, &l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__6_once, _init_l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__6);
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__4, &l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__4_once, _init_l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__4);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__8(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__7, &l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__7_once, _init_l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__7);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__11(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__10));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__12(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__11, &l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__11_once, _init_l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__11);
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__4, &l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__4_once, _init_l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__4);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__13(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__12, &l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__12_once, _init_l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__12);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__16(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__15));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__17(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__16, &l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__16_once, _init_l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__16);
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__4, &l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__4_once, _init_l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__4);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__18(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__17, &l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__17_once, _init_l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__17);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Firefox_instFromJsonSampleUnits_fromJson(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = ((lean_object*)(l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__0));
lean_inc(x_1);
x_3 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__1(x_1, x_2);
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
x_7 = lean_obj_once(&l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__8, &l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__8_once, _init_l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__8);
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
x_23 = ((lean_object*)(l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__9));
lean_inc(x_1);
x_24 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__1(x_1, x_23);
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
x_28 = lean_obj_once(&l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__13, &l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__13_once, _init_l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__13);
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
x_44 = ((lean_object*)(l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__14));
x_45 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__1(x_1, x_44);
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
x_49 = lean_obj_once(&l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__18, &l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__18_once, _init_l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__18);
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
lean_object* x_64; lean_object* x_65; uint8_t x_66; uint8_t x_72; 
x_64 = lean_ctor_get(x_45, 0);
x_72 = !lean_is_exclusive(x_45);
if (x_72 == 0)
{
x_65 = x_45;
x_66 = x_72;
goto block_71;
}
else
{
lean_inc(x_64);
lean_dec(x_45);
x_65 = lean_box(0);
x_66 = x_72;
goto block_71;
}
block_71:
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_67, 0, x_22);
lean_ctor_set(x_67, 1, x_43);
lean_ctor_set(x_67, 2, x_64);
if (x_66 == 0)
{
lean_ctor_set(x_65, 0, x_67);
x_68 = x_65;
goto block_69;
}
else
{
lean_object* x_70; 
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_67);
x_68 = x_70;
goto block_69;
}
block_69:
{
return x_68;
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
LEAN_EXPORT lean_object* l_Lean_Firefox_instToJsonSampleUnits_toJson(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
x_5 = ((lean_object*)(l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__0));
lean_inc_ref(x_2);
x_6 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_6, 0, x_2);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = ((lean_object*)(l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__9));
lean_inc_ref(x_3);
x_11 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_11, 0, x_3);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_8);
x_14 = ((lean_object*)(l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__14));
lean_inc_ref(x_4);
x_15 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_15, 0, x_4);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_8);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_8);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_9);
lean_ctor_set(x_20, 1, x_19);
x_21 = ((lean_object*)(l_Lean_Firefox_instToJsonCategory_toJson___closed__0));
x_22 = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Firefox_instToJsonCategory_toJson_spec__1(x_20, x_21);
x_23 = l_Lean_Json_mkObj(x_22);
return x_23;
}
}
LEAN_EXPORT lean_object* l_Lean_Firefox_instToJsonSampleUnits_toJson___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Firefox_instToJsonSampleUnits_toJson(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l_Float_fromJson_x3f(x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_12; 
x_5 = lean_ctor_get(x_4, 0);
x_12 = !lean_is_exclusive(x_4);
if (x_12 == 0)
{
x_6 = x_4;
x_7 = x_12;
goto block_11;
}
else
{
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_box(0);
x_7 = x_12;
goto block_11;
}
block_11:
{
lean_object* x_8; 
if (x_7 == 0)
{
x_8 = x_6;
goto block_9;
}
else
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_5);
x_8 = x_10;
goto block_9;
}
block_9:
{
return x_8;
}
}
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_20; 
x_13 = lean_ctor_get(x_4, 0);
x_20 = !lean_is_exclusive(x_4);
if (x_20 == 0)
{
x_14 = x_4;
x_15 = x_20;
goto block_19;
}
else
{
lean_inc(x_13);
lean_dec(x_4);
x_14 = lean_box(0);
x_15 = x_20;
goto block_19;
}
block_19:
{
lean_object* x_16; 
if (x_15 == 0)
{
x_16 = x_14;
goto block_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_13);
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
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__0(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l_Lean_Json_getNat_x3f(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__2(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l_Lean_Firefox_instFromJsonSampleUnits_fromJson(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__4(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__1_spec__1_spec__4(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_7 = l_Lean_Firefox_instFromJsonCategory_fromJson(x_6);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__1_spec__1_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__1_spec__1_spec__4(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__1_spec__1(lean_object* x_1) {
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
x_5 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__1_spec__1_spec__4(x_3, x_4, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__2_spec__2___closed__0));
x_7 = lean_unsigned_to_nat(80u);
x_8 = l_Lean_Json_pretty(x_1, x_7);
x_9 = lean_string_append(x_6, x_8);
lean_dec_ref(x_8);
x_10 = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__2_spec__2___closed__1));
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__1_spec__1(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__1(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__3_spec__4_spec__7(size_t x_1, size_t x_2, lean_object* x_3) {
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_6 = lean_array_uget(x_3, x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_8, x_2, x_6);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__3_spec__4_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__3_spec__4_spec__7(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__3_spec__4(lean_object* x_1) {
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
x_5 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__3_spec__4_spec__7(x_3, x_4, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__2_spec__2___closed__0));
x_7 = lean_unsigned_to_nat(80u);
x_8 = l_Lean_Json_pretty(x_1, x_7);
x_9 = lean_string_append(x_6, x_8);
lean_dec_ref(x_8);
x_10 = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__2_spec__2___closed__1));
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__3_spec__4(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__3(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__3(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__2));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__6));
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__3, &l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__3_once, _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__3);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__6(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__5));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__6, &l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__6_once, _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__6);
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__4, &l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__4_once, _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__4);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__8(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__7, &l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__7_once, _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__7);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__11(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__10));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__12(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__11, &l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__11_once, _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__11);
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__4, &l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__4_once, _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__4);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__13(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__12, &l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__12_once, _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__12);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__16(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__15));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__17(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__16, &l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__16_once, _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__16);
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__4, &l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__4_once, _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__4);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__18(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__17, &l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__17_once, _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__17);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__21(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__20));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__22(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__21, &l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__21_once, _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__21);
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__4, &l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__4_once, _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__4);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__23(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__22, &l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__22_once, _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__22);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__26(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__25));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__27(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__26, &l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__26_once, _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__26);
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__4, &l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__4_once, _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__4);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__28(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__27, &l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__27_once, _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__27);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__31(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__30));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__32(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__31, &l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__31_once, _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__31);
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__4, &l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__4_once, _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__4);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__33(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__32, &l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__32_once, _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__32);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__36(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__35));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__37(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__36, &l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__36_once, _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__36);
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__4, &l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__4_once, _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__4);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__38(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__37, &l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__37_once, _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__37);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__41(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__40));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__42(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__41, &l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__41_once, _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__41);
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__4, &l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__4_once, _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__4);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__43(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__42, &l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__42_once, _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__42);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Firefox_instFromJsonProfileMeta_fromJson(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = ((lean_object*)(l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__0));
lean_inc(x_1);
x_3 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__0(x_1, x_2);
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
x_7 = lean_obj_once(&l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__8, &l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__8_once, _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__8);
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
x_23 = ((lean_object*)(l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__9));
lean_inc(x_1);
x_24 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__0(x_1, x_23);
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
x_28 = lean_obj_once(&l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__13, &l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__13_once, _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__13);
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
x_44 = ((lean_object*)(l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__14));
lean_inc(x_1);
x_45 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__1(x_1, x_44);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_55; 
lean_dec(x_43);
lean_dec(x_22);
lean_dec(x_1);
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
x_49 = lean_obj_once(&l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__18, &l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__18_once, _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__18);
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
lean_dec(x_1);
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
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_45, 0);
lean_inc(x_64);
lean_dec_ref(x_45);
x_65 = ((lean_object*)(l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__19));
lean_inc(x_1);
x_66 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__2(x_1, x_65);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; uint8_t x_76; 
lean_dec(x_64);
lean_dec(x_43);
lean_dec(x_22);
lean_dec(x_1);
x_67 = lean_ctor_get(x_66, 0);
x_76 = !lean_is_exclusive(x_66);
if (x_76 == 0)
{
x_68 = x_66;
x_69 = x_76;
goto block_75;
}
else
{
lean_inc(x_67);
lean_dec(x_66);
x_68 = lean_box(0);
x_69 = x_76;
goto block_75;
}
block_75:
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_obj_once(&l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__23, &l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__23_once, _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__23);
x_71 = lean_string_append(x_70, x_67);
lean_dec(x_67);
if (x_69 == 0)
{
lean_ctor_set(x_68, 0, x_71);
x_72 = x_68;
goto block_73;
}
else
{
lean_object* x_74; 
x_74 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_74, 0, x_71);
x_72 = x_74;
goto block_73;
}
block_73:
{
return x_72;
}
}
}
else
{
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_77; lean_object* x_78; uint8_t x_79; uint8_t x_84; 
lean_dec(x_64);
lean_dec(x_43);
lean_dec(x_22);
lean_dec(x_1);
x_77 = lean_ctor_get(x_66, 0);
x_84 = !lean_is_exclusive(x_66);
if (x_84 == 0)
{
x_78 = x_66;
x_79 = x_84;
goto block_83;
}
else
{
lean_inc(x_77);
lean_dec(x_66);
x_78 = lean_box(0);
x_79 = x_84;
goto block_83;
}
block_83:
{
lean_object* x_80; 
if (x_79 == 0)
{
lean_ctor_set_tag(x_78, 0);
x_80 = x_78;
goto block_81;
}
else
{
lean_object* x_82; 
x_82 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_82, 0, x_77);
x_80 = x_82;
goto block_81;
}
block_81:
{
return x_80;
}
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_66, 0);
lean_inc(x_85);
lean_dec_ref(x_66);
x_86 = ((lean_object*)(l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__24));
lean_inc(x_1);
x_87 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__1(x_1, x_86);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; uint8_t x_90; uint8_t x_97; 
lean_dec(x_85);
lean_dec(x_64);
lean_dec(x_43);
lean_dec(x_22);
lean_dec(x_1);
x_88 = lean_ctor_get(x_87, 0);
x_97 = !lean_is_exclusive(x_87);
if (x_97 == 0)
{
x_89 = x_87;
x_90 = x_97;
goto block_96;
}
else
{
lean_inc(x_88);
lean_dec(x_87);
x_89 = lean_box(0);
x_90 = x_97;
goto block_96;
}
block_96:
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_obj_once(&l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__28, &l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__28_once, _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__28);
x_92 = lean_string_append(x_91, x_88);
lean_dec(x_88);
if (x_90 == 0)
{
lean_ctor_set(x_89, 0, x_92);
x_93 = x_89;
goto block_94;
}
else
{
lean_object* x_95; 
x_95 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_95, 0, x_92);
x_93 = x_95;
goto block_94;
}
block_94:
{
return x_93;
}
}
}
else
{
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_98; lean_object* x_99; uint8_t x_100; uint8_t x_105; 
lean_dec(x_85);
lean_dec(x_64);
lean_dec(x_43);
lean_dec(x_22);
lean_dec(x_1);
x_98 = lean_ctor_get(x_87, 0);
x_105 = !lean_is_exclusive(x_87);
if (x_105 == 0)
{
x_99 = x_87;
x_100 = x_105;
goto block_104;
}
else
{
lean_inc(x_98);
lean_dec(x_87);
x_99 = lean_box(0);
x_100 = x_105;
goto block_104;
}
block_104:
{
lean_object* x_101; 
if (x_100 == 0)
{
lean_ctor_set_tag(x_99, 0);
x_101 = x_99;
goto block_102;
}
else
{
lean_object* x_103; 
x_103 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_103, 0, x_98);
x_101 = x_103;
goto block_102;
}
block_102:
{
return x_101;
}
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_87, 0);
lean_inc(x_106);
lean_dec_ref(x_87);
x_107 = ((lean_object*)(l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__29));
lean_inc(x_1);
x_108 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__2(x_1, x_107);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; uint8_t x_111; uint8_t x_118; 
lean_dec(x_106);
lean_dec(x_85);
lean_dec(x_64);
lean_dec(x_43);
lean_dec(x_22);
lean_dec(x_1);
x_109 = lean_ctor_get(x_108, 0);
x_118 = !lean_is_exclusive(x_108);
if (x_118 == 0)
{
x_110 = x_108;
x_111 = x_118;
goto block_117;
}
else
{
lean_inc(x_109);
lean_dec(x_108);
x_110 = lean_box(0);
x_111 = x_118;
goto block_117;
}
block_117:
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_obj_once(&l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__33, &l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__33_once, _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__33);
x_113 = lean_string_append(x_112, x_109);
lean_dec(x_109);
if (x_111 == 0)
{
lean_ctor_set(x_110, 0, x_113);
x_114 = x_110;
goto block_115;
}
else
{
lean_object* x_116; 
x_116 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_116, 0, x_113);
x_114 = x_116;
goto block_115;
}
block_115:
{
return x_114;
}
}
}
else
{
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_119; lean_object* x_120; uint8_t x_121; uint8_t x_126; 
lean_dec(x_106);
lean_dec(x_85);
lean_dec(x_64);
lean_dec(x_43);
lean_dec(x_22);
lean_dec(x_1);
x_119 = lean_ctor_get(x_108, 0);
x_126 = !lean_is_exclusive(x_108);
if (x_126 == 0)
{
x_120 = x_108;
x_121 = x_126;
goto block_125;
}
else
{
lean_inc(x_119);
lean_dec(x_108);
x_120 = lean_box(0);
x_121 = x_126;
goto block_125;
}
block_125:
{
lean_object* x_122; 
if (x_121 == 0)
{
lean_ctor_set_tag(x_120, 0);
x_122 = x_120;
goto block_123;
}
else
{
lean_object* x_124; 
x_124 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_124, 0, x_119);
x_122 = x_124;
goto block_123;
}
block_123:
{
return x_122;
}
}
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_108, 0);
lean_inc(x_127);
lean_dec_ref(x_108);
x_128 = ((lean_object*)(l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__34));
lean_inc(x_1);
x_129 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__3(x_1, x_128);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; uint8_t x_132; uint8_t x_139; 
lean_dec(x_127);
lean_dec(x_106);
lean_dec(x_85);
lean_dec(x_64);
lean_dec(x_43);
lean_dec(x_22);
lean_dec(x_1);
x_130 = lean_ctor_get(x_129, 0);
x_139 = !lean_is_exclusive(x_129);
if (x_139 == 0)
{
x_131 = x_129;
x_132 = x_139;
goto block_138;
}
else
{
lean_inc(x_130);
lean_dec(x_129);
x_131 = lean_box(0);
x_132 = x_139;
goto block_138;
}
block_138:
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_obj_once(&l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__38, &l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__38_once, _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__38);
x_134 = lean_string_append(x_133, x_130);
lean_dec(x_130);
if (x_132 == 0)
{
lean_ctor_set(x_131, 0, x_134);
x_135 = x_131;
goto block_136;
}
else
{
lean_object* x_137; 
x_137 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_137, 0, x_134);
x_135 = x_137;
goto block_136;
}
block_136:
{
return x_135;
}
}
}
else
{
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_140; lean_object* x_141; uint8_t x_142; uint8_t x_147; 
lean_dec(x_127);
lean_dec(x_106);
lean_dec(x_85);
lean_dec(x_64);
lean_dec(x_43);
lean_dec(x_22);
lean_dec(x_1);
x_140 = lean_ctor_get(x_129, 0);
x_147 = !lean_is_exclusive(x_129);
if (x_147 == 0)
{
x_141 = x_129;
x_142 = x_147;
goto block_146;
}
else
{
lean_inc(x_140);
lean_dec(x_129);
x_141 = lean_box(0);
x_142 = x_147;
goto block_146;
}
block_146:
{
lean_object* x_143; 
if (x_142 == 0)
{
lean_ctor_set_tag(x_141, 0);
x_143 = x_141;
goto block_144;
}
else
{
lean_object* x_145; 
x_145 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_145, 0, x_140);
x_143 = x_145;
goto block_144;
}
block_144:
{
return x_143;
}
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_148 = lean_ctor_get(x_129, 0);
lean_inc(x_148);
lean_dec_ref(x_129);
x_149 = ((lean_object*)(l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__39));
x_150 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__4(x_1, x_149);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; lean_object* x_152; uint8_t x_153; uint8_t x_160; 
lean_dec(x_148);
lean_dec(x_127);
lean_dec(x_106);
lean_dec(x_85);
lean_dec(x_64);
lean_dec(x_43);
lean_dec(x_22);
x_151 = lean_ctor_get(x_150, 0);
x_160 = !lean_is_exclusive(x_150);
if (x_160 == 0)
{
x_152 = x_150;
x_153 = x_160;
goto block_159;
}
else
{
lean_inc(x_151);
lean_dec(x_150);
x_152 = lean_box(0);
x_153 = x_160;
goto block_159;
}
block_159:
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_154 = lean_obj_once(&l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__43, &l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__43_once, _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__43);
x_155 = lean_string_append(x_154, x_151);
lean_dec(x_151);
if (x_153 == 0)
{
lean_ctor_set(x_152, 0, x_155);
x_156 = x_152;
goto block_157;
}
else
{
lean_object* x_158; 
x_158 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_158, 0, x_155);
x_156 = x_158;
goto block_157;
}
block_157:
{
return x_156;
}
}
}
else
{
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_161; lean_object* x_162; uint8_t x_163; uint8_t x_168; 
lean_dec(x_148);
lean_dec(x_127);
lean_dec(x_106);
lean_dec(x_85);
lean_dec(x_64);
lean_dec(x_43);
lean_dec(x_22);
x_161 = lean_ctor_get(x_150, 0);
x_168 = !lean_is_exclusive(x_150);
if (x_168 == 0)
{
x_162 = x_150;
x_163 = x_168;
goto block_167;
}
else
{
lean_inc(x_161);
lean_dec(x_150);
x_162 = lean_box(0);
x_163 = x_168;
goto block_167;
}
block_167:
{
lean_object* x_164; 
if (x_163 == 0)
{
lean_ctor_set_tag(x_162, 0);
x_164 = x_162;
goto block_165;
}
else
{
lean_object* x_166; 
x_166 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_166, 0, x_161);
x_164 = x_166;
goto block_165;
}
block_165:
{
return x_164;
}
}
}
else
{
lean_object* x_169; lean_object* x_170; uint8_t x_171; uint8_t x_179; 
x_169 = lean_ctor_get(x_150, 0);
x_179 = !lean_is_exclusive(x_150);
if (x_179 == 0)
{
x_170 = x_150;
x_171 = x_179;
goto block_178;
}
else
{
lean_inc(x_169);
lean_dec(x_150);
x_170 = lean_box(0);
x_171 = x_179;
goto block_178;
}
block_178:
{
lean_object* x_172; double x_173; double x_174; lean_object* x_175; 
x_172 = lean_alloc_ctor(0, 6, 16);
lean_ctor_set(x_172, 0, x_64);
lean_ctor_set(x_172, 1, x_85);
lean_ctor_set(x_172, 2, x_106);
lean_ctor_set(x_172, 3, x_127);
lean_ctor_set(x_172, 4, x_148);
lean_ctor_set(x_172, 5, x_169);
x_173 = lean_unbox_float(x_22);
lean_dec(x_22);
lean_ctor_set_float(x_172, sizeof(void*)*6, x_173);
x_174 = lean_unbox_float(x_43);
lean_dec(x_43);
lean_ctor_set_float(x_172, sizeof(void*)*6 + 8, x_174);
if (x_171 == 0)
{
lean_ctor_set(x_170, 0, x_172);
x_175 = x_170;
goto block_176;
}
else
{
lean_object* x_177; 
x_177 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_177, 0, x_172);
x_175 = x_177;
goto block_176;
}
block_176:
{
return x_175;
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
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Firefox_instToJsonProfileMeta_toJson_spec__1_spec__2(size_t x_1, size_t x_2, lean_object* x_3) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_10 = lean_array_uset(x_7, x_2, x_5);
x_2 = x_9;
x_3 = x_10;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Firefox_instToJsonProfileMeta_toJson_spec__1_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Firefox_instToJsonProfileMeta_toJson_spec__1_spec__2(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Firefox_instToJsonProfileMeta_toJson_spec__1(lean_object* x_1) {
_start:
{
size_t x_2; size_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_array_size(x_1);
x_3 = 0;
x_4 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Firefox_instToJsonProfileMeta_toJson_spec__1_spec__2(x_2, x_3, x_1);
x_5 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Firefox_instToJsonProfileMeta_toJson_spec__0_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_8 = l_Lean_Firefox_instToJsonCategory_toJson(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Firefox_instToJsonProfileMeta_toJson_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Firefox_instToJsonProfileMeta_toJson_spec__0_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Firefox_instToJsonProfileMeta_toJson_spec__0(lean_object* x_1) {
_start:
{
size_t x_2; size_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_array_size(x_1);
x_3 = 0;
x_4 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Firefox_instToJsonProfileMeta_toJson_spec__0_spec__0(x_2, x_3, x_1);
x_5 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Firefox_instToJsonProfileMeta_toJson(lean_object* x_1) {
_start:
{
double x_2; double x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_2 = lean_ctor_get_float(x_1, sizeof(void*)*6);
x_3 = lean_ctor_get_float(x_1, sizeof(void*)*6 + 8);
x_4 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 4);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_1, 5);
lean_inc_ref(x_9);
lean_dec_ref(x_1);
x_10 = ((lean_object*)(l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__0));
x_11 = l_Float_toJson(x_2);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = ((lean_object*)(l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__9));
x_16 = l_Float_toJson(x_3);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_13);
x_19 = ((lean_object*)(l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__14));
x_20 = l_Array_toJson___at___00Lean_Firefox_instToJsonProfileMeta_toJson_spec__0(x_4);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_13);
x_23 = ((lean_object*)(l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__19));
x_24 = l_Lean_JsonNumber_fromNat(x_5);
x_25 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_13);
x_28 = ((lean_object*)(l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__24));
x_29 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_29, 0, x_6);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_13);
x_32 = ((lean_object*)(l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__29));
x_33 = l_Lean_JsonNumber_fromNat(x_7);
x_34 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_13);
x_37 = ((lean_object*)(l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__34));
x_38 = l_Array_toJson___at___00Lean_Firefox_instToJsonProfileMeta_toJson_spec__1(x_8);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_13);
x_41 = ((lean_object*)(l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__39));
x_42 = l_Lean_Firefox_instToJsonSampleUnits_toJson(x_9);
lean_dec_ref(x_9);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_13);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_13);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_40);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_36);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_31);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_27);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_22);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_18);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_14);
lean_ctor_set(x_52, 1, x_51);
x_53 = ((lean_object*)(l_Lean_Firefox_instToJsonCategory_toJson___closed__0));
x_54 = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Firefox_instToJsonCategory_toJson_spec__1(x_52, x_53);
x_55 = l_Lean_Json_mkObj(x_54);
return x_55;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonStackTable_fromJson_spec__0_spec__0_spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_7 = l_Lean_Json_getNat_x3f(x_6);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonStackTable_fromJson_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonStackTable_fromJson_spec__0_spec__0_spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonStackTable_fromJson_spec__0_spec__0(lean_object* x_1) {
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
x_5 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonStackTable_fromJson_spec__0_spec__0_spec__1(x_3, x_4, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__2_spec__2___closed__0));
x_7 = lean_unsigned_to_nat(80u);
x_8 = l_Lean_Json_pretty(x_1, x_7);
x_9 = lean_string_append(x_6, x_8);
lean_dec_ref(x_8);
x_10 = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__2_spec__2___closed__1));
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonStackTable_fromJson_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonStackTable_fromJson_spec__0_spec__0(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonStackTable_fromJson_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonStackTable_fromJson_spec__0(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonStackTable_fromJson_spec__1_spec__2_spec__4(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_Option_fromJson_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonStackTable_fromJson_spec__1_spec__2_spec__4___closed__0));
return x_2;
}
else
{
lean_object* x_3; 
x_3 = l_Lean_Json_getNat_x3f(x_1);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonStackTable_fromJson_spec__1_spec__2_spec__5(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_7 = l_Option_fromJson_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonStackTable_fromJson_spec__1_spec__2_spec__4(x_6);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonStackTable_fromJson_spec__1_spec__2_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonStackTable_fromJson_spec__1_spec__2_spec__5(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonStackTable_fromJson_spec__1_spec__2(lean_object* x_1) {
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
x_5 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonStackTable_fromJson_spec__1_spec__2_spec__5(x_3, x_4, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__2_spec__2___closed__0));
x_7 = lean_unsigned_to_nat(80u);
x_8 = l_Lean_Json_pretty(x_1, x_7);
x_9 = lean_string_append(x_6, x_8);
lean_dec_ref(x_8);
x_10 = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__2_spec__2___closed__1));
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonStackTable_fromJson_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonStackTable_fromJson_spec__1_spec__2(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonStackTable_fromJson_spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonStackTable_fromJson_spec__1(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__3(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__2));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__6));
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__3, &l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__3_once, _init_l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__3);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__6(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__5));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__6, &l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__6_once, _init_l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__6);
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__4, &l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__4_once, _init_l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__4);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__8(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__7, &l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__7_once, _init_l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__7);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__11(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__10));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__12(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__11, &l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__11_once, _init_l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__11);
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__4, &l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__4_once, _init_l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__4);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__13(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__12, &l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__12_once, _init_l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__12);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__16(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__15));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__17(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__16, &l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__16_once, _init_l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__16);
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__4, &l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__4_once, _init_l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__4);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__18(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__17, &l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__17_once, _init_l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__17);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__21(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__20));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__22(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__21, &l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__21_once, _init_l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__21);
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__4, &l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__4_once, _init_l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__4);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__23(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__22, &l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__22_once, _init_l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__22);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__26(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__25));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__27(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__26, &l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__26_once, _init_l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__26);
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__4, &l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__4_once, _init_l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__4);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__28(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__27, &l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__27_once, _init_l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__27);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Firefox_instFromJsonStackTable_fromJson(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = ((lean_object*)(l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__0));
lean_inc(x_1);
x_3 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonStackTable_fromJson_spec__0(x_1, x_2);
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
x_7 = lean_obj_once(&l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__8, &l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__8_once, _init_l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__8);
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
x_23 = ((lean_object*)(l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__9));
lean_inc(x_1);
x_24 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonStackTable_fromJson_spec__0(x_1, x_23);
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
x_28 = lean_obj_once(&l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__13, &l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__13_once, _init_l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__13);
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
x_44 = ((lean_object*)(l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__14));
lean_inc(x_1);
x_45 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonStackTable_fromJson_spec__0(x_1, x_44);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_55; 
lean_dec(x_43);
lean_dec(x_22);
lean_dec(x_1);
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
x_49 = lean_obj_once(&l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__18, &l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__18_once, _init_l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__18);
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
lean_dec(x_1);
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
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_45, 0);
lean_inc(x_64);
lean_dec_ref(x_45);
x_65 = ((lean_object*)(l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__19));
lean_inc(x_1);
x_66 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonStackTable_fromJson_spec__1(x_1, x_65);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; uint8_t x_76; 
lean_dec(x_64);
lean_dec(x_43);
lean_dec(x_22);
lean_dec(x_1);
x_67 = lean_ctor_get(x_66, 0);
x_76 = !lean_is_exclusive(x_66);
if (x_76 == 0)
{
x_68 = x_66;
x_69 = x_76;
goto block_75;
}
else
{
lean_inc(x_67);
lean_dec(x_66);
x_68 = lean_box(0);
x_69 = x_76;
goto block_75;
}
block_75:
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_obj_once(&l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__23, &l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__23_once, _init_l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__23);
x_71 = lean_string_append(x_70, x_67);
lean_dec(x_67);
if (x_69 == 0)
{
lean_ctor_set(x_68, 0, x_71);
x_72 = x_68;
goto block_73;
}
else
{
lean_object* x_74; 
x_74 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_74, 0, x_71);
x_72 = x_74;
goto block_73;
}
block_73:
{
return x_72;
}
}
}
else
{
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_77; lean_object* x_78; uint8_t x_79; uint8_t x_84; 
lean_dec(x_64);
lean_dec(x_43);
lean_dec(x_22);
lean_dec(x_1);
x_77 = lean_ctor_get(x_66, 0);
x_84 = !lean_is_exclusive(x_66);
if (x_84 == 0)
{
x_78 = x_66;
x_79 = x_84;
goto block_83;
}
else
{
lean_inc(x_77);
lean_dec(x_66);
x_78 = lean_box(0);
x_79 = x_84;
goto block_83;
}
block_83:
{
lean_object* x_80; 
if (x_79 == 0)
{
lean_ctor_set_tag(x_78, 0);
x_80 = x_78;
goto block_81;
}
else
{
lean_object* x_82; 
x_82 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_82, 0, x_77);
x_80 = x_82;
goto block_81;
}
block_81:
{
return x_80;
}
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_66, 0);
lean_inc(x_85);
lean_dec_ref(x_66);
x_86 = ((lean_object*)(l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__24));
x_87 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__2(x_1, x_86);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; uint8_t x_90; uint8_t x_97; 
lean_dec(x_85);
lean_dec(x_64);
lean_dec(x_43);
lean_dec(x_22);
x_88 = lean_ctor_get(x_87, 0);
x_97 = !lean_is_exclusive(x_87);
if (x_97 == 0)
{
x_89 = x_87;
x_90 = x_97;
goto block_96;
}
else
{
lean_inc(x_88);
lean_dec(x_87);
x_89 = lean_box(0);
x_90 = x_97;
goto block_96;
}
block_96:
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_obj_once(&l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__28, &l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__28_once, _init_l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__28);
x_92 = lean_string_append(x_91, x_88);
lean_dec(x_88);
if (x_90 == 0)
{
lean_ctor_set(x_89, 0, x_92);
x_93 = x_89;
goto block_94;
}
else
{
lean_object* x_95; 
x_95 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_95, 0, x_92);
x_93 = x_95;
goto block_94;
}
block_94:
{
return x_93;
}
}
}
else
{
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_98; lean_object* x_99; uint8_t x_100; uint8_t x_105; 
lean_dec(x_85);
lean_dec(x_64);
lean_dec(x_43);
lean_dec(x_22);
x_98 = lean_ctor_get(x_87, 0);
x_105 = !lean_is_exclusive(x_87);
if (x_105 == 0)
{
x_99 = x_87;
x_100 = x_105;
goto block_104;
}
else
{
lean_inc(x_98);
lean_dec(x_87);
x_99 = lean_box(0);
x_100 = x_105;
goto block_104;
}
block_104:
{
lean_object* x_101; 
if (x_100 == 0)
{
lean_ctor_set_tag(x_99, 0);
x_101 = x_99;
goto block_102;
}
else
{
lean_object* x_103; 
x_103 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_103, 0, x_98);
x_101 = x_103;
goto block_102;
}
block_102:
{
return x_101;
}
}
}
else
{
lean_object* x_106; lean_object* x_107; uint8_t x_108; uint8_t x_114; 
x_106 = lean_ctor_get(x_87, 0);
x_114 = !lean_is_exclusive(x_87);
if (x_114 == 0)
{
x_107 = x_87;
x_108 = x_114;
goto block_113;
}
else
{
lean_inc(x_106);
lean_dec(x_87);
x_107 = lean_box(0);
x_108 = x_114;
goto block_113;
}
block_113:
{
lean_object* x_109; lean_object* x_110; 
x_109 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_109, 0, x_22);
lean_ctor_set(x_109, 1, x_43);
lean_ctor_set(x_109, 2, x_64);
lean_ctor_set(x_109, 3, x_85);
lean_ctor_set(x_109, 4, x_106);
if (x_108 == 0)
{
lean_ctor_set(x_107, 0, x_109);
x_110 = x_107;
goto block_111;
}
else
{
lean_object* x_112; 
x_112 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_112, 0, x_109);
x_110 = x_112;
goto block_111;
}
block_111:
{
return x_110;
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
}
}
LEAN_EXPORT lean_object* l_Option_toJson___at___00Array_toJson___at___00Lean_Firefox_instToJsonStackTable_toJson_spec__1_spec__2(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_11; 
x_3 = lean_ctor_get(x_1, 0);
x_11 = !lean_is_exclusive(x_1);
if (x_11 == 0)
{
x_4 = x_1;
x_5 = x_11;
goto block_10;
}
else
{
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_box(0);
x_5 = x_11;
goto block_10;
}
block_10:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_JsonNumber_fromNat(x_3);
if (x_5 == 0)
{
lean_ctor_set_tag(x_4, 2);
lean_ctor_set(x_4, 0, x_6);
x_7 = x_4;
goto block_8;
}
else
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_9, 0, x_6);
x_7 = x_9;
goto block_8;
}
block_8:
{
return x_7;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Firefox_instToJsonStackTable_toJson_spec__1_spec__3(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_8 = l_Option_toJson___at___00Array_toJson___at___00Lean_Firefox_instToJsonStackTable_toJson_spec__1_spec__2(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Firefox_instToJsonStackTable_toJson_spec__1_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Firefox_instToJsonStackTable_toJson_spec__1_spec__3(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Firefox_instToJsonStackTable_toJson_spec__1(lean_object* x_1) {
_start:
{
size_t x_2; size_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_array_size(x_1);
x_3 = 0;
x_4 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Firefox_instToJsonStackTable_toJson_spec__1_spec__3(x_2, x_3, x_1);
x_5 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Firefox_instToJsonStackTable_toJson_spec__0_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l_Lean_JsonNumber_fromNat(x_5);
x_9 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = 1;
x_11 = lean_usize_add(x_2, x_10);
x_12 = lean_array_uset(x_7, x_2, x_9);
x_2 = x_11;
x_3 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Firefox_instToJsonStackTable_toJson_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Firefox_instToJsonStackTable_toJson_spec__0_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Firefox_instToJsonStackTable_toJson_spec__0(lean_object* x_1) {
_start:
{
size_t x_2; size_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_array_size(x_1);
x_3 = 0;
x_4 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Firefox_instToJsonStackTable_toJson_spec__0_spec__0(x_2, x_3, x_1);
x_5 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Firefox_instToJsonStackTable_toJson(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_1, 4);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = ((lean_object*)(l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__0));
x_8 = l_Array_toJson___at___00Lean_Firefox_instToJsonStackTable_toJson_spec__0(x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = ((lean_object*)(l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__9));
x_13 = l_Array_toJson___at___00Lean_Firefox_instToJsonStackTable_toJson_spec__0(x_3);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_10);
x_16 = ((lean_object*)(l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__14));
x_17 = l_Array_toJson___at___00Lean_Firefox_instToJsonStackTable_toJson_spec__0(x_4);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_10);
x_20 = ((lean_object*)(l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__19));
x_21 = l_Array_toJson___at___00Lean_Firefox_instToJsonStackTable_toJson_spec__1(x_5);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_10);
x_24 = ((lean_object*)(l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__24));
x_25 = l_Lean_JsonNumber_fromNat(x_6);
x_26 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_10);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_10);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_23);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_19);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_15);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_11);
lean_ctor_set(x_33, 1, x_32);
x_34 = ((lean_object*)(l_Lean_Firefox_instToJsonCategory_toJson___closed__0));
x_35 = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Firefox_instToJsonCategory_toJson_spec__1(x_33, x_34);
x_36 = l_Lean_Json_mkObj(x_35);
return x_36;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonSamplesTable_fromJson_spec__0_spec__0_spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_7 = l_Float_fromJson_x3f(x_6);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonSamplesTable_fromJson_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonSamplesTable_fromJson_spec__0_spec__0_spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonSamplesTable_fromJson_spec__0_spec__0(lean_object* x_1) {
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
x_5 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonSamplesTable_fromJson_spec__0_spec__0_spec__1(x_3, x_4, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__2_spec__2___closed__0));
x_7 = lean_unsigned_to_nat(80u);
x_8 = l_Lean_Json_pretty(x_1, x_7);
x_9 = lean_string_append(x_6, x_8);
lean_dec_ref(x_8);
x_10 = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__2_spec__2___closed__1));
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonSamplesTable_fromJson_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonSamplesTable_fromJson_spec__0_spec__0(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonSamplesTable_fromJson_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonSamplesTable_fromJson_spec__0(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonSamplesTable_fromJson_spec__1_spec__2_spec__4(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_7 = l_Float_fromJson_x3f(x_6);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonSamplesTable_fromJson_spec__1_spec__2_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonSamplesTable_fromJson_spec__1_spec__2_spec__4(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonSamplesTable_fromJson_spec__1_spec__2(lean_object* x_1) {
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
x_5 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonSamplesTable_fromJson_spec__1_spec__2_spec__4(x_3, x_4, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__2_spec__2___closed__0));
x_7 = lean_unsigned_to_nat(80u);
x_8 = l_Lean_Json_pretty(x_1, x_7);
x_9 = lean_string_append(x_6, x_8);
lean_dec_ref(x_8);
x_10 = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__2_spec__2___closed__1));
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonSamplesTable_fromJson_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonSamplesTable_fromJson_spec__1_spec__2(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonSamplesTable_fromJson_spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonSamplesTable_fromJson_spec__1(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__3(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__2));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__6));
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__3, &l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__3_once, _init_l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__3);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__6(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__5));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__6, &l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__6_once, _init_l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__6);
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__4, &l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__4_once, _init_l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__4);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__8(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__7, &l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__7_once, _init_l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__7);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__9(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__6, &l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__6_once, _init_l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__6);
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__4, &l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__4_once, _init_l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__4);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__10(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__9, &l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__9_once, _init_l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__9);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__13(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__12));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__14(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__13, &l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__13_once, _init_l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__13);
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__4, &l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__4_once, _init_l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__4);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__15(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__14, &l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__14_once, _init_l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__14);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__18(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__17));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__19(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__18, &l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__18_once, _init_l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__18);
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__4, &l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__4_once, _init_l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__4);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__20(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__19, &l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__19_once, _init_l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__19);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__21(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__16, &l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__16_once, _init_l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__16);
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__4, &l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__4_once, _init_l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__4);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__22(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__21, &l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__21_once, _init_l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__21);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__23(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__26, &l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__26_once, _init_l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__26);
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__4, &l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__4_once, _init_l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__4);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__24(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__23, &l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__23_once, _init_l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__23);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Firefox_instFromJsonSamplesTable_fromJson(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = ((lean_object*)(l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__0));
lean_inc(x_1);
x_3 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonStackTable_fromJson_spec__0(x_1, x_2);
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
x_7 = lean_obj_once(&l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__8, &l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__8_once, _init_l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__8);
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
x_23 = ((lean_object*)(l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__0));
lean_inc(x_1);
x_24 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonSamplesTable_fromJson_spec__0(x_1, x_23);
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
x_28 = lean_obj_once(&l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__10, &l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__10_once, _init_l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__10);
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
x_44 = ((lean_object*)(l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__11));
lean_inc(x_1);
x_45 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonSamplesTable_fromJson_spec__0(x_1, x_44);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_55; 
lean_dec(x_43);
lean_dec(x_22);
lean_dec(x_1);
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
x_49 = lean_obj_once(&l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__15, &l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__15_once, _init_l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__15);
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
lean_dec(x_1);
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
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_45, 0);
lean_inc(x_64);
lean_dec_ref(x_45);
x_65 = ((lean_object*)(l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__16));
lean_inc(x_1);
x_66 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__1(x_1, x_65);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; uint8_t x_76; 
lean_dec(x_64);
lean_dec(x_43);
lean_dec(x_22);
lean_dec(x_1);
x_67 = lean_ctor_get(x_66, 0);
x_76 = !lean_is_exclusive(x_66);
if (x_76 == 0)
{
x_68 = x_66;
x_69 = x_76;
goto block_75;
}
else
{
lean_inc(x_67);
lean_dec(x_66);
x_68 = lean_box(0);
x_69 = x_76;
goto block_75;
}
block_75:
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_obj_once(&l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__20, &l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__20_once, _init_l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__20);
x_71 = lean_string_append(x_70, x_67);
lean_dec(x_67);
if (x_69 == 0)
{
lean_ctor_set(x_68, 0, x_71);
x_72 = x_68;
goto block_73;
}
else
{
lean_object* x_74; 
x_74 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_74, 0, x_71);
x_72 = x_74;
goto block_73;
}
block_73:
{
return x_72;
}
}
}
else
{
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_77; lean_object* x_78; uint8_t x_79; uint8_t x_84; 
lean_dec(x_64);
lean_dec(x_43);
lean_dec(x_22);
lean_dec(x_1);
x_77 = lean_ctor_get(x_66, 0);
x_84 = !lean_is_exclusive(x_66);
if (x_84 == 0)
{
x_78 = x_66;
x_79 = x_84;
goto block_83;
}
else
{
lean_inc(x_77);
lean_dec(x_66);
x_78 = lean_box(0);
x_79 = x_84;
goto block_83;
}
block_83:
{
lean_object* x_80; 
if (x_79 == 0)
{
lean_ctor_set_tag(x_78, 0);
x_80 = x_78;
goto block_81;
}
else
{
lean_object* x_82; 
x_82 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_82, 0, x_77);
x_80 = x_82;
goto block_81;
}
block_81:
{
return x_80;
}
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_66, 0);
lean_inc(x_85);
lean_dec_ref(x_66);
x_86 = ((lean_object*)(l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__14));
lean_inc(x_1);
x_87 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonSamplesTable_fromJson_spec__1(x_1, x_86);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; uint8_t x_90; uint8_t x_97; 
lean_dec(x_85);
lean_dec(x_64);
lean_dec(x_43);
lean_dec(x_22);
lean_dec(x_1);
x_88 = lean_ctor_get(x_87, 0);
x_97 = !lean_is_exclusive(x_87);
if (x_97 == 0)
{
x_89 = x_87;
x_90 = x_97;
goto block_96;
}
else
{
lean_inc(x_88);
lean_dec(x_87);
x_89 = lean_box(0);
x_90 = x_97;
goto block_96;
}
block_96:
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_obj_once(&l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__22, &l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__22_once, _init_l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__22);
x_92 = lean_string_append(x_91, x_88);
lean_dec(x_88);
if (x_90 == 0)
{
lean_ctor_set(x_89, 0, x_92);
x_93 = x_89;
goto block_94;
}
else
{
lean_object* x_95; 
x_95 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_95, 0, x_92);
x_93 = x_95;
goto block_94;
}
block_94:
{
return x_93;
}
}
}
else
{
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_98; lean_object* x_99; uint8_t x_100; uint8_t x_105; 
lean_dec(x_85);
lean_dec(x_64);
lean_dec(x_43);
lean_dec(x_22);
lean_dec(x_1);
x_98 = lean_ctor_get(x_87, 0);
x_105 = !lean_is_exclusive(x_87);
if (x_105 == 0)
{
x_99 = x_87;
x_100 = x_105;
goto block_104;
}
else
{
lean_inc(x_98);
lean_dec(x_87);
x_99 = lean_box(0);
x_100 = x_105;
goto block_104;
}
block_104:
{
lean_object* x_101; 
if (x_100 == 0)
{
lean_ctor_set_tag(x_99, 0);
x_101 = x_99;
goto block_102;
}
else
{
lean_object* x_103; 
x_103 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_103, 0, x_98);
x_101 = x_103;
goto block_102;
}
block_102:
{
return x_101;
}
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_87, 0);
lean_inc(x_106);
lean_dec_ref(x_87);
x_107 = ((lean_object*)(l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__24));
x_108 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__2(x_1, x_107);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; uint8_t x_111; uint8_t x_118; 
lean_dec(x_106);
lean_dec(x_85);
lean_dec(x_64);
lean_dec(x_43);
lean_dec(x_22);
x_109 = lean_ctor_get(x_108, 0);
x_118 = !lean_is_exclusive(x_108);
if (x_118 == 0)
{
x_110 = x_108;
x_111 = x_118;
goto block_117;
}
else
{
lean_inc(x_109);
lean_dec(x_108);
x_110 = lean_box(0);
x_111 = x_118;
goto block_117;
}
block_117:
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_obj_once(&l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__24, &l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__24_once, _init_l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__24);
x_113 = lean_string_append(x_112, x_109);
lean_dec(x_109);
if (x_111 == 0)
{
lean_ctor_set(x_110, 0, x_113);
x_114 = x_110;
goto block_115;
}
else
{
lean_object* x_116; 
x_116 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_116, 0, x_113);
x_114 = x_116;
goto block_115;
}
block_115:
{
return x_114;
}
}
}
else
{
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_119; lean_object* x_120; uint8_t x_121; uint8_t x_126; 
lean_dec(x_106);
lean_dec(x_85);
lean_dec(x_64);
lean_dec(x_43);
lean_dec(x_22);
x_119 = lean_ctor_get(x_108, 0);
x_126 = !lean_is_exclusive(x_108);
if (x_126 == 0)
{
x_120 = x_108;
x_121 = x_126;
goto block_125;
}
else
{
lean_inc(x_119);
lean_dec(x_108);
x_120 = lean_box(0);
x_121 = x_126;
goto block_125;
}
block_125:
{
lean_object* x_122; 
if (x_121 == 0)
{
lean_ctor_set_tag(x_120, 0);
x_122 = x_120;
goto block_123;
}
else
{
lean_object* x_124; 
x_124 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_124, 0, x_119);
x_122 = x_124;
goto block_123;
}
block_123:
{
return x_122;
}
}
}
else
{
lean_object* x_127; lean_object* x_128; uint8_t x_129; uint8_t x_135; 
x_127 = lean_ctor_get(x_108, 0);
x_135 = !lean_is_exclusive(x_108);
if (x_135 == 0)
{
x_128 = x_108;
x_129 = x_135;
goto block_134;
}
else
{
lean_inc(x_127);
lean_dec(x_108);
x_128 = lean_box(0);
x_129 = x_135;
goto block_134;
}
block_134:
{
lean_object* x_130; lean_object* x_131; 
x_130 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_130, 0, x_22);
lean_ctor_set(x_130, 1, x_43);
lean_ctor_set(x_130, 2, x_64);
lean_ctor_set(x_130, 3, x_85);
lean_ctor_set(x_130, 4, x_106);
lean_ctor_set(x_130, 5, x_127);
if (x_129 == 0)
{
lean_ctor_set(x_128, 0, x_130);
x_131 = x_128;
goto block_132;
}
else
{
lean_object* x_133; 
x_133 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_133, 0, x_130);
x_131 = x_133;
goto block_132;
}
block_132:
{
return x_131;
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
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Firefox_instToJsonSamplesTable_toJson_spec__1_spec__2(size_t x_1, size_t x_2, lean_object* x_3) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; double x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = lean_unbox_float(x_5);
lean_dec(x_5);
x_9 = l_Float_toJson(x_8);
x_10 = 1;
x_11 = lean_usize_add(x_2, x_10);
x_12 = lean_array_uset(x_7, x_2, x_9);
x_2 = x_11;
x_3 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Firefox_instToJsonSamplesTable_toJson_spec__1_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Firefox_instToJsonSamplesTable_toJson_spec__1_spec__2(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Firefox_instToJsonSamplesTable_toJson_spec__1(lean_object* x_1) {
_start:
{
size_t x_2; size_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_array_size(x_1);
x_3 = 0;
x_4 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Firefox_instToJsonSamplesTable_toJson_spec__1_spec__2(x_2, x_3, x_1);
x_5 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Firefox_instToJsonSamplesTable_toJson_spec__0_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; double x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = lean_unbox_float(x_5);
lean_dec(x_5);
x_9 = l_Float_toJson(x_8);
x_10 = 1;
x_11 = lean_usize_add(x_2, x_10);
x_12 = lean_array_uset(x_7, x_2, x_9);
x_2 = x_11;
x_3 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Firefox_instToJsonSamplesTable_toJson_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Firefox_instToJsonSamplesTable_toJson_spec__0_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Firefox_instToJsonSamplesTable_toJson_spec__0(lean_object* x_1) {
_start:
{
size_t x_2; size_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_array_size(x_1);
x_3 = 0;
x_4 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Firefox_instToJsonSamplesTable_toJson_spec__0_spec__0(x_2, x_3, x_1);
x_5 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Firefox_instToJsonSamplesTable_toJson(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_1, 4);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_1, 5);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = ((lean_object*)(l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__0));
x_9 = l_Array_toJson___at___00Lean_Firefox_instToJsonStackTable_toJson_spec__0(x_2);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = ((lean_object*)(l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__0));
x_14 = l_Array_toJson___at___00Lean_Firefox_instToJsonSamplesTable_toJson_spec__0(x_3);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_11);
x_17 = ((lean_object*)(l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__11));
x_18 = l_Array_toJson___at___00Lean_Firefox_instToJsonSamplesTable_toJson_spec__0(x_4);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_11);
x_21 = ((lean_object*)(l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__16));
x_22 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_22, 0, x_5);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_11);
x_25 = ((lean_object*)(l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__14));
x_26 = l_Array_toJson___at___00Lean_Firefox_instToJsonSamplesTable_toJson_spec__1(x_6);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_11);
x_29 = ((lean_object*)(l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__24));
x_30 = l_Lean_JsonNumber_fromNat(x_7);
x_31 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_11);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_11);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_28);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_24);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_20);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_16);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_12);
lean_ctor_set(x_39, 1, x_38);
x_40 = ((lean_object*)(l_Lean_Firefox_instToJsonCategory_toJson___closed__0));
x_41 = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Firefox_instToJsonCategory_toJson_spec__1(x_39, x_40);
x_42 = l_Lean_Json_mkObj(x_41);
return x_42;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonFuncTable_fromJson_spec__0_spec__0_spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_7 = l_Lean_Json_getInt_x3f(x_6);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonFuncTable_fromJson_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonFuncTable_fromJson_spec__0_spec__0_spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonFuncTable_fromJson_spec__0_spec__0(lean_object* x_1) {
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
x_5 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonFuncTable_fromJson_spec__0_spec__0_spec__1(x_3, x_4, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__2_spec__2___closed__0));
x_7 = lean_unsigned_to_nat(80u);
x_8 = l_Lean_Json_pretty(x_1, x_7);
x_9 = lean_string_append(x_6, x_8);
lean_dec_ref(x_8);
x_10 = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__2_spec__2___closed__1));
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonFuncTable_fromJson_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonFuncTable_fromJson_spec__0_spec__0(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonFuncTable_fromJson_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonFuncTable_fromJson_spec__0(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__2(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__1));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__6));
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__2, &l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__2_once, _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__2);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Firefox_instFromJsonCategory_fromJson___closed__9, &l_Lean_Firefox_instFromJsonCategory_fromJson___closed__9_once, _init_l_Lean_Firefox_instFromJsonCategory_fromJson___closed__9);
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__3, &l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__3_once, _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__3);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__4, &l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__4_once, _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__4);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__8(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__7));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__9(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__8, &l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__8_once, _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__8);
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__3, &l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__3_once, _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__3);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__10(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__9, &l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__9_once, _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__9);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__13(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__12));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__14(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__13, &l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__13_once, _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__13);
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__3, &l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__3_once, _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__3);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__15(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__14, &l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__14_once, _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__14);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__18(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__17));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__19(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__18, &l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__18_once, _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__18);
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__3, &l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__3_once, _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__3);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__20(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__19, &l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__19_once, _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__19);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__23(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__22));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__24(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__23, &l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__23_once, _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__23);
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__3, &l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__3_once, _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__3);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__25(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__24, &l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__24_once, _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__24);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__28(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__27));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__29(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__28, &l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__28_once, _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__28);
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__3, &l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__3_once, _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__3);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__30(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__29, &l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__29_once, _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__29);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__33(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__32));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__34(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__33, &l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__33_once, _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__33);
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__3, &l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__3_once, _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__3);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__35(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__34, &l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__34_once, _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__34);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__36(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__26, &l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__26_once, _init_l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__26);
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__3, &l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__3_once, _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__3);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__37(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__36, &l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__36_once, _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__36);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Firefox_instFromJsonFuncTable_fromJson(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__0));
lean_inc(x_1);
x_3 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonStackTable_fromJson_spec__0(x_1, x_2);
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
x_7 = lean_obj_once(&l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__5, &l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__5_once, _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__5);
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
x_23 = ((lean_object*)(l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__6));
lean_inc(x_1);
x_24 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__3(x_1, x_23);
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
x_28 = lean_obj_once(&l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__10, &l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__10_once, _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__10);
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
x_44 = ((lean_object*)(l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__11));
lean_inc(x_1);
x_45 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__3(x_1, x_44);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_55; 
lean_dec(x_43);
lean_dec(x_22);
lean_dec(x_1);
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
x_49 = lean_obj_once(&l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__15, &l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__15_once, _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__15);
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
lean_dec(x_1);
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
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_45, 0);
lean_inc(x_64);
lean_dec_ref(x_45);
x_65 = ((lean_object*)(l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__16));
lean_inc(x_1);
x_66 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonFuncTable_fromJson_spec__0(x_1, x_65);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; uint8_t x_76; 
lean_dec(x_64);
lean_dec(x_43);
lean_dec(x_22);
lean_dec(x_1);
x_67 = lean_ctor_get(x_66, 0);
x_76 = !lean_is_exclusive(x_66);
if (x_76 == 0)
{
x_68 = x_66;
x_69 = x_76;
goto block_75;
}
else
{
lean_inc(x_67);
lean_dec(x_66);
x_68 = lean_box(0);
x_69 = x_76;
goto block_75;
}
block_75:
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_obj_once(&l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__20, &l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__20_once, _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__20);
x_71 = lean_string_append(x_70, x_67);
lean_dec(x_67);
if (x_69 == 0)
{
lean_ctor_set(x_68, 0, x_71);
x_72 = x_68;
goto block_73;
}
else
{
lean_object* x_74; 
x_74 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_74, 0, x_71);
x_72 = x_74;
goto block_73;
}
block_73:
{
return x_72;
}
}
}
else
{
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_77; lean_object* x_78; uint8_t x_79; uint8_t x_84; 
lean_dec(x_64);
lean_dec(x_43);
lean_dec(x_22);
lean_dec(x_1);
x_77 = lean_ctor_get(x_66, 0);
x_84 = !lean_is_exclusive(x_66);
if (x_84 == 0)
{
x_78 = x_66;
x_79 = x_84;
goto block_83;
}
else
{
lean_inc(x_77);
lean_dec(x_66);
x_78 = lean_box(0);
x_79 = x_84;
goto block_83;
}
block_83:
{
lean_object* x_80; 
if (x_79 == 0)
{
lean_ctor_set_tag(x_78, 0);
x_80 = x_78;
goto block_81;
}
else
{
lean_object* x_82; 
x_82 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_82, 0, x_77);
x_80 = x_82;
goto block_81;
}
block_81:
{
return x_80;
}
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_66, 0);
lean_inc(x_85);
lean_dec_ref(x_66);
x_86 = ((lean_object*)(l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__21));
lean_inc(x_1);
x_87 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonStackTable_fromJson_spec__1(x_1, x_86);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; uint8_t x_90; uint8_t x_97; 
lean_dec(x_85);
lean_dec(x_64);
lean_dec(x_43);
lean_dec(x_22);
lean_dec(x_1);
x_88 = lean_ctor_get(x_87, 0);
x_97 = !lean_is_exclusive(x_87);
if (x_97 == 0)
{
x_89 = x_87;
x_90 = x_97;
goto block_96;
}
else
{
lean_inc(x_88);
lean_dec(x_87);
x_89 = lean_box(0);
x_90 = x_97;
goto block_96;
}
block_96:
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_obj_once(&l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__25, &l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__25_once, _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__25);
x_92 = lean_string_append(x_91, x_88);
lean_dec(x_88);
if (x_90 == 0)
{
lean_ctor_set(x_89, 0, x_92);
x_93 = x_89;
goto block_94;
}
else
{
lean_object* x_95; 
x_95 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_95, 0, x_92);
x_93 = x_95;
goto block_94;
}
block_94:
{
return x_93;
}
}
}
else
{
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_98; lean_object* x_99; uint8_t x_100; uint8_t x_105; 
lean_dec(x_85);
lean_dec(x_64);
lean_dec(x_43);
lean_dec(x_22);
lean_dec(x_1);
x_98 = lean_ctor_get(x_87, 0);
x_105 = !lean_is_exclusive(x_87);
if (x_105 == 0)
{
x_99 = x_87;
x_100 = x_105;
goto block_104;
}
else
{
lean_inc(x_98);
lean_dec(x_87);
x_99 = lean_box(0);
x_100 = x_105;
goto block_104;
}
block_104:
{
lean_object* x_101; 
if (x_100 == 0)
{
lean_ctor_set_tag(x_99, 0);
x_101 = x_99;
goto block_102;
}
else
{
lean_object* x_103; 
x_103 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_103, 0, x_98);
x_101 = x_103;
goto block_102;
}
block_102:
{
return x_101;
}
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_87, 0);
lean_inc(x_106);
lean_dec_ref(x_87);
x_107 = ((lean_object*)(l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__26));
lean_inc(x_1);
x_108 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonStackTable_fromJson_spec__1(x_1, x_107);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; uint8_t x_111; uint8_t x_118; 
lean_dec(x_106);
lean_dec(x_85);
lean_dec(x_64);
lean_dec(x_43);
lean_dec(x_22);
lean_dec(x_1);
x_109 = lean_ctor_get(x_108, 0);
x_118 = !lean_is_exclusive(x_108);
if (x_118 == 0)
{
x_110 = x_108;
x_111 = x_118;
goto block_117;
}
else
{
lean_inc(x_109);
lean_dec(x_108);
x_110 = lean_box(0);
x_111 = x_118;
goto block_117;
}
block_117:
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_obj_once(&l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__30, &l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__30_once, _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__30);
x_113 = lean_string_append(x_112, x_109);
lean_dec(x_109);
if (x_111 == 0)
{
lean_ctor_set(x_110, 0, x_113);
x_114 = x_110;
goto block_115;
}
else
{
lean_object* x_116; 
x_116 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_116, 0, x_113);
x_114 = x_116;
goto block_115;
}
block_115:
{
return x_114;
}
}
}
else
{
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_119; lean_object* x_120; uint8_t x_121; uint8_t x_126; 
lean_dec(x_106);
lean_dec(x_85);
lean_dec(x_64);
lean_dec(x_43);
lean_dec(x_22);
lean_dec(x_1);
x_119 = lean_ctor_get(x_108, 0);
x_126 = !lean_is_exclusive(x_108);
if (x_126 == 0)
{
x_120 = x_108;
x_121 = x_126;
goto block_125;
}
else
{
lean_inc(x_119);
lean_dec(x_108);
x_120 = lean_box(0);
x_121 = x_126;
goto block_125;
}
block_125:
{
lean_object* x_122; 
if (x_121 == 0)
{
lean_ctor_set_tag(x_120, 0);
x_122 = x_120;
goto block_123;
}
else
{
lean_object* x_124; 
x_124 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_124, 0, x_119);
x_122 = x_124;
goto block_123;
}
block_123:
{
return x_122;
}
}
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_108, 0);
lean_inc(x_127);
lean_dec_ref(x_108);
x_128 = ((lean_object*)(l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__31));
lean_inc(x_1);
x_129 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonStackTable_fromJson_spec__1(x_1, x_128);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; uint8_t x_132; uint8_t x_139; 
lean_dec(x_127);
lean_dec(x_106);
lean_dec(x_85);
lean_dec(x_64);
lean_dec(x_43);
lean_dec(x_22);
lean_dec(x_1);
x_130 = lean_ctor_get(x_129, 0);
x_139 = !lean_is_exclusive(x_129);
if (x_139 == 0)
{
x_131 = x_129;
x_132 = x_139;
goto block_138;
}
else
{
lean_inc(x_130);
lean_dec(x_129);
x_131 = lean_box(0);
x_132 = x_139;
goto block_138;
}
block_138:
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_obj_once(&l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__35, &l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__35_once, _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__35);
x_134 = lean_string_append(x_133, x_130);
lean_dec(x_130);
if (x_132 == 0)
{
lean_ctor_set(x_131, 0, x_134);
x_135 = x_131;
goto block_136;
}
else
{
lean_object* x_137; 
x_137 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_137, 0, x_134);
x_135 = x_137;
goto block_136;
}
block_136:
{
return x_135;
}
}
}
else
{
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_140; lean_object* x_141; uint8_t x_142; uint8_t x_147; 
lean_dec(x_127);
lean_dec(x_106);
lean_dec(x_85);
lean_dec(x_64);
lean_dec(x_43);
lean_dec(x_22);
lean_dec(x_1);
x_140 = lean_ctor_get(x_129, 0);
x_147 = !lean_is_exclusive(x_129);
if (x_147 == 0)
{
x_141 = x_129;
x_142 = x_147;
goto block_146;
}
else
{
lean_inc(x_140);
lean_dec(x_129);
x_141 = lean_box(0);
x_142 = x_147;
goto block_146;
}
block_146:
{
lean_object* x_143; 
if (x_142 == 0)
{
lean_ctor_set_tag(x_141, 0);
x_143 = x_141;
goto block_144;
}
else
{
lean_object* x_145; 
x_145 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_145, 0, x_140);
x_143 = x_145;
goto block_144;
}
block_144:
{
return x_143;
}
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_148 = lean_ctor_get(x_129, 0);
lean_inc(x_148);
lean_dec_ref(x_129);
x_149 = ((lean_object*)(l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__24));
x_150 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__2(x_1, x_149);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; lean_object* x_152; uint8_t x_153; uint8_t x_160; 
lean_dec(x_148);
lean_dec(x_127);
lean_dec(x_106);
lean_dec(x_85);
lean_dec(x_64);
lean_dec(x_43);
lean_dec(x_22);
x_151 = lean_ctor_get(x_150, 0);
x_160 = !lean_is_exclusive(x_150);
if (x_160 == 0)
{
x_152 = x_150;
x_153 = x_160;
goto block_159;
}
else
{
lean_inc(x_151);
lean_dec(x_150);
x_152 = lean_box(0);
x_153 = x_160;
goto block_159;
}
block_159:
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_154 = lean_obj_once(&l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__37, &l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__37_once, _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__37);
x_155 = lean_string_append(x_154, x_151);
lean_dec(x_151);
if (x_153 == 0)
{
lean_ctor_set(x_152, 0, x_155);
x_156 = x_152;
goto block_157;
}
else
{
lean_object* x_158; 
x_158 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_158, 0, x_155);
x_156 = x_158;
goto block_157;
}
block_157:
{
return x_156;
}
}
}
else
{
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_161; lean_object* x_162; uint8_t x_163; uint8_t x_168; 
lean_dec(x_148);
lean_dec(x_127);
lean_dec(x_106);
lean_dec(x_85);
lean_dec(x_64);
lean_dec(x_43);
lean_dec(x_22);
x_161 = lean_ctor_get(x_150, 0);
x_168 = !lean_is_exclusive(x_150);
if (x_168 == 0)
{
x_162 = x_150;
x_163 = x_168;
goto block_167;
}
else
{
lean_inc(x_161);
lean_dec(x_150);
x_162 = lean_box(0);
x_163 = x_168;
goto block_167;
}
block_167:
{
lean_object* x_164; 
if (x_163 == 0)
{
lean_ctor_set_tag(x_162, 0);
x_164 = x_162;
goto block_165;
}
else
{
lean_object* x_166; 
x_166 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_166, 0, x_161);
x_164 = x_166;
goto block_165;
}
block_165:
{
return x_164;
}
}
}
else
{
lean_object* x_169; lean_object* x_170; uint8_t x_171; uint8_t x_177; 
x_169 = lean_ctor_get(x_150, 0);
x_177 = !lean_is_exclusive(x_150);
if (x_177 == 0)
{
x_170 = x_150;
x_171 = x_177;
goto block_176;
}
else
{
lean_inc(x_169);
lean_dec(x_150);
x_170 = lean_box(0);
x_171 = x_177;
goto block_176;
}
block_176:
{
lean_object* x_172; lean_object* x_173; 
x_172 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_172, 0, x_22);
lean_ctor_set(x_172, 1, x_43);
lean_ctor_set(x_172, 2, x_64);
lean_ctor_set(x_172, 3, x_85);
lean_ctor_set(x_172, 4, x_106);
lean_ctor_set(x_172, 5, x_127);
lean_ctor_set(x_172, 6, x_148);
lean_ctor_set(x_172, 7, x_169);
if (x_171 == 0)
{
lean_ctor_set(x_170, 0, x_172);
x_173 = x_170;
goto block_174;
}
else
{
lean_object* x_175; 
x_175 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_175, 0, x_172);
x_173 = x_175;
goto block_174;
}
block_174:
{
return x_173;
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
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Firefox_instToJsonFuncTable_toJson_spec__0_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l_Lean_JsonNumber_fromInt(x_5);
x_9 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = 1;
x_11 = lean_usize_add(x_2, x_10);
x_12 = lean_array_uset(x_7, x_2, x_9);
x_2 = x_11;
x_3 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Firefox_instToJsonFuncTable_toJson_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Firefox_instToJsonFuncTable_toJson_spec__0_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Firefox_instToJsonFuncTable_toJson_spec__0(lean_object* x_1) {
_start:
{
size_t x_2; size_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_array_size(x_1);
x_3 = 0;
x_4 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Firefox_instToJsonFuncTable_toJson_spec__0_spec__0(x_2, x_3, x_1);
x_5 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Firefox_instToJsonFuncTable_toJson(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_1, 4);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_1, 5);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_1, 6);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_1, 7);
lean_inc(x_9);
lean_dec_ref(x_1);
x_10 = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__0));
x_11 = l_Array_toJson___at___00Lean_Firefox_instToJsonStackTable_toJson_spec__0(x_2);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = ((lean_object*)(l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__6));
x_16 = l_Array_toJson___at___00Lean_Firefox_instToJsonProfileMeta_toJson_spec__1(x_3);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_13);
x_19 = ((lean_object*)(l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__11));
x_20 = l_Array_toJson___at___00Lean_Firefox_instToJsonProfileMeta_toJson_spec__1(x_4);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_13);
x_23 = ((lean_object*)(l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__16));
x_24 = l_Array_toJson___at___00Lean_Firefox_instToJsonFuncTable_toJson_spec__0(x_5);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_13);
x_27 = ((lean_object*)(l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__21));
x_28 = l_Array_toJson___at___00Lean_Firefox_instToJsonStackTable_toJson_spec__1(x_6);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_13);
x_31 = ((lean_object*)(l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__26));
x_32 = l_Array_toJson___at___00Lean_Firefox_instToJsonStackTable_toJson_spec__1(x_7);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_13);
x_35 = ((lean_object*)(l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__31));
x_36 = l_Array_toJson___at___00Lean_Firefox_instToJsonStackTable_toJson_spec__1(x_8);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_13);
x_39 = ((lean_object*)(l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__24));
x_40 = l_Lean_JsonNumber_fromNat(x_9);
x_41 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_13);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_13);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_38);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_34);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_30);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_26);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_22);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_18);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_14);
lean_ctor_set(x_51, 1, x_50);
x_52 = ((lean_object*)(l_Lean_Firefox_instToJsonCategory_toJson___closed__0));
x_53 = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Firefox_instToJsonCategory_toJson_spec__1(x_51, x_52);
x_54 = l_Lean_Json_mkObj(x_53);
return x_54;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonFrameTable_fromJson_spec__0_spec__0_spec__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_Option_fromJson_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonFrameTable_fromJson_spec__0_spec__0_spec__1___closed__0));
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_1);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonFrameTable_fromJson_spec__0_spec__0_spec__2(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_7 = l_Option_fromJson_x3f___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonFrameTable_fromJson_spec__0_spec__0_spec__1(x_6);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonFrameTable_fromJson_spec__0_spec__0_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonFrameTable_fromJson_spec__0_spec__0_spec__2(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonFrameTable_fromJson_spec__0_spec__0(lean_object* x_1) {
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
x_5 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonFrameTable_fromJson_spec__0_spec__0_spec__2(x_3, x_4, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__2_spec__2___closed__0));
x_7 = lean_unsigned_to_nat(80u);
x_8 = l_Lean_Json_pretty(x_1, x_7);
x_9 = lean_string_append(x_6, x_8);
lean_dec_ref(x_8);
x_10 = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__2_spec__2___closed__1));
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonFrameTable_fromJson_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonFrameTable_fromJson_spec__0_spec__0(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonFrameTable_fromJson_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonFrameTable_fromJson_spec__0(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__3(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__2));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__6));
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__3, &l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__3_once, _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__3);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__6(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__5));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__6, &l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__6_once, _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__6);
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__4, &l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__4_once, _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__4);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__8(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__7, &l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__7_once, _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__7);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__11(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__10));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__12(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__11, &l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__11_once, _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__11);
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__4, &l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__4_once, _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__4);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__13(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__12, &l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__12_once, _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__12);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__14(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__11, &l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__11_once, _init_l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__11);
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__4, &l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__4_once, _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__4);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__15(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__14, &l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__14_once, _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__14);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__16(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__16, &l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__16_once, _init_l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__16);
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__4, &l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__4_once, _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__4);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__17(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__16, &l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__16_once, _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__16);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__20(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__19));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__21(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__20, &l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__20_once, _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__20);
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__4, &l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__4_once, _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__4);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__22(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__21, &l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__21_once, _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__21);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__25(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__24));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__26(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__25, &l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__25_once, _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__25);
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__4, &l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__4_once, _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__4);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__27(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__26, &l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__26_once, _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__26);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__30(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__29));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__31(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__30, &l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__30_once, _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__30);
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__4, &l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__4_once, _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__4);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__32(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__31, &l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__31_once, _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__31);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__35(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__34));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__36(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__35, &l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__35_once, _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__35);
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__4, &l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__4_once, _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__4);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__37(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__36, &l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__36_once, _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__36);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__40(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__39));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__41(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__40, &l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__40_once, _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__40);
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__4, &l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__4_once, _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__4);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__42(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__41, &l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__41_once, _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__41);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__45(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__44));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__46(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__45, &l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__45_once, _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__45);
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__4, &l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__4_once, _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__4);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__47(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__46, &l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__46_once, _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__46);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__48(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__26, &l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__26_once, _init_l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__26);
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__4, &l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__4_once, _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__4);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__49(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__48, &l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__48_once, _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__48);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Firefox_instFromJsonFrameTable_fromJson(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = ((lean_object*)(l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__0));
lean_inc(x_1);
x_3 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonFuncTable_fromJson_spec__0(x_1, x_2);
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
x_7 = lean_obj_once(&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__8, &l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__8_once, _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__8);
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
x_23 = ((lean_object*)(l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__9));
lean_inc(x_1);
x_24 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonStackTable_fromJson_spec__0(x_1, x_23);
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
x_28 = lean_obj_once(&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__13, &l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__13_once, _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__13);
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
x_44 = ((lean_object*)(l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__9));
lean_inc(x_1);
x_45 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonStackTable_fromJson_spec__1(x_1, x_44);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_55; 
lean_dec(x_43);
lean_dec(x_22);
lean_dec(x_1);
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
x_49 = lean_obj_once(&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__15, &l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__15_once, _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__15);
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
lean_dec(x_1);
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
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_45, 0);
lean_inc(x_64);
lean_dec_ref(x_45);
x_65 = ((lean_object*)(l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__14));
lean_inc(x_1);
x_66 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonStackTable_fromJson_spec__1(x_1, x_65);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; uint8_t x_76; 
lean_dec(x_64);
lean_dec(x_43);
lean_dec(x_22);
lean_dec(x_1);
x_67 = lean_ctor_get(x_66, 0);
x_76 = !lean_is_exclusive(x_66);
if (x_76 == 0)
{
x_68 = x_66;
x_69 = x_76;
goto block_75;
}
else
{
lean_inc(x_67);
lean_dec(x_66);
x_68 = lean_box(0);
x_69 = x_76;
goto block_75;
}
block_75:
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_obj_once(&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__17, &l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__17_once, _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__17);
x_71 = lean_string_append(x_70, x_67);
lean_dec(x_67);
if (x_69 == 0)
{
lean_ctor_set(x_68, 0, x_71);
x_72 = x_68;
goto block_73;
}
else
{
lean_object* x_74; 
x_74 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_74, 0, x_71);
x_72 = x_74;
goto block_73;
}
block_73:
{
return x_72;
}
}
}
else
{
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_77; lean_object* x_78; uint8_t x_79; uint8_t x_84; 
lean_dec(x_64);
lean_dec(x_43);
lean_dec(x_22);
lean_dec(x_1);
x_77 = lean_ctor_get(x_66, 0);
x_84 = !lean_is_exclusive(x_66);
if (x_84 == 0)
{
x_78 = x_66;
x_79 = x_84;
goto block_83;
}
else
{
lean_inc(x_77);
lean_dec(x_66);
x_78 = lean_box(0);
x_79 = x_84;
goto block_83;
}
block_83:
{
lean_object* x_80; 
if (x_79 == 0)
{
lean_ctor_set_tag(x_78, 0);
x_80 = x_78;
goto block_81;
}
else
{
lean_object* x_82; 
x_82 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_82, 0, x_77);
x_80 = x_82;
goto block_81;
}
block_81:
{
return x_80;
}
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_66, 0);
lean_inc(x_85);
lean_dec_ref(x_66);
x_86 = ((lean_object*)(l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__18));
lean_inc(x_1);
x_87 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonStackTable_fromJson_spec__0(x_1, x_86);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; uint8_t x_90; uint8_t x_97; 
lean_dec(x_85);
lean_dec(x_64);
lean_dec(x_43);
lean_dec(x_22);
lean_dec(x_1);
x_88 = lean_ctor_get(x_87, 0);
x_97 = !lean_is_exclusive(x_87);
if (x_97 == 0)
{
x_89 = x_87;
x_90 = x_97;
goto block_96;
}
else
{
lean_inc(x_88);
lean_dec(x_87);
x_89 = lean_box(0);
x_90 = x_97;
goto block_96;
}
block_96:
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_obj_once(&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__22, &l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__22_once, _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__22);
x_92 = lean_string_append(x_91, x_88);
lean_dec(x_88);
if (x_90 == 0)
{
lean_ctor_set(x_89, 0, x_92);
x_93 = x_89;
goto block_94;
}
else
{
lean_object* x_95; 
x_95 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_95, 0, x_92);
x_93 = x_95;
goto block_94;
}
block_94:
{
return x_93;
}
}
}
else
{
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_98; lean_object* x_99; uint8_t x_100; uint8_t x_105; 
lean_dec(x_85);
lean_dec(x_64);
lean_dec(x_43);
lean_dec(x_22);
lean_dec(x_1);
x_98 = lean_ctor_get(x_87, 0);
x_105 = !lean_is_exclusive(x_87);
if (x_105 == 0)
{
x_99 = x_87;
x_100 = x_105;
goto block_104;
}
else
{
lean_inc(x_98);
lean_dec(x_87);
x_99 = lean_box(0);
x_100 = x_105;
goto block_104;
}
block_104:
{
lean_object* x_101; 
if (x_100 == 0)
{
lean_ctor_set_tag(x_99, 0);
x_101 = x_99;
goto block_102;
}
else
{
lean_object* x_103; 
x_103 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_103, 0, x_98);
x_101 = x_103;
goto block_102;
}
block_102:
{
return x_101;
}
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_87, 0);
lean_inc(x_106);
lean_dec_ref(x_87);
x_107 = ((lean_object*)(l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__23));
lean_inc(x_1);
x_108 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonFrameTable_fromJson_spec__0(x_1, x_107);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; uint8_t x_111; uint8_t x_118; 
lean_dec(x_106);
lean_dec(x_85);
lean_dec(x_64);
lean_dec(x_43);
lean_dec(x_22);
lean_dec(x_1);
x_109 = lean_ctor_get(x_108, 0);
x_118 = !lean_is_exclusive(x_108);
if (x_118 == 0)
{
x_110 = x_108;
x_111 = x_118;
goto block_117;
}
else
{
lean_inc(x_109);
lean_dec(x_108);
x_110 = lean_box(0);
x_111 = x_118;
goto block_117;
}
block_117:
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_obj_once(&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__27, &l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__27_once, _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__27);
x_113 = lean_string_append(x_112, x_109);
lean_dec(x_109);
if (x_111 == 0)
{
lean_ctor_set(x_110, 0, x_113);
x_114 = x_110;
goto block_115;
}
else
{
lean_object* x_116; 
x_116 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_116, 0, x_113);
x_114 = x_116;
goto block_115;
}
block_115:
{
return x_114;
}
}
}
else
{
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_119; lean_object* x_120; uint8_t x_121; uint8_t x_126; 
lean_dec(x_106);
lean_dec(x_85);
lean_dec(x_64);
lean_dec(x_43);
lean_dec(x_22);
lean_dec(x_1);
x_119 = lean_ctor_get(x_108, 0);
x_126 = !lean_is_exclusive(x_108);
if (x_126 == 0)
{
x_120 = x_108;
x_121 = x_126;
goto block_125;
}
else
{
lean_inc(x_119);
lean_dec(x_108);
x_120 = lean_box(0);
x_121 = x_126;
goto block_125;
}
block_125:
{
lean_object* x_122; 
if (x_121 == 0)
{
lean_ctor_set_tag(x_120, 0);
x_122 = x_120;
goto block_123;
}
else
{
lean_object* x_124; 
x_124 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_124, 0, x_119);
x_122 = x_124;
goto block_123;
}
block_123:
{
return x_122;
}
}
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_108, 0);
lean_inc(x_127);
lean_dec_ref(x_108);
x_128 = ((lean_object*)(l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__28));
lean_inc(x_1);
x_129 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonFrameTable_fromJson_spec__0(x_1, x_128);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; uint8_t x_132; uint8_t x_139; 
lean_dec(x_127);
lean_dec(x_106);
lean_dec(x_85);
lean_dec(x_64);
lean_dec(x_43);
lean_dec(x_22);
lean_dec(x_1);
x_130 = lean_ctor_get(x_129, 0);
x_139 = !lean_is_exclusive(x_129);
if (x_139 == 0)
{
x_131 = x_129;
x_132 = x_139;
goto block_138;
}
else
{
lean_inc(x_130);
lean_dec(x_129);
x_131 = lean_box(0);
x_132 = x_139;
goto block_138;
}
block_138:
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_obj_once(&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__32, &l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__32_once, _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__32);
x_134 = lean_string_append(x_133, x_130);
lean_dec(x_130);
if (x_132 == 0)
{
lean_ctor_set(x_131, 0, x_134);
x_135 = x_131;
goto block_136;
}
else
{
lean_object* x_137; 
x_137 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_137, 0, x_134);
x_135 = x_137;
goto block_136;
}
block_136:
{
return x_135;
}
}
}
else
{
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_140; lean_object* x_141; uint8_t x_142; uint8_t x_147; 
lean_dec(x_127);
lean_dec(x_106);
lean_dec(x_85);
lean_dec(x_64);
lean_dec(x_43);
lean_dec(x_22);
lean_dec(x_1);
x_140 = lean_ctor_get(x_129, 0);
x_147 = !lean_is_exclusive(x_129);
if (x_147 == 0)
{
x_141 = x_129;
x_142 = x_147;
goto block_146;
}
else
{
lean_inc(x_140);
lean_dec(x_129);
x_141 = lean_box(0);
x_142 = x_147;
goto block_146;
}
block_146:
{
lean_object* x_143; 
if (x_142 == 0)
{
lean_ctor_set_tag(x_141, 0);
x_143 = x_141;
goto block_144;
}
else
{
lean_object* x_145; 
x_145 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_145, 0, x_140);
x_143 = x_145;
goto block_144;
}
block_144:
{
return x_143;
}
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_148 = lean_ctor_get(x_129, 0);
lean_inc(x_148);
lean_dec_ref(x_129);
x_149 = ((lean_object*)(l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__33));
lean_inc(x_1);
x_150 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonFrameTable_fromJson_spec__0(x_1, x_149);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; lean_object* x_152; uint8_t x_153; uint8_t x_160; 
lean_dec(x_148);
lean_dec(x_127);
lean_dec(x_106);
lean_dec(x_85);
lean_dec(x_64);
lean_dec(x_43);
lean_dec(x_22);
lean_dec(x_1);
x_151 = lean_ctor_get(x_150, 0);
x_160 = !lean_is_exclusive(x_150);
if (x_160 == 0)
{
x_152 = x_150;
x_153 = x_160;
goto block_159;
}
else
{
lean_inc(x_151);
lean_dec(x_150);
x_152 = lean_box(0);
x_153 = x_160;
goto block_159;
}
block_159:
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_154 = lean_obj_once(&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__37, &l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__37_once, _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__37);
x_155 = lean_string_append(x_154, x_151);
lean_dec(x_151);
if (x_153 == 0)
{
lean_ctor_set(x_152, 0, x_155);
x_156 = x_152;
goto block_157;
}
else
{
lean_object* x_158; 
x_158 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_158, 0, x_155);
x_156 = x_158;
goto block_157;
}
block_157:
{
return x_156;
}
}
}
else
{
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_161; lean_object* x_162; uint8_t x_163; uint8_t x_168; 
lean_dec(x_148);
lean_dec(x_127);
lean_dec(x_106);
lean_dec(x_85);
lean_dec(x_64);
lean_dec(x_43);
lean_dec(x_22);
lean_dec(x_1);
x_161 = lean_ctor_get(x_150, 0);
x_168 = !lean_is_exclusive(x_150);
if (x_168 == 0)
{
x_162 = x_150;
x_163 = x_168;
goto block_167;
}
else
{
lean_inc(x_161);
lean_dec(x_150);
x_162 = lean_box(0);
x_163 = x_168;
goto block_167;
}
block_167:
{
lean_object* x_164; 
if (x_163 == 0)
{
lean_ctor_set_tag(x_162, 0);
x_164 = x_162;
goto block_165;
}
else
{
lean_object* x_166; 
x_166 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_166, 0, x_161);
x_164 = x_166;
goto block_165;
}
block_165:
{
return x_164;
}
}
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_169 = lean_ctor_get(x_150, 0);
lean_inc(x_169);
lean_dec_ref(x_150);
x_170 = ((lean_object*)(l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__38));
lean_inc(x_1);
x_171 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonStackTable_fromJson_spec__1(x_1, x_170);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; lean_object* x_173; uint8_t x_174; uint8_t x_181; 
lean_dec(x_169);
lean_dec(x_148);
lean_dec(x_127);
lean_dec(x_106);
lean_dec(x_85);
lean_dec(x_64);
lean_dec(x_43);
lean_dec(x_22);
lean_dec(x_1);
x_172 = lean_ctor_get(x_171, 0);
x_181 = !lean_is_exclusive(x_171);
if (x_181 == 0)
{
x_173 = x_171;
x_174 = x_181;
goto block_180;
}
else
{
lean_inc(x_172);
lean_dec(x_171);
x_173 = lean_box(0);
x_174 = x_181;
goto block_180;
}
block_180:
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_175 = lean_obj_once(&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__42, &l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__42_once, _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__42);
x_176 = lean_string_append(x_175, x_172);
lean_dec(x_172);
if (x_174 == 0)
{
lean_ctor_set(x_173, 0, x_176);
x_177 = x_173;
goto block_178;
}
else
{
lean_object* x_179; 
x_179 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_179, 0, x_176);
x_177 = x_179;
goto block_178;
}
block_178:
{
return x_177;
}
}
}
else
{
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_182; lean_object* x_183; uint8_t x_184; uint8_t x_189; 
lean_dec(x_169);
lean_dec(x_148);
lean_dec(x_127);
lean_dec(x_106);
lean_dec(x_85);
lean_dec(x_64);
lean_dec(x_43);
lean_dec(x_22);
lean_dec(x_1);
x_182 = lean_ctor_get(x_171, 0);
x_189 = !lean_is_exclusive(x_171);
if (x_189 == 0)
{
x_183 = x_171;
x_184 = x_189;
goto block_188;
}
else
{
lean_inc(x_182);
lean_dec(x_171);
x_183 = lean_box(0);
x_184 = x_189;
goto block_188;
}
block_188:
{
lean_object* x_185; 
if (x_184 == 0)
{
lean_ctor_set_tag(x_183, 0);
x_185 = x_183;
goto block_186;
}
else
{
lean_object* x_187; 
x_187 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_187, 0, x_182);
x_185 = x_187;
goto block_186;
}
block_186:
{
return x_185;
}
}
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_190 = lean_ctor_get(x_171, 0);
lean_inc(x_190);
lean_dec_ref(x_171);
x_191 = ((lean_object*)(l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__43));
lean_inc(x_1);
x_192 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonStackTable_fromJson_spec__1(x_1, x_191);
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_193; lean_object* x_194; uint8_t x_195; uint8_t x_202; 
lean_dec(x_190);
lean_dec(x_169);
lean_dec(x_148);
lean_dec(x_127);
lean_dec(x_106);
lean_dec(x_85);
lean_dec(x_64);
lean_dec(x_43);
lean_dec(x_22);
lean_dec(x_1);
x_193 = lean_ctor_get(x_192, 0);
x_202 = !lean_is_exclusive(x_192);
if (x_202 == 0)
{
x_194 = x_192;
x_195 = x_202;
goto block_201;
}
else
{
lean_inc(x_193);
lean_dec(x_192);
x_194 = lean_box(0);
x_195 = x_202;
goto block_201;
}
block_201:
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_196 = lean_obj_once(&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__47, &l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__47_once, _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__47);
x_197 = lean_string_append(x_196, x_193);
lean_dec(x_193);
if (x_195 == 0)
{
lean_ctor_set(x_194, 0, x_197);
x_198 = x_194;
goto block_199;
}
else
{
lean_object* x_200; 
x_200 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_200, 0, x_197);
x_198 = x_200;
goto block_199;
}
block_199:
{
return x_198;
}
}
}
else
{
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_203; lean_object* x_204; uint8_t x_205; uint8_t x_210; 
lean_dec(x_190);
lean_dec(x_169);
lean_dec(x_148);
lean_dec(x_127);
lean_dec(x_106);
lean_dec(x_85);
lean_dec(x_64);
lean_dec(x_43);
lean_dec(x_22);
lean_dec(x_1);
x_203 = lean_ctor_get(x_192, 0);
x_210 = !lean_is_exclusive(x_192);
if (x_210 == 0)
{
x_204 = x_192;
x_205 = x_210;
goto block_209;
}
else
{
lean_inc(x_203);
lean_dec(x_192);
x_204 = lean_box(0);
x_205 = x_210;
goto block_209;
}
block_209:
{
lean_object* x_206; 
if (x_205 == 0)
{
lean_ctor_set_tag(x_204, 0);
x_206 = x_204;
goto block_207;
}
else
{
lean_object* x_208; 
x_208 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_208, 0, x_203);
x_206 = x_208;
goto block_207;
}
block_207:
{
return x_206;
}
}
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_211 = lean_ctor_get(x_192, 0);
lean_inc(x_211);
lean_dec_ref(x_192);
x_212 = ((lean_object*)(l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__24));
x_213 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__2(x_1, x_212);
if (lean_obj_tag(x_213) == 0)
{
lean_object* x_214; lean_object* x_215; uint8_t x_216; uint8_t x_223; 
lean_dec(x_211);
lean_dec(x_190);
lean_dec(x_169);
lean_dec(x_148);
lean_dec(x_127);
lean_dec(x_106);
lean_dec(x_85);
lean_dec(x_64);
lean_dec(x_43);
lean_dec(x_22);
x_214 = lean_ctor_get(x_213, 0);
x_223 = !lean_is_exclusive(x_213);
if (x_223 == 0)
{
x_215 = x_213;
x_216 = x_223;
goto block_222;
}
else
{
lean_inc(x_214);
lean_dec(x_213);
x_215 = lean_box(0);
x_216 = x_223;
goto block_222;
}
block_222:
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_217 = lean_obj_once(&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__49, &l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__49_once, _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__49);
x_218 = lean_string_append(x_217, x_214);
lean_dec(x_214);
if (x_216 == 0)
{
lean_ctor_set(x_215, 0, x_218);
x_219 = x_215;
goto block_220;
}
else
{
lean_object* x_221; 
x_221 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_221, 0, x_218);
x_219 = x_221;
goto block_220;
}
block_220:
{
return x_219;
}
}
}
else
{
if (lean_obj_tag(x_213) == 0)
{
lean_object* x_224; lean_object* x_225; uint8_t x_226; uint8_t x_231; 
lean_dec(x_211);
lean_dec(x_190);
lean_dec(x_169);
lean_dec(x_148);
lean_dec(x_127);
lean_dec(x_106);
lean_dec(x_85);
lean_dec(x_64);
lean_dec(x_43);
lean_dec(x_22);
x_224 = lean_ctor_get(x_213, 0);
x_231 = !lean_is_exclusive(x_213);
if (x_231 == 0)
{
x_225 = x_213;
x_226 = x_231;
goto block_230;
}
else
{
lean_inc(x_224);
lean_dec(x_213);
x_225 = lean_box(0);
x_226 = x_231;
goto block_230;
}
block_230:
{
lean_object* x_227; 
if (x_226 == 0)
{
lean_ctor_set_tag(x_225, 0);
x_227 = x_225;
goto block_228;
}
else
{
lean_object* x_229; 
x_229 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_229, 0, x_224);
x_227 = x_229;
goto block_228;
}
block_228:
{
return x_227;
}
}
}
else
{
lean_object* x_232; lean_object* x_233; uint8_t x_234; uint8_t x_240; 
x_232 = lean_ctor_get(x_213, 0);
x_240 = !lean_is_exclusive(x_213);
if (x_240 == 0)
{
x_233 = x_213;
x_234 = x_240;
goto block_239;
}
else
{
lean_inc(x_232);
lean_dec(x_213);
x_233 = lean_box(0);
x_234 = x_240;
goto block_239;
}
block_239:
{
lean_object* x_235; lean_object* x_236; 
x_235 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_235, 0, x_22);
lean_ctor_set(x_235, 1, x_43);
lean_ctor_set(x_235, 2, x_64);
lean_ctor_set(x_235, 3, x_85);
lean_ctor_set(x_235, 4, x_106);
lean_ctor_set(x_235, 5, x_127);
lean_ctor_set(x_235, 6, x_148);
lean_ctor_set(x_235, 7, x_169);
lean_ctor_set(x_235, 8, x_190);
lean_ctor_set(x_235, 9, x_211);
lean_ctor_set(x_235, 10, x_232);
if (x_234 == 0)
{
lean_ctor_set(x_233, 0, x_235);
x_236 = x_233;
goto block_237;
}
else
{
lean_object* x_238; 
x_238 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_238, 0, x_235);
x_236 = x_238;
goto block_237;
}
block_237:
{
return x_236;
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
}
}
LEAN_EXPORT lean_object* l_Option_toJson___at___00Array_toJson___at___00Lean_Firefox_instToJsonFrameTable_toJson_spec__0_spec__0(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Option_toJson___at___00Array_toJson___at___00Lean_Firefox_instToJsonFrameTable_toJson_spec__0_spec__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Option_toJson___at___00Array_toJson___at___00Lean_Firefox_instToJsonFrameTable_toJson_spec__0_spec__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Firefox_instToJsonFrameTable_toJson_spec__0_spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_8 = l_Option_toJson___at___00Array_toJson___at___00Lean_Firefox_instToJsonFrameTable_toJson_spec__0_spec__0(x_5);
lean_dec(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Firefox_instToJsonFrameTable_toJson_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Firefox_instToJsonFrameTable_toJson_spec__0_spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Firefox_instToJsonFrameTable_toJson_spec__0(lean_object* x_1) {
_start:
{
size_t x_2; size_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_array_size(x_1);
x_3 = 0;
x_4 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Firefox_instToJsonFrameTable_toJson_spec__0_spec__1(x_2, x_3, x_1);
x_5 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Firefox_instToJsonFrameTable_toJson(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_1, 4);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_1, 5);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_1, 6);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_1, 7);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_1, 8);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_1, 9);
lean_inc_ref(x_11);
x_12 = lean_ctor_get(x_1, 10);
lean_inc(x_12);
lean_dec_ref(x_1);
x_13 = ((lean_object*)(l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__0));
x_14 = l_Array_toJson___at___00Lean_Firefox_instToJsonFuncTable_toJson_spec__0(x_2);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = ((lean_object*)(l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__9));
x_19 = l_Array_toJson___at___00Lean_Firefox_instToJsonStackTable_toJson_spec__0(x_3);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_16);
x_22 = ((lean_object*)(l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__9));
x_23 = l_Array_toJson___at___00Lean_Firefox_instToJsonStackTable_toJson_spec__1(x_4);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_16);
x_26 = ((lean_object*)(l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__14));
x_27 = l_Array_toJson___at___00Lean_Firefox_instToJsonStackTable_toJson_spec__1(x_5);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_16);
x_30 = ((lean_object*)(l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__18));
x_31 = l_Array_toJson___at___00Lean_Firefox_instToJsonStackTable_toJson_spec__0(x_6);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_16);
x_34 = ((lean_object*)(l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__23));
x_35 = l_Array_toJson___at___00Lean_Firefox_instToJsonFrameTable_toJson_spec__0(x_7);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_16);
x_38 = ((lean_object*)(l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__28));
x_39 = l_Array_toJson___at___00Lean_Firefox_instToJsonFrameTable_toJson_spec__0(x_8);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_16);
x_42 = ((lean_object*)(l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__33));
x_43 = l_Array_toJson___at___00Lean_Firefox_instToJsonFrameTable_toJson_spec__0(x_9);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_16);
x_46 = ((lean_object*)(l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__38));
x_47 = l_Array_toJson___at___00Lean_Firefox_instToJsonStackTable_toJson_spec__1(x_10);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_16);
x_50 = ((lean_object*)(l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__43));
x_51 = l_Array_toJson___at___00Lean_Firefox_instToJsonStackTable_toJson_spec__1(x_11);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_16);
x_54 = ((lean_object*)(l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__24));
x_55 = l_Lean_JsonNumber_fromNat(x_12);
x_56 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_56, 0, x_55);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_16);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_16);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_53);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_49);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_45);
lean_ctor_set(x_62, 1, x_61);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_41);
lean_ctor_set(x_63, 1, x_62);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_37);
lean_ctor_set(x_64, 1, x_63);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_33);
lean_ctor_set(x_65, 1, x_64);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_29);
lean_ctor_set(x_66, 1, x_65);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_25);
lean_ctor_set(x_67, 1, x_66);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_21);
lean_ctor_set(x_68, 1, x_67);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_17);
lean_ctor_set(x_69, 1, x_68);
x_70 = ((lean_object*)(l_Lean_Firefox_instToJsonCategory_toJson___closed__0));
x_71 = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Firefox_instToJsonCategory_toJson_spec__1(x_69, x_70);
x_72 = l_Lean_Json_mkObj(x_71);
return x_72;
}
}
static lean_object* _init_l_Lean_Firefox_instInhabitedFrameTable_default___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = ((lean_object*)(l_Lean_Firefox_instInhabitedFrameTable_default___closed__0));
x_3 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 3, x_2);
lean_ctor_set(x_3, 4, x_2);
lean_ctor_set(x_3, 5, x_2);
lean_ctor_set(x_3, 6, x_2);
lean_ctor_set(x_3, 7, x_2);
lean_ctor_set(x_3, 8, x_2);
lean_ctor_set(x_3, 9, x_2);
lean_ctor_set(x_3, 10, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instInhabitedFrameTable_default(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_Lean_Firefox_instInhabitedFrameTable_default___closed__1, &l_Lean_Firefox_instInhabitedFrameTable_default___closed__1_once, _init_l_Lean_Firefox_instInhabitedFrameTable_default___closed__1);
return x_1;
}
}
static lean_object* _init_l_Lean_Firefox_instInhabitedFrameTable(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Firefox_instInhabitedFrameTable_default;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Firefox_FrameTable_push(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_42; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_ctor_get(x_1, 3);
x_7 = lean_ctor_get(x_1, 4);
x_8 = lean_ctor_get(x_1, 5);
x_9 = lean_ctor_get(x_1, 6);
x_10 = lean_ctor_get(x_1, 7);
x_11 = lean_ctor_get(x_1, 8);
x_12 = lean_ctor_get(x_1, 9);
x_13 = lean_ctor_get(x_1, 10);
x_42 = !lean_is_exclusive(x_1);
if (x_42 == 0)
{
x_14 = x_1;
x_15 = x_42;
goto block_41;
}
else
{
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_1);
x_14 = lean_box(0);
x_15 = x_42;
goto block_41;
}
block_41:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_16 = lean_ctor_get(x_2, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_2, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_2, 2);
lean_inc(x_18);
x_19 = lean_ctor_get(x_2, 3);
lean_inc(x_19);
x_20 = lean_ctor_get(x_2, 4);
lean_inc(x_20);
x_21 = lean_ctor_get(x_2, 5);
lean_inc(x_21);
x_22 = lean_ctor_get(x_2, 6);
lean_inc(x_22);
x_23 = lean_ctor_get(x_2, 7);
lean_inc(x_23);
x_24 = lean_ctor_get(x_2, 8);
lean_inc(x_24);
x_25 = lean_ctor_get(x_2, 9);
lean_inc(x_25);
lean_dec_ref(x_2);
x_26 = lean_array_push(x_3, x_16);
x_27 = lean_array_push(x_4, x_17);
x_28 = lean_array_push(x_5, x_18);
x_29 = lean_array_push(x_6, x_19);
x_30 = lean_array_push(x_7, x_20);
x_31 = lean_array_push(x_8, x_21);
x_32 = lean_array_push(x_9, x_22);
x_33 = lean_array_push(x_10, x_23);
x_34 = lean_array_push(x_11, x_24);
x_35 = lean_array_push(x_12, x_25);
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_nat_add(x_13, x_36);
lean_dec(x_13);
if (x_15 == 0)
{
lean_ctor_set(x_14, 10, x_37);
lean_ctor_set(x_14, 9, x_35);
lean_ctor_set(x_14, 8, x_34);
lean_ctor_set(x_14, 7, x_33);
lean_ctor_set(x_14, 6, x_32);
lean_ctor_set(x_14, 5, x_31);
lean_ctor_set(x_14, 4, x_30);
lean_ctor_set(x_14, 3, x_29);
lean_ctor_set(x_14, 2, x_28);
lean_ctor_set(x_14, 1, x_27);
lean_ctor_set(x_14, 0, x_26);
x_38 = x_14;
goto block_39;
}
else
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_40, 0, x_26);
lean_ctor_set(x_40, 1, x_27);
lean_ctor_set(x_40, 2, x_28);
lean_ctor_set(x_40, 3, x_29);
lean_ctor_set(x_40, 4, x_30);
lean_ctor_set(x_40, 5, x_31);
lean_ctor_set(x_40, 6, x_32);
lean_ctor_set(x_40, 7, x_33);
lean_ctor_set(x_40, 8, x_34);
lean_ctor_set(x_40, 9, x_35);
lean_ctor_set(x_40, 10, x_37);
x_38 = x_40;
goto block_39;
}
block_39:
{
return x_38;
}
}
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__3(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__2));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__6));
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__3, &l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__3_once, _init_l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__3);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__6(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__5));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__6, &l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__6_once, _init_l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__6);
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__4, &l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__4_once, _init_l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__4);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__8(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__7, &l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__7_once, _init_l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__7);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__9(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Firefox_instFromJsonCategory_fromJson___closed__9, &l_Lean_Firefox_instFromJsonCategory_fromJson___closed__9_once, _init_l_Lean_Firefox_instFromJsonCategory_fromJson___closed__9);
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__4, &l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__4_once, _init_l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__4);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__10(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__9, &l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__9_once, _init_l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__9);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__11(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__26, &l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__26_once, _init_l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__26);
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__4, &l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__4_once, _init_l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__4);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__12(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__11, &l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__11_once, _init_l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__11);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = ((lean_object*)(l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__0));
lean_inc(x_1);
x_3 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__3(x_1, x_2);
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
x_7 = lean_obj_once(&l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__8, &l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__8_once, _init_l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__8);
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
x_23 = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__0));
lean_inc(x_1);
x_24 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__3(x_1, x_23);
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
x_28 = lean_obj_once(&l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__10, &l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__10_once, _init_l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__10);
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
x_44 = ((lean_object*)(l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__24));
x_45 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__2(x_1, x_44);
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
x_49 = lean_obj_once(&l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__12, &l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__12_once, _init_l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__12);
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
lean_object* x_64; lean_object* x_65; uint8_t x_66; uint8_t x_72; 
x_64 = lean_ctor_get(x_45, 0);
x_72 = !lean_is_exclusive(x_45);
if (x_72 == 0)
{
x_65 = x_45;
x_66 = x_72;
goto block_71;
}
else
{
lean_inc(x_64);
lean_dec(x_45);
x_65 = lean_box(0);
x_66 = x_72;
goto block_71;
}
block_71:
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_67, 0, x_22);
lean_ctor_set(x_67, 1, x_43);
lean_ctor_set(x_67, 2, x_64);
if (x_66 == 0)
{
lean_ctor_set(x_65, 0, x_67);
x_68 = x_65;
goto block_69;
}
else
{
lean_object* x_70; 
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_67);
x_68 = x_70;
goto block_69;
}
block_69:
{
return x_68;
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
LEAN_EXPORT lean_object* l_Lean_Firefox_instToJsonRawMarkerTable_toJson(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = ((lean_object*)(l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__0));
x_6 = l_Array_toJson___at___00Lean_Firefox_instToJsonProfileMeta_toJson_spec__1(x_2);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__0));
x_11 = l_Array_toJson___at___00Lean_Firefox_instToJsonProfileMeta_toJson_spec__1(x_3);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_8);
x_14 = ((lean_object*)(l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__24));
x_15 = l_Lean_JsonNumber_fromNat(x_4);
x_16 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_8);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_8);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_13);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_9);
lean_ctor_set(x_21, 1, x_20);
x_22 = ((lean_object*)(l_Lean_Firefox_instToJsonCategory_toJson___closed__0));
x_23 = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Firefox_instToJsonCategory_toJson_spec__1(x_21, x_22);
x_24 = l_Lean_Json_mkObj(x_23);
return x_24;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__3(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__2));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__6));
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__3, &l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__3_once, _init_l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__3);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__6(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__5));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__6, &l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__6_once, _init_l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__6);
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__4, &l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__4_once, _init_l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__4);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__8(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__7, &l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__7_once, _init_l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__7);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__9(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__26, &l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__26_once, _init_l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__26);
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__4, &l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__4_once, _init_l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__4);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__10(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__9, &l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__9_once, _init_l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__9);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Firefox_instFromJsonResourceTable_fromJson(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = ((lean_object*)(l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__0));
lean_inc(x_1);
x_3 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__3(x_1, x_2);
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
x_7 = lean_obj_once(&l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__8, &l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__8_once, _init_l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__8);
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
x_23 = ((lean_object*)(l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__24));
x_24 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__2(x_1, x_23);
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
x_28 = lean_obj_once(&l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__10, &l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__10_once, _init_l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__10);
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
lean_object* x_43; lean_object* x_44; uint8_t x_45; uint8_t x_51; 
x_43 = lean_ctor_get(x_24, 0);
x_51 = !lean_is_exclusive(x_24);
if (x_51 == 0)
{
x_44 = x_24;
x_45 = x_51;
goto block_50;
}
else
{
lean_inc(x_43);
lean_dec(x_24);
x_44 = lean_box(0);
x_45 = x_51;
goto block_50;
}
block_50:
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_22);
lean_ctor_set(x_46, 1, x_43);
if (x_45 == 0)
{
lean_ctor_set(x_44, 0, x_46);
x_47 = x_44;
goto block_48;
}
else
{
lean_object* x_49; 
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_46);
x_47 = x_49;
goto block_48;
}
block_48:
{
return x_47;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Firefox_instToJsonResourceTable_toJson(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_24; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_24 = !lean_is_exclusive(x_1);
if (x_24 == 0)
{
x_4 = x_1;
x_5 = x_24;
goto block_23;
}
else
{
lean_inc(x_3);
lean_inc(x_2);
lean_dec(x_1);
x_4 = lean_box(0);
x_5 = x_24;
goto block_23;
}
block_23:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = ((lean_object*)(l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__0));
x_7 = l_Array_toJson___at___00Lean_Firefox_instToJsonProfileMeta_toJson_spec__1(x_2);
if (x_5 == 0)
{
lean_ctor_set(x_4, 1, x_7);
lean_ctor_set(x_4, 0, x_6);
x_8 = x_4;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_6);
lean_ctor_set(x_22, 1, x_7);
x_8 = x_22;
goto block_21;
}
block_21:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = ((lean_object*)(l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__24));
x_12 = l_Lean_JsonNumber_fromNat(x_3);
x_13 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_9);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_9);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_16);
x_18 = ((lean_object*)(l_Lean_Firefox_instToJsonCategory_toJson___closed__0));
x_19 = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Firefox_instToJsonCategory_toJson_spec__1(x_17, x_18);
x_20 = l_Lean_Json_mkObj(x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonThread_fromJson_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l_Lean_Json_getBool_x3f(x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonThread_fromJson_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonThread_fromJson_spec__0(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonThread_fromJson_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l_Lean_Firefox_instFromJsonSamplesTable_fromJson(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonThread_fromJson_spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonThread_fromJson_spec__1(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonThread_fromJson_spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonThread_fromJson_spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonThread_fromJson_spec__2(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonThread_fromJson_spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l_Lean_Firefox_instFromJsonStackTable_fromJson(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonThread_fromJson_spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonThread_fromJson_spec__3(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonThread_fromJson_spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l_Lean_Firefox_instFromJsonFrameTable_fromJson(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonThread_fromJson_spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonThread_fromJson_spec__4(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonThread_fromJson_spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l_Lean_Firefox_instFromJsonResourceTable_fromJson(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonThread_fromJson_spec__5___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonThread_fromJson_spec__5(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonThread_fromJson_spec__6(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l_Lean_Firefox_instFromJsonFuncTable_fromJson(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonThread_fromJson_spec__6___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonThread_fromJson_spec__6(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__2(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_Firefox_instFromJsonThread_fromJson___closed__1));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__6));
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonThread_fromJson___closed__2, &l_Lean_Firefox_instFromJsonThread_fromJson___closed__2_once, _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__2);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Firefox_instFromJsonCategory_fromJson___closed__9, &l_Lean_Firefox_instFromJsonCategory_fromJson___closed__9_once, _init_l_Lean_Firefox_instFromJsonCategory_fromJson___closed__9);
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonThread_fromJson___closed__3, &l_Lean_Firefox_instFromJsonThread_fromJson___closed__3_once, _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__3);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonThread_fromJson___closed__4, &l_Lean_Firefox_instFromJsonThread_fromJson___closed__4_once, _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__4);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__21, &l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__21_once, _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__21);
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonThread_fromJson___closed__3, &l_Lean_Firefox_instFromJsonThread_fromJson___closed__3_once, _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__3);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonThread_fromJson___closed__6, &l_Lean_Firefox_instFromJsonThread_fromJson___closed__6_once, _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__6);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__10(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_Firefox_instFromJsonThread_fromJson___closed__9));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__11(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Firefox_instFromJsonThread_fromJson___closed__10, &l_Lean_Firefox_instFromJsonThread_fromJson___closed__10_once, _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__10);
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonThread_fromJson___closed__3, &l_Lean_Firefox_instFromJsonThread_fromJson___closed__3_once, _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__3);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__12(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonThread_fromJson___closed__11, &l_Lean_Firefox_instFromJsonThread_fromJson___closed__11_once, _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__11);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__15(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_Firefox_instFromJsonThread_fromJson___closed__14));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__16(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Firefox_instFromJsonThread_fromJson___closed__15, &l_Lean_Firefox_instFromJsonThread_fromJson___closed__15_once, _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__15);
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonThread_fromJson___closed__3, &l_Lean_Firefox_instFromJsonThread_fromJson___closed__3_once, _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__3);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__17(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonThread_fromJson___closed__16, &l_Lean_Firefox_instFromJsonThread_fromJson___closed__16_once, _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__16);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__20(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_Firefox_instFromJsonThread_fromJson___closed__19));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__21(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Firefox_instFromJsonThread_fromJson___closed__20, &l_Lean_Firefox_instFromJsonThread_fromJson___closed__20_once, _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__20);
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonThread_fromJson___closed__3, &l_Lean_Firefox_instFromJsonThread_fromJson___closed__3_once, _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__3);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__22(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonThread_fromJson___closed__21, &l_Lean_Firefox_instFromJsonThread_fromJson___closed__21_once, _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__21);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__25(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_Firefox_instFromJsonThread_fromJson___closed__24));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__26(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Firefox_instFromJsonThread_fromJson___closed__25, &l_Lean_Firefox_instFromJsonThread_fromJson___closed__25_once, _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__25);
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonThread_fromJson___closed__3, &l_Lean_Firefox_instFromJsonThread_fromJson___closed__3_once, _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__3);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__27(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonThread_fromJson___closed__26, &l_Lean_Firefox_instFromJsonThread_fromJson___closed__26_once, _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__26);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__30(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_Firefox_instFromJsonThread_fromJson___closed__29));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__31(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Firefox_instFromJsonThread_fromJson___closed__30, &l_Lean_Firefox_instFromJsonThread_fromJson___closed__30_once, _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__30);
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonThread_fromJson___closed__3, &l_Lean_Firefox_instFromJsonThread_fromJson___closed__3_once, _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__3);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__32(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonThread_fromJson___closed__31, &l_Lean_Firefox_instFromJsonThread_fromJson___closed__31_once, _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__31);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__35(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_Firefox_instFromJsonThread_fromJson___closed__34));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__36(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Firefox_instFromJsonThread_fromJson___closed__35, &l_Lean_Firefox_instFromJsonThread_fromJson___closed__35_once, _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__35);
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonThread_fromJson___closed__3, &l_Lean_Firefox_instFromJsonThread_fromJson___closed__3_once, _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__3);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__37(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonThread_fromJson___closed__36, &l_Lean_Firefox_instFromJsonThread_fromJson___closed__36_once, _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__36);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__40(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_Firefox_instFromJsonThread_fromJson___closed__39));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__41(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Firefox_instFromJsonThread_fromJson___closed__40, &l_Lean_Firefox_instFromJsonThread_fromJson___closed__40_once, _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__40);
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonThread_fromJson___closed__3, &l_Lean_Firefox_instFromJsonThread_fromJson___closed__3_once, _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__3);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__42(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonThread_fromJson___closed__41, &l_Lean_Firefox_instFromJsonThread_fromJson___closed__41_once, _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__41);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__45(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_Firefox_instFromJsonThread_fromJson___closed__44));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__46(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Firefox_instFromJsonThread_fromJson___closed__45, &l_Lean_Firefox_instFromJsonThread_fromJson___closed__45_once, _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__45);
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonThread_fromJson___closed__3, &l_Lean_Firefox_instFromJsonThread_fromJson___closed__3_once, _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__3);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__47(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonThread_fromJson___closed__46, &l_Lean_Firefox_instFromJsonThread_fromJson___closed__46_once, _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__46);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__50(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_Firefox_instFromJsonThread_fromJson___closed__49));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__51(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Firefox_instFromJsonThread_fromJson___closed__50, &l_Lean_Firefox_instFromJsonThread_fromJson___closed__50_once, _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__50);
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonThread_fromJson___closed__3, &l_Lean_Firefox_instFromJsonThread_fromJson___closed__3_once, _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__3);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__52(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonThread_fromJson___closed__51, &l_Lean_Firefox_instFromJsonThread_fromJson___closed__51_once, _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__51);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Firefox_instFromJsonThread_fromJson(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__0));
lean_inc(x_1);
x_3 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__1(x_1, x_2);
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
x_7 = lean_obj_once(&l_Lean_Firefox_instFromJsonThread_fromJson___closed__5, &l_Lean_Firefox_instFromJsonThread_fromJson___closed__5_once, _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__5);
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
x_23 = ((lean_object*)(l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__19));
lean_inc(x_1);
x_24 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__1(x_1, x_23);
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
x_28 = lean_obj_once(&l_Lean_Firefox_instFromJsonThread_fromJson___closed__7, &l_Lean_Firefox_instFromJsonThread_fromJson___closed__7_once, _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__7);
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
x_44 = ((lean_object*)(l_Lean_Firefox_instFromJsonThread_fromJson___closed__8));
lean_inc(x_1);
x_45 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonThread_fromJson_spec__0(x_1, x_44);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_55; 
lean_dec(x_43);
lean_dec(x_22);
lean_dec(x_1);
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
x_49 = lean_obj_once(&l_Lean_Firefox_instFromJsonThread_fromJson___closed__12, &l_Lean_Firefox_instFromJsonThread_fromJson___closed__12_once, _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__12);
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
lean_dec(x_1);
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
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_45, 0);
lean_inc(x_64);
lean_dec_ref(x_45);
x_65 = ((lean_object*)(l_Lean_Firefox_instFromJsonThread_fromJson___closed__13));
lean_inc(x_1);
x_66 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonThread_fromJson_spec__1(x_1, x_65);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; uint8_t x_76; 
lean_dec(x_64);
lean_dec(x_43);
lean_dec(x_22);
lean_dec(x_1);
x_67 = lean_ctor_get(x_66, 0);
x_76 = !lean_is_exclusive(x_66);
if (x_76 == 0)
{
x_68 = x_66;
x_69 = x_76;
goto block_75;
}
else
{
lean_inc(x_67);
lean_dec(x_66);
x_68 = lean_box(0);
x_69 = x_76;
goto block_75;
}
block_75:
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_obj_once(&l_Lean_Firefox_instFromJsonThread_fromJson___closed__17, &l_Lean_Firefox_instFromJsonThread_fromJson___closed__17_once, _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__17);
x_71 = lean_string_append(x_70, x_67);
lean_dec(x_67);
if (x_69 == 0)
{
lean_ctor_set(x_68, 0, x_71);
x_72 = x_68;
goto block_73;
}
else
{
lean_object* x_74; 
x_74 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_74, 0, x_71);
x_72 = x_74;
goto block_73;
}
block_73:
{
return x_72;
}
}
}
else
{
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_77; lean_object* x_78; uint8_t x_79; uint8_t x_84; 
lean_dec(x_64);
lean_dec(x_43);
lean_dec(x_22);
lean_dec(x_1);
x_77 = lean_ctor_get(x_66, 0);
x_84 = !lean_is_exclusive(x_66);
if (x_84 == 0)
{
x_78 = x_66;
x_79 = x_84;
goto block_83;
}
else
{
lean_inc(x_77);
lean_dec(x_66);
x_78 = lean_box(0);
x_79 = x_84;
goto block_83;
}
block_83:
{
lean_object* x_80; 
if (x_79 == 0)
{
lean_ctor_set_tag(x_78, 0);
x_80 = x_78;
goto block_81;
}
else
{
lean_object* x_82; 
x_82 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_82, 0, x_77);
x_80 = x_82;
goto block_81;
}
block_81:
{
return x_80;
}
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_66, 0);
lean_inc(x_85);
lean_dec_ref(x_66);
x_86 = ((lean_object*)(l_Lean_Firefox_instFromJsonThread_fromJson___closed__18));
lean_inc(x_1);
x_87 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonThread_fromJson_spec__2(x_1, x_86);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; uint8_t x_90; uint8_t x_97; 
lean_dec(x_85);
lean_dec(x_64);
lean_dec(x_43);
lean_dec(x_22);
lean_dec(x_1);
x_88 = lean_ctor_get(x_87, 0);
x_97 = !lean_is_exclusive(x_87);
if (x_97 == 0)
{
x_89 = x_87;
x_90 = x_97;
goto block_96;
}
else
{
lean_inc(x_88);
lean_dec(x_87);
x_89 = lean_box(0);
x_90 = x_97;
goto block_96;
}
block_96:
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_obj_once(&l_Lean_Firefox_instFromJsonThread_fromJson___closed__22, &l_Lean_Firefox_instFromJsonThread_fromJson___closed__22_once, _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__22);
x_92 = lean_string_append(x_91, x_88);
lean_dec(x_88);
if (x_90 == 0)
{
lean_ctor_set(x_89, 0, x_92);
x_93 = x_89;
goto block_94;
}
else
{
lean_object* x_95; 
x_95 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_95, 0, x_92);
x_93 = x_95;
goto block_94;
}
block_94:
{
return x_93;
}
}
}
else
{
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_98; lean_object* x_99; uint8_t x_100; uint8_t x_105; 
lean_dec(x_85);
lean_dec(x_64);
lean_dec(x_43);
lean_dec(x_22);
lean_dec(x_1);
x_98 = lean_ctor_get(x_87, 0);
x_105 = !lean_is_exclusive(x_87);
if (x_105 == 0)
{
x_99 = x_87;
x_100 = x_105;
goto block_104;
}
else
{
lean_inc(x_98);
lean_dec(x_87);
x_99 = lean_box(0);
x_100 = x_105;
goto block_104;
}
block_104:
{
lean_object* x_101; 
if (x_100 == 0)
{
lean_ctor_set_tag(x_99, 0);
x_101 = x_99;
goto block_102;
}
else
{
lean_object* x_103; 
x_103 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_103, 0, x_98);
x_101 = x_103;
goto block_102;
}
block_102:
{
return x_101;
}
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_87, 0);
lean_inc(x_106);
lean_dec_ref(x_87);
x_107 = ((lean_object*)(l_Lean_Firefox_instFromJsonThread_fromJson___closed__23));
lean_inc(x_1);
x_108 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonThread_fromJson_spec__3(x_1, x_107);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; uint8_t x_111; uint8_t x_118; 
lean_dec(x_106);
lean_dec(x_85);
lean_dec(x_64);
lean_dec(x_43);
lean_dec(x_22);
lean_dec(x_1);
x_109 = lean_ctor_get(x_108, 0);
x_118 = !lean_is_exclusive(x_108);
if (x_118 == 0)
{
x_110 = x_108;
x_111 = x_118;
goto block_117;
}
else
{
lean_inc(x_109);
lean_dec(x_108);
x_110 = lean_box(0);
x_111 = x_118;
goto block_117;
}
block_117:
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_obj_once(&l_Lean_Firefox_instFromJsonThread_fromJson___closed__27, &l_Lean_Firefox_instFromJsonThread_fromJson___closed__27_once, _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__27);
x_113 = lean_string_append(x_112, x_109);
lean_dec(x_109);
if (x_111 == 0)
{
lean_ctor_set(x_110, 0, x_113);
x_114 = x_110;
goto block_115;
}
else
{
lean_object* x_116; 
x_116 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_116, 0, x_113);
x_114 = x_116;
goto block_115;
}
block_115:
{
return x_114;
}
}
}
else
{
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_119; lean_object* x_120; uint8_t x_121; uint8_t x_126; 
lean_dec(x_106);
lean_dec(x_85);
lean_dec(x_64);
lean_dec(x_43);
lean_dec(x_22);
lean_dec(x_1);
x_119 = lean_ctor_get(x_108, 0);
x_126 = !lean_is_exclusive(x_108);
if (x_126 == 0)
{
x_120 = x_108;
x_121 = x_126;
goto block_125;
}
else
{
lean_inc(x_119);
lean_dec(x_108);
x_120 = lean_box(0);
x_121 = x_126;
goto block_125;
}
block_125:
{
lean_object* x_122; 
if (x_121 == 0)
{
lean_ctor_set_tag(x_120, 0);
x_122 = x_120;
goto block_123;
}
else
{
lean_object* x_124; 
x_124 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_124, 0, x_119);
x_122 = x_124;
goto block_123;
}
block_123:
{
return x_122;
}
}
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_108, 0);
lean_inc(x_127);
lean_dec_ref(x_108);
x_128 = ((lean_object*)(l_Lean_Firefox_instFromJsonThread_fromJson___closed__28));
lean_inc(x_1);
x_129 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonThread_fromJson_spec__4(x_1, x_128);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; uint8_t x_132; uint8_t x_139; 
lean_dec(x_127);
lean_dec(x_106);
lean_dec(x_85);
lean_dec(x_64);
lean_dec(x_43);
lean_dec(x_22);
lean_dec(x_1);
x_130 = lean_ctor_get(x_129, 0);
x_139 = !lean_is_exclusive(x_129);
if (x_139 == 0)
{
x_131 = x_129;
x_132 = x_139;
goto block_138;
}
else
{
lean_inc(x_130);
lean_dec(x_129);
x_131 = lean_box(0);
x_132 = x_139;
goto block_138;
}
block_138:
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_obj_once(&l_Lean_Firefox_instFromJsonThread_fromJson___closed__32, &l_Lean_Firefox_instFromJsonThread_fromJson___closed__32_once, _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__32);
x_134 = lean_string_append(x_133, x_130);
lean_dec(x_130);
if (x_132 == 0)
{
lean_ctor_set(x_131, 0, x_134);
x_135 = x_131;
goto block_136;
}
else
{
lean_object* x_137; 
x_137 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_137, 0, x_134);
x_135 = x_137;
goto block_136;
}
block_136:
{
return x_135;
}
}
}
else
{
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_140; lean_object* x_141; uint8_t x_142; uint8_t x_147; 
lean_dec(x_127);
lean_dec(x_106);
lean_dec(x_85);
lean_dec(x_64);
lean_dec(x_43);
lean_dec(x_22);
lean_dec(x_1);
x_140 = lean_ctor_get(x_129, 0);
x_147 = !lean_is_exclusive(x_129);
if (x_147 == 0)
{
x_141 = x_129;
x_142 = x_147;
goto block_146;
}
else
{
lean_inc(x_140);
lean_dec(x_129);
x_141 = lean_box(0);
x_142 = x_147;
goto block_146;
}
block_146:
{
lean_object* x_143; 
if (x_142 == 0)
{
lean_ctor_set_tag(x_141, 0);
x_143 = x_141;
goto block_144;
}
else
{
lean_object* x_145; 
x_145 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_145, 0, x_140);
x_143 = x_145;
goto block_144;
}
block_144:
{
return x_143;
}
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_148 = lean_ctor_get(x_129, 0);
lean_inc(x_148);
lean_dec_ref(x_129);
x_149 = ((lean_object*)(l_Lean_Firefox_instFromJsonThread_fromJson___closed__33));
lean_inc(x_1);
x_150 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonThread_fromJson_spec__5(x_1, x_149);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; lean_object* x_152; uint8_t x_153; uint8_t x_160; 
lean_dec(x_148);
lean_dec(x_127);
lean_dec(x_106);
lean_dec(x_85);
lean_dec(x_64);
lean_dec(x_43);
lean_dec(x_22);
lean_dec(x_1);
x_151 = lean_ctor_get(x_150, 0);
x_160 = !lean_is_exclusive(x_150);
if (x_160 == 0)
{
x_152 = x_150;
x_153 = x_160;
goto block_159;
}
else
{
lean_inc(x_151);
lean_dec(x_150);
x_152 = lean_box(0);
x_153 = x_160;
goto block_159;
}
block_159:
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_154 = lean_obj_once(&l_Lean_Firefox_instFromJsonThread_fromJson___closed__37, &l_Lean_Firefox_instFromJsonThread_fromJson___closed__37_once, _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__37);
x_155 = lean_string_append(x_154, x_151);
lean_dec(x_151);
if (x_153 == 0)
{
lean_ctor_set(x_152, 0, x_155);
x_156 = x_152;
goto block_157;
}
else
{
lean_object* x_158; 
x_158 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_158, 0, x_155);
x_156 = x_158;
goto block_157;
}
block_157:
{
return x_156;
}
}
}
else
{
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_161; lean_object* x_162; uint8_t x_163; uint8_t x_168; 
lean_dec(x_148);
lean_dec(x_127);
lean_dec(x_106);
lean_dec(x_85);
lean_dec(x_64);
lean_dec(x_43);
lean_dec(x_22);
lean_dec(x_1);
x_161 = lean_ctor_get(x_150, 0);
x_168 = !lean_is_exclusive(x_150);
if (x_168 == 0)
{
x_162 = x_150;
x_163 = x_168;
goto block_167;
}
else
{
lean_inc(x_161);
lean_dec(x_150);
x_162 = lean_box(0);
x_163 = x_168;
goto block_167;
}
block_167:
{
lean_object* x_164; 
if (x_163 == 0)
{
lean_ctor_set_tag(x_162, 0);
x_164 = x_162;
goto block_165;
}
else
{
lean_object* x_166; 
x_166 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_166, 0, x_161);
x_164 = x_166;
goto block_165;
}
block_165:
{
return x_164;
}
}
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_169 = lean_ctor_get(x_150, 0);
lean_inc(x_169);
lean_dec_ref(x_150);
x_170 = ((lean_object*)(l_Lean_Firefox_instFromJsonThread_fromJson___closed__38));
lean_inc(x_1);
x_171 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonThread_fromJson_spec__5(x_1, x_170);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; lean_object* x_173; uint8_t x_174; uint8_t x_181; 
lean_dec(x_169);
lean_dec(x_148);
lean_dec(x_127);
lean_dec(x_106);
lean_dec(x_85);
lean_dec(x_64);
lean_dec(x_43);
lean_dec(x_22);
lean_dec(x_1);
x_172 = lean_ctor_get(x_171, 0);
x_181 = !lean_is_exclusive(x_171);
if (x_181 == 0)
{
x_173 = x_171;
x_174 = x_181;
goto block_180;
}
else
{
lean_inc(x_172);
lean_dec(x_171);
x_173 = lean_box(0);
x_174 = x_181;
goto block_180;
}
block_180:
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_175 = lean_obj_once(&l_Lean_Firefox_instFromJsonThread_fromJson___closed__42, &l_Lean_Firefox_instFromJsonThread_fromJson___closed__42_once, _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__42);
x_176 = lean_string_append(x_175, x_172);
lean_dec(x_172);
if (x_174 == 0)
{
lean_ctor_set(x_173, 0, x_176);
x_177 = x_173;
goto block_178;
}
else
{
lean_object* x_179; 
x_179 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_179, 0, x_176);
x_177 = x_179;
goto block_178;
}
block_178:
{
return x_177;
}
}
}
else
{
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_182; lean_object* x_183; uint8_t x_184; uint8_t x_189; 
lean_dec(x_169);
lean_dec(x_148);
lean_dec(x_127);
lean_dec(x_106);
lean_dec(x_85);
lean_dec(x_64);
lean_dec(x_43);
lean_dec(x_22);
lean_dec(x_1);
x_182 = lean_ctor_get(x_171, 0);
x_189 = !lean_is_exclusive(x_171);
if (x_189 == 0)
{
x_183 = x_171;
x_184 = x_189;
goto block_188;
}
else
{
lean_inc(x_182);
lean_dec(x_171);
x_183 = lean_box(0);
x_184 = x_189;
goto block_188;
}
block_188:
{
lean_object* x_185; 
if (x_184 == 0)
{
lean_ctor_set_tag(x_183, 0);
x_185 = x_183;
goto block_186;
}
else
{
lean_object* x_187; 
x_187 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_187, 0, x_182);
x_185 = x_187;
goto block_186;
}
block_186:
{
return x_185;
}
}
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_190 = lean_ctor_get(x_171, 0);
lean_inc(x_190);
lean_dec_ref(x_171);
x_191 = ((lean_object*)(l_Lean_Firefox_instFromJsonThread_fromJson___closed__43));
lean_inc(x_1);
x_192 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__2(x_1, x_191);
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_193; lean_object* x_194; uint8_t x_195; uint8_t x_202; 
lean_dec(x_190);
lean_dec(x_169);
lean_dec(x_148);
lean_dec(x_127);
lean_dec(x_106);
lean_dec(x_85);
lean_dec(x_64);
lean_dec(x_43);
lean_dec(x_22);
lean_dec(x_1);
x_193 = lean_ctor_get(x_192, 0);
x_202 = !lean_is_exclusive(x_192);
if (x_202 == 0)
{
x_194 = x_192;
x_195 = x_202;
goto block_201;
}
else
{
lean_inc(x_193);
lean_dec(x_192);
x_194 = lean_box(0);
x_195 = x_202;
goto block_201;
}
block_201:
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_196 = lean_obj_once(&l_Lean_Firefox_instFromJsonThread_fromJson___closed__47, &l_Lean_Firefox_instFromJsonThread_fromJson___closed__47_once, _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__47);
x_197 = lean_string_append(x_196, x_193);
lean_dec(x_193);
if (x_195 == 0)
{
lean_ctor_set(x_194, 0, x_197);
x_198 = x_194;
goto block_199;
}
else
{
lean_object* x_200; 
x_200 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_200, 0, x_197);
x_198 = x_200;
goto block_199;
}
block_199:
{
return x_198;
}
}
}
else
{
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_203; lean_object* x_204; uint8_t x_205; uint8_t x_210; 
lean_dec(x_190);
lean_dec(x_169);
lean_dec(x_148);
lean_dec(x_127);
lean_dec(x_106);
lean_dec(x_85);
lean_dec(x_64);
lean_dec(x_43);
lean_dec(x_22);
lean_dec(x_1);
x_203 = lean_ctor_get(x_192, 0);
x_210 = !lean_is_exclusive(x_192);
if (x_210 == 0)
{
x_204 = x_192;
x_205 = x_210;
goto block_209;
}
else
{
lean_inc(x_203);
lean_dec(x_192);
x_204 = lean_box(0);
x_205 = x_210;
goto block_209;
}
block_209:
{
lean_object* x_206; 
if (x_205 == 0)
{
lean_ctor_set_tag(x_204, 0);
x_206 = x_204;
goto block_207;
}
else
{
lean_object* x_208; 
x_208 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_208, 0, x_203);
x_206 = x_208;
goto block_207;
}
block_207:
{
return x_206;
}
}
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_211 = lean_ctor_get(x_192, 0);
lean_inc(x_211);
lean_dec_ref(x_192);
x_212 = ((lean_object*)(l_Lean_Firefox_instFromJsonThread_fromJson___closed__48));
x_213 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonThread_fromJson_spec__6(x_1, x_212);
if (lean_obj_tag(x_213) == 0)
{
lean_object* x_214; lean_object* x_215; uint8_t x_216; uint8_t x_223; 
lean_dec(x_211);
lean_dec(x_190);
lean_dec(x_169);
lean_dec(x_148);
lean_dec(x_127);
lean_dec(x_106);
lean_dec(x_85);
lean_dec(x_64);
lean_dec(x_43);
lean_dec(x_22);
x_214 = lean_ctor_get(x_213, 0);
x_223 = !lean_is_exclusive(x_213);
if (x_223 == 0)
{
x_215 = x_213;
x_216 = x_223;
goto block_222;
}
else
{
lean_inc(x_214);
lean_dec(x_213);
x_215 = lean_box(0);
x_216 = x_223;
goto block_222;
}
block_222:
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_217 = lean_obj_once(&l_Lean_Firefox_instFromJsonThread_fromJson___closed__52, &l_Lean_Firefox_instFromJsonThread_fromJson___closed__52_once, _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__52);
x_218 = lean_string_append(x_217, x_214);
lean_dec(x_214);
if (x_216 == 0)
{
lean_ctor_set(x_215, 0, x_218);
x_219 = x_215;
goto block_220;
}
else
{
lean_object* x_221; 
x_221 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_221, 0, x_218);
x_219 = x_221;
goto block_220;
}
block_220:
{
return x_219;
}
}
}
else
{
if (lean_obj_tag(x_213) == 0)
{
lean_object* x_224; lean_object* x_225; uint8_t x_226; uint8_t x_231; 
lean_dec(x_211);
lean_dec(x_190);
lean_dec(x_169);
lean_dec(x_148);
lean_dec(x_127);
lean_dec(x_106);
lean_dec(x_85);
lean_dec(x_64);
lean_dec(x_43);
lean_dec(x_22);
x_224 = lean_ctor_get(x_213, 0);
x_231 = !lean_is_exclusive(x_213);
if (x_231 == 0)
{
x_225 = x_213;
x_226 = x_231;
goto block_230;
}
else
{
lean_inc(x_224);
lean_dec(x_213);
x_225 = lean_box(0);
x_226 = x_231;
goto block_230;
}
block_230:
{
lean_object* x_227; 
if (x_226 == 0)
{
lean_ctor_set_tag(x_225, 0);
x_227 = x_225;
goto block_228;
}
else
{
lean_object* x_229; 
x_229 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_229, 0, x_224);
x_227 = x_229;
goto block_228;
}
block_228:
{
return x_227;
}
}
}
else
{
lean_object* x_232; lean_object* x_233; uint8_t x_234; uint8_t x_241; 
x_232 = lean_ctor_get(x_213, 0);
x_241 = !lean_is_exclusive(x_213);
if (x_241 == 0)
{
x_233 = x_213;
x_234 = x_241;
goto block_240;
}
else
{
lean_inc(x_232);
lean_dec(x_213);
x_233 = lean_box(0);
x_234 = x_241;
goto block_240;
}
block_240:
{
lean_object* x_235; uint8_t x_236; lean_object* x_237; 
x_235 = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(x_235, 0, x_22);
lean_ctor_set(x_235, 1, x_43);
lean_ctor_set(x_235, 2, x_85);
lean_ctor_set(x_235, 3, x_106);
lean_ctor_set(x_235, 4, x_127);
lean_ctor_set(x_235, 5, x_148);
lean_ctor_set(x_235, 6, x_169);
lean_ctor_set(x_235, 7, x_190);
lean_ctor_set(x_235, 8, x_211);
lean_ctor_set(x_235, 9, x_232);
x_236 = lean_unbox(x_64);
lean_dec(x_64);
lean_ctor_set_uint8(x_235, sizeof(void*)*10, x_236);
if (x_234 == 0)
{
lean_ctor_set(x_233, 0, x_235);
x_237 = x_233;
goto block_238;
}
else
{
lean_object* x_239; 
x_239 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_239, 0, x_235);
x_237 = x_239;
goto block_238;
}
block_238:
{
return x_237;
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
}
}
LEAN_EXPORT lean_object* l_Lean_Firefox_instToJsonThread_toJson(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_3);
x_4 = lean_ctor_get_uint8(x_1, sizeof(void*)*10);
x_5 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_1, 4);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_1, 5);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_1, 6);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_1, 7);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_1, 8);
lean_inc_ref(x_11);
x_12 = lean_ctor_get(x_1, 9);
lean_inc_ref(x_12);
lean_dec_ref(x_1);
x_13 = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__0));
x_14 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_14, 0, x_2);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = ((lean_object*)(l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__19));
x_19 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_19, 0, x_3);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_16);
x_22 = ((lean_object*)(l_Lean_Firefox_instFromJsonThread_fromJson___closed__8));
x_23 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_23, 0, x_4);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_16);
x_26 = ((lean_object*)(l_Lean_Firefox_instFromJsonThread_fromJson___closed__13));
x_27 = l_Lean_Firefox_instToJsonSamplesTable_toJson(x_5);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_16);
x_30 = ((lean_object*)(l_Lean_Firefox_instFromJsonThread_fromJson___closed__18));
x_31 = l_Lean_Firefox_instToJsonRawMarkerTable_toJson(x_6);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_16);
x_34 = ((lean_object*)(l_Lean_Firefox_instFromJsonThread_fromJson___closed__23));
x_35 = l_Lean_Firefox_instToJsonStackTable_toJson(x_7);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_16);
x_38 = ((lean_object*)(l_Lean_Firefox_instFromJsonThread_fromJson___closed__28));
x_39 = l_Lean_Firefox_instToJsonFrameTable_toJson(x_8);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_16);
x_42 = ((lean_object*)(l_Lean_Firefox_instFromJsonThread_fromJson___closed__33));
x_43 = l_Lean_Firefox_instToJsonResourceTable_toJson(x_9);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_16);
x_46 = ((lean_object*)(l_Lean_Firefox_instFromJsonThread_fromJson___closed__38));
x_47 = l_Lean_Firefox_instToJsonResourceTable_toJson(x_10);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_16);
x_50 = ((lean_object*)(l_Lean_Firefox_instFromJsonThread_fromJson___closed__43));
x_51 = l_Array_toJson___at___00Lean_Firefox_instToJsonCategory_toJson_spec__0(x_11);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_16);
x_54 = ((lean_object*)(l_Lean_Firefox_instFromJsonThread_fromJson___closed__48));
x_55 = l_Lean_Firefox_instToJsonFuncTable_toJson(x_12);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_16);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_16);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_53);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_49);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_45);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_41);
lean_ctor_set(x_62, 1, x_61);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_37);
lean_ctor_set(x_63, 1, x_62);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_33);
lean_ctor_set(x_64, 1, x_63);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_29);
lean_ctor_set(x_65, 1, x_64);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_25);
lean_ctor_set(x_66, 1, x_65);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_21);
lean_ctor_set(x_67, 1, x_66);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_17);
lean_ctor_set(x_68, 1, x_67);
x_69 = ((lean_object*)(l_Lean_Firefox_instToJsonCategory_toJson___closed__0));
x_70 = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Firefox_instToJsonCategory_toJson_spec__1(x_68, x_69);
x_71 = l_Lean_Json_mkObj(x_70);
return x_71;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfile_fromJson_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l_Lean_Firefox_instFromJsonProfileMeta_fromJson(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfile_fromJson_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfile_fromJson_spec__0(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfile_fromJson_spec__1_spec__1_spec__2(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_7 = l_Lean_Firefox_instFromJsonThread_fromJson(x_6);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfile_fromJson_spec__1_spec__1_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfile_fromJson_spec__1_spec__1_spec__2(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfile_fromJson_spec__1_spec__1(lean_object* x_1) {
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
x_5 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfile_fromJson_spec__1_spec__1_spec__2(x_3, x_4, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__2_spec__2___closed__0));
x_7 = lean_unsigned_to_nat(80u);
x_8 = l_Lean_Json_pretty(x_1, x_7);
x_9 = lean_string_append(x_6, x_8);
lean_dec_ref(x_8);
x_10 = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__2_spec__2___closed__1));
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfile_fromJson_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfile_fromJson_spec__1_spec__1(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfile_fromJson_spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfile_fromJson_spec__1(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonProfile_fromJson___closed__3(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_Firefox_instFromJsonProfile_fromJson___closed__2));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonProfile_fromJson___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__6));
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonProfile_fromJson___closed__3, &l_Lean_Firefox_instFromJsonProfile_fromJson___closed__3_once, _init_l_Lean_Firefox_instFromJsonProfile_fromJson___closed__3);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonProfile_fromJson___closed__6(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_Firefox_instFromJsonProfile_fromJson___closed__5));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonProfile_fromJson___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Firefox_instFromJsonProfile_fromJson___closed__6, &l_Lean_Firefox_instFromJsonProfile_fromJson___closed__6_once, _init_l_Lean_Firefox_instFromJsonProfile_fromJson___closed__6);
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonProfile_fromJson___closed__4, &l_Lean_Firefox_instFromJsonProfile_fromJson___closed__4_once, _init_l_Lean_Firefox_instFromJsonProfile_fromJson___closed__4);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonProfile_fromJson___closed__8(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonProfile_fromJson___closed__7, &l_Lean_Firefox_instFromJsonProfile_fromJson___closed__7_once, _init_l_Lean_Firefox_instFromJsonProfile_fromJson___closed__7);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonProfile_fromJson___closed__11(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_Firefox_instFromJsonProfile_fromJson___closed__10));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonProfile_fromJson___closed__12(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Firefox_instFromJsonProfile_fromJson___closed__11, &l_Lean_Firefox_instFromJsonProfile_fromJson___closed__11_once, _init_l_Lean_Firefox_instFromJsonProfile_fromJson___closed__11);
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonProfile_fromJson___closed__4, &l_Lean_Firefox_instFromJsonProfile_fromJson___closed__4_once, _init_l_Lean_Firefox_instFromJsonProfile_fromJson___closed__4);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonProfile_fromJson___closed__13(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonProfile_fromJson___closed__12, &l_Lean_Firefox_instFromJsonProfile_fromJson___closed__12_once, _init_l_Lean_Firefox_instFromJsonProfile_fromJson___closed__12);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonProfile_fromJson___closed__16(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_Firefox_instFromJsonProfile_fromJson___closed__15));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonProfile_fromJson___closed__17(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Firefox_instFromJsonProfile_fromJson___closed__16, &l_Lean_Firefox_instFromJsonProfile_fromJson___closed__16_once, _init_l_Lean_Firefox_instFromJsonProfile_fromJson___closed__16);
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonProfile_fromJson___closed__4, &l_Lean_Firefox_instFromJsonProfile_fromJson___closed__4_once, _init_l_Lean_Firefox_instFromJsonProfile_fromJson___closed__4);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonProfile_fromJson___closed__18(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
x_2 = lean_obj_once(&l_Lean_Firefox_instFromJsonProfile_fromJson___closed__17, &l_Lean_Firefox_instFromJsonProfile_fromJson___closed__17_once, _init_l_Lean_Firefox_instFromJsonProfile_fromJson___closed__17);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Firefox_instFromJsonProfile_fromJson(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = ((lean_object*)(l_Lean_Firefox_instFromJsonProfile_fromJson___closed__0));
lean_inc(x_1);
x_3 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfile_fromJson_spec__0(x_1, x_2);
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
x_7 = lean_obj_once(&l_Lean_Firefox_instFromJsonProfile_fromJson___closed__8, &l_Lean_Firefox_instFromJsonProfile_fromJson___closed__8_once, _init_l_Lean_Firefox_instFromJsonProfile_fromJson___closed__8);
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
x_23 = ((lean_object*)(l_Lean_Firefox_instFromJsonProfile_fromJson___closed__9));
lean_inc(x_1);
x_24 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__3(x_1, x_23);
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
x_28 = lean_obj_once(&l_Lean_Firefox_instFromJsonProfile_fromJson___closed__13, &l_Lean_Firefox_instFromJsonProfile_fromJson___closed__13_once, _init_l_Lean_Firefox_instFromJsonProfile_fromJson___closed__13);
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
x_44 = ((lean_object*)(l_Lean_Firefox_instFromJsonProfile_fromJson___closed__14));
x_45 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfile_fromJson_spec__1(x_1, x_44);
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
x_49 = lean_obj_once(&l_Lean_Firefox_instFromJsonProfile_fromJson___closed__18, &l_Lean_Firefox_instFromJsonProfile_fromJson___closed__18_once, _init_l_Lean_Firefox_instFromJsonProfile_fromJson___closed__18);
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
lean_object* x_64; lean_object* x_65; uint8_t x_66; uint8_t x_72; 
x_64 = lean_ctor_get(x_45, 0);
x_72 = !lean_is_exclusive(x_45);
if (x_72 == 0)
{
x_65 = x_45;
x_66 = x_72;
goto block_71;
}
else
{
lean_inc(x_64);
lean_dec(x_45);
x_65 = lean_box(0);
x_66 = x_72;
goto block_71;
}
block_71:
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_67, 0, x_22);
lean_ctor_set(x_67, 1, x_43);
lean_ctor_set(x_67, 2, x_64);
if (x_66 == 0)
{
lean_ctor_set(x_65, 0, x_67);
x_68 = x_65;
goto block_69;
}
else
{
lean_object* x_70; 
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_67);
x_68 = x_70;
goto block_69;
}
block_69:
{
return x_68;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Firefox_instToJsonProfile_toJson_spec__0_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_8 = l_Lean_Firefox_instToJsonThread_toJson(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Firefox_instToJsonProfile_toJson_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Firefox_instToJsonProfile_toJson_spec__0_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Firefox_instToJsonProfile_toJson_spec__0(lean_object* x_1) {
_start:
{
size_t x_2; size_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_array_size(x_1);
x_3 = 0;
x_4 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Firefox_instToJsonProfile_toJson_spec__0_spec__0(x_2, x_3, x_1);
x_5 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Firefox_instToJsonProfile_toJson(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_4);
lean_dec_ref(x_1);
x_5 = ((lean_object*)(l_Lean_Firefox_instFromJsonProfile_fromJson___closed__0));
x_6 = l_Lean_Firefox_instToJsonProfileMeta_toJson(x_2);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = ((lean_object*)(l_Lean_Firefox_instFromJsonProfile_fromJson___closed__9));
x_11 = l_Array_toJson___at___00Lean_Firefox_instToJsonProfileMeta_toJson_spec__1(x_3);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_8);
x_14 = ((lean_object*)(l_Lean_Firefox_instFromJsonProfile_fromJson___closed__14));
x_15 = l_Array_toJson___at___00Lean_Firefox_instToJsonProfile_toJson_spec__0(x_4);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_8);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_8);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_9);
lean_ctor_set(x_20, 1, x_19);
x_21 = ((lean_object*)(l_Lean_Firefox_instToJsonCategory_toJson___closed__0));
x_22 = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Firefox_instToJsonCategory_toJson_spec__1(x_20, x_21);
x_23 = l_Lean_Json_mkObj(x_22);
return x_23;
}
}
static double _init_l___private_Lean_Util_Profiler_0__Lean_Firefox_getFirstStart_x3f___closed__0(void) {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Profiler_0__Lean_Firefox_getFirstStart_x3f(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 9:
{
lean_object* x_2; lean_object* x_3; double x_4; double x_5; uint8_t x_6; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 2);
x_4 = lean_ctor_get_float(x_2, sizeof(void*)*2);
x_5 = lean_float_once(&l___private_Lean_Util_Profiler_0__Lean_Firefox_getFirstStart_x3f___closed__0, &l___private_Lean_Util_Profiler_0__Lean_Firefox_getFirstStart_x3f___closed__0_once, _init_l___private_Lean_Util_Profiler_0__Lean_Firefox_getFirstStart_x3f___closed__0);
x_6 = lean_float_beq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box_float(x_4);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_box(0);
x_10 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_getFirstStart_x3f_spec__0___closed__0));
x_11 = lean_array_size(x_3);
x_12 = 0;
x_13 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_getFirstStart_x3f_spec__0(x_3, x_11, x_12, x_10);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
if (lean_obj_tag(x_14) == 0)
{
return x_9;
}
else
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
if (lean_obj_tag(x_15) == 1)
{
return x_15;
}
else
{
lean_dec(x_15);
return x_9;
}
}
}
}
case 3:
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_1, 1);
x_1 = x_16;
goto _start;
}
default: 
{
lean_object* x_18; 
x_18 = lean_box(0);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_getFirstStart_x3f_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec_ref(x_4);
x_6 = lean_box(0);
x_7 = lean_array_uget_borrowed(x_1, x_3);
x_8 = l___private_Lean_Util_Profiler_0__Lean_Firefox_getFirstStart_x3f(x_7);
if (lean_obj_tag(x_8) == 1)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
return x_10;
}
else
{
lean_object* x_11; size_t x_12; size_t x_13; 
lean_dec(x_8);
x_11 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_getFirstStart_x3f_spec__0___closed__0));
x_12 = 1;
x_13 = lean_usize_add(x_3, x_12);
x_3 = x_13;
x_4 = x_11;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_getFirstStart_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_getFirstStart_x3f_spec__0(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Profiler_0__Lean_Firefox_getFirstStart_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Util_Profiler_0__Lean_Firefox_getFirstStart_x3f(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = l_Lean_Name_isPrefixOf(x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go___lam__0(x_1, x_2);
lean_dec_ref(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__3_spec__7___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_nat_dec_eq(x_4, x_1);
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_9; 
lean_inc(x_5);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_5);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__3_spec__7___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__3_spec__7___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__3___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = lean_uint64_of_nat(x_2);
x_6 = 32;
x_7 = lean_uint64_shift_right(x_5, x_6);
x_8 = lean_uint64_xor(x_5, x_7);
x_9 = 16;
x_10 = lean_uint64_shift_right(x_8, x_9);
x_11 = lean_uint64_xor(x_8, x_10);
x_12 = lean_uint64_to_usize(x_11);
x_13 = lean_usize_of_nat(x_4);
x_14 = 1;
x_15 = lean_usize_sub(x_13, x_14);
x_16 = lean_usize_land(x_12, x_15);
x_17 = lean_array_uget_borrowed(x_3, x_16);
x_18 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__3_spec__7___redArg(x_2, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__3___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__1_spec__1_spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_nat_dec_eq(x_6, x_7);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__1_spec__1_spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__1_spec__1_spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__2_spec__5___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_25; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_3, 2);
x_25 = !lean_is_exclusive(x_3);
if (x_25 == 0)
{
x_7 = x_3;
x_8 = x_25;
goto block_24;
}
else
{
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_3);
x_7 = lean_box(0);
x_8 = x_25;
goto block_24;
}
block_24:
{
uint8_t x_9; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_4, 0);
x_19 = lean_ctor_get(x_4, 1);
x_20 = lean_ctor_get(x_1, 0);
x_21 = lean_ctor_get(x_1, 1);
x_22 = lean_nat_dec_eq(x_18, x_20);
if (x_22 == 0)
{
x_9 = x_22;
goto block_17;
}
else
{
uint8_t x_23; 
x_23 = l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__1_spec__1_spec__2(x_19, x_21);
x_9 = x_23;
goto block_17;
}
block_17:
{
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__2_spec__5___redArg(x_1, x_2, x_6);
if (x_8 == 0)
{
lean_ctor_set(x_7, 2, x_10);
x_11 = x_7;
goto block_12;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_5);
lean_ctor_set(x_13, 2, x_10);
x_11 = x_13;
goto block_12;
}
block_12:
{
return x_11;
}
}
else
{
lean_object* x_14; 
lean_dec(x_5);
lean_dec(x_4);
if (x_8 == 0)
{
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 0, x_1);
x_14 = x_7;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_2);
lean_ctor_set(x_16, 2, x_6);
x_14 = x_16;
goto block_15;
}
block_15:
{
return x_14;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__2_spec__4_spec__6_spec__11___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_38; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
x_38 = !lean_is_exclusive(x_2);
if (x_38 == 0)
{
x_6 = x_2;
x_7 = x_38;
goto block_37;
}
else
{
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_2);
x_6 = lean_box(0);
x_7 = x_38;
goto block_37;
}
block_37:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint64_t x_11; uint64_t x_12; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_ctor_get(x_3, 1);
x_10 = lean_array_get_size(x_1);
x_11 = lean_uint64_of_nat(x_8);
if (lean_obj_tag(x_9) == 0)
{
uint64_t x_32; 
x_32 = 11;
x_12 = x_32;
goto block_31;
}
else
{
lean_object* x_33; uint64_t x_34; uint64_t x_35; uint64_t x_36; 
x_33 = lean_ctor_get(x_9, 0);
x_34 = lean_uint64_of_nat(x_33);
x_35 = 13;
x_36 = lean_uint64_mix_hash(x_34, x_35);
x_12 = x_36;
goto block_31;
}
block_31:
{
uint64_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; size_t x_20; size_t x_21; size_t x_22; size_t x_23; size_t x_24; lean_object* x_25; lean_object* x_26; 
x_13 = lean_uint64_mix_hash(x_11, x_12);
x_14 = 32;
x_15 = lean_uint64_shift_right(x_13, x_14);
x_16 = lean_uint64_xor(x_13, x_15);
x_17 = 16;
x_18 = lean_uint64_shift_right(x_16, x_17);
x_19 = lean_uint64_xor(x_16, x_18);
x_20 = lean_uint64_to_usize(x_19);
x_21 = lean_usize_of_nat(x_10);
x_22 = 1;
x_23 = lean_usize_sub(x_21, x_22);
x_24 = lean_usize_land(x_20, x_23);
x_25 = lean_array_uget_borrowed(x_1, x_24);
lean_inc(x_25);
if (x_7 == 0)
{
lean_ctor_set(x_6, 2, x_25);
x_26 = x_6;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_30, 0, x_3);
lean_ctor_set(x_30, 1, x_4);
lean_ctor_set(x_30, 2, x_25);
x_26 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_27; 
x_27 = lean_array_uset(x_1, x_24, x_26);
x_1 = x_27;
x_2 = x_5;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__2_spec__4_spec__6___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
if (x_5 == 0)
{
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__2_spec__4_spec__6_spec__11___redArg(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__2_spec__4___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_2, x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_4, x_6);
x_8 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__2_spec__4_spec__6___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__2_spec__3___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get(x_4, 1);
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
x_13 = lean_nat_dec_eq(x_9, x_11);
if (x_13 == 0)
{
x_6 = x_13;
goto block_8;
}
else
{
uint8_t x_14; 
x_14 = l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__1_spec__1_spec__2(x_10, x_12);
x_6 = x_14;
goto block_8;
}
block_8:
{
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
return x_6;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__2_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__2_spec__3___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_58; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_58 = !lean_is_exclusive(x_1);
if (x_58 == 0)
{
x_6 = x_1;
x_7 = x_58;
goto block_57;
}
else
{
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = x_58;
goto block_57;
}
block_57:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint64_t x_11; uint64_t x_12; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
x_10 = lean_array_get_size(x_5);
x_11 = lean_uint64_of_nat(x_8);
if (lean_obj_tag(x_9) == 0)
{
uint64_t x_52; 
x_52 = 11;
x_12 = x_52;
goto block_51;
}
else
{
lean_object* x_53; uint64_t x_54; uint64_t x_55; uint64_t x_56; 
x_53 = lean_ctor_get(x_9, 0);
x_54 = lean_uint64_of_nat(x_53);
x_55 = 13;
x_56 = lean_uint64_mix_hash(x_54, x_55);
x_12 = x_56;
goto block_51;
}
block_51:
{
uint64_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; size_t x_20; size_t x_21; size_t x_22; size_t x_23; size_t x_24; lean_object* x_25; uint8_t x_26; 
x_13 = lean_uint64_mix_hash(x_11, x_12);
x_14 = 32;
x_15 = lean_uint64_shift_right(x_13, x_14);
x_16 = lean_uint64_xor(x_13, x_15);
x_17 = 16;
x_18 = lean_uint64_shift_right(x_16, x_17);
x_19 = lean_uint64_xor(x_16, x_18);
x_20 = lean_uint64_to_usize(x_19);
x_21 = lean_usize_of_nat(x_10);
x_22 = 1;
x_23 = lean_usize_sub(x_21, x_22);
x_24 = lean_usize_land(x_20, x_23);
x_25 = lean_array_uget_borrowed(x_5, x_24);
x_26 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__2_spec__3___redArg(x_2, x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_4, x_27);
lean_dec(x_4);
lean_inc(x_25);
x_29 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_29, 0, x_2);
lean_ctor_set(x_29, 1, x_3);
lean_ctor_set(x_29, 2, x_25);
x_30 = lean_array_uset(x_5, x_24, x_29);
x_31 = lean_unsigned_to_nat(4u);
x_32 = lean_nat_mul(x_28, x_31);
x_33 = lean_unsigned_to_nat(3u);
x_34 = lean_nat_div(x_32, x_33);
lean_dec(x_32);
x_35 = lean_array_get_size(x_30);
x_36 = lean_nat_dec_le(x_34, x_35);
lean_dec(x_34);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__2_spec__4___redArg(x_30);
if (x_7 == 0)
{
lean_ctor_set(x_6, 1, x_37);
lean_ctor_set(x_6, 0, x_28);
x_38 = x_6;
goto block_39;
}
else
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_28);
lean_ctor_set(x_40, 1, x_37);
x_38 = x_40;
goto block_39;
}
block_39:
{
return x_38;
}
}
else
{
lean_object* x_41; 
if (x_7 == 0)
{
lean_ctor_set(x_6, 1, x_30);
lean_ctor_set(x_6, 0, x_28);
x_41 = x_6;
goto block_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_28);
lean_ctor_set(x_43, 1, x_30);
x_41 = x_43;
goto block_42;
}
block_42:
{
return x_41;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_inc(x_25);
x_44 = lean_box(0);
x_45 = lean_array_uset(x_5, x_24, x_44);
x_46 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__2_spec__5___redArg(x_2, x_3, x_25);
x_47 = lean_array_uset(x_45, x_24, x_46);
if (x_7 == 0)
{
lean_ctor_set(x_6, 1, x_47);
x_48 = x_6;
goto block_49;
}
else
{
lean_object* x_50; 
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_4);
lean_ctor_set(x_50, 1, x_47);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__6_spec__16_spec__20_spec__23___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_28; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
x_28 = !lean_is_exclusive(x_2);
if (x_28 == 0)
{
x_6 = x_2;
x_7 = x_28;
goto block_27;
}
else
{
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_2);
x_6 = lean_box(0);
x_7 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; 
x_8 = lean_array_get_size(x_1);
x_9 = lean_string_hash(x_3);
x_10 = 32;
x_11 = lean_uint64_shift_right(x_9, x_10);
x_12 = lean_uint64_xor(x_9, x_11);
x_13 = 16;
x_14 = lean_uint64_shift_right(x_12, x_13);
x_15 = lean_uint64_xor(x_12, x_14);
x_16 = lean_uint64_to_usize(x_15);
x_17 = lean_usize_of_nat(x_8);
x_18 = 1;
x_19 = lean_usize_sub(x_17, x_18);
x_20 = lean_usize_land(x_16, x_19);
x_21 = lean_array_uget_borrowed(x_1, x_20);
lean_inc(x_21);
if (x_7 == 0)
{
lean_ctor_set(x_6, 2, x_21);
x_22 = x_6;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_26, 0, x_3);
lean_ctor_set(x_26, 1, x_4);
lean_ctor_set(x_26, 2, x_21);
x_22 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_23; 
x_23 = lean_array_uset(x_1, x_20, x_22);
x_1 = x_23;
x_2 = x_5;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__6_spec__16_spec__20___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
if (x_5 == 0)
{
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__6_spec__16_spec__20_spec__23___redArg(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__6_spec__16___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_2, x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_4, x_6);
x_8 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__6_spec__16_spec__20___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__6_spec__17___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_18; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_3, 2);
x_18 = !lean_is_exclusive(x_3);
if (x_18 == 0)
{
x_7 = x_3;
x_8 = x_18;
goto block_17;
}
else
{
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_3);
x_7 = lean_box(0);
x_8 = x_18;
goto block_17;
}
block_17:
{
uint8_t x_9; 
x_9 = lean_string_dec_eq(x_4, x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__6_spec__17___redArg(x_1, x_2, x_6);
if (x_8 == 0)
{
lean_ctor_set(x_7, 2, x_10);
x_11 = x_7;
goto block_12;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_5);
lean_ctor_set(x_13, 2, x_10);
x_11 = x_13;
goto block_12;
}
block_12:
{
return x_11;
}
}
else
{
lean_object* x_14; 
lean_dec(x_5);
lean_dec(x_4);
if (x_8 == 0)
{
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 0, x_1);
x_14 = x_7;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_2);
lean_ctor_set(x_16, 2, x_6);
x_14 = x_16;
goto block_15;
}
block_15:
{
return x_14;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__6_spec__15___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_string_dec_eq(x_4, x_1);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__6_spec__15___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__6_spec__15___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__6___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_48; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_48 = !lean_is_exclusive(x_1);
if (x_48 == 0)
{
x_6 = x_1;
x_7 = x_48;
goto block_47;
}
else
{
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; size_t x_20; lean_object* x_21; uint8_t x_22; 
x_8 = lean_array_get_size(x_5);
x_9 = lean_string_hash(x_2);
x_10 = 32;
x_11 = lean_uint64_shift_right(x_9, x_10);
x_12 = lean_uint64_xor(x_9, x_11);
x_13 = 16;
x_14 = lean_uint64_shift_right(x_12, x_13);
x_15 = lean_uint64_xor(x_12, x_14);
x_16 = lean_uint64_to_usize(x_15);
x_17 = lean_usize_of_nat(x_8);
x_18 = 1;
x_19 = lean_usize_sub(x_17, x_18);
x_20 = lean_usize_land(x_16, x_19);
x_21 = lean_array_uget_borrowed(x_5, x_20);
x_22 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__6_spec__15___redArg(x_2, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_4, x_23);
lean_dec(x_4);
lean_inc(x_21);
x_25 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_25, 0, x_2);
lean_ctor_set(x_25, 1, x_3);
lean_ctor_set(x_25, 2, x_21);
x_26 = lean_array_uset(x_5, x_20, x_25);
x_27 = lean_unsigned_to_nat(4u);
x_28 = lean_nat_mul(x_24, x_27);
x_29 = lean_unsigned_to_nat(3u);
x_30 = lean_nat_div(x_28, x_29);
lean_dec(x_28);
x_31 = lean_array_get_size(x_26);
x_32 = lean_nat_dec_le(x_30, x_31);
lean_dec(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__6_spec__16___redArg(x_26);
if (x_7 == 0)
{
lean_ctor_set(x_6, 1, x_33);
lean_ctor_set(x_6, 0, x_24);
x_34 = x_6;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_24);
lean_ctor_set(x_36, 1, x_33);
x_34 = x_36;
goto block_35;
}
block_35:
{
return x_34;
}
}
else
{
lean_object* x_37; 
if (x_7 == 0)
{
lean_ctor_set(x_6, 1, x_26);
lean_ctor_set(x_6, 0, x_24);
x_37 = x_6;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_24);
lean_ctor_set(x_39, 1, x_26);
x_37 = x_39;
goto block_38;
}
block_38:
{
return x_37;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_inc(x_21);
x_40 = lean_box(0);
x_41 = lean_array_uset(x_5, x_20, x_40);
x_42 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__6_spec__17___redArg(x_2, x_3, x_21);
x_43 = lean_array_uset(x_41, x_20, x_42);
if (x_7 == 0)
{
lean_ctor_set(x_6, 1, x_43);
x_44 = x_6;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_4);
lean_ctor_set(x_46, 1, x_43);
x_44 = x_46;
goto block_45;
}
block_45:
{
return x_44;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_11 = lean_ctor_get(x_4, 0);
x_12 = lean_ctor_get(x_4, 1);
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
x_15 = lean_nat_dec_eq(x_11, x_13);
if (x_15 == 0)
{
x_7 = x_15;
goto block_10;
}
else
{
uint8_t x_16; 
x_16 = l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__1_spec__1_spec__2(x_12, x_14);
x_7 = x_16;
goto block_10;
}
block_10:
{
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_9; 
lean_inc(x_5);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_5);
return x_9;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__1_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__1_spec__1___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; uint64_t x_8; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_array_get_size(x_3);
x_7 = lean_uint64_of_nat(x_4);
if (lean_obj_tag(x_5) == 0)
{
uint64_t x_24; 
x_24 = 11;
x_8 = x_24;
goto block_23;
}
else
{
lean_object* x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; 
x_25 = lean_ctor_get(x_5, 0);
x_26 = lean_uint64_of_nat(x_25);
x_27 = 13;
x_28 = lean_uint64_mix_hash(x_26, x_27);
x_8 = x_28;
goto block_23;
}
block_23:
{
uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; 
x_9 = lean_uint64_mix_hash(x_7, x_8);
x_10 = 32;
x_11 = lean_uint64_shift_right(x_9, x_10);
x_12 = lean_uint64_xor(x_9, x_11);
x_13 = 16;
x_14 = lean_uint64_shift_right(x_12, x_13);
x_15 = lean_uint64_xor(x_12, x_14);
x_16 = lean_uint64_to_usize(x_15);
x_17 = lean_usize_of_nat(x_6);
x_18 = 1;
x_19 = lean_usize_sub(x_17, x_18);
x_20 = lean_usize_land(x_16, x_19);
x_21 = lean_array_uget_borrowed(x_3, x_20);
x_22 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__1_spec__1___redArg(x_2, x_21);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__1___redArg(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__5_spec__13___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_string_dec_eq(x_4, x_1);
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_9; 
lean_inc(x_5);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_5);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__5_spec__13___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__5_spec__13___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__5___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = lean_string_hash(x_2);
x_6 = 32;
x_7 = lean_uint64_shift_right(x_5, x_6);
x_8 = lean_uint64_xor(x_5, x_7);
x_9 = 16;
x_10 = lean_uint64_shift_right(x_8, x_9);
x_11 = lean_uint64_xor(x_8, x_10);
x_12 = lean_uint64_to_usize(x_11);
x_13 = lean_usize_of_nat(x_4);
x_14 = 1;
x_15 = lean_usize_sub(x_13, x_14);
x_16 = lean_usize_land(x_12, x_15);
x_17 = lean_array_uget_borrowed(x_3, x_16);
x_18 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__5_spec__13___redArg(x_2, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__5___redArg(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__4_spec__10_spec__13_spec__17___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_28; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
x_28 = !lean_is_exclusive(x_2);
if (x_28 == 0)
{
x_6 = x_2;
x_7 = x_28;
goto block_27;
}
else
{
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_2);
x_6 = lean_box(0);
x_7 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; 
x_8 = lean_array_get_size(x_1);
x_9 = lean_uint64_of_nat(x_3);
x_10 = 32;
x_11 = lean_uint64_shift_right(x_9, x_10);
x_12 = lean_uint64_xor(x_9, x_11);
x_13 = 16;
x_14 = lean_uint64_shift_right(x_12, x_13);
x_15 = lean_uint64_xor(x_12, x_14);
x_16 = lean_uint64_to_usize(x_15);
x_17 = lean_usize_of_nat(x_8);
x_18 = 1;
x_19 = lean_usize_sub(x_17, x_18);
x_20 = lean_usize_land(x_16, x_19);
x_21 = lean_array_uget_borrowed(x_1, x_20);
lean_inc(x_21);
if (x_7 == 0)
{
lean_ctor_set(x_6, 2, x_21);
x_22 = x_6;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_26, 0, x_3);
lean_ctor_set(x_26, 1, x_4);
lean_ctor_set(x_26, 2, x_21);
x_22 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_23; 
x_23 = lean_array_uset(x_1, x_20, x_22);
x_1 = x_23;
x_2 = x_5;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__4_spec__10_spec__13___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
if (x_5 == 0)
{
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__4_spec__10_spec__13_spec__17___redArg(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__4_spec__10___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_2, x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_4, x_6);
x_8 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__4_spec__10_spec__13___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__4_spec__9___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_nat_dec_eq(x_4, x_1);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__4_spec__9___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__4_spec__9___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__4_spec__11___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_18; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_3, 2);
x_18 = !lean_is_exclusive(x_3);
if (x_18 == 0)
{
x_7 = x_3;
x_8 = x_18;
goto block_17;
}
else
{
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_3);
x_7 = lean_box(0);
x_8 = x_18;
goto block_17;
}
block_17:
{
uint8_t x_9; 
x_9 = lean_nat_dec_eq(x_4, x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__4_spec__11___redArg(x_1, x_2, x_6);
if (x_8 == 0)
{
lean_ctor_set(x_7, 2, x_10);
x_11 = x_7;
goto block_12;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_5);
lean_ctor_set(x_13, 2, x_10);
x_11 = x_13;
goto block_12;
}
block_12:
{
return x_11;
}
}
else
{
lean_object* x_14; 
lean_dec(x_5);
lean_dec(x_4);
if (x_8 == 0)
{
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 0, x_1);
x_14 = x_7;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_2);
lean_ctor_set(x_16, 2, x_6);
x_14 = x_16;
goto block_15;
}
block_15:
{
return x_14;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_48; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_48 = !lean_is_exclusive(x_1);
if (x_48 == 0)
{
x_6 = x_1;
x_7 = x_48;
goto block_47;
}
else
{
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; size_t x_20; lean_object* x_21; uint8_t x_22; 
x_8 = lean_array_get_size(x_5);
x_9 = lean_uint64_of_nat(x_2);
x_10 = 32;
x_11 = lean_uint64_shift_right(x_9, x_10);
x_12 = lean_uint64_xor(x_9, x_11);
x_13 = 16;
x_14 = lean_uint64_shift_right(x_12, x_13);
x_15 = lean_uint64_xor(x_12, x_14);
x_16 = lean_uint64_to_usize(x_15);
x_17 = lean_usize_of_nat(x_8);
x_18 = 1;
x_19 = lean_usize_sub(x_17, x_18);
x_20 = lean_usize_land(x_16, x_19);
x_21 = lean_array_uget_borrowed(x_5, x_20);
x_22 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__4_spec__9___redArg(x_2, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_4, x_23);
lean_dec(x_4);
lean_inc(x_21);
x_25 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_25, 0, x_2);
lean_ctor_set(x_25, 1, x_3);
lean_ctor_set(x_25, 2, x_21);
x_26 = lean_array_uset(x_5, x_20, x_25);
x_27 = lean_unsigned_to_nat(4u);
x_28 = lean_nat_mul(x_24, x_27);
x_29 = lean_unsigned_to_nat(3u);
x_30 = lean_nat_div(x_28, x_29);
lean_dec(x_28);
x_31 = lean_array_get_size(x_26);
x_32 = lean_nat_dec_le(x_30, x_31);
lean_dec(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__4_spec__10___redArg(x_26);
if (x_7 == 0)
{
lean_ctor_set(x_6, 1, x_33);
lean_ctor_set(x_6, 0, x_24);
x_34 = x_6;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_24);
lean_ctor_set(x_36, 1, x_33);
x_34 = x_36;
goto block_35;
}
block_35:
{
return x_34;
}
}
else
{
lean_object* x_37; 
if (x_7 == 0)
{
lean_ctor_set(x_6, 1, x_26);
lean_ctor_set(x_6, 0, x_24);
x_37 = x_6;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_24);
lean_ctor_set(x_39, 1, x_26);
x_37 = x_39;
goto block_38;
}
block_38:
{
return x_37;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_inc(x_21);
x_40 = lean_box(0);
x_41 = lean_array_uset(x_5, x_20, x_40);
x_42 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__4_spec__11___redArg(x_2, x_3, x_21);
x_43 = lean_array_uset(x_41, x_20, x_42);
if (x_7 == 0)
{
lean_ctor_set(x_6, 1, x_43);
x_44 = x_6;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_4);
lean_ctor_set(x_46, 1, x_43);
x_44 = x_46;
goto block_45;
}
block_45:
{
return x_44;
}
}
}
}
}
static double _init_l___private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go___closed__0(void) {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; double x_4; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = 1;
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Float_ofScientific(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go___boxed__const__1(void) {
_start:
{
double x_1; lean_object* x_2; 
x_1 = lean_float_once(&l___private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go___closed__0, &l___private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go___closed__0_once, _init_l___private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go___closed__0);
x_2 = lean_box_float(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l___private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go___closed__1, &l___private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go___closed__1_once, _init_l___private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go___closed__1);
x_2 = lean_int_neg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (lean_obj_tag(x_4)) {
case 9:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; double x_11; double x_12; lean_object* x_13; lean_object* x_14; double x_15; uint8_t x_16; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_4, 1);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_9);
lean_dec_ref(x_4);
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
x_11 = lean_ctor_get_float(x_7, sizeof(void*)*2);
x_12 = lean_ctor_get_float(x_7, sizeof(void*)*2 + 8);
x_13 = lean_ctor_get(x_7, 1);
lean_inc_ref(x_13);
lean_dec_ref(x_7);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_float_once(&l___private_Lean_Util_Profiler_0__Lean_Firefox_getFirstStart_x3f___closed__0, &l___private_Lean_Util_Profiler_0__Lean_Firefox_getFirstStart_x3f___closed__0_once, _init_l___private_Lean_Util_Profiler_0__Lean_Firefox_getFirstStart_x3f___closed__0);
x_16 = lean_float_beq(x_11, x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; double x_123; lean_object* x_124; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_288; lean_object* x_293; uint8_t x_294; 
lean_inc(x_10);
x_17 = lean_alloc_closure((void*)(l___private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go___lam__0___boxed), 2, 1);
lean_closure_set(x_17, 0, x_10);
x_18 = 1;
x_288 = l_Lean_Name_toString(x_10, x_18);
x_293 = lean_string_utf8_byte_size(x_13);
x_294 = lean_nat_dec_eq(x_293, x_14);
if (x_294 == 0)
{
goto block_292;
}
else
{
if (x_16 == 0)
{
lean_dec_ref(x_13);
x_278 = x_288;
x_279 = x_5;
x_280 = lean_box(0);
goto block_287;
}
else
{
goto block_292;
}
}
block_116:
{
lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; lean_object* x_29; 
x_25 = lean_alloc_ctor(0, 4, 8);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_25, 1, x_21);
lean_ctor_set(x_25, 2, x_22);
lean_ctor_set(x_25, 3, x_23);
lean_ctor_set_float(x_25, sizeof(void*)*4, x_11);
x_26 = lean_box(0);
x_27 = lean_array_size(x_9);
x_28 = 0;
lean_inc(x_19);
x_29 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__0(x_19, x_1, x_3, x_9, x_27, x_28, x_26, x_25);
lean_dec_ref(x_9);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_115; 
x_30 = lean_ctor_get(x_29, 0);
x_115 = !lean_is_exclusive(x_29);
if (x_115 == 0)
{
x_31 = x_29;
x_32 = x_115;
goto block_114;
}
else
{
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_box(0);
x_32 = x_115;
goto block_114;
}
block_114:
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_112; 
x_33 = lean_ctor_get(x_30, 1);
x_112 = !lean_is_exclusive(x_30);
if (x_112 == 0)
{
lean_object* x_113; 
x_113 = lean_ctor_get(x_30, 0);
lean_dec(x_113);
x_34 = x_30;
x_35 = x_112;
goto block_111;
}
else
{
lean_inc(x_33);
lean_dec(x_30);
x_34 = lean_box(0);
x_35 = x_112;
goto block_111;
}
block_111:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; double x_41; lean_object* x_42; uint8_t x_43; uint8_t x_109; 
x_36 = lean_ctor_get(x_33, 0);
lean_inc_ref(x_36);
x_37 = lean_ctor_get(x_36, 2);
lean_inc_ref(x_37);
x_38 = lean_ctor_get(x_33, 1);
x_39 = lean_ctor_get(x_33, 2);
x_40 = lean_ctor_get(x_33, 3);
x_41 = lean_ctor_get_float(x_33, sizeof(void*)*4);
x_109 = !lean_is_exclusive(x_33);
if (x_109 == 0)
{
lean_object* x_110; 
x_110 = lean_ctor_get(x_33, 0);
lean_dec(x_110);
x_42 = x_33;
x_43 = x_109;
goto block_108;
}
else
{
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_33);
x_42 = lean_box(0);
x_43 = x_109;
goto block_108;
}
block_108:
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; uint8_t x_106; 
x_44 = lean_ctor_get(x_36, 0);
x_45 = lean_ctor_get(x_36, 1);
x_46 = lean_ctor_get_uint8(x_36, sizeof(void*)*10);
x_47 = lean_ctor_get(x_36, 3);
x_48 = lean_ctor_get(x_36, 4);
x_49 = lean_ctor_get(x_36, 5);
x_50 = lean_ctor_get(x_36, 6);
x_51 = lean_ctor_get(x_36, 7);
x_52 = lean_ctor_get(x_36, 8);
x_53 = lean_ctor_get(x_36, 9);
x_106 = !lean_is_exclusive(x_36);
if (x_106 == 0)
{
lean_object* x_107; 
x_107 = lean_ctor_get(x_36, 2);
lean_dec(x_107);
x_54 = x_36;
x_55 = x_106;
goto block_105;
}
else
{
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_36);
x_54 = lean_box(0);
x_55 = x_106;
goto block_105;
}
block_105:
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; uint8_t x_103; 
x_56 = lean_ctor_get(x_37, 0);
x_57 = lean_ctor_get(x_37, 1);
x_58 = lean_ctor_get(x_37, 2);
x_59 = lean_ctor_get(x_37, 4);
x_60 = lean_ctor_get(x_37, 5);
x_103 = !lean_is_exclusive(x_37);
if (x_103 == 0)
{
lean_object* x_104; 
x_104 = lean_ctor_get(x_37, 3);
lean_dec(x_104);
x_61 = x_37;
x_62 = x_103;
goto block_102;
}
else
{
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_37);
x_61 = lean_box(0);
x_62 = x_103;
goto block_102;
}
block_102:
{
lean_object* x_63; lean_object* x_64; double x_65; double x_66; lean_object* x_67; lean_object* x_68; double x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; double x_74; double x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; double x_81; double x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_inc(x_19);
x_63 = lean_array_push(x_56, x_19);
x_64 = lean_array_push(x_63, x_19);
x_65 = lean_float_once(&l_Lean_Firefox_instCoeFloatMilliseconds___lam__0___closed__0, &l_Lean_Firefox_instCoeFloatMilliseconds___lam__0___closed__0_once, _init_l_Lean_Firefox_instCoeFloatMilliseconds___lam__0___closed__0);
x_66 = lean_float_mul(x_41, x_65);
x_67 = lean_box_float(x_66);
x_68 = lean_array_push(x_57, x_67);
x_69 = lean_float_mul(x_12, x_65);
x_70 = lean_box_float(x_69);
x_71 = lean_array_push(x_68, x_70);
x_72 = l___private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go___boxed__const__1;
x_73 = lean_array_push(x_58, x_72);
x_74 = lean_float_sub(x_12, x_41);
x_75 = lean_float_mul(x_74, x_65);
x_76 = lean_box_float(x_75);
x_77 = lean_array_push(x_73, x_76);
x_78 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__0___closed__0));
x_79 = l___private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go___boxed__const__1;
x_80 = lean_array_push(x_59, x_79);
x_81 = lean_float_once(&l_Lean_Firefox_instCoeFloatMicroseconds___lam__0___closed__0, &l_Lean_Firefox_instCoeFloatMicroseconds___lam__0___closed__0_once, _init_l_Lean_Firefox_instCoeFloatMicroseconds___lam__0___closed__0);
x_82 = lean_float_mul(x_74, x_81);
x_83 = lean_box_float(x_82);
x_84 = lean_array_push(x_80, x_83);
x_85 = lean_unsigned_to_nat(2u);
x_86 = lean_nat_add(x_60, x_85);
lean_dec(x_60);
if (x_62 == 0)
{
lean_ctor_set(x_61, 5, x_86);
lean_ctor_set(x_61, 4, x_84);
lean_ctor_set(x_61, 3, x_78);
lean_ctor_set(x_61, 2, x_77);
lean_ctor_set(x_61, 1, x_71);
lean_ctor_set(x_61, 0, x_64);
x_87 = x_61;
goto block_100;
}
else
{
lean_object* x_101; 
x_101 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_101, 0, x_64);
lean_ctor_set(x_101, 1, x_71);
lean_ctor_set(x_101, 2, x_77);
lean_ctor_set(x_101, 3, x_78);
lean_ctor_set(x_101, 4, x_84);
lean_ctor_set(x_101, 5, x_86);
x_87 = x_101;
goto block_100;
}
block_100:
{
lean_object* x_88; 
if (x_55 == 0)
{
lean_ctor_set(x_54, 2, x_87);
x_88 = x_54;
goto block_98;
}
else
{
lean_object* x_99; 
x_99 = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(x_99, 0, x_44);
lean_ctor_set(x_99, 1, x_45);
lean_ctor_set(x_99, 2, x_87);
lean_ctor_set(x_99, 3, x_47);
lean_ctor_set(x_99, 4, x_48);
lean_ctor_set(x_99, 5, x_49);
lean_ctor_set(x_99, 6, x_50);
lean_ctor_set(x_99, 7, x_51);
lean_ctor_set(x_99, 8, x_52);
lean_ctor_set(x_99, 9, x_53);
lean_ctor_set_uint8(x_99, sizeof(void*)*10, x_46);
x_88 = x_99;
goto block_98;
}
block_98:
{
lean_object* x_89; 
if (x_43 == 0)
{
lean_ctor_set(x_42, 0, x_88);
x_89 = x_42;
goto block_96;
}
else
{
lean_object* x_97; 
x_97 = lean_alloc_ctor(0, 4, 8);
lean_ctor_set(x_97, 0, x_88);
lean_ctor_set(x_97, 1, x_38);
lean_ctor_set(x_97, 2, x_39);
lean_ctor_set(x_97, 3, x_40);
x_89 = x_97;
goto block_96;
}
block_96:
{
lean_object* x_90; 
lean_ctor_set_float(x_89, sizeof(void*)*4, x_12);
if (x_35 == 0)
{
lean_ctor_set(x_34, 1, x_89);
lean_ctor_set(x_34, 0, x_26);
x_90 = x_34;
goto block_94;
}
else
{
lean_object* x_95; 
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_26);
lean_ctor_set(x_95, 1, x_89);
x_90 = x_95;
goto block_94;
}
block_94:
{
lean_object* x_91; 
if (x_32 == 0)
{
lean_ctor_set(x_31, 0, x_90);
x_91 = x_31;
goto block_92;
}
else
{
lean_object* x_93; 
x_93 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_93, 0, x_90);
x_91 = x_93;
goto block_92;
}
block_92:
{
return x_91;
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
else
{
lean_dec(x_19);
return x_29;
}
}
block_167:
{
lean_object* x_125; lean_object* x_126; 
lean_inc(x_2);
lean_inc(x_118);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_118);
lean_ctor_set(x_125, 1, x_2);
x_126 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__1___redArg(x_122, x_125);
if (lean_obj_tag(x_126) == 1)
{
lean_object* x_127; 
lean_dec_ref(x_125);
lean_dec(x_118);
lean_dec(x_117);
lean_dec(x_2);
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
lean_dec_ref(x_126);
x_19 = x_127;
x_20 = x_119;
x_21 = x_120;
x_22 = x_121;
x_23 = x_122;
x_24 = lean_box(0);
goto block_116;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; uint8_t x_165; 
lean_dec(x_126);
x_128 = lean_ctor_get(x_119, 4);
lean_inc_ref(x_128);
x_129 = lean_ctor_get(x_122, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_119, 0);
x_131 = lean_ctor_get(x_119, 1);
x_132 = lean_ctor_get_uint8(x_119, sizeof(void*)*10);
x_133 = lean_ctor_get(x_119, 2);
x_134 = lean_ctor_get(x_119, 3);
x_135 = lean_ctor_get(x_119, 5);
x_136 = lean_ctor_get(x_119, 6);
x_137 = lean_ctor_get(x_119, 7);
x_138 = lean_ctor_get(x_119, 8);
x_139 = lean_ctor_get(x_119, 9);
x_165 = !lean_is_exclusive(x_119);
if (x_165 == 0)
{
lean_object* x_166; 
x_166 = lean_ctor_get(x_119, 4);
lean_dec(x_166);
x_140 = x_119;
x_141 = x_165;
goto block_164;
}
else
{
lean_inc(x_139);
lean_inc(x_138);
lean_inc(x_137);
lean_inc(x_136);
lean_inc(x_135);
lean_inc(x_134);
lean_inc(x_133);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_119);
x_140 = lean_box(0);
x_141 = x_165;
goto block_164;
}
block_164:
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; uint8_t x_163; 
x_142 = lean_ctor_get(x_128, 0);
x_143 = lean_ctor_get(x_128, 1);
x_144 = lean_ctor_get(x_128, 2);
x_145 = lean_ctor_get(x_128, 3);
x_146 = lean_ctor_get(x_128, 4);
x_163 = !lean_is_exclusive(x_128);
if (x_163 == 0)
{
x_147 = x_128;
x_148 = x_163;
goto block_162;
}
else
{
lean_inc(x_146);
lean_inc(x_145);
lean_inc(x_144);
lean_inc(x_143);
lean_inc(x_142);
lean_dec(x_128);
x_147 = lean_box(0);
x_148 = x_163;
goto block_162;
}
block_162:
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_149 = lean_array_push(x_142, x_118);
x_150 = lean_array_push(x_143, x_117);
x_151 = lean_array_push(x_144, x_14);
x_152 = lean_array_push(x_145, x_2);
x_153 = lean_unsigned_to_nat(1u);
x_154 = lean_nat_add(x_146, x_153);
lean_dec(x_146);
if (x_148 == 0)
{
lean_ctor_set(x_147, 4, x_154);
lean_ctor_set(x_147, 3, x_152);
lean_ctor_set(x_147, 2, x_151);
lean_ctor_set(x_147, 1, x_150);
lean_ctor_set(x_147, 0, x_149);
x_155 = x_147;
goto block_160;
}
else
{
lean_object* x_161; 
x_161 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_161, 0, x_149);
lean_ctor_set(x_161, 1, x_150);
lean_ctor_set(x_161, 2, x_151);
lean_ctor_set(x_161, 3, x_152);
lean_ctor_set(x_161, 4, x_154);
x_155 = x_161;
goto block_160;
}
block_160:
{
lean_object* x_156; 
if (x_141 == 0)
{
lean_ctor_set(x_140, 4, x_155);
x_156 = x_140;
goto block_158;
}
else
{
lean_object* x_159; 
x_159 = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(x_159, 0, x_130);
lean_ctor_set(x_159, 1, x_131);
lean_ctor_set(x_159, 2, x_133);
lean_ctor_set(x_159, 3, x_134);
lean_ctor_set(x_159, 4, x_155);
lean_ctor_set(x_159, 5, x_135);
lean_ctor_set(x_159, 6, x_136);
lean_ctor_set(x_159, 7, x_137);
lean_ctor_set(x_159, 8, x_138);
lean_ctor_set(x_159, 9, x_139);
lean_ctor_set_uint8(x_159, sizeof(void*)*10, x_132);
x_156 = x_159;
goto block_158;
}
block_158:
{
lean_object* x_157; 
lean_inc(x_129);
x_157 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__2___redArg(x_122, x_125, x_129);
x_19 = x_129;
x_20 = x_156;
x_21 = x_120;
x_22 = x_121;
x_23 = x_157;
x_24 = lean_box(0);
goto block_116;
}
}
}
}
}
}
block_227:
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; double x_176; lean_object* x_177; 
x_172 = lean_ctor_get(x_170, 0);
lean_inc_ref(x_172);
x_173 = lean_ctor_get(x_170, 1);
lean_inc_ref(x_173);
x_174 = lean_ctor_get(x_170, 2);
lean_inc_ref(x_174);
x_175 = lean_ctor_get(x_170, 3);
lean_inc_ref(x_175);
x_176 = lean_ctor_get_float(x_170, sizeof(void*)*4);
lean_dec_ref(x_170);
x_177 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__3___redArg(x_174, x_168);
if (lean_obj_tag(x_177) == 1)
{
lean_object* x_178; 
lean_dec(x_168);
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
lean_dec_ref(x_177);
x_117 = x_171;
x_118 = x_178;
x_119 = x_172;
x_120 = x_173;
x_121 = x_174;
x_122 = x_175;
x_123 = x_176;
x_124 = lean_box(0);
goto block_167;
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; uint8_t x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; uint8_t x_192; uint8_t x_226; 
lean_dec(x_177);
x_179 = lean_ctor_get(x_174, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_172, 0);
x_181 = lean_ctor_get(x_172, 1);
x_182 = lean_ctor_get_uint8(x_172, sizeof(void*)*10);
x_183 = lean_ctor_get(x_172, 2);
x_184 = lean_ctor_get(x_172, 3);
x_185 = lean_ctor_get(x_172, 4);
x_186 = lean_ctor_get(x_172, 5);
x_187 = lean_ctor_get(x_172, 6);
x_188 = lean_ctor_get(x_172, 7);
x_189 = lean_ctor_get(x_172, 8);
x_190 = lean_ctor_get(x_172, 9);
x_226 = !lean_is_exclusive(x_172);
if (x_226 == 0)
{
x_191 = x_172;
x_192 = x_226;
goto block_225;
}
else
{
lean_inc(x_190);
lean_inc(x_189);
lean_inc(x_188);
lean_inc(x_187);
lean_inc(x_186);
lean_inc(x_185);
lean_inc(x_184);
lean_inc(x_183);
lean_inc(x_181);
lean_inc(x_180);
lean_dec(x_172);
x_191 = lean_box(0);
x_192 = x_226;
goto block_225;
}
block_225:
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; uint8_t x_205; uint8_t x_222; 
x_193 = lean_unsigned_to_nat(1u);
x_194 = lean_obj_once(&l___private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go___closed__2, &l___private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go___closed__2_once, _init_l___private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go___closed__2);
lean_inc(x_171);
x_195 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_195, 0, x_171);
x_196 = lean_box(0);
lean_inc(x_179);
x_197 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_197, 0, x_194);
lean_ctor_set(x_197, 1, x_14);
lean_ctor_set(x_197, 2, x_195);
lean_ctor_set(x_197, 3, x_196);
lean_ctor_set(x_197, 4, x_179);
lean_ctor_set(x_197, 5, x_196);
lean_ctor_set(x_197, 6, x_196);
lean_ctor_set(x_197, 7, x_196);
lean_ctor_set(x_197, 8, x_196);
lean_ctor_set(x_197, 9, x_196);
x_198 = lean_ctor_get(x_190, 0);
x_199 = lean_ctor_get(x_190, 3);
x_200 = lean_ctor_get(x_190, 4);
x_201 = lean_ctor_get(x_190, 5);
x_202 = lean_ctor_get(x_190, 6);
x_203 = lean_ctor_get(x_190, 7);
x_222 = !lean_is_exclusive(x_190);
if (x_222 == 0)
{
lean_object* x_223; lean_object* x_224; 
x_223 = lean_ctor_get(x_190, 2);
lean_dec(x_223);
x_224 = lean_ctor_get(x_190, 1);
lean_dec(x_224);
x_204 = x_190;
x_205 = x_222;
goto block_221;
}
else
{
lean_inc(x_203);
lean_inc(x_202);
lean_inc(x_201);
lean_inc(x_200);
lean_inc(x_199);
lean_inc(x_198);
lean_dec(x_190);
x_204 = lean_box(0);
x_205 = x_222;
goto block_221;
}
block_221:
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_206 = l_Lean_Firefox_FrameTable_push(x_186, x_197);
lean_inc(x_168);
x_207 = lean_array_push(x_198, x_168);
x_208 = ((lean_object*)(l___private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go___closed__3));
x_209 = lean_array_push(x_199, x_194);
x_210 = lean_array_push(x_200, x_196);
x_211 = lean_array_push(x_201, x_196);
x_212 = lean_array_push(x_202, x_196);
x_213 = lean_nat_add(x_203, x_193);
lean_dec(x_203);
if (x_205 == 0)
{
lean_ctor_set(x_204, 7, x_213);
lean_ctor_set(x_204, 6, x_212);
lean_ctor_set(x_204, 5, x_211);
lean_ctor_set(x_204, 4, x_210);
lean_ctor_set(x_204, 3, x_209);
lean_ctor_set(x_204, 2, x_208);
lean_ctor_set(x_204, 1, x_208);
lean_ctor_set(x_204, 0, x_207);
x_214 = x_204;
goto block_219;
}
else
{
lean_object* x_220; 
x_220 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_220, 0, x_207);
lean_ctor_set(x_220, 1, x_208);
lean_ctor_set(x_220, 2, x_208);
lean_ctor_set(x_220, 3, x_209);
lean_ctor_set(x_220, 4, x_210);
lean_ctor_set(x_220, 5, x_211);
lean_ctor_set(x_220, 6, x_212);
lean_ctor_set(x_220, 7, x_213);
x_214 = x_220;
goto block_219;
}
block_219:
{
lean_object* x_215; 
if (x_192 == 0)
{
lean_ctor_set(x_191, 9, x_214);
lean_ctor_set(x_191, 5, x_206);
x_215 = x_191;
goto block_217;
}
else
{
lean_object* x_218; 
x_218 = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(x_218, 0, x_180);
lean_ctor_set(x_218, 1, x_181);
lean_ctor_set(x_218, 2, x_183);
lean_ctor_set(x_218, 3, x_184);
lean_ctor_set(x_218, 4, x_185);
lean_ctor_set(x_218, 5, x_206);
lean_ctor_set(x_218, 6, x_187);
lean_ctor_set(x_218, 7, x_188);
lean_ctor_set(x_218, 8, x_189);
lean_ctor_set(x_218, 9, x_214);
lean_ctor_set_uint8(x_218, sizeof(void*)*10, x_182);
x_215 = x_218;
goto block_217;
}
block_217:
{
lean_object* x_216; 
lean_inc(x_179);
x_216 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__4___redArg(x_174, x_168, x_179);
x_117 = x_171;
x_118 = x_179;
x_119 = x_215;
x_120 = x_173;
x_121 = x_216;
x_122 = x_175;
x_123 = x_176;
x_124 = lean_box(0);
goto block_167;
}
}
}
}
}
}
block_234:
{
lean_object* x_231; lean_object* x_232; 
x_231 = ((lean_object*)(l_Lean_Firefox_categories));
x_232 = l_Array_findIdx_x3f_loop___redArg(x_17, x_231, x_14);
if (lean_obj_tag(x_232) == 0)
{
x_168 = x_228;
x_169 = lean_box(0);
x_170 = x_229;
x_171 = x_14;
goto block_227;
}
else
{
lean_object* x_233; 
x_233 = lean_ctor_get(x_232, 0);
lean_inc(x_233);
lean_dec_ref(x_232);
x_168 = x_228;
x_169 = lean_box(0);
x_170 = x_229;
x_171 = x_233;
goto block_227;
}
}
block_277:
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; double x_242; lean_object* x_243; 
x_238 = lean_ctor_get(x_236, 0);
lean_inc_ref(x_238);
x_239 = lean_ctor_get(x_236, 1);
x_240 = lean_ctor_get(x_236, 2);
x_241 = lean_ctor_get(x_236, 3);
x_242 = lean_ctor_get_float(x_236, sizeof(void*)*4);
x_243 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__5___redArg(x_239, x_235);
if (lean_obj_tag(x_243) == 1)
{
lean_object* x_244; 
lean_dec_ref(x_238);
lean_dec_ref(x_235);
x_244 = lean_ctor_get(x_243, 0);
lean_inc(x_244);
lean_dec_ref(x_243);
x_228 = x_244;
x_229 = x_236;
x_230 = lean_box(0);
goto block_234;
}
else
{
lean_object* x_245; uint8_t x_246; uint8_t x_272; 
lean_inc_ref(x_241);
lean_inc_ref(x_240);
lean_inc_ref(x_239);
lean_dec(x_243);
x_272 = !lean_is_exclusive(x_236);
if (x_272 == 0)
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; 
x_273 = lean_ctor_get(x_236, 3);
lean_dec(x_273);
x_274 = lean_ctor_get(x_236, 2);
lean_dec(x_274);
x_275 = lean_ctor_get(x_236, 1);
lean_dec(x_275);
x_276 = lean_ctor_get(x_236, 0);
lean_dec(x_276);
x_245 = x_236;
x_246 = x_272;
goto block_271;
}
else
{
lean_dec(x_236);
x_245 = lean_box(0);
x_246 = x_272;
goto block_271;
}
block_271:
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; uint8_t x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; uint8_t x_260; uint8_t x_270; 
x_247 = lean_ctor_get(x_239, 0);
lean_inc(x_247);
x_248 = lean_ctor_get(x_238, 0);
x_249 = lean_ctor_get(x_238, 1);
x_250 = lean_ctor_get_uint8(x_238, sizeof(void*)*10);
x_251 = lean_ctor_get(x_238, 2);
x_252 = lean_ctor_get(x_238, 3);
x_253 = lean_ctor_get(x_238, 4);
x_254 = lean_ctor_get(x_238, 5);
x_255 = lean_ctor_get(x_238, 6);
x_256 = lean_ctor_get(x_238, 7);
x_257 = lean_ctor_get(x_238, 8);
x_258 = lean_ctor_get(x_238, 9);
x_270 = !lean_is_exclusive(x_238);
if (x_270 == 0)
{
x_259 = x_238;
x_260 = x_270;
goto block_269;
}
else
{
lean_inc(x_258);
lean_inc(x_257);
lean_inc(x_256);
lean_inc(x_255);
lean_inc(x_254);
lean_inc(x_253);
lean_inc(x_252);
lean_inc(x_251);
lean_inc(x_249);
lean_inc(x_248);
lean_dec(x_238);
x_259 = lean_box(0);
x_260 = x_270;
goto block_269;
}
block_269:
{
lean_object* x_261; lean_object* x_262; 
lean_inc_ref(x_235);
x_261 = lean_array_push(x_257, x_235);
if (x_260 == 0)
{
lean_ctor_set(x_259, 8, x_261);
x_262 = x_259;
goto block_267;
}
else
{
lean_object* x_268; 
x_268 = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(x_268, 0, x_248);
lean_ctor_set(x_268, 1, x_249);
lean_ctor_set(x_268, 2, x_251);
lean_ctor_set(x_268, 3, x_252);
lean_ctor_set(x_268, 4, x_253);
lean_ctor_set(x_268, 5, x_254);
lean_ctor_set(x_268, 6, x_255);
lean_ctor_set(x_268, 7, x_256);
lean_ctor_set(x_268, 8, x_261);
lean_ctor_set(x_268, 9, x_258);
lean_ctor_set_uint8(x_268, sizeof(void*)*10, x_250);
x_262 = x_268;
goto block_267;
}
block_267:
{
lean_object* x_263; lean_object* x_264; 
lean_inc(x_247);
x_263 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__6___redArg(x_239, x_235, x_247);
if (x_246 == 0)
{
lean_ctor_set(x_245, 1, x_263);
lean_ctor_set(x_245, 0, x_262);
x_264 = x_245;
goto block_265;
}
else
{
lean_object* x_266; 
x_266 = lean_alloc_ctor(0, 4, 8);
lean_ctor_set(x_266, 0, x_262);
lean_ctor_set(x_266, 1, x_263);
lean_ctor_set(x_266, 2, x_240);
lean_ctor_set(x_266, 3, x_241);
lean_ctor_set_float(x_266, sizeof(void*)*4, x_242);
x_264 = x_266;
goto block_265;
}
block_265:
{
x_228 = x_247;
x_229 = x_264;
x_230 = lean_box(0);
goto block_234;
}
}
}
}
}
}
block_287:
{
if (x_1 == 0)
{
lean_dec_ref(x_8);
x_235 = x_278;
x_236 = x_279;
x_237 = lean_box(0);
goto block_277;
}
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; 
lean_inc(x_3);
x_281 = l_Lean_MessageData_format(x_8, x_3);
x_282 = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
x_283 = lean_string_append(x_278, x_282);
x_284 = l_Std_Format_defWidth;
x_285 = l_Std_Format_pretty(x_281, x_284, x_14, x_14);
x_286 = lean_string_append(x_283, x_285);
lean_dec_ref(x_285);
x_235 = x_286;
x_236 = x_279;
x_237 = lean_box(0);
goto block_277;
}
}
block_292:
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; 
x_289 = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
x_290 = lean_string_append(x_288, x_289);
x_291 = lean_string_append(x_290, x_13);
lean_dec_ref(x_13);
x_278 = x_291;
x_279 = x_5;
x_280 = lean_box(0);
goto block_287;
}
}
else
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; 
lean_dec_ref(x_13);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_295 = lean_box(0);
x_296 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_296, 0, x_295);
lean_ctor_set(x_296, 1, x_5);
x_297 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_297, 0, x_296);
return x_297;
}
}
case 3:
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; 
lean_dec(x_3);
x_298 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_298);
x_299 = lean_ctor_get(x_4, 1);
lean_inc_ref(x_299);
lean_dec_ref(x_4);
x_300 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_300, 0, x_298);
x_3 = x_300;
x_4 = x_299;
goto _start;
}
default: 
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; 
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_302 = lean_box(0);
x_303 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_303, 0, x_302);
lean_ctor_set(x_303, 1, x_5);
x_304 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_304, 0, x_303);
return x_304;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_17; 
x_17 = lean_usize_dec_lt(x_6, x_5);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_3);
lean_dec(x_1);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_7);
lean_ctor_set(x_18, 1, x_8);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_box(0);
x_21 = lean_array_uget_borrowed(x_4, x_6);
x_22 = l___private_Lean_Util_Profiler_0__Lean_Firefox_getFirstStart_x3f(x_21);
if (lean_obj_tag(x_22) == 1)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_107; 
x_23 = lean_ctor_get(x_8, 0);
lean_inc_ref(x_23);
x_24 = lean_ctor_get(x_23, 2);
lean_inc_ref(x_24);
x_25 = lean_ctor_get(x_22, 0);
x_107 = !lean_is_exclusive(x_22);
if (x_107 == 0)
{
x_26 = x_22;
x_27 = x_107;
goto block_106;
}
else
{
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_box(0);
x_27 = x_107;
goto block_106;
}
block_106:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; double x_31; lean_object* x_32; uint8_t x_33; uint8_t x_104; 
x_28 = lean_ctor_get(x_8, 1);
x_29 = lean_ctor_get(x_8, 2);
x_30 = lean_ctor_get(x_8, 3);
x_31 = lean_ctor_get_float(x_8, sizeof(void*)*4);
x_104 = !lean_is_exclusive(x_8);
if (x_104 == 0)
{
lean_object* x_105; 
x_105 = lean_ctor_get(x_8, 0);
lean_dec(x_105);
x_32 = x_8;
x_33 = x_104;
goto block_103;
}
else
{
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_8);
x_32 = lean_box(0);
x_33 = x_104;
goto block_103;
}
block_103:
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; uint8_t x_101; 
x_34 = lean_ctor_get(x_23, 0);
x_35 = lean_ctor_get(x_23, 1);
x_36 = lean_ctor_get_uint8(x_23, sizeof(void*)*10);
x_37 = lean_ctor_get(x_23, 3);
x_38 = lean_ctor_get(x_23, 4);
x_39 = lean_ctor_get(x_23, 5);
x_40 = lean_ctor_get(x_23, 6);
x_41 = lean_ctor_get(x_23, 7);
x_42 = lean_ctor_get(x_23, 8);
x_43 = lean_ctor_get(x_23, 9);
x_101 = !lean_is_exclusive(x_23);
if (x_101 == 0)
{
lean_object* x_102; 
x_102 = lean_ctor_get(x_23, 2);
lean_dec(x_102);
x_44 = x_23;
x_45 = x_101;
goto block_100;
}
else
{
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_23);
x_44 = lean_box(0);
x_45 = x_101;
goto block_100;
}
block_100:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; uint8_t x_98; 
x_46 = lean_ctor_get(x_24, 0);
x_47 = lean_ctor_get(x_24, 1);
x_48 = lean_ctor_get(x_24, 2);
x_49 = lean_ctor_get(x_24, 4);
x_50 = lean_ctor_get(x_24, 5);
x_98 = !lean_is_exclusive(x_24);
if (x_98 == 0)
{
lean_object* x_99; 
x_99 = lean_ctor_get(x_24, 3);
lean_dec(x_99);
x_51 = x_24;
x_52 = x_98;
goto block_97;
}
else
{
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_24);
x_51 = lean_box(0);
x_52 = x_98;
goto block_97;
}
block_97:
{
lean_object* x_53; lean_object* x_54; double x_55; double x_56; lean_object* x_57; lean_object* x_58; double x_59; double x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; double x_65; lean_object* x_66; lean_object* x_67; double x_68; double x_69; double x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; double x_76; double x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_inc(x_1);
x_53 = lean_array_push(x_46, x_1);
lean_inc(x_1);
x_54 = lean_array_push(x_53, x_1);
x_55 = lean_float_once(&l_Lean_Firefox_instCoeFloatMilliseconds___lam__0___closed__0, &l_Lean_Firefox_instCoeFloatMilliseconds___lam__0___closed__0_once, _init_l_Lean_Firefox_instCoeFloatMilliseconds___lam__0___closed__0);
x_56 = lean_float_mul(x_31, x_55);
x_57 = lean_box_float(x_56);
x_58 = lean_array_push(x_47, x_57);
x_59 = lean_unbox_float(x_25);
x_60 = lean_float_mul(x_59, x_55);
x_61 = lean_box_float(x_60);
x_62 = lean_array_push(x_58, x_61);
x_63 = lean_unsigned_to_nat(0u);
x_64 = lean_unsigned_to_nat(1u);
x_65 = l_Float_ofScientific(x_63, x_17, x_64);
x_66 = lean_box_float(x_65);
x_67 = lean_array_push(x_48, x_66);
x_68 = lean_unbox_float(x_25);
lean_dec(x_25);
x_69 = lean_float_sub(x_68, x_31);
x_70 = lean_float_mul(x_69, x_55);
x_71 = lean_box_float(x_70);
x_72 = lean_array_push(x_67, x_71);
x_73 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__0___closed__0));
x_74 = lean_box_float(x_65);
x_75 = lean_array_push(x_49, x_74);
x_76 = lean_float_once(&l_Lean_Firefox_instCoeFloatMicroseconds___lam__0___closed__0, &l_Lean_Firefox_instCoeFloatMicroseconds___lam__0___closed__0_once, _init_l_Lean_Firefox_instCoeFloatMicroseconds___lam__0___closed__0);
x_77 = lean_float_mul(x_69, x_76);
x_78 = lean_box_float(x_77);
x_79 = lean_array_push(x_75, x_78);
x_80 = lean_unsigned_to_nat(2u);
x_81 = lean_nat_add(x_50, x_80);
lean_dec(x_50);
if (x_52 == 0)
{
lean_ctor_set(x_51, 5, x_81);
lean_ctor_set(x_51, 4, x_79);
lean_ctor_set(x_51, 3, x_73);
lean_ctor_set(x_51, 2, x_72);
lean_ctor_set(x_51, 1, x_62);
lean_ctor_set(x_51, 0, x_54);
x_82 = x_51;
goto block_95;
}
else
{
lean_object* x_96; 
x_96 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_96, 0, x_54);
lean_ctor_set(x_96, 1, x_62);
lean_ctor_set(x_96, 2, x_72);
lean_ctor_set(x_96, 3, x_73);
lean_ctor_set(x_96, 4, x_79);
lean_ctor_set(x_96, 5, x_81);
x_82 = x_96;
goto block_95;
}
block_95:
{
lean_object* x_83; 
if (x_45 == 0)
{
lean_ctor_set(x_44, 2, x_82);
x_83 = x_44;
goto block_93;
}
else
{
lean_object* x_94; 
x_94 = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(x_94, 0, x_34);
lean_ctor_set(x_94, 1, x_35);
lean_ctor_set(x_94, 2, x_82);
lean_ctor_set(x_94, 3, x_37);
lean_ctor_set(x_94, 4, x_38);
lean_ctor_set(x_94, 5, x_39);
lean_ctor_set(x_94, 6, x_40);
lean_ctor_set(x_94, 7, x_41);
lean_ctor_set(x_94, 8, x_42);
lean_ctor_set(x_94, 9, x_43);
lean_ctor_set_uint8(x_94, sizeof(void*)*10, x_36);
x_83 = x_94;
goto block_93;
}
block_93:
{
lean_object* x_84; 
if (x_33 == 0)
{
lean_ctor_set(x_32, 0, x_83);
x_84 = x_32;
goto block_91;
}
else
{
lean_object* x_92; 
x_92 = lean_alloc_ctor(0, 4, 8);
lean_ctor_set(x_92, 0, x_83);
lean_ctor_set(x_92, 1, x_28);
lean_ctor_set(x_92, 2, x_29);
lean_ctor_set(x_92, 3, x_30);
lean_ctor_set_float(x_92, sizeof(void*)*4, x_31);
x_84 = x_92;
goto block_91;
}
block_91:
{
lean_object* x_85; 
lean_inc(x_1);
if (x_27 == 0)
{
lean_ctor_set(x_26, 0, x_1);
x_85 = x_26;
goto block_89;
}
else
{
lean_object* x_90; 
x_90 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_90, 0, x_1);
x_85 = x_90;
goto block_89;
}
block_89:
{
lean_object* x_86; 
lean_inc(x_21);
lean_inc(x_3);
x_86 = l___private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go(x_2, x_85, x_3, x_21, x_84);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
lean_dec_ref(x_86);
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
lean_dec(x_87);
x_10 = x_20;
x_11 = x_88;
x_12 = lean_box(0);
goto block_16;
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_86;
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
else
{
lean_dec(x_22);
x_10 = x_20;
x_11 = x_8;
x_12 = lean_box(0);
goto block_16;
}
}
block_16:
{
size_t x_13; size_t x_14; 
x_13 = 1;
x_14 = lean_usize_add(x_6, x_13);
x_6 = x_14;
x_7 = x_10;
x_8 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_10 = lean_unbox(x_2);
x_11 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_12 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_13 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__0(x_1, x_10, x_3, x_4, x_11, x_12, x_7, x_8);
lean_dec_ref(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_1);
x_8 = l___private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go(x_7, x_2, x_3, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__1___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__1(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__2___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__3___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__3(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__4___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__5___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__5(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__6___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__1_spec__1___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__1_spec__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__2_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__2_spec__3___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__2_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__2_spec__3(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__2_spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__2_spec__4___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__2_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__2_spec__5___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__3_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__3_spec__7___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__3_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__3_spec__7(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__4_spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__4_spec__9___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__4_spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__4_spec__9(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__4_spec__10(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__4_spec__10___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__4_spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__4_spec__11___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__5_spec__13(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__5_spec__13___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__5_spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__5_spec__13(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__6_spec__15(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__6_spec__15___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__6_spec__15___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__6_spec__15(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__6_spec__16(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__6_spec__16___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__6_spec__17(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__6_spec__17___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__2_spec__4_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__2_spec__4_spec__6___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__4_spec__10_spec__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__4_spec__10_spec__13___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__6_spec__16_spec__20(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__6_spec__16_spec__20___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__2_spec__4_spec__6_spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__2_spec__4_spec__6_spec__11___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__4_spec__10_spec__13_spec__17(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__4_spec__10_spec__13_spec__17___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__6_spec__16_spec__20_spec__23(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__6_spec__16_spec__20_spec__23___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Profiler_0__Lean_Firefox_addTrace(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = l___private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go(x_1, x_5, x_5, x_3, x_2);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_15; 
x_7 = lean_ctor_get(x_6, 0);
x_15 = !lean_is_exclusive(x_6);
if (x_15 == 0)
{
x_8 = x_6;
x_9 = x_15;
goto block_14;
}
else
{
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_box(0);
x_9 = x_15;
goto block_14;
}
block_14:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
if (x_9 == 0)
{
lean_ctor_set(x_8, 0, x_10);
x_11 = x_8;
goto block_12;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_10);
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
lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_23; 
x_16 = lean_ctor_get(x_6, 0);
x_23 = !lean_is_exclusive(x_6);
if (x_23 == 0)
{
x_17 = x_6;
x_18 = x_23;
goto block_22;
}
else
{
lean_inc(x_16);
lean_dec(x_6);
x_17 = lean_box(0);
x_18 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_19; 
if (x_18 == 0)
{
x_19 = x_17;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_16);
x_19 = x_21;
goto block_20;
}
block_20:
{
return x_19;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Profiler_0__Lean_Firefox_addTrace___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
x_6 = l___private_Lean_Util_Profiler_0__Lean_Firefox_addTrace(x_5, x_2, x_3);
return x_6;
}
}
static lean_object* _init_l_Lean_Firefox_Thread_new___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__0___closed__0));
x_3 = ((lean_object*)(l_Lean_Firefox_Thread_new___closed__1));
x_4 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set(x_4, 2, x_3);
lean_ctor_set(x_4, 3, x_2);
lean_ctor_set(x_4, 4, x_3);
lean_ctor_set(x_4, 5, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Firefox_Thread_new___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = ((lean_object*)(l_Lean_Firefox_Thread_new___closed__1));
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_Thread_new___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = ((lean_object*)(l_Lean_Firefox_Thread_new___closed__1));
x_3 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 3, x_2);
lean_ctor_set(x_3, 4, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Firefox_Thread_new___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = ((lean_object*)(l_Lean_Firefox_Thread_new___closed__1));
x_3 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 3, x_2);
lean_ctor_set(x_3, 4, x_2);
lean_ctor_set(x_3, 5, x_2);
lean_ctor_set(x_3, 6, x_2);
lean_ctor_set(x_3, 7, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Firefox_Thread_new(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = ((lean_object*)(l_Lean_Firefox_Thread_new___closed__0));
x_3 = 1;
x_4 = ((lean_object*)(l_Lean_Firefox_Thread_new___closed__1));
x_5 = lean_obj_once(&l_Lean_Firefox_Thread_new___closed__2, &l_Lean_Firefox_Thread_new___closed__2_once, _init_l_Lean_Firefox_Thread_new___closed__2);
x_6 = lean_obj_once(&l_Lean_Firefox_Thread_new___closed__3, &l_Lean_Firefox_Thread_new___closed__3_once, _init_l_Lean_Firefox_Thread_new___closed__3);
x_7 = lean_obj_once(&l_Lean_Firefox_Thread_new___closed__4, &l_Lean_Firefox_Thread_new___closed__4_once, _init_l_Lean_Firefox_Thread_new___closed__4);
x_8 = l_Lean_Firefox_instInhabitedFrameTable_default;
x_9 = ((lean_object*)(l_Lean_Firefox_Thread_new___closed__5));
x_10 = lean_obj_once(&l_Lean_Firefox_Thread_new___closed__6, &l_Lean_Firefox_Thread_new___closed__6_once, _init_l_Lean_Firefox_Thread_new___closed__6);
x_11 = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_2);
lean_ctor_set(x_11, 2, x_5);
lean_ctor_set(x_11, 3, x_6);
lean_ctor_set(x_11, 4, x_7);
lean_ctor_set(x_11, 5, x_8);
lean_ctor_set(x_11, 6, x_9);
lean_ctor_set(x_11, 7, x_9);
lean_ctor_set(x_11, 8, x_4);
lean_ctor_set(x_11, 9, x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*10, x_3);
return x_11;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Firefox_Profile_export_spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_1, 0);
x_6 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(x_5, x_3);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = lean_unbox(x_4);
return x_7;
}
else
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec_ref(x_6);
if (lean_obj_tag(x_8) == 1)
{
uint8_t x_9; 
x_9 = lean_ctor_get_uint8(x_8, 0);
lean_dec_ref(x_8);
return x_9;
}
else
{
uint8_t x_10; 
lean_dec(x_8);
x_10 = lean_unbox(x_4);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Firefox_Profile_export_spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Option_get___at___00Lean_Firefox_Profile_export_spec__2(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint64_t l_Lean_Firefox_Profile_export___lam__0(lean_object* x_1) {
_start:
{
uint64_t x_2; 
x_2 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Firefox_Profile_export___lam__0___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lean_Firefox_Profile_export___lam__0(x_1);
lean_dec_ref(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_5 = lean_array_uget_borrowed(x_3, x_2);
x_6 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_6);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = l_Lean_PersistentArray_toArray___redArg(x_6);
lean_dec_ref(x_6);
x_10 = 1;
x_11 = lean_usize_add(x_2, x_10);
x_12 = lean_array_uset(x_8, x_2, x_9);
x_2 = x_11;
x_3 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__4(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_5 = lean_array_uget_borrowed(x_3, x_2);
x_6 = lean_ctor_get(x_5, 1);
lean_inc_ref(x_6);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_8, x_2, x_6);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__4(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Firefox_Profile_export_spec__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget_borrowed(x_1, x_2);
x_7 = l_Array_append___redArg(x_4, x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_2 = x_9;
x_4 = x_7;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Firefox_Profile_export_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Firefox_Profile_export_spec__5(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__6___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; double x_6; double x_7; uint8_t x_8; 
lean_inc_ref(x_1);
x_4 = lean_apply_1(x_1, x_2);
x_5 = lean_apply_1(x_1, x_3);
x_6 = lean_unbox_float(x_4);
lean_dec_ref(x_4);
x_7 = lean_unbox_float(x_5);
lean_dec_ref(x_5);
x_8 = lean_float_decLt(x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__6___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__6___redArg___lam__1(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT double l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__6___redArg___lam__0(lean_object* x_1, double x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_3);
x_5 = lean_nat_dec_lt(x_1, x_4);
if (x_5 == 0)
{
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_array_fget_borrowed(x_3, x_1);
x_7 = lean_ctor_get(x_6, 1);
x_8 = l___private_Lean_Util_Profiler_0__Lean_Firefox_getFirstStart_x3f(x_7);
if (lean_obj_tag(x_8) == 0)
{
return x_2;
}
else
{
lean_object* x_9; double x_10; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec_ref(x_8);
x_10 = lean_unbox_float(x_9);
lean_dec(x_9);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__6___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
double x_4; double x_5; lean_object* x_6; 
x_4 = lean_unbox_float(x_2);
lean_dec_ref(x_2);
x_5 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__6___redArg___lam__0(x_1, x_4, x_3);
lean_dec_ref(x_3);
lean_dec(x_1);
x_6 = lean_box_float(x_5);
return x_6;
}
}
static lean_object* _init_l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__6___redArg___closed__0___boxed__const__1(void) {
_start:
{
double x_1; lean_object* x_2; 
x_1 = lean_float_once(&l___private_Lean_Util_Profiler_0__Lean_Firefox_getFirstStart_x3f___closed__0, &l___private_Lean_Util_Profiler_0__Lean_Firefox_getFirstStart_x3f___closed__0_once, _init_l___private_Lean_Util_Profiler_0__Lean_Firefox_getFirstStart_x3f___closed__0);
x_2 = lean_box_float(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__6___redArg___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__6___redArg___closed__0___boxed__const__1;
x_3 = lean_alloc_closure((void*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__6___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__6___redArg___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__6___redArg___closed__0, &l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__6___redArg___closed__0_once, _init_l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__6___redArg___closed__0);
x_2 = lean_alloc_closure((void*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__6___redArg___lam__1___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__6___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_lt(x_2, x_3);
if (x_4 == 0)
{
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_obj_once(&l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__6___redArg___closed__1, &l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__6___redArg___closed__1_once, _init_l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__6___redArg___closed__1);
lean_inc(x_2);
x_6 = l_Array_qpartition___redArg(x_1, x_5, x_2, x_3);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = lean_nat_dec_le(x_3, x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__6___redArg(x_8, x_2, x_7);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_7, x_11);
lean_dec(x_7);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
else
{
lean_dec(x_7);
lean_dec(x_2);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__6___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__6___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Firefox_Profile_export_spec__3(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_4, x_3);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_5);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; double x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; double x_27; uint8_t x_28; 
x_9 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_5, 1);
x_11 = lean_ctor_get(x_5, 2);
x_12 = lean_ctor_get(x_5, 3);
x_13 = lean_ctor_get_float(x_5, sizeof(void*)*4);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_array_uget_borrowed(x_2, x_4);
x_27 = l_Float_ofScientific(x_14, x_7, x_15);
x_28 = lean_float_decLt(x_27, x_13);
if (x_28 == 0)
{
lean_dec_ref(x_9);
x_17 = x_5;
x_18 = lean_box(0);
goto block_26;
}
else
{
lean_object* x_29; 
x_29 = l___private_Lean_Util_Profiler_0__Lean_Firefox_getFirstStart_x3f(x_16);
if (lean_obj_tag(x_29) == 1)
{
lean_object* x_30; uint8_t x_31; uint8_t x_90; 
lean_inc_ref(x_12);
lean_inc_ref(x_11);
lean_inc_ref(x_10);
x_90 = !lean_is_exclusive(x_5);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_91 = lean_ctor_get(x_5, 3);
lean_dec(x_91);
x_92 = lean_ctor_get(x_5, 2);
lean_dec(x_92);
x_93 = lean_ctor_get(x_5, 1);
lean_dec(x_93);
x_94 = lean_ctor_get(x_5, 0);
lean_dec(x_94);
x_30 = x_5;
x_31 = x_90;
goto block_89;
}
else
{
lean_dec(x_5);
x_30 = lean_box(0);
x_31 = x_90;
goto block_89;
}
block_89:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; uint8_t x_87; 
x_32 = lean_ctor_get(x_9, 2);
lean_inc_ref(x_32);
x_33 = lean_ctor_get(x_29, 0);
lean_inc(x_33);
lean_dec_ref(x_29);
x_34 = lean_ctor_get(x_9, 0);
x_35 = lean_ctor_get(x_9, 1);
x_36 = lean_ctor_get_uint8(x_9, sizeof(void*)*10);
x_37 = lean_ctor_get(x_9, 3);
x_38 = lean_ctor_get(x_9, 4);
x_39 = lean_ctor_get(x_9, 5);
x_40 = lean_ctor_get(x_9, 6);
x_41 = lean_ctor_get(x_9, 7);
x_42 = lean_ctor_get(x_9, 8);
x_43 = lean_ctor_get(x_9, 9);
x_87 = !lean_is_exclusive(x_9);
if (x_87 == 0)
{
lean_object* x_88; 
x_88 = lean_ctor_get(x_9, 2);
lean_dec(x_88);
x_44 = x_9;
x_45 = x_87;
goto block_86;
}
else
{
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_9);
x_44 = lean_box(0);
x_45 = x_87;
goto block_86;
}
block_86:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; uint8_t x_84; 
x_46 = lean_ctor_get(x_32, 0);
x_47 = lean_ctor_get(x_32, 1);
x_48 = lean_ctor_get(x_32, 2);
x_49 = lean_ctor_get(x_32, 4);
x_50 = lean_ctor_get(x_32, 5);
x_84 = !lean_is_exclusive(x_32);
if (x_84 == 0)
{
lean_object* x_85; 
x_85 = lean_ctor_get(x_32, 3);
lean_dec(x_85);
x_51 = x_32;
x_52 = x_84;
goto block_83;
}
else
{
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_32);
x_51 = lean_box(0);
x_52 = x_84;
goto block_83;
}
block_83:
{
lean_object* x_53; lean_object* x_54; double x_55; double x_56; lean_object* x_57; lean_object* x_58; double x_59; double x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_53 = lean_array_push(x_46, x_14);
x_54 = lean_array_push(x_53, x_14);
x_55 = lean_float_once(&l_Lean_Firefox_instCoeFloatMilliseconds___lam__0___closed__0, &l_Lean_Firefox_instCoeFloatMilliseconds___lam__0___closed__0_once, _init_l_Lean_Firefox_instCoeFloatMilliseconds___lam__0___closed__0);
x_56 = lean_float_mul(x_13, x_55);
x_57 = lean_box_float(x_56);
x_58 = lean_array_push(x_47, x_57);
x_59 = lean_unbox_float(x_33);
lean_dec(x_33);
x_60 = lean_float_mul(x_59, x_55);
x_61 = lean_box_float(x_60);
x_62 = lean_array_push(x_58, x_61);
x_63 = lean_box_float(x_27);
x_64 = lean_array_push(x_48, x_63);
x_65 = lean_box_float(x_27);
x_66 = lean_array_push(x_64, x_65);
x_67 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__0___closed__0));
x_68 = lean_box_float(x_27);
x_69 = lean_array_push(x_49, x_68);
x_70 = lean_box_float(x_27);
x_71 = lean_array_push(x_69, x_70);
x_72 = lean_unsigned_to_nat(2u);
x_73 = lean_nat_add(x_50, x_72);
lean_dec(x_50);
if (x_52 == 0)
{
lean_ctor_set(x_51, 5, x_73);
lean_ctor_set(x_51, 4, x_71);
lean_ctor_set(x_51, 3, x_67);
lean_ctor_set(x_51, 2, x_66);
lean_ctor_set(x_51, 1, x_62);
lean_ctor_set(x_51, 0, x_54);
x_74 = x_51;
goto block_81;
}
else
{
lean_object* x_82; 
x_82 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_82, 0, x_54);
lean_ctor_set(x_82, 1, x_62);
lean_ctor_set(x_82, 2, x_66);
lean_ctor_set(x_82, 3, x_67);
lean_ctor_set(x_82, 4, x_71);
lean_ctor_set(x_82, 5, x_73);
x_74 = x_82;
goto block_81;
}
block_81:
{
lean_object* x_75; 
if (x_45 == 0)
{
lean_ctor_set(x_44, 2, x_74);
x_75 = x_44;
goto block_79;
}
else
{
lean_object* x_80; 
x_80 = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(x_80, 0, x_34);
lean_ctor_set(x_80, 1, x_35);
lean_ctor_set(x_80, 2, x_74);
lean_ctor_set(x_80, 3, x_37);
lean_ctor_set(x_80, 4, x_38);
lean_ctor_set(x_80, 5, x_39);
lean_ctor_set(x_80, 6, x_40);
lean_ctor_set(x_80, 7, x_41);
lean_ctor_set(x_80, 8, x_42);
lean_ctor_set(x_80, 9, x_43);
lean_ctor_set_uint8(x_80, sizeof(void*)*10, x_36);
x_75 = x_80;
goto block_79;
}
block_79:
{
lean_object* x_76; 
if (x_31 == 0)
{
lean_ctor_set(x_30, 0, x_75);
x_76 = x_30;
goto block_77;
}
else
{
lean_object* x_78; 
x_78 = lean_alloc_ctor(0, 4, 8);
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_10);
lean_ctor_set(x_78, 2, x_11);
lean_ctor_set(x_78, 3, x_12);
lean_ctor_set_float(x_78, sizeof(void*)*4, x_13);
x_76 = x_78;
goto block_77;
}
block_77:
{
x_17 = x_76;
x_18 = lean_box(0);
goto block_26;
}
}
}
}
}
}
}
else
{
lean_dec(x_29);
lean_dec_ref(x_9);
x_17 = x_5;
x_18 = lean_box(0);
goto block_26;
}
}
block_26:
{
lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_19 = l_Lean_trace_profiler_output_pp;
x_20 = l_Lean_Option_get___at___00Lean_Firefox_Profile_export_spec__2(x_1, x_19);
lean_inc(x_16);
x_21 = l___private_Lean_Util_Profiler_0__Lean_Firefox_addTrace(x_20, x_17, x_16);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; size_t x_23; size_t x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
x_23 = 1;
x_24 = lean_usize_add(x_4, x_23);
x_4 = x_24;
x_5 = x_22;
goto _start;
}
else
{
return x_21;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Firefox_Profile_export_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Firefox_Profile_export_spec__3(x_1, x_2, x_7, x_8, x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_9;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__7___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__7___closed__3));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__7___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(16u);
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__7___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__7___closed__6, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__7___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__7___closed__6);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__7(lean_object* x_1, double x_2, double x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_6, x_5);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec_ref(x_4);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint64_t x_36; uint64_t x_37; uint8_t x_38; lean_object* x_39; size_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_53; size_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_66; lean_object* x_67; lean_object* x_68; size_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_75; lean_object* x_76; lean_object* x_77; size_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_84; 
x_11 = lean_array_uget_borrowed(x_7, x_6);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_array_uset(x_7, x_6, x_14);
x_36 = 0;
x_37 = lean_unbox_uint64(x_12);
x_38 = lean_uint64_dec_eq(x_37, x_36);
if (x_38 == 0)
{
uint64_t x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_unbox_uint64(x_12);
lean_dec(x_12);
x_116 = lean_uint64_to_nat(x_115);
x_117 = l_Nat_reprFast(x_116);
x_84 = x_117;
goto block_114;
}
else
{
lean_dec(x_12);
lean_inc_ref(x_4);
x_84 = x_4;
goto block_114;
}
block_35:
{
size_t x_20; lean_object* x_21; 
x_20 = lean_array_size(x_18);
x_21 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Firefox_Profile_export_spec__3(x_1, x_18, x_20, x_16, x_17);
lean_dec_ref(x_18);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
x_23 = 1;
x_24 = lean_usize_add(x_6, x_23);
x_25 = lean_array_uset(x_15, x_6, x_22);
x_6 = x_24;
x_7 = x_25;
goto _start;
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_34; 
lean_dec_ref(x_15);
lean_dec_ref(x_4);
x_27 = lean_ctor_get(x_21, 0);
x_34 = !lean_is_exclusive(x_21);
if (x_34 == 0)
{
x_28 = x_21;
x_29 = x_34;
goto block_33;
}
else
{
lean_inc(x_27);
lean_dec(x_21);
x_28 = lean_box(0);
x_29 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_30; 
if (x_29 == 0)
{
x_30 = x_28;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_27);
x_30 = x_32;
goto block_31;
}
block_31:
{
return x_30;
}
}
}
}
block_52:
{
size_t x_43; lean_object* x_44; 
x_43 = lean_array_size(x_42);
x_44 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__4(x_43, x_40, x_42);
if (x_38 == 0)
{
x_16 = x_40;
x_17 = x_41;
x_18 = x_44;
x_19 = lean_box(0);
goto block_35;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_45 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__7___closed__1));
x_46 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__7___closed__2));
x_47 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
lean_ctor_set_float(x_47, sizeof(void*)*2, x_2);
lean_ctor_set_float(x_47, sizeof(void*)*2 + 8, x_3);
lean_ctor_set_uint8(x_47, sizeof(void*)*2 + 16, x_38);
x_48 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__7___closed__4, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__7___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__7___closed__4);
x_49 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
lean_ctor_set(x_49, 2, x_44);
x_50 = lean_mk_empty_array_with_capacity(x_39);
x_51 = lean_array_push(x_50, x_49);
x_16 = x_40;
x_17 = x_41;
x_18 = x_51;
x_19 = lean_box(0);
goto block_35;
}
}
block_65:
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_57 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__7___closed__5));
x_58 = lean_array_get_size(x_56);
x_59 = lean_nat_dec_lt(x_14, x_58);
if (x_59 == 0)
{
lean_dec_ref(x_56);
x_39 = x_53;
x_40 = x_54;
x_41 = x_55;
x_42 = x_57;
goto block_52;
}
else
{
uint8_t x_60; 
x_60 = lean_nat_dec_le(x_58, x_58);
if (x_60 == 0)
{
if (x_59 == 0)
{
lean_dec_ref(x_56);
x_39 = x_53;
x_40 = x_54;
x_41 = x_55;
x_42 = x_57;
goto block_52;
}
else
{
size_t x_61; lean_object* x_62; 
x_61 = lean_usize_of_nat(x_58);
x_62 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Firefox_Profile_export_spec__5(x_56, x_54, x_61, x_57);
lean_dec_ref(x_56);
x_39 = x_53;
x_40 = x_54;
x_41 = x_55;
x_42 = x_62;
goto block_52;
}
}
else
{
size_t x_63; lean_object* x_64; 
x_63 = lean_usize_of_nat(x_58);
x_64 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Firefox_Profile_export_spec__5(x_56, x_54, x_63, x_57);
lean_dec_ref(x_56);
x_39 = x_53;
x_40 = x_54;
x_41 = x_55;
x_42 = x_64;
goto block_52;
}
}
}
block_74:
{
lean_object* x_73; 
lean_dec(x_70);
x_73 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__6___redArg(x_67, x_68, x_72);
lean_dec(x_72);
x_53 = x_66;
x_54 = x_69;
x_55 = x_71;
x_56 = x_73;
goto block_65;
}
block_83:
{
uint8_t x_82; 
x_82 = lean_nat_dec_le(x_81, x_75);
if (x_82 == 0)
{
lean_dec(x_75);
lean_inc(x_81);
x_66 = x_76;
x_67 = x_77;
x_68 = x_81;
x_69 = x_78;
x_70 = x_79;
x_71 = x_80;
x_72 = x_81;
goto block_74;
}
else
{
x_66 = x_76;
x_67 = x_77;
x_68 = x_81;
x_69 = x_78;
x_70 = x_79;
x_71 = x_80;
x_72 = x_75;
goto block_74;
}
}
block_114:
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; uint8_t x_113; 
x_85 = l_Lean_Firefox_Thread_new(x_84);
x_86 = lean_ctor_get(x_85, 0);
x_87 = lean_ctor_get(x_85, 1);
x_88 = lean_ctor_get(x_85, 2);
x_89 = lean_ctor_get(x_85, 3);
x_90 = lean_ctor_get(x_85, 4);
x_91 = lean_ctor_get(x_85, 5);
x_92 = lean_ctor_get(x_85, 6);
x_93 = lean_ctor_get(x_85, 7);
x_94 = lean_ctor_get(x_85, 8);
x_95 = lean_ctor_get(x_85, 9);
x_113 = !lean_is_exclusive(x_85);
if (x_113 == 0)
{
x_96 = x_85;
x_97 = x_113;
goto block_112;
}
else
{
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_85);
x_96 = lean_box(0);
x_97 = x_113;
goto block_112;
}
block_112:
{
lean_object* x_98; 
if (x_97 == 0)
{
x_98 = x_96;
goto block_110;
}
else
{
lean_object* x_111; 
x_111 = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(x_111, 0, x_86);
lean_ctor_set(x_111, 1, x_87);
lean_ctor_set(x_111, 2, x_88);
lean_ctor_set(x_111, 3, x_89);
lean_ctor_set(x_111, 4, x_90);
lean_ctor_set(x_111, 5, x_91);
lean_ctor_set(x_111, 6, x_92);
lean_ctor_set(x_111, 7, x_93);
lean_ctor_set(x_111, 8, x_94);
lean_ctor_set(x_111, 9, x_95);
x_98 = x_111;
goto block_110;
}
block_110:
{
lean_object* x_99; double x_100; lean_object* x_101; size_t x_102; size_t x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; 
lean_ctor_set_uint8(x_98, sizeof(void*)*10, x_38);
x_99 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__7___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__7___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__7___closed__7);
x_100 = lean_float_once(&l___private_Lean_Util_Profiler_0__Lean_Firefox_getFirstStart_x3f___closed__0, &l___private_Lean_Util_Profiler_0__Lean_Firefox_getFirstStart_x3f___closed__0_once, _init_l___private_Lean_Util_Profiler_0__Lean_Firefox_getFirstStart_x3f___closed__0);
x_101 = lean_alloc_ctor(0, 4, 8);
lean_ctor_set(x_101, 0, x_98);
lean_ctor_set(x_101, 1, x_99);
lean_ctor_set(x_101, 2, x_99);
lean_ctor_set(x_101, 3, x_99);
lean_ctor_set_float(x_101, sizeof(void*)*4, x_100);
x_102 = lean_array_size(x_13);
x_103 = 0;
x_104 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__1(x_102, x_103, x_13);
x_105 = lean_unsigned_to_nat(1u);
x_106 = lean_array_get_size(x_104);
x_107 = lean_nat_dec_eq(x_106, x_14);
if (x_107 == 0)
{
lean_object* x_108; uint8_t x_109; 
x_108 = lean_nat_sub(x_106, x_105);
x_109 = lean_nat_dec_le(x_14, x_108);
if (x_109 == 0)
{
lean_inc(x_108);
x_75 = x_108;
x_76 = x_105;
x_77 = x_104;
x_78 = x_103;
x_79 = x_106;
x_80 = x_101;
x_81 = x_108;
goto block_83;
}
else
{
x_75 = x_108;
x_76 = x_105;
x_77 = x_104;
x_78 = x_103;
x_79 = x_106;
x_80 = x_101;
x_81 = x_14;
goto block_83;
}
}
else
{
x_53 = x_105;
x_54 = x_103;
x_55 = x_101;
x_56 = x_104;
goto block_65;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
double x_9; double x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_9 = lean_unbox_float(x_2);
lean_dec_ref(x_2);
x_10 = lean_unbox_float(x_3);
lean_dec_ref(x_3);
x_11 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_12 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_13 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__7(x_1, x_9, x_10, x_4, x_11, x_12, x_7);
lean_dec_ref(x_1);
return x_13;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__2___redArg(uint64_t x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint64_t x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_unbox_uint64(x_4);
x_7 = lean_uint64_dec_eq(x_6, x_1);
if (x_7 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox_uint64(x_1);
lean_dec_ref(x_1);
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__2___redArg(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__4___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_7; 
x_7 = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__4___redArg___lam__0___closed__0));
x_3 = x_7;
goto block_6;
}
else
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec_ref(x_2);
x_3 = x_8;
goto block_6;
}
block_6:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_array_push(x_3, x_1);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__4___redArg(lean_object* x_1, uint64_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_box(0);
x_5 = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__4___redArg___lam__0(x_1, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_box_uint64(x_2);
x_8 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
lean_ctor_set(x_8, 2, x_3);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_28; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
x_11 = lean_ctor_get(x_3, 2);
x_28 = !lean_is_exclusive(x_3);
if (x_28 == 0)
{
x_12 = x_3;
x_13 = x_28;
goto block_27;
}
else
{
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_3);
x_12 = lean_box(0);
x_13 = x_28;
goto block_27;
}
block_27:
{
uint64_t x_14; uint8_t x_15; 
x_14 = lean_unbox_uint64(x_9);
x_15 = lean_uint64_dec_eq(x_14, x_2);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__4___redArg(x_1, x_2, x_11);
if (x_13 == 0)
{
lean_ctor_set(x_12, 2, x_16);
x_17 = x_12;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_19, 0, x_9);
lean_ctor_set(x_19, 1, x_10);
lean_ctor_set(x_19, 2, x_16);
x_17 = x_19;
goto block_18;
}
block_18:
{
return x_17;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_9);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_10);
x_21 = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__4___redArg___lam__0(x_1, x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_box_uint64(x_2);
if (x_13 == 0)
{
lean_ctor_set(x_12, 1, x_22);
lean_ctor_set(x_12, 0, x_23);
x_24 = x_12;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_22);
lean_ctor_set(x_26, 2, x_11);
x_24 = x_26;
goto block_25;
}
block_25:
{
return x_24;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint64(x_2);
lean_dec_ref(x_2);
x_5 = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__4___redArg(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__3_spec__14_spec__16___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_29; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
x_29 = !lean_is_exclusive(x_2);
if (x_29 == 0)
{
x_6 = x_2;
x_7 = x_29;
goto block_28;
}
else
{
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_2);
x_6 = lean_box(0);
x_7 = x_29;
goto block_28;
}
block_28:
{
lean_object* x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; size_t x_17; size_t x_18; size_t x_19; size_t x_20; size_t x_21; lean_object* x_22; lean_object* x_23; 
x_8 = lean_array_get_size(x_1);
x_9 = 32;
x_10 = lean_unbox_uint64(x_3);
x_11 = lean_uint64_shift_right(x_10, x_9);
x_12 = lean_unbox_uint64(x_3);
x_13 = lean_uint64_xor(x_12, x_11);
x_14 = 16;
x_15 = lean_uint64_shift_right(x_13, x_14);
x_16 = lean_uint64_xor(x_13, x_15);
x_17 = lean_uint64_to_usize(x_16);
x_18 = lean_usize_of_nat(x_8);
x_19 = 1;
x_20 = lean_usize_sub(x_18, x_19);
x_21 = lean_usize_land(x_17, x_20);
x_22 = lean_array_uget_borrowed(x_1, x_21);
lean_inc(x_22);
if (x_7 == 0)
{
lean_ctor_set(x_6, 2, x_22);
x_23 = x_6;
goto block_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_27, 0, x_3);
lean_ctor_set(x_27, 1, x_4);
lean_ctor_set(x_27, 2, x_22);
x_23 = x_27;
goto block_26;
}
block_26:
{
lean_object* x_24; 
x_24 = lean_array_uset(x_1, x_21, x_23);
x_1 = x_24;
x_2 = x_5;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__3_spec__14___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
if (x_5 == 0)
{
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__3_spec__14_spec__16___redArg(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__3___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_2, x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_4, x_6);
x_8 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__3_spec__14___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, uint64_t x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_55; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_55 = !lean_is_exclusive(x_2);
if (x_55 == 0)
{
x_6 = x_2;
x_7 = x_55;
goto block_54;
}
else
{
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_2);
x_6 = lean_box(0);
x_7 = x_55;
goto block_54;
}
block_54:
{
lean_object* x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; lean_object* x_20; uint8_t x_21; 
x_8 = lean_array_get_size(x_5);
x_9 = 32;
x_10 = lean_uint64_shift_right(x_3, x_9);
x_11 = lean_uint64_xor(x_3, x_10);
x_12 = 16;
x_13 = lean_uint64_shift_right(x_11, x_12);
x_14 = lean_uint64_xor(x_11, x_13);
x_15 = lean_uint64_to_usize(x_14);
x_16 = lean_usize_of_nat(x_8);
x_17 = 1;
x_18 = lean_usize_sub(x_16, x_17);
x_19 = lean_usize_land(x_15, x_18);
x_20 = lean_array_uget_borrowed(x_5, x_19);
x_21 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__2___redArg(x_3, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_22 = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__4___redArg___lam__0___closed__0));
x_23 = lean_array_push(x_22, x_1);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_4, x_24);
lean_dec(x_4);
x_26 = lean_box_uint64(x_3);
lean_inc(x_20);
x_27 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_23);
lean_ctor_set(x_27, 2, x_20);
x_28 = lean_array_uset(x_5, x_19, x_27);
x_29 = lean_unsigned_to_nat(4u);
x_30 = lean_nat_mul(x_25, x_29);
x_31 = lean_unsigned_to_nat(3u);
x_32 = lean_nat_div(x_30, x_31);
lean_dec(x_30);
x_33 = lean_array_get_size(x_28);
x_34 = lean_nat_dec_le(x_32, x_33);
lean_dec(x_32);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__3___redArg(x_28);
if (x_7 == 0)
{
lean_ctor_set(x_6, 1, x_35);
lean_ctor_set(x_6, 0, x_25);
x_36 = x_6;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_25);
lean_ctor_set(x_38, 1, x_35);
x_36 = x_38;
goto block_37;
}
block_37:
{
return x_36;
}
}
else
{
lean_object* x_39; 
if (x_7 == 0)
{
lean_ctor_set(x_6, 1, x_28);
lean_ctor_set(x_6, 0, x_25);
x_39 = x_6;
goto block_40;
}
else
{
lean_object* x_41; 
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_25);
lean_ctor_set(x_41, 1, x_28);
x_39 = x_41;
goto block_40;
}
block_40:
{
return x_39;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_51; 
lean_inc(x_20);
x_42 = lean_box(0);
x_43 = lean_array_uset(x_5, x_19, x_42);
x_44 = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__4___redArg(x_1, x_3, x_20);
x_51 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__2___redArg(x_3, x_44);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_unsigned_to_nat(1u);
x_53 = lean_nat_sub(x_4, x_52);
lean_dec(x_4);
x_45 = x_53;
goto block_50;
}
else
{
x_45 = x_4;
goto block_50;
}
block_50:
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_array_uset(x_43, x_19, x_44);
if (x_7 == 0)
{
lean_ctor_set(x_6, 1, x_46);
lean_ctor_set(x_6, 0, x_45);
x_47 = x_6;
goto block_48;
}
else
{
lean_object* x_49; 
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_45);
lean_ctor_set(x_49, 1, x_46);
x_47 = x_49;
goto block_48;
}
block_48:
{
return x_47;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint64(x_3);
lean_dec_ref(x_3);
x_5 = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0___redArg(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__1___redArg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_4, x_3);
if (x_6 == 0)
{
lean_dec_ref(x_1);
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; uint64_t x_9; lean_object* x_10; size_t x_11; size_t x_12; 
x_7 = lean_array_uget_borrowed(x_2, x_4);
lean_inc_ref(x_1);
lean_inc(x_7);
x_8 = lean_apply_1(x_1, x_7);
x_9 = lean_unbox_uint64(x_8);
lean_dec_ref(x_8);
lean_inc(x_7);
x_10 = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0___redArg(x_7, x_5, x_9);
x_11 = 1;
x_12 = lean_usize_add(x_4, x_11);
x_4 = x_12;
x_5 = x_10;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__1___redArg(x_1, x_2, x_6, x_7, x_5);
lean_dec_ref(x_2);
return x_8;
}
}
static lean_object* _init_l_Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0___redArg___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(16u);
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0___redArg___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0___redArg___closed__0, &l_Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0___redArg___closed__0_once, _init_l_Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0___redArg___closed__0);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_obj_once(&l_Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0___redArg___closed__1, &l_Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0___redArg___closed__1_once, _init_l_Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0___redArg___closed__1);
x_4 = lean_array_size(x_2);
x_5 = 0;
x_6 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__1___redArg(x_1, x_2, x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0___redArg(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__9___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; uint64_t x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_unbox_uint64(x_3);
x_6 = lean_unbox_uint64(x_4);
x_7 = lean_uint64_dec_lt(x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__9___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__9___redArg___lam__0(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__9___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_lt(x_2, x_3);
if (x_4 == 0)
{
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__9___redArg___closed__0));
lean_inc(x_2);
x_6 = l_Array_qpartition___redArg(x_1, x_5, x_2, x_3);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = lean_nat_dec_le(x_3, x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__9___redArg(x_8, x_2, x_7);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_7, x_11);
lean_dec(x_7);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
else
{
lean_dec(x_7);
lean_dec(x_2);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__9___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__9___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Firefox_Profile_export_spec__10(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_4);
lean_inc(x_3);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_4);
x_7 = lean_array_push(x_1, x_6);
x_1 = x_7;
x_2 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Firefox_Profile_export_spec__10___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Firefox_Profile_export_spec__10(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Firefox_Profile_export_spec__11(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget_borrowed(x_1, x_2);
x_7 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Firefox_Profile_export_spec__10(x_4, x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_2 = x_9;
x_4 = x_7;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Firefox_Profile_export_spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Firefox_Profile_export_spec__11(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__8(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_5 = lean_array_uget_borrowed(x_3, x_2);
x_6 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_6);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_8, x_2, x_6);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__8(x_4, x_5, x_3);
return x_6;
}
}
static double _init_l_Lean_Firefox_Profile_export___closed__1(void) {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(1000000000u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Firefox_Profile_export___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Firefox_Profile_export___closed__4));
x_2 = ((lean_object*)(l_Lean_Firefox_Profile_export___closed__3));
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Firefox_Profile_export(lean_object* x_1, double x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; double x_11; double x_12; double x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_66; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_6 = lean_io_mono_nanos_now();
x_7 = ((lean_object*)(l_Lean_Firefox_Profile_export___closed__0));
x_8 = l_Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0___redArg(x_7, x_3);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc_ref(x_10);
lean_dec_ref(x_8);
x_11 = lean_float_of_nat(x_6);
x_12 = lean_float_once(&l_Lean_Firefox_Profile_export___closed__1, &l_Lean_Firefox_Profile_export___closed__1_once, _init_l_Lean_Firefox_Profile_export___closed__1);
x_13 = lean_float_div(x_11, x_12);
x_74 = lean_mk_empty_array_with_capacity(x_9);
lean_dec(x_9);
x_75 = lean_unsigned_to_nat(0u);
x_76 = lean_array_get_size(x_10);
x_77 = lean_nat_dec_lt(x_75, x_76);
if (x_77 == 0)
{
lean_dec_ref(x_10);
x_66 = x_74;
goto block_73;
}
else
{
uint8_t x_78; 
x_78 = lean_nat_dec_le(x_76, x_76);
if (x_78 == 0)
{
if (x_77 == 0)
{
lean_dec_ref(x_10);
x_66 = x_74;
goto block_73;
}
else
{
size_t x_79; size_t x_80; lean_object* x_81; 
x_79 = 0;
x_80 = lean_usize_of_nat(x_76);
x_81 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Firefox_Profile_export_spec__11(x_10, x_79, x_80, x_74);
lean_dec_ref(x_10);
x_66 = x_81;
goto block_73;
}
}
else
{
size_t x_82; size_t x_83; lean_object* x_84; 
x_82 = 0;
x_83 = lean_usize_of_nat(x_76);
x_84 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Firefox_Profile_export_spec__11(x_10, x_82, x_83, x_74);
lean_dec_ref(x_10);
x_66 = x_84;
goto block_73;
}
}
block_49:
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = lean_array_size(x_16);
x_18 = 0;
x_19 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__7(x_4, x_2, x_13, x_1, x_17, x_18, x_16);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_40; 
x_20 = lean_ctor_get(x_19, 0);
x_40 = !lean_is_exclusive(x_19);
if (x_40 == 0)
{
x_21 = x_19;
x_22 = x_40;
goto block_39;
}
else
{
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_box(0);
x_22 = x_40;
goto block_39;
}
block_39:
{
uint8_t x_23; double x_24; double x_25; double x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; size_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_23 = 1;
x_24 = l_Float_ofScientific(x_14, x_23, x_15);
x_25 = lean_float_once(&l_Lean_Firefox_instCoeFloatMilliseconds___lam__0___closed__0, &l_Lean_Firefox_instCoeFloatMilliseconds___lam__0___closed__0_once, _init_l_Lean_Firefox_instCoeFloatMilliseconds___lam__0___closed__0);
x_26 = lean_float_mul(x_2, x_25);
x_27 = ((lean_object*)(l_Lean_Firefox_categories));
x_28 = ((lean_object*)(l_Lean_Firefox_Profile_export___closed__2));
x_29 = lean_unsigned_to_nat(48u);
x_30 = lean_mk_empty_array_with_capacity(x_14);
x_31 = lean_obj_once(&l_Lean_Firefox_Profile_export___closed__5, &l_Lean_Firefox_Profile_export___closed__5_once, _init_l_Lean_Firefox_Profile_export___closed__5);
lean_inc_ref(x_30);
x_32 = lean_alloc_ctor(0, 6, 16);
lean_ctor_set(x_32, 0, x_27);
lean_ctor_set(x_32, 1, x_14);
lean_ctor_set(x_32, 2, x_28);
lean_ctor_set(x_32, 3, x_29);
lean_ctor_set(x_32, 4, x_30);
lean_ctor_set(x_32, 5, x_31);
lean_ctor_set_float(x_32, sizeof(void*)*6, x_24);
lean_ctor_set_float(x_32, sizeof(void*)*6 + 8, x_26);
x_33 = lean_array_size(x_20);
x_34 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__8(x_33, x_18, x_20);
x_35 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_30);
lean_ctor_set(x_35, 2, x_34);
if (x_22 == 0)
{
lean_ctor_set(x_21, 0, x_35);
x_36 = x_21;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_35);
x_36 = x_38;
goto block_37;
}
block_37:
{
return x_36;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_48; 
lean_dec(x_15);
lean_dec(x_14);
x_41 = lean_ctor_get(x_19, 0);
x_48 = !lean_is_exclusive(x_19);
if (x_48 == 0)
{
x_42 = x_19;
x_43 = x_48;
goto block_47;
}
else
{
lean_inc(x_41);
lean_dec(x_19);
x_42 = lean_box(0);
x_43 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_44; 
if (x_43 == 0)
{
x_44 = x_42;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_41);
x_44 = x_46;
goto block_45;
}
block_45:
{
return x_44;
}
}
}
}
block_57:
{
lean_object* x_56; 
lean_dec(x_53);
x_56 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__9___redArg(x_51, x_50, x_55);
lean_dec(x_55);
x_14 = x_52;
x_15 = x_54;
x_16 = x_56;
goto block_49;
}
block_65:
{
uint8_t x_64; 
x_64 = lean_nat_dec_le(x_63, x_58);
if (x_64 == 0)
{
lean_dec(x_58);
lean_inc(x_63);
x_50 = x_63;
x_51 = x_59;
x_52 = x_60;
x_53 = x_61;
x_54 = x_62;
x_55 = x_63;
goto block_57;
}
else
{
x_50 = x_63;
x_51 = x_59;
x_52 = x_60;
x_53 = x_61;
x_54 = x_62;
x_55 = x_58;
goto block_57;
}
}
block_73:
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_67 = lean_unsigned_to_nat(0u);
x_68 = lean_unsigned_to_nat(1u);
x_69 = lean_array_get_size(x_66);
x_70 = lean_nat_dec_eq(x_69, x_67);
if (x_70 == 0)
{
lean_object* x_71; uint8_t x_72; 
x_71 = lean_nat_sub(x_69, x_68);
x_72 = lean_nat_dec_le(x_67, x_71);
if (x_72 == 0)
{
lean_inc(x_71);
x_58 = x_71;
x_59 = x_66;
x_60 = x_67;
x_61 = x_69;
x_62 = x_68;
x_63 = x_71;
goto block_65;
}
else
{
x_58 = x_71;
x_59 = x_66;
x_60 = x_67;
x_61 = x_69;
x_62 = x_68;
x_63 = x_67;
goto block_65;
}
}
else
{
x_14 = x_67;
x_15 = x_68;
x_16 = x_66;
goto block_49;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Firefox_Profile_export___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
double x_6; lean_object* x_7; 
x_6 = lean_unbox_float(x_2);
lean_dec_ref(x_2);
x_7 = l_Lean_Firefox_Profile_export(x_1, x_6, x_3, x_4);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0(x_1, x_2, x_3);
lean_dec_ref(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__6___redArg(x_2, x_3, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__9___redArg(x_2, x_3, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__9(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint64_t x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint64_t x_5; lean_object* x_6; 
x_5 = lean_unbox_uint64(x_4);
lean_dec_ref(x_4);
x_6 = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0(x_1, x_2, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__1___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__1(x_1, x_2, x_3, x_7, x_8, x_6);
lean_dec_ref(x_3);
return x_9;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__2(lean_object* x_1, uint64_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__2___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox_uint64(x_2);
lean_dec_ref(x_2);
x_5 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__2(x_1, x_4, x_3);
lean_dec(x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__3___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__4(lean_object* x_1, lean_object* x_2, uint64_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__4___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint64_t x_5; lean_object* x_6; 
x_5 = lean_unbox_uint64(x_3);
lean_dec_ref(x_3);
x_6 = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__4(x_1, x_2, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__3_spec__14(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__3_spec__14___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__3_spec__14_spec__16(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__3_spec__14_spec__16___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Profiler_0__Lean_Firefox_collideThreads_getStrIdx(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; double x_9; lean_object* x_10; uint8_t x_11; uint8_t x_50; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 2);
x_8 = lean_ctor_get(x_3, 3);
x_9 = lean_ctor_get_float(x_3, sizeof(void*)*4);
x_50 = !lean_is_exclusive(x_3);
if (x_50 == 0)
{
x_10 = x_3;
x_11 = x_50;
goto block_49;
}
else
{
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_3);
x_10 = lean_box(0);
x_11 = x_50;
goto block_49;
}
block_49:
{
lean_object* x_12; 
x_12 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__5___redArg(x_6, x_1);
if (lean_obj_tag(x_12) == 1)
{
lean_object* x_13; lean_object* x_14; 
lean_del_object(x_10);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_2);
return x_14;
}
else
{
lean_object* x_15; uint8_t x_16; uint8_t x_46; 
lean_inc_ref(x_4);
lean_dec(x_12);
x_46 = !lean_is_exclusive(x_2);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_2, 1);
lean_dec(x_47);
x_48 = lean_ctor_get(x_2, 0);
lean_dec(x_48);
x_15 = x_2;
x_16 = x_46;
goto block_45;
}
else
{
lean_dec(x_2);
x_15 = lean_box(0);
x_16 = x_46;
goto block_45;
}
block_45:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_44; 
x_17 = lean_ctor_get(x_6, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_5, 0);
x_19 = lean_ctor_get(x_5, 1);
x_20 = lean_ctor_get_uint8(x_5, sizeof(void*)*10);
x_21 = lean_ctor_get(x_5, 2);
x_22 = lean_ctor_get(x_5, 3);
x_23 = lean_ctor_get(x_5, 4);
x_24 = lean_ctor_get(x_5, 5);
x_25 = lean_ctor_get(x_5, 6);
x_26 = lean_ctor_get(x_5, 7);
x_27 = lean_ctor_get(x_5, 8);
x_28 = lean_ctor_get(x_5, 9);
x_44 = !lean_is_exclusive(x_5);
if (x_44 == 0)
{
x_29 = x_5;
x_30 = x_44;
goto block_43;
}
else
{
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_5);
x_29 = lean_box(0);
x_30 = x_44;
goto block_43;
}
block_43:
{
lean_object* x_31; lean_object* x_32; 
lean_inc_ref(x_1);
x_31 = lean_array_push(x_27, x_1);
if (x_30 == 0)
{
lean_ctor_set(x_29, 8, x_31);
x_32 = x_29;
goto block_41;
}
else
{
lean_object* x_42; 
x_42 = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(x_42, 0, x_18);
lean_ctor_set(x_42, 1, x_19);
lean_ctor_set(x_42, 2, x_21);
lean_ctor_set(x_42, 3, x_22);
lean_ctor_set(x_42, 4, x_23);
lean_ctor_set(x_42, 5, x_24);
lean_ctor_set(x_42, 6, x_25);
lean_ctor_set(x_42, 7, x_26);
lean_ctor_set(x_42, 8, x_31);
lean_ctor_set(x_42, 9, x_28);
lean_ctor_set_uint8(x_42, sizeof(void*)*10, x_20);
x_32 = x_42;
goto block_41;
}
block_41:
{
lean_object* x_33; lean_object* x_34; 
lean_inc(x_17);
x_33 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__6___redArg(x_6, x_1, x_17);
if (x_11 == 0)
{
lean_ctor_set(x_10, 1, x_33);
lean_ctor_set(x_10, 0, x_32);
x_34 = x_10;
goto block_39;
}
else
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(0, 4, 8);
lean_ctor_set(x_40, 0, x_32);
lean_ctor_set(x_40, 1, x_33);
lean_ctor_set(x_40, 2, x_7);
lean_ctor_set(x_40, 3, x_8);
lean_ctor_set_float(x_40, sizeof(void*)*4, x_9);
x_34 = x_40;
goto block_39;
}
block_39:
{
lean_object* x_35; 
if (x_16 == 0)
{
lean_ctor_set(x_15, 0, x_34);
x_35 = x_15;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_34);
lean_ctor_set(x_38, 1, x_4);
x_35 = x_38;
goto block_37;
}
block_37:
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_17);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Profiler_0__Lean_Firefox_collideThreads_collideStacks(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; double x_21; lean_object* x_22; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_155; 
x_4 = lean_ctor_get(x_1, 4);
x_5 = lean_ctor_get(x_1, 5);
x_6 = lean_ctor_get(x_1, 8);
x_7 = lean_ctor_get(x_1, 9);
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_ctor_get(x_4, 1);
x_10 = lean_ctor_get(x_4, 2);
x_11 = lean_ctor_get(x_4, 3);
x_12 = lean_box(0);
x_13 = lean_unsigned_to_nat(0u);
x_71 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__7___closed__2));
x_155 = lean_array_get(x_12, x_11, x_2);
if (lean_obj_tag(x_155) == 0)
{
x_72 = x_155;
x_73 = x_3;
goto block_154;
}
else
{
lean_object* x_156; lean_object* x_157; uint8_t x_158; uint8_t x_166; 
x_156 = lean_ctor_get(x_155, 0);
x_166 = !lean_is_exclusive(x_155);
if (x_166 == 0)
{
x_157 = x_155;
x_158 = x_166;
goto block_165;
}
else
{
lean_inc(x_156);
lean_dec(x_155);
x_157 = lean_box(0);
x_158 = x_166;
goto block_165;
}
block_165:
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_159 = l___private_Lean_Util_Profiler_0__Lean_Firefox_collideThreads_collideStacks(x_1, x_156, x_3);
lean_dec(x_156);
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
lean_dec_ref(x_159);
if (x_158 == 0)
{
lean_ctor_set(x_157, 0, x_160);
x_162 = x_157;
goto block_163;
}
else
{
lean_object* x_164; 
x_164 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_164, 0, x_160);
x_162 = x_164;
goto block_163;
}
block_163:
{
x_72 = x_162;
x_73 = x_161;
goto block_154;
}
}
}
block_70:
{
lean_object* x_23; lean_object* x_24; 
lean_inc(x_14);
lean_inc(x_15);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_15);
lean_ctor_set(x_23, 1, x_14);
x_24 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__1___redArg(x_20, x_23);
if (lean_obj_tag(x_24) == 1)
{
lean_object* x_25; lean_object* x_26; 
lean_dec_ref(x_23);
lean_dec_ref(x_22);
lean_dec_ref(x_20);
lean_dec_ref(x_19);
lean_dec_ref(x_18);
lean_dec_ref(x_17);
lean_dec(x_15);
lean_dec(x_14);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec_ref(x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_16);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_69; 
lean_dec(x_24);
lean_dec_ref(x_16);
x_27 = lean_ctor_get(x_17, 4);
x_28 = lean_ctor_get(x_17, 0);
x_29 = lean_ctor_get(x_17, 1);
x_30 = lean_ctor_get_uint8(x_17, sizeof(void*)*10);
x_31 = lean_ctor_get(x_17, 2);
x_32 = lean_ctor_get(x_17, 3);
x_33 = lean_ctor_get(x_17, 5);
x_34 = lean_ctor_get(x_17, 6);
x_35 = lean_ctor_get(x_17, 7);
x_36 = lean_ctor_get(x_17, 8);
x_37 = lean_ctor_get(x_17, 9);
x_69 = !lean_is_exclusive(x_17);
if (x_69 == 0)
{
x_38 = x_17;
x_39 = x_69;
goto block_68;
}
else
{
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_27);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_17);
x_38 = lean_box(0);
x_39 = x_69;
goto block_68;
}
block_68:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; uint8_t x_67; 
x_40 = lean_ctor_get(x_27, 0);
x_41 = lean_ctor_get(x_27, 1);
x_42 = lean_ctor_get(x_27, 2);
x_43 = lean_ctor_get(x_27, 3);
x_44 = lean_ctor_get(x_27, 4);
x_67 = !lean_is_exclusive(x_27);
if (x_67 == 0)
{
x_45 = x_27;
x_46 = x_67;
goto block_66;
}
else
{
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_27);
x_45 = lean_box(0);
x_46 = x_67;
goto block_66;
}
block_66:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_47 = lean_ctor_get(x_20, 0);
lean_inc(x_47);
x_48 = lean_array_push(x_40, x_15);
x_49 = lean_array_get_borrowed(x_13, x_9, x_2);
lean_inc(x_49);
x_50 = lean_array_push(x_41, x_49);
x_51 = lean_array_get_borrowed(x_13, x_10, x_2);
lean_inc(x_51);
x_52 = lean_array_push(x_42, x_51);
x_53 = lean_array_push(x_43, x_14);
x_54 = lean_unsigned_to_nat(1u);
x_55 = lean_nat_add(x_44, x_54);
lean_dec(x_44);
if (x_46 == 0)
{
lean_ctor_set(x_45, 4, x_55);
lean_ctor_set(x_45, 3, x_53);
lean_ctor_set(x_45, 2, x_52);
lean_ctor_set(x_45, 1, x_50);
lean_ctor_set(x_45, 0, x_48);
x_56 = x_45;
goto block_64;
}
else
{
lean_object* x_65; 
x_65 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_65, 0, x_48);
lean_ctor_set(x_65, 1, x_50);
lean_ctor_set(x_65, 2, x_52);
lean_ctor_set(x_65, 3, x_53);
lean_ctor_set(x_65, 4, x_55);
x_56 = x_65;
goto block_64;
}
block_64:
{
lean_object* x_57; lean_object* x_58; 
lean_inc(x_47);
x_57 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__2___redArg(x_20, x_23, x_47);
if (x_39 == 0)
{
lean_ctor_set(x_38, 4, x_56);
x_58 = x_38;
goto block_62;
}
else
{
lean_object* x_63; 
x_63 = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(x_63, 0, x_28);
lean_ctor_set(x_63, 1, x_29);
lean_ctor_set(x_63, 2, x_31);
lean_ctor_set(x_63, 3, x_32);
lean_ctor_set(x_63, 4, x_56);
lean_ctor_set(x_63, 5, x_33);
lean_ctor_set(x_63, 6, x_34);
lean_ctor_set(x_63, 7, x_35);
lean_ctor_set(x_63, 8, x_36);
lean_ctor_set(x_63, 9, x_37);
lean_ctor_set_uint8(x_63, sizeof(void*)*10, x_30);
x_58 = x_63;
goto block_62;
}
block_62:
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_alloc_ctor(0, 4, 8);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_18);
lean_ctor_set(x_59, 2, x_19);
lean_ctor_set(x_59, 3, x_57);
lean_ctor_set_float(x_59, sizeof(void*)*4, x_21);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_22);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_47);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
}
}
}
block_154:
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; double x_89; lean_object* x_90; uint8_t x_91; uint8_t x_153; 
x_74 = lean_ctor_get(x_5, 4);
x_75 = lean_ctor_get(x_7, 0);
x_76 = lean_array_get_borrowed(x_13, x_8, x_2);
x_77 = lean_array_get_borrowed(x_13, x_74, x_76);
x_78 = lean_array_get_borrowed(x_13, x_75, x_77);
x_79 = lean_array_get_borrowed(x_71, x_6, x_78);
lean_inc(x_79);
x_80 = l___private_Lean_Util_Profiler_0__Lean_Firefox_collideThreads_getStrIdx(x_79, x_73);
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
x_82 = lean_ctor_get(x_81, 0);
lean_inc_ref(x_82);
x_83 = lean_ctor_get(x_80, 0);
lean_inc(x_83);
lean_dec_ref(x_80);
x_84 = lean_ctor_get(x_81, 1);
lean_inc_ref(x_84);
x_85 = lean_ctor_get(x_82, 0);
x_86 = lean_ctor_get(x_82, 1);
x_87 = lean_ctor_get(x_82, 2);
x_88 = lean_ctor_get(x_82, 3);
x_89 = lean_ctor_get_float(x_82, sizeof(void*)*4);
x_153 = !lean_is_exclusive(x_82);
if (x_153 == 0)
{
x_90 = x_82;
x_91 = x_153;
goto block_152;
}
else
{
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_82);
x_90 = lean_box(0);
x_91 = x_153;
goto block_152;
}
block_152:
{
lean_object* x_92; 
x_92 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__3___redArg(x_87, x_83);
if (lean_obj_tag(x_92) == 1)
{
lean_object* x_93; 
lean_del_object(x_90);
lean_dec(x_83);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
lean_dec_ref(x_92);
x_14 = x_72;
x_15 = x_93;
x_16 = x_81;
x_17 = x_85;
x_18 = x_86;
x_19 = x_87;
x_20 = x_88;
x_21 = x_89;
x_22 = x_84;
goto block_70;
}
else
{
lean_object* x_94; uint8_t x_95; uint8_t x_149; 
lean_dec(x_92);
x_149 = !lean_is_exclusive(x_81);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; 
x_150 = lean_ctor_get(x_81, 1);
lean_dec(x_150);
x_151 = lean_ctor_get(x_81, 0);
lean_dec(x_151);
x_94 = x_81;
x_95 = x_149;
goto block_148;
}
else
{
lean_dec(x_81);
x_94 = lean_box(0);
x_95 = x_149;
goto block_148;
}
block_148:
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; uint8_t x_147; 
x_96 = lean_ctor_get(x_87, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_85, 0);
x_98 = lean_ctor_get(x_85, 1);
x_99 = lean_ctor_get_uint8(x_85, sizeof(void*)*10);
x_100 = lean_ctor_get(x_85, 2);
x_101 = lean_ctor_get(x_85, 3);
x_102 = lean_ctor_get(x_85, 4);
x_103 = lean_ctor_get(x_85, 5);
x_104 = lean_ctor_get(x_85, 6);
x_105 = lean_ctor_get(x_85, 7);
x_106 = lean_ctor_get(x_85, 8);
x_107 = lean_ctor_get(x_85, 9);
x_147 = !lean_is_exclusive(x_85);
if (x_147 == 0)
{
x_108 = x_85;
x_109 = x_147;
goto block_146;
}
else
{
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_85);
x_108 = lean_box(0);
x_109 = x_147;
goto block_146;
}
block_146:
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; uint8_t x_143; 
x_110 = lean_unsigned_to_nat(1u);
x_111 = lean_obj_once(&l___private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go___closed__2, &l___private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go___closed__2_once, _init_l___private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go___closed__2);
lean_inc(x_96);
x_112 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_13);
lean_ctor_set(x_112, 2, x_12);
lean_ctor_set(x_112, 3, x_12);
lean_ctor_set(x_112, 4, x_96);
lean_ctor_set(x_112, 5, x_12);
lean_ctor_set(x_112, 6, x_12);
lean_ctor_set(x_112, 7, x_12);
lean_ctor_set(x_112, 8, x_12);
lean_ctor_set(x_112, 9, x_12);
x_113 = lean_ctor_get(x_107, 0);
x_114 = lean_ctor_get(x_107, 3);
x_115 = lean_ctor_get(x_107, 4);
x_116 = lean_ctor_get(x_107, 5);
x_117 = lean_ctor_get(x_107, 6);
x_118 = lean_ctor_get(x_107, 7);
x_143 = !lean_is_exclusive(x_107);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; 
x_144 = lean_ctor_get(x_107, 2);
lean_dec(x_144);
x_145 = lean_ctor_get(x_107, 1);
lean_dec(x_145);
x_119 = x_107;
x_120 = x_143;
goto block_142;
}
else
{
lean_inc(x_118);
lean_inc(x_117);
lean_inc(x_116);
lean_inc(x_115);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_107);
x_119 = lean_box(0);
x_120 = x_143;
goto block_142;
}
block_142:
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_121 = l_Lean_Firefox_FrameTable_push(x_103, x_112);
lean_inc(x_83);
x_122 = lean_array_push(x_113, x_83);
x_123 = ((lean_object*)(l___private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go___closed__3));
x_124 = lean_array_push(x_114, x_111);
x_125 = lean_array_push(x_115, x_12);
x_126 = lean_array_push(x_116, x_12);
x_127 = lean_array_push(x_117, x_12);
x_128 = lean_nat_add(x_118, x_110);
lean_dec(x_118);
if (x_120 == 0)
{
lean_ctor_set(x_119, 7, x_128);
lean_ctor_set(x_119, 6, x_127);
lean_ctor_set(x_119, 5, x_126);
lean_ctor_set(x_119, 4, x_125);
lean_ctor_set(x_119, 3, x_124);
lean_ctor_set(x_119, 2, x_123);
lean_ctor_set(x_119, 1, x_123);
lean_ctor_set(x_119, 0, x_122);
x_129 = x_119;
goto block_140;
}
else
{
lean_object* x_141; 
x_141 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_141, 0, x_122);
lean_ctor_set(x_141, 1, x_123);
lean_ctor_set(x_141, 2, x_123);
lean_ctor_set(x_141, 3, x_124);
lean_ctor_set(x_141, 4, x_125);
lean_ctor_set(x_141, 5, x_126);
lean_ctor_set(x_141, 6, x_127);
lean_ctor_set(x_141, 7, x_128);
x_129 = x_141;
goto block_140;
}
block_140:
{
lean_object* x_130; 
if (x_109 == 0)
{
lean_ctor_set(x_108, 9, x_129);
lean_ctor_set(x_108, 5, x_121);
x_130 = x_108;
goto block_138;
}
else
{
lean_object* x_139; 
x_139 = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(x_139, 0, x_97);
lean_ctor_set(x_139, 1, x_98);
lean_ctor_set(x_139, 2, x_100);
lean_ctor_set(x_139, 3, x_101);
lean_ctor_set(x_139, 4, x_102);
lean_ctor_set(x_139, 5, x_121);
lean_ctor_set(x_139, 6, x_104);
lean_ctor_set(x_139, 7, x_105);
lean_ctor_set(x_139, 8, x_106);
lean_ctor_set(x_139, 9, x_129);
lean_ctor_set_uint8(x_139, sizeof(void*)*10, x_99);
x_130 = x_139;
goto block_138;
}
block_138:
{
lean_object* x_131; lean_object* x_132; 
lean_inc(x_96);
x_131 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__4___redArg(x_87, x_83, x_96);
lean_inc_ref(x_88);
lean_inc_ref(x_131);
lean_inc_ref(x_86);
lean_inc_ref(x_130);
if (x_91 == 0)
{
lean_ctor_set(x_90, 2, x_131);
lean_ctor_set(x_90, 0, x_130);
x_132 = x_90;
goto block_136;
}
else
{
lean_object* x_137; 
x_137 = lean_alloc_ctor(0, 4, 8);
lean_ctor_set(x_137, 0, x_130);
lean_ctor_set(x_137, 1, x_86);
lean_ctor_set(x_137, 2, x_131);
lean_ctor_set(x_137, 3, x_88);
lean_ctor_set_float(x_137, sizeof(void*)*4, x_89);
x_132 = x_137;
goto block_136;
}
block_136:
{
lean_object* x_133; 
lean_inc_ref(x_84);
if (x_95 == 0)
{
lean_ctor_set(x_94, 0, x_132);
x_133 = x_94;
goto block_134;
}
else
{
lean_object* x_135; 
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_132);
lean_ctor_set(x_135, 1, x_84);
x_133 = x_135;
goto block_134;
}
block_134:
{
x_14 = x_72;
x_15 = x_96;
x_16 = x_133;
x_17 = x_130;
x_18 = x_86;
x_19 = x_131;
x_20 = x_88;
x_21 = x_89;
x_22 = x_84;
goto block_70;
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
LEAN_EXPORT lean_object* l___private_Lean_Util_Profiler_0__Lean_Firefox_collideThreads_collideStacks___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Util_Profiler_0__Lean_Firefox_collideThreads_collideStacks(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_collideThreads_collideSamples_spec__0___redArg___boxed__const__1(void) {
_start:
{
double x_1; lean_object* x_2; 
x_1 = l_Lean_Firefox_instInhabitedMilliseconds_default;
x_2 = lean_box_float(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_collideThreads_collideSamples_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_13; 
x_13 = lean_nat_dec_lt(x_4, x_1);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_4);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_5);
lean_ctor_set(x_14, 1, x_6);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_154; 
x_15 = lean_ctor_get(x_2, 0);
x_16 = lean_ctor_get(x_2, 2);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_array_get_borrowed(x_17, x_15, x_4);
x_19 = l___private_Lean_Util_Profiler_0__Lean_Firefox_collideThreads_collideStacks(x_3, x_18, x_6);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec_ref(x_19);
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
x_154 = !lean_is_exclusive(x_20);
if (x_154 == 0)
{
x_24 = x_20;
x_25 = x_154;
goto block_153;
}
else
{
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_20);
x_24 = lean_box(0);
x_25 = x_154;
goto block_153;
}
block_153:
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_box(0);
x_27 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__3___redArg(x_23, x_21);
if (lean_obj_tag(x_27) == 1)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; double x_34; lean_object* x_35; uint8_t x_36; uint8_t x_84; 
lean_dec(x_21);
x_28 = lean_ctor_get(x_22, 0);
lean_inc_ref(x_28);
x_29 = lean_ctor_get(x_28, 2);
lean_inc_ref(x_29);
x_30 = lean_ctor_get(x_27, 0);
lean_inc(x_30);
lean_dec_ref(x_27);
x_31 = lean_ctor_get(x_22, 1);
x_32 = lean_ctor_get(x_22, 2);
x_33 = lean_ctor_get(x_22, 3);
x_34 = lean_ctor_get_float(x_22, sizeof(void*)*4);
x_84 = !lean_is_exclusive(x_22);
if (x_84 == 0)
{
lean_object* x_85; 
x_85 = lean_ctor_get(x_22, 0);
lean_dec(x_85);
x_35 = x_22;
x_36 = x_84;
goto block_83;
}
else
{
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_22);
x_35 = lean_box(0);
x_36 = x_84;
goto block_83;
}
block_83:
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_81; 
x_37 = lean_ctor_get(x_28, 0);
x_38 = lean_ctor_get(x_28, 1);
x_39 = lean_ctor_get_uint8(x_28, sizeof(void*)*10);
x_40 = lean_ctor_get(x_28, 3);
x_41 = lean_ctor_get(x_28, 4);
x_42 = lean_ctor_get(x_28, 5);
x_43 = lean_ctor_get(x_28, 6);
x_44 = lean_ctor_get(x_28, 7);
x_45 = lean_ctor_get(x_28, 8);
x_46 = lean_ctor_get(x_28, 9);
x_81 = !lean_is_exclusive(x_28);
if (x_81 == 0)
{
lean_object* x_82; 
x_82 = lean_ctor_get(x_28, 2);
lean_dec(x_82);
x_47 = x_28;
x_48 = x_81;
goto block_80;
}
else
{
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_28);
x_47 = lean_box(0);
x_48 = x_81;
goto block_80;
}
block_80:
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; uint8_t x_79; 
x_49 = lean_ctor_get(x_29, 0);
x_50 = lean_ctor_get(x_29, 1);
x_51 = lean_ctor_get(x_29, 2);
x_52 = lean_ctor_get(x_29, 3);
x_53 = lean_ctor_get(x_29, 4);
x_54 = lean_ctor_get(x_29, 5);
x_79 = !lean_is_exclusive(x_29);
if (x_79 == 0)
{
x_55 = x_29;
x_56 = x_79;
goto block_78;
}
else
{
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_29);
x_55 = lean_box(0);
x_56 = x_79;
goto block_78;
}
block_78:
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; double x_61; double x_62; double x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_57 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_collideThreads_collideSamples_spec__0___redArg___boxed__const__1;
x_58 = lean_array_get_borrowed(x_57, x_51, x_30);
x_59 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_collideThreads_collideSamples_spec__0___redArg___boxed__const__1;
x_60 = lean_array_get_borrowed(x_59, x_16, x_4);
x_61 = lean_unbox_float(x_58);
x_62 = lean_unbox_float(x_60);
x_63 = lean_float_add(x_61, x_62);
x_64 = lean_box_float(x_63);
x_65 = lean_array_set(x_51, x_30, x_64);
lean_dec(x_30);
if (x_56 == 0)
{
lean_ctor_set(x_55, 2, x_65);
x_66 = x_55;
goto block_76;
}
else
{
lean_object* x_77; 
x_77 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_77, 0, x_49);
lean_ctor_set(x_77, 1, x_50);
lean_ctor_set(x_77, 2, x_65);
lean_ctor_set(x_77, 3, x_52);
lean_ctor_set(x_77, 4, x_53);
lean_ctor_set(x_77, 5, x_54);
x_66 = x_77;
goto block_76;
}
block_76:
{
lean_object* x_67; 
if (x_48 == 0)
{
lean_ctor_set(x_47, 2, x_66);
x_67 = x_47;
goto block_74;
}
else
{
lean_object* x_75; 
x_75 = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(x_75, 0, x_37);
lean_ctor_set(x_75, 1, x_38);
lean_ctor_set(x_75, 2, x_66);
lean_ctor_set(x_75, 3, x_40);
lean_ctor_set(x_75, 4, x_41);
lean_ctor_set(x_75, 5, x_42);
lean_ctor_set(x_75, 6, x_43);
lean_ctor_set(x_75, 7, x_44);
lean_ctor_set(x_75, 8, x_45);
lean_ctor_set(x_75, 9, x_46);
lean_ctor_set_uint8(x_75, sizeof(void*)*10, x_39);
x_67 = x_75;
goto block_74;
}
block_74:
{
lean_object* x_68; 
if (x_36 == 0)
{
lean_ctor_set(x_35, 0, x_67);
x_68 = x_35;
goto block_72;
}
else
{
lean_object* x_73; 
x_73 = lean_alloc_ctor(0, 4, 8);
lean_ctor_set(x_73, 0, x_67);
lean_ctor_set(x_73, 1, x_31);
lean_ctor_set(x_73, 2, x_32);
lean_ctor_set(x_73, 3, x_33);
lean_ctor_set_float(x_73, sizeof(void*)*4, x_34);
x_68 = x_73;
goto block_72;
}
block_72:
{
lean_object* x_69; 
if (x_25 == 0)
{
lean_ctor_set(x_24, 0, x_68);
x_69 = x_24;
goto block_70;
}
else
{
lean_object* x_71; 
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_68);
lean_ctor_set(x_71, 1, x_23);
x_69 = x_71;
goto block_70;
}
block_70:
{
x_7 = x_26;
x_8 = x_69;
goto block_12;
}
}
}
}
}
}
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; double x_91; lean_object* x_92; uint8_t x_93; uint8_t x_151; 
lean_dec(x_27);
x_86 = lean_ctor_get(x_22, 0);
lean_inc_ref(x_86);
x_87 = lean_ctor_get(x_86, 2);
lean_inc_ref(x_87);
x_88 = lean_ctor_get(x_22, 1);
x_89 = lean_ctor_get(x_22, 2);
x_90 = lean_ctor_get(x_22, 3);
x_91 = lean_ctor_get_float(x_22, sizeof(void*)*4);
x_151 = !lean_is_exclusive(x_22);
if (x_151 == 0)
{
lean_object* x_152; 
x_152 = lean_ctor_get(x_22, 0);
lean_dec(x_152);
x_92 = x_22;
x_93 = x_151;
goto block_150;
}
else
{
lean_inc(x_90);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_22);
x_92 = lean_box(0);
x_93 = x_151;
goto block_150;
}
block_150:
{
lean_object* x_94; lean_object* x_95; uint8_t x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; uint8_t x_148; 
x_94 = lean_ctor_get(x_86, 0);
x_95 = lean_ctor_get(x_86, 1);
x_96 = lean_ctor_get_uint8(x_86, sizeof(void*)*10);
x_97 = lean_ctor_get(x_86, 3);
x_98 = lean_ctor_get(x_86, 4);
x_99 = lean_ctor_get(x_86, 5);
x_100 = lean_ctor_get(x_86, 6);
x_101 = lean_ctor_get(x_86, 7);
x_102 = lean_ctor_get(x_86, 8);
x_103 = lean_ctor_get(x_86, 9);
x_148 = !lean_is_exclusive(x_86);
if (x_148 == 0)
{
lean_object* x_149; 
x_149 = lean_ctor_get(x_86, 2);
lean_dec(x_149);
x_104 = x_86;
x_105 = x_148;
goto block_147;
}
else
{
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_86);
x_104 = lean_box(0);
x_105 = x_148;
goto block_147;
}
block_147:
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; uint8_t x_145; 
x_106 = lean_ctor_get(x_87, 0);
x_107 = lean_ctor_get(x_87, 1);
x_108 = lean_ctor_get(x_87, 2);
x_109 = lean_ctor_get(x_87, 4);
x_110 = lean_ctor_get(x_87, 5);
x_145 = !lean_is_exclusive(x_87);
if (x_145 == 0)
{
lean_object* x_146; 
x_146 = lean_ctor_get(x_87, 3);
lean_dec(x_146);
x_111 = x_87;
x_112 = x_145;
goto block_144;
}
else
{
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_87);
x_111 = lean_box(0);
x_112 = x_145;
goto block_144;
}
block_144:
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; double x_116; double x_117; double x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; double x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_113 = lean_ctor_get(x_23, 0);
lean_inc(x_113);
x_114 = lean_array_get_size(x_107);
lean_inc(x_21);
x_115 = lean_array_push(x_106, x_21);
x_116 = lean_float_of_nat(x_114);
x_117 = lean_float_once(&l_Lean_Firefox_instCoeFloatMilliseconds___lam__0___closed__0, &l_Lean_Firefox_instCoeFloatMilliseconds___lam__0___closed__0_once, _init_l_Lean_Firefox_instCoeFloatMilliseconds___lam__0___closed__0);
x_118 = lean_float_mul(x_116, x_117);
x_119 = lean_box_float(x_118);
x_120 = lean_array_push(x_107, x_119);
x_121 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_collideThreads_collideSamples_spec__0___redArg___boxed__const__1;
x_122 = lean_array_get_borrowed(x_121, x_16, x_4);
lean_inc(x_122);
x_123 = lean_array_push(x_108, x_122);
x_124 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__0___closed__0));
x_125 = lean_unsigned_to_nat(10u);
x_126 = lean_unsigned_to_nat(1u);
x_127 = l_Float_ofScientific(x_125, x_13, x_126);
x_128 = lean_box_float(x_127);
x_129 = lean_array_push(x_109, x_128);
x_130 = lean_nat_add(x_110, x_126);
lean_dec(x_110);
if (x_112 == 0)
{
lean_ctor_set(x_111, 5, x_130);
lean_ctor_set(x_111, 4, x_129);
lean_ctor_set(x_111, 3, x_124);
lean_ctor_set(x_111, 2, x_123);
lean_ctor_set(x_111, 1, x_120);
lean_ctor_set(x_111, 0, x_115);
x_131 = x_111;
goto block_142;
}
else
{
lean_object* x_143; 
x_143 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_143, 0, x_115);
lean_ctor_set(x_143, 1, x_120);
lean_ctor_set(x_143, 2, x_123);
lean_ctor_set(x_143, 3, x_124);
lean_ctor_set(x_143, 4, x_129);
lean_ctor_set(x_143, 5, x_130);
x_131 = x_143;
goto block_142;
}
block_142:
{
lean_object* x_132; lean_object* x_133; 
x_132 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__4___redArg(x_23, x_21, x_113);
if (x_105 == 0)
{
lean_ctor_set(x_104, 2, x_131);
x_133 = x_104;
goto block_140;
}
else
{
lean_object* x_141; 
x_141 = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(x_141, 0, x_94);
lean_ctor_set(x_141, 1, x_95);
lean_ctor_set(x_141, 2, x_131);
lean_ctor_set(x_141, 3, x_97);
lean_ctor_set(x_141, 4, x_98);
lean_ctor_set(x_141, 5, x_99);
lean_ctor_set(x_141, 6, x_100);
lean_ctor_set(x_141, 7, x_101);
lean_ctor_set(x_141, 8, x_102);
lean_ctor_set(x_141, 9, x_103);
lean_ctor_set_uint8(x_141, sizeof(void*)*10, x_96);
x_133 = x_141;
goto block_140;
}
block_140:
{
lean_object* x_134; 
if (x_93 == 0)
{
lean_ctor_set(x_92, 0, x_133);
x_134 = x_92;
goto block_138;
}
else
{
lean_object* x_139; 
x_139 = lean_alloc_ctor(0, 4, 8);
lean_ctor_set(x_139, 0, x_133);
lean_ctor_set(x_139, 1, x_88);
lean_ctor_set(x_139, 2, x_89);
lean_ctor_set(x_139, 3, x_90);
lean_ctor_set_float(x_139, sizeof(void*)*4, x_91);
x_134 = x_139;
goto block_138;
}
block_138:
{
lean_object* x_135; 
if (x_25 == 0)
{
lean_ctor_set(x_24, 1, x_132);
lean_ctor_set(x_24, 0, x_134);
x_135 = x_24;
goto block_136;
}
else
{
lean_object* x_137; 
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_134);
lean_ctor_set(x_137, 1, x_132);
x_135 = x_137;
goto block_136;
}
block_136:
{
x_7 = x_26;
x_8 = x_135;
goto block_12;
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
block_12:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_4, x_9);
lean_dec(x_4);
x_4 = x_10;
x_5 = x_7;
x_6 = x_8;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_collideThreads_collideSamples_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_collideThreads_collideSamples_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Profiler_0__Lean_Firefox_collideThreads_collideSamples(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_15; 
x_3 = lean_ctor_get(x_1, 2);
x_4 = lean_ctor_get(x_3, 5);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_box(0);
x_7 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_collideThreads_collideSamples_spec__0___redArg(x_4, x_3, x_1, x_5, x_6, x_2);
x_8 = lean_ctor_get(x_7, 1);
x_15 = !lean_is_exclusive(x_7);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_7, 0);
lean_dec(x_16);
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
lean_ctor_set(x_9, 0, x_6);
x_11 = x_9;
goto block_12;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_8);
x_11 = x_13;
goto block_12;
}
block_12:
{
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Profiler_0__Lean_Firefox_collideThreads_collideSamples___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Util_Profiler_0__Lean_Firefox_collideThreads_collideSamples(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_collideThreads_collideSamples_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_collideThreads_collideSamples_spec__0___redArg(x_1, x_2, x_3, x_6, x_7, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_collideThreads_collideSamples_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_collideThreads_collideSamples_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Profiler_0__Lean_Firefox_collideThreads(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l___private_Lean_Util_Profiler_0__Lean_Firefox_collideThreads_collideSamples(x_2, x_1);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec_ref(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Profiler_0__Lean_Firefox_collideThreads___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Util_Profiler_0__Lean_Firefox_collideThreads(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_collide_spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_5 = lean_array_uget_borrowed(x_3, x_2);
x_6 = lean_ctor_get(x_5, 2);
lean_inc_ref(x_6);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_8, x_2, x_6);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_collide_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_collide_spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Firefox_Profile_collide_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget_borrowed(x_1, x_2);
x_7 = l___private_Lean_Util_Profiler_0__Lean_Firefox_collideThreads(x_4, x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_2 = x_9;
x_4 = x_7;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Firefox_Profile_collide_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Firefox_Profile_collide_spec__0(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Firefox_Profile_collide_spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget_borrowed(x_1, x_2);
x_7 = l_Array_append___redArg(x_4, x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_2 = x_9;
x_4 = x_7;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Firefox_Profile_collide_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Firefox_Profile_collide_spec__2(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
static lean_object* _init_l_Lean_Firefox_Profile_collide___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Firefox_Profile_collide___closed__0));
x_2 = l_Lean_Firefox_Thread_new(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Firefox_Profile_collide___closed__2(void) {
_start:
{
double x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_float_once(&l___private_Lean_Util_Profiler_0__Lean_Firefox_getFirstStart_x3f___closed__0, &l___private_Lean_Util_Profiler_0__Lean_Firefox_getFirstStart_x3f___closed__0_once, _init_l___private_Lean_Util_Profiler_0__Lean_Firefox_getFirstStart_x3f___closed__0);
x_2 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__7___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__7___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__7___closed__7);
x_3 = lean_obj_once(&l_Lean_Firefox_Profile_collide___closed__1, &l_Lean_Firefox_Profile_collide___closed__1_once, _init_l_Lean_Firefox_Profile_collide___closed__1);
x_4 = lean_alloc_ctor(0, 4, 8);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_2);
lean_ctor_set(x_4, 3, x_2);
lean_ctor_set_float(x_4, sizeof(void*)*4, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Firefox_Profile_collide___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__7___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__7___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__7___closed__7);
x_2 = lean_obj_once(&l_Lean_Firefox_Profile_collide___closed__2, &l_Lean_Firefox_Profile_collide___closed__2_once, _init_l_Lean_Firefox_Profile_collide___closed__2);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Firefox_Profile_collide(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_array_get_size(x_1);
x_4 = lean_nat_dec_lt(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec_ref(x_1);
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_25; lean_object* x_26; size_t x_37; size_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_6 = lean_array_fget(x_1, x_2);
x_25 = lean_obj_once(&l_Lean_Firefox_Profile_collide___closed__3, &l_Lean_Firefox_Profile_collide___closed__3_once, _init_l_Lean_Firefox_Profile_collide___closed__3);
x_37 = lean_array_size(x_1);
x_38 = 0;
x_39 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_collide_spec__1(x_37, x_38, x_1);
x_40 = ((lean_object*)(l_Lean_Firefox_Profile_collide___closed__4));
x_41 = lean_array_get_size(x_39);
x_42 = lean_nat_dec_lt(x_2, x_41);
if (x_42 == 0)
{
lean_dec_ref(x_39);
x_26 = x_40;
goto block_36;
}
else
{
uint8_t x_43; 
x_43 = lean_nat_dec_le(x_41, x_41);
if (x_43 == 0)
{
if (x_42 == 0)
{
lean_dec_ref(x_39);
x_26 = x_40;
goto block_36;
}
else
{
size_t x_44; lean_object* x_45; 
x_44 = lean_usize_of_nat(x_41);
x_45 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Firefox_Profile_collide_spec__2(x_39, x_38, x_44, x_40);
lean_dec_ref(x_39);
x_26 = x_45;
goto block_36;
}
}
else
{
size_t x_46; lean_object* x_47; 
x_46 = lean_usize_of_nat(x_41);
x_47 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Firefox_Profile_collide_spec__2(x_39, x_38, x_46, x_40);
lean_dec_ref(x_39);
x_26 = x_47;
goto block_36;
}
}
block_24:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_22; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
lean_dec_ref(x_7);
x_9 = lean_ctor_get(x_6, 0);
x_10 = lean_ctor_get(x_6, 1);
x_22 = !lean_is_exclusive(x_6);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_6, 2);
lean_dec(x_23);
x_11 = x_6;
x_12 = x_22;
goto block_21;
}
else
{
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_6);
x_11 = lean_box(0);
x_12 = x_22;
goto block_21;
}
block_21:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_8, 0);
lean_inc_ref(x_13);
lean_dec_ref(x_8);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_mk_empty_array_with_capacity(x_14);
x_16 = lean_array_push(x_15, x_13);
if (x_12 == 0)
{
lean_ctor_set(x_11, 2, x_16);
x_17 = x_11;
goto block_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_20, 0, x_9);
lean_ctor_set(x_20, 1, x_10);
lean_ctor_set(x_20, 2, x_16);
x_17 = x_20;
goto block_19;
}
block_19:
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
}
block_36:
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_array_get_size(x_26);
x_28 = lean_nat_dec_lt(x_2, x_27);
if (x_28 == 0)
{
lean_dec_ref(x_26);
x_7 = x_25;
goto block_24;
}
else
{
uint8_t x_29; 
x_29 = lean_nat_dec_le(x_27, x_27);
if (x_29 == 0)
{
if (x_28 == 0)
{
lean_dec_ref(x_26);
x_7 = x_25;
goto block_24;
}
else
{
size_t x_30; size_t x_31; lean_object* x_32; 
x_30 = 0;
x_31 = lean_usize_of_nat(x_27);
x_32 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Firefox_Profile_collide_spec__0(x_26, x_30, x_31, x_25);
lean_dec_ref(x_26);
x_7 = x_32;
goto block_24;
}
}
else
{
size_t x_33; size_t x_34; lean_object* x_35; 
x_33 = 0;
x_34 = lean_usize_of_nat(x_27);
x_35 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Firefox_Profile_collide_spec__0(x_26, x_33, x_34, x_25);
lean_dec_ref(x_26);
x_7 = x_35;
goto block_24;
}
}
}
}
}
}
lean_object* runtime_initialize_Lean_Util_Trace(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Util_Profiler(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Util_Trace(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Firefox_instInhabitedMilliseconds_default = _init_l_Lean_Firefox_instInhabitedMilliseconds_default();
l_Lean_Firefox_instInhabitedMilliseconds = _init_l_Lean_Firefox_instInhabitedMilliseconds();
l_Lean_Firefox_instInhabitedFrameTable_default = _init_l_Lean_Firefox_instInhabitedFrameTable_default();
lean_mark_persistent(l_Lean_Firefox_instInhabitedFrameTable_default);
l_Lean_Firefox_instInhabitedFrameTable = _init_l_Lean_Firefox_instInhabitedFrameTable();
lean_mark_persistent(l_Lean_Firefox_instInhabitedFrameTable);
l___private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go___boxed__const__1 = _init_l___private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go___boxed__const__1();
lean_mark_persistent(l___private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go___boxed__const__1);
l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__6___redArg___closed__0___boxed__const__1 = _init_l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__6___redArg___closed__0___boxed__const__1();
lean_mark_persistent(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__6___redArg___closed__0___boxed__const__1);
l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_collideThreads_collideSamples_spec__0___redArg___boxed__const__1 = _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_collideThreads_collideSamples_spec__0___redArg___boxed__const__1();
lean_mark_persistent(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_collideThreads_collideSamples_spec__0___redArg___boxed__const__1);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Util_Profiler(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Util_Trace(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_Profiler(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Util_Trace(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_Profiler(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Util_Profiler(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Util_Profiler(builtin);
}
#ifdef __cplusplus
}
#endif

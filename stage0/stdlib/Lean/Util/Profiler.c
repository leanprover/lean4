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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_uint64_dec_lt(uint64_t, uint64_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Json_getInt_x3f(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_Lean_Json_getNat_x3f(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
lean_object* l_Lean_Float_toJson(double);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
lean_object* lean_array_get_size(lean_object*);
double lean_float_of_nat(lean_object*);
uint8_t lean_float_beq(double, double);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_JsonNumber_fromNat(lean_object*);
lean_object* l_Float_add___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Float_fromJson_x3f(lean_object*);
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
lean_object* l_Lean_Float_toJson___boxed(lean_object*);
lean_object* l_Lean_Name_fromJson_x3f(lean_object*);
lean_object* l_Lean_JsonNumber_fromInt(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t lean_float_decLt(double, double);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint64_t lean_string_hash(lean_object*);
double lean_float_mul(double, double);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* l_Lean_Json_getBool_x3f(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Float_ofScientific___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_trace_profiler_output_pp;
double l_Float_ofScientific(lean_object*, uint8_t, lean_object*);
double lean_float_sub(double, double);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_format(lean_object*, lean_object*);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
lean_object* lean_uint64_to_nat(uint64_t);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
double lean_uint64_to_float(uint64_t);
double lean_float_add(double, double);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_mono_nanos_now();
double lean_float_div(double, double);
static lean_once_cell_t l_Lean_Firefox_instInhabitedMilliseconds_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_Firefox_instInhabitedMilliseconds_default___closed__0;
LEAN_EXPORT double l_Lean_Firefox_instInhabitedMilliseconds_default;
LEAN_EXPORT double l_Lean_Firefox_instInhabitedMilliseconds;
static lean_once_cell_t l_Lean_Firefox_instCoeFloatMilliseconds___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_Firefox_instCoeFloatMilliseconds___lam__0___closed__0;
LEAN_EXPORT double l_Lean_Firefox_instCoeFloatMilliseconds___lam__0(double);
LEAN_EXPORT lean_object* l_Lean_Firefox_instCoeFloatMilliseconds___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Firefox_instCoeFloatMilliseconds___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Firefox_instCoeFloatMilliseconds___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Firefox_instCoeFloatMilliseconds___closed__0 = (const lean_object*)&l_Lean_Firefox_instCoeFloatMilliseconds___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Firefox_instCoeFloatMilliseconds = (const lean_object*)&l_Lean_Firefox_instCoeFloatMilliseconds___closed__0_value;
static const lean_closure_object l_Lean_Firefox_instOfScientificMilliseconds___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Float_ofScientific___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Firefox_instOfScientificMilliseconds___closed__0 = (const lean_object*)&l_Lean_Firefox_instOfScientificMilliseconds___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Firefox_instOfScientificMilliseconds = (const lean_object*)&l_Lean_Firefox_instOfScientificMilliseconds___closed__0_value;
static const lean_closure_object l_Lean_Firefox_instToJsonMilliseconds___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Float_toJson___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Firefox_instToJsonMilliseconds___closed__0 = (const lean_object*)&l_Lean_Firefox_instToJsonMilliseconds___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Firefox_instToJsonMilliseconds = (const lean_object*)&l_Lean_Firefox_instToJsonMilliseconds___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Firefox_instFromJsonMilliseconds___lam__0(lean_object*);
static const lean_closure_object l_Lean_Firefox_instFromJsonMilliseconds___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Firefox_instFromJsonMilliseconds___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Firefox_instFromJsonMilliseconds___closed__0 = (const lean_object*)&l_Lean_Firefox_instFromJsonMilliseconds___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Firefox_instFromJsonMilliseconds = (const lean_object*)&l_Lean_Firefox_instFromJsonMilliseconds___closed__0_value;
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
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__2_spec__2_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__2_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__2_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "expected JSON array, got '"};
static const lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__2_spec__2___closed__0 = (const lean_object*)&l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__2_spec__2___closed__0_value;
static const lean_string_object l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__2_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__2_spec__2___closed__1 = (const lean_object*)&l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__2_spec__2___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__2_spec__2(lean_object*);
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
static const lean_ctor_object l_Lean_Firefox_instFromJsonCategory_fromJson___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Firefox_instFromJsonCategory_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Firefox_instFromJsonCategory_fromJson___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Firefox_instFromJsonCategory_fromJson___closed__4_value_aux_0),((lean_object*)&l_Lean_Firefox_instFromJsonCategory_fromJson___closed__2_value),LEAN_SCALAR_PTR_LITERAL(1, 221, 142, 98, 103, 73, 209, 133)}};
static const lean_ctor_object l_Lean_Firefox_instFromJsonCategory_fromJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Firefox_instFromJsonCategory_fromJson___closed__4_value_aux_1),((lean_object*)&l_Lean_Firefox_instFromJsonCategory_fromJson___closed__3_value),LEAN_SCALAR_PTR_LITERAL(218, 120, 30, 24, 139, 24, 153, 254)}};
static const lean_object* l_Lean_Firefox_instFromJsonCategory_fromJson___closed__4 = (const lean_object*)&l_Lean_Firefox_instFromJsonCategory_fromJson___closed__4_value;
static lean_once_cell_t l_Lean_Firefox_instFromJsonCategory_fromJson___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonCategory_fromJson___closed__5;
static const lean_string_object l_Lean_Firefox_instFromJsonCategory_fromJson___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lean_Firefox_instFromJsonCategory_fromJson___closed__6 = (const lean_object*)&l_Lean_Firefox_instFromJsonCategory_fromJson___closed__6_value;
static lean_once_cell_t l_Lean_Firefox_instFromJsonCategory_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Firefox_instFromJsonCategory_fromJson___closed__7;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Firefox_instToJsonCategory_toJson_spec__0_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Firefox_instToJsonCategory_toJson_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Firefox_instToJsonCategory_toJson_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Firefox_instToJsonCategory_toJson_spec__1(lean_object*, lean_object*);
static const lean_array_object l_Lean_Firefox_instToJsonCategory_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Firefox_instToJsonCategory_toJson___closed__0 = (const lean_object*)&l_Lean_Firefox_instToJsonCategory_toJson___closed__0_value;
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
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__1_spec__1_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__1_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__1_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__3_spec__4_spec__7(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__3_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__3_spec__4(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Firefox_instToJsonProfileMeta_toJson_spec__0_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Firefox_instToJsonProfileMeta_toJson_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Firefox_instToJsonProfileMeta_toJson_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Firefox_instToJsonProfileMeta_toJson_spec__1_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Firefox_instToJsonProfileMeta_toJson_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Firefox_instToJsonProfileMeta_toJson_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Firefox_instToJsonProfileMeta_toJson(lean_object*);
static const lean_closure_object l_Lean_Firefox_instToJsonProfileMeta___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Firefox_instToJsonProfileMeta_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Firefox_instToJsonProfileMeta___closed__0 = (const lean_object*)&l_Lean_Firefox_instToJsonProfileMeta___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Firefox_instToJsonProfileMeta = (const lean_object*)&l_Lean_Firefox_instToJsonProfileMeta___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonStackTable_fromJson_spec__0_spec__0_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonStackTable_fromJson_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonStackTable_fromJson_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonStackTable_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonStackTable_fromJson_spec__0___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonStackTable_fromJson_spec__1_spec__2_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonStackTable_fromJson_spec__1_spec__2_spec__4___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonStackTable_fromJson_spec__1_spec__2_spec__4___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonStackTable_fromJson_spec__1_spec__2_spec__4(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonStackTable_fromJson_spec__1_spec__2_spec__5(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonStackTable_fromJson_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonStackTable_fromJson_spec__1_spec__2(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Option_toJson___at___00Lean_Array_toJson___at___00Lean_Firefox_instToJsonStackTable_toJson_spec__1_spec__2(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Firefox_instToJsonStackTable_toJson_spec__1_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Firefox_instToJsonStackTable_toJson_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Firefox_instToJsonStackTable_toJson_spec__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Firefox_instToJsonStackTable_toJson_spec__0_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Firefox_instToJsonStackTable_toJson_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Firefox_instToJsonStackTable_toJson_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Firefox_instToJsonStackTable_toJson(lean_object*);
static const lean_closure_object l_Lean_Firefox_instToJsonStackTable___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Firefox_instToJsonStackTable_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Firefox_instToJsonStackTable___closed__0 = (const lean_object*)&l_Lean_Firefox_instToJsonStackTable___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Firefox_instToJsonStackTable = (const lean_object*)&l_Lean_Firefox_instToJsonStackTable___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonSamplesTable_fromJson_spec__0_spec__0_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonSamplesTable_fromJson_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonSamplesTable_fromJson_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonSamplesTable_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonSamplesTable_fromJson_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonSamplesTable_fromJson_spec__1_spec__2_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonSamplesTable_fromJson_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonSamplesTable_fromJson_spec__1_spec__2(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Firefox_instToJsonSamplesTable_toJson_spec__1_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Firefox_instToJsonSamplesTable_toJson_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Firefox_instToJsonSamplesTable_toJson_spec__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Firefox_instToJsonSamplesTable_toJson_spec__0_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Firefox_instToJsonSamplesTable_toJson_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Firefox_instToJsonSamplesTable_toJson_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Firefox_instToJsonSamplesTable_toJson(lean_object*);
static const lean_closure_object l_Lean_Firefox_instToJsonSamplesTable___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Firefox_instToJsonSamplesTable_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Firefox_instToJsonSamplesTable___closed__0 = (const lean_object*)&l_Lean_Firefox_instToJsonSamplesTable___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Firefox_instToJsonSamplesTable = (const lean_object*)&l_Lean_Firefox_instToJsonSamplesTable___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonFuncTable_fromJson_spec__0_spec__0_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonFuncTable_fromJson_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonFuncTable_fromJson_spec__0_spec__0(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Firefox_instToJsonFuncTable_toJson_spec__0_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Firefox_instToJsonFuncTable_toJson_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Firefox_instToJsonFuncTable_toJson_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Firefox_instToJsonFuncTable_toJson(lean_object*);
static const lean_closure_object l_Lean_Firefox_instToJsonFuncTable___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Firefox_instToJsonFuncTable_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Firefox_instToJsonFuncTable___closed__0 = (const lean_object*)&l_Lean_Firefox_instToJsonFuncTable___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Firefox_instToJsonFuncTable = (const lean_object*)&l_Lean_Firefox_instToJsonFuncTable___closed__0_value;
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonFrameTable_fromJson_spec__0_spec__0_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonFrameTable_fromJson_spec__0_spec__0_spec__1___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonFrameTable_fromJson_spec__0_spec__0_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonFrameTable_fromJson_spec__0_spec__0_spec__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonFrameTable_fromJson_spec__0_spec__0_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonFrameTable_fromJson_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonFrameTable_fromJson_spec__0_spec__0(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Option_toJson___at___00Lean_Array_toJson___at___00Lean_Firefox_instToJsonFrameTable_toJson_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_toJson___at___00Lean_Array_toJson___at___00Lean_Firefox_instToJsonFrameTable_toJson_spec__0_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Firefox_instToJsonFrameTable_toJson_spec__0_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Firefox_instToJsonFrameTable_toJson_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Firefox_instToJsonFrameTable_toJson_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Firefox_instToJsonFrameTable_toJson(lean_object*);
static const lean_closure_object l_Lean_Firefox_instToJsonFrameTable___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Firefox_instToJsonFrameTable_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Firefox_instToJsonFrameTable___closed__0 = (const lean_object*)&l_Lean_Firefox_instToJsonFrameTable___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Firefox_instToJsonFrameTable = (const lean_object*)&l_Lean_Firefox_instToJsonFrameTable___closed__0_value;
static const lean_array_object l_Lean_Firefox_instInhabitedFrameTable_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Firefox_instInhabitedFrameTable_default___closed__0 = (const lean_object*)&l_Lean_Firefox_instInhabitedFrameTable_default___closed__0_value;
static const lean_ctor_object l_Lean_Firefox_instInhabitedFrameTable_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*11 + 0, .m_other = 11, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Firefox_instInhabitedFrameTable_default___closed__0_value),((lean_object*)&l_Lean_Firefox_instInhabitedFrameTable_default___closed__0_value),((lean_object*)&l_Lean_Firefox_instInhabitedFrameTable_default___closed__0_value),((lean_object*)&l_Lean_Firefox_instInhabitedFrameTable_default___closed__0_value),((lean_object*)&l_Lean_Firefox_instInhabitedFrameTable_default___closed__0_value),((lean_object*)&l_Lean_Firefox_instInhabitedFrameTable_default___closed__0_value),((lean_object*)&l_Lean_Firefox_instInhabitedFrameTable_default___closed__0_value),((lean_object*)&l_Lean_Firefox_instInhabitedFrameTable_default___closed__0_value),((lean_object*)&l_Lean_Firefox_instInhabitedFrameTable_default___closed__0_value),((lean_object*)&l_Lean_Firefox_instInhabitedFrameTable_default___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Firefox_instInhabitedFrameTable_default___closed__1 = (const lean_object*)&l_Lean_Firefox_instInhabitedFrameTable_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Firefox_instInhabitedFrameTable_default = (const lean_object*)&l_Lean_Firefox_instInhabitedFrameTable_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Firefox_instInhabitedFrameTable = (const lean_object*)&l_Lean_Firefox_instInhabitedFrameTable_default___closed__1_value;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfile_fromJson_spec__1_spec__1_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfile_fromJson_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfile_fromJson_spec__1_spec__1(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Firefox_instToJsonProfile_toJson_spec__0_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Firefox_instToJsonProfile_toJson_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Firefox_instToJsonProfile_toJson_spec__0(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Util_Profiler_0__Lean_Firefox_getFirstStart_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_getFirstStart_x3f_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_getFirstStart_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Profiler_0__Lean_Firefox_getFirstStart_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__3_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__3_spec__7___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__1_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__2_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__2_spec__4_spec__6_spec__12___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__2_spec__4_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__2_spec__4___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__2_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__6_spec__14___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__6_spec__14___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__7_spec__16___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__7_spec__16___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__7_spec__18___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__7_spec__17_spec__21_spec__24___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__7_spec__17_spec__21___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__7_spec__17___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__4_spec__10_spec__13_spec__18___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__4_spec__10_spec__13___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__4_spec__10___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__4_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__4_spec__9___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__4_spec__11___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__4___redArg(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "tracing-ms"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go___boxed__const__1;
static lean_once_cell_t l___private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go___closed__1;
static lean_once_cell_t l___private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go___closed__2;
static const lean_array_object l___private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go___closed__3 = (const lean_object*)&l___private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__6_spec__14(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__6_spec__14___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__7_spec__16(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__7_spec__16___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__7_spec__17(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__7_spec__18(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__2_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__4_spec__10_spec__13(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__7_spec__17_spec__21(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__2_spec__4_spec__6_spec__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__4_spec__10_spec__13_spec__18(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__7_spec__17_spec__21_spec__24(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Profiler_0__Lean_Firefox_addTrace(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Profiler_0__Lean_Firefox_addTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Firefox_Thread_new___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "default"};
static const lean_object* l_Lean_Firefox_Thread_new___closed__0 = (const lean_object*)&l_Lean_Firefox_Thread_new___closed__0_value;
static const lean_array_object l_Lean_Firefox_Thread_new___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Firefox_Thread_new___closed__1 = (const lean_object*)&l_Lean_Firefox_Thread_new___closed__1_value;
static const lean_ctor_object l_Lean_Firefox_Thread_new___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*6 + 0, .m_other = 6, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Firefox_Thread_new___closed__1_value),((lean_object*)&l_Lean_Firefox_Thread_new___closed__1_value),((lean_object*)&l_Lean_Firefox_Thread_new___closed__1_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__0___closed__0_value),((lean_object*)&l_Lean_Firefox_Thread_new___closed__1_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Firefox_Thread_new___closed__2 = (const lean_object*)&l_Lean_Firefox_Thread_new___closed__2_value;
static const lean_ctor_object l_Lean_Firefox_Thread_new___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Firefox_Thread_new___closed__1_value),((lean_object*)&l_Lean_Firefox_Thread_new___closed__1_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Firefox_Thread_new___closed__3 = (const lean_object*)&l_Lean_Firefox_Thread_new___closed__3_value;
static const lean_ctor_object l_Lean_Firefox_Thread_new___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Firefox_Thread_new___closed__1_value),((lean_object*)&l_Lean_Firefox_Thread_new___closed__1_value),((lean_object*)&l_Lean_Firefox_Thread_new___closed__1_value),((lean_object*)&l_Lean_Firefox_Thread_new___closed__1_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Firefox_Thread_new___closed__4 = (const lean_object*)&l_Lean_Firefox_Thread_new___closed__4_value;
static const lean_ctor_object l_Lean_Firefox_Thread_new___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Firefox_Thread_new___closed__1_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Firefox_Thread_new___closed__5 = (const lean_object*)&l_Lean_Firefox_Thread_new___closed__5_value;
static const lean_ctor_object l_Lean_Firefox_Thread_new___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*8 + 0, .m_other = 8, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Firefox_Thread_new___closed__1_value),((lean_object*)&l_Lean_Firefox_Thread_new___closed__1_value),((lean_object*)&l_Lean_Firefox_Thread_new___closed__1_value),((lean_object*)&l_Lean_Firefox_Thread_new___closed__1_value),((lean_object*)&l_Lean_Firefox_Thread_new___closed__1_value),((lean_object*)&l_Lean_Firefox_Thread_new___closed__1_value),((lean_object*)&l_Lean_Firefox_Thread_new___closed__1_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Firefox_Thread_new___closed__6 = (const lean_object*)&l_Lean_Firefox_Thread_new___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Firefox_Thread_new(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Firefox_Profile_export_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Firefox_Profile_export_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lean_Firefox_Profile_export___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Firefox_Profile_export___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Firefox_Profile_export_spec__5(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Firefox_Profile_export_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__6___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__6___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT double l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__6___redArg___lam__0(lean_object*, double, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__6___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__6_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__6_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__6___redArg___closed__0___boxed__const__1;
static lean_once_cell_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__6___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__6___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__7___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__7___closed__4;
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__7___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__7___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__7___closed__5_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__7___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__7___closed__6;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__7___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__7___closed__7;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__7(lean_object*, double, double, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__2___redArg(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*);
static const lean_array_object l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__4___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__4___redArg___lam__0___closed__0 = (const lean_object*)&l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__4___redArg___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__4___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__4___redArg(lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__3_spec__14_spec__18___redArg(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__9___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__9___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__9_spec__12___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__9_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l_Lean_Firefox_Profile_export___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Firefox_Profile_export___closed__3_value),((lean_object*)&l_Lean_Firefox_Profile_export___closed__3_value),((lean_object*)&l_Lean_Firefox_Profile_export___closed__4_value)}};
static const lean_object* l_Lean_Firefox_Profile_export___closed__5 = (const lean_object*)&l_Lean_Firefox_Profile_export___closed__5_value;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__6_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__9_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__9_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__2(lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__4(lean_object*, lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__3_spec__14(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__3_spec__14_spec__18(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Profiler_0__Lean_Firefox_collideThreads_getStrIdx(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Profiler_0__Lean_Firefox_collideThreads_collideStacks(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Profiler_0__Lean_Firefox_collideThreads_collideStacks___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_collideThreads_collideSamples_spec__0___redArg___boxed__const__1;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_collideThreads_collideSamples_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static double _init_l_Lean_Firefox_instInhabitedMilliseconds_default___closed__0(void){
_start:
{
uint64_t v___x_1_; double v___x_2_; 
v___x_1_ = 0ULL;
v___x_2_ = lean_uint64_to_float(v___x_1_);
return v___x_2_;
}
}
static double _init_l_Lean_Firefox_instInhabitedMilliseconds_default(void){
_start:
{
double v___x_3_; 
v___x_3_ = lean_float_once(&l_Lean_Firefox_instInhabitedMilliseconds_default___closed__0, &l_Lean_Firefox_instInhabitedMilliseconds_default___closed__0_once, _init_l_Lean_Firefox_instInhabitedMilliseconds_default___closed__0);
return v___x_3_;
}
}
static double _init_l_Lean_Firefox_instInhabitedMilliseconds(void){
_start:
{
double v___x_4_; 
v___x_4_ = l_Lean_Firefox_instInhabitedMilliseconds_default;
return v___x_4_;
}
}
static double _init_l_Lean_Firefox_instCoeFloatMilliseconds___lam__0___closed__0(void){
_start:
{
lean_object* v___x_5_; double v___x_6_; 
v___x_5_ = lean_unsigned_to_nat(1000u);
v___x_6_ = lean_float_of_nat(v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT double l_Lean_Firefox_instCoeFloatMilliseconds___lam__0(double v_s_7_){
_start:
{
double v___x_8_; double v___x_9_; 
v___x_8_ = lean_float_once(&l_Lean_Firefox_instCoeFloatMilliseconds___lam__0___closed__0, &l_Lean_Firefox_instCoeFloatMilliseconds___lam__0___closed__0_once, _init_l_Lean_Firefox_instCoeFloatMilliseconds___lam__0___closed__0);
v___x_9_ = lean_float_mul(v_s_7_, v___x_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Firefox_instCoeFloatMilliseconds___lam__0___boxed(lean_object* v_s_10_){
_start:
{
double v_s_boxed_11_; double v_res_12_; lean_object* v_r_13_; 
v_s_boxed_11_ = lean_unbox_float(v_s_10_);
lean_dec_ref(v_s_10_);
v_res_12_ = l_Lean_Firefox_instCoeFloatMilliseconds___lam__0(v_s_boxed_11_);
v_r_13_ = lean_box_float(v_res_12_);
return v_r_13_;
}
}
LEAN_EXPORT lean_object* l_Lean_Firefox_instFromJsonMilliseconds___lam__0(lean_object* v_j_20_){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = l_Lean_Float_fromJson_x3f(v_j_20_);
if (lean_obj_tag(v___x_21_) == 0)
{
lean_object* v_a_22_; lean_object* v___x_24_; uint8_t v_isShared_25_; uint8_t v_isSharedCheck_29_; 
v_a_22_ = lean_ctor_get(v___x_21_, 0);
v_isSharedCheck_29_ = !lean_is_exclusive(v___x_21_);
if (v_isSharedCheck_29_ == 0)
{
v___x_24_ = v___x_21_;
v_isShared_25_ = v_isSharedCheck_29_;
goto v_resetjp_23_;
}
else
{
lean_inc(v_a_22_);
lean_dec(v___x_21_);
v___x_24_ = lean_box(0);
v_isShared_25_ = v_isSharedCheck_29_;
goto v_resetjp_23_;
}
v_resetjp_23_:
{
lean_object* v___x_27_; 
if (v_isShared_25_ == 0)
{
v___x_27_ = v___x_24_;
goto v_reusejp_26_;
}
else
{
lean_object* v_reuseFailAlloc_28_; 
v_reuseFailAlloc_28_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_28_, 0, v_a_22_);
v___x_27_ = v_reuseFailAlloc_28_;
goto v_reusejp_26_;
}
v_reusejp_26_:
{
return v___x_27_;
}
}
}
else
{
lean_object* v_a_30_; lean_object* v___x_32_; uint8_t v_isShared_33_; uint8_t v_isSharedCheck_37_; 
v_a_30_ = lean_ctor_get(v___x_21_, 0);
v_isSharedCheck_37_ = !lean_is_exclusive(v___x_21_);
if (v_isSharedCheck_37_ == 0)
{
v___x_32_ = v___x_21_;
v_isShared_33_ = v_isSharedCheck_37_;
goto v_resetjp_31_;
}
else
{
lean_inc(v_a_30_);
lean_dec(v___x_21_);
v___x_32_ = lean_box(0);
v_isShared_33_ = v_isSharedCheck_37_;
goto v_resetjp_31_;
}
v_resetjp_31_:
{
lean_object* v___x_35_; 
if (v_isShared_33_ == 0)
{
v___x_35_ = v___x_32_;
goto v_reusejp_34_;
}
else
{
lean_object* v_reuseFailAlloc_36_; 
v_reuseFailAlloc_36_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_36_, 0, v_a_30_);
v___x_35_ = v_reuseFailAlloc_36_;
goto v_reusejp_34_;
}
v_reusejp_34_:
{
return v___x_35_;
}
}
}
}
}
static double _init_l_Lean_Firefox_instCoeFloatMicroseconds___lam__0___closed__0(void){
_start:
{
lean_object* v___x_42_; double v___x_43_; 
v___x_42_ = lean_unsigned_to_nat(1000000u);
v___x_43_ = lean_float_of_nat(v___x_42_);
return v___x_43_;
}
}
LEAN_EXPORT double l_Lean_Firefox_instCoeFloatMicroseconds___lam__0(double v_s_44_){
_start:
{
double v___x_45_; double v___x_46_; 
v___x_45_ = lean_float_once(&l_Lean_Firefox_instCoeFloatMicroseconds___lam__0___closed__0, &l_Lean_Firefox_instCoeFloatMicroseconds___lam__0___closed__0_once, _init_l_Lean_Firefox_instCoeFloatMicroseconds___lam__0___closed__0);
v___x_46_ = lean_float_mul(v_s_44_, v___x_45_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l_Lean_Firefox_instCoeFloatMicroseconds___lam__0___boxed(lean_object* v_s_47_){
_start:
{
double v_s_boxed_48_; double v_res_49_; lean_object* v_r_50_; 
v_s_boxed_48_ = lean_unbox_float(v_s_47_);
lean_dec_ref(v_s_47_);
v_res_49_ = l_Lean_Firefox_instCoeFloatMicroseconds___lam__0(v_s_boxed_48_);
v_r_50_ = lean_box_float(v_res_49_);
return v_r_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__0(lean_object* v_j_56_, lean_object* v_k_57_){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_58_ = l_Lean_Json_getObjValD(v_j_56_, v_k_57_);
v___x_59_ = l_Lean_Name_fromJson_x3f(v___x_58_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__0___boxed(lean_object* v_j_60_, lean_object* v_k_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__0(v_j_60_, v_k_61_);
lean_dec_ref(v_k_61_);
return v_res_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__1(lean_object* v_j_63_, lean_object* v_k_64_){
_start:
{
lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_65_ = l_Lean_Json_getObjValD(v_j_63_, v_k_64_);
v___x_66_ = l_Lean_Json_getStr_x3f(v___x_65_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__1___boxed(lean_object* v_j_67_, lean_object* v_k_68_){
_start:
{
lean_object* v_res_69_; 
v_res_69_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__1(v_j_67_, v_k_68_);
lean_dec_ref(v_k_68_);
return v_res_69_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__2_spec__2_spec__3(size_t v_sz_70_, size_t v_i_71_, lean_object* v_bs_72_){
_start:
{
uint8_t v___x_73_; 
v___x_73_ = lean_usize_dec_lt(v_i_71_, v_sz_70_);
if (v___x_73_ == 0)
{
lean_object* v___x_74_; 
v___x_74_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_74_, 0, v_bs_72_);
return v___x_74_;
}
else
{
lean_object* v_v_75_; lean_object* v___x_76_; 
v_v_75_ = lean_array_uget_borrowed(v_bs_72_, v_i_71_);
lean_inc(v_v_75_);
v___x_76_ = l_Lean_Json_getStr_x3f(v_v_75_);
if (lean_obj_tag(v___x_76_) == 0)
{
lean_object* v_a_77_; lean_object* v___x_79_; uint8_t v_isShared_80_; uint8_t v_isSharedCheck_84_; 
lean_dec_ref(v_bs_72_);
v_a_77_ = lean_ctor_get(v___x_76_, 0);
v_isSharedCheck_84_ = !lean_is_exclusive(v___x_76_);
if (v_isSharedCheck_84_ == 0)
{
v___x_79_ = v___x_76_;
v_isShared_80_ = v_isSharedCheck_84_;
goto v_resetjp_78_;
}
else
{
lean_inc(v_a_77_);
lean_dec(v___x_76_);
v___x_79_ = lean_box(0);
v_isShared_80_ = v_isSharedCheck_84_;
goto v_resetjp_78_;
}
v_resetjp_78_:
{
lean_object* v___x_82_; 
if (v_isShared_80_ == 0)
{
v___x_82_ = v___x_79_;
goto v_reusejp_81_;
}
else
{
lean_object* v_reuseFailAlloc_83_; 
v_reuseFailAlloc_83_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_83_, 0, v_a_77_);
v___x_82_ = v_reuseFailAlloc_83_;
goto v_reusejp_81_;
}
v_reusejp_81_:
{
return v___x_82_;
}
}
}
else
{
lean_object* v_a_85_; lean_object* v___x_86_; lean_object* v_bs_x27_87_; size_t v___x_88_; size_t v___x_89_; lean_object* v___x_90_; 
v_a_85_ = lean_ctor_get(v___x_76_, 0);
lean_inc(v_a_85_);
lean_dec_ref_known(v___x_76_, 1);
v___x_86_ = lean_unsigned_to_nat(0u);
v_bs_x27_87_ = lean_array_uset(v_bs_72_, v_i_71_, v___x_86_);
v___x_88_ = ((size_t)1ULL);
v___x_89_ = lean_usize_add(v_i_71_, v___x_88_);
v___x_90_ = lean_array_uset(v_bs_x27_87_, v_i_71_, v_a_85_);
v_i_71_ = v___x_89_;
v_bs_72_ = v___x_90_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__2_spec__2_spec__3___boxed(lean_object* v_sz_92_, lean_object* v_i_93_, lean_object* v_bs_94_){
_start:
{
size_t v_sz_boxed_95_; size_t v_i_boxed_96_; lean_object* v_res_97_; 
v_sz_boxed_95_ = lean_unbox_usize(v_sz_92_);
lean_dec(v_sz_92_);
v_i_boxed_96_ = lean_unbox_usize(v_i_93_);
lean_dec(v_i_93_);
v_res_97_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__2_spec__2_spec__3(v_sz_boxed_95_, v_i_boxed_96_, v_bs_94_);
return v_res_97_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__2_spec__2(lean_object* v_x_100_){
_start:
{
if (lean_obj_tag(v_x_100_) == 4)
{
lean_object* v_elems_101_; size_t v_sz_102_; size_t v___x_103_; lean_object* v___x_104_; 
v_elems_101_ = lean_ctor_get(v_x_100_, 0);
lean_inc_ref(v_elems_101_);
lean_dec_ref_known(v_x_100_, 1);
v_sz_102_ = lean_array_size(v_elems_101_);
v___x_103_ = ((size_t)0ULL);
v___x_104_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__2_spec__2_spec__3(v_sz_102_, v___x_103_, v_elems_101_);
return v___x_104_;
}
else
{
lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_105_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__2_spec__2___closed__0));
v___x_106_ = lean_unsigned_to_nat(80u);
v___x_107_ = l_Lean_Json_pretty(v_x_100_, v___x_106_);
v___x_108_ = lean_string_append(v___x_105_, v___x_107_);
lean_dec_ref(v___x_107_);
v___x_109_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__2_spec__2___closed__1));
v___x_110_ = lean_string_append(v___x_108_, v___x_109_);
v___x_111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_111_, 0, v___x_110_);
return v___x_111_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__2(lean_object* v_j_112_, lean_object* v_k_113_){
_start:
{
lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_114_ = l_Lean_Json_getObjValD(v_j_112_, v_k_113_);
v___x_115_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__2_spec__2(v___x_114_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__2___boxed(lean_object* v_j_116_, lean_object* v_k_117_){
_start:
{
lean_object* v_res_118_; 
v_res_118_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__2(v_j_116_, v_k_117_);
lean_dec_ref(v_k_117_);
return v_res_118_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonCategory_fromJson___closed__5(void){
_start:
{
uint8_t v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_127_ = 1;
v___x_128_ = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__4));
v___x_129_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_128_, v___x_127_);
return v___x_129_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonCategory_fromJson___closed__7(void){
_start:
{
lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; 
v___x_131_ = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__6));
v___x_132_ = lean_obj_once(&l_Lean_Firefox_instFromJsonCategory_fromJson___closed__5, &l_Lean_Firefox_instFromJsonCategory_fromJson___closed__5_once, _init_l_Lean_Firefox_instFromJsonCategory_fromJson___closed__5);
v___x_133_ = lean_string_append(v___x_132_, v___x_131_);
return v___x_133_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonCategory_fromJson___closed__9(void){
_start:
{
uint8_t v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
v___x_136_ = 1;
v___x_137_ = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__8));
v___x_138_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_137_, v___x_136_);
return v___x_138_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonCategory_fromJson___closed__10(void){
_start:
{
lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_139_ = lean_obj_once(&l_Lean_Firefox_instFromJsonCategory_fromJson___closed__9, &l_Lean_Firefox_instFromJsonCategory_fromJson___closed__9_once, _init_l_Lean_Firefox_instFromJsonCategory_fromJson___closed__9);
v___x_140_ = lean_obj_once(&l_Lean_Firefox_instFromJsonCategory_fromJson___closed__7, &l_Lean_Firefox_instFromJsonCategory_fromJson___closed__7_once, _init_l_Lean_Firefox_instFromJsonCategory_fromJson___closed__7);
v___x_141_ = lean_string_append(v___x_140_, v___x_139_);
return v___x_141_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonCategory_fromJson___closed__12(void){
_start:
{
lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_143_ = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
v___x_144_ = lean_obj_once(&l_Lean_Firefox_instFromJsonCategory_fromJson___closed__10, &l_Lean_Firefox_instFromJsonCategory_fromJson___closed__10_once, _init_l_Lean_Firefox_instFromJsonCategory_fromJson___closed__10);
v___x_145_ = lean_string_append(v___x_144_, v___x_143_);
return v___x_145_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonCategory_fromJson___closed__15(void){
_start:
{
uint8_t v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_149_ = 1;
v___x_150_ = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__14));
v___x_151_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_150_, v___x_149_);
return v___x_151_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonCategory_fromJson___closed__16(void){
_start:
{
lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_152_ = lean_obj_once(&l_Lean_Firefox_instFromJsonCategory_fromJson___closed__15, &l_Lean_Firefox_instFromJsonCategory_fromJson___closed__15_once, _init_l_Lean_Firefox_instFromJsonCategory_fromJson___closed__15);
v___x_153_ = lean_obj_once(&l_Lean_Firefox_instFromJsonCategory_fromJson___closed__7, &l_Lean_Firefox_instFromJsonCategory_fromJson___closed__7_once, _init_l_Lean_Firefox_instFromJsonCategory_fromJson___closed__7);
v___x_154_ = lean_string_append(v___x_153_, v___x_152_);
return v___x_154_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonCategory_fromJson___closed__17(void){
_start:
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_155_ = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
v___x_156_ = lean_obj_once(&l_Lean_Firefox_instFromJsonCategory_fromJson___closed__16, &l_Lean_Firefox_instFromJsonCategory_fromJson___closed__16_once, _init_l_Lean_Firefox_instFromJsonCategory_fromJson___closed__16);
v___x_157_ = lean_string_append(v___x_156_, v___x_155_);
return v___x_157_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonCategory_fromJson___closed__20(void){
_start:
{
uint8_t v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_161_ = 1;
v___x_162_ = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__19));
v___x_163_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_162_, v___x_161_);
return v___x_163_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonCategory_fromJson___closed__21(void){
_start:
{
lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_164_ = lean_obj_once(&l_Lean_Firefox_instFromJsonCategory_fromJson___closed__20, &l_Lean_Firefox_instFromJsonCategory_fromJson___closed__20_once, _init_l_Lean_Firefox_instFromJsonCategory_fromJson___closed__20);
v___x_165_ = lean_obj_once(&l_Lean_Firefox_instFromJsonCategory_fromJson___closed__7, &l_Lean_Firefox_instFromJsonCategory_fromJson___closed__7_once, _init_l_Lean_Firefox_instFromJsonCategory_fromJson___closed__7);
v___x_166_ = lean_string_append(v___x_165_, v___x_164_);
return v___x_166_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonCategory_fromJson___closed__22(void){
_start:
{
lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
v___x_167_ = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
v___x_168_ = lean_obj_once(&l_Lean_Firefox_instFromJsonCategory_fromJson___closed__21, &l_Lean_Firefox_instFromJsonCategory_fromJson___closed__21_once, _init_l_Lean_Firefox_instFromJsonCategory_fromJson___closed__21);
v___x_169_ = lean_string_append(v___x_168_, v___x_167_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Firefox_instFromJsonCategory_fromJson(lean_object* v_json_170_){
_start:
{
lean_object* v___x_171_; lean_object* v___x_172_; 
v___x_171_ = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__0));
lean_inc(v_json_170_);
v___x_172_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__0(v_json_170_, v___x_171_);
if (lean_obj_tag(v___x_172_) == 0)
{
lean_object* v_a_173_; lean_object* v___x_175_; uint8_t v_isShared_176_; uint8_t v_isSharedCheck_182_; 
lean_dec(v_json_170_);
v_a_173_ = lean_ctor_get(v___x_172_, 0);
v_isSharedCheck_182_ = !lean_is_exclusive(v___x_172_);
if (v_isSharedCheck_182_ == 0)
{
v___x_175_ = v___x_172_;
v_isShared_176_ = v_isSharedCheck_182_;
goto v_resetjp_174_;
}
else
{
lean_inc(v_a_173_);
lean_dec(v___x_172_);
v___x_175_ = lean_box(0);
v_isShared_176_ = v_isSharedCheck_182_;
goto v_resetjp_174_;
}
v_resetjp_174_:
{
lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_180_; 
v___x_177_ = lean_obj_once(&l_Lean_Firefox_instFromJsonCategory_fromJson___closed__12, &l_Lean_Firefox_instFromJsonCategory_fromJson___closed__12_once, _init_l_Lean_Firefox_instFromJsonCategory_fromJson___closed__12);
v___x_178_ = lean_string_append(v___x_177_, v_a_173_);
lean_dec(v_a_173_);
if (v_isShared_176_ == 0)
{
lean_ctor_set(v___x_175_, 0, v___x_178_);
v___x_180_ = v___x_175_;
goto v_reusejp_179_;
}
else
{
lean_object* v_reuseFailAlloc_181_; 
v_reuseFailAlloc_181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_181_, 0, v___x_178_);
v___x_180_ = v_reuseFailAlloc_181_;
goto v_reusejp_179_;
}
v_reusejp_179_:
{
return v___x_180_;
}
}
}
else
{
lean_object* v_a_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v_a_183_ = lean_ctor_get(v___x_172_, 0);
lean_inc(v_a_183_);
lean_dec_ref_known(v___x_172_, 1);
v___x_184_ = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__13));
lean_inc(v_json_170_);
v___x_185_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__1(v_json_170_, v___x_184_);
if (lean_obj_tag(v___x_185_) == 0)
{
lean_object* v_a_186_; lean_object* v___x_188_; uint8_t v_isShared_189_; uint8_t v_isSharedCheck_195_; 
lean_dec(v_a_183_);
lean_dec(v_json_170_);
v_a_186_ = lean_ctor_get(v___x_185_, 0);
v_isSharedCheck_195_ = !lean_is_exclusive(v___x_185_);
if (v_isSharedCheck_195_ == 0)
{
v___x_188_ = v___x_185_;
v_isShared_189_ = v_isSharedCheck_195_;
goto v_resetjp_187_;
}
else
{
lean_inc(v_a_186_);
lean_dec(v___x_185_);
v___x_188_ = lean_box(0);
v_isShared_189_ = v_isSharedCheck_195_;
goto v_resetjp_187_;
}
v_resetjp_187_:
{
lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_193_; 
v___x_190_ = lean_obj_once(&l_Lean_Firefox_instFromJsonCategory_fromJson___closed__17, &l_Lean_Firefox_instFromJsonCategory_fromJson___closed__17_once, _init_l_Lean_Firefox_instFromJsonCategory_fromJson___closed__17);
v___x_191_ = lean_string_append(v___x_190_, v_a_186_);
lean_dec(v_a_186_);
if (v_isShared_189_ == 0)
{
lean_ctor_set(v___x_188_, 0, v___x_191_);
v___x_193_ = v___x_188_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v___x_191_);
v___x_193_ = v_reuseFailAlloc_194_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
return v___x_193_;
}
}
}
else
{
lean_object* v_a_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
v_a_196_ = lean_ctor_get(v___x_185_, 0);
lean_inc(v_a_196_);
lean_dec_ref_known(v___x_185_, 1);
v___x_197_ = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__18));
v___x_198_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__2(v_json_170_, v___x_197_);
if (lean_obj_tag(v___x_198_) == 0)
{
lean_object* v_a_199_; lean_object* v___x_201_; uint8_t v_isShared_202_; uint8_t v_isSharedCheck_208_; 
lean_dec(v_a_196_);
lean_dec(v_a_183_);
v_a_199_ = lean_ctor_get(v___x_198_, 0);
v_isSharedCheck_208_ = !lean_is_exclusive(v___x_198_);
if (v_isSharedCheck_208_ == 0)
{
v___x_201_ = v___x_198_;
v_isShared_202_ = v_isSharedCheck_208_;
goto v_resetjp_200_;
}
else
{
lean_inc(v_a_199_);
lean_dec(v___x_198_);
v___x_201_ = lean_box(0);
v_isShared_202_ = v_isSharedCheck_208_;
goto v_resetjp_200_;
}
v_resetjp_200_:
{
lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_206_; 
v___x_203_ = lean_obj_once(&l_Lean_Firefox_instFromJsonCategory_fromJson___closed__22, &l_Lean_Firefox_instFromJsonCategory_fromJson___closed__22_once, _init_l_Lean_Firefox_instFromJsonCategory_fromJson___closed__22);
v___x_204_ = lean_string_append(v___x_203_, v_a_199_);
lean_dec(v_a_199_);
if (v_isShared_202_ == 0)
{
lean_ctor_set(v___x_201_, 0, v___x_204_);
v___x_206_ = v___x_201_;
goto v_reusejp_205_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_207_, 0, v___x_204_);
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
lean_object* v_a_209_; lean_object* v___x_211_; uint8_t v_isShared_212_; uint8_t v_isSharedCheck_217_; 
v_a_209_ = lean_ctor_get(v___x_198_, 0);
v_isSharedCheck_217_ = !lean_is_exclusive(v___x_198_);
if (v_isSharedCheck_217_ == 0)
{
v___x_211_ = v___x_198_;
v_isShared_212_ = v_isSharedCheck_217_;
goto v_resetjp_210_;
}
else
{
lean_inc(v_a_209_);
lean_dec(v___x_198_);
v___x_211_ = lean_box(0);
v_isShared_212_ = v_isSharedCheck_217_;
goto v_resetjp_210_;
}
v_resetjp_210_:
{
lean_object* v___x_213_; lean_object* v___x_215_; 
v___x_213_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_213_, 0, v_a_183_);
lean_ctor_set(v___x_213_, 1, v_a_196_);
lean_ctor_set(v___x_213_, 2, v_a_209_);
if (v_isShared_212_ == 0)
{
lean_ctor_set(v___x_211_, 0, v___x_213_);
v___x_215_ = v___x_211_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_216_; 
v_reuseFailAlloc_216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_216_, 0, v___x_213_);
v___x_215_ = v_reuseFailAlloc_216_;
goto v_reusejp_214_;
}
v_reusejp_214_:
{
return v___x_215_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Firefox_instToJsonCategory_toJson_spec__0_spec__0(size_t v_sz_220_, size_t v_i_221_, lean_object* v_bs_222_){
_start:
{
uint8_t v___x_223_; 
v___x_223_ = lean_usize_dec_lt(v_i_221_, v_sz_220_);
if (v___x_223_ == 0)
{
return v_bs_222_;
}
else
{
lean_object* v_v_224_; lean_object* v___x_225_; lean_object* v_bs_x27_226_; lean_object* v___x_227_; size_t v___x_228_; size_t v___x_229_; lean_object* v___x_230_; 
v_v_224_ = lean_array_uget(v_bs_222_, v_i_221_);
v___x_225_ = lean_unsigned_to_nat(0u);
v_bs_x27_226_ = lean_array_uset(v_bs_222_, v_i_221_, v___x_225_);
v___x_227_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_227_, 0, v_v_224_);
v___x_228_ = ((size_t)1ULL);
v___x_229_ = lean_usize_add(v_i_221_, v___x_228_);
v___x_230_ = lean_array_uset(v_bs_x27_226_, v_i_221_, v___x_227_);
v_i_221_ = v___x_229_;
v_bs_222_ = v___x_230_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Firefox_instToJsonCategory_toJson_spec__0_spec__0___boxed(lean_object* v_sz_232_, lean_object* v_i_233_, lean_object* v_bs_234_){
_start:
{
size_t v_sz_boxed_235_; size_t v_i_boxed_236_; lean_object* v_res_237_; 
v_sz_boxed_235_ = lean_unbox_usize(v_sz_232_);
lean_dec(v_sz_232_);
v_i_boxed_236_ = lean_unbox_usize(v_i_233_);
lean_dec(v_i_233_);
v_res_237_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Firefox_instToJsonCategory_toJson_spec__0_spec__0(v_sz_boxed_235_, v_i_boxed_236_, v_bs_234_);
return v_res_237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Firefox_instToJsonCategory_toJson_spec__0(lean_object* v_a_238_){
_start:
{
size_t v_sz_239_; size_t v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; 
v_sz_239_ = lean_array_size(v_a_238_);
v___x_240_ = ((size_t)0ULL);
v___x_241_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Firefox_instToJsonCategory_toJson_spec__0_spec__0(v_sz_239_, v___x_240_, v_a_238_);
v___x_242_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_242_, 0, v___x_241_);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Firefox_instToJsonCategory_toJson_spec__1(lean_object* v_a_243_, lean_object* v_a_244_){
_start:
{
if (lean_obj_tag(v_a_243_) == 0)
{
lean_object* v___x_245_; 
v___x_245_ = lean_array_to_list(v_a_244_);
return v___x_245_;
}
else
{
lean_object* v_head_246_; lean_object* v_tail_247_; lean_object* v___x_248_; 
v_head_246_ = lean_ctor_get(v_a_243_, 0);
lean_inc(v_head_246_);
v_tail_247_ = lean_ctor_get(v_a_243_, 1);
lean_inc(v_tail_247_);
lean_dec_ref_known(v_a_243_, 2);
v___x_248_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_244_, v_head_246_);
v_a_243_ = v_tail_247_;
v_a_244_ = v___x_248_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Firefox_instToJsonCategory_toJson(lean_object* v_x_252_){
_start:
{
lean_object* v_name_253_; lean_object* v_color_254_; lean_object* v_subcategories_255_; lean_object* v___x_256_; uint8_t v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
v_name_253_ = lean_ctor_get(v_x_252_, 0);
lean_inc(v_name_253_);
v_color_254_ = lean_ctor_get(v_x_252_, 1);
lean_inc_ref(v_color_254_);
v_subcategories_255_ = lean_ctor_get(v_x_252_, 2);
lean_inc_ref(v_subcategories_255_);
lean_dec_ref(v_x_252_);
v___x_256_ = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__0));
v___x_257_ = 1;
v___x_258_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_253_, v___x_257_);
v___x_259_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_259_, 0, v___x_258_);
v___x_260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_260_, 0, v___x_256_);
lean_ctor_set(v___x_260_, 1, v___x_259_);
v___x_261_ = lean_box(0);
v___x_262_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_262_, 0, v___x_260_);
lean_ctor_set(v___x_262_, 1, v___x_261_);
v___x_263_ = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__13));
v___x_264_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_264_, 0, v_color_254_);
v___x_265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_265_, 0, v___x_263_);
lean_ctor_set(v___x_265_, 1, v___x_264_);
v___x_266_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_266_, 0, v___x_265_);
lean_ctor_set(v___x_266_, 1, v___x_261_);
v___x_267_ = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__18));
v___x_268_ = l_Lean_Array_toJson___at___00Lean_Firefox_instToJsonCategory_toJson_spec__0(v_subcategories_255_);
v___x_269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_269_, 0, v___x_267_);
lean_ctor_set(v___x_269_, 1, v___x_268_);
v___x_270_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_270_, 0, v___x_269_);
lean_ctor_set(v___x_270_, 1, v___x_261_);
v___x_271_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_271_, 0, v___x_270_);
lean_ctor_set(v___x_271_, 1, v___x_261_);
v___x_272_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_272_, 0, v___x_266_);
lean_ctor_set(v___x_272_, 1, v___x_271_);
v___x_273_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_273_, 0, v___x_262_);
lean_ctor_set(v___x_273_, 1, v___x_272_);
v___x_274_ = ((lean_object*)(l_Lean_Firefox_instToJsonCategory_toJson___closed__0));
v___x_275_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Firefox_instToJsonCategory_toJson_spec__1(v___x_273_, v___x_274_);
v___x_276_ = l_Lean_Json_mkObj(v___x_275_);
lean_dec(v___x_275_);
return v___x_276_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__3(void){
_start:
{
uint8_t v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_285_ = 1;
v___x_286_ = ((lean_object*)(l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__2));
v___x_287_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_286_, v___x_285_);
return v___x_287_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__4(void){
_start:
{
lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_288_ = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__6));
v___x_289_ = lean_obj_once(&l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__3, &l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__3_once, _init_l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__3);
v___x_290_ = lean_string_append(v___x_289_, v___x_288_);
return v___x_290_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__6(void){
_start:
{
uint8_t v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_293_ = 1;
v___x_294_ = ((lean_object*)(l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__5));
v___x_295_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_294_, v___x_293_);
return v___x_295_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__7(void){
_start:
{
lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_296_ = lean_obj_once(&l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__6, &l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__6_once, _init_l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__6);
v___x_297_ = lean_obj_once(&l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__4, &l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__4_once, _init_l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__4);
v___x_298_ = lean_string_append(v___x_297_, v___x_296_);
return v___x_298_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__8(void){
_start:
{
lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_299_ = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
v___x_300_ = lean_obj_once(&l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__7, &l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__7_once, _init_l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__7);
v___x_301_ = lean_string_append(v___x_300_, v___x_299_);
return v___x_301_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__11(void){
_start:
{
uint8_t v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_305_ = 1;
v___x_306_ = ((lean_object*)(l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__10));
v___x_307_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_306_, v___x_305_);
return v___x_307_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__12(void){
_start:
{
lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_308_ = lean_obj_once(&l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__11, &l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__11_once, _init_l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__11);
v___x_309_ = lean_obj_once(&l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__4, &l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__4_once, _init_l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__4);
v___x_310_ = lean_string_append(v___x_309_, v___x_308_);
return v___x_310_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__13(void){
_start:
{
lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_311_ = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
v___x_312_ = lean_obj_once(&l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__12, &l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__12_once, _init_l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__12);
v___x_313_ = lean_string_append(v___x_312_, v___x_311_);
return v___x_313_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__16(void){
_start:
{
uint8_t v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_317_ = 1;
v___x_318_ = ((lean_object*)(l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__15));
v___x_319_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_318_, v___x_317_);
return v___x_319_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__17(void){
_start:
{
lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_320_ = lean_obj_once(&l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__16, &l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__16_once, _init_l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__16);
v___x_321_ = lean_obj_once(&l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__4, &l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__4_once, _init_l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__4);
v___x_322_ = lean_string_append(v___x_321_, v___x_320_);
return v___x_322_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__18(void){
_start:
{
lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_323_ = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
v___x_324_ = lean_obj_once(&l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__17, &l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__17_once, _init_l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__17);
v___x_325_ = lean_string_append(v___x_324_, v___x_323_);
return v___x_325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Firefox_instFromJsonSampleUnits_fromJson(lean_object* v_json_326_){
_start:
{
lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_327_ = ((lean_object*)(l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__0));
lean_inc(v_json_326_);
v___x_328_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__1(v_json_326_, v___x_327_);
if (lean_obj_tag(v___x_328_) == 0)
{
lean_object* v_a_329_; lean_object* v___x_331_; uint8_t v_isShared_332_; uint8_t v_isSharedCheck_338_; 
lean_dec(v_json_326_);
v_a_329_ = lean_ctor_get(v___x_328_, 0);
v_isSharedCheck_338_ = !lean_is_exclusive(v___x_328_);
if (v_isSharedCheck_338_ == 0)
{
v___x_331_ = v___x_328_;
v_isShared_332_ = v_isSharedCheck_338_;
goto v_resetjp_330_;
}
else
{
lean_inc(v_a_329_);
lean_dec(v___x_328_);
v___x_331_ = lean_box(0);
v_isShared_332_ = v_isSharedCheck_338_;
goto v_resetjp_330_;
}
v_resetjp_330_:
{
lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_336_; 
v___x_333_ = lean_obj_once(&l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__8, &l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__8_once, _init_l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__8);
v___x_334_ = lean_string_append(v___x_333_, v_a_329_);
lean_dec(v_a_329_);
if (v_isShared_332_ == 0)
{
lean_ctor_set(v___x_331_, 0, v___x_334_);
v___x_336_ = v___x_331_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_337_; 
v_reuseFailAlloc_337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_337_, 0, v___x_334_);
v___x_336_ = v_reuseFailAlloc_337_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
return v___x_336_;
}
}
}
else
{
lean_object* v_a_339_; lean_object* v___x_340_; lean_object* v___x_341_; 
v_a_339_ = lean_ctor_get(v___x_328_, 0);
lean_inc(v_a_339_);
lean_dec_ref_known(v___x_328_, 1);
v___x_340_ = ((lean_object*)(l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__9));
lean_inc(v_json_326_);
v___x_341_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__1(v_json_326_, v___x_340_);
if (lean_obj_tag(v___x_341_) == 0)
{
lean_object* v_a_342_; lean_object* v___x_344_; uint8_t v_isShared_345_; uint8_t v_isSharedCheck_351_; 
lean_dec(v_a_339_);
lean_dec(v_json_326_);
v_a_342_ = lean_ctor_get(v___x_341_, 0);
v_isSharedCheck_351_ = !lean_is_exclusive(v___x_341_);
if (v_isSharedCheck_351_ == 0)
{
v___x_344_ = v___x_341_;
v_isShared_345_ = v_isSharedCheck_351_;
goto v_resetjp_343_;
}
else
{
lean_inc(v_a_342_);
lean_dec(v___x_341_);
v___x_344_ = lean_box(0);
v_isShared_345_ = v_isSharedCheck_351_;
goto v_resetjp_343_;
}
v_resetjp_343_:
{
lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_349_; 
v___x_346_ = lean_obj_once(&l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__13, &l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__13_once, _init_l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__13);
v___x_347_ = lean_string_append(v___x_346_, v_a_342_);
lean_dec(v_a_342_);
if (v_isShared_345_ == 0)
{
lean_ctor_set(v___x_344_, 0, v___x_347_);
v___x_349_ = v___x_344_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v___x_347_);
v___x_349_ = v_reuseFailAlloc_350_;
goto v_reusejp_348_;
}
v_reusejp_348_:
{
return v___x_349_;
}
}
}
else
{
lean_object* v_a_352_; lean_object* v___x_353_; lean_object* v___x_354_; 
v_a_352_ = lean_ctor_get(v___x_341_, 0);
lean_inc(v_a_352_);
lean_dec_ref_known(v___x_341_, 1);
v___x_353_ = ((lean_object*)(l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__14));
v___x_354_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__1(v_json_326_, v___x_353_);
if (lean_obj_tag(v___x_354_) == 0)
{
lean_object* v_a_355_; lean_object* v___x_357_; uint8_t v_isShared_358_; uint8_t v_isSharedCheck_364_; 
lean_dec(v_a_352_);
lean_dec(v_a_339_);
v_a_355_ = lean_ctor_get(v___x_354_, 0);
v_isSharedCheck_364_ = !lean_is_exclusive(v___x_354_);
if (v_isSharedCheck_364_ == 0)
{
v___x_357_ = v___x_354_;
v_isShared_358_ = v_isSharedCheck_364_;
goto v_resetjp_356_;
}
else
{
lean_inc(v_a_355_);
lean_dec(v___x_354_);
v___x_357_ = lean_box(0);
v_isShared_358_ = v_isSharedCheck_364_;
goto v_resetjp_356_;
}
v_resetjp_356_:
{
lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_362_; 
v___x_359_ = lean_obj_once(&l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__18, &l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__18_once, _init_l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__18);
v___x_360_ = lean_string_append(v___x_359_, v_a_355_);
lean_dec(v_a_355_);
if (v_isShared_358_ == 0)
{
lean_ctor_set(v___x_357_, 0, v___x_360_);
v___x_362_ = v___x_357_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_363_; 
v_reuseFailAlloc_363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_363_, 0, v___x_360_);
v___x_362_ = v_reuseFailAlloc_363_;
goto v_reusejp_361_;
}
v_reusejp_361_:
{
return v___x_362_;
}
}
}
else
{
lean_object* v_a_365_; lean_object* v___x_367_; uint8_t v_isShared_368_; uint8_t v_isSharedCheck_373_; 
v_a_365_ = lean_ctor_get(v___x_354_, 0);
v_isSharedCheck_373_ = !lean_is_exclusive(v___x_354_);
if (v_isSharedCheck_373_ == 0)
{
v___x_367_ = v___x_354_;
v_isShared_368_ = v_isSharedCheck_373_;
goto v_resetjp_366_;
}
else
{
lean_inc(v_a_365_);
lean_dec(v___x_354_);
v___x_367_ = lean_box(0);
v_isShared_368_ = v_isSharedCheck_373_;
goto v_resetjp_366_;
}
v_resetjp_366_:
{
lean_object* v___x_369_; lean_object* v___x_371_; 
v___x_369_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_369_, 0, v_a_339_);
lean_ctor_set(v___x_369_, 1, v_a_352_);
lean_ctor_set(v___x_369_, 2, v_a_365_);
if (v_isShared_368_ == 0)
{
lean_ctor_set(v___x_367_, 0, v___x_369_);
v___x_371_ = v___x_367_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v___x_369_);
v___x_371_ = v_reuseFailAlloc_372_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
return v___x_371_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Firefox_instToJsonSampleUnits_toJson(lean_object* v_x_376_){
_start:
{
lean_object* v_time_377_; lean_object* v_eventDelay_378_; lean_object* v_threadCPUDelta_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; 
v_time_377_ = lean_ctor_get(v_x_376_, 0);
v_eventDelay_378_ = lean_ctor_get(v_x_376_, 1);
v_threadCPUDelta_379_ = lean_ctor_get(v_x_376_, 2);
v___x_380_ = ((lean_object*)(l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__0));
lean_inc_ref(v_time_377_);
v___x_381_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_381_, 0, v_time_377_);
v___x_382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_382_, 0, v___x_380_);
lean_ctor_set(v___x_382_, 1, v___x_381_);
v___x_383_ = lean_box(0);
v___x_384_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_384_, 0, v___x_382_);
lean_ctor_set(v___x_384_, 1, v___x_383_);
v___x_385_ = ((lean_object*)(l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__9));
lean_inc_ref(v_eventDelay_378_);
v___x_386_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_386_, 0, v_eventDelay_378_);
v___x_387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_387_, 0, v___x_385_);
lean_ctor_set(v___x_387_, 1, v___x_386_);
v___x_388_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_388_, 0, v___x_387_);
lean_ctor_set(v___x_388_, 1, v___x_383_);
v___x_389_ = ((lean_object*)(l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__14));
lean_inc_ref(v_threadCPUDelta_379_);
v___x_390_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_390_, 0, v_threadCPUDelta_379_);
v___x_391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_391_, 0, v___x_389_);
lean_ctor_set(v___x_391_, 1, v___x_390_);
v___x_392_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_392_, 0, v___x_391_);
lean_ctor_set(v___x_392_, 1, v___x_383_);
v___x_393_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_393_, 0, v___x_392_);
lean_ctor_set(v___x_393_, 1, v___x_383_);
v___x_394_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_394_, 0, v___x_388_);
lean_ctor_set(v___x_394_, 1, v___x_393_);
v___x_395_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_395_, 0, v___x_384_);
lean_ctor_set(v___x_395_, 1, v___x_394_);
v___x_396_ = ((lean_object*)(l_Lean_Firefox_instToJsonCategory_toJson___closed__0));
v___x_397_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Firefox_instToJsonCategory_toJson_spec__1(v___x_395_, v___x_396_);
v___x_398_ = l_Lean_Json_mkObj(v___x_397_);
lean_dec(v___x_397_);
return v___x_398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Firefox_instToJsonSampleUnits_toJson___boxed(lean_object* v_x_399_){
_start:
{
lean_object* v_res_400_; 
v_res_400_ = l_Lean_Firefox_instToJsonSampleUnits_toJson(v_x_399_);
lean_dec_ref(v_x_399_);
return v_res_400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__0(lean_object* v_j_403_, lean_object* v_k_404_){
_start:
{
lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_405_ = l_Lean_Json_getObjValD(v_j_403_, v_k_404_);
v___x_406_ = l_Lean_Float_fromJson_x3f(v___x_405_);
if (lean_obj_tag(v___x_406_) == 0)
{
lean_object* v_a_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_414_; 
v_a_407_ = lean_ctor_get(v___x_406_, 0);
v_isSharedCheck_414_ = !lean_is_exclusive(v___x_406_);
if (v_isSharedCheck_414_ == 0)
{
v___x_409_ = v___x_406_;
v_isShared_410_ = v_isSharedCheck_414_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_a_407_);
lean_dec(v___x_406_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_414_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v___x_412_; 
if (v_isShared_410_ == 0)
{
v___x_412_ = v___x_409_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v_a_407_);
v___x_412_ = v_reuseFailAlloc_413_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
return v___x_412_;
}
}
}
else
{
lean_object* v_a_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_422_; 
v_a_415_ = lean_ctor_get(v___x_406_, 0);
v_isSharedCheck_422_ = !lean_is_exclusive(v___x_406_);
if (v_isSharedCheck_422_ == 0)
{
v___x_417_ = v___x_406_;
v_isShared_418_ = v_isSharedCheck_422_;
goto v_resetjp_416_;
}
else
{
lean_inc(v_a_415_);
lean_dec(v___x_406_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_422_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
lean_object* v___x_420_; 
if (v_isShared_418_ == 0)
{
v___x_420_ = v___x_417_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v_a_415_);
v___x_420_ = v_reuseFailAlloc_421_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
return v___x_420_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__0___boxed(lean_object* v_j_423_, lean_object* v_k_424_){
_start:
{
lean_object* v_res_425_; 
v_res_425_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__0(v_j_423_, v_k_424_);
lean_dec_ref(v_k_424_);
return v_res_425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__2(lean_object* v_j_426_, lean_object* v_k_427_){
_start:
{
lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_428_ = l_Lean_Json_getObjValD(v_j_426_, v_k_427_);
v___x_429_ = l_Lean_Json_getNat_x3f(v___x_428_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__2___boxed(lean_object* v_j_430_, lean_object* v_k_431_){
_start:
{
lean_object* v_res_432_; 
v_res_432_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__2(v_j_430_, v_k_431_);
lean_dec_ref(v_k_431_);
return v_res_432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__4(lean_object* v_j_433_, lean_object* v_k_434_){
_start:
{
lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_435_ = l_Lean_Json_getObjValD(v_j_433_, v_k_434_);
v___x_436_ = l_Lean_Firefox_instFromJsonSampleUnits_fromJson(v___x_435_);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__4___boxed(lean_object* v_j_437_, lean_object* v_k_438_){
_start:
{
lean_object* v_res_439_; 
v_res_439_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__4(v_j_437_, v_k_438_);
lean_dec_ref(v_k_438_);
return v_res_439_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__1_spec__1_spec__4(size_t v_sz_440_, size_t v_i_441_, lean_object* v_bs_442_){
_start:
{
uint8_t v___x_443_; 
v___x_443_ = lean_usize_dec_lt(v_i_441_, v_sz_440_);
if (v___x_443_ == 0)
{
lean_object* v___x_444_; 
v___x_444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_444_, 0, v_bs_442_);
return v___x_444_;
}
else
{
lean_object* v_v_445_; lean_object* v___x_446_; 
v_v_445_ = lean_array_uget_borrowed(v_bs_442_, v_i_441_);
lean_inc(v_v_445_);
v___x_446_ = l_Lean_Firefox_instFromJsonCategory_fromJson(v_v_445_);
if (lean_obj_tag(v___x_446_) == 0)
{
lean_object* v_a_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_454_; 
lean_dec_ref(v_bs_442_);
v_a_447_ = lean_ctor_get(v___x_446_, 0);
v_isSharedCheck_454_ = !lean_is_exclusive(v___x_446_);
if (v_isSharedCheck_454_ == 0)
{
v___x_449_ = v___x_446_;
v_isShared_450_ = v_isSharedCheck_454_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_a_447_);
lean_dec(v___x_446_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_454_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v___x_452_; 
if (v_isShared_450_ == 0)
{
v___x_452_ = v___x_449_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v_a_447_);
v___x_452_ = v_reuseFailAlloc_453_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
return v___x_452_;
}
}
}
else
{
lean_object* v_a_455_; lean_object* v___x_456_; lean_object* v_bs_x27_457_; size_t v___x_458_; size_t v___x_459_; lean_object* v___x_460_; 
v_a_455_ = lean_ctor_get(v___x_446_, 0);
lean_inc(v_a_455_);
lean_dec_ref_known(v___x_446_, 1);
v___x_456_ = lean_unsigned_to_nat(0u);
v_bs_x27_457_ = lean_array_uset(v_bs_442_, v_i_441_, v___x_456_);
v___x_458_ = ((size_t)1ULL);
v___x_459_ = lean_usize_add(v_i_441_, v___x_458_);
v___x_460_ = lean_array_uset(v_bs_x27_457_, v_i_441_, v_a_455_);
v_i_441_ = v___x_459_;
v_bs_442_ = v___x_460_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__1_spec__1_spec__4___boxed(lean_object* v_sz_462_, lean_object* v_i_463_, lean_object* v_bs_464_){
_start:
{
size_t v_sz_boxed_465_; size_t v_i_boxed_466_; lean_object* v_res_467_; 
v_sz_boxed_465_ = lean_unbox_usize(v_sz_462_);
lean_dec(v_sz_462_);
v_i_boxed_466_ = lean_unbox_usize(v_i_463_);
lean_dec(v_i_463_);
v_res_467_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__1_spec__1_spec__4(v_sz_boxed_465_, v_i_boxed_466_, v_bs_464_);
return v_res_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__1_spec__1(lean_object* v_x_468_){
_start:
{
if (lean_obj_tag(v_x_468_) == 4)
{
lean_object* v_elems_469_; size_t v_sz_470_; size_t v___x_471_; lean_object* v___x_472_; 
v_elems_469_ = lean_ctor_get(v_x_468_, 0);
lean_inc_ref(v_elems_469_);
lean_dec_ref_known(v_x_468_, 1);
v_sz_470_ = lean_array_size(v_elems_469_);
v___x_471_ = ((size_t)0ULL);
v___x_472_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__1_spec__1_spec__4(v_sz_470_, v___x_471_, v_elems_469_);
return v___x_472_;
}
else
{
lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; 
v___x_473_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__2_spec__2___closed__0));
v___x_474_ = lean_unsigned_to_nat(80u);
v___x_475_ = l_Lean_Json_pretty(v_x_468_, v___x_474_);
v___x_476_ = lean_string_append(v___x_473_, v___x_475_);
lean_dec_ref(v___x_475_);
v___x_477_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__2_spec__2___closed__1));
v___x_478_ = lean_string_append(v___x_476_, v___x_477_);
v___x_479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_479_, 0, v___x_478_);
return v___x_479_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__1(lean_object* v_j_480_, lean_object* v_k_481_){
_start:
{
lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_482_ = l_Lean_Json_getObjValD(v_j_480_, v_k_481_);
v___x_483_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__1_spec__1(v___x_482_);
return v___x_483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__1___boxed(lean_object* v_j_484_, lean_object* v_k_485_){
_start:
{
lean_object* v_res_486_; 
v_res_486_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__1(v_j_484_, v_k_485_);
lean_dec_ref(v_k_485_);
return v_res_486_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__3_spec__4_spec__7(size_t v_sz_487_, size_t v_i_488_, lean_object* v_bs_489_){
_start:
{
uint8_t v___x_490_; 
v___x_490_ = lean_usize_dec_lt(v_i_488_, v_sz_487_);
if (v___x_490_ == 0)
{
lean_object* v___x_491_; 
v___x_491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_491_, 0, v_bs_489_);
return v___x_491_;
}
else
{
lean_object* v_v_492_; lean_object* v___x_493_; lean_object* v_bs_x27_494_; size_t v___x_495_; size_t v___x_496_; lean_object* v___x_497_; 
v_v_492_ = lean_array_uget(v_bs_489_, v_i_488_);
v___x_493_ = lean_unsigned_to_nat(0u);
v_bs_x27_494_ = lean_array_uset(v_bs_489_, v_i_488_, v___x_493_);
v___x_495_ = ((size_t)1ULL);
v___x_496_ = lean_usize_add(v_i_488_, v___x_495_);
v___x_497_ = lean_array_uset(v_bs_x27_494_, v_i_488_, v_v_492_);
v_i_488_ = v___x_496_;
v_bs_489_ = v___x_497_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__3_spec__4_spec__7___boxed(lean_object* v_sz_499_, lean_object* v_i_500_, lean_object* v_bs_501_){
_start:
{
size_t v_sz_boxed_502_; size_t v_i_boxed_503_; lean_object* v_res_504_; 
v_sz_boxed_502_ = lean_unbox_usize(v_sz_499_);
lean_dec(v_sz_499_);
v_i_boxed_503_ = lean_unbox_usize(v_i_500_);
lean_dec(v_i_500_);
v_res_504_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__3_spec__4_spec__7(v_sz_boxed_502_, v_i_boxed_503_, v_bs_501_);
return v_res_504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__3_spec__4(lean_object* v_x_505_){
_start:
{
if (lean_obj_tag(v_x_505_) == 4)
{
lean_object* v_elems_506_; size_t v_sz_507_; size_t v___x_508_; lean_object* v___x_509_; 
v_elems_506_ = lean_ctor_get(v_x_505_, 0);
lean_inc_ref(v_elems_506_);
lean_dec_ref_known(v_x_505_, 1);
v_sz_507_ = lean_array_size(v_elems_506_);
v___x_508_ = ((size_t)0ULL);
v___x_509_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__3_spec__4_spec__7(v_sz_507_, v___x_508_, v_elems_506_);
return v___x_509_;
}
else
{
lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_510_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__2_spec__2___closed__0));
v___x_511_ = lean_unsigned_to_nat(80u);
v___x_512_ = l_Lean_Json_pretty(v_x_505_, v___x_511_);
v___x_513_ = lean_string_append(v___x_510_, v___x_512_);
lean_dec_ref(v___x_512_);
v___x_514_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__2_spec__2___closed__1));
v___x_515_ = lean_string_append(v___x_513_, v___x_514_);
v___x_516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_516_, 0, v___x_515_);
return v___x_516_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__3(lean_object* v_j_517_, lean_object* v_k_518_){
_start:
{
lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_519_ = l_Lean_Json_getObjValD(v_j_517_, v_k_518_);
v___x_520_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__3_spec__4(v___x_519_);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__3___boxed(lean_object* v_j_521_, lean_object* v_k_522_){
_start:
{
lean_object* v_res_523_; 
v_res_523_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__3(v_j_521_, v_k_522_);
lean_dec_ref(v_k_522_);
return v_res_523_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__3(void){
_start:
{
uint8_t v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_530_ = 1;
v___x_531_ = ((lean_object*)(l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__2));
v___x_532_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_531_, v___x_530_);
return v___x_532_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__4(void){
_start:
{
lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_533_ = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__6));
v___x_534_ = lean_obj_once(&l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__3, &l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__3_once, _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__3);
v___x_535_ = lean_string_append(v___x_534_, v___x_533_);
return v___x_535_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__6(void){
_start:
{
uint8_t v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_538_ = 1;
v___x_539_ = ((lean_object*)(l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__5));
v___x_540_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_539_, v___x_538_);
return v___x_540_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__7(void){
_start:
{
lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; 
v___x_541_ = lean_obj_once(&l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__6, &l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__6_once, _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__6);
v___x_542_ = lean_obj_once(&l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__4, &l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__4_once, _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__4);
v___x_543_ = lean_string_append(v___x_542_, v___x_541_);
return v___x_543_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__8(void){
_start:
{
lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; 
v___x_544_ = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
v___x_545_ = lean_obj_once(&l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__7, &l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__7_once, _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__7);
v___x_546_ = lean_string_append(v___x_545_, v___x_544_);
return v___x_546_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__11(void){
_start:
{
uint8_t v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; 
v___x_550_ = 1;
v___x_551_ = ((lean_object*)(l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__10));
v___x_552_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_551_, v___x_550_);
return v___x_552_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__12(void){
_start:
{
lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; 
v___x_553_ = lean_obj_once(&l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__11, &l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__11_once, _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__11);
v___x_554_ = lean_obj_once(&l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__4, &l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__4_once, _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__4);
v___x_555_ = lean_string_append(v___x_554_, v___x_553_);
return v___x_555_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__13(void){
_start:
{
lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_556_ = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
v___x_557_ = lean_obj_once(&l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__12, &l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__12_once, _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__12);
v___x_558_ = lean_string_append(v___x_557_, v___x_556_);
return v___x_558_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__16(void){
_start:
{
uint8_t v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; 
v___x_562_ = 1;
v___x_563_ = ((lean_object*)(l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__15));
v___x_564_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_563_, v___x_562_);
return v___x_564_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__17(void){
_start:
{
lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; 
v___x_565_ = lean_obj_once(&l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__16, &l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__16_once, _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__16);
v___x_566_ = lean_obj_once(&l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__4, &l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__4_once, _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__4);
v___x_567_ = lean_string_append(v___x_566_, v___x_565_);
return v___x_567_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__18(void){
_start:
{
lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; 
v___x_568_ = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
v___x_569_ = lean_obj_once(&l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__17, &l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__17_once, _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__17);
v___x_570_ = lean_string_append(v___x_569_, v___x_568_);
return v___x_570_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__21(void){
_start:
{
uint8_t v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_574_ = 1;
v___x_575_ = ((lean_object*)(l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__20));
v___x_576_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_575_, v___x_574_);
return v___x_576_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__22(void){
_start:
{
lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; 
v___x_577_ = lean_obj_once(&l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__21, &l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__21_once, _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__21);
v___x_578_ = lean_obj_once(&l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__4, &l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__4_once, _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__4);
v___x_579_ = lean_string_append(v___x_578_, v___x_577_);
return v___x_579_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__23(void){
_start:
{
lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; 
v___x_580_ = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
v___x_581_ = lean_obj_once(&l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__22, &l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__22_once, _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__22);
v___x_582_ = lean_string_append(v___x_581_, v___x_580_);
return v___x_582_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__26(void){
_start:
{
uint8_t v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; 
v___x_586_ = 1;
v___x_587_ = ((lean_object*)(l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__25));
v___x_588_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_587_, v___x_586_);
return v___x_588_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__27(void){
_start:
{
lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; 
v___x_589_ = lean_obj_once(&l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__26, &l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__26_once, _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__26);
v___x_590_ = lean_obj_once(&l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__4, &l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__4_once, _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__4);
v___x_591_ = lean_string_append(v___x_590_, v___x_589_);
return v___x_591_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__28(void){
_start:
{
lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; 
v___x_592_ = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
v___x_593_ = lean_obj_once(&l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__27, &l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__27_once, _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__27);
v___x_594_ = lean_string_append(v___x_593_, v___x_592_);
return v___x_594_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__31(void){
_start:
{
uint8_t v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; 
v___x_598_ = 1;
v___x_599_ = ((lean_object*)(l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__30));
v___x_600_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_599_, v___x_598_);
return v___x_600_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__32(void){
_start:
{
lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; 
v___x_601_ = lean_obj_once(&l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__31, &l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__31_once, _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__31);
v___x_602_ = lean_obj_once(&l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__4, &l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__4_once, _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__4);
v___x_603_ = lean_string_append(v___x_602_, v___x_601_);
return v___x_603_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__33(void){
_start:
{
lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; 
v___x_604_ = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
v___x_605_ = lean_obj_once(&l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__32, &l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__32_once, _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__32);
v___x_606_ = lean_string_append(v___x_605_, v___x_604_);
return v___x_606_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__36(void){
_start:
{
uint8_t v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_610_ = 1;
v___x_611_ = ((lean_object*)(l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__35));
v___x_612_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_611_, v___x_610_);
return v___x_612_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__37(void){
_start:
{
lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_613_ = lean_obj_once(&l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__36, &l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__36_once, _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__36);
v___x_614_ = lean_obj_once(&l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__4, &l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__4_once, _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__4);
v___x_615_ = lean_string_append(v___x_614_, v___x_613_);
return v___x_615_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__38(void){
_start:
{
lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; 
v___x_616_ = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
v___x_617_ = lean_obj_once(&l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__37, &l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__37_once, _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__37);
v___x_618_ = lean_string_append(v___x_617_, v___x_616_);
return v___x_618_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__41(void){
_start:
{
uint8_t v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; 
v___x_622_ = 1;
v___x_623_ = ((lean_object*)(l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__40));
v___x_624_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_623_, v___x_622_);
return v___x_624_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__42(void){
_start:
{
lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_625_ = lean_obj_once(&l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__41, &l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__41_once, _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__41);
v___x_626_ = lean_obj_once(&l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__4, &l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__4_once, _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__4);
v___x_627_ = lean_string_append(v___x_626_, v___x_625_);
return v___x_627_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__43(void){
_start:
{
lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_628_ = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
v___x_629_ = lean_obj_once(&l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__42, &l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__42_once, _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__42);
v___x_630_ = lean_string_append(v___x_629_, v___x_628_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Firefox_instFromJsonProfileMeta_fromJson(lean_object* v_json_631_){
_start:
{
lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_632_ = ((lean_object*)(l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__0));
lean_inc(v_json_631_);
v___x_633_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__0(v_json_631_, v___x_632_);
if (lean_obj_tag(v___x_633_) == 0)
{
lean_object* v_a_634_; lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_643_; 
lean_dec(v_json_631_);
v_a_634_ = lean_ctor_get(v___x_633_, 0);
v_isSharedCheck_643_ = !lean_is_exclusive(v___x_633_);
if (v_isSharedCheck_643_ == 0)
{
v___x_636_ = v___x_633_;
v_isShared_637_ = v_isSharedCheck_643_;
goto v_resetjp_635_;
}
else
{
lean_inc(v_a_634_);
lean_dec(v___x_633_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_643_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_641_; 
v___x_638_ = lean_obj_once(&l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__8, &l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__8_once, _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__8);
v___x_639_ = lean_string_append(v___x_638_, v_a_634_);
lean_dec(v_a_634_);
if (v_isShared_637_ == 0)
{
lean_ctor_set(v___x_636_, 0, v___x_639_);
v___x_641_ = v___x_636_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v___x_639_);
v___x_641_ = v_reuseFailAlloc_642_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
return v___x_641_;
}
}
}
else
{
lean_object* v_a_644_; lean_object* v___x_645_; lean_object* v___x_646_; 
v_a_644_ = lean_ctor_get(v___x_633_, 0);
lean_inc(v_a_644_);
lean_dec_ref_known(v___x_633_, 1);
v___x_645_ = ((lean_object*)(l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__9));
lean_inc(v_json_631_);
v___x_646_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__0(v_json_631_, v___x_645_);
if (lean_obj_tag(v___x_646_) == 0)
{
lean_object* v_a_647_; lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_656_; 
lean_dec(v_a_644_);
lean_dec(v_json_631_);
v_a_647_ = lean_ctor_get(v___x_646_, 0);
v_isSharedCheck_656_ = !lean_is_exclusive(v___x_646_);
if (v_isSharedCheck_656_ == 0)
{
v___x_649_ = v___x_646_;
v_isShared_650_ = v_isSharedCheck_656_;
goto v_resetjp_648_;
}
else
{
lean_inc(v_a_647_);
lean_dec(v___x_646_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_656_;
goto v_resetjp_648_;
}
v_resetjp_648_:
{
lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_654_; 
v___x_651_ = lean_obj_once(&l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__13, &l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__13_once, _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__13);
v___x_652_ = lean_string_append(v___x_651_, v_a_647_);
lean_dec(v_a_647_);
if (v_isShared_650_ == 0)
{
lean_ctor_set(v___x_649_, 0, v___x_652_);
v___x_654_ = v___x_649_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v___x_652_);
v___x_654_ = v_reuseFailAlloc_655_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
return v___x_654_;
}
}
}
else
{
lean_object* v_a_657_; lean_object* v___x_658_; lean_object* v___x_659_; 
v_a_657_ = lean_ctor_get(v___x_646_, 0);
lean_inc(v_a_657_);
lean_dec_ref_known(v___x_646_, 1);
v___x_658_ = ((lean_object*)(l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__14));
lean_inc(v_json_631_);
v___x_659_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__1(v_json_631_, v___x_658_);
if (lean_obj_tag(v___x_659_) == 0)
{
lean_object* v_a_660_; lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_669_; 
lean_dec(v_a_657_);
lean_dec(v_a_644_);
lean_dec(v_json_631_);
v_a_660_ = lean_ctor_get(v___x_659_, 0);
v_isSharedCheck_669_ = !lean_is_exclusive(v___x_659_);
if (v_isSharedCheck_669_ == 0)
{
v___x_662_ = v___x_659_;
v_isShared_663_ = v_isSharedCheck_669_;
goto v_resetjp_661_;
}
else
{
lean_inc(v_a_660_);
lean_dec(v___x_659_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_669_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_667_; 
v___x_664_ = lean_obj_once(&l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__18, &l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__18_once, _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__18);
v___x_665_ = lean_string_append(v___x_664_, v_a_660_);
lean_dec(v_a_660_);
if (v_isShared_663_ == 0)
{
lean_ctor_set(v___x_662_, 0, v___x_665_);
v___x_667_ = v___x_662_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v___x_665_);
v___x_667_ = v_reuseFailAlloc_668_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
return v___x_667_;
}
}
}
else
{
lean_object* v_a_670_; lean_object* v___x_671_; lean_object* v___x_672_; 
v_a_670_ = lean_ctor_get(v___x_659_, 0);
lean_inc(v_a_670_);
lean_dec_ref_known(v___x_659_, 1);
v___x_671_ = ((lean_object*)(l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__19));
lean_inc(v_json_631_);
v___x_672_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__2(v_json_631_, v___x_671_);
if (lean_obj_tag(v___x_672_) == 0)
{
lean_object* v_a_673_; lean_object* v___x_675_; uint8_t v_isShared_676_; uint8_t v_isSharedCheck_682_; 
lean_dec(v_a_670_);
lean_dec(v_a_657_);
lean_dec(v_a_644_);
lean_dec(v_json_631_);
v_a_673_ = lean_ctor_get(v___x_672_, 0);
v_isSharedCheck_682_ = !lean_is_exclusive(v___x_672_);
if (v_isSharedCheck_682_ == 0)
{
v___x_675_ = v___x_672_;
v_isShared_676_ = v_isSharedCheck_682_;
goto v_resetjp_674_;
}
else
{
lean_inc(v_a_673_);
lean_dec(v___x_672_);
v___x_675_ = lean_box(0);
v_isShared_676_ = v_isSharedCheck_682_;
goto v_resetjp_674_;
}
v_resetjp_674_:
{
lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_680_; 
v___x_677_ = lean_obj_once(&l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__23, &l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__23_once, _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__23);
v___x_678_ = lean_string_append(v___x_677_, v_a_673_);
lean_dec(v_a_673_);
if (v_isShared_676_ == 0)
{
lean_ctor_set(v___x_675_, 0, v___x_678_);
v___x_680_ = v___x_675_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v___x_678_);
v___x_680_ = v_reuseFailAlloc_681_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
return v___x_680_;
}
}
}
else
{
lean_object* v_a_683_; lean_object* v___x_684_; lean_object* v___x_685_; 
v_a_683_ = lean_ctor_get(v___x_672_, 0);
lean_inc(v_a_683_);
lean_dec_ref_known(v___x_672_, 1);
v___x_684_ = ((lean_object*)(l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__24));
lean_inc(v_json_631_);
v___x_685_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__1(v_json_631_, v___x_684_);
if (lean_obj_tag(v___x_685_) == 0)
{
lean_object* v_a_686_; lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_695_; 
lean_dec(v_a_683_);
lean_dec(v_a_670_);
lean_dec(v_a_657_);
lean_dec(v_a_644_);
lean_dec(v_json_631_);
v_a_686_ = lean_ctor_get(v___x_685_, 0);
v_isSharedCheck_695_ = !lean_is_exclusive(v___x_685_);
if (v_isSharedCheck_695_ == 0)
{
v___x_688_ = v___x_685_;
v_isShared_689_ = v_isSharedCheck_695_;
goto v_resetjp_687_;
}
else
{
lean_inc(v_a_686_);
lean_dec(v___x_685_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_695_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_693_; 
v___x_690_ = lean_obj_once(&l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__28, &l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__28_once, _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__28);
v___x_691_ = lean_string_append(v___x_690_, v_a_686_);
lean_dec(v_a_686_);
if (v_isShared_689_ == 0)
{
lean_ctor_set(v___x_688_, 0, v___x_691_);
v___x_693_ = v___x_688_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v___x_691_);
v___x_693_ = v_reuseFailAlloc_694_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
return v___x_693_;
}
}
}
else
{
lean_object* v_a_696_; lean_object* v___x_697_; lean_object* v___x_698_; 
v_a_696_ = lean_ctor_get(v___x_685_, 0);
lean_inc(v_a_696_);
lean_dec_ref_known(v___x_685_, 1);
v___x_697_ = ((lean_object*)(l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__29));
lean_inc(v_json_631_);
v___x_698_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__2(v_json_631_, v___x_697_);
if (lean_obj_tag(v___x_698_) == 0)
{
lean_object* v_a_699_; lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_708_; 
lean_dec(v_a_696_);
lean_dec(v_a_683_);
lean_dec(v_a_670_);
lean_dec(v_a_657_);
lean_dec(v_a_644_);
lean_dec(v_json_631_);
v_a_699_ = lean_ctor_get(v___x_698_, 0);
v_isSharedCheck_708_ = !lean_is_exclusive(v___x_698_);
if (v_isSharedCheck_708_ == 0)
{
v___x_701_ = v___x_698_;
v_isShared_702_ = v_isSharedCheck_708_;
goto v_resetjp_700_;
}
else
{
lean_inc(v_a_699_);
lean_dec(v___x_698_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_708_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_706_; 
v___x_703_ = lean_obj_once(&l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__33, &l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__33_once, _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__33);
v___x_704_ = lean_string_append(v___x_703_, v_a_699_);
lean_dec(v_a_699_);
if (v_isShared_702_ == 0)
{
lean_ctor_set(v___x_701_, 0, v___x_704_);
v___x_706_ = v___x_701_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v___x_704_);
v___x_706_ = v_reuseFailAlloc_707_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
return v___x_706_;
}
}
}
else
{
lean_object* v_a_709_; lean_object* v___x_710_; lean_object* v___x_711_; 
v_a_709_ = lean_ctor_get(v___x_698_, 0);
lean_inc(v_a_709_);
lean_dec_ref_known(v___x_698_, 1);
v___x_710_ = ((lean_object*)(l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__34));
lean_inc(v_json_631_);
v___x_711_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__3(v_json_631_, v___x_710_);
if (lean_obj_tag(v___x_711_) == 0)
{
lean_object* v_a_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_721_; 
lean_dec(v_a_709_);
lean_dec(v_a_696_);
lean_dec(v_a_683_);
lean_dec(v_a_670_);
lean_dec(v_a_657_);
lean_dec(v_a_644_);
lean_dec(v_json_631_);
v_a_712_ = lean_ctor_get(v___x_711_, 0);
v_isSharedCheck_721_ = !lean_is_exclusive(v___x_711_);
if (v_isSharedCheck_721_ == 0)
{
v___x_714_ = v___x_711_;
v_isShared_715_ = v_isSharedCheck_721_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_a_712_);
lean_dec(v___x_711_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_721_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_719_; 
v___x_716_ = lean_obj_once(&l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__38, &l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__38_once, _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__38);
v___x_717_ = lean_string_append(v___x_716_, v_a_712_);
lean_dec(v_a_712_);
if (v_isShared_715_ == 0)
{
lean_ctor_set(v___x_714_, 0, v___x_717_);
v___x_719_ = v___x_714_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v___x_717_);
v___x_719_ = v_reuseFailAlloc_720_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
return v___x_719_;
}
}
}
else
{
lean_object* v_a_722_; lean_object* v___x_723_; lean_object* v___x_724_; 
v_a_722_ = lean_ctor_get(v___x_711_, 0);
lean_inc(v_a_722_);
lean_dec_ref_known(v___x_711_, 1);
v___x_723_ = ((lean_object*)(l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__39));
v___x_724_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__4(v_json_631_, v___x_723_);
if (lean_obj_tag(v___x_724_) == 0)
{
lean_object* v_a_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_734_; 
lean_dec(v_a_722_);
lean_dec(v_a_709_);
lean_dec(v_a_696_);
lean_dec(v_a_683_);
lean_dec(v_a_670_);
lean_dec(v_a_657_);
lean_dec(v_a_644_);
v_a_725_ = lean_ctor_get(v___x_724_, 0);
v_isSharedCheck_734_ = !lean_is_exclusive(v___x_724_);
if (v_isSharedCheck_734_ == 0)
{
v___x_727_ = v___x_724_;
v_isShared_728_ = v_isSharedCheck_734_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_a_725_);
lean_dec(v___x_724_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_734_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_732_; 
v___x_729_ = lean_obj_once(&l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__43, &l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__43_once, _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__43);
v___x_730_ = lean_string_append(v___x_729_, v_a_725_);
lean_dec(v_a_725_);
if (v_isShared_728_ == 0)
{
lean_ctor_set(v___x_727_, 0, v___x_730_);
v___x_732_ = v___x_727_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v___x_730_);
v___x_732_ = v_reuseFailAlloc_733_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
return v___x_732_;
}
}
}
else
{
lean_object* v_a_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_745_; 
v_a_735_ = lean_ctor_get(v___x_724_, 0);
v_isSharedCheck_745_ = !lean_is_exclusive(v___x_724_);
if (v_isSharedCheck_745_ == 0)
{
v___x_737_ = v___x_724_;
v_isShared_738_ = v_isSharedCheck_745_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_a_735_);
lean_dec(v___x_724_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_745_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
lean_object* v___x_739_; double v___x_740_; double v___x_741_; lean_object* v___x_743_; 
v___x_739_ = lean_alloc_ctor(0, 6, 16);
lean_ctor_set(v___x_739_, 0, v_a_670_);
lean_ctor_set(v___x_739_, 1, v_a_683_);
lean_ctor_set(v___x_739_, 2, v_a_696_);
lean_ctor_set(v___x_739_, 3, v_a_709_);
lean_ctor_set(v___x_739_, 4, v_a_722_);
lean_ctor_set(v___x_739_, 5, v_a_735_);
v___x_740_ = lean_unbox_float(v_a_644_);
lean_dec(v_a_644_);
lean_ctor_set_float(v___x_739_, sizeof(void*)*6, v___x_740_);
v___x_741_ = lean_unbox_float(v_a_657_);
lean_dec(v_a_657_);
lean_ctor_set_float(v___x_739_, sizeof(void*)*6 + 8, v___x_741_);
if (v_isShared_738_ == 0)
{
lean_ctor_set(v___x_737_, 0, v___x_739_);
v___x_743_ = v___x_737_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v___x_739_);
v___x_743_ = v_reuseFailAlloc_744_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
return v___x_743_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Firefox_instToJsonProfileMeta_toJson_spec__0_spec__0(size_t v_sz_748_, size_t v_i_749_, lean_object* v_bs_750_){
_start:
{
uint8_t v___x_751_; 
v___x_751_ = lean_usize_dec_lt(v_i_749_, v_sz_748_);
if (v___x_751_ == 0)
{
return v_bs_750_;
}
else
{
lean_object* v_v_752_; lean_object* v___x_753_; lean_object* v_bs_x27_754_; lean_object* v___x_755_; size_t v___x_756_; size_t v___x_757_; lean_object* v___x_758_; 
v_v_752_ = lean_array_uget(v_bs_750_, v_i_749_);
v___x_753_ = lean_unsigned_to_nat(0u);
v_bs_x27_754_ = lean_array_uset(v_bs_750_, v_i_749_, v___x_753_);
v___x_755_ = l_Lean_Firefox_instToJsonCategory_toJson(v_v_752_);
v___x_756_ = ((size_t)1ULL);
v___x_757_ = lean_usize_add(v_i_749_, v___x_756_);
v___x_758_ = lean_array_uset(v_bs_x27_754_, v_i_749_, v___x_755_);
v_i_749_ = v___x_757_;
v_bs_750_ = v___x_758_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Firefox_instToJsonProfileMeta_toJson_spec__0_spec__0___boxed(lean_object* v_sz_760_, lean_object* v_i_761_, lean_object* v_bs_762_){
_start:
{
size_t v_sz_boxed_763_; size_t v_i_boxed_764_; lean_object* v_res_765_; 
v_sz_boxed_763_ = lean_unbox_usize(v_sz_760_);
lean_dec(v_sz_760_);
v_i_boxed_764_ = lean_unbox_usize(v_i_761_);
lean_dec(v_i_761_);
v_res_765_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Firefox_instToJsonProfileMeta_toJson_spec__0_spec__0(v_sz_boxed_763_, v_i_boxed_764_, v_bs_762_);
return v_res_765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Firefox_instToJsonProfileMeta_toJson_spec__0(lean_object* v_a_766_){
_start:
{
size_t v_sz_767_; size_t v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; 
v_sz_767_ = lean_array_size(v_a_766_);
v___x_768_ = ((size_t)0ULL);
v___x_769_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Firefox_instToJsonProfileMeta_toJson_spec__0_spec__0(v_sz_767_, v___x_768_, v_a_766_);
v___x_770_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_770_, 0, v___x_769_);
return v___x_770_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Firefox_instToJsonProfileMeta_toJson_spec__1_spec__2(size_t v_sz_771_, size_t v_i_772_, lean_object* v_bs_773_){
_start:
{
uint8_t v___x_774_; 
v___x_774_ = lean_usize_dec_lt(v_i_772_, v_sz_771_);
if (v___x_774_ == 0)
{
return v_bs_773_;
}
else
{
lean_object* v_v_775_; lean_object* v___x_776_; lean_object* v_bs_x27_777_; size_t v___x_778_; size_t v___x_779_; lean_object* v___x_780_; 
v_v_775_ = lean_array_uget(v_bs_773_, v_i_772_);
v___x_776_ = lean_unsigned_to_nat(0u);
v_bs_x27_777_ = lean_array_uset(v_bs_773_, v_i_772_, v___x_776_);
v___x_778_ = ((size_t)1ULL);
v___x_779_ = lean_usize_add(v_i_772_, v___x_778_);
v___x_780_ = lean_array_uset(v_bs_x27_777_, v_i_772_, v_v_775_);
v_i_772_ = v___x_779_;
v_bs_773_ = v___x_780_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Firefox_instToJsonProfileMeta_toJson_spec__1_spec__2___boxed(lean_object* v_sz_782_, lean_object* v_i_783_, lean_object* v_bs_784_){
_start:
{
size_t v_sz_boxed_785_; size_t v_i_boxed_786_; lean_object* v_res_787_; 
v_sz_boxed_785_ = lean_unbox_usize(v_sz_782_);
lean_dec(v_sz_782_);
v_i_boxed_786_ = lean_unbox_usize(v_i_783_);
lean_dec(v_i_783_);
v_res_787_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Firefox_instToJsonProfileMeta_toJson_spec__1_spec__2(v_sz_boxed_785_, v_i_boxed_786_, v_bs_784_);
return v_res_787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Firefox_instToJsonProfileMeta_toJson_spec__1(lean_object* v_a_788_){
_start:
{
size_t v_sz_789_; size_t v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; 
v_sz_789_ = lean_array_size(v_a_788_);
v___x_790_ = ((size_t)0ULL);
v___x_791_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Firefox_instToJsonProfileMeta_toJson_spec__1_spec__2(v_sz_789_, v___x_790_, v_a_788_);
v___x_792_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_792_, 0, v___x_791_);
return v___x_792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Firefox_instToJsonProfileMeta_toJson(lean_object* v_x_793_){
_start:
{
double v_interval_794_; double v_startTime_795_; lean_object* v_categories_796_; lean_object* v_processType_797_; lean_object* v_product_798_; lean_object* v_preprocessedProfileVersion_799_; lean_object* v_markerSchema_800_; lean_object* v_sampleUnits_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; 
v_interval_794_ = lean_ctor_get_float(v_x_793_, sizeof(void*)*6);
v_startTime_795_ = lean_ctor_get_float(v_x_793_, sizeof(void*)*6 + 8);
v_categories_796_ = lean_ctor_get(v_x_793_, 0);
lean_inc_ref(v_categories_796_);
v_processType_797_ = lean_ctor_get(v_x_793_, 1);
lean_inc(v_processType_797_);
v_product_798_ = lean_ctor_get(v_x_793_, 2);
lean_inc_ref(v_product_798_);
v_preprocessedProfileVersion_799_ = lean_ctor_get(v_x_793_, 3);
lean_inc(v_preprocessedProfileVersion_799_);
v_markerSchema_800_ = lean_ctor_get(v_x_793_, 4);
lean_inc_ref(v_markerSchema_800_);
v_sampleUnits_801_ = lean_ctor_get(v_x_793_, 5);
lean_inc_ref(v_sampleUnits_801_);
lean_dec_ref(v_x_793_);
v___x_802_ = ((lean_object*)(l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__0));
v___x_803_ = l_Lean_Float_toJson(v_interval_794_);
v___x_804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_804_, 0, v___x_802_);
lean_ctor_set(v___x_804_, 1, v___x_803_);
v___x_805_ = lean_box(0);
v___x_806_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_806_, 0, v___x_804_);
lean_ctor_set(v___x_806_, 1, v___x_805_);
v___x_807_ = ((lean_object*)(l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__9));
v___x_808_ = l_Lean_Float_toJson(v_startTime_795_);
v___x_809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_809_, 0, v___x_807_);
lean_ctor_set(v___x_809_, 1, v___x_808_);
v___x_810_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_810_, 0, v___x_809_);
lean_ctor_set(v___x_810_, 1, v___x_805_);
v___x_811_ = ((lean_object*)(l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__14));
v___x_812_ = l_Lean_Array_toJson___at___00Lean_Firefox_instToJsonProfileMeta_toJson_spec__0(v_categories_796_);
v___x_813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_813_, 0, v___x_811_);
lean_ctor_set(v___x_813_, 1, v___x_812_);
v___x_814_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_814_, 0, v___x_813_);
lean_ctor_set(v___x_814_, 1, v___x_805_);
v___x_815_ = ((lean_object*)(l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__19));
v___x_816_ = l_Lean_JsonNumber_fromNat(v_processType_797_);
v___x_817_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_817_, 0, v___x_816_);
v___x_818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_818_, 0, v___x_815_);
lean_ctor_set(v___x_818_, 1, v___x_817_);
v___x_819_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_819_, 0, v___x_818_);
lean_ctor_set(v___x_819_, 1, v___x_805_);
v___x_820_ = ((lean_object*)(l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__24));
v___x_821_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_821_, 0, v_product_798_);
v___x_822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_822_, 0, v___x_820_);
lean_ctor_set(v___x_822_, 1, v___x_821_);
v___x_823_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_823_, 0, v___x_822_);
lean_ctor_set(v___x_823_, 1, v___x_805_);
v___x_824_ = ((lean_object*)(l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__29));
v___x_825_ = l_Lean_JsonNumber_fromNat(v_preprocessedProfileVersion_799_);
v___x_826_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_826_, 0, v___x_825_);
v___x_827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_827_, 0, v___x_824_);
lean_ctor_set(v___x_827_, 1, v___x_826_);
v___x_828_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_828_, 0, v___x_827_);
lean_ctor_set(v___x_828_, 1, v___x_805_);
v___x_829_ = ((lean_object*)(l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__34));
v___x_830_ = l_Lean_Array_toJson___at___00Lean_Firefox_instToJsonProfileMeta_toJson_spec__1(v_markerSchema_800_);
v___x_831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_831_, 0, v___x_829_);
lean_ctor_set(v___x_831_, 1, v___x_830_);
v___x_832_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_832_, 0, v___x_831_);
lean_ctor_set(v___x_832_, 1, v___x_805_);
v___x_833_ = ((lean_object*)(l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__39));
v___x_834_ = l_Lean_Firefox_instToJsonSampleUnits_toJson(v_sampleUnits_801_);
lean_dec_ref(v_sampleUnits_801_);
v___x_835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_835_, 0, v___x_833_);
lean_ctor_set(v___x_835_, 1, v___x_834_);
v___x_836_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_836_, 0, v___x_835_);
lean_ctor_set(v___x_836_, 1, v___x_805_);
v___x_837_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_837_, 0, v___x_836_);
lean_ctor_set(v___x_837_, 1, v___x_805_);
v___x_838_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_838_, 0, v___x_832_);
lean_ctor_set(v___x_838_, 1, v___x_837_);
v___x_839_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_839_, 0, v___x_828_);
lean_ctor_set(v___x_839_, 1, v___x_838_);
v___x_840_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_840_, 0, v___x_823_);
lean_ctor_set(v___x_840_, 1, v___x_839_);
v___x_841_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_841_, 0, v___x_819_);
lean_ctor_set(v___x_841_, 1, v___x_840_);
v___x_842_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_842_, 0, v___x_814_);
lean_ctor_set(v___x_842_, 1, v___x_841_);
v___x_843_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_843_, 0, v___x_810_);
lean_ctor_set(v___x_843_, 1, v___x_842_);
v___x_844_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_844_, 0, v___x_806_);
lean_ctor_set(v___x_844_, 1, v___x_843_);
v___x_845_ = ((lean_object*)(l_Lean_Firefox_instToJsonCategory_toJson___closed__0));
v___x_846_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Firefox_instToJsonCategory_toJson_spec__1(v___x_844_, v___x_845_);
v___x_847_ = l_Lean_Json_mkObj(v___x_846_);
lean_dec(v___x_846_);
return v___x_847_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonStackTable_fromJson_spec__0_spec__0_spec__1(size_t v_sz_850_, size_t v_i_851_, lean_object* v_bs_852_){
_start:
{
uint8_t v___x_853_; 
v___x_853_ = lean_usize_dec_lt(v_i_851_, v_sz_850_);
if (v___x_853_ == 0)
{
lean_object* v___x_854_; 
v___x_854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_854_, 0, v_bs_852_);
return v___x_854_;
}
else
{
lean_object* v_v_855_; lean_object* v___x_856_; 
v_v_855_ = lean_array_uget_borrowed(v_bs_852_, v_i_851_);
lean_inc(v_v_855_);
v___x_856_ = l_Lean_Json_getNat_x3f(v_v_855_);
if (lean_obj_tag(v___x_856_) == 0)
{
lean_object* v_a_857_; lean_object* v___x_859_; uint8_t v_isShared_860_; uint8_t v_isSharedCheck_864_; 
lean_dec_ref(v_bs_852_);
v_a_857_ = lean_ctor_get(v___x_856_, 0);
v_isSharedCheck_864_ = !lean_is_exclusive(v___x_856_);
if (v_isSharedCheck_864_ == 0)
{
v___x_859_ = v___x_856_;
v_isShared_860_ = v_isSharedCheck_864_;
goto v_resetjp_858_;
}
else
{
lean_inc(v_a_857_);
lean_dec(v___x_856_);
v___x_859_ = lean_box(0);
v_isShared_860_ = v_isSharedCheck_864_;
goto v_resetjp_858_;
}
v_resetjp_858_:
{
lean_object* v___x_862_; 
if (v_isShared_860_ == 0)
{
v___x_862_ = v___x_859_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v_a_857_);
v___x_862_ = v_reuseFailAlloc_863_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
return v___x_862_;
}
}
}
else
{
lean_object* v_a_865_; lean_object* v___x_866_; lean_object* v_bs_x27_867_; size_t v___x_868_; size_t v___x_869_; lean_object* v___x_870_; 
v_a_865_ = lean_ctor_get(v___x_856_, 0);
lean_inc(v_a_865_);
lean_dec_ref_known(v___x_856_, 1);
v___x_866_ = lean_unsigned_to_nat(0u);
v_bs_x27_867_ = lean_array_uset(v_bs_852_, v_i_851_, v___x_866_);
v___x_868_ = ((size_t)1ULL);
v___x_869_ = lean_usize_add(v_i_851_, v___x_868_);
v___x_870_ = lean_array_uset(v_bs_x27_867_, v_i_851_, v_a_865_);
v_i_851_ = v___x_869_;
v_bs_852_ = v___x_870_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonStackTable_fromJson_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_872_, lean_object* v_i_873_, lean_object* v_bs_874_){
_start:
{
size_t v_sz_boxed_875_; size_t v_i_boxed_876_; lean_object* v_res_877_; 
v_sz_boxed_875_ = lean_unbox_usize(v_sz_872_);
lean_dec(v_sz_872_);
v_i_boxed_876_ = lean_unbox_usize(v_i_873_);
lean_dec(v_i_873_);
v_res_877_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonStackTable_fromJson_spec__0_spec__0_spec__1(v_sz_boxed_875_, v_i_boxed_876_, v_bs_874_);
return v_res_877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonStackTable_fromJson_spec__0_spec__0(lean_object* v_x_878_){
_start:
{
if (lean_obj_tag(v_x_878_) == 4)
{
lean_object* v_elems_879_; size_t v_sz_880_; size_t v___x_881_; lean_object* v___x_882_; 
v_elems_879_ = lean_ctor_get(v_x_878_, 0);
lean_inc_ref(v_elems_879_);
lean_dec_ref_known(v_x_878_, 1);
v_sz_880_ = lean_array_size(v_elems_879_);
v___x_881_ = ((size_t)0ULL);
v___x_882_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonStackTable_fromJson_spec__0_spec__0_spec__1(v_sz_880_, v___x_881_, v_elems_879_);
return v___x_882_;
}
else
{
lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; 
v___x_883_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__2_spec__2___closed__0));
v___x_884_ = lean_unsigned_to_nat(80u);
v___x_885_ = l_Lean_Json_pretty(v_x_878_, v___x_884_);
v___x_886_ = lean_string_append(v___x_883_, v___x_885_);
lean_dec_ref(v___x_885_);
v___x_887_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__2_spec__2___closed__1));
v___x_888_ = lean_string_append(v___x_886_, v___x_887_);
v___x_889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_889_, 0, v___x_888_);
return v___x_889_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonStackTable_fromJson_spec__0(lean_object* v_j_890_, lean_object* v_k_891_){
_start:
{
lean_object* v___x_892_; lean_object* v___x_893_; 
v___x_892_ = l_Lean_Json_getObjValD(v_j_890_, v_k_891_);
v___x_893_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonStackTable_fromJson_spec__0_spec__0(v___x_892_);
return v___x_893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonStackTable_fromJson_spec__0___boxed(lean_object* v_j_894_, lean_object* v_k_895_){
_start:
{
lean_object* v_res_896_; 
v_res_896_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonStackTable_fromJson_spec__0(v_j_894_, v_k_895_);
lean_dec_ref(v_k_895_);
return v_res_896_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonStackTable_fromJson_spec__1_spec__2_spec__4(lean_object* v_x_899_){
_start:
{
if (lean_obj_tag(v_x_899_) == 0)
{
lean_object* v___x_900_; 
v___x_900_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonStackTable_fromJson_spec__1_spec__2_spec__4___closed__0));
return v___x_900_;
}
else
{
lean_object* v___x_901_; 
v___x_901_ = l_Lean_Json_getNat_x3f(v_x_899_);
if (lean_obj_tag(v___x_901_) == 0)
{
lean_object* v_a_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_909_; 
v_a_902_ = lean_ctor_get(v___x_901_, 0);
v_isSharedCheck_909_ = !lean_is_exclusive(v___x_901_);
if (v_isSharedCheck_909_ == 0)
{
v___x_904_ = v___x_901_;
v_isShared_905_ = v_isSharedCheck_909_;
goto v_resetjp_903_;
}
else
{
lean_inc(v_a_902_);
lean_dec(v___x_901_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_909_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
lean_object* v___x_907_; 
if (v_isShared_905_ == 0)
{
v___x_907_ = v___x_904_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v_a_902_);
v___x_907_ = v_reuseFailAlloc_908_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
return v___x_907_;
}
}
}
else
{
lean_object* v_a_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_918_; 
v_a_910_ = lean_ctor_get(v___x_901_, 0);
v_isSharedCheck_918_ = !lean_is_exclusive(v___x_901_);
if (v_isSharedCheck_918_ == 0)
{
v___x_912_ = v___x_901_;
v_isShared_913_ = v_isSharedCheck_918_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_a_910_);
lean_dec(v___x_901_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_918_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
lean_object* v___x_914_; lean_object* v___x_916_; 
v___x_914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_914_, 0, v_a_910_);
if (v_isShared_913_ == 0)
{
lean_ctor_set(v___x_912_, 0, v___x_914_);
v___x_916_ = v___x_912_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v___x_914_);
v___x_916_ = v_reuseFailAlloc_917_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
return v___x_916_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonStackTable_fromJson_spec__1_spec__2_spec__5(size_t v_sz_919_, size_t v_i_920_, lean_object* v_bs_921_){
_start:
{
uint8_t v___x_922_; 
v___x_922_ = lean_usize_dec_lt(v_i_920_, v_sz_919_);
if (v___x_922_ == 0)
{
lean_object* v___x_923_; 
v___x_923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_923_, 0, v_bs_921_);
return v___x_923_;
}
else
{
lean_object* v_v_924_; lean_object* v___x_925_; 
v_v_924_ = lean_array_uget_borrowed(v_bs_921_, v_i_920_);
lean_inc(v_v_924_);
v___x_925_ = l_Lean_Option_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonStackTable_fromJson_spec__1_spec__2_spec__4(v_v_924_);
if (lean_obj_tag(v___x_925_) == 0)
{
lean_object* v_a_926_; lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_933_; 
lean_dec_ref(v_bs_921_);
v_a_926_ = lean_ctor_get(v___x_925_, 0);
v_isSharedCheck_933_ = !lean_is_exclusive(v___x_925_);
if (v_isSharedCheck_933_ == 0)
{
v___x_928_ = v___x_925_;
v_isShared_929_ = v_isSharedCheck_933_;
goto v_resetjp_927_;
}
else
{
lean_inc(v_a_926_);
lean_dec(v___x_925_);
v___x_928_ = lean_box(0);
v_isShared_929_ = v_isSharedCheck_933_;
goto v_resetjp_927_;
}
v_resetjp_927_:
{
lean_object* v___x_931_; 
if (v_isShared_929_ == 0)
{
v___x_931_ = v___x_928_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v_a_926_);
v___x_931_ = v_reuseFailAlloc_932_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
return v___x_931_;
}
}
}
else
{
lean_object* v_a_934_; lean_object* v___x_935_; lean_object* v_bs_x27_936_; size_t v___x_937_; size_t v___x_938_; lean_object* v___x_939_; 
v_a_934_ = lean_ctor_get(v___x_925_, 0);
lean_inc(v_a_934_);
lean_dec_ref_known(v___x_925_, 1);
v___x_935_ = lean_unsigned_to_nat(0u);
v_bs_x27_936_ = lean_array_uset(v_bs_921_, v_i_920_, v___x_935_);
v___x_937_ = ((size_t)1ULL);
v___x_938_ = lean_usize_add(v_i_920_, v___x_937_);
v___x_939_ = lean_array_uset(v_bs_x27_936_, v_i_920_, v_a_934_);
v_i_920_ = v___x_938_;
v_bs_921_ = v___x_939_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonStackTable_fromJson_spec__1_spec__2_spec__5___boxed(lean_object* v_sz_941_, lean_object* v_i_942_, lean_object* v_bs_943_){
_start:
{
size_t v_sz_boxed_944_; size_t v_i_boxed_945_; lean_object* v_res_946_; 
v_sz_boxed_944_ = lean_unbox_usize(v_sz_941_);
lean_dec(v_sz_941_);
v_i_boxed_945_ = lean_unbox_usize(v_i_942_);
lean_dec(v_i_942_);
v_res_946_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonStackTable_fromJson_spec__1_spec__2_spec__5(v_sz_boxed_944_, v_i_boxed_945_, v_bs_943_);
return v_res_946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonStackTable_fromJson_spec__1_spec__2(lean_object* v_x_947_){
_start:
{
if (lean_obj_tag(v_x_947_) == 4)
{
lean_object* v_elems_948_; size_t v_sz_949_; size_t v___x_950_; lean_object* v___x_951_; 
v_elems_948_ = lean_ctor_get(v_x_947_, 0);
lean_inc_ref(v_elems_948_);
lean_dec_ref_known(v_x_947_, 1);
v_sz_949_ = lean_array_size(v_elems_948_);
v___x_950_ = ((size_t)0ULL);
v___x_951_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonStackTable_fromJson_spec__1_spec__2_spec__5(v_sz_949_, v___x_950_, v_elems_948_);
return v___x_951_;
}
else
{
lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; 
v___x_952_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__2_spec__2___closed__0));
v___x_953_ = lean_unsigned_to_nat(80u);
v___x_954_ = l_Lean_Json_pretty(v_x_947_, v___x_953_);
v___x_955_ = lean_string_append(v___x_952_, v___x_954_);
lean_dec_ref(v___x_954_);
v___x_956_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__2_spec__2___closed__1));
v___x_957_ = lean_string_append(v___x_955_, v___x_956_);
v___x_958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_958_, 0, v___x_957_);
return v___x_958_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonStackTable_fromJson_spec__1(lean_object* v_j_959_, lean_object* v_k_960_){
_start:
{
lean_object* v___x_961_; lean_object* v___x_962_; 
v___x_961_ = l_Lean_Json_getObjValD(v_j_959_, v_k_960_);
v___x_962_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonStackTable_fromJson_spec__1_spec__2(v___x_961_);
return v___x_962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonStackTable_fromJson_spec__1___boxed(lean_object* v_j_963_, lean_object* v_k_964_){
_start:
{
lean_object* v_res_965_; 
v_res_965_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonStackTable_fromJson_spec__1(v_j_963_, v_k_964_);
lean_dec_ref(v_k_964_);
return v_res_965_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__3(void){
_start:
{
uint8_t v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; 
v___x_972_ = 1;
v___x_973_ = ((lean_object*)(l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__2));
v___x_974_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_973_, v___x_972_);
return v___x_974_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__4(void){
_start:
{
lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; 
v___x_975_ = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__6));
v___x_976_ = lean_obj_once(&l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__3, &l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__3_once, _init_l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__3);
v___x_977_ = lean_string_append(v___x_976_, v___x_975_);
return v___x_977_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__6(void){
_start:
{
uint8_t v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; 
v___x_980_ = 1;
v___x_981_ = ((lean_object*)(l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__5));
v___x_982_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_981_, v___x_980_);
return v___x_982_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__7(void){
_start:
{
lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; 
v___x_983_ = lean_obj_once(&l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__6, &l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__6_once, _init_l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__6);
v___x_984_ = lean_obj_once(&l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__4, &l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__4_once, _init_l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__4);
v___x_985_ = lean_string_append(v___x_984_, v___x_983_);
return v___x_985_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__8(void){
_start:
{
lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; 
v___x_986_ = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
v___x_987_ = lean_obj_once(&l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__7, &l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__7_once, _init_l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__7);
v___x_988_ = lean_string_append(v___x_987_, v___x_986_);
return v___x_988_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__11(void){
_start:
{
uint8_t v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; 
v___x_992_ = 1;
v___x_993_ = ((lean_object*)(l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__10));
v___x_994_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_993_, v___x_992_);
return v___x_994_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__12(void){
_start:
{
lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; 
v___x_995_ = lean_obj_once(&l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__11, &l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__11_once, _init_l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__11);
v___x_996_ = lean_obj_once(&l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__4, &l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__4_once, _init_l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__4);
v___x_997_ = lean_string_append(v___x_996_, v___x_995_);
return v___x_997_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__13(void){
_start:
{
lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; 
v___x_998_ = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
v___x_999_ = lean_obj_once(&l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__12, &l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__12_once, _init_l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__12);
v___x_1000_ = lean_string_append(v___x_999_, v___x_998_);
return v___x_1000_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__16(void){
_start:
{
uint8_t v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; 
v___x_1004_ = 1;
v___x_1005_ = ((lean_object*)(l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__15));
v___x_1006_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1005_, v___x_1004_);
return v___x_1006_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__17(void){
_start:
{
lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; 
v___x_1007_ = lean_obj_once(&l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__16, &l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__16_once, _init_l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__16);
v___x_1008_ = lean_obj_once(&l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__4, &l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__4_once, _init_l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__4);
v___x_1009_ = lean_string_append(v___x_1008_, v___x_1007_);
return v___x_1009_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__18(void){
_start:
{
lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; 
v___x_1010_ = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
v___x_1011_ = lean_obj_once(&l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__17, &l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__17_once, _init_l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__17);
v___x_1012_ = lean_string_append(v___x_1011_, v___x_1010_);
return v___x_1012_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__21(void){
_start:
{
uint8_t v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; 
v___x_1016_ = 1;
v___x_1017_ = ((lean_object*)(l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__20));
v___x_1018_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1017_, v___x_1016_);
return v___x_1018_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__22(void){
_start:
{
lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; 
v___x_1019_ = lean_obj_once(&l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__21, &l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__21_once, _init_l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__21);
v___x_1020_ = lean_obj_once(&l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__4, &l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__4_once, _init_l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__4);
v___x_1021_ = lean_string_append(v___x_1020_, v___x_1019_);
return v___x_1021_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__23(void){
_start:
{
lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; 
v___x_1022_ = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
v___x_1023_ = lean_obj_once(&l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__22, &l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__22_once, _init_l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__22);
v___x_1024_ = lean_string_append(v___x_1023_, v___x_1022_);
return v___x_1024_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__26(void){
_start:
{
uint8_t v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; 
v___x_1028_ = 1;
v___x_1029_ = ((lean_object*)(l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__25));
v___x_1030_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1029_, v___x_1028_);
return v___x_1030_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__27(void){
_start:
{
lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; 
v___x_1031_ = lean_obj_once(&l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__26, &l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__26_once, _init_l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__26);
v___x_1032_ = lean_obj_once(&l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__4, &l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__4_once, _init_l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__4);
v___x_1033_ = lean_string_append(v___x_1032_, v___x_1031_);
return v___x_1033_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__28(void){
_start:
{
lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; 
v___x_1034_ = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
v___x_1035_ = lean_obj_once(&l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__27, &l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__27_once, _init_l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__27);
v___x_1036_ = lean_string_append(v___x_1035_, v___x_1034_);
return v___x_1036_;
}
}
LEAN_EXPORT lean_object* l_Lean_Firefox_instFromJsonStackTable_fromJson(lean_object* v_json_1037_){
_start:
{
lean_object* v___x_1038_; lean_object* v___x_1039_; 
v___x_1038_ = ((lean_object*)(l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__0));
lean_inc(v_json_1037_);
v___x_1039_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonStackTable_fromJson_spec__0(v_json_1037_, v___x_1038_);
if (lean_obj_tag(v___x_1039_) == 0)
{
lean_object* v_a_1040_; lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1049_; 
lean_dec(v_json_1037_);
v_a_1040_ = lean_ctor_get(v___x_1039_, 0);
v_isSharedCheck_1049_ = !lean_is_exclusive(v___x_1039_);
if (v_isSharedCheck_1049_ == 0)
{
v___x_1042_ = v___x_1039_;
v_isShared_1043_ = v_isSharedCheck_1049_;
goto v_resetjp_1041_;
}
else
{
lean_inc(v_a_1040_);
lean_dec(v___x_1039_);
v___x_1042_ = lean_box(0);
v_isShared_1043_ = v_isSharedCheck_1049_;
goto v_resetjp_1041_;
}
v_resetjp_1041_:
{
lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1047_; 
v___x_1044_ = lean_obj_once(&l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__8, &l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__8_once, _init_l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__8);
v___x_1045_ = lean_string_append(v___x_1044_, v_a_1040_);
lean_dec(v_a_1040_);
if (v_isShared_1043_ == 0)
{
lean_ctor_set(v___x_1042_, 0, v___x_1045_);
v___x_1047_ = v___x_1042_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v___x_1045_);
v___x_1047_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
return v___x_1047_;
}
}
}
else
{
lean_object* v_a_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; 
v_a_1050_ = lean_ctor_get(v___x_1039_, 0);
lean_inc(v_a_1050_);
lean_dec_ref_known(v___x_1039_, 1);
v___x_1051_ = ((lean_object*)(l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__9));
lean_inc(v_json_1037_);
v___x_1052_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonStackTable_fromJson_spec__0(v_json_1037_, v___x_1051_);
if (lean_obj_tag(v___x_1052_) == 0)
{
lean_object* v_a_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1062_; 
lean_dec(v_a_1050_);
lean_dec(v_json_1037_);
v_a_1053_ = lean_ctor_get(v___x_1052_, 0);
v_isSharedCheck_1062_ = !lean_is_exclusive(v___x_1052_);
if (v_isSharedCheck_1062_ == 0)
{
v___x_1055_ = v___x_1052_;
v_isShared_1056_ = v_isSharedCheck_1062_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_a_1053_);
lean_dec(v___x_1052_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1062_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1060_; 
v___x_1057_ = lean_obj_once(&l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__13, &l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__13_once, _init_l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__13);
v___x_1058_ = lean_string_append(v___x_1057_, v_a_1053_);
lean_dec(v_a_1053_);
if (v_isShared_1056_ == 0)
{
lean_ctor_set(v___x_1055_, 0, v___x_1058_);
v___x_1060_ = v___x_1055_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v___x_1058_);
v___x_1060_ = v_reuseFailAlloc_1061_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
return v___x_1060_;
}
}
}
else
{
lean_object* v_a_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; 
v_a_1063_ = lean_ctor_get(v___x_1052_, 0);
lean_inc(v_a_1063_);
lean_dec_ref_known(v___x_1052_, 1);
v___x_1064_ = ((lean_object*)(l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__14));
lean_inc(v_json_1037_);
v___x_1065_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonStackTable_fromJson_spec__0(v_json_1037_, v___x_1064_);
if (lean_obj_tag(v___x_1065_) == 0)
{
lean_object* v_a_1066_; lean_object* v___x_1068_; uint8_t v_isShared_1069_; uint8_t v_isSharedCheck_1075_; 
lean_dec(v_a_1063_);
lean_dec(v_a_1050_);
lean_dec(v_json_1037_);
v_a_1066_ = lean_ctor_get(v___x_1065_, 0);
v_isSharedCheck_1075_ = !lean_is_exclusive(v___x_1065_);
if (v_isSharedCheck_1075_ == 0)
{
v___x_1068_ = v___x_1065_;
v_isShared_1069_ = v_isSharedCheck_1075_;
goto v_resetjp_1067_;
}
else
{
lean_inc(v_a_1066_);
lean_dec(v___x_1065_);
v___x_1068_ = lean_box(0);
v_isShared_1069_ = v_isSharedCheck_1075_;
goto v_resetjp_1067_;
}
v_resetjp_1067_:
{
lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1073_; 
v___x_1070_ = lean_obj_once(&l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__18, &l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__18_once, _init_l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__18);
v___x_1071_ = lean_string_append(v___x_1070_, v_a_1066_);
lean_dec(v_a_1066_);
if (v_isShared_1069_ == 0)
{
lean_ctor_set(v___x_1068_, 0, v___x_1071_);
v___x_1073_ = v___x_1068_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v___x_1071_);
v___x_1073_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
return v___x_1073_;
}
}
}
else
{
lean_object* v_a_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; 
v_a_1076_ = lean_ctor_get(v___x_1065_, 0);
lean_inc(v_a_1076_);
lean_dec_ref_known(v___x_1065_, 1);
v___x_1077_ = ((lean_object*)(l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__19));
lean_inc(v_json_1037_);
v___x_1078_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonStackTable_fromJson_spec__1(v_json_1037_, v___x_1077_);
if (lean_obj_tag(v___x_1078_) == 0)
{
lean_object* v_a_1079_; lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1088_; 
lean_dec(v_a_1076_);
lean_dec(v_a_1063_);
lean_dec(v_a_1050_);
lean_dec(v_json_1037_);
v_a_1079_ = lean_ctor_get(v___x_1078_, 0);
v_isSharedCheck_1088_ = !lean_is_exclusive(v___x_1078_);
if (v_isSharedCheck_1088_ == 0)
{
v___x_1081_ = v___x_1078_;
v_isShared_1082_ = v_isSharedCheck_1088_;
goto v_resetjp_1080_;
}
else
{
lean_inc(v_a_1079_);
lean_dec(v___x_1078_);
v___x_1081_ = lean_box(0);
v_isShared_1082_ = v_isSharedCheck_1088_;
goto v_resetjp_1080_;
}
v_resetjp_1080_:
{
lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1086_; 
v___x_1083_ = lean_obj_once(&l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__23, &l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__23_once, _init_l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__23);
v___x_1084_ = lean_string_append(v___x_1083_, v_a_1079_);
lean_dec(v_a_1079_);
if (v_isShared_1082_ == 0)
{
lean_ctor_set(v___x_1081_, 0, v___x_1084_);
v___x_1086_ = v___x_1081_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v___x_1084_);
v___x_1086_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
return v___x_1086_;
}
}
}
else
{
lean_object* v_a_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; 
v_a_1089_ = lean_ctor_get(v___x_1078_, 0);
lean_inc(v_a_1089_);
lean_dec_ref_known(v___x_1078_, 1);
v___x_1090_ = ((lean_object*)(l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__24));
v___x_1091_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__2(v_json_1037_, v___x_1090_);
if (lean_obj_tag(v___x_1091_) == 0)
{
lean_object* v_a_1092_; lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1101_; 
lean_dec(v_a_1089_);
lean_dec(v_a_1076_);
lean_dec(v_a_1063_);
lean_dec(v_a_1050_);
v_a_1092_ = lean_ctor_get(v___x_1091_, 0);
v_isSharedCheck_1101_ = !lean_is_exclusive(v___x_1091_);
if (v_isSharedCheck_1101_ == 0)
{
v___x_1094_ = v___x_1091_;
v_isShared_1095_ = v_isSharedCheck_1101_;
goto v_resetjp_1093_;
}
else
{
lean_inc(v_a_1092_);
lean_dec(v___x_1091_);
v___x_1094_ = lean_box(0);
v_isShared_1095_ = v_isSharedCheck_1101_;
goto v_resetjp_1093_;
}
v_resetjp_1093_:
{
lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1099_; 
v___x_1096_ = lean_obj_once(&l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__28, &l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__28_once, _init_l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__28);
v___x_1097_ = lean_string_append(v___x_1096_, v_a_1092_);
lean_dec(v_a_1092_);
if (v_isShared_1095_ == 0)
{
lean_ctor_set(v___x_1094_, 0, v___x_1097_);
v___x_1099_ = v___x_1094_;
goto v_reusejp_1098_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v___x_1097_);
v___x_1099_ = v_reuseFailAlloc_1100_;
goto v_reusejp_1098_;
}
v_reusejp_1098_:
{
return v___x_1099_;
}
}
}
else
{
lean_object* v_a_1102_; lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1110_; 
v_a_1102_ = lean_ctor_get(v___x_1091_, 0);
v_isSharedCheck_1110_ = !lean_is_exclusive(v___x_1091_);
if (v_isSharedCheck_1110_ == 0)
{
v___x_1104_ = v___x_1091_;
v_isShared_1105_ = v_isSharedCheck_1110_;
goto v_resetjp_1103_;
}
else
{
lean_inc(v_a_1102_);
lean_dec(v___x_1091_);
v___x_1104_ = lean_box(0);
v_isShared_1105_ = v_isSharedCheck_1110_;
goto v_resetjp_1103_;
}
v_resetjp_1103_:
{
lean_object* v___x_1106_; lean_object* v___x_1108_; 
v___x_1106_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1106_, 0, v_a_1050_);
lean_ctor_set(v___x_1106_, 1, v_a_1063_);
lean_ctor_set(v___x_1106_, 2, v_a_1076_);
lean_ctor_set(v___x_1106_, 3, v_a_1089_);
lean_ctor_set(v___x_1106_, 4, v_a_1102_);
if (v_isShared_1105_ == 0)
{
lean_ctor_set(v___x_1104_, 0, v___x_1106_);
v___x_1108_ = v___x_1104_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v___x_1106_);
v___x_1108_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
return v___x_1108_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_toJson___at___00Lean_Array_toJson___at___00Lean_Firefox_instToJsonStackTable_toJson_spec__1_spec__2(lean_object* v_x_1113_){
_start:
{
if (lean_obj_tag(v_x_1113_) == 0)
{
lean_object* v___x_1114_; 
v___x_1114_ = lean_box(0);
return v___x_1114_;
}
else
{
lean_object* v_val_1115_; lean_object* v___x_1117_; uint8_t v_isShared_1118_; uint8_t v_isSharedCheck_1123_; 
v_val_1115_ = lean_ctor_get(v_x_1113_, 0);
v_isSharedCheck_1123_ = !lean_is_exclusive(v_x_1113_);
if (v_isSharedCheck_1123_ == 0)
{
v___x_1117_ = v_x_1113_;
v_isShared_1118_ = v_isSharedCheck_1123_;
goto v_resetjp_1116_;
}
else
{
lean_inc(v_val_1115_);
lean_dec(v_x_1113_);
v___x_1117_ = lean_box(0);
v_isShared_1118_ = v_isSharedCheck_1123_;
goto v_resetjp_1116_;
}
v_resetjp_1116_:
{
lean_object* v___x_1119_; lean_object* v___x_1121_; 
v___x_1119_ = l_Lean_JsonNumber_fromNat(v_val_1115_);
if (v_isShared_1118_ == 0)
{
lean_ctor_set_tag(v___x_1117_, 2);
lean_ctor_set(v___x_1117_, 0, v___x_1119_);
v___x_1121_ = v___x_1117_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v___x_1119_);
v___x_1121_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
return v___x_1121_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Firefox_instToJsonStackTable_toJson_spec__1_spec__3(size_t v_sz_1124_, size_t v_i_1125_, lean_object* v_bs_1126_){
_start:
{
uint8_t v___x_1127_; 
v___x_1127_ = lean_usize_dec_lt(v_i_1125_, v_sz_1124_);
if (v___x_1127_ == 0)
{
return v_bs_1126_;
}
else
{
lean_object* v_v_1128_; lean_object* v___x_1129_; lean_object* v_bs_x27_1130_; lean_object* v___x_1131_; size_t v___x_1132_; size_t v___x_1133_; lean_object* v___x_1134_; 
v_v_1128_ = lean_array_uget(v_bs_1126_, v_i_1125_);
v___x_1129_ = lean_unsigned_to_nat(0u);
v_bs_x27_1130_ = lean_array_uset(v_bs_1126_, v_i_1125_, v___x_1129_);
v___x_1131_ = l_Lean_Option_toJson___at___00Lean_Array_toJson___at___00Lean_Firefox_instToJsonStackTable_toJson_spec__1_spec__2(v_v_1128_);
v___x_1132_ = ((size_t)1ULL);
v___x_1133_ = lean_usize_add(v_i_1125_, v___x_1132_);
v___x_1134_ = lean_array_uset(v_bs_x27_1130_, v_i_1125_, v___x_1131_);
v_i_1125_ = v___x_1133_;
v_bs_1126_ = v___x_1134_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Firefox_instToJsonStackTable_toJson_spec__1_spec__3___boxed(lean_object* v_sz_1136_, lean_object* v_i_1137_, lean_object* v_bs_1138_){
_start:
{
size_t v_sz_boxed_1139_; size_t v_i_boxed_1140_; lean_object* v_res_1141_; 
v_sz_boxed_1139_ = lean_unbox_usize(v_sz_1136_);
lean_dec(v_sz_1136_);
v_i_boxed_1140_ = lean_unbox_usize(v_i_1137_);
lean_dec(v_i_1137_);
v_res_1141_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Firefox_instToJsonStackTable_toJson_spec__1_spec__3(v_sz_boxed_1139_, v_i_boxed_1140_, v_bs_1138_);
return v_res_1141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Firefox_instToJsonStackTable_toJson_spec__1(lean_object* v_a_1142_){
_start:
{
size_t v_sz_1143_; size_t v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; 
v_sz_1143_ = lean_array_size(v_a_1142_);
v___x_1144_ = ((size_t)0ULL);
v___x_1145_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Firefox_instToJsonStackTable_toJson_spec__1_spec__3(v_sz_1143_, v___x_1144_, v_a_1142_);
v___x_1146_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1146_, 0, v___x_1145_);
return v___x_1146_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Firefox_instToJsonStackTable_toJson_spec__0_spec__0(size_t v_sz_1147_, size_t v_i_1148_, lean_object* v_bs_1149_){
_start:
{
uint8_t v___x_1150_; 
v___x_1150_ = lean_usize_dec_lt(v_i_1148_, v_sz_1147_);
if (v___x_1150_ == 0)
{
return v_bs_1149_;
}
else
{
lean_object* v_v_1151_; lean_object* v___x_1152_; lean_object* v_bs_x27_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; size_t v___x_1156_; size_t v___x_1157_; lean_object* v___x_1158_; 
v_v_1151_ = lean_array_uget(v_bs_1149_, v_i_1148_);
v___x_1152_ = lean_unsigned_to_nat(0u);
v_bs_x27_1153_ = lean_array_uset(v_bs_1149_, v_i_1148_, v___x_1152_);
v___x_1154_ = l_Lean_JsonNumber_fromNat(v_v_1151_);
v___x_1155_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1155_, 0, v___x_1154_);
v___x_1156_ = ((size_t)1ULL);
v___x_1157_ = lean_usize_add(v_i_1148_, v___x_1156_);
v___x_1158_ = lean_array_uset(v_bs_x27_1153_, v_i_1148_, v___x_1155_);
v_i_1148_ = v___x_1157_;
v_bs_1149_ = v___x_1158_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Firefox_instToJsonStackTable_toJson_spec__0_spec__0___boxed(lean_object* v_sz_1160_, lean_object* v_i_1161_, lean_object* v_bs_1162_){
_start:
{
size_t v_sz_boxed_1163_; size_t v_i_boxed_1164_; lean_object* v_res_1165_; 
v_sz_boxed_1163_ = lean_unbox_usize(v_sz_1160_);
lean_dec(v_sz_1160_);
v_i_boxed_1164_ = lean_unbox_usize(v_i_1161_);
lean_dec(v_i_1161_);
v_res_1165_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Firefox_instToJsonStackTable_toJson_spec__0_spec__0(v_sz_boxed_1163_, v_i_boxed_1164_, v_bs_1162_);
return v_res_1165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Firefox_instToJsonStackTable_toJson_spec__0(lean_object* v_a_1166_){
_start:
{
size_t v_sz_1167_; size_t v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; 
v_sz_1167_ = lean_array_size(v_a_1166_);
v___x_1168_ = ((size_t)0ULL);
v___x_1169_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Firefox_instToJsonStackTable_toJson_spec__0_spec__0(v_sz_1167_, v___x_1168_, v_a_1166_);
v___x_1170_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1170_, 0, v___x_1169_);
return v___x_1170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Firefox_instToJsonStackTable_toJson(lean_object* v_x_1171_){
_start:
{
lean_object* v_frame_1172_; lean_object* v_category_1173_; lean_object* v_subcategory_1174_; lean_object* v_prefix_1175_; lean_object* v_length_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; 
v_frame_1172_ = lean_ctor_get(v_x_1171_, 0);
lean_inc_ref(v_frame_1172_);
v_category_1173_ = lean_ctor_get(v_x_1171_, 1);
lean_inc_ref(v_category_1173_);
v_subcategory_1174_ = lean_ctor_get(v_x_1171_, 2);
lean_inc_ref(v_subcategory_1174_);
v_prefix_1175_ = lean_ctor_get(v_x_1171_, 3);
lean_inc_ref(v_prefix_1175_);
v_length_1176_ = lean_ctor_get(v_x_1171_, 4);
lean_inc(v_length_1176_);
lean_dec_ref(v_x_1171_);
v___x_1177_ = ((lean_object*)(l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__0));
v___x_1178_ = l_Lean_Array_toJson___at___00Lean_Firefox_instToJsonStackTable_toJson_spec__0(v_frame_1172_);
v___x_1179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1179_, 0, v___x_1177_);
lean_ctor_set(v___x_1179_, 1, v___x_1178_);
v___x_1180_ = lean_box(0);
v___x_1181_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1181_, 0, v___x_1179_);
lean_ctor_set(v___x_1181_, 1, v___x_1180_);
v___x_1182_ = ((lean_object*)(l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__9));
v___x_1183_ = l_Lean_Array_toJson___at___00Lean_Firefox_instToJsonStackTable_toJson_spec__0(v_category_1173_);
v___x_1184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1184_, 0, v___x_1182_);
lean_ctor_set(v___x_1184_, 1, v___x_1183_);
v___x_1185_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1185_, 0, v___x_1184_);
lean_ctor_set(v___x_1185_, 1, v___x_1180_);
v___x_1186_ = ((lean_object*)(l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__14));
v___x_1187_ = l_Lean_Array_toJson___at___00Lean_Firefox_instToJsonStackTable_toJson_spec__0(v_subcategory_1174_);
v___x_1188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1188_, 0, v___x_1186_);
lean_ctor_set(v___x_1188_, 1, v___x_1187_);
v___x_1189_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1189_, 0, v___x_1188_);
lean_ctor_set(v___x_1189_, 1, v___x_1180_);
v___x_1190_ = ((lean_object*)(l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__19));
v___x_1191_ = l_Lean_Array_toJson___at___00Lean_Firefox_instToJsonStackTable_toJson_spec__1(v_prefix_1175_);
v___x_1192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1192_, 0, v___x_1190_);
lean_ctor_set(v___x_1192_, 1, v___x_1191_);
v___x_1193_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1193_, 0, v___x_1192_);
lean_ctor_set(v___x_1193_, 1, v___x_1180_);
v___x_1194_ = ((lean_object*)(l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__24));
v___x_1195_ = l_Lean_JsonNumber_fromNat(v_length_1176_);
v___x_1196_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1196_, 0, v___x_1195_);
v___x_1197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1197_, 0, v___x_1194_);
lean_ctor_set(v___x_1197_, 1, v___x_1196_);
v___x_1198_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1198_, 0, v___x_1197_);
lean_ctor_set(v___x_1198_, 1, v___x_1180_);
v___x_1199_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1199_, 0, v___x_1198_);
lean_ctor_set(v___x_1199_, 1, v___x_1180_);
v___x_1200_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1200_, 0, v___x_1193_);
lean_ctor_set(v___x_1200_, 1, v___x_1199_);
v___x_1201_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1201_, 0, v___x_1189_);
lean_ctor_set(v___x_1201_, 1, v___x_1200_);
v___x_1202_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1202_, 0, v___x_1185_);
lean_ctor_set(v___x_1202_, 1, v___x_1201_);
v___x_1203_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1203_, 0, v___x_1181_);
lean_ctor_set(v___x_1203_, 1, v___x_1202_);
v___x_1204_ = ((lean_object*)(l_Lean_Firefox_instToJsonCategory_toJson___closed__0));
v___x_1205_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Firefox_instToJsonCategory_toJson_spec__1(v___x_1203_, v___x_1204_);
v___x_1206_ = l_Lean_Json_mkObj(v___x_1205_);
lean_dec(v___x_1205_);
return v___x_1206_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonSamplesTable_fromJson_spec__0_spec__0_spec__1(size_t v_sz_1209_, size_t v_i_1210_, lean_object* v_bs_1211_){
_start:
{
uint8_t v___x_1212_; 
v___x_1212_ = lean_usize_dec_lt(v_i_1210_, v_sz_1209_);
if (v___x_1212_ == 0)
{
lean_object* v___x_1213_; 
v___x_1213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1213_, 0, v_bs_1211_);
return v___x_1213_;
}
else
{
lean_object* v_v_1214_; lean_object* v___x_1215_; 
v_v_1214_ = lean_array_uget_borrowed(v_bs_1211_, v_i_1210_);
lean_inc(v_v_1214_);
v___x_1215_ = l_Lean_Float_fromJson_x3f(v_v_1214_);
if (lean_obj_tag(v___x_1215_) == 0)
{
lean_object* v_a_1216_; lean_object* v___x_1218_; uint8_t v_isShared_1219_; uint8_t v_isSharedCheck_1223_; 
lean_dec_ref(v_bs_1211_);
v_a_1216_ = lean_ctor_get(v___x_1215_, 0);
v_isSharedCheck_1223_ = !lean_is_exclusive(v___x_1215_);
if (v_isSharedCheck_1223_ == 0)
{
v___x_1218_ = v___x_1215_;
v_isShared_1219_ = v_isSharedCheck_1223_;
goto v_resetjp_1217_;
}
else
{
lean_inc(v_a_1216_);
lean_dec(v___x_1215_);
v___x_1218_ = lean_box(0);
v_isShared_1219_ = v_isSharedCheck_1223_;
goto v_resetjp_1217_;
}
v_resetjp_1217_:
{
lean_object* v___x_1221_; 
if (v_isShared_1219_ == 0)
{
v___x_1221_ = v___x_1218_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v_a_1216_);
v___x_1221_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
return v___x_1221_;
}
}
}
else
{
lean_object* v_a_1224_; lean_object* v___x_1225_; lean_object* v_bs_x27_1226_; size_t v___x_1227_; size_t v___x_1228_; lean_object* v___x_1229_; 
v_a_1224_ = lean_ctor_get(v___x_1215_, 0);
lean_inc(v_a_1224_);
lean_dec_ref_known(v___x_1215_, 1);
v___x_1225_ = lean_unsigned_to_nat(0u);
v_bs_x27_1226_ = lean_array_uset(v_bs_1211_, v_i_1210_, v___x_1225_);
v___x_1227_ = ((size_t)1ULL);
v___x_1228_ = lean_usize_add(v_i_1210_, v___x_1227_);
v___x_1229_ = lean_array_uset(v_bs_x27_1226_, v_i_1210_, v_a_1224_);
v_i_1210_ = v___x_1228_;
v_bs_1211_ = v___x_1229_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonSamplesTable_fromJson_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_1231_, lean_object* v_i_1232_, lean_object* v_bs_1233_){
_start:
{
size_t v_sz_boxed_1234_; size_t v_i_boxed_1235_; lean_object* v_res_1236_; 
v_sz_boxed_1234_ = lean_unbox_usize(v_sz_1231_);
lean_dec(v_sz_1231_);
v_i_boxed_1235_ = lean_unbox_usize(v_i_1232_);
lean_dec(v_i_1232_);
v_res_1236_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonSamplesTable_fromJson_spec__0_spec__0_spec__1(v_sz_boxed_1234_, v_i_boxed_1235_, v_bs_1233_);
return v_res_1236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonSamplesTable_fromJson_spec__0_spec__0(lean_object* v_x_1237_){
_start:
{
if (lean_obj_tag(v_x_1237_) == 4)
{
lean_object* v_elems_1238_; size_t v_sz_1239_; size_t v___x_1240_; lean_object* v___x_1241_; 
v_elems_1238_ = lean_ctor_get(v_x_1237_, 0);
lean_inc_ref(v_elems_1238_);
lean_dec_ref_known(v_x_1237_, 1);
v_sz_1239_ = lean_array_size(v_elems_1238_);
v___x_1240_ = ((size_t)0ULL);
v___x_1241_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonSamplesTable_fromJson_spec__0_spec__0_spec__1(v_sz_1239_, v___x_1240_, v_elems_1238_);
return v___x_1241_;
}
else
{
lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; 
v___x_1242_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__2_spec__2___closed__0));
v___x_1243_ = lean_unsigned_to_nat(80u);
v___x_1244_ = l_Lean_Json_pretty(v_x_1237_, v___x_1243_);
v___x_1245_ = lean_string_append(v___x_1242_, v___x_1244_);
lean_dec_ref(v___x_1244_);
v___x_1246_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__2_spec__2___closed__1));
v___x_1247_ = lean_string_append(v___x_1245_, v___x_1246_);
v___x_1248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1248_, 0, v___x_1247_);
return v___x_1248_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonSamplesTable_fromJson_spec__0(lean_object* v_j_1249_, lean_object* v_k_1250_){
_start:
{
lean_object* v___x_1251_; lean_object* v___x_1252_; 
v___x_1251_ = l_Lean_Json_getObjValD(v_j_1249_, v_k_1250_);
v___x_1252_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonSamplesTable_fromJson_spec__0_spec__0(v___x_1251_);
return v___x_1252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonSamplesTable_fromJson_spec__0___boxed(lean_object* v_j_1253_, lean_object* v_k_1254_){
_start:
{
lean_object* v_res_1255_; 
v_res_1255_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonSamplesTable_fromJson_spec__0(v_j_1253_, v_k_1254_);
lean_dec_ref(v_k_1254_);
return v_res_1255_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonSamplesTable_fromJson_spec__1_spec__2_spec__4(size_t v_sz_1256_, size_t v_i_1257_, lean_object* v_bs_1258_){
_start:
{
uint8_t v___x_1259_; 
v___x_1259_ = lean_usize_dec_lt(v_i_1257_, v_sz_1256_);
if (v___x_1259_ == 0)
{
lean_object* v___x_1260_; 
v___x_1260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1260_, 0, v_bs_1258_);
return v___x_1260_;
}
else
{
lean_object* v_v_1261_; lean_object* v___x_1262_; 
v_v_1261_ = lean_array_uget_borrowed(v_bs_1258_, v_i_1257_);
lean_inc(v_v_1261_);
v___x_1262_ = l_Lean_Float_fromJson_x3f(v_v_1261_);
if (lean_obj_tag(v___x_1262_) == 0)
{
lean_object* v_a_1263_; lean_object* v___x_1265_; uint8_t v_isShared_1266_; uint8_t v_isSharedCheck_1270_; 
lean_dec_ref(v_bs_1258_);
v_a_1263_ = lean_ctor_get(v___x_1262_, 0);
v_isSharedCheck_1270_ = !lean_is_exclusive(v___x_1262_);
if (v_isSharedCheck_1270_ == 0)
{
v___x_1265_ = v___x_1262_;
v_isShared_1266_ = v_isSharedCheck_1270_;
goto v_resetjp_1264_;
}
else
{
lean_inc(v_a_1263_);
lean_dec(v___x_1262_);
v___x_1265_ = lean_box(0);
v_isShared_1266_ = v_isSharedCheck_1270_;
goto v_resetjp_1264_;
}
v_resetjp_1264_:
{
lean_object* v___x_1268_; 
if (v_isShared_1266_ == 0)
{
v___x_1268_ = v___x_1265_;
goto v_reusejp_1267_;
}
else
{
lean_object* v_reuseFailAlloc_1269_; 
v_reuseFailAlloc_1269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1269_, 0, v_a_1263_);
v___x_1268_ = v_reuseFailAlloc_1269_;
goto v_reusejp_1267_;
}
v_reusejp_1267_:
{
return v___x_1268_;
}
}
}
else
{
lean_object* v_a_1271_; lean_object* v___x_1272_; lean_object* v_bs_x27_1273_; size_t v___x_1274_; size_t v___x_1275_; lean_object* v___x_1276_; 
v_a_1271_ = lean_ctor_get(v___x_1262_, 0);
lean_inc(v_a_1271_);
lean_dec_ref_known(v___x_1262_, 1);
v___x_1272_ = lean_unsigned_to_nat(0u);
v_bs_x27_1273_ = lean_array_uset(v_bs_1258_, v_i_1257_, v___x_1272_);
v___x_1274_ = ((size_t)1ULL);
v___x_1275_ = lean_usize_add(v_i_1257_, v___x_1274_);
v___x_1276_ = lean_array_uset(v_bs_x27_1273_, v_i_1257_, v_a_1271_);
v_i_1257_ = v___x_1275_;
v_bs_1258_ = v___x_1276_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonSamplesTable_fromJson_spec__1_spec__2_spec__4___boxed(lean_object* v_sz_1278_, lean_object* v_i_1279_, lean_object* v_bs_1280_){
_start:
{
size_t v_sz_boxed_1281_; size_t v_i_boxed_1282_; lean_object* v_res_1283_; 
v_sz_boxed_1281_ = lean_unbox_usize(v_sz_1278_);
lean_dec(v_sz_1278_);
v_i_boxed_1282_ = lean_unbox_usize(v_i_1279_);
lean_dec(v_i_1279_);
v_res_1283_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonSamplesTable_fromJson_spec__1_spec__2_spec__4(v_sz_boxed_1281_, v_i_boxed_1282_, v_bs_1280_);
return v_res_1283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonSamplesTable_fromJson_spec__1_spec__2(lean_object* v_x_1284_){
_start:
{
if (lean_obj_tag(v_x_1284_) == 4)
{
lean_object* v_elems_1285_; size_t v_sz_1286_; size_t v___x_1287_; lean_object* v___x_1288_; 
v_elems_1285_ = lean_ctor_get(v_x_1284_, 0);
lean_inc_ref(v_elems_1285_);
lean_dec_ref_known(v_x_1284_, 1);
v_sz_1286_ = lean_array_size(v_elems_1285_);
v___x_1287_ = ((size_t)0ULL);
v___x_1288_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonSamplesTable_fromJson_spec__1_spec__2_spec__4(v_sz_1286_, v___x_1287_, v_elems_1285_);
return v___x_1288_;
}
else
{
lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; 
v___x_1289_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__2_spec__2___closed__0));
v___x_1290_ = lean_unsigned_to_nat(80u);
v___x_1291_ = l_Lean_Json_pretty(v_x_1284_, v___x_1290_);
v___x_1292_ = lean_string_append(v___x_1289_, v___x_1291_);
lean_dec_ref(v___x_1291_);
v___x_1293_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__2_spec__2___closed__1));
v___x_1294_ = lean_string_append(v___x_1292_, v___x_1293_);
v___x_1295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1295_, 0, v___x_1294_);
return v___x_1295_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonSamplesTable_fromJson_spec__1(lean_object* v_j_1296_, lean_object* v_k_1297_){
_start:
{
lean_object* v___x_1298_; lean_object* v___x_1299_; 
v___x_1298_ = l_Lean_Json_getObjValD(v_j_1296_, v_k_1297_);
v___x_1299_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonSamplesTable_fromJson_spec__1_spec__2(v___x_1298_);
return v___x_1299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonSamplesTable_fromJson_spec__1___boxed(lean_object* v_j_1300_, lean_object* v_k_1301_){
_start:
{
lean_object* v_res_1302_; 
v_res_1302_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonSamplesTable_fromJson_spec__1(v_j_1300_, v_k_1301_);
lean_dec_ref(v_k_1301_);
return v_res_1302_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__3(void){
_start:
{
uint8_t v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; 
v___x_1309_ = 1;
v___x_1310_ = ((lean_object*)(l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__2));
v___x_1311_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1310_, v___x_1309_);
return v___x_1311_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__4(void){
_start:
{
lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; 
v___x_1312_ = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__6));
v___x_1313_ = lean_obj_once(&l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__3, &l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__3_once, _init_l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__3);
v___x_1314_ = lean_string_append(v___x_1313_, v___x_1312_);
return v___x_1314_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__6(void){
_start:
{
uint8_t v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; 
v___x_1317_ = 1;
v___x_1318_ = ((lean_object*)(l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__5));
v___x_1319_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1318_, v___x_1317_);
return v___x_1319_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__7(void){
_start:
{
lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; 
v___x_1320_ = lean_obj_once(&l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__6, &l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__6_once, _init_l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__6);
v___x_1321_ = lean_obj_once(&l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__4, &l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__4_once, _init_l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__4);
v___x_1322_ = lean_string_append(v___x_1321_, v___x_1320_);
return v___x_1322_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__8(void){
_start:
{
lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; 
v___x_1323_ = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
v___x_1324_ = lean_obj_once(&l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__7, &l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__7_once, _init_l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__7);
v___x_1325_ = lean_string_append(v___x_1324_, v___x_1323_);
return v___x_1325_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__9(void){
_start:
{
lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; 
v___x_1326_ = lean_obj_once(&l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__6, &l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__6_once, _init_l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__6);
v___x_1327_ = lean_obj_once(&l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__4, &l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__4_once, _init_l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__4);
v___x_1328_ = lean_string_append(v___x_1327_, v___x_1326_);
return v___x_1328_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__10(void){
_start:
{
lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; 
v___x_1329_ = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
v___x_1330_ = lean_obj_once(&l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__9, &l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__9_once, _init_l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__9);
v___x_1331_ = lean_string_append(v___x_1330_, v___x_1329_);
return v___x_1331_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__13(void){
_start:
{
uint8_t v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; 
v___x_1335_ = 1;
v___x_1336_ = ((lean_object*)(l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__12));
v___x_1337_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1336_, v___x_1335_);
return v___x_1337_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__14(void){
_start:
{
lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; 
v___x_1338_ = lean_obj_once(&l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__13, &l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__13_once, _init_l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__13);
v___x_1339_ = lean_obj_once(&l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__4, &l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__4_once, _init_l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__4);
v___x_1340_ = lean_string_append(v___x_1339_, v___x_1338_);
return v___x_1340_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__15(void){
_start:
{
lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; 
v___x_1341_ = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
v___x_1342_ = lean_obj_once(&l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__14, &l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__14_once, _init_l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__14);
v___x_1343_ = lean_string_append(v___x_1342_, v___x_1341_);
return v___x_1343_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__18(void){
_start:
{
uint8_t v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; 
v___x_1347_ = 1;
v___x_1348_ = ((lean_object*)(l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__17));
v___x_1349_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1348_, v___x_1347_);
return v___x_1349_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__19(void){
_start:
{
lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; 
v___x_1350_ = lean_obj_once(&l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__18, &l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__18_once, _init_l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__18);
v___x_1351_ = lean_obj_once(&l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__4, &l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__4_once, _init_l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__4);
v___x_1352_ = lean_string_append(v___x_1351_, v___x_1350_);
return v___x_1352_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__20(void){
_start:
{
lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; 
v___x_1353_ = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
v___x_1354_ = lean_obj_once(&l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__19, &l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__19_once, _init_l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__19);
v___x_1355_ = lean_string_append(v___x_1354_, v___x_1353_);
return v___x_1355_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__21(void){
_start:
{
lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; 
v___x_1356_ = lean_obj_once(&l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__16, &l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__16_once, _init_l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__16);
v___x_1357_ = lean_obj_once(&l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__4, &l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__4_once, _init_l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__4);
v___x_1358_ = lean_string_append(v___x_1357_, v___x_1356_);
return v___x_1358_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__22(void){
_start:
{
lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; 
v___x_1359_ = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
v___x_1360_ = lean_obj_once(&l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__21, &l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__21_once, _init_l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__21);
v___x_1361_ = lean_string_append(v___x_1360_, v___x_1359_);
return v___x_1361_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__23(void){
_start:
{
lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; 
v___x_1362_ = lean_obj_once(&l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__26, &l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__26_once, _init_l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__26);
v___x_1363_ = lean_obj_once(&l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__4, &l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__4_once, _init_l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__4);
v___x_1364_ = lean_string_append(v___x_1363_, v___x_1362_);
return v___x_1364_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__24(void){
_start:
{
lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; 
v___x_1365_ = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
v___x_1366_ = lean_obj_once(&l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__23, &l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__23_once, _init_l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__23);
v___x_1367_ = lean_string_append(v___x_1366_, v___x_1365_);
return v___x_1367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Firefox_instFromJsonSamplesTable_fromJson(lean_object* v_json_1368_){
_start:
{
lean_object* v___x_1369_; lean_object* v___x_1370_; 
v___x_1369_ = ((lean_object*)(l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__0));
lean_inc(v_json_1368_);
v___x_1370_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonStackTable_fromJson_spec__0(v_json_1368_, v___x_1369_);
if (lean_obj_tag(v___x_1370_) == 0)
{
lean_object* v_a_1371_; lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1380_; 
lean_dec(v_json_1368_);
v_a_1371_ = lean_ctor_get(v___x_1370_, 0);
v_isSharedCheck_1380_ = !lean_is_exclusive(v___x_1370_);
if (v_isSharedCheck_1380_ == 0)
{
v___x_1373_ = v___x_1370_;
v_isShared_1374_ = v_isSharedCheck_1380_;
goto v_resetjp_1372_;
}
else
{
lean_inc(v_a_1371_);
lean_dec(v___x_1370_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1380_;
goto v_resetjp_1372_;
}
v_resetjp_1372_:
{
lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1378_; 
v___x_1375_ = lean_obj_once(&l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__8, &l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__8_once, _init_l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__8);
v___x_1376_ = lean_string_append(v___x_1375_, v_a_1371_);
lean_dec(v_a_1371_);
if (v_isShared_1374_ == 0)
{
lean_ctor_set(v___x_1373_, 0, v___x_1376_);
v___x_1378_ = v___x_1373_;
goto v_reusejp_1377_;
}
else
{
lean_object* v_reuseFailAlloc_1379_; 
v_reuseFailAlloc_1379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1379_, 0, v___x_1376_);
v___x_1378_ = v_reuseFailAlloc_1379_;
goto v_reusejp_1377_;
}
v_reusejp_1377_:
{
return v___x_1378_;
}
}
}
else
{
lean_object* v_a_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; 
v_a_1381_ = lean_ctor_get(v___x_1370_, 0);
lean_inc(v_a_1381_);
lean_dec_ref_known(v___x_1370_, 1);
v___x_1382_ = ((lean_object*)(l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__0));
lean_inc(v_json_1368_);
v___x_1383_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonSamplesTable_fromJson_spec__0(v_json_1368_, v___x_1382_);
if (lean_obj_tag(v___x_1383_) == 0)
{
lean_object* v_a_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1393_; 
lean_dec(v_a_1381_);
lean_dec(v_json_1368_);
v_a_1384_ = lean_ctor_get(v___x_1383_, 0);
v_isSharedCheck_1393_ = !lean_is_exclusive(v___x_1383_);
if (v_isSharedCheck_1393_ == 0)
{
v___x_1386_ = v___x_1383_;
v_isShared_1387_ = v_isSharedCheck_1393_;
goto v_resetjp_1385_;
}
else
{
lean_inc(v_a_1384_);
lean_dec(v___x_1383_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1393_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1391_; 
v___x_1388_ = lean_obj_once(&l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__10, &l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__10_once, _init_l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__10);
v___x_1389_ = lean_string_append(v___x_1388_, v_a_1384_);
lean_dec(v_a_1384_);
if (v_isShared_1387_ == 0)
{
lean_ctor_set(v___x_1386_, 0, v___x_1389_);
v___x_1391_ = v___x_1386_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v___x_1389_);
v___x_1391_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
return v___x_1391_;
}
}
}
else
{
lean_object* v_a_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; 
v_a_1394_ = lean_ctor_get(v___x_1383_, 0);
lean_inc(v_a_1394_);
lean_dec_ref_known(v___x_1383_, 1);
v___x_1395_ = ((lean_object*)(l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__11));
lean_inc(v_json_1368_);
v___x_1396_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonSamplesTable_fromJson_spec__0(v_json_1368_, v___x_1395_);
if (lean_obj_tag(v___x_1396_) == 0)
{
lean_object* v_a_1397_; lean_object* v___x_1399_; uint8_t v_isShared_1400_; uint8_t v_isSharedCheck_1406_; 
lean_dec(v_a_1394_);
lean_dec(v_a_1381_);
lean_dec(v_json_1368_);
v_a_1397_ = lean_ctor_get(v___x_1396_, 0);
v_isSharedCheck_1406_ = !lean_is_exclusive(v___x_1396_);
if (v_isSharedCheck_1406_ == 0)
{
v___x_1399_ = v___x_1396_;
v_isShared_1400_ = v_isSharedCheck_1406_;
goto v_resetjp_1398_;
}
else
{
lean_inc(v_a_1397_);
lean_dec(v___x_1396_);
v___x_1399_ = lean_box(0);
v_isShared_1400_ = v_isSharedCheck_1406_;
goto v_resetjp_1398_;
}
v_resetjp_1398_:
{
lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1404_; 
v___x_1401_ = lean_obj_once(&l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__15, &l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__15_once, _init_l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__15);
v___x_1402_ = lean_string_append(v___x_1401_, v_a_1397_);
lean_dec(v_a_1397_);
if (v_isShared_1400_ == 0)
{
lean_ctor_set(v___x_1399_, 0, v___x_1402_);
v___x_1404_ = v___x_1399_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1405_; 
v_reuseFailAlloc_1405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1405_, 0, v___x_1402_);
v___x_1404_ = v_reuseFailAlloc_1405_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
return v___x_1404_;
}
}
}
else
{
lean_object* v_a_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; 
v_a_1407_ = lean_ctor_get(v___x_1396_, 0);
lean_inc(v_a_1407_);
lean_dec_ref_known(v___x_1396_, 1);
v___x_1408_ = ((lean_object*)(l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__16));
lean_inc(v_json_1368_);
v___x_1409_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__1(v_json_1368_, v___x_1408_);
if (lean_obj_tag(v___x_1409_) == 0)
{
lean_object* v_a_1410_; lean_object* v___x_1412_; uint8_t v_isShared_1413_; uint8_t v_isSharedCheck_1419_; 
lean_dec(v_a_1407_);
lean_dec(v_a_1394_);
lean_dec(v_a_1381_);
lean_dec(v_json_1368_);
v_a_1410_ = lean_ctor_get(v___x_1409_, 0);
v_isSharedCheck_1419_ = !lean_is_exclusive(v___x_1409_);
if (v_isSharedCheck_1419_ == 0)
{
v___x_1412_ = v___x_1409_;
v_isShared_1413_ = v_isSharedCheck_1419_;
goto v_resetjp_1411_;
}
else
{
lean_inc(v_a_1410_);
lean_dec(v___x_1409_);
v___x_1412_ = lean_box(0);
v_isShared_1413_ = v_isSharedCheck_1419_;
goto v_resetjp_1411_;
}
v_resetjp_1411_:
{
lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1417_; 
v___x_1414_ = lean_obj_once(&l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__20, &l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__20_once, _init_l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__20);
v___x_1415_ = lean_string_append(v___x_1414_, v_a_1410_);
lean_dec(v_a_1410_);
if (v_isShared_1413_ == 0)
{
lean_ctor_set(v___x_1412_, 0, v___x_1415_);
v___x_1417_ = v___x_1412_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v___x_1415_);
v___x_1417_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
return v___x_1417_;
}
}
}
else
{
lean_object* v_a_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; 
v_a_1420_ = lean_ctor_get(v___x_1409_, 0);
lean_inc(v_a_1420_);
lean_dec_ref_known(v___x_1409_, 1);
v___x_1421_ = ((lean_object*)(l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__14));
lean_inc(v_json_1368_);
v___x_1422_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonSamplesTable_fromJson_spec__1(v_json_1368_, v___x_1421_);
if (lean_obj_tag(v___x_1422_) == 0)
{
lean_object* v_a_1423_; lean_object* v___x_1425_; uint8_t v_isShared_1426_; uint8_t v_isSharedCheck_1432_; 
lean_dec(v_a_1420_);
lean_dec(v_a_1407_);
lean_dec(v_a_1394_);
lean_dec(v_a_1381_);
lean_dec(v_json_1368_);
v_a_1423_ = lean_ctor_get(v___x_1422_, 0);
v_isSharedCheck_1432_ = !lean_is_exclusive(v___x_1422_);
if (v_isSharedCheck_1432_ == 0)
{
v___x_1425_ = v___x_1422_;
v_isShared_1426_ = v_isSharedCheck_1432_;
goto v_resetjp_1424_;
}
else
{
lean_inc(v_a_1423_);
lean_dec(v___x_1422_);
v___x_1425_ = lean_box(0);
v_isShared_1426_ = v_isSharedCheck_1432_;
goto v_resetjp_1424_;
}
v_resetjp_1424_:
{
lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1430_; 
v___x_1427_ = lean_obj_once(&l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__22, &l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__22_once, _init_l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__22);
v___x_1428_ = lean_string_append(v___x_1427_, v_a_1423_);
lean_dec(v_a_1423_);
if (v_isShared_1426_ == 0)
{
lean_ctor_set(v___x_1425_, 0, v___x_1428_);
v___x_1430_ = v___x_1425_;
goto v_reusejp_1429_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v___x_1428_);
v___x_1430_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1429_;
}
v_reusejp_1429_:
{
return v___x_1430_;
}
}
}
else
{
lean_object* v_a_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; 
v_a_1433_ = lean_ctor_get(v___x_1422_, 0);
lean_inc(v_a_1433_);
lean_dec_ref_known(v___x_1422_, 1);
v___x_1434_ = ((lean_object*)(l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__24));
v___x_1435_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__2(v_json_1368_, v___x_1434_);
if (lean_obj_tag(v___x_1435_) == 0)
{
lean_object* v_a_1436_; lean_object* v___x_1438_; uint8_t v_isShared_1439_; uint8_t v_isSharedCheck_1445_; 
lean_dec(v_a_1433_);
lean_dec(v_a_1420_);
lean_dec(v_a_1407_);
lean_dec(v_a_1394_);
lean_dec(v_a_1381_);
v_a_1436_ = lean_ctor_get(v___x_1435_, 0);
v_isSharedCheck_1445_ = !lean_is_exclusive(v___x_1435_);
if (v_isSharedCheck_1445_ == 0)
{
v___x_1438_ = v___x_1435_;
v_isShared_1439_ = v_isSharedCheck_1445_;
goto v_resetjp_1437_;
}
else
{
lean_inc(v_a_1436_);
lean_dec(v___x_1435_);
v___x_1438_ = lean_box(0);
v_isShared_1439_ = v_isSharedCheck_1445_;
goto v_resetjp_1437_;
}
v_resetjp_1437_:
{
lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1443_; 
v___x_1440_ = lean_obj_once(&l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__24, &l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__24_once, _init_l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__24);
v___x_1441_ = lean_string_append(v___x_1440_, v_a_1436_);
lean_dec(v_a_1436_);
if (v_isShared_1439_ == 0)
{
lean_ctor_set(v___x_1438_, 0, v___x_1441_);
v___x_1443_ = v___x_1438_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v___x_1441_);
v___x_1443_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
return v___x_1443_;
}
}
}
else
{
lean_object* v_a_1446_; lean_object* v___x_1448_; uint8_t v_isShared_1449_; uint8_t v_isSharedCheck_1454_; 
v_a_1446_ = lean_ctor_get(v___x_1435_, 0);
v_isSharedCheck_1454_ = !lean_is_exclusive(v___x_1435_);
if (v_isSharedCheck_1454_ == 0)
{
v___x_1448_ = v___x_1435_;
v_isShared_1449_ = v_isSharedCheck_1454_;
goto v_resetjp_1447_;
}
else
{
lean_inc(v_a_1446_);
lean_dec(v___x_1435_);
v___x_1448_ = lean_box(0);
v_isShared_1449_ = v_isSharedCheck_1454_;
goto v_resetjp_1447_;
}
v_resetjp_1447_:
{
lean_object* v___x_1450_; lean_object* v___x_1452_; 
v___x_1450_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1450_, 0, v_a_1381_);
lean_ctor_set(v___x_1450_, 1, v_a_1394_);
lean_ctor_set(v___x_1450_, 2, v_a_1407_);
lean_ctor_set(v___x_1450_, 3, v_a_1420_);
lean_ctor_set(v___x_1450_, 4, v_a_1433_);
lean_ctor_set(v___x_1450_, 5, v_a_1446_);
if (v_isShared_1449_ == 0)
{
lean_ctor_set(v___x_1448_, 0, v___x_1450_);
v___x_1452_ = v___x_1448_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v___x_1450_);
v___x_1452_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
return v___x_1452_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Firefox_instToJsonSamplesTable_toJson_spec__1_spec__2(size_t v_sz_1457_, size_t v_i_1458_, lean_object* v_bs_1459_){
_start:
{
uint8_t v___x_1460_; 
v___x_1460_ = lean_usize_dec_lt(v_i_1458_, v_sz_1457_);
if (v___x_1460_ == 0)
{
return v_bs_1459_;
}
else
{
lean_object* v_v_1461_; lean_object* v___x_1462_; lean_object* v_bs_x27_1463_; double v___x_1464_; lean_object* v___x_1465_; size_t v___x_1466_; size_t v___x_1467_; lean_object* v___x_1468_; 
v_v_1461_ = lean_array_uget(v_bs_1459_, v_i_1458_);
v___x_1462_ = lean_unsigned_to_nat(0u);
v_bs_x27_1463_ = lean_array_uset(v_bs_1459_, v_i_1458_, v___x_1462_);
v___x_1464_ = lean_unbox_float(v_v_1461_);
lean_dec(v_v_1461_);
v___x_1465_ = l_Lean_Float_toJson(v___x_1464_);
v___x_1466_ = ((size_t)1ULL);
v___x_1467_ = lean_usize_add(v_i_1458_, v___x_1466_);
v___x_1468_ = lean_array_uset(v_bs_x27_1463_, v_i_1458_, v___x_1465_);
v_i_1458_ = v___x_1467_;
v_bs_1459_ = v___x_1468_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Firefox_instToJsonSamplesTable_toJson_spec__1_spec__2___boxed(lean_object* v_sz_1470_, lean_object* v_i_1471_, lean_object* v_bs_1472_){
_start:
{
size_t v_sz_boxed_1473_; size_t v_i_boxed_1474_; lean_object* v_res_1475_; 
v_sz_boxed_1473_ = lean_unbox_usize(v_sz_1470_);
lean_dec(v_sz_1470_);
v_i_boxed_1474_ = lean_unbox_usize(v_i_1471_);
lean_dec(v_i_1471_);
v_res_1475_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Firefox_instToJsonSamplesTable_toJson_spec__1_spec__2(v_sz_boxed_1473_, v_i_boxed_1474_, v_bs_1472_);
return v_res_1475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Firefox_instToJsonSamplesTable_toJson_spec__1(lean_object* v_a_1476_){
_start:
{
size_t v_sz_1477_; size_t v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; 
v_sz_1477_ = lean_array_size(v_a_1476_);
v___x_1478_ = ((size_t)0ULL);
v___x_1479_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Firefox_instToJsonSamplesTable_toJson_spec__1_spec__2(v_sz_1477_, v___x_1478_, v_a_1476_);
v___x_1480_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1480_, 0, v___x_1479_);
return v___x_1480_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Firefox_instToJsonSamplesTable_toJson_spec__0_spec__0(size_t v_sz_1481_, size_t v_i_1482_, lean_object* v_bs_1483_){
_start:
{
uint8_t v___x_1484_; 
v___x_1484_ = lean_usize_dec_lt(v_i_1482_, v_sz_1481_);
if (v___x_1484_ == 0)
{
return v_bs_1483_;
}
else
{
lean_object* v_v_1485_; lean_object* v___x_1486_; lean_object* v_bs_x27_1487_; double v___x_1488_; lean_object* v___x_1489_; size_t v___x_1490_; size_t v___x_1491_; lean_object* v___x_1492_; 
v_v_1485_ = lean_array_uget(v_bs_1483_, v_i_1482_);
v___x_1486_ = lean_unsigned_to_nat(0u);
v_bs_x27_1487_ = lean_array_uset(v_bs_1483_, v_i_1482_, v___x_1486_);
v___x_1488_ = lean_unbox_float(v_v_1485_);
lean_dec(v_v_1485_);
v___x_1489_ = l_Lean_Float_toJson(v___x_1488_);
v___x_1490_ = ((size_t)1ULL);
v___x_1491_ = lean_usize_add(v_i_1482_, v___x_1490_);
v___x_1492_ = lean_array_uset(v_bs_x27_1487_, v_i_1482_, v___x_1489_);
v_i_1482_ = v___x_1491_;
v_bs_1483_ = v___x_1492_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Firefox_instToJsonSamplesTable_toJson_spec__0_spec__0___boxed(lean_object* v_sz_1494_, lean_object* v_i_1495_, lean_object* v_bs_1496_){
_start:
{
size_t v_sz_boxed_1497_; size_t v_i_boxed_1498_; lean_object* v_res_1499_; 
v_sz_boxed_1497_ = lean_unbox_usize(v_sz_1494_);
lean_dec(v_sz_1494_);
v_i_boxed_1498_ = lean_unbox_usize(v_i_1495_);
lean_dec(v_i_1495_);
v_res_1499_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Firefox_instToJsonSamplesTable_toJson_spec__0_spec__0(v_sz_boxed_1497_, v_i_boxed_1498_, v_bs_1496_);
return v_res_1499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Firefox_instToJsonSamplesTable_toJson_spec__0(lean_object* v_a_1500_){
_start:
{
size_t v_sz_1501_; size_t v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; 
v_sz_1501_ = lean_array_size(v_a_1500_);
v___x_1502_ = ((size_t)0ULL);
v___x_1503_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Firefox_instToJsonSamplesTable_toJson_spec__0_spec__0(v_sz_1501_, v___x_1502_, v_a_1500_);
v___x_1504_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1504_, 0, v___x_1503_);
return v___x_1504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Firefox_instToJsonSamplesTable_toJson(lean_object* v_x_1505_){
_start:
{
lean_object* v_stack_1506_; lean_object* v_time_1507_; lean_object* v_weight_1508_; lean_object* v_weightType_1509_; lean_object* v_threadCPUDelta_1510_; lean_object* v_length_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; 
v_stack_1506_ = lean_ctor_get(v_x_1505_, 0);
lean_inc_ref(v_stack_1506_);
v_time_1507_ = lean_ctor_get(v_x_1505_, 1);
lean_inc_ref(v_time_1507_);
v_weight_1508_ = lean_ctor_get(v_x_1505_, 2);
lean_inc_ref(v_weight_1508_);
v_weightType_1509_ = lean_ctor_get(v_x_1505_, 3);
lean_inc_ref(v_weightType_1509_);
v_threadCPUDelta_1510_ = lean_ctor_get(v_x_1505_, 4);
lean_inc_ref(v_threadCPUDelta_1510_);
v_length_1511_ = lean_ctor_get(v_x_1505_, 5);
lean_inc(v_length_1511_);
lean_dec_ref(v_x_1505_);
v___x_1512_ = ((lean_object*)(l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__0));
v___x_1513_ = l_Lean_Array_toJson___at___00Lean_Firefox_instToJsonStackTable_toJson_spec__0(v_stack_1506_);
v___x_1514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1514_, 0, v___x_1512_);
lean_ctor_set(v___x_1514_, 1, v___x_1513_);
v___x_1515_ = lean_box(0);
v___x_1516_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1516_, 0, v___x_1514_);
lean_ctor_set(v___x_1516_, 1, v___x_1515_);
v___x_1517_ = ((lean_object*)(l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__0));
v___x_1518_ = l_Lean_Array_toJson___at___00Lean_Firefox_instToJsonSamplesTable_toJson_spec__0(v_time_1507_);
v___x_1519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1519_, 0, v___x_1517_);
lean_ctor_set(v___x_1519_, 1, v___x_1518_);
v___x_1520_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1520_, 0, v___x_1519_);
lean_ctor_set(v___x_1520_, 1, v___x_1515_);
v___x_1521_ = ((lean_object*)(l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__11));
v___x_1522_ = l_Lean_Array_toJson___at___00Lean_Firefox_instToJsonSamplesTable_toJson_spec__0(v_weight_1508_);
v___x_1523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1523_, 0, v___x_1521_);
lean_ctor_set(v___x_1523_, 1, v___x_1522_);
v___x_1524_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1524_, 0, v___x_1523_);
lean_ctor_set(v___x_1524_, 1, v___x_1515_);
v___x_1525_ = ((lean_object*)(l_Lean_Firefox_instFromJsonSamplesTable_fromJson___closed__16));
v___x_1526_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1526_, 0, v_weightType_1509_);
v___x_1527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1527_, 0, v___x_1525_);
lean_ctor_set(v___x_1527_, 1, v___x_1526_);
v___x_1528_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1528_, 0, v___x_1527_);
lean_ctor_set(v___x_1528_, 1, v___x_1515_);
v___x_1529_ = ((lean_object*)(l_Lean_Firefox_instFromJsonSampleUnits_fromJson___closed__14));
v___x_1530_ = l_Lean_Array_toJson___at___00Lean_Firefox_instToJsonSamplesTable_toJson_spec__1(v_threadCPUDelta_1510_);
v___x_1531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1531_, 0, v___x_1529_);
lean_ctor_set(v___x_1531_, 1, v___x_1530_);
v___x_1532_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1532_, 0, v___x_1531_);
lean_ctor_set(v___x_1532_, 1, v___x_1515_);
v___x_1533_ = ((lean_object*)(l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__24));
v___x_1534_ = l_Lean_JsonNumber_fromNat(v_length_1511_);
v___x_1535_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1535_, 0, v___x_1534_);
v___x_1536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1536_, 0, v___x_1533_);
lean_ctor_set(v___x_1536_, 1, v___x_1535_);
v___x_1537_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1537_, 0, v___x_1536_);
lean_ctor_set(v___x_1537_, 1, v___x_1515_);
v___x_1538_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1538_, 0, v___x_1537_);
lean_ctor_set(v___x_1538_, 1, v___x_1515_);
v___x_1539_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1539_, 0, v___x_1532_);
lean_ctor_set(v___x_1539_, 1, v___x_1538_);
v___x_1540_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1540_, 0, v___x_1528_);
lean_ctor_set(v___x_1540_, 1, v___x_1539_);
v___x_1541_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1541_, 0, v___x_1524_);
lean_ctor_set(v___x_1541_, 1, v___x_1540_);
v___x_1542_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1542_, 0, v___x_1520_);
lean_ctor_set(v___x_1542_, 1, v___x_1541_);
v___x_1543_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1543_, 0, v___x_1516_);
lean_ctor_set(v___x_1543_, 1, v___x_1542_);
v___x_1544_ = ((lean_object*)(l_Lean_Firefox_instToJsonCategory_toJson___closed__0));
v___x_1545_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Firefox_instToJsonCategory_toJson_spec__1(v___x_1543_, v___x_1544_);
v___x_1546_ = l_Lean_Json_mkObj(v___x_1545_);
lean_dec(v___x_1545_);
return v___x_1546_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonFuncTable_fromJson_spec__0_spec__0_spec__1(size_t v_sz_1549_, size_t v_i_1550_, lean_object* v_bs_1551_){
_start:
{
uint8_t v___x_1552_; 
v___x_1552_ = lean_usize_dec_lt(v_i_1550_, v_sz_1549_);
if (v___x_1552_ == 0)
{
lean_object* v___x_1553_; 
v___x_1553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1553_, 0, v_bs_1551_);
return v___x_1553_;
}
else
{
lean_object* v_v_1554_; lean_object* v___x_1555_; 
v_v_1554_ = lean_array_uget_borrowed(v_bs_1551_, v_i_1550_);
lean_inc(v_v_1554_);
v___x_1555_ = l_Lean_Json_getInt_x3f(v_v_1554_);
if (lean_obj_tag(v___x_1555_) == 0)
{
lean_object* v_a_1556_; lean_object* v___x_1558_; uint8_t v_isShared_1559_; uint8_t v_isSharedCheck_1563_; 
lean_dec_ref(v_bs_1551_);
v_a_1556_ = lean_ctor_get(v___x_1555_, 0);
v_isSharedCheck_1563_ = !lean_is_exclusive(v___x_1555_);
if (v_isSharedCheck_1563_ == 0)
{
v___x_1558_ = v___x_1555_;
v_isShared_1559_ = v_isSharedCheck_1563_;
goto v_resetjp_1557_;
}
else
{
lean_inc(v_a_1556_);
lean_dec(v___x_1555_);
v___x_1558_ = lean_box(0);
v_isShared_1559_ = v_isSharedCheck_1563_;
goto v_resetjp_1557_;
}
v_resetjp_1557_:
{
lean_object* v___x_1561_; 
if (v_isShared_1559_ == 0)
{
v___x_1561_ = v___x_1558_;
goto v_reusejp_1560_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v_a_1556_);
v___x_1561_ = v_reuseFailAlloc_1562_;
goto v_reusejp_1560_;
}
v_reusejp_1560_:
{
return v___x_1561_;
}
}
}
else
{
lean_object* v_a_1564_; lean_object* v___x_1565_; lean_object* v_bs_x27_1566_; size_t v___x_1567_; size_t v___x_1568_; lean_object* v___x_1569_; 
v_a_1564_ = lean_ctor_get(v___x_1555_, 0);
lean_inc(v_a_1564_);
lean_dec_ref_known(v___x_1555_, 1);
v___x_1565_ = lean_unsigned_to_nat(0u);
v_bs_x27_1566_ = lean_array_uset(v_bs_1551_, v_i_1550_, v___x_1565_);
v___x_1567_ = ((size_t)1ULL);
v___x_1568_ = lean_usize_add(v_i_1550_, v___x_1567_);
v___x_1569_ = lean_array_uset(v_bs_x27_1566_, v_i_1550_, v_a_1564_);
v_i_1550_ = v___x_1568_;
v_bs_1551_ = v___x_1569_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonFuncTable_fromJson_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_1571_, lean_object* v_i_1572_, lean_object* v_bs_1573_){
_start:
{
size_t v_sz_boxed_1574_; size_t v_i_boxed_1575_; lean_object* v_res_1576_; 
v_sz_boxed_1574_ = lean_unbox_usize(v_sz_1571_);
lean_dec(v_sz_1571_);
v_i_boxed_1575_ = lean_unbox_usize(v_i_1572_);
lean_dec(v_i_1572_);
v_res_1576_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonFuncTable_fromJson_spec__0_spec__0_spec__1(v_sz_boxed_1574_, v_i_boxed_1575_, v_bs_1573_);
return v_res_1576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonFuncTable_fromJson_spec__0_spec__0(lean_object* v_x_1577_){
_start:
{
if (lean_obj_tag(v_x_1577_) == 4)
{
lean_object* v_elems_1578_; size_t v_sz_1579_; size_t v___x_1580_; lean_object* v___x_1581_; 
v_elems_1578_ = lean_ctor_get(v_x_1577_, 0);
lean_inc_ref(v_elems_1578_);
lean_dec_ref_known(v_x_1577_, 1);
v_sz_1579_ = lean_array_size(v_elems_1578_);
v___x_1580_ = ((size_t)0ULL);
v___x_1581_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonFuncTable_fromJson_spec__0_spec__0_spec__1(v_sz_1579_, v___x_1580_, v_elems_1578_);
return v___x_1581_;
}
else
{
lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; 
v___x_1582_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__2_spec__2___closed__0));
v___x_1583_ = lean_unsigned_to_nat(80u);
v___x_1584_ = l_Lean_Json_pretty(v_x_1577_, v___x_1583_);
v___x_1585_ = lean_string_append(v___x_1582_, v___x_1584_);
lean_dec_ref(v___x_1584_);
v___x_1586_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__2_spec__2___closed__1));
v___x_1587_ = lean_string_append(v___x_1585_, v___x_1586_);
v___x_1588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1588_, 0, v___x_1587_);
return v___x_1588_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonFuncTable_fromJson_spec__0(lean_object* v_j_1589_, lean_object* v_k_1590_){
_start:
{
lean_object* v___x_1591_; lean_object* v___x_1592_; 
v___x_1591_ = l_Lean_Json_getObjValD(v_j_1589_, v_k_1590_);
v___x_1592_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonFuncTable_fromJson_spec__0_spec__0(v___x_1591_);
return v___x_1592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonFuncTable_fromJson_spec__0___boxed(lean_object* v_j_1593_, lean_object* v_k_1594_){
_start:
{
lean_object* v_res_1595_; 
v_res_1595_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonFuncTable_fromJson_spec__0(v_j_1593_, v_k_1594_);
lean_dec_ref(v_k_1594_);
return v_res_1595_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__2(void){
_start:
{
uint8_t v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; 
v___x_1601_ = 1;
v___x_1602_ = ((lean_object*)(l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__1));
v___x_1603_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1602_, v___x_1601_);
return v___x_1603_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__3(void){
_start:
{
lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; 
v___x_1604_ = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__6));
v___x_1605_ = lean_obj_once(&l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__2, &l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__2_once, _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__2);
v___x_1606_ = lean_string_append(v___x_1605_, v___x_1604_);
return v___x_1606_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__4(void){
_start:
{
lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; 
v___x_1607_ = lean_obj_once(&l_Lean_Firefox_instFromJsonCategory_fromJson___closed__9, &l_Lean_Firefox_instFromJsonCategory_fromJson___closed__9_once, _init_l_Lean_Firefox_instFromJsonCategory_fromJson___closed__9);
v___x_1608_ = lean_obj_once(&l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__3, &l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__3_once, _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__3);
v___x_1609_ = lean_string_append(v___x_1608_, v___x_1607_);
return v___x_1609_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__5(void){
_start:
{
lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; 
v___x_1610_ = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
v___x_1611_ = lean_obj_once(&l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__4, &l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__4_once, _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__4);
v___x_1612_ = lean_string_append(v___x_1611_, v___x_1610_);
return v___x_1612_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__8(void){
_start:
{
uint8_t v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; 
v___x_1616_ = 1;
v___x_1617_ = ((lean_object*)(l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__7));
v___x_1618_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1617_, v___x_1616_);
return v___x_1618_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__9(void){
_start:
{
lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; 
v___x_1619_ = lean_obj_once(&l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__8, &l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__8_once, _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__8);
v___x_1620_ = lean_obj_once(&l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__3, &l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__3_once, _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__3);
v___x_1621_ = lean_string_append(v___x_1620_, v___x_1619_);
return v___x_1621_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__10(void){
_start:
{
lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; 
v___x_1622_ = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
v___x_1623_ = lean_obj_once(&l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__9, &l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__9_once, _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__9);
v___x_1624_ = lean_string_append(v___x_1623_, v___x_1622_);
return v___x_1624_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__13(void){
_start:
{
uint8_t v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; 
v___x_1628_ = 1;
v___x_1629_ = ((lean_object*)(l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__12));
v___x_1630_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1629_, v___x_1628_);
return v___x_1630_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__14(void){
_start:
{
lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; 
v___x_1631_ = lean_obj_once(&l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__13, &l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__13_once, _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__13);
v___x_1632_ = lean_obj_once(&l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__3, &l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__3_once, _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__3);
v___x_1633_ = lean_string_append(v___x_1632_, v___x_1631_);
return v___x_1633_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__15(void){
_start:
{
lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; 
v___x_1634_ = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
v___x_1635_ = lean_obj_once(&l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__14, &l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__14_once, _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__14);
v___x_1636_ = lean_string_append(v___x_1635_, v___x_1634_);
return v___x_1636_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__18(void){
_start:
{
uint8_t v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; 
v___x_1640_ = 1;
v___x_1641_ = ((lean_object*)(l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__17));
v___x_1642_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1641_, v___x_1640_);
return v___x_1642_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__19(void){
_start:
{
lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; 
v___x_1643_ = lean_obj_once(&l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__18, &l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__18_once, _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__18);
v___x_1644_ = lean_obj_once(&l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__3, &l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__3_once, _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__3);
v___x_1645_ = lean_string_append(v___x_1644_, v___x_1643_);
return v___x_1645_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__20(void){
_start:
{
lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; 
v___x_1646_ = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
v___x_1647_ = lean_obj_once(&l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__19, &l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__19_once, _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__19);
v___x_1648_ = lean_string_append(v___x_1647_, v___x_1646_);
return v___x_1648_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__23(void){
_start:
{
uint8_t v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; 
v___x_1652_ = 1;
v___x_1653_ = ((lean_object*)(l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__22));
v___x_1654_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1653_, v___x_1652_);
return v___x_1654_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__24(void){
_start:
{
lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; 
v___x_1655_ = lean_obj_once(&l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__23, &l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__23_once, _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__23);
v___x_1656_ = lean_obj_once(&l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__3, &l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__3_once, _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__3);
v___x_1657_ = lean_string_append(v___x_1656_, v___x_1655_);
return v___x_1657_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__25(void){
_start:
{
lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; 
v___x_1658_ = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
v___x_1659_ = lean_obj_once(&l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__24, &l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__24_once, _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__24);
v___x_1660_ = lean_string_append(v___x_1659_, v___x_1658_);
return v___x_1660_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__28(void){
_start:
{
uint8_t v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; 
v___x_1664_ = 1;
v___x_1665_ = ((lean_object*)(l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__27));
v___x_1666_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1665_, v___x_1664_);
return v___x_1666_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__29(void){
_start:
{
lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; 
v___x_1667_ = lean_obj_once(&l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__28, &l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__28_once, _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__28);
v___x_1668_ = lean_obj_once(&l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__3, &l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__3_once, _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__3);
v___x_1669_ = lean_string_append(v___x_1668_, v___x_1667_);
return v___x_1669_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__30(void){
_start:
{
lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; 
v___x_1670_ = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
v___x_1671_ = lean_obj_once(&l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__29, &l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__29_once, _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__29);
v___x_1672_ = lean_string_append(v___x_1671_, v___x_1670_);
return v___x_1672_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__33(void){
_start:
{
uint8_t v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; 
v___x_1676_ = 1;
v___x_1677_ = ((lean_object*)(l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__32));
v___x_1678_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1677_, v___x_1676_);
return v___x_1678_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__34(void){
_start:
{
lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; 
v___x_1679_ = lean_obj_once(&l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__33, &l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__33_once, _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__33);
v___x_1680_ = lean_obj_once(&l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__3, &l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__3_once, _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__3);
v___x_1681_ = lean_string_append(v___x_1680_, v___x_1679_);
return v___x_1681_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__35(void){
_start:
{
lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; 
v___x_1682_ = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
v___x_1683_ = lean_obj_once(&l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__34, &l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__34_once, _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__34);
v___x_1684_ = lean_string_append(v___x_1683_, v___x_1682_);
return v___x_1684_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__36(void){
_start:
{
lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; 
v___x_1685_ = lean_obj_once(&l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__26, &l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__26_once, _init_l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__26);
v___x_1686_ = lean_obj_once(&l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__3, &l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__3_once, _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__3);
v___x_1687_ = lean_string_append(v___x_1686_, v___x_1685_);
return v___x_1687_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__37(void){
_start:
{
lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; 
v___x_1688_ = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
v___x_1689_ = lean_obj_once(&l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__36, &l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__36_once, _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__36);
v___x_1690_ = lean_string_append(v___x_1689_, v___x_1688_);
return v___x_1690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Firefox_instFromJsonFuncTable_fromJson(lean_object* v_json_1691_){
_start:
{
lean_object* v___x_1692_; lean_object* v___x_1693_; 
v___x_1692_ = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__0));
lean_inc(v_json_1691_);
v___x_1693_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonStackTable_fromJson_spec__0(v_json_1691_, v___x_1692_);
if (lean_obj_tag(v___x_1693_) == 0)
{
lean_object* v_a_1694_; lean_object* v___x_1696_; uint8_t v_isShared_1697_; uint8_t v_isSharedCheck_1703_; 
lean_dec(v_json_1691_);
v_a_1694_ = lean_ctor_get(v___x_1693_, 0);
v_isSharedCheck_1703_ = !lean_is_exclusive(v___x_1693_);
if (v_isSharedCheck_1703_ == 0)
{
v___x_1696_ = v___x_1693_;
v_isShared_1697_ = v_isSharedCheck_1703_;
goto v_resetjp_1695_;
}
else
{
lean_inc(v_a_1694_);
lean_dec(v___x_1693_);
v___x_1696_ = lean_box(0);
v_isShared_1697_ = v_isSharedCheck_1703_;
goto v_resetjp_1695_;
}
v_resetjp_1695_:
{
lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1701_; 
v___x_1698_ = lean_obj_once(&l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__5, &l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__5_once, _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__5);
v___x_1699_ = lean_string_append(v___x_1698_, v_a_1694_);
lean_dec(v_a_1694_);
if (v_isShared_1697_ == 0)
{
lean_ctor_set(v___x_1696_, 0, v___x_1699_);
v___x_1701_ = v___x_1696_;
goto v_reusejp_1700_;
}
else
{
lean_object* v_reuseFailAlloc_1702_; 
v_reuseFailAlloc_1702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1702_, 0, v___x_1699_);
v___x_1701_ = v_reuseFailAlloc_1702_;
goto v_reusejp_1700_;
}
v_reusejp_1700_:
{
return v___x_1701_;
}
}
}
else
{
lean_object* v_a_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; 
v_a_1704_ = lean_ctor_get(v___x_1693_, 0);
lean_inc(v_a_1704_);
lean_dec_ref_known(v___x_1693_, 1);
v___x_1705_ = ((lean_object*)(l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__6));
lean_inc(v_json_1691_);
v___x_1706_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__3(v_json_1691_, v___x_1705_);
if (lean_obj_tag(v___x_1706_) == 0)
{
lean_object* v_a_1707_; lean_object* v___x_1709_; uint8_t v_isShared_1710_; uint8_t v_isSharedCheck_1716_; 
lean_dec(v_a_1704_);
lean_dec(v_json_1691_);
v_a_1707_ = lean_ctor_get(v___x_1706_, 0);
v_isSharedCheck_1716_ = !lean_is_exclusive(v___x_1706_);
if (v_isSharedCheck_1716_ == 0)
{
v___x_1709_ = v___x_1706_;
v_isShared_1710_ = v_isSharedCheck_1716_;
goto v_resetjp_1708_;
}
else
{
lean_inc(v_a_1707_);
lean_dec(v___x_1706_);
v___x_1709_ = lean_box(0);
v_isShared_1710_ = v_isSharedCheck_1716_;
goto v_resetjp_1708_;
}
v_resetjp_1708_:
{
lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1714_; 
v___x_1711_ = lean_obj_once(&l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__10, &l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__10_once, _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__10);
v___x_1712_ = lean_string_append(v___x_1711_, v_a_1707_);
lean_dec(v_a_1707_);
if (v_isShared_1710_ == 0)
{
lean_ctor_set(v___x_1709_, 0, v___x_1712_);
v___x_1714_ = v___x_1709_;
goto v_reusejp_1713_;
}
else
{
lean_object* v_reuseFailAlloc_1715_; 
v_reuseFailAlloc_1715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1715_, 0, v___x_1712_);
v___x_1714_ = v_reuseFailAlloc_1715_;
goto v_reusejp_1713_;
}
v_reusejp_1713_:
{
return v___x_1714_;
}
}
}
else
{
lean_object* v_a_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; 
v_a_1717_ = lean_ctor_get(v___x_1706_, 0);
lean_inc(v_a_1717_);
lean_dec_ref_known(v___x_1706_, 1);
v___x_1718_ = ((lean_object*)(l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__11));
lean_inc(v_json_1691_);
v___x_1719_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__3(v_json_1691_, v___x_1718_);
if (lean_obj_tag(v___x_1719_) == 0)
{
lean_object* v_a_1720_; lean_object* v___x_1722_; uint8_t v_isShared_1723_; uint8_t v_isSharedCheck_1729_; 
lean_dec(v_a_1717_);
lean_dec(v_a_1704_);
lean_dec(v_json_1691_);
v_a_1720_ = lean_ctor_get(v___x_1719_, 0);
v_isSharedCheck_1729_ = !lean_is_exclusive(v___x_1719_);
if (v_isSharedCheck_1729_ == 0)
{
v___x_1722_ = v___x_1719_;
v_isShared_1723_ = v_isSharedCheck_1729_;
goto v_resetjp_1721_;
}
else
{
lean_inc(v_a_1720_);
lean_dec(v___x_1719_);
v___x_1722_ = lean_box(0);
v_isShared_1723_ = v_isSharedCheck_1729_;
goto v_resetjp_1721_;
}
v_resetjp_1721_:
{
lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1727_; 
v___x_1724_ = lean_obj_once(&l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__15, &l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__15_once, _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__15);
v___x_1725_ = lean_string_append(v___x_1724_, v_a_1720_);
lean_dec(v_a_1720_);
if (v_isShared_1723_ == 0)
{
lean_ctor_set(v___x_1722_, 0, v___x_1725_);
v___x_1727_ = v___x_1722_;
goto v_reusejp_1726_;
}
else
{
lean_object* v_reuseFailAlloc_1728_; 
v_reuseFailAlloc_1728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1728_, 0, v___x_1725_);
v___x_1727_ = v_reuseFailAlloc_1728_;
goto v_reusejp_1726_;
}
v_reusejp_1726_:
{
return v___x_1727_;
}
}
}
else
{
lean_object* v_a_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; 
v_a_1730_ = lean_ctor_get(v___x_1719_, 0);
lean_inc(v_a_1730_);
lean_dec_ref_known(v___x_1719_, 1);
v___x_1731_ = ((lean_object*)(l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__16));
lean_inc(v_json_1691_);
v___x_1732_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonFuncTable_fromJson_spec__0(v_json_1691_, v___x_1731_);
if (lean_obj_tag(v___x_1732_) == 0)
{
lean_object* v_a_1733_; lean_object* v___x_1735_; uint8_t v_isShared_1736_; uint8_t v_isSharedCheck_1742_; 
lean_dec(v_a_1730_);
lean_dec(v_a_1717_);
lean_dec(v_a_1704_);
lean_dec(v_json_1691_);
v_a_1733_ = lean_ctor_get(v___x_1732_, 0);
v_isSharedCheck_1742_ = !lean_is_exclusive(v___x_1732_);
if (v_isSharedCheck_1742_ == 0)
{
v___x_1735_ = v___x_1732_;
v_isShared_1736_ = v_isSharedCheck_1742_;
goto v_resetjp_1734_;
}
else
{
lean_inc(v_a_1733_);
lean_dec(v___x_1732_);
v___x_1735_ = lean_box(0);
v_isShared_1736_ = v_isSharedCheck_1742_;
goto v_resetjp_1734_;
}
v_resetjp_1734_:
{
lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1740_; 
v___x_1737_ = lean_obj_once(&l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__20, &l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__20_once, _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__20);
v___x_1738_ = lean_string_append(v___x_1737_, v_a_1733_);
lean_dec(v_a_1733_);
if (v_isShared_1736_ == 0)
{
lean_ctor_set(v___x_1735_, 0, v___x_1738_);
v___x_1740_ = v___x_1735_;
goto v_reusejp_1739_;
}
else
{
lean_object* v_reuseFailAlloc_1741_; 
v_reuseFailAlloc_1741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1741_, 0, v___x_1738_);
v___x_1740_ = v_reuseFailAlloc_1741_;
goto v_reusejp_1739_;
}
v_reusejp_1739_:
{
return v___x_1740_;
}
}
}
else
{
lean_object* v_a_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; 
v_a_1743_ = lean_ctor_get(v___x_1732_, 0);
lean_inc(v_a_1743_);
lean_dec_ref_known(v___x_1732_, 1);
v___x_1744_ = ((lean_object*)(l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__21));
lean_inc(v_json_1691_);
v___x_1745_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonStackTable_fromJson_spec__1(v_json_1691_, v___x_1744_);
if (lean_obj_tag(v___x_1745_) == 0)
{
lean_object* v_a_1746_; lean_object* v___x_1748_; uint8_t v_isShared_1749_; uint8_t v_isSharedCheck_1755_; 
lean_dec(v_a_1743_);
lean_dec(v_a_1730_);
lean_dec(v_a_1717_);
lean_dec(v_a_1704_);
lean_dec(v_json_1691_);
v_a_1746_ = lean_ctor_get(v___x_1745_, 0);
v_isSharedCheck_1755_ = !lean_is_exclusive(v___x_1745_);
if (v_isSharedCheck_1755_ == 0)
{
v___x_1748_ = v___x_1745_;
v_isShared_1749_ = v_isSharedCheck_1755_;
goto v_resetjp_1747_;
}
else
{
lean_inc(v_a_1746_);
lean_dec(v___x_1745_);
v___x_1748_ = lean_box(0);
v_isShared_1749_ = v_isSharedCheck_1755_;
goto v_resetjp_1747_;
}
v_resetjp_1747_:
{
lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1753_; 
v___x_1750_ = lean_obj_once(&l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__25, &l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__25_once, _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__25);
v___x_1751_ = lean_string_append(v___x_1750_, v_a_1746_);
lean_dec(v_a_1746_);
if (v_isShared_1749_ == 0)
{
lean_ctor_set(v___x_1748_, 0, v___x_1751_);
v___x_1753_ = v___x_1748_;
goto v_reusejp_1752_;
}
else
{
lean_object* v_reuseFailAlloc_1754_; 
v_reuseFailAlloc_1754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1754_, 0, v___x_1751_);
v___x_1753_ = v_reuseFailAlloc_1754_;
goto v_reusejp_1752_;
}
v_reusejp_1752_:
{
return v___x_1753_;
}
}
}
else
{
lean_object* v_a_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; 
v_a_1756_ = lean_ctor_get(v___x_1745_, 0);
lean_inc(v_a_1756_);
lean_dec_ref_known(v___x_1745_, 1);
v___x_1757_ = ((lean_object*)(l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__26));
lean_inc(v_json_1691_);
v___x_1758_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonStackTable_fromJson_spec__1(v_json_1691_, v___x_1757_);
if (lean_obj_tag(v___x_1758_) == 0)
{
lean_object* v_a_1759_; lean_object* v___x_1761_; uint8_t v_isShared_1762_; uint8_t v_isSharedCheck_1768_; 
lean_dec(v_a_1756_);
lean_dec(v_a_1743_);
lean_dec(v_a_1730_);
lean_dec(v_a_1717_);
lean_dec(v_a_1704_);
lean_dec(v_json_1691_);
v_a_1759_ = lean_ctor_get(v___x_1758_, 0);
v_isSharedCheck_1768_ = !lean_is_exclusive(v___x_1758_);
if (v_isSharedCheck_1768_ == 0)
{
v___x_1761_ = v___x_1758_;
v_isShared_1762_ = v_isSharedCheck_1768_;
goto v_resetjp_1760_;
}
else
{
lean_inc(v_a_1759_);
lean_dec(v___x_1758_);
v___x_1761_ = lean_box(0);
v_isShared_1762_ = v_isSharedCheck_1768_;
goto v_resetjp_1760_;
}
v_resetjp_1760_:
{
lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1766_; 
v___x_1763_ = lean_obj_once(&l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__30, &l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__30_once, _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__30);
v___x_1764_ = lean_string_append(v___x_1763_, v_a_1759_);
lean_dec(v_a_1759_);
if (v_isShared_1762_ == 0)
{
lean_ctor_set(v___x_1761_, 0, v___x_1764_);
v___x_1766_ = v___x_1761_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v___x_1764_);
v___x_1766_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
return v___x_1766_;
}
}
}
else
{
lean_object* v_a_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; 
v_a_1769_ = lean_ctor_get(v___x_1758_, 0);
lean_inc(v_a_1769_);
lean_dec_ref_known(v___x_1758_, 1);
v___x_1770_ = ((lean_object*)(l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__31));
lean_inc(v_json_1691_);
v___x_1771_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonStackTable_fromJson_spec__1(v_json_1691_, v___x_1770_);
if (lean_obj_tag(v___x_1771_) == 0)
{
lean_object* v_a_1772_; lean_object* v___x_1774_; uint8_t v_isShared_1775_; uint8_t v_isSharedCheck_1781_; 
lean_dec(v_a_1769_);
lean_dec(v_a_1756_);
lean_dec(v_a_1743_);
lean_dec(v_a_1730_);
lean_dec(v_a_1717_);
lean_dec(v_a_1704_);
lean_dec(v_json_1691_);
v_a_1772_ = lean_ctor_get(v___x_1771_, 0);
v_isSharedCheck_1781_ = !lean_is_exclusive(v___x_1771_);
if (v_isSharedCheck_1781_ == 0)
{
v___x_1774_ = v___x_1771_;
v_isShared_1775_ = v_isSharedCheck_1781_;
goto v_resetjp_1773_;
}
else
{
lean_inc(v_a_1772_);
lean_dec(v___x_1771_);
v___x_1774_ = lean_box(0);
v_isShared_1775_ = v_isSharedCheck_1781_;
goto v_resetjp_1773_;
}
v_resetjp_1773_:
{
lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1779_; 
v___x_1776_ = lean_obj_once(&l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__35, &l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__35_once, _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__35);
v___x_1777_ = lean_string_append(v___x_1776_, v_a_1772_);
lean_dec(v_a_1772_);
if (v_isShared_1775_ == 0)
{
lean_ctor_set(v___x_1774_, 0, v___x_1777_);
v___x_1779_ = v___x_1774_;
goto v_reusejp_1778_;
}
else
{
lean_object* v_reuseFailAlloc_1780_; 
v_reuseFailAlloc_1780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1780_, 0, v___x_1777_);
v___x_1779_ = v_reuseFailAlloc_1780_;
goto v_reusejp_1778_;
}
v_reusejp_1778_:
{
return v___x_1779_;
}
}
}
else
{
lean_object* v_a_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; 
v_a_1782_ = lean_ctor_get(v___x_1771_, 0);
lean_inc(v_a_1782_);
lean_dec_ref_known(v___x_1771_, 1);
v___x_1783_ = ((lean_object*)(l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__24));
v___x_1784_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__2(v_json_1691_, v___x_1783_);
if (lean_obj_tag(v___x_1784_) == 0)
{
lean_object* v_a_1785_; lean_object* v___x_1787_; uint8_t v_isShared_1788_; uint8_t v_isSharedCheck_1794_; 
lean_dec(v_a_1782_);
lean_dec(v_a_1769_);
lean_dec(v_a_1756_);
lean_dec(v_a_1743_);
lean_dec(v_a_1730_);
lean_dec(v_a_1717_);
lean_dec(v_a_1704_);
v_a_1785_ = lean_ctor_get(v___x_1784_, 0);
v_isSharedCheck_1794_ = !lean_is_exclusive(v___x_1784_);
if (v_isSharedCheck_1794_ == 0)
{
v___x_1787_ = v___x_1784_;
v_isShared_1788_ = v_isSharedCheck_1794_;
goto v_resetjp_1786_;
}
else
{
lean_inc(v_a_1785_);
lean_dec(v___x_1784_);
v___x_1787_ = lean_box(0);
v_isShared_1788_ = v_isSharedCheck_1794_;
goto v_resetjp_1786_;
}
v_resetjp_1786_:
{
lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1792_; 
v___x_1789_ = lean_obj_once(&l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__37, &l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__37_once, _init_l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__37);
v___x_1790_ = lean_string_append(v___x_1789_, v_a_1785_);
lean_dec(v_a_1785_);
if (v_isShared_1788_ == 0)
{
lean_ctor_set(v___x_1787_, 0, v___x_1790_);
v___x_1792_ = v___x_1787_;
goto v_reusejp_1791_;
}
else
{
lean_object* v_reuseFailAlloc_1793_; 
v_reuseFailAlloc_1793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1793_, 0, v___x_1790_);
v___x_1792_ = v_reuseFailAlloc_1793_;
goto v_reusejp_1791_;
}
v_reusejp_1791_:
{
return v___x_1792_;
}
}
}
else
{
lean_object* v_a_1795_; lean_object* v___x_1797_; uint8_t v_isShared_1798_; uint8_t v_isSharedCheck_1803_; 
v_a_1795_ = lean_ctor_get(v___x_1784_, 0);
v_isSharedCheck_1803_ = !lean_is_exclusive(v___x_1784_);
if (v_isSharedCheck_1803_ == 0)
{
v___x_1797_ = v___x_1784_;
v_isShared_1798_ = v_isSharedCheck_1803_;
goto v_resetjp_1796_;
}
else
{
lean_inc(v_a_1795_);
lean_dec(v___x_1784_);
v___x_1797_ = lean_box(0);
v_isShared_1798_ = v_isSharedCheck_1803_;
goto v_resetjp_1796_;
}
v_resetjp_1796_:
{
lean_object* v___x_1799_; lean_object* v___x_1801_; 
v___x_1799_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1799_, 0, v_a_1704_);
lean_ctor_set(v___x_1799_, 1, v_a_1717_);
lean_ctor_set(v___x_1799_, 2, v_a_1730_);
lean_ctor_set(v___x_1799_, 3, v_a_1743_);
lean_ctor_set(v___x_1799_, 4, v_a_1756_);
lean_ctor_set(v___x_1799_, 5, v_a_1769_);
lean_ctor_set(v___x_1799_, 6, v_a_1782_);
lean_ctor_set(v___x_1799_, 7, v_a_1795_);
if (v_isShared_1798_ == 0)
{
lean_ctor_set(v___x_1797_, 0, v___x_1799_);
v___x_1801_ = v___x_1797_;
goto v_reusejp_1800_;
}
else
{
lean_object* v_reuseFailAlloc_1802_; 
v_reuseFailAlloc_1802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1802_, 0, v___x_1799_);
v___x_1801_ = v_reuseFailAlloc_1802_;
goto v_reusejp_1800_;
}
v_reusejp_1800_:
{
return v___x_1801_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Firefox_instToJsonFuncTable_toJson_spec__0_spec__0(size_t v_sz_1806_, size_t v_i_1807_, lean_object* v_bs_1808_){
_start:
{
uint8_t v___x_1809_; 
v___x_1809_ = lean_usize_dec_lt(v_i_1807_, v_sz_1806_);
if (v___x_1809_ == 0)
{
return v_bs_1808_;
}
else
{
lean_object* v_v_1810_; lean_object* v___x_1811_; lean_object* v_bs_x27_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; size_t v___x_1815_; size_t v___x_1816_; lean_object* v___x_1817_; 
v_v_1810_ = lean_array_uget(v_bs_1808_, v_i_1807_);
v___x_1811_ = lean_unsigned_to_nat(0u);
v_bs_x27_1812_ = lean_array_uset(v_bs_1808_, v_i_1807_, v___x_1811_);
v___x_1813_ = l_Lean_JsonNumber_fromInt(v_v_1810_);
v___x_1814_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1814_, 0, v___x_1813_);
v___x_1815_ = ((size_t)1ULL);
v___x_1816_ = lean_usize_add(v_i_1807_, v___x_1815_);
v___x_1817_ = lean_array_uset(v_bs_x27_1812_, v_i_1807_, v___x_1814_);
v_i_1807_ = v___x_1816_;
v_bs_1808_ = v___x_1817_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Firefox_instToJsonFuncTable_toJson_spec__0_spec__0___boxed(lean_object* v_sz_1819_, lean_object* v_i_1820_, lean_object* v_bs_1821_){
_start:
{
size_t v_sz_boxed_1822_; size_t v_i_boxed_1823_; lean_object* v_res_1824_; 
v_sz_boxed_1822_ = lean_unbox_usize(v_sz_1819_);
lean_dec(v_sz_1819_);
v_i_boxed_1823_ = lean_unbox_usize(v_i_1820_);
lean_dec(v_i_1820_);
v_res_1824_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Firefox_instToJsonFuncTable_toJson_spec__0_spec__0(v_sz_boxed_1822_, v_i_boxed_1823_, v_bs_1821_);
return v_res_1824_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Firefox_instToJsonFuncTable_toJson_spec__0(lean_object* v_a_1825_){
_start:
{
size_t v_sz_1826_; size_t v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; 
v_sz_1826_ = lean_array_size(v_a_1825_);
v___x_1827_ = ((size_t)0ULL);
v___x_1828_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Firefox_instToJsonFuncTable_toJson_spec__0_spec__0(v_sz_1826_, v___x_1827_, v_a_1825_);
v___x_1829_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1829_, 0, v___x_1828_);
return v___x_1829_;
}
}
LEAN_EXPORT lean_object* l_Lean_Firefox_instToJsonFuncTable_toJson(lean_object* v_x_1830_){
_start:
{
lean_object* v_name_1831_; lean_object* v_isJS_1832_; lean_object* v_relevantForJS_1833_; lean_object* v_resource_1834_; lean_object* v_fileName_1835_; lean_object* v_lineNumber_1836_; lean_object* v_columnNumber_1837_; lean_object* v_length_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; 
v_name_1831_ = lean_ctor_get(v_x_1830_, 0);
lean_inc_ref(v_name_1831_);
v_isJS_1832_ = lean_ctor_get(v_x_1830_, 1);
lean_inc_ref(v_isJS_1832_);
v_relevantForJS_1833_ = lean_ctor_get(v_x_1830_, 2);
lean_inc_ref(v_relevantForJS_1833_);
v_resource_1834_ = lean_ctor_get(v_x_1830_, 3);
lean_inc_ref(v_resource_1834_);
v_fileName_1835_ = lean_ctor_get(v_x_1830_, 4);
lean_inc_ref(v_fileName_1835_);
v_lineNumber_1836_ = lean_ctor_get(v_x_1830_, 5);
lean_inc_ref(v_lineNumber_1836_);
v_columnNumber_1837_ = lean_ctor_get(v_x_1830_, 6);
lean_inc_ref(v_columnNumber_1837_);
v_length_1838_ = lean_ctor_get(v_x_1830_, 7);
lean_inc(v_length_1838_);
lean_dec_ref(v_x_1830_);
v___x_1839_ = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__0));
v___x_1840_ = l_Lean_Array_toJson___at___00Lean_Firefox_instToJsonStackTable_toJson_spec__0(v_name_1831_);
v___x_1841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1841_, 0, v___x_1839_);
lean_ctor_set(v___x_1841_, 1, v___x_1840_);
v___x_1842_ = lean_box(0);
v___x_1843_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1843_, 0, v___x_1841_);
lean_ctor_set(v___x_1843_, 1, v___x_1842_);
v___x_1844_ = ((lean_object*)(l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__6));
v___x_1845_ = l_Lean_Array_toJson___at___00Lean_Firefox_instToJsonProfileMeta_toJson_spec__1(v_isJS_1832_);
v___x_1846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1846_, 0, v___x_1844_);
lean_ctor_set(v___x_1846_, 1, v___x_1845_);
v___x_1847_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1847_, 0, v___x_1846_);
lean_ctor_set(v___x_1847_, 1, v___x_1842_);
v___x_1848_ = ((lean_object*)(l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__11));
v___x_1849_ = l_Lean_Array_toJson___at___00Lean_Firefox_instToJsonProfileMeta_toJson_spec__1(v_relevantForJS_1833_);
v___x_1850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1850_, 0, v___x_1848_);
lean_ctor_set(v___x_1850_, 1, v___x_1849_);
v___x_1851_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1851_, 0, v___x_1850_);
lean_ctor_set(v___x_1851_, 1, v___x_1842_);
v___x_1852_ = ((lean_object*)(l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__16));
v___x_1853_ = l_Lean_Array_toJson___at___00Lean_Firefox_instToJsonFuncTable_toJson_spec__0(v_resource_1834_);
v___x_1854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1854_, 0, v___x_1852_);
lean_ctor_set(v___x_1854_, 1, v___x_1853_);
v___x_1855_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1855_, 0, v___x_1854_);
lean_ctor_set(v___x_1855_, 1, v___x_1842_);
v___x_1856_ = ((lean_object*)(l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__21));
v___x_1857_ = l_Lean_Array_toJson___at___00Lean_Firefox_instToJsonStackTable_toJson_spec__1(v_fileName_1835_);
v___x_1858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1858_, 0, v___x_1856_);
lean_ctor_set(v___x_1858_, 1, v___x_1857_);
v___x_1859_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1859_, 0, v___x_1858_);
lean_ctor_set(v___x_1859_, 1, v___x_1842_);
v___x_1860_ = ((lean_object*)(l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__26));
v___x_1861_ = l_Lean_Array_toJson___at___00Lean_Firefox_instToJsonStackTable_toJson_spec__1(v_lineNumber_1836_);
v___x_1862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1862_, 0, v___x_1860_);
lean_ctor_set(v___x_1862_, 1, v___x_1861_);
v___x_1863_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1863_, 0, v___x_1862_);
lean_ctor_set(v___x_1863_, 1, v___x_1842_);
v___x_1864_ = ((lean_object*)(l_Lean_Firefox_instFromJsonFuncTable_fromJson___closed__31));
v___x_1865_ = l_Lean_Array_toJson___at___00Lean_Firefox_instToJsonStackTable_toJson_spec__1(v_columnNumber_1837_);
v___x_1866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1866_, 0, v___x_1864_);
lean_ctor_set(v___x_1866_, 1, v___x_1865_);
v___x_1867_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1867_, 0, v___x_1866_);
lean_ctor_set(v___x_1867_, 1, v___x_1842_);
v___x_1868_ = ((lean_object*)(l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__24));
v___x_1869_ = l_Lean_JsonNumber_fromNat(v_length_1838_);
v___x_1870_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1870_, 0, v___x_1869_);
v___x_1871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1871_, 0, v___x_1868_);
lean_ctor_set(v___x_1871_, 1, v___x_1870_);
v___x_1872_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1872_, 0, v___x_1871_);
lean_ctor_set(v___x_1872_, 1, v___x_1842_);
v___x_1873_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1873_, 0, v___x_1872_);
lean_ctor_set(v___x_1873_, 1, v___x_1842_);
v___x_1874_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1874_, 0, v___x_1867_);
lean_ctor_set(v___x_1874_, 1, v___x_1873_);
v___x_1875_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1875_, 0, v___x_1863_);
lean_ctor_set(v___x_1875_, 1, v___x_1874_);
v___x_1876_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1876_, 0, v___x_1859_);
lean_ctor_set(v___x_1876_, 1, v___x_1875_);
v___x_1877_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1877_, 0, v___x_1855_);
lean_ctor_set(v___x_1877_, 1, v___x_1876_);
v___x_1878_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1878_, 0, v___x_1851_);
lean_ctor_set(v___x_1878_, 1, v___x_1877_);
v___x_1879_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1879_, 0, v___x_1847_);
lean_ctor_set(v___x_1879_, 1, v___x_1878_);
v___x_1880_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1880_, 0, v___x_1843_);
lean_ctor_set(v___x_1880_, 1, v___x_1879_);
v___x_1881_ = ((lean_object*)(l_Lean_Firefox_instToJsonCategory_toJson___closed__0));
v___x_1882_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Firefox_instToJsonCategory_toJson_spec__1(v___x_1880_, v___x_1881_);
v___x_1883_ = l_Lean_Json_mkObj(v___x_1882_);
lean_dec(v___x_1882_);
return v___x_1883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonFrameTable_fromJson_spec__0_spec__0_spec__1(lean_object* v_x_1888_){
_start:
{
if (lean_obj_tag(v_x_1888_) == 0)
{
lean_object* v___x_1889_; 
v___x_1889_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonFrameTable_fromJson_spec__0_spec__0_spec__1___closed__0));
return v___x_1889_;
}
else
{
lean_object* v___x_1890_; lean_object* v___x_1891_; 
v___x_1890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1890_, 0, v_x_1888_);
v___x_1891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1891_, 0, v___x_1890_);
return v___x_1891_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonFrameTable_fromJson_spec__0_spec__0_spec__2(size_t v_sz_1892_, size_t v_i_1893_, lean_object* v_bs_1894_){
_start:
{
uint8_t v___x_1895_; 
v___x_1895_ = lean_usize_dec_lt(v_i_1893_, v_sz_1892_);
if (v___x_1895_ == 0)
{
lean_object* v___x_1896_; 
v___x_1896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1896_, 0, v_bs_1894_);
return v___x_1896_;
}
else
{
lean_object* v_v_1897_; lean_object* v___x_1898_; 
v_v_1897_ = lean_array_uget_borrowed(v_bs_1894_, v_i_1893_);
lean_inc(v_v_1897_);
v___x_1898_ = l_Lean_Option_fromJson_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonFrameTable_fromJson_spec__0_spec__0_spec__1(v_v_1897_);
if (lean_obj_tag(v___x_1898_) == 0)
{
lean_object* v_a_1899_; lean_object* v___x_1901_; uint8_t v_isShared_1902_; uint8_t v_isSharedCheck_1906_; 
lean_dec_ref(v_bs_1894_);
v_a_1899_ = lean_ctor_get(v___x_1898_, 0);
v_isSharedCheck_1906_ = !lean_is_exclusive(v___x_1898_);
if (v_isSharedCheck_1906_ == 0)
{
v___x_1901_ = v___x_1898_;
v_isShared_1902_ = v_isSharedCheck_1906_;
goto v_resetjp_1900_;
}
else
{
lean_inc(v_a_1899_);
lean_dec(v___x_1898_);
v___x_1901_ = lean_box(0);
v_isShared_1902_ = v_isSharedCheck_1906_;
goto v_resetjp_1900_;
}
v_resetjp_1900_:
{
lean_object* v___x_1904_; 
if (v_isShared_1902_ == 0)
{
v___x_1904_ = v___x_1901_;
goto v_reusejp_1903_;
}
else
{
lean_object* v_reuseFailAlloc_1905_; 
v_reuseFailAlloc_1905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1905_, 0, v_a_1899_);
v___x_1904_ = v_reuseFailAlloc_1905_;
goto v_reusejp_1903_;
}
v_reusejp_1903_:
{
return v___x_1904_;
}
}
}
else
{
lean_object* v_a_1907_; lean_object* v___x_1908_; lean_object* v_bs_x27_1909_; size_t v___x_1910_; size_t v___x_1911_; lean_object* v___x_1912_; 
v_a_1907_ = lean_ctor_get(v___x_1898_, 0);
lean_inc(v_a_1907_);
lean_dec_ref_known(v___x_1898_, 1);
v___x_1908_ = lean_unsigned_to_nat(0u);
v_bs_x27_1909_ = lean_array_uset(v_bs_1894_, v_i_1893_, v___x_1908_);
v___x_1910_ = ((size_t)1ULL);
v___x_1911_ = lean_usize_add(v_i_1893_, v___x_1910_);
v___x_1912_ = lean_array_uset(v_bs_x27_1909_, v_i_1893_, v_a_1907_);
v_i_1893_ = v___x_1911_;
v_bs_1894_ = v___x_1912_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonFrameTable_fromJson_spec__0_spec__0_spec__2___boxed(lean_object* v_sz_1914_, lean_object* v_i_1915_, lean_object* v_bs_1916_){
_start:
{
size_t v_sz_boxed_1917_; size_t v_i_boxed_1918_; lean_object* v_res_1919_; 
v_sz_boxed_1917_ = lean_unbox_usize(v_sz_1914_);
lean_dec(v_sz_1914_);
v_i_boxed_1918_ = lean_unbox_usize(v_i_1915_);
lean_dec(v_i_1915_);
v_res_1919_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonFrameTable_fromJson_spec__0_spec__0_spec__2(v_sz_boxed_1917_, v_i_boxed_1918_, v_bs_1916_);
return v_res_1919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonFrameTable_fromJson_spec__0_spec__0(lean_object* v_x_1920_){
_start:
{
if (lean_obj_tag(v_x_1920_) == 4)
{
lean_object* v_elems_1921_; size_t v_sz_1922_; size_t v___x_1923_; lean_object* v___x_1924_; 
v_elems_1921_ = lean_ctor_get(v_x_1920_, 0);
lean_inc_ref(v_elems_1921_);
lean_dec_ref_known(v_x_1920_, 1);
v_sz_1922_ = lean_array_size(v_elems_1921_);
v___x_1923_ = ((size_t)0ULL);
v___x_1924_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonFrameTable_fromJson_spec__0_spec__0_spec__2(v_sz_1922_, v___x_1923_, v_elems_1921_);
return v___x_1924_;
}
else
{
lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; 
v___x_1925_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__2_spec__2___closed__0));
v___x_1926_ = lean_unsigned_to_nat(80u);
v___x_1927_ = l_Lean_Json_pretty(v_x_1920_, v___x_1926_);
v___x_1928_ = lean_string_append(v___x_1925_, v___x_1927_);
lean_dec_ref(v___x_1927_);
v___x_1929_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__2_spec__2___closed__1));
v___x_1930_ = lean_string_append(v___x_1928_, v___x_1929_);
v___x_1931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1931_, 0, v___x_1930_);
return v___x_1931_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonFrameTable_fromJson_spec__0(lean_object* v_j_1932_, lean_object* v_k_1933_){
_start:
{
lean_object* v___x_1934_; lean_object* v___x_1935_; 
v___x_1934_ = l_Lean_Json_getObjValD(v_j_1932_, v_k_1933_);
v___x_1935_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonFrameTable_fromJson_spec__0_spec__0(v___x_1934_);
return v___x_1935_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonFrameTable_fromJson_spec__0___boxed(lean_object* v_j_1936_, lean_object* v_k_1937_){
_start:
{
lean_object* v_res_1938_; 
v_res_1938_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonFrameTable_fromJson_spec__0(v_j_1936_, v_k_1937_);
lean_dec_ref(v_k_1937_);
return v_res_1938_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__3(void){
_start:
{
uint8_t v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; 
v___x_1945_ = 1;
v___x_1946_ = ((lean_object*)(l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__2));
v___x_1947_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1946_, v___x_1945_);
return v___x_1947_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__4(void){
_start:
{
lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; 
v___x_1948_ = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__6));
v___x_1949_ = lean_obj_once(&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__3, &l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__3_once, _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__3);
v___x_1950_ = lean_string_append(v___x_1949_, v___x_1948_);
return v___x_1950_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__6(void){
_start:
{
uint8_t v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; 
v___x_1953_ = 1;
v___x_1954_ = ((lean_object*)(l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__5));
v___x_1955_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1954_, v___x_1953_);
return v___x_1955_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__7(void){
_start:
{
lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; 
v___x_1956_ = lean_obj_once(&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__6, &l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__6_once, _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__6);
v___x_1957_ = lean_obj_once(&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__4, &l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__4_once, _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__4);
v___x_1958_ = lean_string_append(v___x_1957_, v___x_1956_);
return v___x_1958_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__8(void){
_start:
{
lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; 
v___x_1959_ = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
v___x_1960_ = lean_obj_once(&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__7, &l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__7_once, _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__7);
v___x_1961_ = lean_string_append(v___x_1960_, v___x_1959_);
return v___x_1961_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__11(void){
_start:
{
uint8_t v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; 
v___x_1965_ = 1;
v___x_1966_ = ((lean_object*)(l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__10));
v___x_1967_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1966_, v___x_1965_);
return v___x_1967_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__12(void){
_start:
{
lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; 
v___x_1968_ = lean_obj_once(&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__11, &l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__11_once, _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__11);
v___x_1969_ = lean_obj_once(&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__4, &l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__4_once, _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__4);
v___x_1970_ = lean_string_append(v___x_1969_, v___x_1968_);
return v___x_1970_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__13(void){
_start:
{
lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; 
v___x_1971_ = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
v___x_1972_ = lean_obj_once(&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__12, &l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__12_once, _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__12);
v___x_1973_ = lean_string_append(v___x_1972_, v___x_1971_);
return v___x_1973_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__14(void){
_start:
{
lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; 
v___x_1974_ = lean_obj_once(&l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__11, &l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__11_once, _init_l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__11);
v___x_1975_ = lean_obj_once(&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__4, &l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__4_once, _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__4);
v___x_1976_ = lean_string_append(v___x_1975_, v___x_1974_);
return v___x_1976_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__15(void){
_start:
{
lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; 
v___x_1977_ = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
v___x_1978_ = lean_obj_once(&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__14, &l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__14_once, _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__14);
v___x_1979_ = lean_string_append(v___x_1978_, v___x_1977_);
return v___x_1979_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__16(void){
_start:
{
lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; 
v___x_1980_ = lean_obj_once(&l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__16, &l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__16_once, _init_l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__16);
v___x_1981_ = lean_obj_once(&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__4, &l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__4_once, _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__4);
v___x_1982_ = lean_string_append(v___x_1981_, v___x_1980_);
return v___x_1982_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__17(void){
_start:
{
lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; 
v___x_1983_ = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
v___x_1984_ = lean_obj_once(&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__16, &l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__16_once, _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__16);
v___x_1985_ = lean_string_append(v___x_1984_, v___x_1983_);
return v___x_1985_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__20(void){
_start:
{
uint8_t v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; 
v___x_1989_ = 1;
v___x_1990_ = ((lean_object*)(l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__19));
v___x_1991_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1990_, v___x_1989_);
return v___x_1991_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__21(void){
_start:
{
lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; 
v___x_1992_ = lean_obj_once(&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__20, &l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__20_once, _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__20);
v___x_1993_ = lean_obj_once(&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__4, &l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__4_once, _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__4);
v___x_1994_ = lean_string_append(v___x_1993_, v___x_1992_);
return v___x_1994_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__22(void){
_start:
{
lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; 
v___x_1995_ = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
v___x_1996_ = lean_obj_once(&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__21, &l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__21_once, _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__21);
v___x_1997_ = lean_string_append(v___x_1996_, v___x_1995_);
return v___x_1997_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__25(void){
_start:
{
uint8_t v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; 
v___x_2001_ = 1;
v___x_2002_ = ((lean_object*)(l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__24));
v___x_2003_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2002_, v___x_2001_);
return v___x_2003_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__26(void){
_start:
{
lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; 
v___x_2004_ = lean_obj_once(&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__25, &l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__25_once, _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__25);
v___x_2005_ = lean_obj_once(&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__4, &l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__4_once, _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__4);
v___x_2006_ = lean_string_append(v___x_2005_, v___x_2004_);
return v___x_2006_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__27(void){
_start:
{
lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; 
v___x_2007_ = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
v___x_2008_ = lean_obj_once(&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__26, &l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__26_once, _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__26);
v___x_2009_ = lean_string_append(v___x_2008_, v___x_2007_);
return v___x_2009_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__30(void){
_start:
{
uint8_t v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; 
v___x_2013_ = 1;
v___x_2014_ = ((lean_object*)(l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__29));
v___x_2015_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2014_, v___x_2013_);
return v___x_2015_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__31(void){
_start:
{
lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; 
v___x_2016_ = lean_obj_once(&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__30, &l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__30_once, _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__30);
v___x_2017_ = lean_obj_once(&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__4, &l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__4_once, _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__4);
v___x_2018_ = lean_string_append(v___x_2017_, v___x_2016_);
return v___x_2018_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__32(void){
_start:
{
lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; 
v___x_2019_ = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
v___x_2020_ = lean_obj_once(&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__31, &l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__31_once, _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__31);
v___x_2021_ = lean_string_append(v___x_2020_, v___x_2019_);
return v___x_2021_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__35(void){
_start:
{
uint8_t v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; 
v___x_2025_ = 1;
v___x_2026_ = ((lean_object*)(l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__34));
v___x_2027_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2026_, v___x_2025_);
return v___x_2027_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__36(void){
_start:
{
lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; 
v___x_2028_ = lean_obj_once(&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__35, &l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__35_once, _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__35);
v___x_2029_ = lean_obj_once(&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__4, &l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__4_once, _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__4);
v___x_2030_ = lean_string_append(v___x_2029_, v___x_2028_);
return v___x_2030_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__37(void){
_start:
{
lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; 
v___x_2031_ = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
v___x_2032_ = lean_obj_once(&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__36, &l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__36_once, _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__36);
v___x_2033_ = lean_string_append(v___x_2032_, v___x_2031_);
return v___x_2033_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__40(void){
_start:
{
uint8_t v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; 
v___x_2037_ = 1;
v___x_2038_ = ((lean_object*)(l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__39));
v___x_2039_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2038_, v___x_2037_);
return v___x_2039_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__41(void){
_start:
{
lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; 
v___x_2040_ = lean_obj_once(&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__40, &l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__40_once, _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__40);
v___x_2041_ = lean_obj_once(&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__4, &l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__4_once, _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__4);
v___x_2042_ = lean_string_append(v___x_2041_, v___x_2040_);
return v___x_2042_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__42(void){
_start:
{
lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; 
v___x_2043_ = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
v___x_2044_ = lean_obj_once(&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__41, &l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__41_once, _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__41);
v___x_2045_ = lean_string_append(v___x_2044_, v___x_2043_);
return v___x_2045_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__45(void){
_start:
{
uint8_t v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; 
v___x_2049_ = 1;
v___x_2050_ = ((lean_object*)(l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__44));
v___x_2051_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2050_, v___x_2049_);
return v___x_2051_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__46(void){
_start:
{
lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; 
v___x_2052_ = lean_obj_once(&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__45, &l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__45_once, _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__45);
v___x_2053_ = lean_obj_once(&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__4, &l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__4_once, _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__4);
v___x_2054_ = lean_string_append(v___x_2053_, v___x_2052_);
return v___x_2054_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__47(void){
_start:
{
lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; 
v___x_2055_ = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
v___x_2056_ = lean_obj_once(&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__46, &l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__46_once, _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__46);
v___x_2057_ = lean_string_append(v___x_2056_, v___x_2055_);
return v___x_2057_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__48(void){
_start:
{
lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; 
v___x_2058_ = lean_obj_once(&l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__26, &l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__26_once, _init_l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__26);
v___x_2059_ = lean_obj_once(&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__4, &l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__4_once, _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__4);
v___x_2060_ = lean_string_append(v___x_2059_, v___x_2058_);
return v___x_2060_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__49(void){
_start:
{
lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; 
v___x_2061_ = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
v___x_2062_ = lean_obj_once(&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__48, &l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__48_once, _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__48);
v___x_2063_ = lean_string_append(v___x_2062_, v___x_2061_);
return v___x_2063_;
}
}
LEAN_EXPORT lean_object* l_Lean_Firefox_instFromJsonFrameTable_fromJson(lean_object* v_json_2064_){
_start:
{
lean_object* v___x_2065_; lean_object* v___x_2066_; 
v___x_2065_ = ((lean_object*)(l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__0));
lean_inc(v_json_2064_);
v___x_2066_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonFuncTable_fromJson_spec__0(v_json_2064_, v___x_2065_);
if (lean_obj_tag(v___x_2066_) == 0)
{
lean_object* v_a_2067_; lean_object* v___x_2069_; uint8_t v_isShared_2070_; uint8_t v_isSharedCheck_2076_; 
lean_dec(v_json_2064_);
v_a_2067_ = lean_ctor_get(v___x_2066_, 0);
v_isSharedCheck_2076_ = !lean_is_exclusive(v___x_2066_);
if (v_isSharedCheck_2076_ == 0)
{
v___x_2069_ = v___x_2066_;
v_isShared_2070_ = v_isSharedCheck_2076_;
goto v_resetjp_2068_;
}
else
{
lean_inc(v_a_2067_);
lean_dec(v___x_2066_);
v___x_2069_ = lean_box(0);
v_isShared_2070_ = v_isSharedCheck_2076_;
goto v_resetjp_2068_;
}
v_resetjp_2068_:
{
lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2074_; 
v___x_2071_ = lean_obj_once(&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__8, &l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__8_once, _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__8);
v___x_2072_ = lean_string_append(v___x_2071_, v_a_2067_);
lean_dec(v_a_2067_);
if (v_isShared_2070_ == 0)
{
lean_ctor_set(v___x_2069_, 0, v___x_2072_);
v___x_2074_ = v___x_2069_;
goto v_reusejp_2073_;
}
else
{
lean_object* v_reuseFailAlloc_2075_; 
v_reuseFailAlloc_2075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2075_, 0, v___x_2072_);
v___x_2074_ = v_reuseFailAlloc_2075_;
goto v_reusejp_2073_;
}
v_reusejp_2073_:
{
return v___x_2074_;
}
}
}
else
{
lean_object* v_a_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; 
v_a_2077_ = lean_ctor_get(v___x_2066_, 0);
lean_inc(v_a_2077_);
lean_dec_ref_known(v___x_2066_, 1);
v___x_2078_ = ((lean_object*)(l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__9));
lean_inc(v_json_2064_);
v___x_2079_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonStackTable_fromJson_spec__0(v_json_2064_, v___x_2078_);
if (lean_obj_tag(v___x_2079_) == 0)
{
lean_object* v_a_2080_; lean_object* v___x_2082_; uint8_t v_isShared_2083_; uint8_t v_isSharedCheck_2089_; 
lean_dec(v_a_2077_);
lean_dec(v_json_2064_);
v_a_2080_ = lean_ctor_get(v___x_2079_, 0);
v_isSharedCheck_2089_ = !lean_is_exclusive(v___x_2079_);
if (v_isSharedCheck_2089_ == 0)
{
v___x_2082_ = v___x_2079_;
v_isShared_2083_ = v_isSharedCheck_2089_;
goto v_resetjp_2081_;
}
else
{
lean_inc(v_a_2080_);
lean_dec(v___x_2079_);
v___x_2082_ = lean_box(0);
v_isShared_2083_ = v_isSharedCheck_2089_;
goto v_resetjp_2081_;
}
v_resetjp_2081_:
{
lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2087_; 
v___x_2084_ = lean_obj_once(&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__13, &l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__13_once, _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__13);
v___x_2085_ = lean_string_append(v___x_2084_, v_a_2080_);
lean_dec(v_a_2080_);
if (v_isShared_2083_ == 0)
{
lean_ctor_set(v___x_2082_, 0, v___x_2085_);
v___x_2087_ = v___x_2082_;
goto v_reusejp_2086_;
}
else
{
lean_object* v_reuseFailAlloc_2088_; 
v_reuseFailAlloc_2088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2088_, 0, v___x_2085_);
v___x_2087_ = v_reuseFailAlloc_2088_;
goto v_reusejp_2086_;
}
v_reusejp_2086_:
{
return v___x_2087_;
}
}
}
else
{
lean_object* v_a_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; 
v_a_2090_ = lean_ctor_get(v___x_2079_, 0);
lean_inc(v_a_2090_);
lean_dec_ref_known(v___x_2079_, 1);
v___x_2091_ = ((lean_object*)(l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__9));
lean_inc(v_json_2064_);
v___x_2092_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonStackTable_fromJson_spec__1(v_json_2064_, v___x_2091_);
if (lean_obj_tag(v___x_2092_) == 0)
{
lean_object* v_a_2093_; lean_object* v___x_2095_; uint8_t v_isShared_2096_; uint8_t v_isSharedCheck_2102_; 
lean_dec(v_a_2090_);
lean_dec(v_a_2077_);
lean_dec(v_json_2064_);
v_a_2093_ = lean_ctor_get(v___x_2092_, 0);
v_isSharedCheck_2102_ = !lean_is_exclusive(v___x_2092_);
if (v_isSharedCheck_2102_ == 0)
{
v___x_2095_ = v___x_2092_;
v_isShared_2096_ = v_isSharedCheck_2102_;
goto v_resetjp_2094_;
}
else
{
lean_inc(v_a_2093_);
lean_dec(v___x_2092_);
v___x_2095_ = lean_box(0);
v_isShared_2096_ = v_isSharedCheck_2102_;
goto v_resetjp_2094_;
}
v_resetjp_2094_:
{
lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2100_; 
v___x_2097_ = lean_obj_once(&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__15, &l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__15_once, _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__15);
v___x_2098_ = lean_string_append(v___x_2097_, v_a_2093_);
lean_dec(v_a_2093_);
if (v_isShared_2096_ == 0)
{
lean_ctor_set(v___x_2095_, 0, v___x_2098_);
v___x_2100_ = v___x_2095_;
goto v_reusejp_2099_;
}
else
{
lean_object* v_reuseFailAlloc_2101_; 
v_reuseFailAlloc_2101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2101_, 0, v___x_2098_);
v___x_2100_ = v_reuseFailAlloc_2101_;
goto v_reusejp_2099_;
}
v_reusejp_2099_:
{
return v___x_2100_;
}
}
}
else
{
lean_object* v_a_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; 
v_a_2103_ = lean_ctor_get(v___x_2092_, 0);
lean_inc(v_a_2103_);
lean_dec_ref_known(v___x_2092_, 1);
v___x_2104_ = ((lean_object*)(l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__14));
lean_inc(v_json_2064_);
v___x_2105_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonStackTable_fromJson_spec__1(v_json_2064_, v___x_2104_);
if (lean_obj_tag(v___x_2105_) == 0)
{
lean_object* v_a_2106_; lean_object* v___x_2108_; uint8_t v_isShared_2109_; uint8_t v_isSharedCheck_2115_; 
lean_dec(v_a_2103_);
lean_dec(v_a_2090_);
lean_dec(v_a_2077_);
lean_dec(v_json_2064_);
v_a_2106_ = lean_ctor_get(v___x_2105_, 0);
v_isSharedCheck_2115_ = !lean_is_exclusive(v___x_2105_);
if (v_isSharedCheck_2115_ == 0)
{
v___x_2108_ = v___x_2105_;
v_isShared_2109_ = v_isSharedCheck_2115_;
goto v_resetjp_2107_;
}
else
{
lean_inc(v_a_2106_);
lean_dec(v___x_2105_);
v___x_2108_ = lean_box(0);
v_isShared_2109_ = v_isSharedCheck_2115_;
goto v_resetjp_2107_;
}
v_resetjp_2107_:
{
lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2113_; 
v___x_2110_ = lean_obj_once(&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__17, &l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__17_once, _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__17);
v___x_2111_ = lean_string_append(v___x_2110_, v_a_2106_);
lean_dec(v_a_2106_);
if (v_isShared_2109_ == 0)
{
lean_ctor_set(v___x_2108_, 0, v___x_2111_);
v___x_2113_ = v___x_2108_;
goto v_reusejp_2112_;
}
else
{
lean_object* v_reuseFailAlloc_2114_; 
v_reuseFailAlloc_2114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2114_, 0, v___x_2111_);
v___x_2113_ = v_reuseFailAlloc_2114_;
goto v_reusejp_2112_;
}
v_reusejp_2112_:
{
return v___x_2113_;
}
}
}
else
{
lean_object* v_a_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; 
v_a_2116_ = lean_ctor_get(v___x_2105_, 0);
lean_inc(v_a_2116_);
lean_dec_ref_known(v___x_2105_, 1);
v___x_2117_ = ((lean_object*)(l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__18));
lean_inc(v_json_2064_);
v___x_2118_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonStackTable_fromJson_spec__0(v_json_2064_, v___x_2117_);
if (lean_obj_tag(v___x_2118_) == 0)
{
lean_object* v_a_2119_; lean_object* v___x_2121_; uint8_t v_isShared_2122_; uint8_t v_isSharedCheck_2128_; 
lean_dec(v_a_2116_);
lean_dec(v_a_2103_);
lean_dec(v_a_2090_);
lean_dec(v_a_2077_);
lean_dec(v_json_2064_);
v_a_2119_ = lean_ctor_get(v___x_2118_, 0);
v_isSharedCheck_2128_ = !lean_is_exclusive(v___x_2118_);
if (v_isSharedCheck_2128_ == 0)
{
v___x_2121_ = v___x_2118_;
v_isShared_2122_ = v_isSharedCheck_2128_;
goto v_resetjp_2120_;
}
else
{
lean_inc(v_a_2119_);
lean_dec(v___x_2118_);
v___x_2121_ = lean_box(0);
v_isShared_2122_ = v_isSharedCheck_2128_;
goto v_resetjp_2120_;
}
v_resetjp_2120_:
{
lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2126_; 
v___x_2123_ = lean_obj_once(&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__22, &l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__22_once, _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__22);
v___x_2124_ = lean_string_append(v___x_2123_, v_a_2119_);
lean_dec(v_a_2119_);
if (v_isShared_2122_ == 0)
{
lean_ctor_set(v___x_2121_, 0, v___x_2124_);
v___x_2126_ = v___x_2121_;
goto v_reusejp_2125_;
}
else
{
lean_object* v_reuseFailAlloc_2127_; 
v_reuseFailAlloc_2127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2127_, 0, v___x_2124_);
v___x_2126_ = v_reuseFailAlloc_2127_;
goto v_reusejp_2125_;
}
v_reusejp_2125_:
{
return v___x_2126_;
}
}
}
else
{
lean_object* v_a_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; 
v_a_2129_ = lean_ctor_get(v___x_2118_, 0);
lean_inc(v_a_2129_);
lean_dec_ref_known(v___x_2118_, 1);
v___x_2130_ = ((lean_object*)(l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__23));
lean_inc(v_json_2064_);
v___x_2131_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonFrameTable_fromJson_spec__0(v_json_2064_, v___x_2130_);
if (lean_obj_tag(v___x_2131_) == 0)
{
lean_object* v_a_2132_; lean_object* v___x_2134_; uint8_t v_isShared_2135_; uint8_t v_isSharedCheck_2141_; 
lean_dec(v_a_2129_);
lean_dec(v_a_2116_);
lean_dec(v_a_2103_);
lean_dec(v_a_2090_);
lean_dec(v_a_2077_);
lean_dec(v_json_2064_);
v_a_2132_ = lean_ctor_get(v___x_2131_, 0);
v_isSharedCheck_2141_ = !lean_is_exclusive(v___x_2131_);
if (v_isSharedCheck_2141_ == 0)
{
v___x_2134_ = v___x_2131_;
v_isShared_2135_ = v_isSharedCheck_2141_;
goto v_resetjp_2133_;
}
else
{
lean_inc(v_a_2132_);
lean_dec(v___x_2131_);
v___x_2134_ = lean_box(0);
v_isShared_2135_ = v_isSharedCheck_2141_;
goto v_resetjp_2133_;
}
v_resetjp_2133_:
{
lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2139_; 
v___x_2136_ = lean_obj_once(&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__27, &l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__27_once, _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__27);
v___x_2137_ = lean_string_append(v___x_2136_, v_a_2132_);
lean_dec(v_a_2132_);
if (v_isShared_2135_ == 0)
{
lean_ctor_set(v___x_2134_, 0, v___x_2137_);
v___x_2139_ = v___x_2134_;
goto v_reusejp_2138_;
}
else
{
lean_object* v_reuseFailAlloc_2140_; 
v_reuseFailAlloc_2140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2140_, 0, v___x_2137_);
v___x_2139_ = v_reuseFailAlloc_2140_;
goto v_reusejp_2138_;
}
v_reusejp_2138_:
{
return v___x_2139_;
}
}
}
else
{
lean_object* v_a_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; 
v_a_2142_ = lean_ctor_get(v___x_2131_, 0);
lean_inc(v_a_2142_);
lean_dec_ref_known(v___x_2131_, 1);
v___x_2143_ = ((lean_object*)(l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__28));
lean_inc(v_json_2064_);
v___x_2144_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonFrameTable_fromJson_spec__0(v_json_2064_, v___x_2143_);
if (lean_obj_tag(v___x_2144_) == 0)
{
lean_object* v_a_2145_; lean_object* v___x_2147_; uint8_t v_isShared_2148_; uint8_t v_isSharedCheck_2154_; 
lean_dec(v_a_2142_);
lean_dec(v_a_2129_);
lean_dec(v_a_2116_);
lean_dec(v_a_2103_);
lean_dec(v_a_2090_);
lean_dec(v_a_2077_);
lean_dec(v_json_2064_);
v_a_2145_ = lean_ctor_get(v___x_2144_, 0);
v_isSharedCheck_2154_ = !lean_is_exclusive(v___x_2144_);
if (v_isSharedCheck_2154_ == 0)
{
v___x_2147_ = v___x_2144_;
v_isShared_2148_ = v_isSharedCheck_2154_;
goto v_resetjp_2146_;
}
else
{
lean_inc(v_a_2145_);
lean_dec(v___x_2144_);
v___x_2147_ = lean_box(0);
v_isShared_2148_ = v_isSharedCheck_2154_;
goto v_resetjp_2146_;
}
v_resetjp_2146_:
{
lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2152_; 
v___x_2149_ = lean_obj_once(&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__32, &l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__32_once, _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__32);
v___x_2150_ = lean_string_append(v___x_2149_, v_a_2145_);
lean_dec(v_a_2145_);
if (v_isShared_2148_ == 0)
{
lean_ctor_set(v___x_2147_, 0, v___x_2150_);
v___x_2152_ = v___x_2147_;
goto v_reusejp_2151_;
}
else
{
lean_object* v_reuseFailAlloc_2153_; 
v_reuseFailAlloc_2153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2153_, 0, v___x_2150_);
v___x_2152_ = v_reuseFailAlloc_2153_;
goto v_reusejp_2151_;
}
v_reusejp_2151_:
{
return v___x_2152_;
}
}
}
else
{
lean_object* v_a_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; 
v_a_2155_ = lean_ctor_get(v___x_2144_, 0);
lean_inc(v_a_2155_);
lean_dec_ref_known(v___x_2144_, 1);
v___x_2156_ = ((lean_object*)(l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__33));
lean_inc(v_json_2064_);
v___x_2157_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonFrameTable_fromJson_spec__0(v_json_2064_, v___x_2156_);
if (lean_obj_tag(v___x_2157_) == 0)
{
lean_object* v_a_2158_; lean_object* v___x_2160_; uint8_t v_isShared_2161_; uint8_t v_isSharedCheck_2167_; 
lean_dec(v_a_2155_);
lean_dec(v_a_2142_);
lean_dec(v_a_2129_);
lean_dec(v_a_2116_);
lean_dec(v_a_2103_);
lean_dec(v_a_2090_);
lean_dec(v_a_2077_);
lean_dec(v_json_2064_);
v_a_2158_ = lean_ctor_get(v___x_2157_, 0);
v_isSharedCheck_2167_ = !lean_is_exclusive(v___x_2157_);
if (v_isSharedCheck_2167_ == 0)
{
v___x_2160_ = v___x_2157_;
v_isShared_2161_ = v_isSharedCheck_2167_;
goto v_resetjp_2159_;
}
else
{
lean_inc(v_a_2158_);
lean_dec(v___x_2157_);
v___x_2160_ = lean_box(0);
v_isShared_2161_ = v_isSharedCheck_2167_;
goto v_resetjp_2159_;
}
v_resetjp_2159_:
{
lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2165_; 
v___x_2162_ = lean_obj_once(&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__37, &l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__37_once, _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__37);
v___x_2163_ = lean_string_append(v___x_2162_, v_a_2158_);
lean_dec(v_a_2158_);
if (v_isShared_2161_ == 0)
{
lean_ctor_set(v___x_2160_, 0, v___x_2163_);
v___x_2165_ = v___x_2160_;
goto v_reusejp_2164_;
}
else
{
lean_object* v_reuseFailAlloc_2166_; 
v_reuseFailAlloc_2166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2166_, 0, v___x_2163_);
v___x_2165_ = v_reuseFailAlloc_2166_;
goto v_reusejp_2164_;
}
v_reusejp_2164_:
{
return v___x_2165_;
}
}
}
else
{
lean_object* v_a_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; 
v_a_2168_ = lean_ctor_get(v___x_2157_, 0);
lean_inc(v_a_2168_);
lean_dec_ref_known(v___x_2157_, 1);
v___x_2169_ = ((lean_object*)(l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__38));
lean_inc(v_json_2064_);
v___x_2170_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonStackTable_fromJson_spec__1(v_json_2064_, v___x_2169_);
if (lean_obj_tag(v___x_2170_) == 0)
{
lean_object* v_a_2171_; lean_object* v___x_2173_; uint8_t v_isShared_2174_; uint8_t v_isSharedCheck_2180_; 
lean_dec(v_a_2168_);
lean_dec(v_a_2155_);
lean_dec(v_a_2142_);
lean_dec(v_a_2129_);
lean_dec(v_a_2116_);
lean_dec(v_a_2103_);
lean_dec(v_a_2090_);
lean_dec(v_a_2077_);
lean_dec(v_json_2064_);
v_a_2171_ = lean_ctor_get(v___x_2170_, 0);
v_isSharedCheck_2180_ = !lean_is_exclusive(v___x_2170_);
if (v_isSharedCheck_2180_ == 0)
{
v___x_2173_ = v___x_2170_;
v_isShared_2174_ = v_isSharedCheck_2180_;
goto v_resetjp_2172_;
}
else
{
lean_inc(v_a_2171_);
lean_dec(v___x_2170_);
v___x_2173_ = lean_box(0);
v_isShared_2174_ = v_isSharedCheck_2180_;
goto v_resetjp_2172_;
}
v_resetjp_2172_:
{
lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2178_; 
v___x_2175_ = lean_obj_once(&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__42, &l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__42_once, _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__42);
v___x_2176_ = lean_string_append(v___x_2175_, v_a_2171_);
lean_dec(v_a_2171_);
if (v_isShared_2174_ == 0)
{
lean_ctor_set(v___x_2173_, 0, v___x_2176_);
v___x_2178_ = v___x_2173_;
goto v_reusejp_2177_;
}
else
{
lean_object* v_reuseFailAlloc_2179_; 
v_reuseFailAlloc_2179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2179_, 0, v___x_2176_);
v___x_2178_ = v_reuseFailAlloc_2179_;
goto v_reusejp_2177_;
}
v_reusejp_2177_:
{
return v___x_2178_;
}
}
}
else
{
lean_object* v_a_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; 
v_a_2181_ = lean_ctor_get(v___x_2170_, 0);
lean_inc(v_a_2181_);
lean_dec_ref_known(v___x_2170_, 1);
v___x_2182_ = ((lean_object*)(l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__43));
lean_inc(v_json_2064_);
v___x_2183_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonStackTable_fromJson_spec__1(v_json_2064_, v___x_2182_);
if (lean_obj_tag(v___x_2183_) == 0)
{
lean_object* v_a_2184_; lean_object* v___x_2186_; uint8_t v_isShared_2187_; uint8_t v_isSharedCheck_2193_; 
lean_dec(v_a_2181_);
lean_dec(v_a_2168_);
lean_dec(v_a_2155_);
lean_dec(v_a_2142_);
lean_dec(v_a_2129_);
lean_dec(v_a_2116_);
lean_dec(v_a_2103_);
lean_dec(v_a_2090_);
lean_dec(v_a_2077_);
lean_dec(v_json_2064_);
v_a_2184_ = lean_ctor_get(v___x_2183_, 0);
v_isSharedCheck_2193_ = !lean_is_exclusive(v___x_2183_);
if (v_isSharedCheck_2193_ == 0)
{
v___x_2186_ = v___x_2183_;
v_isShared_2187_ = v_isSharedCheck_2193_;
goto v_resetjp_2185_;
}
else
{
lean_inc(v_a_2184_);
lean_dec(v___x_2183_);
v___x_2186_ = lean_box(0);
v_isShared_2187_ = v_isSharedCheck_2193_;
goto v_resetjp_2185_;
}
v_resetjp_2185_:
{
lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2191_; 
v___x_2188_ = lean_obj_once(&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__47, &l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__47_once, _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__47);
v___x_2189_ = lean_string_append(v___x_2188_, v_a_2184_);
lean_dec(v_a_2184_);
if (v_isShared_2187_ == 0)
{
lean_ctor_set(v___x_2186_, 0, v___x_2189_);
v___x_2191_ = v___x_2186_;
goto v_reusejp_2190_;
}
else
{
lean_object* v_reuseFailAlloc_2192_; 
v_reuseFailAlloc_2192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2192_, 0, v___x_2189_);
v___x_2191_ = v_reuseFailAlloc_2192_;
goto v_reusejp_2190_;
}
v_reusejp_2190_:
{
return v___x_2191_;
}
}
}
else
{
lean_object* v_a_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; 
v_a_2194_ = lean_ctor_get(v___x_2183_, 0);
lean_inc(v_a_2194_);
lean_dec_ref_known(v___x_2183_, 1);
v___x_2195_ = ((lean_object*)(l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__24));
v___x_2196_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__2(v_json_2064_, v___x_2195_);
if (lean_obj_tag(v___x_2196_) == 0)
{
lean_object* v_a_2197_; lean_object* v___x_2199_; uint8_t v_isShared_2200_; uint8_t v_isSharedCheck_2206_; 
lean_dec(v_a_2194_);
lean_dec(v_a_2181_);
lean_dec(v_a_2168_);
lean_dec(v_a_2155_);
lean_dec(v_a_2142_);
lean_dec(v_a_2129_);
lean_dec(v_a_2116_);
lean_dec(v_a_2103_);
lean_dec(v_a_2090_);
lean_dec(v_a_2077_);
v_a_2197_ = lean_ctor_get(v___x_2196_, 0);
v_isSharedCheck_2206_ = !lean_is_exclusive(v___x_2196_);
if (v_isSharedCheck_2206_ == 0)
{
v___x_2199_ = v___x_2196_;
v_isShared_2200_ = v_isSharedCheck_2206_;
goto v_resetjp_2198_;
}
else
{
lean_inc(v_a_2197_);
lean_dec(v___x_2196_);
v___x_2199_ = lean_box(0);
v_isShared_2200_ = v_isSharedCheck_2206_;
goto v_resetjp_2198_;
}
v_resetjp_2198_:
{
lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2204_; 
v___x_2201_ = lean_obj_once(&l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__49, &l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__49_once, _init_l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__49);
v___x_2202_ = lean_string_append(v___x_2201_, v_a_2197_);
lean_dec(v_a_2197_);
if (v_isShared_2200_ == 0)
{
lean_ctor_set(v___x_2199_, 0, v___x_2202_);
v___x_2204_ = v___x_2199_;
goto v_reusejp_2203_;
}
else
{
lean_object* v_reuseFailAlloc_2205_; 
v_reuseFailAlloc_2205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2205_, 0, v___x_2202_);
v___x_2204_ = v_reuseFailAlloc_2205_;
goto v_reusejp_2203_;
}
v_reusejp_2203_:
{
return v___x_2204_;
}
}
}
else
{
lean_object* v_a_2207_; lean_object* v___x_2209_; uint8_t v_isShared_2210_; uint8_t v_isSharedCheck_2215_; 
v_a_2207_ = lean_ctor_get(v___x_2196_, 0);
v_isSharedCheck_2215_ = !lean_is_exclusive(v___x_2196_);
if (v_isSharedCheck_2215_ == 0)
{
v___x_2209_ = v___x_2196_;
v_isShared_2210_ = v_isSharedCheck_2215_;
goto v_resetjp_2208_;
}
else
{
lean_inc(v_a_2207_);
lean_dec(v___x_2196_);
v___x_2209_ = lean_box(0);
v_isShared_2210_ = v_isSharedCheck_2215_;
goto v_resetjp_2208_;
}
v_resetjp_2208_:
{
lean_object* v___x_2211_; lean_object* v___x_2213_; 
v___x_2211_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_2211_, 0, v_a_2077_);
lean_ctor_set(v___x_2211_, 1, v_a_2090_);
lean_ctor_set(v___x_2211_, 2, v_a_2103_);
lean_ctor_set(v___x_2211_, 3, v_a_2116_);
lean_ctor_set(v___x_2211_, 4, v_a_2129_);
lean_ctor_set(v___x_2211_, 5, v_a_2142_);
lean_ctor_set(v___x_2211_, 6, v_a_2155_);
lean_ctor_set(v___x_2211_, 7, v_a_2168_);
lean_ctor_set(v___x_2211_, 8, v_a_2181_);
lean_ctor_set(v___x_2211_, 9, v_a_2194_);
lean_ctor_set(v___x_2211_, 10, v_a_2207_);
if (v_isShared_2210_ == 0)
{
lean_ctor_set(v___x_2209_, 0, v___x_2211_);
v___x_2213_ = v___x_2209_;
goto v_reusejp_2212_;
}
else
{
lean_object* v_reuseFailAlloc_2214_; 
v_reuseFailAlloc_2214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2214_, 0, v___x_2211_);
v___x_2213_ = v_reuseFailAlloc_2214_;
goto v_reusejp_2212_;
}
v_reusejp_2212_:
{
return v___x_2213_;
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
LEAN_EXPORT lean_object* l_Lean_Option_toJson___at___00Lean_Array_toJson___at___00Lean_Firefox_instToJsonFrameTable_toJson_spec__0_spec__0(lean_object* v_x_2218_){
_start:
{
if (lean_obj_tag(v_x_2218_) == 0)
{
lean_object* v___x_2219_; 
v___x_2219_ = lean_box(0);
return v___x_2219_;
}
else
{
lean_object* v_val_2220_; 
v_val_2220_ = lean_ctor_get(v_x_2218_, 0);
lean_inc(v_val_2220_);
return v_val_2220_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_toJson___at___00Lean_Array_toJson___at___00Lean_Firefox_instToJsonFrameTable_toJson_spec__0_spec__0___boxed(lean_object* v_x_2221_){
_start:
{
lean_object* v_res_2222_; 
v_res_2222_ = l_Lean_Option_toJson___at___00Lean_Array_toJson___at___00Lean_Firefox_instToJsonFrameTable_toJson_spec__0_spec__0(v_x_2221_);
lean_dec(v_x_2221_);
return v_res_2222_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Firefox_instToJsonFrameTable_toJson_spec__0_spec__1(size_t v_sz_2223_, size_t v_i_2224_, lean_object* v_bs_2225_){
_start:
{
uint8_t v___x_2226_; 
v___x_2226_ = lean_usize_dec_lt(v_i_2224_, v_sz_2223_);
if (v___x_2226_ == 0)
{
return v_bs_2225_;
}
else
{
lean_object* v_v_2227_; lean_object* v___x_2228_; lean_object* v_bs_x27_2229_; lean_object* v___x_2230_; size_t v___x_2231_; size_t v___x_2232_; lean_object* v___x_2233_; 
v_v_2227_ = lean_array_uget(v_bs_2225_, v_i_2224_);
v___x_2228_ = lean_unsigned_to_nat(0u);
v_bs_x27_2229_ = lean_array_uset(v_bs_2225_, v_i_2224_, v___x_2228_);
v___x_2230_ = l_Lean_Option_toJson___at___00Lean_Array_toJson___at___00Lean_Firefox_instToJsonFrameTable_toJson_spec__0_spec__0(v_v_2227_);
lean_dec(v_v_2227_);
v___x_2231_ = ((size_t)1ULL);
v___x_2232_ = lean_usize_add(v_i_2224_, v___x_2231_);
v___x_2233_ = lean_array_uset(v_bs_x27_2229_, v_i_2224_, v___x_2230_);
v_i_2224_ = v___x_2232_;
v_bs_2225_ = v___x_2233_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Firefox_instToJsonFrameTable_toJson_spec__0_spec__1___boxed(lean_object* v_sz_2235_, lean_object* v_i_2236_, lean_object* v_bs_2237_){
_start:
{
size_t v_sz_boxed_2238_; size_t v_i_boxed_2239_; lean_object* v_res_2240_; 
v_sz_boxed_2238_ = lean_unbox_usize(v_sz_2235_);
lean_dec(v_sz_2235_);
v_i_boxed_2239_ = lean_unbox_usize(v_i_2236_);
lean_dec(v_i_2236_);
v_res_2240_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Firefox_instToJsonFrameTable_toJson_spec__0_spec__1(v_sz_boxed_2238_, v_i_boxed_2239_, v_bs_2237_);
return v_res_2240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Firefox_instToJsonFrameTable_toJson_spec__0(lean_object* v_a_2241_){
_start:
{
size_t v_sz_2242_; size_t v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; 
v_sz_2242_ = lean_array_size(v_a_2241_);
v___x_2243_ = ((size_t)0ULL);
v___x_2244_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Firefox_instToJsonFrameTable_toJson_spec__0_spec__1(v_sz_2242_, v___x_2243_, v_a_2241_);
v___x_2245_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_2245_, 0, v___x_2244_);
return v___x_2245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Firefox_instToJsonFrameTable_toJson(lean_object* v_x_2246_){
_start:
{
lean_object* v_address_2247_; lean_object* v_inlineDepth_2248_; lean_object* v_category_2249_; lean_object* v_subcategory_2250_; lean_object* v_func_2251_; lean_object* v_nativeSymbol_2252_; lean_object* v_innerWindowID_2253_; lean_object* v_implementation_2254_; lean_object* v_line_2255_; lean_object* v_column_2256_; lean_object* v_length_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; 
v_address_2247_ = lean_ctor_get(v_x_2246_, 0);
lean_inc_ref(v_address_2247_);
v_inlineDepth_2248_ = lean_ctor_get(v_x_2246_, 1);
lean_inc_ref(v_inlineDepth_2248_);
v_category_2249_ = lean_ctor_get(v_x_2246_, 2);
lean_inc_ref(v_category_2249_);
v_subcategory_2250_ = lean_ctor_get(v_x_2246_, 3);
lean_inc_ref(v_subcategory_2250_);
v_func_2251_ = lean_ctor_get(v_x_2246_, 4);
lean_inc_ref(v_func_2251_);
v_nativeSymbol_2252_ = lean_ctor_get(v_x_2246_, 5);
lean_inc_ref(v_nativeSymbol_2252_);
v_innerWindowID_2253_ = lean_ctor_get(v_x_2246_, 6);
lean_inc_ref(v_innerWindowID_2253_);
v_implementation_2254_ = lean_ctor_get(v_x_2246_, 7);
lean_inc_ref(v_implementation_2254_);
v_line_2255_ = lean_ctor_get(v_x_2246_, 8);
lean_inc_ref(v_line_2255_);
v_column_2256_ = lean_ctor_get(v_x_2246_, 9);
lean_inc_ref(v_column_2256_);
v_length_2257_ = lean_ctor_get(v_x_2246_, 10);
lean_inc(v_length_2257_);
lean_dec_ref(v_x_2246_);
v___x_2258_ = ((lean_object*)(l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__0));
v___x_2259_ = l_Lean_Array_toJson___at___00Lean_Firefox_instToJsonFuncTable_toJson_spec__0(v_address_2247_);
v___x_2260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2260_, 0, v___x_2258_);
lean_ctor_set(v___x_2260_, 1, v___x_2259_);
v___x_2261_ = lean_box(0);
v___x_2262_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2262_, 0, v___x_2260_);
lean_ctor_set(v___x_2262_, 1, v___x_2261_);
v___x_2263_ = ((lean_object*)(l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__9));
v___x_2264_ = l_Lean_Array_toJson___at___00Lean_Firefox_instToJsonStackTable_toJson_spec__0(v_inlineDepth_2248_);
v___x_2265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2265_, 0, v___x_2263_);
lean_ctor_set(v___x_2265_, 1, v___x_2264_);
v___x_2266_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2266_, 0, v___x_2265_);
lean_ctor_set(v___x_2266_, 1, v___x_2261_);
v___x_2267_ = ((lean_object*)(l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__9));
v___x_2268_ = l_Lean_Array_toJson___at___00Lean_Firefox_instToJsonStackTable_toJson_spec__1(v_category_2249_);
v___x_2269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2269_, 0, v___x_2267_);
lean_ctor_set(v___x_2269_, 1, v___x_2268_);
v___x_2270_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2270_, 0, v___x_2269_);
lean_ctor_set(v___x_2270_, 1, v___x_2261_);
v___x_2271_ = ((lean_object*)(l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__14));
v___x_2272_ = l_Lean_Array_toJson___at___00Lean_Firefox_instToJsonStackTable_toJson_spec__1(v_subcategory_2250_);
v___x_2273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2273_, 0, v___x_2271_);
lean_ctor_set(v___x_2273_, 1, v___x_2272_);
v___x_2274_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2274_, 0, v___x_2273_);
lean_ctor_set(v___x_2274_, 1, v___x_2261_);
v___x_2275_ = ((lean_object*)(l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__18));
v___x_2276_ = l_Lean_Array_toJson___at___00Lean_Firefox_instToJsonStackTable_toJson_spec__0(v_func_2251_);
v___x_2277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2277_, 0, v___x_2275_);
lean_ctor_set(v___x_2277_, 1, v___x_2276_);
v___x_2278_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2278_, 0, v___x_2277_);
lean_ctor_set(v___x_2278_, 1, v___x_2261_);
v___x_2279_ = ((lean_object*)(l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__23));
v___x_2280_ = l_Lean_Array_toJson___at___00Lean_Firefox_instToJsonFrameTable_toJson_spec__0(v_nativeSymbol_2252_);
v___x_2281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2281_, 0, v___x_2279_);
lean_ctor_set(v___x_2281_, 1, v___x_2280_);
v___x_2282_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2282_, 0, v___x_2281_);
lean_ctor_set(v___x_2282_, 1, v___x_2261_);
v___x_2283_ = ((lean_object*)(l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__28));
v___x_2284_ = l_Lean_Array_toJson___at___00Lean_Firefox_instToJsonFrameTable_toJson_spec__0(v_innerWindowID_2253_);
v___x_2285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2285_, 0, v___x_2283_);
lean_ctor_set(v___x_2285_, 1, v___x_2284_);
v___x_2286_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2286_, 0, v___x_2285_);
lean_ctor_set(v___x_2286_, 1, v___x_2261_);
v___x_2287_ = ((lean_object*)(l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__33));
v___x_2288_ = l_Lean_Array_toJson___at___00Lean_Firefox_instToJsonFrameTable_toJson_spec__0(v_implementation_2254_);
v___x_2289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2289_, 0, v___x_2287_);
lean_ctor_set(v___x_2289_, 1, v___x_2288_);
v___x_2290_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2290_, 0, v___x_2289_);
lean_ctor_set(v___x_2290_, 1, v___x_2261_);
v___x_2291_ = ((lean_object*)(l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__38));
v___x_2292_ = l_Lean_Array_toJson___at___00Lean_Firefox_instToJsonStackTable_toJson_spec__1(v_line_2255_);
v___x_2293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2293_, 0, v___x_2291_);
lean_ctor_set(v___x_2293_, 1, v___x_2292_);
v___x_2294_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2294_, 0, v___x_2293_);
lean_ctor_set(v___x_2294_, 1, v___x_2261_);
v___x_2295_ = ((lean_object*)(l_Lean_Firefox_instFromJsonFrameTable_fromJson___closed__43));
v___x_2296_ = l_Lean_Array_toJson___at___00Lean_Firefox_instToJsonStackTable_toJson_spec__1(v_column_2256_);
v___x_2297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2297_, 0, v___x_2295_);
lean_ctor_set(v___x_2297_, 1, v___x_2296_);
v___x_2298_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2298_, 0, v___x_2297_);
lean_ctor_set(v___x_2298_, 1, v___x_2261_);
v___x_2299_ = ((lean_object*)(l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__24));
v___x_2300_ = l_Lean_JsonNumber_fromNat(v_length_2257_);
v___x_2301_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2301_, 0, v___x_2300_);
v___x_2302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2302_, 0, v___x_2299_);
lean_ctor_set(v___x_2302_, 1, v___x_2301_);
v___x_2303_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2303_, 0, v___x_2302_);
lean_ctor_set(v___x_2303_, 1, v___x_2261_);
v___x_2304_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2304_, 0, v___x_2303_);
lean_ctor_set(v___x_2304_, 1, v___x_2261_);
v___x_2305_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2305_, 0, v___x_2298_);
lean_ctor_set(v___x_2305_, 1, v___x_2304_);
v___x_2306_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2306_, 0, v___x_2294_);
lean_ctor_set(v___x_2306_, 1, v___x_2305_);
v___x_2307_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2307_, 0, v___x_2290_);
lean_ctor_set(v___x_2307_, 1, v___x_2306_);
v___x_2308_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2308_, 0, v___x_2286_);
lean_ctor_set(v___x_2308_, 1, v___x_2307_);
v___x_2309_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2309_, 0, v___x_2282_);
lean_ctor_set(v___x_2309_, 1, v___x_2308_);
v___x_2310_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2310_, 0, v___x_2278_);
lean_ctor_set(v___x_2310_, 1, v___x_2309_);
v___x_2311_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2311_, 0, v___x_2274_);
lean_ctor_set(v___x_2311_, 1, v___x_2310_);
v___x_2312_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2312_, 0, v___x_2270_);
lean_ctor_set(v___x_2312_, 1, v___x_2311_);
v___x_2313_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2313_, 0, v___x_2266_);
lean_ctor_set(v___x_2313_, 1, v___x_2312_);
v___x_2314_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2314_, 0, v___x_2262_);
lean_ctor_set(v___x_2314_, 1, v___x_2313_);
v___x_2315_ = ((lean_object*)(l_Lean_Firefox_instToJsonCategory_toJson___closed__0));
v___x_2316_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Firefox_instToJsonCategory_toJson_spec__1(v___x_2314_, v___x_2315_);
v___x_2317_ = l_Lean_Json_mkObj(v___x_2316_);
lean_dec(v___x_2316_);
return v___x_2317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Firefox_FrameTable_push(lean_object* v_t_2327_, lean_object* v_e_2328_){
_start:
{
lean_object* v_address_2329_; lean_object* v_inlineDepth_2330_; lean_object* v_category_2331_; lean_object* v_subcategory_2332_; lean_object* v_func_2333_; lean_object* v_nativeSymbol_2334_; lean_object* v_innerWindowID_2335_; lean_object* v_implementation_2336_; lean_object* v_line_2337_; lean_object* v_column_2338_; lean_object* v_length_2339_; lean_object* v___x_2341_; uint8_t v_isShared_2342_; uint8_t v_isSharedCheck_2368_; 
v_address_2329_ = lean_ctor_get(v_t_2327_, 0);
v_inlineDepth_2330_ = lean_ctor_get(v_t_2327_, 1);
v_category_2331_ = lean_ctor_get(v_t_2327_, 2);
v_subcategory_2332_ = lean_ctor_get(v_t_2327_, 3);
v_func_2333_ = lean_ctor_get(v_t_2327_, 4);
v_nativeSymbol_2334_ = lean_ctor_get(v_t_2327_, 5);
v_innerWindowID_2335_ = lean_ctor_get(v_t_2327_, 6);
v_implementation_2336_ = lean_ctor_get(v_t_2327_, 7);
v_line_2337_ = lean_ctor_get(v_t_2327_, 8);
v_column_2338_ = lean_ctor_get(v_t_2327_, 9);
v_length_2339_ = lean_ctor_get(v_t_2327_, 10);
v_isSharedCheck_2368_ = !lean_is_exclusive(v_t_2327_);
if (v_isSharedCheck_2368_ == 0)
{
v___x_2341_ = v_t_2327_;
v_isShared_2342_ = v_isSharedCheck_2368_;
goto v_resetjp_2340_;
}
else
{
lean_inc(v_length_2339_);
lean_inc(v_column_2338_);
lean_inc(v_line_2337_);
lean_inc(v_implementation_2336_);
lean_inc(v_innerWindowID_2335_);
lean_inc(v_nativeSymbol_2334_);
lean_inc(v_func_2333_);
lean_inc(v_subcategory_2332_);
lean_inc(v_category_2331_);
lean_inc(v_inlineDepth_2330_);
lean_inc(v_address_2329_);
lean_dec(v_t_2327_);
v___x_2341_ = lean_box(0);
v_isShared_2342_ = v_isSharedCheck_2368_;
goto v_resetjp_2340_;
}
v_resetjp_2340_:
{
lean_object* v_address_2343_; lean_object* v_inlineDepth_2344_; lean_object* v_category_2345_; lean_object* v_subcategory_2346_; lean_object* v_func_2347_; lean_object* v_nativeSymbol_2348_; lean_object* v_innerWindowID_2349_; lean_object* v_implementation_2350_; lean_object* v_line_2351_; lean_object* v_column_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2366_; 
v_address_2343_ = lean_ctor_get(v_e_2328_, 0);
lean_inc(v_address_2343_);
v_inlineDepth_2344_ = lean_ctor_get(v_e_2328_, 1);
lean_inc(v_inlineDepth_2344_);
v_category_2345_ = lean_ctor_get(v_e_2328_, 2);
lean_inc(v_category_2345_);
v_subcategory_2346_ = lean_ctor_get(v_e_2328_, 3);
lean_inc(v_subcategory_2346_);
v_func_2347_ = lean_ctor_get(v_e_2328_, 4);
lean_inc(v_func_2347_);
v_nativeSymbol_2348_ = lean_ctor_get(v_e_2328_, 5);
lean_inc(v_nativeSymbol_2348_);
v_innerWindowID_2349_ = lean_ctor_get(v_e_2328_, 6);
lean_inc(v_innerWindowID_2349_);
v_implementation_2350_ = lean_ctor_get(v_e_2328_, 7);
lean_inc(v_implementation_2350_);
v_line_2351_ = lean_ctor_get(v_e_2328_, 8);
lean_inc(v_line_2351_);
v_column_2352_ = lean_ctor_get(v_e_2328_, 9);
lean_inc(v_column_2352_);
lean_dec_ref(v_e_2328_);
v___x_2353_ = lean_array_push(v_address_2329_, v_address_2343_);
v___x_2354_ = lean_array_push(v_inlineDepth_2330_, v_inlineDepth_2344_);
v___x_2355_ = lean_array_push(v_category_2331_, v_category_2345_);
v___x_2356_ = lean_array_push(v_subcategory_2332_, v_subcategory_2346_);
v___x_2357_ = lean_array_push(v_func_2333_, v_func_2347_);
v___x_2358_ = lean_array_push(v_nativeSymbol_2334_, v_nativeSymbol_2348_);
v___x_2359_ = lean_array_push(v_innerWindowID_2335_, v_innerWindowID_2349_);
v___x_2360_ = lean_array_push(v_implementation_2336_, v_implementation_2350_);
v___x_2361_ = lean_array_push(v_line_2337_, v_line_2351_);
v___x_2362_ = lean_array_push(v_column_2338_, v_column_2352_);
v___x_2363_ = lean_unsigned_to_nat(1u);
v___x_2364_ = lean_nat_add(v_length_2339_, v___x_2363_);
lean_dec(v_length_2339_);
if (v_isShared_2342_ == 0)
{
lean_ctor_set(v___x_2341_, 10, v___x_2364_);
lean_ctor_set(v___x_2341_, 9, v___x_2362_);
lean_ctor_set(v___x_2341_, 8, v___x_2361_);
lean_ctor_set(v___x_2341_, 7, v___x_2360_);
lean_ctor_set(v___x_2341_, 6, v___x_2359_);
lean_ctor_set(v___x_2341_, 5, v___x_2358_);
lean_ctor_set(v___x_2341_, 4, v___x_2357_);
lean_ctor_set(v___x_2341_, 3, v___x_2356_);
lean_ctor_set(v___x_2341_, 2, v___x_2355_);
lean_ctor_set(v___x_2341_, 1, v___x_2354_);
lean_ctor_set(v___x_2341_, 0, v___x_2353_);
v___x_2366_ = v___x_2341_;
goto v_reusejp_2365_;
}
else
{
lean_object* v_reuseFailAlloc_2367_; 
v_reuseFailAlloc_2367_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2367_, 0, v___x_2353_);
lean_ctor_set(v_reuseFailAlloc_2367_, 1, v___x_2354_);
lean_ctor_set(v_reuseFailAlloc_2367_, 2, v___x_2355_);
lean_ctor_set(v_reuseFailAlloc_2367_, 3, v___x_2356_);
lean_ctor_set(v_reuseFailAlloc_2367_, 4, v___x_2357_);
lean_ctor_set(v_reuseFailAlloc_2367_, 5, v___x_2358_);
lean_ctor_set(v_reuseFailAlloc_2367_, 6, v___x_2359_);
lean_ctor_set(v_reuseFailAlloc_2367_, 7, v___x_2360_);
lean_ctor_set(v_reuseFailAlloc_2367_, 8, v___x_2361_);
lean_ctor_set(v_reuseFailAlloc_2367_, 9, v___x_2362_);
lean_ctor_set(v_reuseFailAlloc_2367_, 10, v___x_2364_);
v___x_2366_ = v_reuseFailAlloc_2367_;
goto v_reusejp_2365_;
}
v_reusejp_2365_:
{
return v___x_2366_;
}
}
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__3(void){
_start:
{
uint8_t v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; 
v___x_2375_ = 1;
v___x_2376_ = ((lean_object*)(l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__2));
v___x_2377_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2376_, v___x_2375_);
return v___x_2377_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__4(void){
_start:
{
lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; 
v___x_2378_ = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__6));
v___x_2379_ = lean_obj_once(&l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__3, &l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__3_once, _init_l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__3);
v___x_2380_ = lean_string_append(v___x_2379_, v___x_2378_);
return v___x_2380_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__6(void){
_start:
{
uint8_t v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; 
v___x_2383_ = 1;
v___x_2384_ = ((lean_object*)(l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__5));
v___x_2385_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2384_, v___x_2383_);
return v___x_2385_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__7(void){
_start:
{
lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; 
v___x_2386_ = lean_obj_once(&l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__6, &l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__6_once, _init_l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__6);
v___x_2387_ = lean_obj_once(&l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__4, &l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__4_once, _init_l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__4);
v___x_2388_ = lean_string_append(v___x_2387_, v___x_2386_);
return v___x_2388_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__8(void){
_start:
{
lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; 
v___x_2389_ = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
v___x_2390_ = lean_obj_once(&l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__7, &l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__7_once, _init_l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__7);
v___x_2391_ = lean_string_append(v___x_2390_, v___x_2389_);
return v___x_2391_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__9(void){
_start:
{
lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; 
v___x_2392_ = lean_obj_once(&l_Lean_Firefox_instFromJsonCategory_fromJson___closed__9, &l_Lean_Firefox_instFromJsonCategory_fromJson___closed__9_once, _init_l_Lean_Firefox_instFromJsonCategory_fromJson___closed__9);
v___x_2393_ = lean_obj_once(&l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__4, &l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__4_once, _init_l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__4);
v___x_2394_ = lean_string_append(v___x_2393_, v___x_2392_);
return v___x_2394_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__10(void){
_start:
{
lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; 
v___x_2395_ = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
v___x_2396_ = lean_obj_once(&l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__9, &l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__9_once, _init_l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__9);
v___x_2397_ = lean_string_append(v___x_2396_, v___x_2395_);
return v___x_2397_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__11(void){
_start:
{
lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; 
v___x_2398_ = lean_obj_once(&l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__26, &l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__26_once, _init_l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__26);
v___x_2399_ = lean_obj_once(&l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__4, &l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__4_once, _init_l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__4);
v___x_2400_ = lean_string_append(v___x_2399_, v___x_2398_);
return v___x_2400_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__12(void){
_start:
{
lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; 
v___x_2401_ = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
v___x_2402_ = lean_obj_once(&l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__11, &l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__11_once, _init_l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__11);
v___x_2403_ = lean_string_append(v___x_2402_, v___x_2401_);
return v___x_2403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson(lean_object* v_json_2404_){
_start:
{
lean_object* v___x_2405_; lean_object* v___x_2406_; 
v___x_2405_ = ((lean_object*)(l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__0));
lean_inc(v_json_2404_);
v___x_2406_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__3(v_json_2404_, v___x_2405_);
if (lean_obj_tag(v___x_2406_) == 0)
{
lean_object* v_a_2407_; lean_object* v___x_2409_; uint8_t v_isShared_2410_; uint8_t v_isSharedCheck_2416_; 
lean_dec(v_json_2404_);
v_a_2407_ = lean_ctor_get(v___x_2406_, 0);
v_isSharedCheck_2416_ = !lean_is_exclusive(v___x_2406_);
if (v_isSharedCheck_2416_ == 0)
{
v___x_2409_ = v___x_2406_;
v_isShared_2410_ = v_isSharedCheck_2416_;
goto v_resetjp_2408_;
}
else
{
lean_inc(v_a_2407_);
lean_dec(v___x_2406_);
v___x_2409_ = lean_box(0);
v_isShared_2410_ = v_isSharedCheck_2416_;
goto v_resetjp_2408_;
}
v_resetjp_2408_:
{
lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2414_; 
v___x_2411_ = lean_obj_once(&l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__8, &l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__8_once, _init_l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__8);
v___x_2412_ = lean_string_append(v___x_2411_, v_a_2407_);
lean_dec(v_a_2407_);
if (v_isShared_2410_ == 0)
{
lean_ctor_set(v___x_2409_, 0, v___x_2412_);
v___x_2414_ = v___x_2409_;
goto v_reusejp_2413_;
}
else
{
lean_object* v_reuseFailAlloc_2415_; 
v_reuseFailAlloc_2415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2415_, 0, v___x_2412_);
v___x_2414_ = v_reuseFailAlloc_2415_;
goto v_reusejp_2413_;
}
v_reusejp_2413_:
{
return v___x_2414_;
}
}
}
else
{
lean_object* v_a_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; 
v_a_2417_ = lean_ctor_get(v___x_2406_, 0);
lean_inc(v_a_2417_);
lean_dec_ref_known(v___x_2406_, 1);
v___x_2418_ = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__0));
lean_inc(v_json_2404_);
v___x_2419_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__3(v_json_2404_, v___x_2418_);
if (lean_obj_tag(v___x_2419_) == 0)
{
lean_object* v_a_2420_; lean_object* v___x_2422_; uint8_t v_isShared_2423_; uint8_t v_isSharedCheck_2429_; 
lean_dec(v_a_2417_);
lean_dec(v_json_2404_);
v_a_2420_ = lean_ctor_get(v___x_2419_, 0);
v_isSharedCheck_2429_ = !lean_is_exclusive(v___x_2419_);
if (v_isSharedCheck_2429_ == 0)
{
v___x_2422_ = v___x_2419_;
v_isShared_2423_ = v_isSharedCheck_2429_;
goto v_resetjp_2421_;
}
else
{
lean_inc(v_a_2420_);
lean_dec(v___x_2419_);
v___x_2422_ = lean_box(0);
v_isShared_2423_ = v_isSharedCheck_2429_;
goto v_resetjp_2421_;
}
v_resetjp_2421_:
{
lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2427_; 
v___x_2424_ = lean_obj_once(&l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__10, &l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__10_once, _init_l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__10);
v___x_2425_ = lean_string_append(v___x_2424_, v_a_2420_);
lean_dec(v_a_2420_);
if (v_isShared_2423_ == 0)
{
lean_ctor_set(v___x_2422_, 0, v___x_2425_);
v___x_2427_ = v___x_2422_;
goto v_reusejp_2426_;
}
else
{
lean_object* v_reuseFailAlloc_2428_; 
v_reuseFailAlloc_2428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2428_, 0, v___x_2425_);
v___x_2427_ = v_reuseFailAlloc_2428_;
goto v_reusejp_2426_;
}
v_reusejp_2426_:
{
return v___x_2427_;
}
}
}
else
{
lean_object* v_a_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; 
v_a_2430_ = lean_ctor_get(v___x_2419_, 0);
lean_inc(v_a_2430_);
lean_dec_ref_known(v___x_2419_, 1);
v___x_2431_ = ((lean_object*)(l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__24));
v___x_2432_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__2(v_json_2404_, v___x_2431_);
if (lean_obj_tag(v___x_2432_) == 0)
{
lean_object* v_a_2433_; lean_object* v___x_2435_; uint8_t v_isShared_2436_; uint8_t v_isSharedCheck_2442_; 
lean_dec(v_a_2430_);
lean_dec(v_a_2417_);
v_a_2433_ = lean_ctor_get(v___x_2432_, 0);
v_isSharedCheck_2442_ = !lean_is_exclusive(v___x_2432_);
if (v_isSharedCheck_2442_ == 0)
{
v___x_2435_ = v___x_2432_;
v_isShared_2436_ = v_isSharedCheck_2442_;
goto v_resetjp_2434_;
}
else
{
lean_inc(v_a_2433_);
lean_dec(v___x_2432_);
v___x_2435_ = lean_box(0);
v_isShared_2436_ = v_isSharedCheck_2442_;
goto v_resetjp_2434_;
}
v_resetjp_2434_:
{
lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2440_; 
v___x_2437_ = lean_obj_once(&l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__12, &l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__12_once, _init_l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__12);
v___x_2438_ = lean_string_append(v___x_2437_, v_a_2433_);
lean_dec(v_a_2433_);
if (v_isShared_2436_ == 0)
{
lean_ctor_set(v___x_2435_, 0, v___x_2438_);
v___x_2440_ = v___x_2435_;
goto v_reusejp_2439_;
}
else
{
lean_object* v_reuseFailAlloc_2441_; 
v_reuseFailAlloc_2441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2441_, 0, v___x_2438_);
v___x_2440_ = v_reuseFailAlloc_2441_;
goto v_reusejp_2439_;
}
v_reusejp_2439_:
{
return v___x_2440_;
}
}
}
else
{
lean_object* v_a_2443_; lean_object* v___x_2445_; uint8_t v_isShared_2446_; uint8_t v_isSharedCheck_2451_; 
v_a_2443_ = lean_ctor_get(v___x_2432_, 0);
v_isSharedCheck_2451_ = !lean_is_exclusive(v___x_2432_);
if (v_isSharedCheck_2451_ == 0)
{
v___x_2445_ = v___x_2432_;
v_isShared_2446_ = v_isSharedCheck_2451_;
goto v_resetjp_2444_;
}
else
{
lean_inc(v_a_2443_);
lean_dec(v___x_2432_);
v___x_2445_ = lean_box(0);
v_isShared_2446_ = v_isSharedCheck_2451_;
goto v_resetjp_2444_;
}
v_resetjp_2444_:
{
lean_object* v___x_2447_; lean_object* v___x_2449_; 
v___x_2447_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2447_, 0, v_a_2417_);
lean_ctor_set(v___x_2447_, 1, v_a_2430_);
lean_ctor_set(v___x_2447_, 2, v_a_2443_);
if (v_isShared_2446_ == 0)
{
lean_ctor_set(v___x_2445_, 0, v___x_2447_);
v___x_2449_ = v___x_2445_;
goto v_reusejp_2448_;
}
else
{
lean_object* v_reuseFailAlloc_2450_; 
v_reuseFailAlloc_2450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2450_, 0, v___x_2447_);
v___x_2449_ = v_reuseFailAlloc_2450_;
goto v_reusejp_2448_;
}
v_reusejp_2448_:
{
return v___x_2449_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Firefox_instToJsonRawMarkerTable_toJson(lean_object* v_x_2454_){
_start:
{
lean_object* v_data_2455_; lean_object* v_name_2456_; lean_object* v_length_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; 
v_data_2455_ = lean_ctor_get(v_x_2454_, 0);
lean_inc_ref(v_data_2455_);
v_name_2456_ = lean_ctor_get(v_x_2454_, 1);
lean_inc_ref(v_name_2456_);
v_length_2457_ = lean_ctor_get(v_x_2454_, 2);
lean_inc(v_length_2457_);
lean_dec_ref(v_x_2454_);
v___x_2458_ = ((lean_object*)(l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson___closed__0));
v___x_2459_ = l_Lean_Array_toJson___at___00Lean_Firefox_instToJsonProfileMeta_toJson_spec__1(v_data_2455_);
v___x_2460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2460_, 0, v___x_2458_);
lean_ctor_set(v___x_2460_, 1, v___x_2459_);
v___x_2461_ = lean_box(0);
v___x_2462_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2462_, 0, v___x_2460_);
lean_ctor_set(v___x_2462_, 1, v___x_2461_);
v___x_2463_ = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__0));
v___x_2464_ = l_Lean_Array_toJson___at___00Lean_Firefox_instToJsonProfileMeta_toJson_spec__1(v_name_2456_);
v___x_2465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2465_, 0, v___x_2463_);
lean_ctor_set(v___x_2465_, 1, v___x_2464_);
v___x_2466_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2466_, 0, v___x_2465_);
lean_ctor_set(v___x_2466_, 1, v___x_2461_);
v___x_2467_ = ((lean_object*)(l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__24));
v___x_2468_ = l_Lean_JsonNumber_fromNat(v_length_2457_);
v___x_2469_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2469_, 0, v___x_2468_);
v___x_2470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2470_, 0, v___x_2467_);
lean_ctor_set(v___x_2470_, 1, v___x_2469_);
v___x_2471_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2471_, 0, v___x_2470_);
lean_ctor_set(v___x_2471_, 1, v___x_2461_);
v___x_2472_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2472_, 0, v___x_2471_);
lean_ctor_set(v___x_2472_, 1, v___x_2461_);
v___x_2473_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2473_, 0, v___x_2466_);
lean_ctor_set(v___x_2473_, 1, v___x_2472_);
v___x_2474_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2474_, 0, v___x_2462_);
lean_ctor_set(v___x_2474_, 1, v___x_2473_);
v___x_2475_ = ((lean_object*)(l_Lean_Firefox_instToJsonCategory_toJson___closed__0));
v___x_2476_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Firefox_instToJsonCategory_toJson_spec__1(v___x_2474_, v___x_2475_);
v___x_2477_ = l_Lean_Json_mkObj(v___x_2476_);
lean_dec(v___x_2476_);
return v___x_2477_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__3(void){
_start:
{
uint8_t v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; 
v___x_2486_ = 1;
v___x_2487_ = ((lean_object*)(l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__2));
v___x_2488_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2487_, v___x_2486_);
return v___x_2488_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__4(void){
_start:
{
lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; 
v___x_2489_ = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__6));
v___x_2490_ = lean_obj_once(&l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__3, &l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__3_once, _init_l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__3);
v___x_2491_ = lean_string_append(v___x_2490_, v___x_2489_);
return v___x_2491_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__6(void){
_start:
{
uint8_t v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; 
v___x_2494_ = 1;
v___x_2495_ = ((lean_object*)(l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__5));
v___x_2496_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2495_, v___x_2494_);
return v___x_2496_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__7(void){
_start:
{
lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; 
v___x_2497_ = lean_obj_once(&l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__6, &l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__6_once, _init_l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__6);
v___x_2498_ = lean_obj_once(&l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__4, &l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__4_once, _init_l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__4);
v___x_2499_ = lean_string_append(v___x_2498_, v___x_2497_);
return v___x_2499_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__8(void){
_start:
{
lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; 
v___x_2500_ = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
v___x_2501_ = lean_obj_once(&l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__7, &l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__7_once, _init_l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__7);
v___x_2502_ = lean_string_append(v___x_2501_, v___x_2500_);
return v___x_2502_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__9(void){
_start:
{
lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; 
v___x_2503_ = lean_obj_once(&l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__26, &l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__26_once, _init_l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__26);
v___x_2504_ = lean_obj_once(&l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__4, &l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__4_once, _init_l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__4);
v___x_2505_ = lean_string_append(v___x_2504_, v___x_2503_);
return v___x_2505_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__10(void){
_start:
{
lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; 
v___x_2506_ = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
v___x_2507_ = lean_obj_once(&l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__9, &l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__9_once, _init_l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__9);
v___x_2508_ = lean_string_append(v___x_2507_, v___x_2506_);
return v___x_2508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Firefox_instFromJsonResourceTable_fromJson(lean_object* v_json_2509_){
_start:
{
lean_object* v___x_2510_; lean_object* v___x_2511_; 
v___x_2510_ = ((lean_object*)(l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__0));
lean_inc(v_json_2509_);
v___x_2511_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__3(v_json_2509_, v___x_2510_);
if (lean_obj_tag(v___x_2511_) == 0)
{
lean_object* v_a_2512_; lean_object* v___x_2514_; uint8_t v_isShared_2515_; uint8_t v_isSharedCheck_2521_; 
lean_dec(v_json_2509_);
v_a_2512_ = lean_ctor_get(v___x_2511_, 0);
v_isSharedCheck_2521_ = !lean_is_exclusive(v___x_2511_);
if (v_isSharedCheck_2521_ == 0)
{
v___x_2514_ = v___x_2511_;
v_isShared_2515_ = v_isSharedCheck_2521_;
goto v_resetjp_2513_;
}
else
{
lean_inc(v_a_2512_);
lean_dec(v___x_2511_);
v___x_2514_ = lean_box(0);
v_isShared_2515_ = v_isSharedCheck_2521_;
goto v_resetjp_2513_;
}
v_resetjp_2513_:
{
lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2519_; 
v___x_2516_ = lean_obj_once(&l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__8, &l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__8_once, _init_l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__8);
v___x_2517_ = lean_string_append(v___x_2516_, v_a_2512_);
lean_dec(v_a_2512_);
if (v_isShared_2515_ == 0)
{
lean_ctor_set(v___x_2514_, 0, v___x_2517_);
v___x_2519_ = v___x_2514_;
goto v_reusejp_2518_;
}
else
{
lean_object* v_reuseFailAlloc_2520_; 
v_reuseFailAlloc_2520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2520_, 0, v___x_2517_);
v___x_2519_ = v_reuseFailAlloc_2520_;
goto v_reusejp_2518_;
}
v_reusejp_2518_:
{
return v___x_2519_;
}
}
}
else
{
lean_object* v_a_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; 
v_a_2522_ = lean_ctor_get(v___x_2511_, 0);
lean_inc(v_a_2522_);
lean_dec_ref_known(v___x_2511_, 1);
v___x_2523_ = ((lean_object*)(l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__24));
v___x_2524_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__2(v_json_2509_, v___x_2523_);
if (lean_obj_tag(v___x_2524_) == 0)
{
lean_object* v_a_2525_; lean_object* v___x_2527_; uint8_t v_isShared_2528_; uint8_t v_isSharedCheck_2534_; 
lean_dec(v_a_2522_);
v_a_2525_ = lean_ctor_get(v___x_2524_, 0);
v_isSharedCheck_2534_ = !lean_is_exclusive(v___x_2524_);
if (v_isSharedCheck_2534_ == 0)
{
v___x_2527_ = v___x_2524_;
v_isShared_2528_ = v_isSharedCheck_2534_;
goto v_resetjp_2526_;
}
else
{
lean_inc(v_a_2525_);
lean_dec(v___x_2524_);
v___x_2527_ = lean_box(0);
v_isShared_2528_ = v_isSharedCheck_2534_;
goto v_resetjp_2526_;
}
v_resetjp_2526_:
{
lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2532_; 
v___x_2529_ = lean_obj_once(&l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__10, &l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__10_once, _init_l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__10);
v___x_2530_ = lean_string_append(v___x_2529_, v_a_2525_);
lean_dec(v_a_2525_);
if (v_isShared_2528_ == 0)
{
lean_ctor_set(v___x_2527_, 0, v___x_2530_);
v___x_2532_ = v___x_2527_;
goto v_reusejp_2531_;
}
else
{
lean_object* v_reuseFailAlloc_2533_; 
v_reuseFailAlloc_2533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2533_, 0, v___x_2530_);
v___x_2532_ = v_reuseFailAlloc_2533_;
goto v_reusejp_2531_;
}
v_reusejp_2531_:
{
return v___x_2532_;
}
}
}
else
{
lean_object* v_a_2535_; lean_object* v___x_2537_; uint8_t v_isShared_2538_; uint8_t v_isSharedCheck_2543_; 
v_a_2535_ = lean_ctor_get(v___x_2524_, 0);
v_isSharedCheck_2543_ = !lean_is_exclusive(v___x_2524_);
if (v_isSharedCheck_2543_ == 0)
{
v___x_2537_ = v___x_2524_;
v_isShared_2538_ = v_isSharedCheck_2543_;
goto v_resetjp_2536_;
}
else
{
lean_inc(v_a_2535_);
lean_dec(v___x_2524_);
v___x_2537_ = lean_box(0);
v_isShared_2538_ = v_isSharedCheck_2543_;
goto v_resetjp_2536_;
}
v_resetjp_2536_:
{
lean_object* v___x_2539_; lean_object* v___x_2541_; 
v___x_2539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2539_, 0, v_a_2522_);
lean_ctor_set(v___x_2539_, 1, v_a_2535_);
if (v_isShared_2538_ == 0)
{
lean_ctor_set(v___x_2537_, 0, v___x_2539_);
v___x_2541_ = v___x_2537_;
goto v_reusejp_2540_;
}
else
{
lean_object* v_reuseFailAlloc_2542_; 
v_reuseFailAlloc_2542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2542_, 0, v___x_2539_);
v___x_2541_ = v_reuseFailAlloc_2542_;
goto v_reusejp_2540_;
}
v_reusejp_2540_:
{
return v___x_2541_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Firefox_instToJsonResourceTable_toJson(lean_object* v_x_2546_){
_start:
{
lean_object* v_type_2547_; lean_object* v_length_2548_; lean_object* v___x_2550_; uint8_t v_isShared_2551_; uint8_t v_isSharedCheck_2569_; 
v_type_2547_ = lean_ctor_get(v_x_2546_, 0);
v_length_2548_ = lean_ctor_get(v_x_2546_, 1);
v_isSharedCheck_2569_ = !lean_is_exclusive(v_x_2546_);
if (v_isSharedCheck_2569_ == 0)
{
v___x_2550_ = v_x_2546_;
v_isShared_2551_ = v_isSharedCheck_2569_;
goto v_resetjp_2549_;
}
else
{
lean_inc(v_length_2548_);
lean_inc(v_type_2547_);
lean_dec(v_x_2546_);
v___x_2550_ = lean_box(0);
v_isShared_2551_ = v_isSharedCheck_2569_;
goto v_resetjp_2549_;
}
v_resetjp_2549_:
{
lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2555_; 
v___x_2552_ = ((lean_object*)(l_Lean_Firefox_instFromJsonResourceTable_fromJson___closed__0));
v___x_2553_ = l_Lean_Array_toJson___at___00Lean_Firefox_instToJsonProfileMeta_toJson_spec__1(v_type_2547_);
if (v_isShared_2551_ == 0)
{
lean_ctor_set(v___x_2550_, 1, v___x_2553_);
lean_ctor_set(v___x_2550_, 0, v___x_2552_);
v___x_2555_ = v___x_2550_;
goto v_reusejp_2554_;
}
else
{
lean_object* v_reuseFailAlloc_2568_; 
v_reuseFailAlloc_2568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2568_, 0, v___x_2552_);
lean_ctor_set(v_reuseFailAlloc_2568_, 1, v___x_2553_);
v___x_2555_ = v_reuseFailAlloc_2568_;
goto v_reusejp_2554_;
}
v_reusejp_2554_:
{
lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; 
v___x_2556_ = lean_box(0);
v___x_2557_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2557_, 0, v___x_2555_);
lean_ctor_set(v___x_2557_, 1, v___x_2556_);
v___x_2558_ = ((lean_object*)(l_Lean_Firefox_instFromJsonStackTable_fromJson___closed__24));
v___x_2559_ = l_Lean_JsonNumber_fromNat(v_length_2548_);
v___x_2560_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2560_, 0, v___x_2559_);
v___x_2561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2561_, 0, v___x_2558_);
lean_ctor_set(v___x_2561_, 1, v___x_2560_);
v___x_2562_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2562_, 0, v___x_2561_);
lean_ctor_set(v___x_2562_, 1, v___x_2556_);
v___x_2563_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2563_, 0, v___x_2562_);
lean_ctor_set(v___x_2563_, 1, v___x_2556_);
v___x_2564_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2564_, 0, v___x_2557_);
lean_ctor_set(v___x_2564_, 1, v___x_2563_);
v___x_2565_ = ((lean_object*)(l_Lean_Firefox_instToJsonCategory_toJson___closed__0));
v___x_2566_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Firefox_instToJsonCategory_toJson_spec__1(v___x_2564_, v___x_2565_);
v___x_2567_ = l_Lean_Json_mkObj(v___x_2566_);
lean_dec(v___x_2566_);
return v___x_2567_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonThread_fromJson_spec__0(lean_object* v_j_2572_, lean_object* v_k_2573_){
_start:
{
lean_object* v___x_2574_; lean_object* v___x_2575_; 
v___x_2574_ = l_Lean_Json_getObjValD(v_j_2572_, v_k_2573_);
v___x_2575_ = l_Lean_Json_getBool_x3f(v___x_2574_);
lean_dec(v___x_2574_);
return v___x_2575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonThread_fromJson_spec__0___boxed(lean_object* v_j_2576_, lean_object* v_k_2577_){
_start:
{
lean_object* v_res_2578_; 
v_res_2578_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonThread_fromJson_spec__0(v_j_2576_, v_k_2577_);
lean_dec_ref(v_k_2577_);
return v_res_2578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonThread_fromJson_spec__1(lean_object* v_j_2579_, lean_object* v_k_2580_){
_start:
{
lean_object* v___x_2581_; lean_object* v___x_2582_; 
v___x_2581_ = l_Lean_Json_getObjValD(v_j_2579_, v_k_2580_);
v___x_2582_ = l_Lean_Firefox_instFromJsonSamplesTable_fromJson(v___x_2581_);
return v___x_2582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonThread_fromJson_spec__1___boxed(lean_object* v_j_2583_, lean_object* v_k_2584_){
_start:
{
lean_object* v_res_2585_; 
v_res_2585_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonThread_fromJson_spec__1(v_j_2583_, v_k_2584_);
lean_dec_ref(v_k_2584_);
return v_res_2585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonThread_fromJson_spec__2(lean_object* v_j_2586_, lean_object* v_k_2587_){
_start:
{
lean_object* v___x_2588_; lean_object* v___x_2589_; 
v___x_2588_ = l_Lean_Json_getObjValD(v_j_2586_, v_k_2587_);
v___x_2589_ = l_Lean_Firefox_instFromJsonRawMarkerTable_fromJson(v___x_2588_);
return v___x_2589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonThread_fromJson_spec__2___boxed(lean_object* v_j_2590_, lean_object* v_k_2591_){
_start:
{
lean_object* v_res_2592_; 
v_res_2592_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonThread_fromJson_spec__2(v_j_2590_, v_k_2591_);
lean_dec_ref(v_k_2591_);
return v_res_2592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonThread_fromJson_spec__3(lean_object* v_j_2593_, lean_object* v_k_2594_){
_start:
{
lean_object* v___x_2595_; lean_object* v___x_2596_; 
v___x_2595_ = l_Lean_Json_getObjValD(v_j_2593_, v_k_2594_);
v___x_2596_ = l_Lean_Firefox_instFromJsonStackTable_fromJson(v___x_2595_);
return v___x_2596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonThread_fromJson_spec__3___boxed(lean_object* v_j_2597_, lean_object* v_k_2598_){
_start:
{
lean_object* v_res_2599_; 
v_res_2599_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonThread_fromJson_spec__3(v_j_2597_, v_k_2598_);
lean_dec_ref(v_k_2598_);
return v_res_2599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonThread_fromJson_spec__4(lean_object* v_j_2600_, lean_object* v_k_2601_){
_start:
{
lean_object* v___x_2602_; lean_object* v___x_2603_; 
v___x_2602_ = l_Lean_Json_getObjValD(v_j_2600_, v_k_2601_);
v___x_2603_ = l_Lean_Firefox_instFromJsonFrameTable_fromJson(v___x_2602_);
return v___x_2603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonThread_fromJson_spec__4___boxed(lean_object* v_j_2604_, lean_object* v_k_2605_){
_start:
{
lean_object* v_res_2606_; 
v_res_2606_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonThread_fromJson_spec__4(v_j_2604_, v_k_2605_);
lean_dec_ref(v_k_2605_);
return v_res_2606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonThread_fromJson_spec__5(lean_object* v_j_2607_, lean_object* v_k_2608_){
_start:
{
lean_object* v___x_2609_; lean_object* v___x_2610_; 
v___x_2609_ = l_Lean_Json_getObjValD(v_j_2607_, v_k_2608_);
v___x_2610_ = l_Lean_Firefox_instFromJsonResourceTable_fromJson(v___x_2609_);
return v___x_2610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonThread_fromJson_spec__5___boxed(lean_object* v_j_2611_, lean_object* v_k_2612_){
_start:
{
lean_object* v_res_2613_; 
v_res_2613_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonThread_fromJson_spec__5(v_j_2611_, v_k_2612_);
lean_dec_ref(v_k_2612_);
return v_res_2613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonThread_fromJson_spec__6(lean_object* v_j_2614_, lean_object* v_k_2615_){
_start:
{
lean_object* v___x_2616_; lean_object* v___x_2617_; 
v___x_2616_ = l_Lean_Json_getObjValD(v_j_2614_, v_k_2615_);
v___x_2617_ = l_Lean_Firefox_instFromJsonFuncTable_fromJson(v___x_2616_);
return v___x_2617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonThread_fromJson_spec__6___boxed(lean_object* v_j_2618_, lean_object* v_k_2619_){
_start:
{
lean_object* v_res_2620_; 
v_res_2620_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonThread_fromJson_spec__6(v_j_2618_, v_k_2619_);
lean_dec_ref(v_k_2619_);
return v_res_2620_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__2(void){
_start:
{
uint8_t v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; 
v___x_2626_ = 1;
v___x_2627_ = ((lean_object*)(l_Lean_Firefox_instFromJsonThread_fromJson___closed__1));
v___x_2628_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2627_, v___x_2626_);
return v___x_2628_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__3(void){
_start:
{
lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; 
v___x_2629_ = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__6));
v___x_2630_ = lean_obj_once(&l_Lean_Firefox_instFromJsonThread_fromJson___closed__2, &l_Lean_Firefox_instFromJsonThread_fromJson___closed__2_once, _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__2);
v___x_2631_ = lean_string_append(v___x_2630_, v___x_2629_);
return v___x_2631_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__4(void){
_start:
{
lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; 
v___x_2632_ = lean_obj_once(&l_Lean_Firefox_instFromJsonCategory_fromJson___closed__9, &l_Lean_Firefox_instFromJsonCategory_fromJson___closed__9_once, _init_l_Lean_Firefox_instFromJsonCategory_fromJson___closed__9);
v___x_2633_ = lean_obj_once(&l_Lean_Firefox_instFromJsonThread_fromJson___closed__3, &l_Lean_Firefox_instFromJsonThread_fromJson___closed__3_once, _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__3);
v___x_2634_ = lean_string_append(v___x_2633_, v___x_2632_);
return v___x_2634_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__5(void){
_start:
{
lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; 
v___x_2635_ = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
v___x_2636_ = lean_obj_once(&l_Lean_Firefox_instFromJsonThread_fromJson___closed__4, &l_Lean_Firefox_instFromJsonThread_fromJson___closed__4_once, _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__4);
v___x_2637_ = lean_string_append(v___x_2636_, v___x_2635_);
return v___x_2637_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__6(void){
_start:
{
lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; 
v___x_2638_ = lean_obj_once(&l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__21, &l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__21_once, _init_l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__21);
v___x_2639_ = lean_obj_once(&l_Lean_Firefox_instFromJsonThread_fromJson___closed__3, &l_Lean_Firefox_instFromJsonThread_fromJson___closed__3_once, _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__3);
v___x_2640_ = lean_string_append(v___x_2639_, v___x_2638_);
return v___x_2640_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__7(void){
_start:
{
lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; 
v___x_2641_ = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
v___x_2642_ = lean_obj_once(&l_Lean_Firefox_instFromJsonThread_fromJson___closed__6, &l_Lean_Firefox_instFromJsonThread_fromJson___closed__6_once, _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__6);
v___x_2643_ = lean_string_append(v___x_2642_, v___x_2641_);
return v___x_2643_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__10(void){
_start:
{
uint8_t v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; 
v___x_2647_ = 1;
v___x_2648_ = ((lean_object*)(l_Lean_Firefox_instFromJsonThread_fromJson___closed__9));
v___x_2649_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2648_, v___x_2647_);
return v___x_2649_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__11(void){
_start:
{
lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; 
v___x_2650_ = lean_obj_once(&l_Lean_Firefox_instFromJsonThread_fromJson___closed__10, &l_Lean_Firefox_instFromJsonThread_fromJson___closed__10_once, _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__10);
v___x_2651_ = lean_obj_once(&l_Lean_Firefox_instFromJsonThread_fromJson___closed__3, &l_Lean_Firefox_instFromJsonThread_fromJson___closed__3_once, _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__3);
v___x_2652_ = lean_string_append(v___x_2651_, v___x_2650_);
return v___x_2652_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__12(void){
_start:
{
lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; 
v___x_2653_ = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
v___x_2654_ = lean_obj_once(&l_Lean_Firefox_instFromJsonThread_fromJson___closed__11, &l_Lean_Firefox_instFromJsonThread_fromJson___closed__11_once, _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__11);
v___x_2655_ = lean_string_append(v___x_2654_, v___x_2653_);
return v___x_2655_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__15(void){
_start:
{
uint8_t v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; 
v___x_2659_ = 1;
v___x_2660_ = ((lean_object*)(l_Lean_Firefox_instFromJsonThread_fromJson___closed__14));
v___x_2661_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2660_, v___x_2659_);
return v___x_2661_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__16(void){
_start:
{
lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; 
v___x_2662_ = lean_obj_once(&l_Lean_Firefox_instFromJsonThread_fromJson___closed__15, &l_Lean_Firefox_instFromJsonThread_fromJson___closed__15_once, _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__15);
v___x_2663_ = lean_obj_once(&l_Lean_Firefox_instFromJsonThread_fromJson___closed__3, &l_Lean_Firefox_instFromJsonThread_fromJson___closed__3_once, _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__3);
v___x_2664_ = lean_string_append(v___x_2663_, v___x_2662_);
return v___x_2664_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__17(void){
_start:
{
lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; 
v___x_2665_ = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
v___x_2666_ = lean_obj_once(&l_Lean_Firefox_instFromJsonThread_fromJson___closed__16, &l_Lean_Firefox_instFromJsonThread_fromJson___closed__16_once, _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__16);
v___x_2667_ = lean_string_append(v___x_2666_, v___x_2665_);
return v___x_2667_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__20(void){
_start:
{
uint8_t v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; 
v___x_2671_ = 1;
v___x_2672_ = ((lean_object*)(l_Lean_Firefox_instFromJsonThread_fromJson___closed__19));
v___x_2673_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2672_, v___x_2671_);
return v___x_2673_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__21(void){
_start:
{
lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; 
v___x_2674_ = lean_obj_once(&l_Lean_Firefox_instFromJsonThread_fromJson___closed__20, &l_Lean_Firefox_instFromJsonThread_fromJson___closed__20_once, _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__20);
v___x_2675_ = lean_obj_once(&l_Lean_Firefox_instFromJsonThread_fromJson___closed__3, &l_Lean_Firefox_instFromJsonThread_fromJson___closed__3_once, _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__3);
v___x_2676_ = lean_string_append(v___x_2675_, v___x_2674_);
return v___x_2676_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__22(void){
_start:
{
lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; 
v___x_2677_ = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
v___x_2678_ = lean_obj_once(&l_Lean_Firefox_instFromJsonThread_fromJson___closed__21, &l_Lean_Firefox_instFromJsonThread_fromJson___closed__21_once, _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__21);
v___x_2679_ = lean_string_append(v___x_2678_, v___x_2677_);
return v___x_2679_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__25(void){
_start:
{
uint8_t v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; 
v___x_2683_ = 1;
v___x_2684_ = ((lean_object*)(l_Lean_Firefox_instFromJsonThread_fromJson___closed__24));
v___x_2685_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2684_, v___x_2683_);
return v___x_2685_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__26(void){
_start:
{
lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; 
v___x_2686_ = lean_obj_once(&l_Lean_Firefox_instFromJsonThread_fromJson___closed__25, &l_Lean_Firefox_instFromJsonThread_fromJson___closed__25_once, _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__25);
v___x_2687_ = lean_obj_once(&l_Lean_Firefox_instFromJsonThread_fromJson___closed__3, &l_Lean_Firefox_instFromJsonThread_fromJson___closed__3_once, _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__3);
v___x_2688_ = lean_string_append(v___x_2687_, v___x_2686_);
return v___x_2688_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__27(void){
_start:
{
lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; 
v___x_2689_ = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
v___x_2690_ = lean_obj_once(&l_Lean_Firefox_instFromJsonThread_fromJson___closed__26, &l_Lean_Firefox_instFromJsonThread_fromJson___closed__26_once, _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__26);
v___x_2691_ = lean_string_append(v___x_2690_, v___x_2689_);
return v___x_2691_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__30(void){
_start:
{
uint8_t v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; 
v___x_2695_ = 1;
v___x_2696_ = ((lean_object*)(l_Lean_Firefox_instFromJsonThread_fromJson___closed__29));
v___x_2697_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2696_, v___x_2695_);
return v___x_2697_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__31(void){
_start:
{
lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; 
v___x_2698_ = lean_obj_once(&l_Lean_Firefox_instFromJsonThread_fromJson___closed__30, &l_Lean_Firefox_instFromJsonThread_fromJson___closed__30_once, _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__30);
v___x_2699_ = lean_obj_once(&l_Lean_Firefox_instFromJsonThread_fromJson___closed__3, &l_Lean_Firefox_instFromJsonThread_fromJson___closed__3_once, _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__3);
v___x_2700_ = lean_string_append(v___x_2699_, v___x_2698_);
return v___x_2700_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__32(void){
_start:
{
lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; 
v___x_2701_ = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
v___x_2702_ = lean_obj_once(&l_Lean_Firefox_instFromJsonThread_fromJson___closed__31, &l_Lean_Firefox_instFromJsonThread_fromJson___closed__31_once, _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__31);
v___x_2703_ = lean_string_append(v___x_2702_, v___x_2701_);
return v___x_2703_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__35(void){
_start:
{
uint8_t v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; 
v___x_2707_ = 1;
v___x_2708_ = ((lean_object*)(l_Lean_Firefox_instFromJsonThread_fromJson___closed__34));
v___x_2709_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2708_, v___x_2707_);
return v___x_2709_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__36(void){
_start:
{
lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; 
v___x_2710_ = lean_obj_once(&l_Lean_Firefox_instFromJsonThread_fromJson___closed__35, &l_Lean_Firefox_instFromJsonThread_fromJson___closed__35_once, _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__35);
v___x_2711_ = lean_obj_once(&l_Lean_Firefox_instFromJsonThread_fromJson___closed__3, &l_Lean_Firefox_instFromJsonThread_fromJson___closed__3_once, _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__3);
v___x_2712_ = lean_string_append(v___x_2711_, v___x_2710_);
return v___x_2712_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__37(void){
_start:
{
lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; 
v___x_2713_ = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
v___x_2714_ = lean_obj_once(&l_Lean_Firefox_instFromJsonThread_fromJson___closed__36, &l_Lean_Firefox_instFromJsonThread_fromJson___closed__36_once, _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__36);
v___x_2715_ = lean_string_append(v___x_2714_, v___x_2713_);
return v___x_2715_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__40(void){
_start:
{
uint8_t v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; 
v___x_2719_ = 1;
v___x_2720_ = ((lean_object*)(l_Lean_Firefox_instFromJsonThread_fromJson___closed__39));
v___x_2721_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2720_, v___x_2719_);
return v___x_2721_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__41(void){
_start:
{
lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; 
v___x_2722_ = lean_obj_once(&l_Lean_Firefox_instFromJsonThread_fromJson___closed__40, &l_Lean_Firefox_instFromJsonThread_fromJson___closed__40_once, _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__40);
v___x_2723_ = lean_obj_once(&l_Lean_Firefox_instFromJsonThread_fromJson___closed__3, &l_Lean_Firefox_instFromJsonThread_fromJson___closed__3_once, _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__3);
v___x_2724_ = lean_string_append(v___x_2723_, v___x_2722_);
return v___x_2724_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__42(void){
_start:
{
lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; 
v___x_2725_ = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
v___x_2726_ = lean_obj_once(&l_Lean_Firefox_instFromJsonThread_fromJson___closed__41, &l_Lean_Firefox_instFromJsonThread_fromJson___closed__41_once, _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__41);
v___x_2727_ = lean_string_append(v___x_2726_, v___x_2725_);
return v___x_2727_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__45(void){
_start:
{
uint8_t v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; 
v___x_2731_ = 1;
v___x_2732_ = ((lean_object*)(l_Lean_Firefox_instFromJsonThread_fromJson___closed__44));
v___x_2733_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2732_, v___x_2731_);
return v___x_2733_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__46(void){
_start:
{
lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; 
v___x_2734_ = lean_obj_once(&l_Lean_Firefox_instFromJsonThread_fromJson___closed__45, &l_Lean_Firefox_instFromJsonThread_fromJson___closed__45_once, _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__45);
v___x_2735_ = lean_obj_once(&l_Lean_Firefox_instFromJsonThread_fromJson___closed__3, &l_Lean_Firefox_instFromJsonThread_fromJson___closed__3_once, _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__3);
v___x_2736_ = lean_string_append(v___x_2735_, v___x_2734_);
return v___x_2736_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__47(void){
_start:
{
lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; 
v___x_2737_ = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
v___x_2738_ = lean_obj_once(&l_Lean_Firefox_instFromJsonThread_fromJson___closed__46, &l_Lean_Firefox_instFromJsonThread_fromJson___closed__46_once, _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__46);
v___x_2739_ = lean_string_append(v___x_2738_, v___x_2737_);
return v___x_2739_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__50(void){
_start:
{
uint8_t v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; 
v___x_2743_ = 1;
v___x_2744_ = ((lean_object*)(l_Lean_Firefox_instFromJsonThread_fromJson___closed__49));
v___x_2745_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2744_, v___x_2743_);
return v___x_2745_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__51(void){
_start:
{
lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; 
v___x_2746_ = lean_obj_once(&l_Lean_Firefox_instFromJsonThread_fromJson___closed__50, &l_Lean_Firefox_instFromJsonThread_fromJson___closed__50_once, _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__50);
v___x_2747_ = lean_obj_once(&l_Lean_Firefox_instFromJsonThread_fromJson___closed__3, &l_Lean_Firefox_instFromJsonThread_fromJson___closed__3_once, _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__3);
v___x_2748_ = lean_string_append(v___x_2747_, v___x_2746_);
return v___x_2748_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__52(void){
_start:
{
lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; 
v___x_2749_ = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
v___x_2750_ = lean_obj_once(&l_Lean_Firefox_instFromJsonThread_fromJson___closed__51, &l_Lean_Firefox_instFromJsonThread_fromJson___closed__51_once, _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__51);
v___x_2751_ = lean_string_append(v___x_2750_, v___x_2749_);
return v___x_2751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Firefox_instFromJsonThread_fromJson(lean_object* v_json_2752_){
_start:
{
lean_object* v___x_2753_; lean_object* v___x_2754_; 
v___x_2753_ = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__0));
lean_inc(v_json_2752_);
v___x_2754_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__1(v_json_2752_, v___x_2753_);
if (lean_obj_tag(v___x_2754_) == 0)
{
lean_object* v_a_2755_; lean_object* v___x_2757_; uint8_t v_isShared_2758_; uint8_t v_isSharedCheck_2764_; 
lean_dec(v_json_2752_);
v_a_2755_ = lean_ctor_get(v___x_2754_, 0);
v_isSharedCheck_2764_ = !lean_is_exclusive(v___x_2754_);
if (v_isSharedCheck_2764_ == 0)
{
v___x_2757_ = v___x_2754_;
v_isShared_2758_ = v_isSharedCheck_2764_;
goto v_resetjp_2756_;
}
else
{
lean_inc(v_a_2755_);
lean_dec(v___x_2754_);
v___x_2757_ = lean_box(0);
v_isShared_2758_ = v_isSharedCheck_2764_;
goto v_resetjp_2756_;
}
v_resetjp_2756_:
{
lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2762_; 
v___x_2759_ = lean_obj_once(&l_Lean_Firefox_instFromJsonThread_fromJson___closed__5, &l_Lean_Firefox_instFromJsonThread_fromJson___closed__5_once, _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__5);
v___x_2760_ = lean_string_append(v___x_2759_, v_a_2755_);
lean_dec(v_a_2755_);
if (v_isShared_2758_ == 0)
{
lean_ctor_set(v___x_2757_, 0, v___x_2760_);
v___x_2762_ = v___x_2757_;
goto v_reusejp_2761_;
}
else
{
lean_object* v_reuseFailAlloc_2763_; 
v_reuseFailAlloc_2763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2763_, 0, v___x_2760_);
v___x_2762_ = v_reuseFailAlloc_2763_;
goto v_reusejp_2761_;
}
v_reusejp_2761_:
{
return v___x_2762_;
}
}
}
else
{
lean_object* v_a_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; 
v_a_2765_ = lean_ctor_get(v___x_2754_, 0);
lean_inc(v_a_2765_);
lean_dec_ref_known(v___x_2754_, 1);
v___x_2766_ = ((lean_object*)(l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__19));
lean_inc(v_json_2752_);
v___x_2767_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__1(v_json_2752_, v___x_2766_);
if (lean_obj_tag(v___x_2767_) == 0)
{
lean_object* v_a_2768_; lean_object* v___x_2770_; uint8_t v_isShared_2771_; uint8_t v_isSharedCheck_2777_; 
lean_dec(v_a_2765_);
lean_dec(v_json_2752_);
v_a_2768_ = lean_ctor_get(v___x_2767_, 0);
v_isSharedCheck_2777_ = !lean_is_exclusive(v___x_2767_);
if (v_isSharedCheck_2777_ == 0)
{
v___x_2770_ = v___x_2767_;
v_isShared_2771_ = v_isSharedCheck_2777_;
goto v_resetjp_2769_;
}
else
{
lean_inc(v_a_2768_);
lean_dec(v___x_2767_);
v___x_2770_ = lean_box(0);
v_isShared_2771_ = v_isSharedCheck_2777_;
goto v_resetjp_2769_;
}
v_resetjp_2769_:
{
lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2775_; 
v___x_2772_ = lean_obj_once(&l_Lean_Firefox_instFromJsonThread_fromJson___closed__7, &l_Lean_Firefox_instFromJsonThread_fromJson___closed__7_once, _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__7);
v___x_2773_ = lean_string_append(v___x_2772_, v_a_2768_);
lean_dec(v_a_2768_);
if (v_isShared_2771_ == 0)
{
lean_ctor_set(v___x_2770_, 0, v___x_2773_);
v___x_2775_ = v___x_2770_;
goto v_reusejp_2774_;
}
else
{
lean_object* v_reuseFailAlloc_2776_; 
v_reuseFailAlloc_2776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2776_, 0, v___x_2773_);
v___x_2775_ = v_reuseFailAlloc_2776_;
goto v_reusejp_2774_;
}
v_reusejp_2774_:
{
return v___x_2775_;
}
}
}
else
{
lean_object* v_a_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; 
v_a_2778_ = lean_ctor_get(v___x_2767_, 0);
lean_inc(v_a_2778_);
lean_dec_ref_known(v___x_2767_, 1);
v___x_2779_ = ((lean_object*)(l_Lean_Firefox_instFromJsonThread_fromJson___closed__8));
lean_inc(v_json_2752_);
v___x_2780_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonThread_fromJson_spec__0(v_json_2752_, v___x_2779_);
if (lean_obj_tag(v___x_2780_) == 0)
{
lean_object* v_a_2781_; lean_object* v___x_2783_; uint8_t v_isShared_2784_; uint8_t v_isSharedCheck_2790_; 
lean_dec(v_a_2778_);
lean_dec(v_a_2765_);
lean_dec(v_json_2752_);
v_a_2781_ = lean_ctor_get(v___x_2780_, 0);
v_isSharedCheck_2790_ = !lean_is_exclusive(v___x_2780_);
if (v_isSharedCheck_2790_ == 0)
{
v___x_2783_ = v___x_2780_;
v_isShared_2784_ = v_isSharedCheck_2790_;
goto v_resetjp_2782_;
}
else
{
lean_inc(v_a_2781_);
lean_dec(v___x_2780_);
v___x_2783_ = lean_box(0);
v_isShared_2784_ = v_isSharedCheck_2790_;
goto v_resetjp_2782_;
}
v_resetjp_2782_:
{
lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2788_; 
v___x_2785_ = lean_obj_once(&l_Lean_Firefox_instFromJsonThread_fromJson___closed__12, &l_Lean_Firefox_instFromJsonThread_fromJson___closed__12_once, _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__12);
v___x_2786_ = lean_string_append(v___x_2785_, v_a_2781_);
lean_dec(v_a_2781_);
if (v_isShared_2784_ == 0)
{
lean_ctor_set(v___x_2783_, 0, v___x_2786_);
v___x_2788_ = v___x_2783_;
goto v_reusejp_2787_;
}
else
{
lean_object* v_reuseFailAlloc_2789_; 
v_reuseFailAlloc_2789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2789_, 0, v___x_2786_);
v___x_2788_ = v_reuseFailAlloc_2789_;
goto v_reusejp_2787_;
}
v_reusejp_2787_:
{
return v___x_2788_;
}
}
}
else
{
lean_object* v_a_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; 
v_a_2791_ = lean_ctor_get(v___x_2780_, 0);
lean_inc(v_a_2791_);
lean_dec_ref_known(v___x_2780_, 1);
v___x_2792_ = ((lean_object*)(l_Lean_Firefox_instFromJsonThread_fromJson___closed__13));
lean_inc(v_json_2752_);
v___x_2793_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonThread_fromJson_spec__1(v_json_2752_, v___x_2792_);
if (lean_obj_tag(v___x_2793_) == 0)
{
lean_object* v_a_2794_; lean_object* v___x_2796_; uint8_t v_isShared_2797_; uint8_t v_isSharedCheck_2803_; 
lean_dec(v_a_2791_);
lean_dec(v_a_2778_);
lean_dec(v_a_2765_);
lean_dec(v_json_2752_);
v_a_2794_ = lean_ctor_get(v___x_2793_, 0);
v_isSharedCheck_2803_ = !lean_is_exclusive(v___x_2793_);
if (v_isSharedCheck_2803_ == 0)
{
v___x_2796_ = v___x_2793_;
v_isShared_2797_ = v_isSharedCheck_2803_;
goto v_resetjp_2795_;
}
else
{
lean_inc(v_a_2794_);
lean_dec(v___x_2793_);
v___x_2796_ = lean_box(0);
v_isShared_2797_ = v_isSharedCheck_2803_;
goto v_resetjp_2795_;
}
v_resetjp_2795_:
{
lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2801_; 
v___x_2798_ = lean_obj_once(&l_Lean_Firefox_instFromJsonThread_fromJson___closed__17, &l_Lean_Firefox_instFromJsonThread_fromJson___closed__17_once, _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__17);
v___x_2799_ = lean_string_append(v___x_2798_, v_a_2794_);
lean_dec(v_a_2794_);
if (v_isShared_2797_ == 0)
{
lean_ctor_set(v___x_2796_, 0, v___x_2799_);
v___x_2801_ = v___x_2796_;
goto v_reusejp_2800_;
}
else
{
lean_object* v_reuseFailAlloc_2802_; 
v_reuseFailAlloc_2802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2802_, 0, v___x_2799_);
v___x_2801_ = v_reuseFailAlloc_2802_;
goto v_reusejp_2800_;
}
v_reusejp_2800_:
{
return v___x_2801_;
}
}
}
else
{
lean_object* v_a_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; 
v_a_2804_ = lean_ctor_get(v___x_2793_, 0);
lean_inc(v_a_2804_);
lean_dec_ref_known(v___x_2793_, 1);
v___x_2805_ = ((lean_object*)(l_Lean_Firefox_instFromJsonThread_fromJson___closed__18));
lean_inc(v_json_2752_);
v___x_2806_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonThread_fromJson_spec__2(v_json_2752_, v___x_2805_);
if (lean_obj_tag(v___x_2806_) == 0)
{
lean_object* v_a_2807_; lean_object* v___x_2809_; uint8_t v_isShared_2810_; uint8_t v_isSharedCheck_2816_; 
lean_dec(v_a_2804_);
lean_dec(v_a_2791_);
lean_dec(v_a_2778_);
lean_dec(v_a_2765_);
lean_dec(v_json_2752_);
v_a_2807_ = lean_ctor_get(v___x_2806_, 0);
v_isSharedCheck_2816_ = !lean_is_exclusive(v___x_2806_);
if (v_isSharedCheck_2816_ == 0)
{
v___x_2809_ = v___x_2806_;
v_isShared_2810_ = v_isSharedCheck_2816_;
goto v_resetjp_2808_;
}
else
{
lean_inc(v_a_2807_);
lean_dec(v___x_2806_);
v___x_2809_ = lean_box(0);
v_isShared_2810_ = v_isSharedCheck_2816_;
goto v_resetjp_2808_;
}
v_resetjp_2808_:
{
lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2814_; 
v___x_2811_ = lean_obj_once(&l_Lean_Firefox_instFromJsonThread_fromJson___closed__22, &l_Lean_Firefox_instFromJsonThread_fromJson___closed__22_once, _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__22);
v___x_2812_ = lean_string_append(v___x_2811_, v_a_2807_);
lean_dec(v_a_2807_);
if (v_isShared_2810_ == 0)
{
lean_ctor_set(v___x_2809_, 0, v___x_2812_);
v___x_2814_ = v___x_2809_;
goto v_reusejp_2813_;
}
else
{
lean_object* v_reuseFailAlloc_2815_; 
v_reuseFailAlloc_2815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2815_, 0, v___x_2812_);
v___x_2814_ = v_reuseFailAlloc_2815_;
goto v_reusejp_2813_;
}
v_reusejp_2813_:
{
return v___x_2814_;
}
}
}
else
{
lean_object* v_a_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; 
v_a_2817_ = lean_ctor_get(v___x_2806_, 0);
lean_inc(v_a_2817_);
lean_dec_ref_known(v___x_2806_, 1);
v___x_2818_ = ((lean_object*)(l_Lean_Firefox_instFromJsonThread_fromJson___closed__23));
lean_inc(v_json_2752_);
v___x_2819_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonThread_fromJson_spec__3(v_json_2752_, v___x_2818_);
if (lean_obj_tag(v___x_2819_) == 0)
{
lean_object* v_a_2820_; lean_object* v___x_2822_; uint8_t v_isShared_2823_; uint8_t v_isSharedCheck_2829_; 
lean_dec(v_a_2817_);
lean_dec(v_a_2804_);
lean_dec(v_a_2791_);
lean_dec(v_a_2778_);
lean_dec(v_a_2765_);
lean_dec(v_json_2752_);
v_a_2820_ = lean_ctor_get(v___x_2819_, 0);
v_isSharedCheck_2829_ = !lean_is_exclusive(v___x_2819_);
if (v_isSharedCheck_2829_ == 0)
{
v___x_2822_ = v___x_2819_;
v_isShared_2823_ = v_isSharedCheck_2829_;
goto v_resetjp_2821_;
}
else
{
lean_inc(v_a_2820_);
lean_dec(v___x_2819_);
v___x_2822_ = lean_box(0);
v_isShared_2823_ = v_isSharedCheck_2829_;
goto v_resetjp_2821_;
}
v_resetjp_2821_:
{
lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2827_; 
v___x_2824_ = lean_obj_once(&l_Lean_Firefox_instFromJsonThread_fromJson___closed__27, &l_Lean_Firefox_instFromJsonThread_fromJson___closed__27_once, _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__27);
v___x_2825_ = lean_string_append(v___x_2824_, v_a_2820_);
lean_dec(v_a_2820_);
if (v_isShared_2823_ == 0)
{
lean_ctor_set(v___x_2822_, 0, v___x_2825_);
v___x_2827_ = v___x_2822_;
goto v_reusejp_2826_;
}
else
{
lean_object* v_reuseFailAlloc_2828_; 
v_reuseFailAlloc_2828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2828_, 0, v___x_2825_);
v___x_2827_ = v_reuseFailAlloc_2828_;
goto v_reusejp_2826_;
}
v_reusejp_2826_:
{
return v___x_2827_;
}
}
}
else
{
lean_object* v_a_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; 
v_a_2830_ = lean_ctor_get(v___x_2819_, 0);
lean_inc(v_a_2830_);
lean_dec_ref_known(v___x_2819_, 1);
v___x_2831_ = ((lean_object*)(l_Lean_Firefox_instFromJsonThread_fromJson___closed__28));
lean_inc(v_json_2752_);
v___x_2832_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonThread_fromJson_spec__4(v_json_2752_, v___x_2831_);
if (lean_obj_tag(v___x_2832_) == 0)
{
lean_object* v_a_2833_; lean_object* v___x_2835_; uint8_t v_isShared_2836_; uint8_t v_isSharedCheck_2842_; 
lean_dec(v_a_2830_);
lean_dec(v_a_2817_);
lean_dec(v_a_2804_);
lean_dec(v_a_2791_);
lean_dec(v_a_2778_);
lean_dec(v_a_2765_);
lean_dec(v_json_2752_);
v_a_2833_ = lean_ctor_get(v___x_2832_, 0);
v_isSharedCheck_2842_ = !lean_is_exclusive(v___x_2832_);
if (v_isSharedCheck_2842_ == 0)
{
v___x_2835_ = v___x_2832_;
v_isShared_2836_ = v_isSharedCheck_2842_;
goto v_resetjp_2834_;
}
else
{
lean_inc(v_a_2833_);
lean_dec(v___x_2832_);
v___x_2835_ = lean_box(0);
v_isShared_2836_ = v_isSharedCheck_2842_;
goto v_resetjp_2834_;
}
v_resetjp_2834_:
{
lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2840_; 
v___x_2837_ = lean_obj_once(&l_Lean_Firefox_instFromJsonThread_fromJson___closed__32, &l_Lean_Firefox_instFromJsonThread_fromJson___closed__32_once, _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__32);
v___x_2838_ = lean_string_append(v___x_2837_, v_a_2833_);
lean_dec(v_a_2833_);
if (v_isShared_2836_ == 0)
{
lean_ctor_set(v___x_2835_, 0, v___x_2838_);
v___x_2840_ = v___x_2835_;
goto v_reusejp_2839_;
}
else
{
lean_object* v_reuseFailAlloc_2841_; 
v_reuseFailAlloc_2841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2841_, 0, v___x_2838_);
v___x_2840_ = v_reuseFailAlloc_2841_;
goto v_reusejp_2839_;
}
v_reusejp_2839_:
{
return v___x_2840_;
}
}
}
else
{
lean_object* v_a_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; 
v_a_2843_ = lean_ctor_get(v___x_2832_, 0);
lean_inc(v_a_2843_);
lean_dec_ref_known(v___x_2832_, 1);
v___x_2844_ = ((lean_object*)(l_Lean_Firefox_instFromJsonThread_fromJson___closed__33));
lean_inc(v_json_2752_);
v___x_2845_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonThread_fromJson_spec__5(v_json_2752_, v___x_2844_);
if (lean_obj_tag(v___x_2845_) == 0)
{
lean_object* v_a_2846_; lean_object* v___x_2848_; uint8_t v_isShared_2849_; uint8_t v_isSharedCheck_2855_; 
lean_dec(v_a_2843_);
lean_dec(v_a_2830_);
lean_dec(v_a_2817_);
lean_dec(v_a_2804_);
lean_dec(v_a_2791_);
lean_dec(v_a_2778_);
lean_dec(v_a_2765_);
lean_dec(v_json_2752_);
v_a_2846_ = lean_ctor_get(v___x_2845_, 0);
v_isSharedCheck_2855_ = !lean_is_exclusive(v___x_2845_);
if (v_isSharedCheck_2855_ == 0)
{
v___x_2848_ = v___x_2845_;
v_isShared_2849_ = v_isSharedCheck_2855_;
goto v_resetjp_2847_;
}
else
{
lean_inc(v_a_2846_);
lean_dec(v___x_2845_);
v___x_2848_ = lean_box(0);
v_isShared_2849_ = v_isSharedCheck_2855_;
goto v_resetjp_2847_;
}
v_resetjp_2847_:
{
lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2853_; 
v___x_2850_ = lean_obj_once(&l_Lean_Firefox_instFromJsonThread_fromJson___closed__37, &l_Lean_Firefox_instFromJsonThread_fromJson___closed__37_once, _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__37);
v___x_2851_ = lean_string_append(v___x_2850_, v_a_2846_);
lean_dec(v_a_2846_);
if (v_isShared_2849_ == 0)
{
lean_ctor_set(v___x_2848_, 0, v___x_2851_);
v___x_2853_ = v___x_2848_;
goto v_reusejp_2852_;
}
else
{
lean_object* v_reuseFailAlloc_2854_; 
v_reuseFailAlloc_2854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2854_, 0, v___x_2851_);
v___x_2853_ = v_reuseFailAlloc_2854_;
goto v_reusejp_2852_;
}
v_reusejp_2852_:
{
return v___x_2853_;
}
}
}
else
{
lean_object* v_a_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; 
v_a_2856_ = lean_ctor_get(v___x_2845_, 0);
lean_inc(v_a_2856_);
lean_dec_ref_known(v___x_2845_, 1);
v___x_2857_ = ((lean_object*)(l_Lean_Firefox_instFromJsonThread_fromJson___closed__38));
lean_inc(v_json_2752_);
v___x_2858_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonThread_fromJson_spec__5(v_json_2752_, v___x_2857_);
if (lean_obj_tag(v___x_2858_) == 0)
{
lean_object* v_a_2859_; lean_object* v___x_2861_; uint8_t v_isShared_2862_; uint8_t v_isSharedCheck_2868_; 
lean_dec(v_a_2856_);
lean_dec(v_a_2843_);
lean_dec(v_a_2830_);
lean_dec(v_a_2817_);
lean_dec(v_a_2804_);
lean_dec(v_a_2791_);
lean_dec(v_a_2778_);
lean_dec(v_a_2765_);
lean_dec(v_json_2752_);
v_a_2859_ = lean_ctor_get(v___x_2858_, 0);
v_isSharedCheck_2868_ = !lean_is_exclusive(v___x_2858_);
if (v_isSharedCheck_2868_ == 0)
{
v___x_2861_ = v___x_2858_;
v_isShared_2862_ = v_isSharedCheck_2868_;
goto v_resetjp_2860_;
}
else
{
lean_inc(v_a_2859_);
lean_dec(v___x_2858_);
v___x_2861_ = lean_box(0);
v_isShared_2862_ = v_isSharedCheck_2868_;
goto v_resetjp_2860_;
}
v_resetjp_2860_:
{
lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2866_; 
v___x_2863_ = lean_obj_once(&l_Lean_Firefox_instFromJsonThread_fromJson___closed__42, &l_Lean_Firefox_instFromJsonThread_fromJson___closed__42_once, _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__42);
v___x_2864_ = lean_string_append(v___x_2863_, v_a_2859_);
lean_dec(v_a_2859_);
if (v_isShared_2862_ == 0)
{
lean_ctor_set(v___x_2861_, 0, v___x_2864_);
v___x_2866_ = v___x_2861_;
goto v_reusejp_2865_;
}
else
{
lean_object* v_reuseFailAlloc_2867_; 
v_reuseFailAlloc_2867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2867_, 0, v___x_2864_);
v___x_2866_ = v_reuseFailAlloc_2867_;
goto v_reusejp_2865_;
}
v_reusejp_2865_:
{
return v___x_2866_;
}
}
}
else
{
lean_object* v_a_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; 
v_a_2869_ = lean_ctor_get(v___x_2858_, 0);
lean_inc(v_a_2869_);
lean_dec_ref_known(v___x_2858_, 1);
v___x_2870_ = ((lean_object*)(l_Lean_Firefox_instFromJsonThread_fromJson___closed__43));
lean_inc(v_json_2752_);
v___x_2871_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__2(v_json_2752_, v___x_2870_);
if (lean_obj_tag(v___x_2871_) == 0)
{
lean_object* v_a_2872_; lean_object* v___x_2874_; uint8_t v_isShared_2875_; uint8_t v_isSharedCheck_2881_; 
lean_dec(v_a_2869_);
lean_dec(v_a_2856_);
lean_dec(v_a_2843_);
lean_dec(v_a_2830_);
lean_dec(v_a_2817_);
lean_dec(v_a_2804_);
lean_dec(v_a_2791_);
lean_dec(v_a_2778_);
lean_dec(v_a_2765_);
lean_dec(v_json_2752_);
v_a_2872_ = lean_ctor_get(v___x_2871_, 0);
v_isSharedCheck_2881_ = !lean_is_exclusive(v___x_2871_);
if (v_isSharedCheck_2881_ == 0)
{
v___x_2874_ = v___x_2871_;
v_isShared_2875_ = v_isSharedCheck_2881_;
goto v_resetjp_2873_;
}
else
{
lean_inc(v_a_2872_);
lean_dec(v___x_2871_);
v___x_2874_ = lean_box(0);
v_isShared_2875_ = v_isSharedCheck_2881_;
goto v_resetjp_2873_;
}
v_resetjp_2873_:
{
lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2879_; 
v___x_2876_ = lean_obj_once(&l_Lean_Firefox_instFromJsonThread_fromJson___closed__47, &l_Lean_Firefox_instFromJsonThread_fromJson___closed__47_once, _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__47);
v___x_2877_ = lean_string_append(v___x_2876_, v_a_2872_);
lean_dec(v_a_2872_);
if (v_isShared_2875_ == 0)
{
lean_ctor_set(v___x_2874_, 0, v___x_2877_);
v___x_2879_ = v___x_2874_;
goto v_reusejp_2878_;
}
else
{
lean_object* v_reuseFailAlloc_2880_; 
v_reuseFailAlloc_2880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2880_, 0, v___x_2877_);
v___x_2879_ = v_reuseFailAlloc_2880_;
goto v_reusejp_2878_;
}
v_reusejp_2878_:
{
return v___x_2879_;
}
}
}
else
{
lean_object* v_a_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; 
v_a_2882_ = lean_ctor_get(v___x_2871_, 0);
lean_inc(v_a_2882_);
lean_dec_ref_known(v___x_2871_, 1);
v___x_2883_ = ((lean_object*)(l_Lean_Firefox_instFromJsonThread_fromJson___closed__48));
v___x_2884_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonThread_fromJson_spec__6(v_json_2752_, v___x_2883_);
if (lean_obj_tag(v___x_2884_) == 0)
{
lean_object* v_a_2885_; lean_object* v___x_2887_; uint8_t v_isShared_2888_; uint8_t v_isSharedCheck_2894_; 
lean_dec(v_a_2882_);
lean_dec(v_a_2869_);
lean_dec(v_a_2856_);
lean_dec(v_a_2843_);
lean_dec(v_a_2830_);
lean_dec(v_a_2817_);
lean_dec(v_a_2804_);
lean_dec(v_a_2791_);
lean_dec(v_a_2778_);
lean_dec(v_a_2765_);
v_a_2885_ = lean_ctor_get(v___x_2884_, 0);
v_isSharedCheck_2894_ = !lean_is_exclusive(v___x_2884_);
if (v_isSharedCheck_2894_ == 0)
{
v___x_2887_ = v___x_2884_;
v_isShared_2888_ = v_isSharedCheck_2894_;
goto v_resetjp_2886_;
}
else
{
lean_inc(v_a_2885_);
lean_dec(v___x_2884_);
v___x_2887_ = lean_box(0);
v_isShared_2888_ = v_isSharedCheck_2894_;
goto v_resetjp_2886_;
}
v_resetjp_2886_:
{
lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2892_; 
v___x_2889_ = lean_obj_once(&l_Lean_Firefox_instFromJsonThread_fromJson___closed__52, &l_Lean_Firefox_instFromJsonThread_fromJson___closed__52_once, _init_l_Lean_Firefox_instFromJsonThread_fromJson___closed__52);
v___x_2890_ = lean_string_append(v___x_2889_, v_a_2885_);
lean_dec(v_a_2885_);
if (v_isShared_2888_ == 0)
{
lean_ctor_set(v___x_2887_, 0, v___x_2890_);
v___x_2892_ = v___x_2887_;
goto v_reusejp_2891_;
}
else
{
lean_object* v_reuseFailAlloc_2893_; 
v_reuseFailAlloc_2893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2893_, 0, v___x_2890_);
v___x_2892_ = v_reuseFailAlloc_2893_;
goto v_reusejp_2891_;
}
v_reusejp_2891_:
{
return v___x_2892_;
}
}
}
else
{
lean_object* v_a_2895_; lean_object* v___x_2897_; uint8_t v_isShared_2898_; uint8_t v_isSharedCheck_2904_; 
v_a_2895_ = lean_ctor_get(v___x_2884_, 0);
v_isSharedCheck_2904_ = !lean_is_exclusive(v___x_2884_);
if (v_isSharedCheck_2904_ == 0)
{
v___x_2897_ = v___x_2884_;
v_isShared_2898_ = v_isSharedCheck_2904_;
goto v_resetjp_2896_;
}
else
{
lean_inc(v_a_2895_);
lean_dec(v___x_2884_);
v___x_2897_ = lean_box(0);
v_isShared_2898_ = v_isSharedCheck_2904_;
goto v_resetjp_2896_;
}
v_resetjp_2896_:
{
lean_object* v___x_2899_; uint8_t v___x_2900_; lean_object* v___x_2902_; 
v___x_2899_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_2899_, 0, v_a_2765_);
lean_ctor_set(v___x_2899_, 1, v_a_2778_);
lean_ctor_set(v___x_2899_, 2, v_a_2804_);
lean_ctor_set(v___x_2899_, 3, v_a_2817_);
lean_ctor_set(v___x_2899_, 4, v_a_2830_);
lean_ctor_set(v___x_2899_, 5, v_a_2843_);
lean_ctor_set(v___x_2899_, 6, v_a_2856_);
lean_ctor_set(v___x_2899_, 7, v_a_2869_);
lean_ctor_set(v___x_2899_, 8, v_a_2882_);
lean_ctor_set(v___x_2899_, 9, v_a_2895_);
v___x_2900_ = lean_unbox(v_a_2791_);
lean_dec(v_a_2791_);
lean_ctor_set_uint8(v___x_2899_, sizeof(void*)*10, v___x_2900_);
if (v_isShared_2898_ == 0)
{
lean_ctor_set(v___x_2897_, 0, v___x_2899_);
v___x_2902_ = v___x_2897_;
goto v_reusejp_2901_;
}
else
{
lean_object* v_reuseFailAlloc_2903_; 
v_reuseFailAlloc_2903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2903_, 0, v___x_2899_);
v___x_2902_ = v_reuseFailAlloc_2903_;
goto v_reusejp_2901_;
}
v_reusejp_2901_:
{
return v___x_2902_;
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
LEAN_EXPORT lean_object* l_Lean_Firefox_instToJsonThread_toJson(lean_object* v_x_2907_){
_start:
{
lean_object* v_name_2908_; lean_object* v_processType_2909_; uint8_t v_isMainThread_2910_; lean_object* v_samples_2911_; lean_object* v_markers_2912_; lean_object* v_stackTable_2913_; lean_object* v_frameTable_2914_; lean_object* v_resourceTable_2915_; lean_object* v_nativeSymbols_2916_; lean_object* v_stringArray_2917_; lean_object* v_funcTable_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; 
v_name_2908_ = lean_ctor_get(v_x_2907_, 0);
lean_inc_ref(v_name_2908_);
v_processType_2909_ = lean_ctor_get(v_x_2907_, 1);
lean_inc_ref(v_processType_2909_);
v_isMainThread_2910_ = lean_ctor_get_uint8(v_x_2907_, sizeof(void*)*10);
v_samples_2911_ = lean_ctor_get(v_x_2907_, 2);
lean_inc_ref(v_samples_2911_);
v_markers_2912_ = lean_ctor_get(v_x_2907_, 3);
lean_inc_ref(v_markers_2912_);
v_stackTable_2913_ = lean_ctor_get(v_x_2907_, 4);
lean_inc_ref(v_stackTable_2913_);
v_frameTable_2914_ = lean_ctor_get(v_x_2907_, 5);
lean_inc_ref(v_frameTable_2914_);
v_resourceTable_2915_ = lean_ctor_get(v_x_2907_, 6);
lean_inc_ref(v_resourceTable_2915_);
v_nativeSymbols_2916_ = lean_ctor_get(v_x_2907_, 7);
lean_inc_ref(v_nativeSymbols_2916_);
v_stringArray_2917_ = lean_ctor_get(v_x_2907_, 8);
lean_inc_ref(v_stringArray_2917_);
v_funcTable_2918_ = lean_ctor_get(v_x_2907_, 9);
lean_inc_ref(v_funcTable_2918_);
lean_dec_ref(v_x_2907_);
v___x_2919_ = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__0));
v___x_2920_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2920_, 0, v_name_2908_);
v___x_2921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2921_, 0, v___x_2919_);
lean_ctor_set(v___x_2921_, 1, v___x_2920_);
v___x_2922_ = lean_box(0);
v___x_2923_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2923_, 0, v___x_2921_);
lean_ctor_set(v___x_2923_, 1, v___x_2922_);
v___x_2924_ = ((lean_object*)(l_Lean_Firefox_instFromJsonProfileMeta_fromJson___closed__19));
v___x_2925_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2925_, 0, v_processType_2909_);
v___x_2926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2926_, 0, v___x_2924_);
lean_ctor_set(v___x_2926_, 1, v___x_2925_);
v___x_2927_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2927_, 0, v___x_2926_);
lean_ctor_set(v___x_2927_, 1, v___x_2922_);
v___x_2928_ = ((lean_object*)(l_Lean_Firefox_instFromJsonThread_fromJson___closed__8));
v___x_2929_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2929_, 0, v_isMainThread_2910_);
v___x_2930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2930_, 0, v___x_2928_);
lean_ctor_set(v___x_2930_, 1, v___x_2929_);
v___x_2931_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2931_, 0, v___x_2930_);
lean_ctor_set(v___x_2931_, 1, v___x_2922_);
v___x_2932_ = ((lean_object*)(l_Lean_Firefox_instFromJsonThread_fromJson___closed__13));
v___x_2933_ = l_Lean_Firefox_instToJsonSamplesTable_toJson(v_samples_2911_);
v___x_2934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2934_, 0, v___x_2932_);
lean_ctor_set(v___x_2934_, 1, v___x_2933_);
v___x_2935_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2935_, 0, v___x_2934_);
lean_ctor_set(v___x_2935_, 1, v___x_2922_);
v___x_2936_ = ((lean_object*)(l_Lean_Firefox_instFromJsonThread_fromJson___closed__18));
v___x_2937_ = l_Lean_Firefox_instToJsonRawMarkerTable_toJson(v_markers_2912_);
v___x_2938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2938_, 0, v___x_2936_);
lean_ctor_set(v___x_2938_, 1, v___x_2937_);
v___x_2939_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2939_, 0, v___x_2938_);
lean_ctor_set(v___x_2939_, 1, v___x_2922_);
v___x_2940_ = ((lean_object*)(l_Lean_Firefox_instFromJsonThread_fromJson___closed__23));
v___x_2941_ = l_Lean_Firefox_instToJsonStackTable_toJson(v_stackTable_2913_);
v___x_2942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2942_, 0, v___x_2940_);
lean_ctor_set(v___x_2942_, 1, v___x_2941_);
v___x_2943_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2943_, 0, v___x_2942_);
lean_ctor_set(v___x_2943_, 1, v___x_2922_);
v___x_2944_ = ((lean_object*)(l_Lean_Firefox_instFromJsonThread_fromJson___closed__28));
v___x_2945_ = l_Lean_Firefox_instToJsonFrameTable_toJson(v_frameTable_2914_);
v___x_2946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2946_, 0, v___x_2944_);
lean_ctor_set(v___x_2946_, 1, v___x_2945_);
v___x_2947_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2947_, 0, v___x_2946_);
lean_ctor_set(v___x_2947_, 1, v___x_2922_);
v___x_2948_ = ((lean_object*)(l_Lean_Firefox_instFromJsonThread_fromJson___closed__33));
v___x_2949_ = l_Lean_Firefox_instToJsonResourceTable_toJson(v_resourceTable_2915_);
v___x_2950_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2950_, 0, v___x_2948_);
lean_ctor_set(v___x_2950_, 1, v___x_2949_);
v___x_2951_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2951_, 0, v___x_2950_);
lean_ctor_set(v___x_2951_, 1, v___x_2922_);
v___x_2952_ = ((lean_object*)(l_Lean_Firefox_instFromJsonThread_fromJson___closed__38));
v___x_2953_ = l_Lean_Firefox_instToJsonResourceTable_toJson(v_nativeSymbols_2916_);
v___x_2954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2954_, 0, v___x_2952_);
lean_ctor_set(v___x_2954_, 1, v___x_2953_);
v___x_2955_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2955_, 0, v___x_2954_);
lean_ctor_set(v___x_2955_, 1, v___x_2922_);
v___x_2956_ = ((lean_object*)(l_Lean_Firefox_instFromJsonThread_fromJson___closed__43));
v___x_2957_ = l_Lean_Array_toJson___at___00Lean_Firefox_instToJsonCategory_toJson_spec__0(v_stringArray_2917_);
v___x_2958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2958_, 0, v___x_2956_);
lean_ctor_set(v___x_2958_, 1, v___x_2957_);
v___x_2959_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2959_, 0, v___x_2958_);
lean_ctor_set(v___x_2959_, 1, v___x_2922_);
v___x_2960_ = ((lean_object*)(l_Lean_Firefox_instFromJsonThread_fromJson___closed__48));
v___x_2961_ = l_Lean_Firefox_instToJsonFuncTable_toJson(v_funcTable_2918_);
v___x_2962_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2962_, 0, v___x_2960_);
lean_ctor_set(v___x_2962_, 1, v___x_2961_);
v___x_2963_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2963_, 0, v___x_2962_);
lean_ctor_set(v___x_2963_, 1, v___x_2922_);
v___x_2964_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2964_, 0, v___x_2963_);
lean_ctor_set(v___x_2964_, 1, v___x_2922_);
v___x_2965_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2965_, 0, v___x_2959_);
lean_ctor_set(v___x_2965_, 1, v___x_2964_);
v___x_2966_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2966_, 0, v___x_2955_);
lean_ctor_set(v___x_2966_, 1, v___x_2965_);
v___x_2967_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2967_, 0, v___x_2951_);
lean_ctor_set(v___x_2967_, 1, v___x_2966_);
v___x_2968_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2968_, 0, v___x_2947_);
lean_ctor_set(v___x_2968_, 1, v___x_2967_);
v___x_2969_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2969_, 0, v___x_2943_);
lean_ctor_set(v___x_2969_, 1, v___x_2968_);
v___x_2970_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2970_, 0, v___x_2939_);
lean_ctor_set(v___x_2970_, 1, v___x_2969_);
v___x_2971_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2971_, 0, v___x_2935_);
lean_ctor_set(v___x_2971_, 1, v___x_2970_);
v___x_2972_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2972_, 0, v___x_2931_);
lean_ctor_set(v___x_2972_, 1, v___x_2971_);
v___x_2973_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2973_, 0, v___x_2927_);
lean_ctor_set(v___x_2973_, 1, v___x_2972_);
v___x_2974_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2974_, 0, v___x_2923_);
lean_ctor_set(v___x_2974_, 1, v___x_2973_);
v___x_2975_ = ((lean_object*)(l_Lean_Firefox_instToJsonCategory_toJson___closed__0));
v___x_2976_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Firefox_instToJsonCategory_toJson_spec__1(v___x_2974_, v___x_2975_);
v___x_2977_ = l_Lean_Json_mkObj(v___x_2976_);
lean_dec(v___x_2976_);
return v___x_2977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfile_fromJson_spec__0(lean_object* v_j_2980_, lean_object* v_k_2981_){
_start:
{
lean_object* v___x_2982_; lean_object* v___x_2983_; 
v___x_2982_ = l_Lean_Json_getObjValD(v_j_2980_, v_k_2981_);
v___x_2983_ = l_Lean_Firefox_instFromJsonProfileMeta_fromJson(v___x_2982_);
return v___x_2983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfile_fromJson_spec__0___boxed(lean_object* v_j_2984_, lean_object* v_k_2985_){
_start:
{
lean_object* v_res_2986_; 
v_res_2986_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfile_fromJson_spec__0(v_j_2984_, v_k_2985_);
lean_dec_ref(v_k_2985_);
return v_res_2986_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfile_fromJson_spec__1_spec__1_spec__2(size_t v_sz_2987_, size_t v_i_2988_, lean_object* v_bs_2989_){
_start:
{
uint8_t v___x_2990_; 
v___x_2990_ = lean_usize_dec_lt(v_i_2988_, v_sz_2987_);
if (v___x_2990_ == 0)
{
lean_object* v___x_2991_; 
v___x_2991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2991_, 0, v_bs_2989_);
return v___x_2991_;
}
else
{
lean_object* v_v_2992_; lean_object* v___x_2993_; 
v_v_2992_ = lean_array_uget_borrowed(v_bs_2989_, v_i_2988_);
lean_inc(v_v_2992_);
v___x_2993_ = l_Lean_Firefox_instFromJsonThread_fromJson(v_v_2992_);
if (lean_obj_tag(v___x_2993_) == 0)
{
lean_object* v_a_2994_; lean_object* v___x_2996_; uint8_t v_isShared_2997_; uint8_t v_isSharedCheck_3001_; 
lean_dec_ref(v_bs_2989_);
v_a_2994_ = lean_ctor_get(v___x_2993_, 0);
v_isSharedCheck_3001_ = !lean_is_exclusive(v___x_2993_);
if (v_isSharedCheck_3001_ == 0)
{
v___x_2996_ = v___x_2993_;
v_isShared_2997_ = v_isSharedCheck_3001_;
goto v_resetjp_2995_;
}
else
{
lean_inc(v_a_2994_);
lean_dec(v___x_2993_);
v___x_2996_ = lean_box(0);
v_isShared_2997_ = v_isSharedCheck_3001_;
goto v_resetjp_2995_;
}
v_resetjp_2995_:
{
lean_object* v___x_2999_; 
if (v_isShared_2997_ == 0)
{
v___x_2999_ = v___x_2996_;
goto v_reusejp_2998_;
}
else
{
lean_object* v_reuseFailAlloc_3000_; 
v_reuseFailAlloc_3000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3000_, 0, v_a_2994_);
v___x_2999_ = v_reuseFailAlloc_3000_;
goto v_reusejp_2998_;
}
v_reusejp_2998_:
{
return v___x_2999_;
}
}
}
else
{
lean_object* v_a_3002_; lean_object* v___x_3003_; lean_object* v_bs_x27_3004_; size_t v___x_3005_; size_t v___x_3006_; lean_object* v___x_3007_; 
v_a_3002_ = lean_ctor_get(v___x_2993_, 0);
lean_inc(v_a_3002_);
lean_dec_ref_known(v___x_2993_, 1);
v___x_3003_ = lean_unsigned_to_nat(0u);
v_bs_x27_3004_ = lean_array_uset(v_bs_2989_, v_i_2988_, v___x_3003_);
v___x_3005_ = ((size_t)1ULL);
v___x_3006_ = lean_usize_add(v_i_2988_, v___x_3005_);
v___x_3007_ = lean_array_uset(v_bs_x27_3004_, v_i_2988_, v_a_3002_);
v_i_2988_ = v___x_3006_;
v_bs_2989_ = v___x_3007_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfile_fromJson_spec__1_spec__1_spec__2___boxed(lean_object* v_sz_3009_, lean_object* v_i_3010_, lean_object* v_bs_3011_){
_start:
{
size_t v_sz_boxed_3012_; size_t v_i_boxed_3013_; lean_object* v_res_3014_; 
v_sz_boxed_3012_ = lean_unbox_usize(v_sz_3009_);
lean_dec(v_sz_3009_);
v_i_boxed_3013_ = lean_unbox_usize(v_i_3010_);
lean_dec(v_i_3010_);
v_res_3014_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfile_fromJson_spec__1_spec__1_spec__2(v_sz_boxed_3012_, v_i_boxed_3013_, v_bs_3011_);
return v_res_3014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfile_fromJson_spec__1_spec__1(lean_object* v_x_3015_){
_start:
{
if (lean_obj_tag(v_x_3015_) == 4)
{
lean_object* v_elems_3016_; size_t v_sz_3017_; size_t v___x_3018_; lean_object* v___x_3019_; 
v_elems_3016_ = lean_ctor_get(v_x_3015_, 0);
lean_inc_ref(v_elems_3016_);
lean_dec_ref_known(v_x_3015_, 1);
v_sz_3017_ = lean_array_size(v_elems_3016_);
v___x_3018_ = ((size_t)0ULL);
v___x_3019_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfile_fromJson_spec__1_spec__1_spec__2(v_sz_3017_, v___x_3018_, v_elems_3016_);
return v___x_3019_;
}
else
{
lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; 
v___x_3020_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__2_spec__2___closed__0));
v___x_3021_ = lean_unsigned_to_nat(80u);
v___x_3022_ = l_Lean_Json_pretty(v_x_3015_, v___x_3021_);
v___x_3023_ = lean_string_append(v___x_3020_, v___x_3022_);
lean_dec_ref(v___x_3022_);
v___x_3024_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonCategory_fromJson_spec__2_spec__2___closed__1));
v___x_3025_ = lean_string_append(v___x_3023_, v___x_3024_);
v___x_3026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3026_, 0, v___x_3025_);
return v___x_3026_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfile_fromJson_spec__1(lean_object* v_j_3027_, lean_object* v_k_3028_){
_start:
{
lean_object* v___x_3029_; lean_object* v___x_3030_; 
v___x_3029_ = l_Lean_Json_getObjValD(v_j_3027_, v_k_3028_);
v___x_3030_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfile_fromJson_spec__1_spec__1(v___x_3029_);
return v___x_3030_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfile_fromJson_spec__1___boxed(lean_object* v_j_3031_, lean_object* v_k_3032_){
_start:
{
lean_object* v_res_3033_; 
v_res_3033_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfile_fromJson_spec__1(v_j_3031_, v_k_3032_);
lean_dec_ref(v_k_3032_);
return v_res_3033_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonProfile_fromJson___closed__3(void){
_start:
{
uint8_t v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; 
v___x_3040_ = 1;
v___x_3041_ = ((lean_object*)(l_Lean_Firefox_instFromJsonProfile_fromJson___closed__2));
v___x_3042_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3041_, v___x_3040_);
return v___x_3042_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonProfile_fromJson___closed__4(void){
_start:
{
lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; 
v___x_3043_ = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__6));
v___x_3044_ = lean_obj_once(&l_Lean_Firefox_instFromJsonProfile_fromJson___closed__3, &l_Lean_Firefox_instFromJsonProfile_fromJson___closed__3_once, _init_l_Lean_Firefox_instFromJsonProfile_fromJson___closed__3);
v___x_3045_ = lean_string_append(v___x_3044_, v___x_3043_);
return v___x_3045_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonProfile_fromJson___closed__6(void){
_start:
{
uint8_t v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; 
v___x_3048_ = 1;
v___x_3049_ = ((lean_object*)(l_Lean_Firefox_instFromJsonProfile_fromJson___closed__5));
v___x_3050_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3049_, v___x_3048_);
return v___x_3050_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonProfile_fromJson___closed__7(void){
_start:
{
lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; 
v___x_3051_ = lean_obj_once(&l_Lean_Firefox_instFromJsonProfile_fromJson___closed__6, &l_Lean_Firefox_instFromJsonProfile_fromJson___closed__6_once, _init_l_Lean_Firefox_instFromJsonProfile_fromJson___closed__6);
v___x_3052_ = lean_obj_once(&l_Lean_Firefox_instFromJsonProfile_fromJson___closed__4, &l_Lean_Firefox_instFromJsonProfile_fromJson___closed__4_once, _init_l_Lean_Firefox_instFromJsonProfile_fromJson___closed__4);
v___x_3053_ = lean_string_append(v___x_3052_, v___x_3051_);
return v___x_3053_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonProfile_fromJson___closed__8(void){
_start:
{
lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; 
v___x_3054_ = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
v___x_3055_ = lean_obj_once(&l_Lean_Firefox_instFromJsonProfile_fromJson___closed__7, &l_Lean_Firefox_instFromJsonProfile_fromJson___closed__7_once, _init_l_Lean_Firefox_instFromJsonProfile_fromJson___closed__7);
v___x_3056_ = lean_string_append(v___x_3055_, v___x_3054_);
return v___x_3056_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonProfile_fromJson___closed__11(void){
_start:
{
uint8_t v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; 
v___x_3060_ = 1;
v___x_3061_ = ((lean_object*)(l_Lean_Firefox_instFromJsonProfile_fromJson___closed__10));
v___x_3062_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3061_, v___x_3060_);
return v___x_3062_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonProfile_fromJson___closed__12(void){
_start:
{
lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; 
v___x_3063_ = lean_obj_once(&l_Lean_Firefox_instFromJsonProfile_fromJson___closed__11, &l_Lean_Firefox_instFromJsonProfile_fromJson___closed__11_once, _init_l_Lean_Firefox_instFromJsonProfile_fromJson___closed__11);
v___x_3064_ = lean_obj_once(&l_Lean_Firefox_instFromJsonProfile_fromJson___closed__4, &l_Lean_Firefox_instFromJsonProfile_fromJson___closed__4_once, _init_l_Lean_Firefox_instFromJsonProfile_fromJson___closed__4);
v___x_3065_ = lean_string_append(v___x_3064_, v___x_3063_);
return v___x_3065_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonProfile_fromJson___closed__13(void){
_start:
{
lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; 
v___x_3066_ = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
v___x_3067_ = lean_obj_once(&l_Lean_Firefox_instFromJsonProfile_fromJson___closed__12, &l_Lean_Firefox_instFromJsonProfile_fromJson___closed__12_once, _init_l_Lean_Firefox_instFromJsonProfile_fromJson___closed__12);
v___x_3068_ = lean_string_append(v___x_3067_, v___x_3066_);
return v___x_3068_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonProfile_fromJson___closed__16(void){
_start:
{
uint8_t v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; 
v___x_3072_ = 1;
v___x_3073_ = ((lean_object*)(l_Lean_Firefox_instFromJsonProfile_fromJson___closed__15));
v___x_3074_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3073_, v___x_3072_);
return v___x_3074_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonProfile_fromJson___closed__17(void){
_start:
{
lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; 
v___x_3075_ = lean_obj_once(&l_Lean_Firefox_instFromJsonProfile_fromJson___closed__16, &l_Lean_Firefox_instFromJsonProfile_fromJson___closed__16_once, _init_l_Lean_Firefox_instFromJsonProfile_fromJson___closed__16);
v___x_3076_ = lean_obj_once(&l_Lean_Firefox_instFromJsonProfile_fromJson___closed__4, &l_Lean_Firefox_instFromJsonProfile_fromJson___closed__4_once, _init_l_Lean_Firefox_instFromJsonProfile_fromJson___closed__4);
v___x_3077_ = lean_string_append(v___x_3076_, v___x_3075_);
return v___x_3077_;
}
}
static lean_object* _init_l_Lean_Firefox_instFromJsonProfile_fromJson___closed__18(void){
_start:
{
lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; 
v___x_3078_ = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
v___x_3079_ = lean_obj_once(&l_Lean_Firefox_instFromJsonProfile_fromJson___closed__17, &l_Lean_Firefox_instFromJsonProfile_fromJson___closed__17_once, _init_l_Lean_Firefox_instFromJsonProfile_fromJson___closed__17);
v___x_3080_ = lean_string_append(v___x_3079_, v___x_3078_);
return v___x_3080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Firefox_instFromJsonProfile_fromJson(lean_object* v_json_3081_){
_start:
{
lean_object* v___x_3082_; lean_object* v___x_3083_; 
v___x_3082_ = ((lean_object*)(l_Lean_Firefox_instFromJsonProfile_fromJson___closed__0));
lean_inc(v_json_3081_);
v___x_3083_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfile_fromJson_spec__0(v_json_3081_, v___x_3082_);
if (lean_obj_tag(v___x_3083_) == 0)
{
lean_object* v_a_3084_; lean_object* v___x_3086_; uint8_t v_isShared_3087_; uint8_t v_isSharedCheck_3093_; 
lean_dec(v_json_3081_);
v_a_3084_ = lean_ctor_get(v___x_3083_, 0);
v_isSharedCheck_3093_ = !lean_is_exclusive(v___x_3083_);
if (v_isSharedCheck_3093_ == 0)
{
v___x_3086_ = v___x_3083_;
v_isShared_3087_ = v_isSharedCheck_3093_;
goto v_resetjp_3085_;
}
else
{
lean_inc(v_a_3084_);
lean_dec(v___x_3083_);
v___x_3086_ = lean_box(0);
v_isShared_3087_ = v_isSharedCheck_3093_;
goto v_resetjp_3085_;
}
v_resetjp_3085_:
{
lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3091_; 
v___x_3088_ = lean_obj_once(&l_Lean_Firefox_instFromJsonProfile_fromJson___closed__8, &l_Lean_Firefox_instFromJsonProfile_fromJson___closed__8_once, _init_l_Lean_Firefox_instFromJsonProfile_fromJson___closed__8);
v___x_3089_ = lean_string_append(v___x_3088_, v_a_3084_);
lean_dec(v_a_3084_);
if (v_isShared_3087_ == 0)
{
lean_ctor_set(v___x_3086_, 0, v___x_3089_);
v___x_3091_ = v___x_3086_;
goto v_reusejp_3090_;
}
else
{
lean_object* v_reuseFailAlloc_3092_; 
v_reuseFailAlloc_3092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3092_, 0, v___x_3089_);
v___x_3091_ = v_reuseFailAlloc_3092_;
goto v_reusejp_3090_;
}
v_reusejp_3090_:
{
return v___x_3091_;
}
}
}
else
{
lean_object* v_a_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; 
v_a_3094_ = lean_ctor_get(v___x_3083_, 0);
lean_inc(v_a_3094_);
lean_dec_ref_known(v___x_3083_, 1);
v___x_3095_ = ((lean_object*)(l_Lean_Firefox_instFromJsonProfile_fromJson___closed__9));
lean_inc(v_json_3081_);
v___x_3096_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfileMeta_fromJson_spec__3(v_json_3081_, v___x_3095_);
if (lean_obj_tag(v___x_3096_) == 0)
{
lean_object* v_a_3097_; lean_object* v___x_3099_; uint8_t v_isShared_3100_; uint8_t v_isSharedCheck_3106_; 
lean_dec(v_a_3094_);
lean_dec(v_json_3081_);
v_a_3097_ = lean_ctor_get(v___x_3096_, 0);
v_isSharedCheck_3106_ = !lean_is_exclusive(v___x_3096_);
if (v_isSharedCheck_3106_ == 0)
{
v___x_3099_ = v___x_3096_;
v_isShared_3100_ = v_isSharedCheck_3106_;
goto v_resetjp_3098_;
}
else
{
lean_inc(v_a_3097_);
lean_dec(v___x_3096_);
v___x_3099_ = lean_box(0);
v_isShared_3100_ = v_isSharedCheck_3106_;
goto v_resetjp_3098_;
}
v_resetjp_3098_:
{
lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3104_; 
v___x_3101_ = lean_obj_once(&l_Lean_Firefox_instFromJsonProfile_fromJson___closed__13, &l_Lean_Firefox_instFromJsonProfile_fromJson___closed__13_once, _init_l_Lean_Firefox_instFromJsonProfile_fromJson___closed__13);
v___x_3102_ = lean_string_append(v___x_3101_, v_a_3097_);
lean_dec(v_a_3097_);
if (v_isShared_3100_ == 0)
{
lean_ctor_set(v___x_3099_, 0, v___x_3102_);
v___x_3104_ = v___x_3099_;
goto v_reusejp_3103_;
}
else
{
lean_object* v_reuseFailAlloc_3105_; 
v_reuseFailAlloc_3105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3105_, 0, v___x_3102_);
v___x_3104_ = v_reuseFailAlloc_3105_;
goto v_reusejp_3103_;
}
v_reusejp_3103_:
{
return v___x_3104_;
}
}
}
else
{
lean_object* v_a_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; 
v_a_3107_ = lean_ctor_get(v___x_3096_, 0);
lean_inc(v_a_3107_);
lean_dec_ref_known(v___x_3096_, 1);
v___x_3108_ = ((lean_object*)(l_Lean_Firefox_instFromJsonProfile_fromJson___closed__14));
v___x_3109_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Firefox_instFromJsonProfile_fromJson_spec__1(v_json_3081_, v___x_3108_);
if (lean_obj_tag(v___x_3109_) == 0)
{
lean_object* v_a_3110_; lean_object* v___x_3112_; uint8_t v_isShared_3113_; uint8_t v_isSharedCheck_3119_; 
lean_dec(v_a_3107_);
lean_dec(v_a_3094_);
v_a_3110_ = lean_ctor_get(v___x_3109_, 0);
v_isSharedCheck_3119_ = !lean_is_exclusive(v___x_3109_);
if (v_isSharedCheck_3119_ == 0)
{
v___x_3112_ = v___x_3109_;
v_isShared_3113_ = v_isSharedCheck_3119_;
goto v_resetjp_3111_;
}
else
{
lean_inc(v_a_3110_);
lean_dec(v___x_3109_);
v___x_3112_ = lean_box(0);
v_isShared_3113_ = v_isSharedCheck_3119_;
goto v_resetjp_3111_;
}
v_resetjp_3111_:
{
lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3117_; 
v___x_3114_ = lean_obj_once(&l_Lean_Firefox_instFromJsonProfile_fromJson___closed__18, &l_Lean_Firefox_instFromJsonProfile_fromJson___closed__18_once, _init_l_Lean_Firefox_instFromJsonProfile_fromJson___closed__18);
v___x_3115_ = lean_string_append(v___x_3114_, v_a_3110_);
lean_dec(v_a_3110_);
if (v_isShared_3113_ == 0)
{
lean_ctor_set(v___x_3112_, 0, v___x_3115_);
v___x_3117_ = v___x_3112_;
goto v_reusejp_3116_;
}
else
{
lean_object* v_reuseFailAlloc_3118_; 
v_reuseFailAlloc_3118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3118_, 0, v___x_3115_);
v___x_3117_ = v_reuseFailAlloc_3118_;
goto v_reusejp_3116_;
}
v_reusejp_3116_:
{
return v___x_3117_;
}
}
}
else
{
lean_object* v_a_3120_; lean_object* v___x_3122_; uint8_t v_isShared_3123_; uint8_t v_isSharedCheck_3128_; 
v_a_3120_ = lean_ctor_get(v___x_3109_, 0);
v_isSharedCheck_3128_ = !lean_is_exclusive(v___x_3109_);
if (v_isSharedCheck_3128_ == 0)
{
v___x_3122_ = v___x_3109_;
v_isShared_3123_ = v_isSharedCheck_3128_;
goto v_resetjp_3121_;
}
else
{
lean_inc(v_a_3120_);
lean_dec(v___x_3109_);
v___x_3122_ = lean_box(0);
v_isShared_3123_ = v_isSharedCheck_3128_;
goto v_resetjp_3121_;
}
v_resetjp_3121_:
{
lean_object* v___x_3124_; lean_object* v___x_3126_; 
v___x_3124_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3124_, 0, v_a_3094_);
lean_ctor_set(v___x_3124_, 1, v_a_3107_);
lean_ctor_set(v___x_3124_, 2, v_a_3120_);
if (v_isShared_3123_ == 0)
{
lean_ctor_set(v___x_3122_, 0, v___x_3124_);
v___x_3126_ = v___x_3122_;
goto v_reusejp_3125_;
}
else
{
lean_object* v_reuseFailAlloc_3127_; 
v_reuseFailAlloc_3127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3127_, 0, v___x_3124_);
v___x_3126_ = v_reuseFailAlloc_3127_;
goto v_reusejp_3125_;
}
v_reusejp_3125_:
{
return v___x_3126_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Firefox_instToJsonProfile_toJson_spec__0_spec__0(size_t v_sz_3131_, size_t v_i_3132_, lean_object* v_bs_3133_){
_start:
{
uint8_t v___x_3134_; 
v___x_3134_ = lean_usize_dec_lt(v_i_3132_, v_sz_3131_);
if (v___x_3134_ == 0)
{
return v_bs_3133_;
}
else
{
lean_object* v_v_3135_; lean_object* v___x_3136_; lean_object* v_bs_x27_3137_; lean_object* v___x_3138_; size_t v___x_3139_; size_t v___x_3140_; lean_object* v___x_3141_; 
v_v_3135_ = lean_array_uget(v_bs_3133_, v_i_3132_);
v___x_3136_ = lean_unsigned_to_nat(0u);
v_bs_x27_3137_ = lean_array_uset(v_bs_3133_, v_i_3132_, v___x_3136_);
v___x_3138_ = l_Lean_Firefox_instToJsonThread_toJson(v_v_3135_);
v___x_3139_ = ((size_t)1ULL);
v___x_3140_ = lean_usize_add(v_i_3132_, v___x_3139_);
v___x_3141_ = lean_array_uset(v_bs_x27_3137_, v_i_3132_, v___x_3138_);
v_i_3132_ = v___x_3140_;
v_bs_3133_ = v___x_3141_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Firefox_instToJsonProfile_toJson_spec__0_spec__0___boxed(lean_object* v_sz_3143_, lean_object* v_i_3144_, lean_object* v_bs_3145_){
_start:
{
size_t v_sz_boxed_3146_; size_t v_i_boxed_3147_; lean_object* v_res_3148_; 
v_sz_boxed_3146_ = lean_unbox_usize(v_sz_3143_);
lean_dec(v_sz_3143_);
v_i_boxed_3147_ = lean_unbox_usize(v_i_3144_);
lean_dec(v_i_3144_);
v_res_3148_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Firefox_instToJsonProfile_toJson_spec__0_spec__0(v_sz_boxed_3146_, v_i_boxed_3147_, v_bs_3145_);
return v_res_3148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Firefox_instToJsonProfile_toJson_spec__0(lean_object* v_a_3149_){
_start:
{
size_t v_sz_3150_; size_t v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; 
v_sz_3150_ = lean_array_size(v_a_3149_);
v___x_3151_ = ((size_t)0ULL);
v___x_3152_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Firefox_instToJsonProfile_toJson_spec__0_spec__0(v_sz_3150_, v___x_3151_, v_a_3149_);
v___x_3153_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3153_, 0, v___x_3152_);
return v___x_3153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Firefox_instToJsonProfile_toJson(lean_object* v_x_3154_){
_start:
{
lean_object* v_meta_3155_; lean_object* v_libs_3156_; lean_object* v_threads_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; 
v_meta_3155_ = lean_ctor_get(v_x_3154_, 0);
lean_inc_ref(v_meta_3155_);
v_libs_3156_ = lean_ctor_get(v_x_3154_, 1);
lean_inc_ref(v_libs_3156_);
v_threads_3157_ = lean_ctor_get(v_x_3154_, 2);
lean_inc_ref(v_threads_3157_);
lean_dec_ref(v_x_3154_);
v___x_3158_ = ((lean_object*)(l_Lean_Firefox_instFromJsonProfile_fromJson___closed__0));
v___x_3159_ = l_Lean_Firefox_instToJsonProfileMeta_toJson(v_meta_3155_);
v___x_3160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3160_, 0, v___x_3158_);
lean_ctor_set(v___x_3160_, 1, v___x_3159_);
v___x_3161_ = lean_box(0);
v___x_3162_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3162_, 0, v___x_3160_);
lean_ctor_set(v___x_3162_, 1, v___x_3161_);
v___x_3163_ = ((lean_object*)(l_Lean_Firefox_instFromJsonProfile_fromJson___closed__9));
v___x_3164_ = l_Lean_Array_toJson___at___00Lean_Firefox_instToJsonProfileMeta_toJson_spec__1(v_libs_3156_);
v___x_3165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3165_, 0, v___x_3163_);
lean_ctor_set(v___x_3165_, 1, v___x_3164_);
v___x_3166_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3166_, 0, v___x_3165_);
lean_ctor_set(v___x_3166_, 1, v___x_3161_);
v___x_3167_ = ((lean_object*)(l_Lean_Firefox_instFromJsonProfile_fromJson___closed__14));
v___x_3168_ = l_Lean_Array_toJson___at___00Lean_Firefox_instToJsonProfile_toJson_spec__0(v_threads_3157_);
v___x_3169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3169_, 0, v___x_3167_);
lean_ctor_set(v___x_3169_, 1, v___x_3168_);
v___x_3170_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3170_, 0, v___x_3169_);
lean_ctor_set(v___x_3170_, 1, v___x_3161_);
v___x_3171_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3171_, 0, v___x_3170_);
lean_ctor_set(v___x_3171_, 1, v___x_3161_);
v___x_3172_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3172_, 0, v___x_3166_);
lean_ctor_set(v___x_3172_, 1, v___x_3171_);
v___x_3173_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3173_, 0, v___x_3162_);
lean_ctor_set(v___x_3173_, 1, v___x_3172_);
v___x_3174_ = ((lean_object*)(l_Lean_Firefox_instToJsonCategory_toJson___closed__0));
v___x_3175_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Firefox_instToJsonCategory_toJson_spec__1(v___x_3173_, v___x_3174_);
v___x_3176_ = l_Lean_Json_mkObj(v___x_3175_);
lean_dec(v___x_3175_);
return v___x_3176_;
}
}
static double _init_l___private_Lean_Util_Profiler_0__Lean_Firefox_getFirstStart_x3f___closed__0(void){
_start:
{
lean_object* v___x_3248_; double v___x_3249_; 
v___x_3248_ = lean_unsigned_to_nat(0u);
v___x_3249_ = lean_float_of_nat(v___x_3248_);
return v___x_3249_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Profiler_0__Lean_Firefox_getFirstStart_x3f(lean_object* v_x_3250_){
_start:
{
switch(lean_obj_tag(v_x_3250_))
{
case 9:
{
lean_object* v_data_3251_; lean_object* v_children_3252_; double v_startTime_3253_; double v___x_3254_; uint8_t v___x_3255_; 
v_data_3251_ = lean_ctor_get(v_x_3250_, 0);
v_children_3252_ = lean_ctor_get(v_x_3250_, 2);
v_startTime_3253_ = lean_ctor_get_float(v_data_3251_, sizeof(void*)*3);
v___x_3254_ = lean_float_once(&l___private_Lean_Util_Profiler_0__Lean_Firefox_getFirstStart_x3f___closed__0, &l___private_Lean_Util_Profiler_0__Lean_Firefox_getFirstStart_x3f___closed__0_once, _init_l___private_Lean_Util_Profiler_0__Lean_Firefox_getFirstStart_x3f___closed__0);
v___x_3255_ = lean_float_beq(v_startTime_3253_, v___x_3254_);
if (v___x_3255_ == 0)
{
lean_object* v___x_3256_; lean_object* v___x_3257_; 
v___x_3256_ = lean_box_float(v_startTime_3253_);
v___x_3257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3257_, 0, v___x_3256_);
return v___x_3257_;
}
else
{
lean_object* v___x_3258_; lean_object* v___x_3259_; size_t v_sz_3260_; size_t v___x_3261_; lean_object* v___x_3262_; lean_object* v_fst_3263_; 
v___x_3258_ = lean_box(0);
v___x_3259_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_getFirstStart_x3f_spec__0___closed__0));
v_sz_3260_ = lean_array_size(v_children_3252_);
v___x_3261_ = ((size_t)0ULL);
v___x_3262_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_getFirstStart_x3f_spec__0(v_children_3252_, v_sz_3260_, v___x_3261_, v___x_3259_);
v_fst_3263_ = lean_ctor_get(v___x_3262_, 0);
lean_inc(v_fst_3263_);
lean_dec_ref(v___x_3262_);
if (lean_obj_tag(v_fst_3263_) == 0)
{
return v___x_3258_;
}
else
{
lean_object* v_val_3264_; 
v_val_3264_ = lean_ctor_get(v_fst_3263_, 0);
lean_inc(v_val_3264_);
lean_dec_ref_known(v_fst_3263_, 1);
if (lean_obj_tag(v_val_3264_) == 1)
{
return v_val_3264_;
}
else
{
lean_dec(v_val_3264_);
return v___x_3258_;
}
}
}
}
case 3:
{
lean_object* v_a_3265_; 
v_a_3265_ = lean_ctor_get(v_x_3250_, 1);
v_x_3250_ = v_a_3265_;
goto _start;
}
default: 
{
lean_object* v___x_3267_; 
v___x_3267_ = lean_box(0);
return v___x_3267_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_getFirstStart_x3f_spec__0(lean_object* v_as_3268_, size_t v_sz_3269_, size_t v_i_3270_, lean_object* v_b_3271_){
_start:
{
uint8_t v___x_3272_; 
v___x_3272_ = lean_usize_dec_lt(v_i_3270_, v_sz_3269_);
if (v___x_3272_ == 0)
{
lean_inc_ref(v_b_3271_);
return v_b_3271_;
}
else
{
lean_object* v___x_3273_; lean_object* v_a_3274_; lean_object* v___x_3275_; 
v___x_3273_ = lean_box(0);
v_a_3274_ = lean_array_uget_borrowed(v_as_3268_, v_i_3270_);
v___x_3275_ = l___private_Lean_Util_Profiler_0__Lean_Firefox_getFirstStart_x3f(v_a_3274_);
if (lean_obj_tag(v___x_3275_) == 1)
{
lean_object* v___x_3276_; lean_object* v___x_3277_; 
v___x_3276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3276_, 0, v___x_3275_);
v___x_3277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3277_, 0, v___x_3276_);
lean_ctor_set(v___x_3277_, 1, v___x_3273_);
return v___x_3277_;
}
else
{
lean_object* v___x_3278_; size_t v___x_3279_; size_t v___x_3280_; 
lean_dec(v___x_3275_);
v___x_3278_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_getFirstStart_x3f_spec__0___closed__0));
v___x_3279_ = ((size_t)1ULL);
v___x_3280_ = lean_usize_add(v_i_3270_, v___x_3279_);
v_i_3270_ = v___x_3280_;
v_b_3271_ = v___x_3278_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_getFirstStart_x3f_spec__0___boxed(lean_object* v_as_3282_, lean_object* v_sz_3283_, lean_object* v_i_3284_, lean_object* v_b_3285_){
_start:
{
size_t v_sz_boxed_3286_; size_t v_i_boxed_3287_; lean_object* v_res_3288_; 
v_sz_boxed_3286_ = lean_unbox_usize(v_sz_3283_);
lean_dec(v_sz_3283_);
v_i_boxed_3287_ = lean_unbox_usize(v_i_3284_);
lean_dec(v_i_3284_);
v_res_3288_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_getFirstStart_x3f_spec__0(v_as_3282_, v_sz_boxed_3286_, v_i_boxed_3287_, v_b_3285_);
lean_dec_ref(v_b_3285_);
lean_dec_ref(v_as_3282_);
return v_res_3288_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Profiler_0__Lean_Firefox_getFirstStart_x3f___boxed(lean_object* v_x_3289_){
_start:
{
lean_object* v_res_3290_; 
v_res_3290_ = l___private_Lean_Util_Profiler_0__Lean_Firefox_getFirstStart_x3f(v_x_3289_);
lean_dec_ref(v_x_3289_);
return v_res_3290_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__3_spec__7___redArg(lean_object* v_a_3291_, lean_object* v_x_3292_){
_start:
{
if (lean_obj_tag(v_x_3292_) == 0)
{
lean_object* v___x_3293_; 
v___x_3293_ = lean_box(0);
return v___x_3293_;
}
else
{
lean_object* v_key_3294_; lean_object* v_value_3295_; lean_object* v_tail_3296_; uint8_t v___x_3297_; 
v_key_3294_ = lean_ctor_get(v_x_3292_, 0);
v_value_3295_ = lean_ctor_get(v_x_3292_, 1);
v_tail_3296_ = lean_ctor_get(v_x_3292_, 2);
v___x_3297_ = lean_nat_dec_eq(v_key_3294_, v_a_3291_);
if (v___x_3297_ == 0)
{
v_x_3292_ = v_tail_3296_;
goto _start;
}
else
{
lean_object* v___x_3299_; 
lean_inc(v_value_3295_);
v___x_3299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3299_, 0, v_value_3295_);
return v___x_3299_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__3_spec__7___redArg___boxed(lean_object* v_a_3300_, lean_object* v_x_3301_){
_start:
{
lean_object* v_res_3302_; 
v_res_3302_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__3_spec__7___redArg(v_a_3300_, v_x_3301_);
lean_dec(v_x_3301_);
lean_dec(v_a_3300_);
return v_res_3302_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__3___redArg(lean_object* v_m_3303_, lean_object* v_a_3304_){
_start:
{
lean_object* v_buckets_3305_; lean_object* v___x_3306_; uint64_t v___x_3307_; uint64_t v___x_3308_; uint64_t v___x_3309_; uint64_t v_fold_3310_; uint64_t v___x_3311_; uint64_t v___x_3312_; uint64_t v___x_3313_; size_t v___x_3314_; size_t v___x_3315_; size_t v___x_3316_; size_t v___x_3317_; size_t v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; 
v_buckets_3305_ = lean_ctor_get(v_m_3303_, 1);
v___x_3306_ = lean_array_get_size(v_buckets_3305_);
v___x_3307_ = lean_uint64_of_nat(v_a_3304_);
v___x_3308_ = 32ULL;
v___x_3309_ = lean_uint64_shift_right(v___x_3307_, v___x_3308_);
v_fold_3310_ = lean_uint64_xor(v___x_3307_, v___x_3309_);
v___x_3311_ = 16ULL;
v___x_3312_ = lean_uint64_shift_right(v_fold_3310_, v___x_3311_);
v___x_3313_ = lean_uint64_xor(v_fold_3310_, v___x_3312_);
v___x_3314_ = lean_uint64_to_usize(v___x_3313_);
v___x_3315_ = lean_usize_of_nat(v___x_3306_);
v___x_3316_ = ((size_t)1ULL);
v___x_3317_ = lean_usize_sub(v___x_3315_, v___x_3316_);
v___x_3318_ = lean_usize_land(v___x_3314_, v___x_3317_);
v___x_3319_ = lean_array_uget_borrowed(v_buckets_3305_, v___x_3318_);
v___x_3320_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__3_spec__7___redArg(v_a_3304_, v___x_3319_);
return v___x_3320_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__3___redArg___boxed(lean_object* v_m_3321_, lean_object* v_a_3322_){
_start:
{
lean_object* v_res_3323_; 
v_res_3323_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__3___redArg(v_m_3321_, v_a_3322_);
lean_dec(v_a_3322_);
lean_dec_ref(v_m_3321_);
return v_res_3323_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__5(lean_object* v___x_3324_, lean_object* v_as_3325_, lean_object* v_j_3326_){
_start:
{
lean_object* v___x_3327_; uint8_t v___x_3328_; 
v___x_3327_ = lean_array_get_size(v_as_3325_);
v___x_3328_ = lean_nat_dec_lt(v_j_3326_, v___x_3327_);
if (v___x_3328_ == 0)
{
lean_object* v___x_3329_; 
lean_dec(v_j_3326_);
v___x_3329_ = lean_box(0);
return v___x_3329_;
}
else
{
lean_object* v___x_3330_; lean_object* v_name_3331_; uint8_t v___x_3332_; 
v___x_3330_ = lean_array_fget_borrowed(v_as_3325_, v_j_3326_);
v_name_3331_ = lean_ctor_get(v___x_3330_, 0);
v___x_3332_ = l_Lean_Name_isPrefixOf(v_name_3331_, v___x_3324_);
if (v___x_3332_ == 0)
{
lean_object* v___x_3333_; lean_object* v___x_3334_; 
v___x_3333_ = lean_unsigned_to_nat(1u);
v___x_3334_ = lean_nat_add(v_j_3326_, v___x_3333_);
lean_dec(v_j_3326_);
v_j_3326_ = v___x_3334_;
goto _start;
}
else
{
lean_object* v___x_3336_; 
v___x_3336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3336_, 0, v_j_3326_);
return v___x_3336_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__5___boxed(lean_object* v___x_3337_, lean_object* v_as_3338_, lean_object* v_j_3339_){
_start:
{
lean_object* v_res_3340_; 
v_res_3340_ = l_Array_findIdx_x3f_loop___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__5(v___x_3337_, v_as_3338_, v_j_3339_);
lean_dec_ref(v_as_3338_);
lean_dec(v___x_3337_);
return v_res_3340_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__1_spec__1_spec__2(lean_object* v_x_3341_, lean_object* v_x_3342_){
_start:
{
if (lean_obj_tag(v_x_3341_) == 0)
{
if (lean_obj_tag(v_x_3342_) == 0)
{
uint8_t v___x_3343_; 
v___x_3343_ = 1;
return v___x_3343_;
}
else
{
uint8_t v___x_3344_; 
v___x_3344_ = 0;
return v___x_3344_;
}
}
else
{
if (lean_obj_tag(v_x_3342_) == 0)
{
uint8_t v___x_3345_; 
v___x_3345_ = 0;
return v___x_3345_;
}
else
{
lean_object* v_val_3346_; lean_object* v_val_3347_; uint8_t v___x_3348_; 
v_val_3346_ = lean_ctor_get(v_x_3341_, 0);
v_val_3347_ = lean_ctor_get(v_x_3342_, 0);
v___x_3348_ = lean_nat_dec_eq(v_val_3346_, v_val_3347_);
return v___x_3348_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__1_spec__1_spec__2___boxed(lean_object* v_x_3349_, lean_object* v_x_3350_){
_start:
{
uint8_t v_res_3351_; lean_object* v_r_3352_; 
v_res_3351_ = l_instBEqOption_beq___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__1_spec__1_spec__2(v_x_3349_, v_x_3350_);
lean_dec(v_x_3350_);
lean_dec(v_x_3349_);
v_r_3352_ = lean_box(v_res_3351_);
return v_r_3352_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__2_spec__5___redArg(lean_object* v_a_3353_, lean_object* v_b_3354_, lean_object* v_x_3355_){
_start:
{
if (lean_obj_tag(v_x_3355_) == 0)
{
lean_dec(v_b_3354_);
lean_dec_ref(v_a_3353_);
return v_x_3355_;
}
else
{
lean_object* v_key_3356_; lean_object* v_value_3357_; lean_object* v_tail_3358_; lean_object* v___x_3360_; uint8_t v_isShared_3361_; uint8_t v_isSharedCheck_3374_; 
v_key_3356_ = lean_ctor_get(v_x_3355_, 0);
v_value_3357_ = lean_ctor_get(v_x_3355_, 1);
v_tail_3358_ = lean_ctor_get(v_x_3355_, 2);
v_isSharedCheck_3374_ = !lean_is_exclusive(v_x_3355_);
if (v_isSharedCheck_3374_ == 0)
{
v___x_3360_ = v_x_3355_;
v_isShared_3361_ = v_isSharedCheck_3374_;
goto v_resetjp_3359_;
}
else
{
lean_inc(v_tail_3358_);
lean_inc(v_value_3357_);
lean_inc(v_key_3356_);
lean_dec(v_x_3355_);
v___x_3360_ = lean_box(0);
v_isShared_3361_ = v_isSharedCheck_3374_;
goto v_resetjp_3359_;
}
v_resetjp_3359_:
{
lean_object* v_fst_3367_; lean_object* v_snd_3368_; lean_object* v_fst_3369_; lean_object* v_snd_3370_; uint8_t v___x_3371_; 
v_fst_3367_ = lean_ctor_get(v_key_3356_, 0);
v_snd_3368_ = lean_ctor_get(v_key_3356_, 1);
v_fst_3369_ = lean_ctor_get(v_a_3353_, 0);
v_snd_3370_ = lean_ctor_get(v_a_3353_, 1);
v___x_3371_ = lean_nat_dec_eq(v_fst_3367_, v_fst_3369_);
if (v___x_3371_ == 0)
{
goto v___jp_3362_;
}
else
{
uint8_t v___x_3372_; 
v___x_3372_ = l_instBEqOption_beq___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__1_spec__1_spec__2(v_snd_3368_, v_snd_3370_);
if (v___x_3372_ == 0)
{
goto v___jp_3362_;
}
else
{
lean_object* v___x_3373_; 
lean_del_object(v___x_3360_);
lean_dec(v_value_3357_);
lean_dec(v_key_3356_);
v___x_3373_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3373_, 0, v_a_3353_);
lean_ctor_set(v___x_3373_, 1, v_b_3354_);
lean_ctor_set(v___x_3373_, 2, v_tail_3358_);
return v___x_3373_;
}
}
v___jp_3362_:
{
lean_object* v___x_3363_; lean_object* v___x_3365_; 
v___x_3363_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__2_spec__5___redArg(v_a_3353_, v_b_3354_, v_tail_3358_);
if (v_isShared_3361_ == 0)
{
lean_ctor_set(v___x_3360_, 2, v___x_3363_);
v___x_3365_ = v___x_3360_;
goto v_reusejp_3364_;
}
else
{
lean_object* v_reuseFailAlloc_3366_; 
v_reuseFailAlloc_3366_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3366_, 0, v_key_3356_);
lean_ctor_set(v_reuseFailAlloc_3366_, 1, v_value_3357_);
lean_ctor_set(v_reuseFailAlloc_3366_, 2, v___x_3363_);
v___x_3365_ = v_reuseFailAlloc_3366_;
goto v_reusejp_3364_;
}
v_reusejp_3364_:
{
return v___x_3365_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__2_spec__4_spec__6_spec__12___redArg(lean_object* v_x_3375_, lean_object* v_x_3376_){
_start:
{
if (lean_obj_tag(v_x_3376_) == 0)
{
return v_x_3375_;
}
else
{
lean_object* v_key_3377_; lean_object* v_value_3378_; lean_object* v_tail_3379_; lean_object* v___x_3381_; uint8_t v_isShared_3382_; uint8_t v_isSharedCheck_3412_; 
v_key_3377_ = lean_ctor_get(v_x_3376_, 0);
v_value_3378_ = lean_ctor_get(v_x_3376_, 1);
v_tail_3379_ = lean_ctor_get(v_x_3376_, 2);
v_isSharedCheck_3412_ = !lean_is_exclusive(v_x_3376_);
if (v_isSharedCheck_3412_ == 0)
{
v___x_3381_ = v_x_3376_;
v_isShared_3382_ = v_isSharedCheck_3412_;
goto v_resetjp_3380_;
}
else
{
lean_inc(v_tail_3379_);
lean_inc(v_value_3378_);
lean_inc(v_key_3377_);
lean_dec(v_x_3376_);
v___x_3381_ = lean_box(0);
v_isShared_3382_ = v_isSharedCheck_3412_;
goto v_resetjp_3380_;
}
v_resetjp_3380_:
{
lean_object* v_fst_3383_; lean_object* v_snd_3384_; lean_object* v___x_3385_; uint64_t v___x_3386_; uint64_t v___y_3388_; 
v_fst_3383_ = lean_ctor_get(v_key_3377_, 0);
v_snd_3384_ = lean_ctor_get(v_key_3377_, 1);
v___x_3385_ = lean_array_get_size(v_x_3375_);
v___x_3386_ = lean_uint64_of_nat(v_fst_3383_);
if (lean_obj_tag(v_snd_3384_) == 0)
{
uint64_t v___x_3407_; 
v___x_3407_ = 11ULL;
v___y_3388_ = v___x_3407_;
goto v___jp_3387_;
}
else
{
lean_object* v_val_3408_; uint64_t v___x_3409_; uint64_t v___x_3410_; uint64_t v___x_3411_; 
v_val_3408_ = lean_ctor_get(v_snd_3384_, 0);
v___x_3409_ = lean_uint64_of_nat(v_val_3408_);
v___x_3410_ = 13ULL;
v___x_3411_ = lean_uint64_mix_hash(v___x_3409_, v___x_3410_);
v___y_3388_ = v___x_3411_;
goto v___jp_3387_;
}
v___jp_3387_:
{
uint64_t v___x_3389_; uint64_t v___x_3390_; uint64_t v___x_3391_; uint64_t v_fold_3392_; uint64_t v___x_3393_; uint64_t v___x_3394_; uint64_t v___x_3395_; size_t v___x_3396_; size_t v___x_3397_; size_t v___x_3398_; size_t v___x_3399_; size_t v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3403_; 
v___x_3389_ = lean_uint64_mix_hash(v___x_3386_, v___y_3388_);
v___x_3390_ = 32ULL;
v___x_3391_ = lean_uint64_shift_right(v___x_3389_, v___x_3390_);
v_fold_3392_ = lean_uint64_xor(v___x_3389_, v___x_3391_);
v___x_3393_ = 16ULL;
v___x_3394_ = lean_uint64_shift_right(v_fold_3392_, v___x_3393_);
v___x_3395_ = lean_uint64_xor(v_fold_3392_, v___x_3394_);
v___x_3396_ = lean_uint64_to_usize(v___x_3395_);
v___x_3397_ = lean_usize_of_nat(v___x_3385_);
v___x_3398_ = ((size_t)1ULL);
v___x_3399_ = lean_usize_sub(v___x_3397_, v___x_3398_);
v___x_3400_ = lean_usize_land(v___x_3396_, v___x_3399_);
v___x_3401_ = lean_array_uget_borrowed(v_x_3375_, v___x_3400_);
lean_inc(v___x_3401_);
if (v_isShared_3382_ == 0)
{
lean_ctor_set(v___x_3381_, 2, v___x_3401_);
v___x_3403_ = v___x_3381_;
goto v_reusejp_3402_;
}
else
{
lean_object* v_reuseFailAlloc_3406_; 
v_reuseFailAlloc_3406_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3406_, 0, v_key_3377_);
lean_ctor_set(v_reuseFailAlloc_3406_, 1, v_value_3378_);
lean_ctor_set(v_reuseFailAlloc_3406_, 2, v___x_3401_);
v___x_3403_ = v_reuseFailAlloc_3406_;
goto v_reusejp_3402_;
}
v_reusejp_3402_:
{
lean_object* v___x_3404_; 
v___x_3404_ = lean_array_uset(v_x_3375_, v___x_3400_, v___x_3403_);
v_x_3375_ = v___x_3404_;
v_x_3376_ = v_tail_3379_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__2_spec__4_spec__6___redArg(lean_object* v_i_3413_, lean_object* v_source_3414_, lean_object* v_target_3415_){
_start:
{
lean_object* v___x_3416_; uint8_t v___x_3417_; 
v___x_3416_ = lean_array_get_size(v_source_3414_);
v___x_3417_ = lean_nat_dec_lt(v_i_3413_, v___x_3416_);
if (v___x_3417_ == 0)
{
lean_dec_ref(v_source_3414_);
lean_dec(v_i_3413_);
return v_target_3415_;
}
else
{
lean_object* v_es_3418_; lean_object* v___x_3419_; lean_object* v_source_3420_; lean_object* v_target_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; 
v_es_3418_ = lean_array_fget(v_source_3414_, v_i_3413_);
v___x_3419_ = lean_box(0);
v_source_3420_ = lean_array_fset(v_source_3414_, v_i_3413_, v___x_3419_);
v_target_3421_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__2_spec__4_spec__6_spec__12___redArg(v_target_3415_, v_es_3418_);
v___x_3422_ = lean_unsigned_to_nat(1u);
v___x_3423_ = lean_nat_add(v_i_3413_, v___x_3422_);
lean_dec(v_i_3413_);
v_i_3413_ = v___x_3423_;
v_source_3414_ = v_source_3420_;
v_target_3415_ = v_target_3421_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__2_spec__4___redArg(lean_object* v_data_3425_){
_start:
{
lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v_nbuckets_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; 
v___x_3426_ = lean_array_get_size(v_data_3425_);
v___x_3427_ = lean_unsigned_to_nat(2u);
v_nbuckets_3428_ = lean_nat_mul(v___x_3426_, v___x_3427_);
v___x_3429_ = lean_unsigned_to_nat(0u);
v___x_3430_ = lean_box(0);
v___x_3431_ = lean_mk_array(v_nbuckets_3428_, v___x_3430_);
v___x_3432_ = lean_array_propagate_mark(v_data_3425_, v___x_3431_);
v___x_3433_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__2_spec__4_spec__6___redArg(v___x_3429_, v_data_3425_, v___x_3432_);
return v___x_3433_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__2_spec__3___redArg(lean_object* v_a_3434_, lean_object* v_x_3435_){
_start:
{
if (lean_obj_tag(v_x_3435_) == 0)
{
uint8_t v___x_3436_; 
v___x_3436_ = 0;
return v___x_3436_;
}
else
{
lean_object* v_key_3437_; lean_object* v_tail_3438_; lean_object* v_fst_3439_; lean_object* v_snd_3440_; lean_object* v_fst_3441_; lean_object* v_snd_3442_; uint8_t v___x_3443_; 
v_key_3437_ = lean_ctor_get(v_x_3435_, 0);
v_tail_3438_ = lean_ctor_get(v_x_3435_, 2);
v_fst_3439_ = lean_ctor_get(v_key_3437_, 0);
v_snd_3440_ = lean_ctor_get(v_key_3437_, 1);
v_fst_3441_ = lean_ctor_get(v_a_3434_, 0);
v_snd_3442_ = lean_ctor_get(v_a_3434_, 1);
v___x_3443_ = lean_nat_dec_eq(v_fst_3439_, v_fst_3441_);
if (v___x_3443_ == 0)
{
v_x_3435_ = v_tail_3438_;
goto _start;
}
else
{
uint8_t v___x_3445_; 
v___x_3445_ = l_instBEqOption_beq___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__1_spec__1_spec__2(v_snd_3440_, v_snd_3442_);
if (v___x_3445_ == 0)
{
v_x_3435_ = v_tail_3438_;
goto _start;
}
else
{
return v___x_3445_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__2_spec__3___redArg___boxed(lean_object* v_a_3447_, lean_object* v_x_3448_){
_start:
{
uint8_t v_res_3449_; lean_object* v_r_3450_; 
v_res_3449_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__2_spec__3___redArg(v_a_3447_, v_x_3448_);
lean_dec(v_x_3448_);
lean_dec_ref(v_a_3447_);
v_r_3450_ = lean_box(v_res_3449_);
return v_r_3450_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__2___redArg(lean_object* v_m_3451_, lean_object* v_a_3452_, lean_object* v_b_3453_){
_start:
{
lean_object* v_size_3454_; lean_object* v_buckets_3455_; lean_object* v___x_3457_; uint8_t v_isShared_3458_; uint8_t v_isSharedCheck_3508_; 
v_size_3454_ = lean_ctor_get(v_m_3451_, 0);
v_buckets_3455_ = lean_ctor_get(v_m_3451_, 1);
v_isSharedCheck_3508_ = !lean_is_exclusive(v_m_3451_);
if (v_isSharedCheck_3508_ == 0)
{
v___x_3457_ = v_m_3451_;
v_isShared_3458_ = v_isSharedCheck_3508_;
goto v_resetjp_3456_;
}
else
{
lean_inc(v_buckets_3455_);
lean_inc(v_size_3454_);
lean_dec(v_m_3451_);
v___x_3457_ = lean_box(0);
v_isShared_3458_ = v_isSharedCheck_3508_;
goto v_resetjp_3456_;
}
v_resetjp_3456_:
{
lean_object* v_fst_3459_; lean_object* v_snd_3460_; lean_object* v___x_3461_; uint64_t v___x_3462_; uint64_t v___y_3464_; 
v_fst_3459_ = lean_ctor_get(v_a_3452_, 0);
v_snd_3460_ = lean_ctor_get(v_a_3452_, 1);
v___x_3461_ = lean_array_get_size(v_buckets_3455_);
v___x_3462_ = lean_uint64_of_nat(v_fst_3459_);
if (lean_obj_tag(v_snd_3460_) == 0)
{
uint64_t v___x_3503_; 
v___x_3503_ = 11ULL;
v___y_3464_ = v___x_3503_;
goto v___jp_3463_;
}
else
{
lean_object* v_val_3504_; uint64_t v___x_3505_; uint64_t v___x_3506_; uint64_t v___x_3507_; 
v_val_3504_ = lean_ctor_get(v_snd_3460_, 0);
v___x_3505_ = lean_uint64_of_nat(v_val_3504_);
v___x_3506_ = 13ULL;
v___x_3507_ = lean_uint64_mix_hash(v___x_3505_, v___x_3506_);
v___y_3464_ = v___x_3507_;
goto v___jp_3463_;
}
v___jp_3463_:
{
uint64_t v___x_3465_; uint64_t v___x_3466_; uint64_t v___x_3467_; uint64_t v_fold_3468_; uint64_t v___x_3469_; uint64_t v___x_3470_; uint64_t v___x_3471_; size_t v___x_3472_; size_t v___x_3473_; size_t v___x_3474_; size_t v___x_3475_; size_t v___x_3476_; lean_object* v_bkt_3477_; uint8_t v___x_3478_; 
v___x_3465_ = lean_uint64_mix_hash(v___x_3462_, v___y_3464_);
v___x_3466_ = 32ULL;
v___x_3467_ = lean_uint64_shift_right(v___x_3465_, v___x_3466_);
v_fold_3468_ = lean_uint64_xor(v___x_3465_, v___x_3467_);
v___x_3469_ = 16ULL;
v___x_3470_ = lean_uint64_shift_right(v_fold_3468_, v___x_3469_);
v___x_3471_ = lean_uint64_xor(v_fold_3468_, v___x_3470_);
v___x_3472_ = lean_uint64_to_usize(v___x_3471_);
v___x_3473_ = lean_usize_of_nat(v___x_3461_);
v___x_3474_ = ((size_t)1ULL);
v___x_3475_ = lean_usize_sub(v___x_3473_, v___x_3474_);
v___x_3476_ = lean_usize_land(v___x_3472_, v___x_3475_);
v_bkt_3477_ = lean_array_uget_borrowed(v_buckets_3455_, v___x_3476_);
v___x_3478_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__2_spec__3___redArg(v_a_3452_, v_bkt_3477_);
if (v___x_3478_ == 0)
{
lean_object* v___x_3479_; lean_object* v_size_x27_3480_; lean_object* v___x_3481_; lean_object* v_buckets_x27_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; uint8_t v___x_3488_; 
v___x_3479_ = lean_unsigned_to_nat(1u);
v_size_x27_3480_ = lean_nat_add(v_size_3454_, v___x_3479_);
lean_dec(v_size_3454_);
lean_inc(v_bkt_3477_);
v___x_3481_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3481_, 0, v_a_3452_);
lean_ctor_set(v___x_3481_, 1, v_b_3453_);
lean_ctor_set(v___x_3481_, 2, v_bkt_3477_);
v_buckets_x27_3482_ = lean_array_uset(v_buckets_3455_, v___x_3476_, v___x_3481_);
v___x_3483_ = lean_unsigned_to_nat(4u);
v___x_3484_ = lean_nat_mul(v_size_x27_3480_, v___x_3483_);
v___x_3485_ = lean_unsigned_to_nat(3u);
v___x_3486_ = lean_nat_div(v___x_3484_, v___x_3485_);
lean_dec(v___x_3484_);
v___x_3487_ = lean_array_get_size(v_buckets_x27_3482_);
v___x_3488_ = lean_nat_dec_le(v___x_3486_, v___x_3487_);
lean_dec(v___x_3486_);
if (v___x_3488_ == 0)
{
lean_object* v_val_3489_; lean_object* v___x_3491_; 
v_val_3489_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__2_spec__4___redArg(v_buckets_x27_3482_);
if (v_isShared_3458_ == 0)
{
lean_ctor_set(v___x_3457_, 1, v_val_3489_);
lean_ctor_set(v___x_3457_, 0, v_size_x27_3480_);
v___x_3491_ = v___x_3457_;
goto v_reusejp_3490_;
}
else
{
lean_object* v_reuseFailAlloc_3492_; 
v_reuseFailAlloc_3492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3492_, 0, v_size_x27_3480_);
lean_ctor_set(v_reuseFailAlloc_3492_, 1, v_val_3489_);
v___x_3491_ = v_reuseFailAlloc_3492_;
goto v_reusejp_3490_;
}
v_reusejp_3490_:
{
return v___x_3491_;
}
}
else
{
lean_object* v___x_3494_; 
if (v_isShared_3458_ == 0)
{
lean_ctor_set(v___x_3457_, 1, v_buckets_x27_3482_);
lean_ctor_set(v___x_3457_, 0, v_size_x27_3480_);
v___x_3494_ = v___x_3457_;
goto v_reusejp_3493_;
}
else
{
lean_object* v_reuseFailAlloc_3495_; 
v_reuseFailAlloc_3495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3495_, 0, v_size_x27_3480_);
lean_ctor_set(v_reuseFailAlloc_3495_, 1, v_buckets_x27_3482_);
v___x_3494_ = v_reuseFailAlloc_3495_;
goto v_reusejp_3493_;
}
v_reusejp_3493_:
{
return v___x_3494_;
}
}
}
else
{
lean_object* v___x_3496_; lean_object* v_buckets_x27_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3501_; 
lean_inc(v_bkt_3477_);
v___x_3496_ = lean_box(0);
v_buckets_x27_3497_ = lean_array_uset(v_buckets_3455_, v___x_3476_, v___x_3496_);
v___x_3498_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__2_spec__5___redArg(v_a_3452_, v_b_3453_, v_bkt_3477_);
v___x_3499_ = lean_array_uset(v_buckets_x27_3497_, v___x_3476_, v___x_3498_);
if (v_isShared_3458_ == 0)
{
lean_ctor_set(v___x_3457_, 1, v___x_3499_);
v___x_3501_ = v___x_3457_;
goto v_reusejp_3500_;
}
else
{
lean_object* v_reuseFailAlloc_3502_; 
v_reuseFailAlloc_3502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3502_, 0, v_size_3454_);
lean_ctor_set(v_reuseFailAlloc_3502_, 1, v___x_3499_);
v___x_3501_ = v_reuseFailAlloc_3502_;
goto v_reusejp_3500_;
}
v_reusejp_3500_:
{
return v___x_3501_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__6_spec__14___redArg(lean_object* v_a_3509_, lean_object* v_x_3510_){
_start:
{
if (lean_obj_tag(v_x_3510_) == 0)
{
lean_object* v___x_3511_; 
v___x_3511_ = lean_box(0);
return v___x_3511_;
}
else
{
lean_object* v_key_3512_; lean_object* v_value_3513_; lean_object* v_tail_3514_; uint8_t v___x_3515_; 
v_key_3512_ = lean_ctor_get(v_x_3510_, 0);
v_value_3513_ = lean_ctor_get(v_x_3510_, 1);
v_tail_3514_ = lean_ctor_get(v_x_3510_, 2);
v___x_3515_ = lean_string_dec_eq(v_key_3512_, v_a_3509_);
if (v___x_3515_ == 0)
{
v_x_3510_ = v_tail_3514_;
goto _start;
}
else
{
lean_object* v___x_3517_; 
lean_inc(v_value_3513_);
v___x_3517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3517_, 0, v_value_3513_);
return v___x_3517_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__6_spec__14___redArg___boxed(lean_object* v_a_3518_, lean_object* v_x_3519_){
_start:
{
lean_object* v_res_3520_; 
v_res_3520_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__6_spec__14___redArg(v_a_3518_, v_x_3519_);
lean_dec(v_x_3519_);
lean_dec_ref(v_a_3518_);
return v_res_3520_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__6___redArg(lean_object* v_m_3521_, lean_object* v_a_3522_){
_start:
{
lean_object* v_buckets_3523_; lean_object* v___x_3524_; uint64_t v___x_3525_; uint64_t v___x_3526_; uint64_t v___x_3527_; uint64_t v_fold_3528_; uint64_t v___x_3529_; uint64_t v___x_3530_; uint64_t v___x_3531_; size_t v___x_3532_; size_t v___x_3533_; size_t v___x_3534_; size_t v___x_3535_; size_t v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; 
v_buckets_3523_ = lean_ctor_get(v_m_3521_, 1);
v___x_3524_ = lean_array_get_size(v_buckets_3523_);
v___x_3525_ = lean_string_hash(v_a_3522_);
v___x_3526_ = 32ULL;
v___x_3527_ = lean_uint64_shift_right(v___x_3525_, v___x_3526_);
v_fold_3528_ = lean_uint64_xor(v___x_3525_, v___x_3527_);
v___x_3529_ = 16ULL;
v___x_3530_ = lean_uint64_shift_right(v_fold_3528_, v___x_3529_);
v___x_3531_ = lean_uint64_xor(v_fold_3528_, v___x_3530_);
v___x_3532_ = lean_uint64_to_usize(v___x_3531_);
v___x_3533_ = lean_usize_of_nat(v___x_3524_);
v___x_3534_ = ((size_t)1ULL);
v___x_3535_ = lean_usize_sub(v___x_3533_, v___x_3534_);
v___x_3536_ = lean_usize_land(v___x_3532_, v___x_3535_);
v___x_3537_ = lean_array_uget_borrowed(v_buckets_3523_, v___x_3536_);
v___x_3538_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__6_spec__14___redArg(v_a_3522_, v___x_3537_);
return v___x_3538_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__6___redArg___boxed(lean_object* v_m_3539_, lean_object* v_a_3540_){
_start:
{
lean_object* v_res_3541_; 
v_res_3541_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__6___redArg(v_m_3539_, v_a_3540_);
lean_dec_ref(v_a_3540_);
lean_dec_ref(v_m_3539_);
return v_res_3541_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__1_spec__1___redArg(lean_object* v_a_3542_, lean_object* v_x_3543_){
_start:
{
if (lean_obj_tag(v_x_3543_) == 0)
{
lean_object* v___x_3544_; 
v___x_3544_ = lean_box(0);
return v___x_3544_;
}
else
{
lean_object* v_key_3545_; lean_object* v_value_3546_; lean_object* v_tail_3547_; lean_object* v_fst_3548_; lean_object* v_snd_3549_; lean_object* v_fst_3550_; lean_object* v_snd_3551_; uint8_t v___x_3552_; 
v_key_3545_ = lean_ctor_get(v_x_3543_, 0);
v_value_3546_ = lean_ctor_get(v_x_3543_, 1);
v_tail_3547_ = lean_ctor_get(v_x_3543_, 2);
v_fst_3548_ = lean_ctor_get(v_key_3545_, 0);
v_snd_3549_ = lean_ctor_get(v_key_3545_, 1);
v_fst_3550_ = lean_ctor_get(v_a_3542_, 0);
v_snd_3551_ = lean_ctor_get(v_a_3542_, 1);
v___x_3552_ = lean_nat_dec_eq(v_fst_3548_, v_fst_3550_);
if (v___x_3552_ == 0)
{
v_x_3543_ = v_tail_3547_;
goto _start;
}
else
{
uint8_t v___x_3554_; 
v___x_3554_ = l_instBEqOption_beq___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__1_spec__1_spec__2(v_snd_3549_, v_snd_3551_);
if (v___x_3554_ == 0)
{
v_x_3543_ = v_tail_3547_;
goto _start;
}
else
{
lean_object* v___x_3556_; 
lean_inc(v_value_3546_);
v___x_3556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3556_, 0, v_value_3546_);
return v___x_3556_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__1_spec__1___redArg___boxed(lean_object* v_a_3557_, lean_object* v_x_3558_){
_start:
{
lean_object* v_res_3559_; 
v_res_3559_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__1_spec__1___redArg(v_a_3557_, v_x_3558_);
lean_dec(v_x_3558_);
lean_dec_ref(v_a_3557_);
return v_res_3559_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__1___redArg(lean_object* v_m_3560_, lean_object* v_a_3561_){
_start:
{
lean_object* v_buckets_3562_; lean_object* v_fst_3563_; lean_object* v_snd_3564_; lean_object* v___x_3565_; uint64_t v___x_3566_; uint64_t v___y_3568_; 
v_buckets_3562_ = lean_ctor_get(v_m_3560_, 1);
v_fst_3563_ = lean_ctor_get(v_a_3561_, 0);
v_snd_3564_ = lean_ctor_get(v_a_3561_, 1);
v___x_3565_ = lean_array_get_size(v_buckets_3562_);
v___x_3566_ = lean_uint64_of_nat(v_fst_3563_);
if (lean_obj_tag(v_snd_3564_) == 0)
{
uint64_t v___x_3583_; 
v___x_3583_ = 11ULL;
v___y_3568_ = v___x_3583_;
goto v___jp_3567_;
}
else
{
lean_object* v_val_3584_; uint64_t v___x_3585_; uint64_t v___x_3586_; uint64_t v___x_3587_; 
v_val_3584_ = lean_ctor_get(v_snd_3564_, 0);
v___x_3585_ = lean_uint64_of_nat(v_val_3584_);
v___x_3586_ = 13ULL;
v___x_3587_ = lean_uint64_mix_hash(v___x_3585_, v___x_3586_);
v___y_3568_ = v___x_3587_;
goto v___jp_3567_;
}
v___jp_3567_:
{
uint64_t v___x_3569_; uint64_t v___x_3570_; uint64_t v___x_3571_; uint64_t v_fold_3572_; uint64_t v___x_3573_; uint64_t v___x_3574_; uint64_t v___x_3575_; size_t v___x_3576_; size_t v___x_3577_; size_t v___x_3578_; size_t v___x_3579_; size_t v___x_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; 
v___x_3569_ = lean_uint64_mix_hash(v___x_3566_, v___y_3568_);
v___x_3570_ = 32ULL;
v___x_3571_ = lean_uint64_shift_right(v___x_3569_, v___x_3570_);
v_fold_3572_ = lean_uint64_xor(v___x_3569_, v___x_3571_);
v___x_3573_ = 16ULL;
v___x_3574_ = lean_uint64_shift_right(v_fold_3572_, v___x_3573_);
v___x_3575_ = lean_uint64_xor(v_fold_3572_, v___x_3574_);
v___x_3576_ = lean_uint64_to_usize(v___x_3575_);
v___x_3577_ = lean_usize_of_nat(v___x_3565_);
v___x_3578_ = ((size_t)1ULL);
v___x_3579_ = lean_usize_sub(v___x_3577_, v___x_3578_);
v___x_3580_ = lean_usize_land(v___x_3576_, v___x_3579_);
v___x_3581_ = lean_array_uget_borrowed(v_buckets_3562_, v___x_3580_);
v___x_3582_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__1_spec__1___redArg(v_a_3561_, v___x_3581_);
return v___x_3582_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__1___redArg___boxed(lean_object* v_m_3588_, lean_object* v_a_3589_){
_start:
{
lean_object* v_res_3590_; 
v_res_3590_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__1___redArg(v_m_3588_, v_a_3589_);
lean_dec_ref(v_a_3589_);
lean_dec_ref(v_m_3588_);
return v_res_3590_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__7_spec__16___redArg(lean_object* v_a_3591_, lean_object* v_x_3592_){
_start:
{
if (lean_obj_tag(v_x_3592_) == 0)
{
uint8_t v___x_3593_; 
v___x_3593_ = 0;
return v___x_3593_;
}
else
{
lean_object* v_key_3594_; lean_object* v_tail_3595_; uint8_t v___x_3596_; 
v_key_3594_ = lean_ctor_get(v_x_3592_, 0);
v_tail_3595_ = lean_ctor_get(v_x_3592_, 2);
v___x_3596_ = lean_string_dec_eq(v_key_3594_, v_a_3591_);
if (v___x_3596_ == 0)
{
v_x_3592_ = v_tail_3595_;
goto _start;
}
else
{
return v___x_3596_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__7_spec__16___redArg___boxed(lean_object* v_a_3598_, lean_object* v_x_3599_){
_start:
{
uint8_t v_res_3600_; lean_object* v_r_3601_; 
v_res_3600_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__7_spec__16___redArg(v_a_3598_, v_x_3599_);
lean_dec(v_x_3599_);
lean_dec_ref(v_a_3598_);
v_r_3601_ = lean_box(v_res_3600_);
return v_r_3601_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__7_spec__18___redArg(lean_object* v_a_3602_, lean_object* v_b_3603_, lean_object* v_x_3604_){
_start:
{
if (lean_obj_tag(v_x_3604_) == 0)
{
lean_dec(v_b_3603_);
lean_dec_ref(v_a_3602_);
return v_x_3604_;
}
else
{
lean_object* v_key_3605_; lean_object* v_value_3606_; lean_object* v_tail_3607_; lean_object* v___x_3609_; uint8_t v_isShared_3610_; uint8_t v_isSharedCheck_3619_; 
v_key_3605_ = lean_ctor_get(v_x_3604_, 0);
v_value_3606_ = lean_ctor_get(v_x_3604_, 1);
v_tail_3607_ = lean_ctor_get(v_x_3604_, 2);
v_isSharedCheck_3619_ = !lean_is_exclusive(v_x_3604_);
if (v_isSharedCheck_3619_ == 0)
{
v___x_3609_ = v_x_3604_;
v_isShared_3610_ = v_isSharedCheck_3619_;
goto v_resetjp_3608_;
}
else
{
lean_inc(v_tail_3607_);
lean_inc(v_value_3606_);
lean_inc(v_key_3605_);
lean_dec(v_x_3604_);
v___x_3609_ = lean_box(0);
v_isShared_3610_ = v_isSharedCheck_3619_;
goto v_resetjp_3608_;
}
v_resetjp_3608_:
{
uint8_t v___x_3611_; 
v___x_3611_ = lean_string_dec_eq(v_key_3605_, v_a_3602_);
if (v___x_3611_ == 0)
{
lean_object* v___x_3612_; lean_object* v___x_3614_; 
v___x_3612_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__7_spec__18___redArg(v_a_3602_, v_b_3603_, v_tail_3607_);
if (v_isShared_3610_ == 0)
{
lean_ctor_set(v___x_3609_, 2, v___x_3612_);
v___x_3614_ = v___x_3609_;
goto v_reusejp_3613_;
}
else
{
lean_object* v_reuseFailAlloc_3615_; 
v_reuseFailAlloc_3615_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3615_, 0, v_key_3605_);
lean_ctor_set(v_reuseFailAlloc_3615_, 1, v_value_3606_);
lean_ctor_set(v_reuseFailAlloc_3615_, 2, v___x_3612_);
v___x_3614_ = v_reuseFailAlloc_3615_;
goto v_reusejp_3613_;
}
v_reusejp_3613_:
{
return v___x_3614_;
}
}
else
{
lean_object* v___x_3617_; 
lean_dec(v_value_3606_);
lean_dec(v_key_3605_);
if (v_isShared_3610_ == 0)
{
lean_ctor_set(v___x_3609_, 1, v_b_3603_);
lean_ctor_set(v___x_3609_, 0, v_a_3602_);
v___x_3617_ = v___x_3609_;
goto v_reusejp_3616_;
}
else
{
lean_object* v_reuseFailAlloc_3618_; 
v_reuseFailAlloc_3618_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3618_, 0, v_a_3602_);
lean_ctor_set(v_reuseFailAlloc_3618_, 1, v_b_3603_);
lean_ctor_set(v_reuseFailAlloc_3618_, 2, v_tail_3607_);
v___x_3617_ = v_reuseFailAlloc_3618_;
goto v_reusejp_3616_;
}
v_reusejp_3616_:
{
return v___x_3617_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__7_spec__17_spec__21_spec__24___redArg(lean_object* v_x_3620_, lean_object* v_x_3621_){
_start:
{
if (lean_obj_tag(v_x_3621_) == 0)
{
return v_x_3620_;
}
else
{
lean_object* v_key_3622_; lean_object* v_value_3623_; lean_object* v_tail_3624_; lean_object* v___x_3626_; uint8_t v_isShared_3627_; uint8_t v_isSharedCheck_3647_; 
v_key_3622_ = lean_ctor_get(v_x_3621_, 0);
v_value_3623_ = lean_ctor_get(v_x_3621_, 1);
v_tail_3624_ = lean_ctor_get(v_x_3621_, 2);
v_isSharedCheck_3647_ = !lean_is_exclusive(v_x_3621_);
if (v_isSharedCheck_3647_ == 0)
{
v___x_3626_ = v_x_3621_;
v_isShared_3627_ = v_isSharedCheck_3647_;
goto v_resetjp_3625_;
}
else
{
lean_inc(v_tail_3624_);
lean_inc(v_value_3623_);
lean_inc(v_key_3622_);
lean_dec(v_x_3621_);
v___x_3626_ = lean_box(0);
v_isShared_3627_ = v_isSharedCheck_3647_;
goto v_resetjp_3625_;
}
v_resetjp_3625_:
{
lean_object* v___x_3628_; uint64_t v___x_3629_; uint64_t v___x_3630_; uint64_t v___x_3631_; uint64_t v_fold_3632_; uint64_t v___x_3633_; uint64_t v___x_3634_; uint64_t v___x_3635_; size_t v___x_3636_; size_t v___x_3637_; size_t v___x_3638_; size_t v___x_3639_; size_t v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3643_; 
v___x_3628_ = lean_array_get_size(v_x_3620_);
v___x_3629_ = lean_string_hash(v_key_3622_);
v___x_3630_ = 32ULL;
v___x_3631_ = lean_uint64_shift_right(v___x_3629_, v___x_3630_);
v_fold_3632_ = lean_uint64_xor(v___x_3629_, v___x_3631_);
v___x_3633_ = 16ULL;
v___x_3634_ = lean_uint64_shift_right(v_fold_3632_, v___x_3633_);
v___x_3635_ = lean_uint64_xor(v_fold_3632_, v___x_3634_);
v___x_3636_ = lean_uint64_to_usize(v___x_3635_);
v___x_3637_ = lean_usize_of_nat(v___x_3628_);
v___x_3638_ = ((size_t)1ULL);
v___x_3639_ = lean_usize_sub(v___x_3637_, v___x_3638_);
v___x_3640_ = lean_usize_land(v___x_3636_, v___x_3639_);
v___x_3641_ = lean_array_uget_borrowed(v_x_3620_, v___x_3640_);
lean_inc(v___x_3641_);
if (v_isShared_3627_ == 0)
{
lean_ctor_set(v___x_3626_, 2, v___x_3641_);
v___x_3643_ = v___x_3626_;
goto v_reusejp_3642_;
}
else
{
lean_object* v_reuseFailAlloc_3646_; 
v_reuseFailAlloc_3646_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3646_, 0, v_key_3622_);
lean_ctor_set(v_reuseFailAlloc_3646_, 1, v_value_3623_);
lean_ctor_set(v_reuseFailAlloc_3646_, 2, v___x_3641_);
v___x_3643_ = v_reuseFailAlloc_3646_;
goto v_reusejp_3642_;
}
v_reusejp_3642_:
{
lean_object* v___x_3644_; 
v___x_3644_ = lean_array_uset(v_x_3620_, v___x_3640_, v___x_3643_);
v_x_3620_ = v___x_3644_;
v_x_3621_ = v_tail_3624_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__7_spec__17_spec__21___redArg(lean_object* v_i_3648_, lean_object* v_source_3649_, lean_object* v_target_3650_){
_start:
{
lean_object* v___x_3651_; uint8_t v___x_3652_; 
v___x_3651_ = lean_array_get_size(v_source_3649_);
v___x_3652_ = lean_nat_dec_lt(v_i_3648_, v___x_3651_);
if (v___x_3652_ == 0)
{
lean_dec_ref(v_source_3649_);
lean_dec(v_i_3648_);
return v_target_3650_;
}
else
{
lean_object* v_es_3653_; lean_object* v___x_3654_; lean_object* v_source_3655_; lean_object* v_target_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; 
v_es_3653_ = lean_array_fget(v_source_3649_, v_i_3648_);
v___x_3654_ = lean_box(0);
v_source_3655_ = lean_array_fset(v_source_3649_, v_i_3648_, v___x_3654_);
v_target_3656_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__7_spec__17_spec__21_spec__24___redArg(v_target_3650_, v_es_3653_);
v___x_3657_ = lean_unsigned_to_nat(1u);
v___x_3658_ = lean_nat_add(v_i_3648_, v___x_3657_);
lean_dec(v_i_3648_);
v_i_3648_ = v___x_3658_;
v_source_3649_ = v_source_3655_;
v_target_3650_ = v_target_3656_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__7_spec__17___redArg(lean_object* v_data_3660_){
_start:
{
lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v_nbuckets_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; 
v___x_3661_ = lean_array_get_size(v_data_3660_);
v___x_3662_ = lean_unsigned_to_nat(2u);
v_nbuckets_3663_ = lean_nat_mul(v___x_3661_, v___x_3662_);
v___x_3664_ = lean_unsigned_to_nat(0u);
v___x_3665_ = lean_box(0);
v___x_3666_ = lean_mk_array(v_nbuckets_3663_, v___x_3665_);
v___x_3667_ = lean_array_propagate_mark(v_data_3660_, v___x_3666_);
v___x_3668_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__7_spec__17_spec__21___redArg(v___x_3664_, v_data_3660_, v___x_3667_);
return v___x_3668_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__7___redArg(lean_object* v_m_3669_, lean_object* v_a_3670_, lean_object* v_b_3671_){
_start:
{
lean_object* v_size_3672_; lean_object* v_buckets_3673_; lean_object* v___x_3675_; uint8_t v_isShared_3676_; uint8_t v_isSharedCheck_3716_; 
v_size_3672_ = lean_ctor_get(v_m_3669_, 0);
v_buckets_3673_ = lean_ctor_get(v_m_3669_, 1);
v_isSharedCheck_3716_ = !lean_is_exclusive(v_m_3669_);
if (v_isSharedCheck_3716_ == 0)
{
v___x_3675_ = v_m_3669_;
v_isShared_3676_ = v_isSharedCheck_3716_;
goto v_resetjp_3674_;
}
else
{
lean_inc(v_buckets_3673_);
lean_inc(v_size_3672_);
lean_dec(v_m_3669_);
v___x_3675_ = lean_box(0);
v_isShared_3676_ = v_isSharedCheck_3716_;
goto v_resetjp_3674_;
}
v_resetjp_3674_:
{
lean_object* v___x_3677_; uint64_t v___x_3678_; uint64_t v___x_3679_; uint64_t v___x_3680_; uint64_t v_fold_3681_; uint64_t v___x_3682_; uint64_t v___x_3683_; uint64_t v___x_3684_; size_t v___x_3685_; size_t v___x_3686_; size_t v___x_3687_; size_t v___x_3688_; size_t v___x_3689_; lean_object* v_bkt_3690_; uint8_t v___x_3691_; 
v___x_3677_ = lean_array_get_size(v_buckets_3673_);
v___x_3678_ = lean_string_hash(v_a_3670_);
v___x_3679_ = 32ULL;
v___x_3680_ = lean_uint64_shift_right(v___x_3678_, v___x_3679_);
v_fold_3681_ = lean_uint64_xor(v___x_3678_, v___x_3680_);
v___x_3682_ = 16ULL;
v___x_3683_ = lean_uint64_shift_right(v_fold_3681_, v___x_3682_);
v___x_3684_ = lean_uint64_xor(v_fold_3681_, v___x_3683_);
v___x_3685_ = lean_uint64_to_usize(v___x_3684_);
v___x_3686_ = lean_usize_of_nat(v___x_3677_);
v___x_3687_ = ((size_t)1ULL);
v___x_3688_ = lean_usize_sub(v___x_3686_, v___x_3687_);
v___x_3689_ = lean_usize_land(v___x_3685_, v___x_3688_);
v_bkt_3690_ = lean_array_uget_borrowed(v_buckets_3673_, v___x_3689_);
v___x_3691_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__7_spec__16___redArg(v_a_3670_, v_bkt_3690_);
if (v___x_3691_ == 0)
{
lean_object* v___x_3692_; lean_object* v_size_x27_3693_; lean_object* v___x_3694_; lean_object* v_buckets_x27_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; uint8_t v___x_3701_; 
v___x_3692_ = lean_unsigned_to_nat(1u);
v_size_x27_3693_ = lean_nat_add(v_size_3672_, v___x_3692_);
lean_dec(v_size_3672_);
lean_inc(v_bkt_3690_);
v___x_3694_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3694_, 0, v_a_3670_);
lean_ctor_set(v___x_3694_, 1, v_b_3671_);
lean_ctor_set(v___x_3694_, 2, v_bkt_3690_);
v_buckets_x27_3695_ = lean_array_uset(v_buckets_3673_, v___x_3689_, v___x_3694_);
v___x_3696_ = lean_unsigned_to_nat(4u);
v___x_3697_ = lean_nat_mul(v_size_x27_3693_, v___x_3696_);
v___x_3698_ = lean_unsigned_to_nat(3u);
v___x_3699_ = lean_nat_div(v___x_3697_, v___x_3698_);
lean_dec(v___x_3697_);
v___x_3700_ = lean_array_get_size(v_buckets_x27_3695_);
v___x_3701_ = lean_nat_dec_le(v___x_3699_, v___x_3700_);
lean_dec(v___x_3699_);
if (v___x_3701_ == 0)
{
lean_object* v_val_3702_; lean_object* v___x_3704_; 
v_val_3702_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__7_spec__17___redArg(v_buckets_x27_3695_);
if (v_isShared_3676_ == 0)
{
lean_ctor_set(v___x_3675_, 1, v_val_3702_);
lean_ctor_set(v___x_3675_, 0, v_size_x27_3693_);
v___x_3704_ = v___x_3675_;
goto v_reusejp_3703_;
}
else
{
lean_object* v_reuseFailAlloc_3705_; 
v_reuseFailAlloc_3705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3705_, 0, v_size_x27_3693_);
lean_ctor_set(v_reuseFailAlloc_3705_, 1, v_val_3702_);
v___x_3704_ = v_reuseFailAlloc_3705_;
goto v_reusejp_3703_;
}
v_reusejp_3703_:
{
return v___x_3704_;
}
}
else
{
lean_object* v___x_3707_; 
if (v_isShared_3676_ == 0)
{
lean_ctor_set(v___x_3675_, 1, v_buckets_x27_3695_);
lean_ctor_set(v___x_3675_, 0, v_size_x27_3693_);
v___x_3707_ = v___x_3675_;
goto v_reusejp_3706_;
}
else
{
lean_object* v_reuseFailAlloc_3708_; 
v_reuseFailAlloc_3708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3708_, 0, v_size_x27_3693_);
lean_ctor_set(v_reuseFailAlloc_3708_, 1, v_buckets_x27_3695_);
v___x_3707_ = v_reuseFailAlloc_3708_;
goto v_reusejp_3706_;
}
v_reusejp_3706_:
{
return v___x_3707_;
}
}
}
else
{
lean_object* v___x_3709_; lean_object* v_buckets_x27_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3714_; 
lean_inc(v_bkt_3690_);
v___x_3709_ = lean_box(0);
v_buckets_x27_3710_ = lean_array_uset(v_buckets_3673_, v___x_3689_, v___x_3709_);
v___x_3711_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__7_spec__18___redArg(v_a_3670_, v_b_3671_, v_bkt_3690_);
v___x_3712_ = lean_array_uset(v_buckets_x27_3710_, v___x_3689_, v___x_3711_);
if (v_isShared_3676_ == 0)
{
lean_ctor_set(v___x_3675_, 1, v___x_3712_);
v___x_3714_ = v___x_3675_;
goto v_reusejp_3713_;
}
else
{
lean_object* v_reuseFailAlloc_3715_; 
v_reuseFailAlloc_3715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3715_, 0, v_size_3672_);
lean_ctor_set(v_reuseFailAlloc_3715_, 1, v___x_3712_);
v___x_3714_ = v_reuseFailAlloc_3715_;
goto v_reusejp_3713_;
}
v_reusejp_3713_:
{
return v___x_3714_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__4_spec__10_spec__13_spec__18___redArg(lean_object* v_x_3717_, lean_object* v_x_3718_){
_start:
{
if (lean_obj_tag(v_x_3718_) == 0)
{
return v_x_3717_;
}
else
{
lean_object* v_key_3719_; lean_object* v_value_3720_; lean_object* v_tail_3721_; lean_object* v___x_3723_; uint8_t v_isShared_3724_; uint8_t v_isSharedCheck_3744_; 
v_key_3719_ = lean_ctor_get(v_x_3718_, 0);
v_value_3720_ = lean_ctor_get(v_x_3718_, 1);
v_tail_3721_ = lean_ctor_get(v_x_3718_, 2);
v_isSharedCheck_3744_ = !lean_is_exclusive(v_x_3718_);
if (v_isSharedCheck_3744_ == 0)
{
v___x_3723_ = v_x_3718_;
v_isShared_3724_ = v_isSharedCheck_3744_;
goto v_resetjp_3722_;
}
else
{
lean_inc(v_tail_3721_);
lean_inc(v_value_3720_);
lean_inc(v_key_3719_);
lean_dec(v_x_3718_);
v___x_3723_ = lean_box(0);
v_isShared_3724_ = v_isSharedCheck_3744_;
goto v_resetjp_3722_;
}
v_resetjp_3722_:
{
lean_object* v___x_3725_; uint64_t v___x_3726_; uint64_t v___x_3727_; uint64_t v___x_3728_; uint64_t v_fold_3729_; uint64_t v___x_3730_; uint64_t v___x_3731_; uint64_t v___x_3732_; size_t v___x_3733_; size_t v___x_3734_; size_t v___x_3735_; size_t v___x_3736_; size_t v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3740_; 
v___x_3725_ = lean_array_get_size(v_x_3717_);
v___x_3726_ = lean_uint64_of_nat(v_key_3719_);
v___x_3727_ = 32ULL;
v___x_3728_ = lean_uint64_shift_right(v___x_3726_, v___x_3727_);
v_fold_3729_ = lean_uint64_xor(v___x_3726_, v___x_3728_);
v___x_3730_ = 16ULL;
v___x_3731_ = lean_uint64_shift_right(v_fold_3729_, v___x_3730_);
v___x_3732_ = lean_uint64_xor(v_fold_3729_, v___x_3731_);
v___x_3733_ = lean_uint64_to_usize(v___x_3732_);
v___x_3734_ = lean_usize_of_nat(v___x_3725_);
v___x_3735_ = ((size_t)1ULL);
v___x_3736_ = lean_usize_sub(v___x_3734_, v___x_3735_);
v___x_3737_ = lean_usize_land(v___x_3733_, v___x_3736_);
v___x_3738_ = lean_array_uget_borrowed(v_x_3717_, v___x_3737_);
lean_inc(v___x_3738_);
if (v_isShared_3724_ == 0)
{
lean_ctor_set(v___x_3723_, 2, v___x_3738_);
v___x_3740_ = v___x_3723_;
goto v_reusejp_3739_;
}
else
{
lean_object* v_reuseFailAlloc_3743_; 
v_reuseFailAlloc_3743_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3743_, 0, v_key_3719_);
lean_ctor_set(v_reuseFailAlloc_3743_, 1, v_value_3720_);
lean_ctor_set(v_reuseFailAlloc_3743_, 2, v___x_3738_);
v___x_3740_ = v_reuseFailAlloc_3743_;
goto v_reusejp_3739_;
}
v_reusejp_3739_:
{
lean_object* v___x_3741_; 
v___x_3741_ = lean_array_uset(v_x_3717_, v___x_3737_, v___x_3740_);
v_x_3717_ = v___x_3741_;
v_x_3718_ = v_tail_3721_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__4_spec__10_spec__13___redArg(lean_object* v_i_3745_, lean_object* v_source_3746_, lean_object* v_target_3747_){
_start:
{
lean_object* v___x_3748_; uint8_t v___x_3749_; 
v___x_3748_ = lean_array_get_size(v_source_3746_);
v___x_3749_ = lean_nat_dec_lt(v_i_3745_, v___x_3748_);
if (v___x_3749_ == 0)
{
lean_dec_ref(v_source_3746_);
lean_dec(v_i_3745_);
return v_target_3747_;
}
else
{
lean_object* v_es_3750_; lean_object* v___x_3751_; lean_object* v_source_3752_; lean_object* v_target_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; 
v_es_3750_ = lean_array_fget(v_source_3746_, v_i_3745_);
v___x_3751_ = lean_box(0);
v_source_3752_ = lean_array_fset(v_source_3746_, v_i_3745_, v___x_3751_);
v_target_3753_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__4_spec__10_spec__13_spec__18___redArg(v_target_3747_, v_es_3750_);
v___x_3754_ = lean_unsigned_to_nat(1u);
v___x_3755_ = lean_nat_add(v_i_3745_, v___x_3754_);
lean_dec(v_i_3745_);
v_i_3745_ = v___x_3755_;
v_source_3746_ = v_source_3752_;
v_target_3747_ = v_target_3753_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__4_spec__10___redArg(lean_object* v_data_3757_){
_start:
{
lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v_nbuckets_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; 
v___x_3758_ = lean_array_get_size(v_data_3757_);
v___x_3759_ = lean_unsigned_to_nat(2u);
v_nbuckets_3760_ = lean_nat_mul(v___x_3758_, v___x_3759_);
v___x_3761_ = lean_unsigned_to_nat(0u);
v___x_3762_ = lean_box(0);
v___x_3763_ = lean_mk_array(v_nbuckets_3760_, v___x_3762_);
v___x_3764_ = lean_array_propagate_mark(v_data_3757_, v___x_3763_);
v___x_3765_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__4_spec__10_spec__13___redArg(v___x_3761_, v_data_3757_, v___x_3764_);
return v___x_3765_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__4_spec__9___redArg(lean_object* v_a_3766_, lean_object* v_x_3767_){
_start:
{
if (lean_obj_tag(v_x_3767_) == 0)
{
uint8_t v___x_3768_; 
v___x_3768_ = 0;
return v___x_3768_;
}
else
{
lean_object* v_key_3769_; lean_object* v_tail_3770_; uint8_t v___x_3771_; 
v_key_3769_ = lean_ctor_get(v_x_3767_, 0);
v_tail_3770_ = lean_ctor_get(v_x_3767_, 2);
v___x_3771_ = lean_nat_dec_eq(v_key_3769_, v_a_3766_);
if (v___x_3771_ == 0)
{
v_x_3767_ = v_tail_3770_;
goto _start;
}
else
{
return v___x_3771_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__4_spec__9___redArg___boxed(lean_object* v_a_3773_, lean_object* v_x_3774_){
_start:
{
uint8_t v_res_3775_; lean_object* v_r_3776_; 
v_res_3775_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__4_spec__9___redArg(v_a_3773_, v_x_3774_);
lean_dec(v_x_3774_);
lean_dec(v_a_3773_);
v_r_3776_ = lean_box(v_res_3775_);
return v_r_3776_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__4_spec__11___redArg(lean_object* v_a_3777_, lean_object* v_b_3778_, lean_object* v_x_3779_){
_start:
{
if (lean_obj_tag(v_x_3779_) == 0)
{
lean_dec(v_b_3778_);
lean_dec(v_a_3777_);
return v_x_3779_;
}
else
{
lean_object* v_key_3780_; lean_object* v_value_3781_; lean_object* v_tail_3782_; lean_object* v___x_3784_; uint8_t v_isShared_3785_; uint8_t v_isSharedCheck_3794_; 
v_key_3780_ = lean_ctor_get(v_x_3779_, 0);
v_value_3781_ = lean_ctor_get(v_x_3779_, 1);
v_tail_3782_ = lean_ctor_get(v_x_3779_, 2);
v_isSharedCheck_3794_ = !lean_is_exclusive(v_x_3779_);
if (v_isSharedCheck_3794_ == 0)
{
v___x_3784_ = v_x_3779_;
v_isShared_3785_ = v_isSharedCheck_3794_;
goto v_resetjp_3783_;
}
else
{
lean_inc(v_tail_3782_);
lean_inc(v_value_3781_);
lean_inc(v_key_3780_);
lean_dec(v_x_3779_);
v___x_3784_ = lean_box(0);
v_isShared_3785_ = v_isSharedCheck_3794_;
goto v_resetjp_3783_;
}
v_resetjp_3783_:
{
uint8_t v___x_3786_; 
v___x_3786_ = lean_nat_dec_eq(v_key_3780_, v_a_3777_);
if (v___x_3786_ == 0)
{
lean_object* v___x_3787_; lean_object* v___x_3789_; 
v___x_3787_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__4_spec__11___redArg(v_a_3777_, v_b_3778_, v_tail_3782_);
if (v_isShared_3785_ == 0)
{
lean_ctor_set(v___x_3784_, 2, v___x_3787_);
v___x_3789_ = v___x_3784_;
goto v_reusejp_3788_;
}
else
{
lean_object* v_reuseFailAlloc_3790_; 
v_reuseFailAlloc_3790_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3790_, 0, v_key_3780_);
lean_ctor_set(v_reuseFailAlloc_3790_, 1, v_value_3781_);
lean_ctor_set(v_reuseFailAlloc_3790_, 2, v___x_3787_);
v___x_3789_ = v_reuseFailAlloc_3790_;
goto v_reusejp_3788_;
}
v_reusejp_3788_:
{
return v___x_3789_;
}
}
else
{
lean_object* v___x_3792_; 
lean_dec(v_value_3781_);
lean_dec(v_key_3780_);
if (v_isShared_3785_ == 0)
{
lean_ctor_set(v___x_3784_, 1, v_b_3778_);
lean_ctor_set(v___x_3784_, 0, v_a_3777_);
v___x_3792_ = v___x_3784_;
goto v_reusejp_3791_;
}
else
{
lean_object* v_reuseFailAlloc_3793_; 
v_reuseFailAlloc_3793_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3793_, 0, v_a_3777_);
lean_ctor_set(v_reuseFailAlloc_3793_, 1, v_b_3778_);
lean_ctor_set(v_reuseFailAlloc_3793_, 2, v_tail_3782_);
v___x_3792_ = v_reuseFailAlloc_3793_;
goto v_reusejp_3791_;
}
v_reusejp_3791_:
{
return v___x_3792_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__4___redArg(lean_object* v_m_3795_, lean_object* v_a_3796_, lean_object* v_b_3797_){
_start:
{
lean_object* v_size_3798_; lean_object* v_buckets_3799_; lean_object* v___x_3801_; uint8_t v_isShared_3802_; uint8_t v_isSharedCheck_3842_; 
v_size_3798_ = lean_ctor_get(v_m_3795_, 0);
v_buckets_3799_ = lean_ctor_get(v_m_3795_, 1);
v_isSharedCheck_3842_ = !lean_is_exclusive(v_m_3795_);
if (v_isSharedCheck_3842_ == 0)
{
v___x_3801_ = v_m_3795_;
v_isShared_3802_ = v_isSharedCheck_3842_;
goto v_resetjp_3800_;
}
else
{
lean_inc(v_buckets_3799_);
lean_inc(v_size_3798_);
lean_dec(v_m_3795_);
v___x_3801_ = lean_box(0);
v_isShared_3802_ = v_isSharedCheck_3842_;
goto v_resetjp_3800_;
}
v_resetjp_3800_:
{
lean_object* v___x_3803_; uint64_t v___x_3804_; uint64_t v___x_3805_; uint64_t v___x_3806_; uint64_t v_fold_3807_; uint64_t v___x_3808_; uint64_t v___x_3809_; uint64_t v___x_3810_; size_t v___x_3811_; size_t v___x_3812_; size_t v___x_3813_; size_t v___x_3814_; size_t v___x_3815_; lean_object* v_bkt_3816_; uint8_t v___x_3817_; 
v___x_3803_ = lean_array_get_size(v_buckets_3799_);
v___x_3804_ = lean_uint64_of_nat(v_a_3796_);
v___x_3805_ = 32ULL;
v___x_3806_ = lean_uint64_shift_right(v___x_3804_, v___x_3805_);
v_fold_3807_ = lean_uint64_xor(v___x_3804_, v___x_3806_);
v___x_3808_ = 16ULL;
v___x_3809_ = lean_uint64_shift_right(v_fold_3807_, v___x_3808_);
v___x_3810_ = lean_uint64_xor(v_fold_3807_, v___x_3809_);
v___x_3811_ = lean_uint64_to_usize(v___x_3810_);
v___x_3812_ = lean_usize_of_nat(v___x_3803_);
v___x_3813_ = ((size_t)1ULL);
v___x_3814_ = lean_usize_sub(v___x_3812_, v___x_3813_);
v___x_3815_ = lean_usize_land(v___x_3811_, v___x_3814_);
v_bkt_3816_ = lean_array_uget_borrowed(v_buckets_3799_, v___x_3815_);
v___x_3817_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__4_spec__9___redArg(v_a_3796_, v_bkt_3816_);
if (v___x_3817_ == 0)
{
lean_object* v___x_3818_; lean_object* v_size_x27_3819_; lean_object* v___x_3820_; lean_object* v_buckets_x27_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; uint8_t v___x_3827_; 
v___x_3818_ = lean_unsigned_to_nat(1u);
v_size_x27_3819_ = lean_nat_add(v_size_3798_, v___x_3818_);
lean_dec(v_size_3798_);
lean_inc(v_bkt_3816_);
v___x_3820_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3820_, 0, v_a_3796_);
lean_ctor_set(v___x_3820_, 1, v_b_3797_);
lean_ctor_set(v___x_3820_, 2, v_bkt_3816_);
v_buckets_x27_3821_ = lean_array_uset(v_buckets_3799_, v___x_3815_, v___x_3820_);
v___x_3822_ = lean_unsigned_to_nat(4u);
v___x_3823_ = lean_nat_mul(v_size_x27_3819_, v___x_3822_);
v___x_3824_ = lean_unsigned_to_nat(3u);
v___x_3825_ = lean_nat_div(v___x_3823_, v___x_3824_);
lean_dec(v___x_3823_);
v___x_3826_ = lean_array_get_size(v_buckets_x27_3821_);
v___x_3827_ = lean_nat_dec_le(v___x_3825_, v___x_3826_);
lean_dec(v___x_3825_);
if (v___x_3827_ == 0)
{
lean_object* v_val_3828_; lean_object* v___x_3830_; 
v_val_3828_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__4_spec__10___redArg(v_buckets_x27_3821_);
if (v_isShared_3802_ == 0)
{
lean_ctor_set(v___x_3801_, 1, v_val_3828_);
lean_ctor_set(v___x_3801_, 0, v_size_x27_3819_);
v___x_3830_ = v___x_3801_;
goto v_reusejp_3829_;
}
else
{
lean_object* v_reuseFailAlloc_3831_; 
v_reuseFailAlloc_3831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3831_, 0, v_size_x27_3819_);
lean_ctor_set(v_reuseFailAlloc_3831_, 1, v_val_3828_);
v___x_3830_ = v_reuseFailAlloc_3831_;
goto v_reusejp_3829_;
}
v_reusejp_3829_:
{
return v___x_3830_;
}
}
else
{
lean_object* v___x_3833_; 
if (v_isShared_3802_ == 0)
{
lean_ctor_set(v___x_3801_, 1, v_buckets_x27_3821_);
lean_ctor_set(v___x_3801_, 0, v_size_x27_3819_);
v___x_3833_ = v___x_3801_;
goto v_reusejp_3832_;
}
else
{
lean_object* v_reuseFailAlloc_3834_; 
v_reuseFailAlloc_3834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3834_, 0, v_size_x27_3819_);
lean_ctor_set(v_reuseFailAlloc_3834_, 1, v_buckets_x27_3821_);
v___x_3833_ = v_reuseFailAlloc_3834_;
goto v_reusejp_3832_;
}
v_reusejp_3832_:
{
return v___x_3833_;
}
}
}
else
{
lean_object* v___x_3835_; lean_object* v_buckets_x27_3836_; lean_object* v___x_3837_; lean_object* v___x_3838_; lean_object* v___x_3840_; 
lean_inc(v_bkt_3816_);
v___x_3835_ = lean_box(0);
v_buckets_x27_3836_ = lean_array_uset(v_buckets_3799_, v___x_3815_, v___x_3835_);
v___x_3837_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__4_spec__11___redArg(v_a_3796_, v_b_3797_, v_bkt_3816_);
v___x_3838_ = lean_array_uset(v_buckets_x27_3836_, v___x_3815_, v___x_3837_);
if (v_isShared_3802_ == 0)
{
lean_ctor_set(v___x_3801_, 1, v___x_3838_);
v___x_3840_ = v___x_3801_;
goto v_reusejp_3839_;
}
else
{
lean_object* v_reuseFailAlloc_3841_; 
v_reuseFailAlloc_3841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3841_, 0, v_size_3798_);
lean_ctor_set(v_reuseFailAlloc_3841_, 1, v___x_3838_);
v___x_3840_ = v_reuseFailAlloc_3841_;
goto v_reusejp_3839_;
}
v_reusejp_3839_:
{
return v___x_3840_;
}
}
}
}
}
static double _init_l___private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go___closed__0(void){
_start:
{
lean_object* v___x_3844_; uint8_t v___x_3845_; lean_object* v___x_3846_; double v___x_3847_; 
v___x_3844_ = lean_unsigned_to_nat(1u);
v___x_3845_ = 1;
v___x_3846_ = lean_unsigned_to_nat(0u);
v___x_3847_ = l_Float_ofScientific(v___x_3846_, v___x_3845_, v___x_3844_);
return v___x_3847_;
}
}
static lean_object* _init_l___private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go___boxed__const__1(void){
_start:
{
double v___x_3848_; lean_object* v___x_3849_; 
v___x_3848_ = lean_float_once(&l___private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go___closed__0, &l___private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go___closed__0_once, _init_l___private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go___closed__0);
v___x_3849_ = lean_box_float(v___x_3848_);
return v___x_3849_;
}
}
static lean_object* _init_l___private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go___closed__1(void){
_start:
{
lean_object* v___x_3850_; lean_object* v___x_3851_; 
v___x_3850_ = lean_unsigned_to_nat(1u);
v___x_3851_ = lean_nat_to_int(v___x_3850_);
return v___x_3851_;
}
}
static lean_object* _init_l___private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go___closed__2(void){
_start:
{
lean_object* v___x_3852_; lean_object* v___x_3853_; 
v___x_3852_ = lean_obj_once(&l___private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go___closed__1, &l___private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go___closed__1_once, _init_l___private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go___closed__1);
v___x_3853_ = lean_int_neg(v___x_3852_);
return v___x_3853_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go(uint8_t v_pp_3856_, lean_object* v_parentStackIdx_x3f_3857_, lean_object* v_ctx_x3f_3858_, lean_object* v_a_3859_, lean_object* v_a_3860_){
_start:
{
switch(lean_obj_tag(v_a_3859_))
{
case 9:
{
lean_object* v_data_3862_; lean_object* v_msg_3863_; lean_object* v_children_3864_; lean_object* v_cls_3865_; double v_startTime_3866_; double v_stopTime_3867_; lean_object* v_tag_3868_; lean_object* v___x_3869_; double v___x_3870_; uint8_t v___x_3871_; 
v_data_3862_ = lean_ctor_get(v_a_3859_, 0);
lean_inc_ref(v_data_3862_);
v_msg_3863_ = lean_ctor_get(v_a_3859_, 1);
lean_inc_ref(v_msg_3863_);
v_children_3864_ = lean_ctor_get(v_a_3859_, 2);
lean_inc_ref(v_children_3864_);
lean_dec_ref_known(v_a_3859_, 3);
v_cls_3865_ = lean_ctor_get(v_data_3862_, 0);
lean_inc(v_cls_3865_);
v_startTime_3866_ = lean_ctor_get_float(v_data_3862_, sizeof(void*)*3);
v_stopTime_3867_ = lean_ctor_get_float(v_data_3862_, sizeof(void*)*3 + 8);
v_tag_3868_ = lean_ctor_get(v_data_3862_, 2);
lean_inc_ref(v_tag_3868_);
lean_dec_ref(v_data_3862_);
v___x_3869_ = lean_unsigned_to_nat(0u);
v___x_3870_ = lean_float_once(&l___private_Lean_Util_Profiler_0__Lean_Firefox_getFirstStart_x3f___closed__0, &l___private_Lean_Util_Profiler_0__Lean_Firefox_getFirstStart_x3f___closed__0_once, _init_l___private_Lean_Util_Profiler_0__Lean_Firefox_getFirstStart_x3f___closed__0);
v___x_3871_ = lean_float_beq(v_startTime_3866_, v___x_3870_);
if (v___x_3871_ == 0)
{
uint8_t v___x_3872_; lean_object* v_fst_3874_; lean_object* v_toThread_3875_; lean_object* v_stringMap_3876_; lean_object* v_funcMap_3877_; lean_object* v_stackMap_3878_; lean_object* v___y_3971_; lean_object* v_fst_3972_; lean_object* v_toThread_3973_; lean_object* v_stringMap_3974_; lean_object* v_funcMap_3975_; lean_object* v_stackMap_3976_; double v_lastTime_3977_; lean_object* v___y_4021_; lean_object* v___y_4022_; lean_object* v___y_4023_; lean_object* v_fst_4080_; lean_object* v_snd_4081_; lean_object* v_funcName_4086_; lean_object* v___y_4087_; lean_object* v_funcName_4128_; lean_object* v___y_4129_; lean_object* v_funcName_4136_; lean_object* v___x_4137_; uint8_t v___x_4138_; 
v___x_3872_ = 1;
lean_inc(v_cls_3865_);
v_funcName_4136_ = l_Lean_Name_toString(v_cls_3865_, v___x_3872_);
v___x_4137_ = lean_string_utf8_byte_size(v_tag_3868_);
v___x_4138_ = lean_nat_dec_eq(v___x_4137_, v___x_3869_);
if (v___x_4138_ == 0)
{
lean_object* v___x_4139_; lean_object* v___x_4140_; lean_object* v_funcName_4141_; 
v___x_4139_ = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
v___x_4140_ = lean_string_append(v_funcName_4136_, v___x_4139_);
v_funcName_4141_ = lean_string_append(v___x_4140_, v_tag_3868_);
lean_dec_ref(v_tag_3868_);
v_funcName_4128_ = v_funcName_4141_;
v___y_4129_ = v_a_3860_;
goto v___jp_4127_;
}
else
{
lean_dec_ref(v_tag_3868_);
v_funcName_4128_ = v_funcName_4136_;
v___y_4129_ = v_a_3860_;
goto v___jp_4127_;
}
v___jp_3873_:
{
lean_object* v___x_3879_; lean_object* v___x_3880_; size_t v_sz_3881_; size_t v___x_3882_; lean_object* v___x_3883_; 
v___x_3879_ = lean_alloc_ctor(0, 4, 8);
lean_ctor_set(v___x_3879_, 0, v_toThread_3875_);
lean_ctor_set(v___x_3879_, 1, v_stringMap_3876_);
lean_ctor_set(v___x_3879_, 2, v_funcMap_3877_);
lean_ctor_set(v___x_3879_, 3, v_stackMap_3878_);
lean_ctor_set_float(v___x_3879_, sizeof(void*)*4, v_startTime_3866_);
v___x_3880_ = lean_box(0);
v_sz_3881_ = lean_array_size(v_children_3864_);
v___x_3882_ = ((size_t)0ULL);
lean_inc(v_fst_3874_);
v___x_3883_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__0(v_fst_3874_, v_pp_3856_, v_ctx_x3f_3858_, v_children_3864_, v_sz_3881_, v___x_3882_, v___x_3880_, v___x_3879_);
lean_dec_ref(v_children_3864_);
if (lean_obj_tag(v___x_3883_) == 0)
{
lean_object* v_a_3884_; lean_object* v___x_3886_; uint8_t v_isShared_3887_; uint8_t v_isSharedCheck_3969_; 
v_a_3884_ = lean_ctor_get(v___x_3883_, 0);
v_isSharedCheck_3969_ = !lean_is_exclusive(v___x_3883_);
if (v_isSharedCheck_3969_ == 0)
{
v___x_3886_ = v___x_3883_;
v_isShared_3887_ = v_isSharedCheck_3969_;
goto v_resetjp_3885_;
}
else
{
lean_inc(v_a_3884_);
lean_dec(v___x_3883_);
v___x_3886_ = lean_box(0);
v_isShared_3887_ = v_isSharedCheck_3969_;
goto v_resetjp_3885_;
}
v_resetjp_3885_:
{
lean_object* v_snd_3888_; lean_object* v___x_3890_; uint8_t v_isShared_3891_; uint8_t v_isSharedCheck_3967_; 
v_snd_3888_ = lean_ctor_get(v_a_3884_, 1);
v_isSharedCheck_3967_ = !lean_is_exclusive(v_a_3884_);
if (v_isSharedCheck_3967_ == 0)
{
lean_object* v_unused_3968_; 
v_unused_3968_ = lean_ctor_get(v_a_3884_, 0);
lean_dec(v_unused_3968_);
v___x_3890_ = v_a_3884_;
v_isShared_3891_ = v_isSharedCheck_3967_;
goto v_resetjp_3889_;
}
else
{
lean_inc(v_snd_3888_);
lean_dec(v_a_3884_);
v___x_3890_ = lean_box(0);
v_isShared_3891_ = v_isSharedCheck_3967_;
goto v_resetjp_3889_;
}
v_resetjp_3889_:
{
lean_object* v_toThread_3892_; lean_object* v_samples_3893_; lean_object* v_stringMap_3894_; lean_object* v_funcMap_3895_; lean_object* v_stackMap_3896_; double v_lastTime_3897_; lean_object* v___x_3899_; uint8_t v_isShared_3900_; uint8_t v_isSharedCheck_3965_; 
v_toThread_3892_ = lean_ctor_get(v_snd_3888_, 0);
lean_inc_ref(v_toThread_3892_);
v_samples_3893_ = lean_ctor_get(v_toThread_3892_, 2);
lean_inc_ref(v_samples_3893_);
v_stringMap_3894_ = lean_ctor_get(v_snd_3888_, 1);
v_funcMap_3895_ = lean_ctor_get(v_snd_3888_, 2);
v_stackMap_3896_ = lean_ctor_get(v_snd_3888_, 3);
v_lastTime_3897_ = lean_ctor_get_float(v_snd_3888_, sizeof(void*)*4);
v_isSharedCheck_3965_ = !lean_is_exclusive(v_snd_3888_);
if (v_isSharedCheck_3965_ == 0)
{
lean_object* v_unused_3966_; 
v_unused_3966_ = lean_ctor_get(v_snd_3888_, 0);
lean_dec(v_unused_3966_);
v___x_3899_ = v_snd_3888_;
v_isShared_3900_ = v_isSharedCheck_3965_;
goto v_resetjp_3898_;
}
else
{
lean_inc(v_stackMap_3896_);
lean_inc(v_funcMap_3895_);
lean_inc(v_stringMap_3894_);
lean_dec(v_snd_3888_);
v___x_3899_ = lean_box(0);
v_isShared_3900_ = v_isSharedCheck_3965_;
goto v_resetjp_3898_;
}
v_resetjp_3898_:
{
lean_object* v_name_3901_; lean_object* v_processType_3902_; uint8_t v_isMainThread_3903_; lean_object* v_markers_3904_; lean_object* v_stackTable_3905_; lean_object* v_frameTable_3906_; lean_object* v_resourceTable_3907_; lean_object* v_nativeSymbols_3908_; lean_object* v_stringArray_3909_; lean_object* v_funcTable_3910_; lean_object* v___x_3912_; uint8_t v_isShared_3913_; uint8_t v_isSharedCheck_3963_; 
v_name_3901_ = lean_ctor_get(v_toThread_3892_, 0);
v_processType_3902_ = lean_ctor_get(v_toThread_3892_, 1);
v_isMainThread_3903_ = lean_ctor_get_uint8(v_toThread_3892_, sizeof(void*)*10);
v_markers_3904_ = lean_ctor_get(v_toThread_3892_, 3);
v_stackTable_3905_ = lean_ctor_get(v_toThread_3892_, 4);
v_frameTable_3906_ = lean_ctor_get(v_toThread_3892_, 5);
v_resourceTable_3907_ = lean_ctor_get(v_toThread_3892_, 6);
v_nativeSymbols_3908_ = lean_ctor_get(v_toThread_3892_, 7);
v_stringArray_3909_ = lean_ctor_get(v_toThread_3892_, 8);
v_funcTable_3910_ = lean_ctor_get(v_toThread_3892_, 9);
v_isSharedCheck_3963_ = !lean_is_exclusive(v_toThread_3892_);
if (v_isSharedCheck_3963_ == 0)
{
lean_object* v_unused_3964_; 
v_unused_3964_ = lean_ctor_get(v_toThread_3892_, 2);
lean_dec(v_unused_3964_);
v___x_3912_ = v_toThread_3892_;
v_isShared_3913_ = v_isSharedCheck_3963_;
goto v_resetjp_3911_;
}
else
{
lean_inc(v_funcTable_3910_);
lean_inc(v_stringArray_3909_);
lean_inc(v_nativeSymbols_3908_);
lean_inc(v_resourceTable_3907_);
lean_inc(v_frameTable_3906_);
lean_inc(v_stackTable_3905_);
lean_inc(v_markers_3904_);
lean_inc(v_processType_3902_);
lean_inc(v_name_3901_);
lean_dec(v_toThread_3892_);
v___x_3912_ = lean_box(0);
v_isShared_3913_ = v_isSharedCheck_3963_;
goto v_resetjp_3911_;
}
v_resetjp_3911_:
{
lean_object* v_stack_3914_; lean_object* v_time_3915_; lean_object* v_weight_3916_; lean_object* v_threadCPUDelta_3917_; lean_object* v_length_3918_; lean_object* v___x_3920_; uint8_t v_isShared_3921_; uint8_t v_isSharedCheck_3961_; 
v_stack_3914_ = lean_ctor_get(v_samples_3893_, 0);
v_time_3915_ = lean_ctor_get(v_samples_3893_, 1);
v_weight_3916_ = lean_ctor_get(v_samples_3893_, 2);
v_threadCPUDelta_3917_ = lean_ctor_get(v_samples_3893_, 4);
v_length_3918_ = lean_ctor_get(v_samples_3893_, 5);
v_isSharedCheck_3961_ = !lean_is_exclusive(v_samples_3893_);
if (v_isSharedCheck_3961_ == 0)
{
lean_object* v_unused_3962_; 
v_unused_3962_ = lean_ctor_get(v_samples_3893_, 3);
lean_dec(v_unused_3962_);
v___x_3920_ = v_samples_3893_;
v_isShared_3921_ = v_isSharedCheck_3961_;
goto v_resetjp_3919_;
}
else
{
lean_inc(v_length_3918_);
lean_inc(v_threadCPUDelta_3917_);
lean_inc(v_weight_3916_);
lean_inc(v_time_3915_);
lean_inc(v_stack_3914_);
lean_dec(v_samples_3893_);
v___x_3920_ = lean_box(0);
v_isShared_3921_ = v_isSharedCheck_3961_;
goto v_resetjp_3919_;
}
v_resetjp_3919_:
{
lean_object* v___x_3922_; lean_object* v___x_3923_; double v___x_3924_; double v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; double v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; double v___x_3933_; double v___x_3934_; lean_object* v___x_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; lean_object* v___x_3938_; lean_object* v___x_3939_; double v___x_3940_; double v___x_3941_; lean_object* v___x_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v___x_3947_; 
lean_inc(v_fst_3874_);
v___x_3922_ = lean_array_push(v_stack_3914_, v_fst_3874_);
v___x_3923_ = lean_array_push(v___x_3922_, v_fst_3874_);
v___x_3924_ = lean_float_once(&l_Lean_Firefox_instCoeFloatMilliseconds___lam__0___closed__0, &l_Lean_Firefox_instCoeFloatMilliseconds___lam__0___closed__0_once, _init_l_Lean_Firefox_instCoeFloatMilliseconds___lam__0___closed__0);
v___x_3925_ = lean_float_mul(v_lastTime_3897_, v___x_3924_);
v___x_3926_ = lean_box_float(v___x_3925_);
v___x_3927_ = lean_array_push(v_time_3915_, v___x_3926_);
v___x_3928_ = lean_float_mul(v_stopTime_3867_, v___x_3924_);
v___x_3929_ = lean_box_float(v___x_3928_);
v___x_3930_ = lean_array_push(v___x_3927_, v___x_3929_);
v___x_3931_ = l___private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go___boxed__const__1;
v___x_3932_ = lean_array_push(v_weight_3916_, v___x_3931_);
v___x_3933_ = lean_float_sub(v_stopTime_3867_, v_lastTime_3897_);
v___x_3934_ = lean_float_mul(v___x_3933_, v___x_3924_);
v___x_3935_ = lean_box_float(v___x_3934_);
v___x_3936_ = lean_array_push(v___x_3932_, v___x_3935_);
v___x_3937_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__0___closed__0));
v___x_3938_ = l___private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go___boxed__const__1;
v___x_3939_ = lean_array_push(v_threadCPUDelta_3917_, v___x_3938_);
v___x_3940_ = lean_float_once(&l_Lean_Firefox_instCoeFloatMicroseconds___lam__0___closed__0, &l_Lean_Firefox_instCoeFloatMicroseconds___lam__0___closed__0_once, _init_l_Lean_Firefox_instCoeFloatMicroseconds___lam__0___closed__0);
v___x_3941_ = lean_float_mul(v___x_3933_, v___x_3940_);
v___x_3942_ = lean_box_float(v___x_3941_);
v___x_3943_ = lean_array_push(v___x_3939_, v___x_3942_);
v___x_3944_ = lean_unsigned_to_nat(2u);
v___x_3945_ = lean_nat_add(v_length_3918_, v___x_3944_);
lean_dec(v_length_3918_);
if (v_isShared_3921_ == 0)
{
lean_ctor_set(v___x_3920_, 5, v___x_3945_);
lean_ctor_set(v___x_3920_, 4, v___x_3943_);
lean_ctor_set(v___x_3920_, 3, v___x_3937_);
lean_ctor_set(v___x_3920_, 2, v___x_3936_);
lean_ctor_set(v___x_3920_, 1, v___x_3930_);
lean_ctor_set(v___x_3920_, 0, v___x_3923_);
v___x_3947_ = v___x_3920_;
goto v_reusejp_3946_;
}
else
{
lean_object* v_reuseFailAlloc_3960_; 
v_reuseFailAlloc_3960_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3960_, 0, v___x_3923_);
lean_ctor_set(v_reuseFailAlloc_3960_, 1, v___x_3930_);
lean_ctor_set(v_reuseFailAlloc_3960_, 2, v___x_3936_);
lean_ctor_set(v_reuseFailAlloc_3960_, 3, v___x_3937_);
lean_ctor_set(v_reuseFailAlloc_3960_, 4, v___x_3943_);
lean_ctor_set(v_reuseFailAlloc_3960_, 5, v___x_3945_);
v___x_3947_ = v_reuseFailAlloc_3960_;
goto v_reusejp_3946_;
}
v_reusejp_3946_:
{
lean_object* v___x_3949_; 
if (v_isShared_3913_ == 0)
{
lean_ctor_set(v___x_3912_, 2, v___x_3947_);
v___x_3949_ = v___x_3912_;
goto v_reusejp_3948_;
}
else
{
lean_object* v_reuseFailAlloc_3959_; 
v_reuseFailAlloc_3959_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_3959_, 0, v_name_3901_);
lean_ctor_set(v_reuseFailAlloc_3959_, 1, v_processType_3902_);
lean_ctor_set(v_reuseFailAlloc_3959_, 2, v___x_3947_);
lean_ctor_set(v_reuseFailAlloc_3959_, 3, v_markers_3904_);
lean_ctor_set(v_reuseFailAlloc_3959_, 4, v_stackTable_3905_);
lean_ctor_set(v_reuseFailAlloc_3959_, 5, v_frameTable_3906_);
lean_ctor_set(v_reuseFailAlloc_3959_, 6, v_resourceTable_3907_);
lean_ctor_set(v_reuseFailAlloc_3959_, 7, v_nativeSymbols_3908_);
lean_ctor_set(v_reuseFailAlloc_3959_, 8, v_stringArray_3909_);
lean_ctor_set(v_reuseFailAlloc_3959_, 9, v_funcTable_3910_);
lean_ctor_set_uint8(v_reuseFailAlloc_3959_, sizeof(void*)*10, v_isMainThread_3903_);
v___x_3949_ = v_reuseFailAlloc_3959_;
goto v_reusejp_3948_;
}
v_reusejp_3948_:
{
lean_object* v___x_3951_; 
if (v_isShared_3900_ == 0)
{
lean_ctor_set(v___x_3899_, 0, v___x_3949_);
v___x_3951_ = v___x_3899_;
goto v_reusejp_3950_;
}
else
{
lean_object* v_reuseFailAlloc_3958_; 
v_reuseFailAlloc_3958_ = lean_alloc_ctor(0, 4, 8);
lean_ctor_set(v_reuseFailAlloc_3958_, 0, v___x_3949_);
lean_ctor_set(v_reuseFailAlloc_3958_, 1, v_stringMap_3894_);
lean_ctor_set(v_reuseFailAlloc_3958_, 2, v_funcMap_3895_);
lean_ctor_set(v_reuseFailAlloc_3958_, 3, v_stackMap_3896_);
v___x_3951_ = v_reuseFailAlloc_3958_;
goto v_reusejp_3950_;
}
v_reusejp_3950_:
{
lean_object* v___x_3953_; 
lean_ctor_set_float(v___x_3951_, sizeof(void*)*4, v_stopTime_3867_);
if (v_isShared_3891_ == 0)
{
lean_ctor_set(v___x_3890_, 1, v___x_3951_);
lean_ctor_set(v___x_3890_, 0, v___x_3880_);
v___x_3953_ = v___x_3890_;
goto v_reusejp_3952_;
}
else
{
lean_object* v_reuseFailAlloc_3957_; 
v_reuseFailAlloc_3957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3957_, 0, v___x_3880_);
lean_ctor_set(v_reuseFailAlloc_3957_, 1, v___x_3951_);
v___x_3953_ = v_reuseFailAlloc_3957_;
goto v_reusejp_3952_;
}
v_reusejp_3952_:
{
lean_object* v___x_3955_; 
if (v_isShared_3887_ == 0)
{
lean_ctor_set(v___x_3886_, 0, v___x_3953_);
v___x_3955_ = v___x_3886_;
goto v_reusejp_3954_;
}
else
{
lean_object* v_reuseFailAlloc_3956_; 
v_reuseFailAlloc_3956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3956_, 0, v___x_3953_);
v___x_3955_ = v_reuseFailAlloc_3956_;
goto v_reusejp_3954_;
}
v_reusejp_3954_:
{
return v___x_3955_;
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
lean_dec(v_fst_3874_);
return v___x_3883_;
}
}
v___jp_3970_:
{
lean_object* v___x_3978_; lean_object* v___x_3979_; 
lean_inc(v_parentStackIdx_x3f_3857_);
lean_inc(v_fst_3972_);
v___x_3978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3978_, 0, v_fst_3972_);
lean_ctor_set(v___x_3978_, 1, v_parentStackIdx_x3f_3857_);
v___x_3979_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__1___redArg(v_stackMap_3976_, v___x_3978_);
if (lean_obj_tag(v___x_3979_) == 1)
{
lean_object* v_val_3980_; 
lean_dec_ref_known(v___x_3978_, 2);
lean_dec(v_fst_3972_);
lean_dec(v___y_3971_);
lean_dec(v_parentStackIdx_x3f_3857_);
v_val_3980_ = lean_ctor_get(v___x_3979_, 0);
lean_inc(v_val_3980_);
lean_dec_ref_known(v___x_3979_, 1);
v_fst_3874_ = v_val_3980_;
v_toThread_3875_ = v_toThread_3973_;
v_stringMap_3876_ = v_stringMap_3974_;
v_funcMap_3877_ = v_funcMap_3975_;
v_stackMap_3878_ = v_stackMap_3976_;
goto v___jp_3873_;
}
else
{
lean_object* v_stackTable_3981_; lean_object* v_size_3982_; lean_object* v_name_3983_; lean_object* v_processType_3984_; uint8_t v_isMainThread_3985_; lean_object* v_samples_3986_; lean_object* v_markers_3987_; lean_object* v_frameTable_3988_; lean_object* v_resourceTable_3989_; lean_object* v_nativeSymbols_3990_; lean_object* v_stringArray_3991_; lean_object* v_funcTable_3992_; lean_object* v___x_3994_; uint8_t v_isShared_3995_; uint8_t v_isSharedCheck_4018_; 
lean_dec(v___x_3979_);
v_stackTable_3981_ = lean_ctor_get(v_toThread_3973_, 4);
lean_inc_ref(v_stackTable_3981_);
v_size_3982_ = lean_ctor_get(v_stackMap_3976_, 0);
lean_inc(v_size_3982_);
v_name_3983_ = lean_ctor_get(v_toThread_3973_, 0);
v_processType_3984_ = lean_ctor_get(v_toThread_3973_, 1);
v_isMainThread_3985_ = lean_ctor_get_uint8(v_toThread_3973_, sizeof(void*)*10);
v_samples_3986_ = lean_ctor_get(v_toThread_3973_, 2);
v_markers_3987_ = lean_ctor_get(v_toThread_3973_, 3);
v_frameTable_3988_ = lean_ctor_get(v_toThread_3973_, 5);
v_resourceTable_3989_ = lean_ctor_get(v_toThread_3973_, 6);
v_nativeSymbols_3990_ = lean_ctor_get(v_toThread_3973_, 7);
v_stringArray_3991_ = lean_ctor_get(v_toThread_3973_, 8);
v_funcTable_3992_ = lean_ctor_get(v_toThread_3973_, 9);
v_isSharedCheck_4018_ = !lean_is_exclusive(v_toThread_3973_);
if (v_isSharedCheck_4018_ == 0)
{
lean_object* v_unused_4019_; 
v_unused_4019_ = lean_ctor_get(v_toThread_3973_, 4);
lean_dec(v_unused_4019_);
v___x_3994_ = v_toThread_3973_;
v_isShared_3995_ = v_isSharedCheck_4018_;
goto v_resetjp_3993_;
}
else
{
lean_inc(v_funcTable_3992_);
lean_inc(v_stringArray_3991_);
lean_inc(v_nativeSymbols_3990_);
lean_inc(v_resourceTable_3989_);
lean_inc(v_frameTable_3988_);
lean_inc(v_markers_3987_);
lean_inc(v_samples_3986_);
lean_inc(v_processType_3984_);
lean_inc(v_name_3983_);
lean_dec(v_toThread_3973_);
v___x_3994_ = lean_box(0);
v_isShared_3995_ = v_isSharedCheck_4018_;
goto v_resetjp_3993_;
}
v_resetjp_3993_:
{
lean_object* v_frame_3996_; lean_object* v_category_3997_; lean_object* v_subcategory_3998_; lean_object* v_prefix_3999_; lean_object* v_length_4000_; lean_object* v___x_4002_; uint8_t v_isShared_4003_; uint8_t v_isSharedCheck_4017_; 
v_frame_3996_ = lean_ctor_get(v_stackTable_3981_, 0);
v_category_3997_ = lean_ctor_get(v_stackTable_3981_, 1);
v_subcategory_3998_ = lean_ctor_get(v_stackTable_3981_, 2);
v_prefix_3999_ = lean_ctor_get(v_stackTable_3981_, 3);
v_length_4000_ = lean_ctor_get(v_stackTable_3981_, 4);
v_isSharedCheck_4017_ = !lean_is_exclusive(v_stackTable_3981_);
if (v_isSharedCheck_4017_ == 0)
{
v___x_4002_ = v_stackTable_3981_;
v_isShared_4003_ = v_isSharedCheck_4017_;
goto v_resetjp_4001_;
}
else
{
lean_inc(v_length_4000_);
lean_inc(v_prefix_3999_);
lean_inc(v_subcategory_3998_);
lean_inc(v_category_3997_);
lean_inc(v_frame_3996_);
lean_dec(v_stackTable_3981_);
v___x_4002_ = lean_box(0);
v_isShared_4003_ = v_isSharedCheck_4017_;
goto v_resetjp_4001_;
}
v_resetjp_4001_:
{
lean_object* v___x_4004_; lean_object* v___x_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; lean_object* v___x_4008_; lean_object* v___x_4009_; lean_object* v___x_4011_; 
v___x_4004_ = lean_array_push(v_frame_3996_, v_fst_3972_);
v___x_4005_ = lean_array_push(v_category_3997_, v___y_3971_);
v___x_4006_ = lean_array_push(v_subcategory_3998_, v___x_3869_);
v___x_4007_ = lean_array_push(v_prefix_3999_, v_parentStackIdx_x3f_3857_);
v___x_4008_ = lean_unsigned_to_nat(1u);
v___x_4009_ = lean_nat_add(v_length_4000_, v___x_4008_);
lean_dec(v_length_4000_);
if (v_isShared_4003_ == 0)
{
lean_ctor_set(v___x_4002_, 4, v___x_4009_);
lean_ctor_set(v___x_4002_, 3, v___x_4007_);
lean_ctor_set(v___x_4002_, 2, v___x_4006_);
lean_ctor_set(v___x_4002_, 1, v___x_4005_);
lean_ctor_set(v___x_4002_, 0, v___x_4004_);
v___x_4011_ = v___x_4002_;
goto v_reusejp_4010_;
}
else
{
lean_object* v_reuseFailAlloc_4016_; 
v_reuseFailAlloc_4016_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4016_, 0, v___x_4004_);
lean_ctor_set(v_reuseFailAlloc_4016_, 1, v___x_4005_);
lean_ctor_set(v_reuseFailAlloc_4016_, 2, v___x_4006_);
lean_ctor_set(v_reuseFailAlloc_4016_, 3, v___x_4007_);
lean_ctor_set(v_reuseFailAlloc_4016_, 4, v___x_4009_);
v___x_4011_ = v_reuseFailAlloc_4016_;
goto v_reusejp_4010_;
}
v_reusejp_4010_:
{
lean_object* v___x_4013_; 
if (v_isShared_3995_ == 0)
{
lean_ctor_set(v___x_3994_, 4, v___x_4011_);
v___x_4013_ = v___x_3994_;
goto v_reusejp_4012_;
}
else
{
lean_object* v_reuseFailAlloc_4015_; 
v_reuseFailAlloc_4015_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_4015_, 0, v_name_3983_);
lean_ctor_set(v_reuseFailAlloc_4015_, 1, v_processType_3984_);
lean_ctor_set(v_reuseFailAlloc_4015_, 2, v_samples_3986_);
lean_ctor_set(v_reuseFailAlloc_4015_, 3, v_markers_3987_);
lean_ctor_set(v_reuseFailAlloc_4015_, 4, v___x_4011_);
lean_ctor_set(v_reuseFailAlloc_4015_, 5, v_frameTable_3988_);
lean_ctor_set(v_reuseFailAlloc_4015_, 6, v_resourceTable_3989_);
lean_ctor_set(v_reuseFailAlloc_4015_, 7, v_nativeSymbols_3990_);
lean_ctor_set(v_reuseFailAlloc_4015_, 8, v_stringArray_3991_);
lean_ctor_set(v_reuseFailAlloc_4015_, 9, v_funcTable_3992_);
lean_ctor_set_uint8(v_reuseFailAlloc_4015_, sizeof(void*)*10, v_isMainThread_3985_);
v___x_4013_ = v_reuseFailAlloc_4015_;
goto v_reusejp_4012_;
}
v_reusejp_4012_:
{
lean_object* v___x_4014_; 
lean_inc(v_size_3982_);
v___x_4014_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__2___redArg(v_stackMap_3976_, v___x_3978_, v_size_3982_);
v_fst_3874_ = v_size_3982_;
v_toThread_3875_ = v___x_4013_;
v_stringMap_3876_ = v_stringMap_3974_;
v_funcMap_3877_ = v_funcMap_3975_;
v_stackMap_3878_ = v___x_4014_;
goto v___jp_3873_;
}
}
}
}
}
}
v___jp_4020_:
{
lean_object* v_toThread_4024_; lean_object* v_stringMap_4025_; lean_object* v_funcMap_4026_; lean_object* v_stackMap_4027_; double v_lastTime_4028_; lean_object* v___x_4029_; 
v_toThread_4024_ = lean_ctor_get(v___y_4022_, 0);
lean_inc_ref(v_toThread_4024_);
v_stringMap_4025_ = lean_ctor_get(v___y_4022_, 1);
lean_inc_ref(v_stringMap_4025_);
v_funcMap_4026_ = lean_ctor_get(v___y_4022_, 2);
lean_inc_ref(v_funcMap_4026_);
v_stackMap_4027_ = lean_ctor_get(v___y_4022_, 3);
lean_inc_ref(v_stackMap_4027_);
v_lastTime_4028_ = lean_ctor_get_float(v___y_4022_, sizeof(void*)*4);
lean_dec_ref(v___y_4022_);
v___x_4029_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__3___redArg(v_funcMap_4026_, v___y_4021_);
if (lean_obj_tag(v___x_4029_) == 1)
{
lean_object* v_val_4030_; 
lean_dec(v___y_4021_);
v_val_4030_ = lean_ctor_get(v___x_4029_, 0);
lean_inc(v_val_4030_);
lean_dec_ref_known(v___x_4029_, 1);
v___y_3971_ = v___y_4023_;
v_fst_3972_ = v_val_4030_;
v_toThread_3973_ = v_toThread_4024_;
v_stringMap_3974_ = v_stringMap_4025_;
v_funcMap_3975_ = v_funcMap_4026_;
v_stackMap_3976_ = v_stackMap_4027_;
v_lastTime_3977_ = v_lastTime_4028_;
goto v___jp_3970_;
}
else
{
lean_object* v_size_4031_; lean_object* v_name_4032_; lean_object* v_processType_4033_; uint8_t v_isMainThread_4034_; lean_object* v_samples_4035_; lean_object* v_markers_4036_; lean_object* v_stackTable_4037_; lean_object* v_frameTable_4038_; lean_object* v_resourceTable_4039_; lean_object* v_nativeSymbols_4040_; lean_object* v_stringArray_4041_; lean_object* v_funcTable_4042_; lean_object* v___x_4044_; uint8_t v_isShared_4045_; uint8_t v_isSharedCheck_4078_; 
lean_dec(v___x_4029_);
v_size_4031_ = lean_ctor_get(v_funcMap_4026_, 0);
lean_inc(v_size_4031_);
v_name_4032_ = lean_ctor_get(v_toThread_4024_, 0);
v_processType_4033_ = lean_ctor_get(v_toThread_4024_, 1);
v_isMainThread_4034_ = lean_ctor_get_uint8(v_toThread_4024_, sizeof(void*)*10);
v_samples_4035_ = lean_ctor_get(v_toThread_4024_, 2);
v_markers_4036_ = lean_ctor_get(v_toThread_4024_, 3);
v_stackTable_4037_ = lean_ctor_get(v_toThread_4024_, 4);
v_frameTable_4038_ = lean_ctor_get(v_toThread_4024_, 5);
v_resourceTable_4039_ = lean_ctor_get(v_toThread_4024_, 6);
v_nativeSymbols_4040_ = lean_ctor_get(v_toThread_4024_, 7);
v_stringArray_4041_ = lean_ctor_get(v_toThread_4024_, 8);
v_funcTable_4042_ = lean_ctor_get(v_toThread_4024_, 9);
v_isSharedCheck_4078_ = !lean_is_exclusive(v_toThread_4024_);
if (v_isSharedCheck_4078_ == 0)
{
v___x_4044_ = v_toThread_4024_;
v_isShared_4045_ = v_isSharedCheck_4078_;
goto v_resetjp_4043_;
}
else
{
lean_inc(v_funcTable_4042_);
lean_inc(v_stringArray_4041_);
lean_inc(v_nativeSymbols_4040_);
lean_inc(v_resourceTable_4039_);
lean_inc(v_frameTable_4038_);
lean_inc(v_stackTable_4037_);
lean_inc(v_markers_4036_);
lean_inc(v_samples_4035_);
lean_inc(v_processType_4033_);
lean_inc(v_name_4032_);
lean_dec(v_toThread_4024_);
v___x_4044_ = lean_box(0);
v_isShared_4045_ = v_isSharedCheck_4078_;
goto v_resetjp_4043_;
}
v_resetjp_4043_:
{
lean_object* v___x_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; lean_object* v_name_4051_; lean_object* v_resource_4052_; lean_object* v_fileName_4053_; lean_object* v_lineNumber_4054_; lean_object* v_columnNumber_4055_; lean_object* v_length_4056_; lean_object* v___x_4058_; uint8_t v_isShared_4059_; uint8_t v_isSharedCheck_4075_; 
v___x_4046_ = lean_unsigned_to_nat(1u);
v___x_4047_ = lean_obj_once(&l___private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go___closed__2, &l___private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go___closed__2_once, _init_l___private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go___closed__2);
lean_inc(v___y_4023_);
v___x_4048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4048_, 0, v___y_4023_);
v___x_4049_ = lean_box(0);
lean_inc(v_size_4031_);
v___x_4050_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_4050_, 0, v___x_4047_);
lean_ctor_set(v___x_4050_, 1, v___x_3869_);
lean_ctor_set(v___x_4050_, 2, v___x_4048_);
lean_ctor_set(v___x_4050_, 3, v___x_4049_);
lean_ctor_set(v___x_4050_, 4, v_size_4031_);
lean_ctor_set(v___x_4050_, 5, v___x_4049_);
lean_ctor_set(v___x_4050_, 6, v___x_4049_);
lean_ctor_set(v___x_4050_, 7, v___x_4049_);
lean_ctor_set(v___x_4050_, 8, v___x_4049_);
lean_ctor_set(v___x_4050_, 9, v___x_4049_);
v_name_4051_ = lean_ctor_get(v_funcTable_4042_, 0);
v_resource_4052_ = lean_ctor_get(v_funcTable_4042_, 3);
v_fileName_4053_ = lean_ctor_get(v_funcTable_4042_, 4);
v_lineNumber_4054_ = lean_ctor_get(v_funcTable_4042_, 5);
v_columnNumber_4055_ = lean_ctor_get(v_funcTable_4042_, 6);
v_length_4056_ = lean_ctor_get(v_funcTable_4042_, 7);
v_isSharedCheck_4075_ = !lean_is_exclusive(v_funcTable_4042_);
if (v_isSharedCheck_4075_ == 0)
{
lean_object* v_unused_4076_; lean_object* v_unused_4077_; 
v_unused_4076_ = lean_ctor_get(v_funcTable_4042_, 2);
lean_dec(v_unused_4076_);
v_unused_4077_ = lean_ctor_get(v_funcTable_4042_, 1);
lean_dec(v_unused_4077_);
v___x_4058_ = v_funcTable_4042_;
v_isShared_4059_ = v_isSharedCheck_4075_;
goto v_resetjp_4057_;
}
else
{
lean_inc(v_length_4056_);
lean_inc(v_columnNumber_4055_);
lean_inc(v_lineNumber_4054_);
lean_inc(v_fileName_4053_);
lean_inc(v_resource_4052_);
lean_inc(v_name_4051_);
lean_dec(v_funcTable_4042_);
v___x_4058_ = lean_box(0);
v_isShared_4059_ = v_isSharedCheck_4075_;
goto v_resetjp_4057_;
}
v_resetjp_4057_:
{
lean_object* v___x_4060_; lean_object* v___x_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4069_; 
v___x_4060_ = l_Lean_Firefox_FrameTable_push(v_frameTable_4038_, v___x_4050_);
lean_inc(v___y_4021_);
v___x_4061_ = lean_array_push(v_name_4051_, v___y_4021_);
v___x_4062_ = ((lean_object*)(l___private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go___closed__3));
v___x_4063_ = lean_array_push(v_resource_4052_, v___x_4047_);
v___x_4064_ = lean_array_push(v_fileName_4053_, v___x_4049_);
v___x_4065_ = lean_array_push(v_lineNumber_4054_, v___x_4049_);
v___x_4066_ = lean_array_push(v_columnNumber_4055_, v___x_4049_);
v___x_4067_ = lean_nat_add(v_length_4056_, v___x_4046_);
lean_dec(v_length_4056_);
if (v_isShared_4059_ == 0)
{
lean_ctor_set(v___x_4058_, 7, v___x_4067_);
lean_ctor_set(v___x_4058_, 6, v___x_4066_);
lean_ctor_set(v___x_4058_, 5, v___x_4065_);
lean_ctor_set(v___x_4058_, 4, v___x_4064_);
lean_ctor_set(v___x_4058_, 3, v___x_4063_);
lean_ctor_set(v___x_4058_, 2, v___x_4062_);
lean_ctor_set(v___x_4058_, 1, v___x_4062_);
lean_ctor_set(v___x_4058_, 0, v___x_4061_);
v___x_4069_ = v___x_4058_;
goto v_reusejp_4068_;
}
else
{
lean_object* v_reuseFailAlloc_4074_; 
v_reuseFailAlloc_4074_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_4074_, 0, v___x_4061_);
lean_ctor_set(v_reuseFailAlloc_4074_, 1, v___x_4062_);
lean_ctor_set(v_reuseFailAlloc_4074_, 2, v___x_4062_);
lean_ctor_set(v_reuseFailAlloc_4074_, 3, v___x_4063_);
lean_ctor_set(v_reuseFailAlloc_4074_, 4, v___x_4064_);
lean_ctor_set(v_reuseFailAlloc_4074_, 5, v___x_4065_);
lean_ctor_set(v_reuseFailAlloc_4074_, 6, v___x_4066_);
lean_ctor_set(v_reuseFailAlloc_4074_, 7, v___x_4067_);
v___x_4069_ = v_reuseFailAlloc_4074_;
goto v_reusejp_4068_;
}
v_reusejp_4068_:
{
lean_object* v___x_4071_; 
if (v_isShared_4045_ == 0)
{
lean_ctor_set(v___x_4044_, 9, v___x_4069_);
lean_ctor_set(v___x_4044_, 5, v___x_4060_);
v___x_4071_ = v___x_4044_;
goto v_reusejp_4070_;
}
else
{
lean_object* v_reuseFailAlloc_4073_; 
v_reuseFailAlloc_4073_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_4073_, 0, v_name_4032_);
lean_ctor_set(v_reuseFailAlloc_4073_, 1, v_processType_4033_);
lean_ctor_set(v_reuseFailAlloc_4073_, 2, v_samples_4035_);
lean_ctor_set(v_reuseFailAlloc_4073_, 3, v_markers_4036_);
lean_ctor_set(v_reuseFailAlloc_4073_, 4, v_stackTable_4037_);
lean_ctor_set(v_reuseFailAlloc_4073_, 5, v___x_4060_);
lean_ctor_set(v_reuseFailAlloc_4073_, 6, v_resourceTable_4039_);
lean_ctor_set(v_reuseFailAlloc_4073_, 7, v_nativeSymbols_4040_);
lean_ctor_set(v_reuseFailAlloc_4073_, 8, v_stringArray_4041_);
lean_ctor_set(v_reuseFailAlloc_4073_, 9, v___x_4069_);
lean_ctor_set_uint8(v_reuseFailAlloc_4073_, sizeof(void*)*10, v_isMainThread_4034_);
v___x_4071_ = v_reuseFailAlloc_4073_;
goto v_reusejp_4070_;
}
v_reusejp_4070_:
{
lean_object* v___x_4072_; 
lean_inc(v_size_4031_);
v___x_4072_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__4___redArg(v_funcMap_4026_, v___y_4021_, v_size_4031_);
v___y_3971_ = v___y_4023_;
v_fst_3972_ = v_size_4031_;
v_toThread_3973_ = v___x_4071_;
v_stringMap_3974_ = v_stringMap_4025_;
v_funcMap_3975_ = v___x_4072_;
v_stackMap_3976_ = v_stackMap_4027_;
v_lastTime_3977_ = v_lastTime_4028_;
goto v___jp_3970_;
}
}
}
}
}
}
v___jp_4079_:
{
lean_object* v___x_4082_; lean_object* v___x_4083_; 
v___x_4082_ = ((lean_object*)(l_Lean_Firefox_categories));
v___x_4083_ = l_Array_findIdx_x3f_loop___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__5(v_cls_3865_, v___x_4082_, v___x_3869_);
lean_dec(v_cls_3865_);
if (lean_obj_tag(v___x_4083_) == 0)
{
v___y_4021_ = v_fst_4080_;
v___y_4022_ = v_snd_4081_;
v___y_4023_ = v___x_3869_;
goto v___jp_4020_;
}
else
{
lean_object* v_val_4084_; 
v_val_4084_ = lean_ctor_get(v___x_4083_, 0);
lean_inc(v_val_4084_);
lean_dec_ref_known(v___x_4083_, 1);
v___y_4021_ = v_fst_4080_;
v___y_4022_ = v_snd_4081_;
v___y_4023_ = v_val_4084_;
goto v___jp_4020_;
}
}
v___jp_4085_:
{
lean_object* v_toThread_4088_; lean_object* v_stringMap_4089_; lean_object* v_funcMap_4090_; lean_object* v_stackMap_4091_; double v_lastTime_4092_; lean_object* v___x_4093_; 
v_toThread_4088_ = lean_ctor_get(v___y_4087_, 0);
lean_inc_ref(v_toThread_4088_);
v_stringMap_4089_ = lean_ctor_get(v___y_4087_, 1);
v_funcMap_4090_ = lean_ctor_get(v___y_4087_, 2);
v_stackMap_4091_ = lean_ctor_get(v___y_4087_, 3);
v_lastTime_4092_ = lean_ctor_get_float(v___y_4087_, sizeof(void*)*4);
v___x_4093_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__6___redArg(v_stringMap_4089_, v_funcName_4086_);
if (lean_obj_tag(v___x_4093_) == 1)
{
lean_object* v_val_4094_; 
lean_dec_ref(v_toThread_4088_);
lean_dec_ref(v_funcName_4086_);
v_val_4094_ = lean_ctor_get(v___x_4093_, 0);
lean_inc(v_val_4094_);
lean_dec_ref_known(v___x_4093_, 1);
v_fst_4080_ = v_val_4094_;
v_snd_4081_ = v___y_4087_;
goto v___jp_4079_;
}
else
{
lean_object* v___x_4096_; uint8_t v_isShared_4097_; uint8_t v_isSharedCheck_4122_; 
lean_inc_ref(v_stackMap_4091_);
lean_inc_ref(v_funcMap_4090_);
lean_inc_ref(v_stringMap_4089_);
lean_dec(v___x_4093_);
v_isSharedCheck_4122_ = !lean_is_exclusive(v___y_4087_);
if (v_isSharedCheck_4122_ == 0)
{
lean_object* v_unused_4123_; lean_object* v_unused_4124_; lean_object* v_unused_4125_; lean_object* v_unused_4126_; 
v_unused_4123_ = lean_ctor_get(v___y_4087_, 3);
lean_dec(v_unused_4123_);
v_unused_4124_ = lean_ctor_get(v___y_4087_, 2);
lean_dec(v_unused_4124_);
v_unused_4125_ = lean_ctor_get(v___y_4087_, 1);
lean_dec(v_unused_4125_);
v_unused_4126_ = lean_ctor_get(v___y_4087_, 0);
lean_dec(v_unused_4126_);
v___x_4096_ = v___y_4087_;
v_isShared_4097_ = v_isSharedCheck_4122_;
goto v_resetjp_4095_;
}
else
{
lean_dec(v___y_4087_);
v___x_4096_ = lean_box(0);
v_isShared_4097_ = v_isSharedCheck_4122_;
goto v_resetjp_4095_;
}
v_resetjp_4095_:
{
lean_object* v_size_4098_; lean_object* v_name_4099_; lean_object* v_processType_4100_; uint8_t v_isMainThread_4101_; lean_object* v_samples_4102_; lean_object* v_markers_4103_; lean_object* v_stackTable_4104_; lean_object* v_frameTable_4105_; lean_object* v_resourceTable_4106_; lean_object* v_nativeSymbols_4107_; lean_object* v_stringArray_4108_; lean_object* v_funcTable_4109_; lean_object* v___x_4111_; uint8_t v_isShared_4112_; uint8_t v_isSharedCheck_4121_; 
v_size_4098_ = lean_ctor_get(v_stringMap_4089_, 0);
lean_inc(v_size_4098_);
v_name_4099_ = lean_ctor_get(v_toThread_4088_, 0);
v_processType_4100_ = lean_ctor_get(v_toThread_4088_, 1);
v_isMainThread_4101_ = lean_ctor_get_uint8(v_toThread_4088_, sizeof(void*)*10);
v_samples_4102_ = lean_ctor_get(v_toThread_4088_, 2);
v_markers_4103_ = lean_ctor_get(v_toThread_4088_, 3);
v_stackTable_4104_ = lean_ctor_get(v_toThread_4088_, 4);
v_frameTable_4105_ = lean_ctor_get(v_toThread_4088_, 5);
v_resourceTable_4106_ = lean_ctor_get(v_toThread_4088_, 6);
v_nativeSymbols_4107_ = lean_ctor_get(v_toThread_4088_, 7);
v_stringArray_4108_ = lean_ctor_get(v_toThread_4088_, 8);
v_funcTable_4109_ = lean_ctor_get(v_toThread_4088_, 9);
v_isSharedCheck_4121_ = !lean_is_exclusive(v_toThread_4088_);
if (v_isSharedCheck_4121_ == 0)
{
v___x_4111_ = v_toThread_4088_;
v_isShared_4112_ = v_isSharedCheck_4121_;
goto v_resetjp_4110_;
}
else
{
lean_inc(v_funcTable_4109_);
lean_inc(v_stringArray_4108_);
lean_inc(v_nativeSymbols_4107_);
lean_inc(v_resourceTable_4106_);
lean_inc(v_frameTable_4105_);
lean_inc(v_stackTable_4104_);
lean_inc(v_markers_4103_);
lean_inc(v_samples_4102_);
lean_inc(v_processType_4100_);
lean_inc(v_name_4099_);
lean_dec(v_toThread_4088_);
v___x_4111_ = lean_box(0);
v_isShared_4112_ = v_isSharedCheck_4121_;
goto v_resetjp_4110_;
}
v_resetjp_4110_:
{
lean_object* v___x_4113_; lean_object* v___x_4115_; 
lean_inc_ref(v_funcName_4086_);
v___x_4113_ = lean_array_push(v_stringArray_4108_, v_funcName_4086_);
if (v_isShared_4112_ == 0)
{
lean_ctor_set(v___x_4111_, 8, v___x_4113_);
v___x_4115_ = v___x_4111_;
goto v_reusejp_4114_;
}
else
{
lean_object* v_reuseFailAlloc_4120_; 
v_reuseFailAlloc_4120_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_4120_, 0, v_name_4099_);
lean_ctor_set(v_reuseFailAlloc_4120_, 1, v_processType_4100_);
lean_ctor_set(v_reuseFailAlloc_4120_, 2, v_samples_4102_);
lean_ctor_set(v_reuseFailAlloc_4120_, 3, v_markers_4103_);
lean_ctor_set(v_reuseFailAlloc_4120_, 4, v_stackTable_4104_);
lean_ctor_set(v_reuseFailAlloc_4120_, 5, v_frameTable_4105_);
lean_ctor_set(v_reuseFailAlloc_4120_, 6, v_resourceTable_4106_);
lean_ctor_set(v_reuseFailAlloc_4120_, 7, v_nativeSymbols_4107_);
lean_ctor_set(v_reuseFailAlloc_4120_, 8, v___x_4113_);
lean_ctor_set(v_reuseFailAlloc_4120_, 9, v_funcTable_4109_);
lean_ctor_set_uint8(v_reuseFailAlloc_4120_, sizeof(void*)*10, v_isMainThread_4101_);
v___x_4115_ = v_reuseFailAlloc_4120_;
goto v_reusejp_4114_;
}
v_reusejp_4114_:
{
lean_object* v___x_4116_; lean_object* v___x_4118_; 
lean_inc(v_size_4098_);
v___x_4116_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__7___redArg(v_stringMap_4089_, v_funcName_4086_, v_size_4098_);
if (v_isShared_4097_ == 0)
{
lean_ctor_set(v___x_4096_, 1, v___x_4116_);
lean_ctor_set(v___x_4096_, 0, v___x_4115_);
v___x_4118_ = v___x_4096_;
goto v_reusejp_4117_;
}
else
{
lean_object* v_reuseFailAlloc_4119_; 
v_reuseFailAlloc_4119_ = lean_alloc_ctor(0, 4, 8);
lean_ctor_set(v_reuseFailAlloc_4119_, 0, v___x_4115_);
lean_ctor_set(v_reuseFailAlloc_4119_, 1, v___x_4116_);
lean_ctor_set(v_reuseFailAlloc_4119_, 2, v_funcMap_4090_);
lean_ctor_set(v_reuseFailAlloc_4119_, 3, v_stackMap_4091_);
lean_ctor_set_float(v_reuseFailAlloc_4119_, sizeof(void*)*4, v_lastTime_4092_);
v___x_4118_ = v_reuseFailAlloc_4119_;
goto v_reusejp_4117_;
}
v_reusejp_4117_:
{
v_fst_4080_ = v_size_4098_;
v_snd_4081_ = v___x_4118_;
goto v___jp_4079_;
}
}
}
}
}
}
v___jp_4127_:
{
if (v_pp_3856_ == 0)
{
lean_dec_ref(v_msg_3863_);
v_funcName_4086_ = v_funcName_4128_;
v___y_4087_ = v___y_4129_;
goto v___jp_4085_;
}
else
{
lean_object* v___x_4130_; lean_object* v___x_4131_; lean_object* v___x_4132_; lean_object* v___x_4133_; lean_object* v___x_4134_; lean_object* v___x_4135_; 
lean_inc(v_ctx_x3f_3858_);
v___x_4130_ = l_Lean_MessageData_format(v_msg_3863_, v_ctx_x3f_3858_);
v___x_4131_ = ((lean_object*)(l_Lean_Firefox_instFromJsonCategory_fromJson___closed__11));
v___x_4132_ = lean_string_append(v_funcName_4128_, v___x_4131_);
v___x_4133_ = l_Std_Format_defWidth;
v___x_4134_ = l_Std_Format_pretty(v___x_4130_, v___x_4133_, v___x_3869_, v___x_3869_);
v___x_4135_ = lean_string_append(v___x_4132_, v___x_4134_);
lean_dec_ref(v___x_4134_);
v_funcName_4086_ = v___x_4135_;
v___y_4087_ = v___y_4129_;
goto v___jp_4085_;
}
}
}
else
{
lean_object* v___x_4142_; lean_object* v___x_4143_; lean_object* v___x_4144_; 
lean_dec_ref(v_tag_3868_);
lean_dec(v_cls_3865_);
lean_dec_ref(v_children_3864_);
lean_dec_ref(v_msg_3863_);
lean_dec(v_ctx_x3f_3858_);
lean_dec(v_parentStackIdx_x3f_3857_);
v___x_4142_ = lean_box(0);
v___x_4143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4143_, 0, v___x_4142_);
lean_ctor_set(v___x_4143_, 1, v_a_3860_);
v___x_4144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4144_, 0, v___x_4143_);
return v___x_4144_;
}
}
case 3:
{
lean_object* v_a_4145_; lean_object* v_a_4146_; lean_object* v___x_4147_; 
lean_dec(v_ctx_x3f_3858_);
v_a_4145_ = lean_ctor_get(v_a_3859_, 0);
lean_inc_ref(v_a_4145_);
v_a_4146_ = lean_ctor_get(v_a_3859_, 1);
lean_inc_ref(v_a_4146_);
lean_dec_ref_known(v_a_3859_, 2);
v___x_4147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4147_, 0, v_a_4145_);
v_ctx_x3f_3858_ = v___x_4147_;
v_a_3859_ = v_a_4146_;
goto _start;
}
default: 
{
lean_object* v___x_4149_; lean_object* v___x_4150_; lean_object* v___x_4151_; 
lean_dec_ref(v_a_3859_);
lean_dec(v_ctx_x3f_3858_);
lean_dec(v_parentStackIdx_x3f_3857_);
v___x_4149_ = lean_box(0);
v___x_4150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4150_, 0, v___x_4149_);
lean_ctor_set(v___x_4150_, 1, v_a_3860_);
v___x_4151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4151_, 0, v___x_4150_);
return v___x_4151_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__0(lean_object* v_fst_4152_, uint8_t v_pp_4153_, lean_object* v_ctx_x3f_4154_, lean_object* v_as_4155_, size_t v_sz_4156_, size_t v_i_4157_, lean_object* v_b_4158_, lean_object* v___y_4159_){
_start:
{
lean_object* v_a_4162_; lean_object* v_snd_4163_; uint8_t v___x_4167_; 
v___x_4167_ = lean_usize_dec_lt(v_i_4157_, v_sz_4156_);
if (v___x_4167_ == 0)
{
lean_object* v___x_4168_; lean_object* v___x_4169_; 
lean_dec(v_ctx_x3f_4154_);
lean_dec(v_fst_4152_);
v___x_4168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4168_, 0, v_b_4158_);
lean_ctor_set(v___x_4168_, 1, v___y_4159_);
v___x_4169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4169_, 0, v___x_4168_);
return v___x_4169_;
}
else
{
lean_object* v___x_4170_; lean_object* v_a_4171_; lean_object* v___x_4172_; 
v___x_4170_ = lean_box(0);
v_a_4171_ = lean_array_uget_borrowed(v_as_4155_, v_i_4157_);
v___x_4172_ = l___private_Lean_Util_Profiler_0__Lean_Firefox_getFirstStart_x3f(v_a_4171_);
if (lean_obj_tag(v___x_4172_) == 1)
{
lean_object* v_toThread_4173_; lean_object* v_samples_4174_; lean_object* v_val_4175_; lean_object* v___x_4177_; uint8_t v_isShared_4178_; uint8_t v_isSharedCheck_4257_; 
v_toThread_4173_ = lean_ctor_get(v___y_4159_, 0);
lean_inc_ref(v_toThread_4173_);
v_samples_4174_ = lean_ctor_get(v_toThread_4173_, 2);
lean_inc_ref(v_samples_4174_);
v_val_4175_ = lean_ctor_get(v___x_4172_, 0);
v_isSharedCheck_4257_ = !lean_is_exclusive(v___x_4172_);
if (v_isSharedCheck_4257_ == 0)
{
v___x_4177_ = v___x_4172_;
v_isShared_4178_ = v_isSharedCheck_4257_;
goto v_resetjp_4176_;
}
else
{
lean_inc(v_val_4175_);
lean_dec(v___x_4172_);
v___x_4177_ = lean_box(0);
v_isShared_4178_ = v_isSharedCheck_4257_;
goto v_resetjp_4176_;
}
v_resetjp_4176_:
{
lean_object* v_stringMap_4179_; lean_object* v_funcMap_4180_; lean_object* v_stackMap_4181_; double v_lastTime_4182_; lean_object* v___x_4184_; uint8_t v_isShared_4185_; uint8_t v_isSharedCheck_4255_; 
v_stringMap_4179_ = lean_ctor_get(v___y_4159_, 1);
v_funcMap_4180_ = lean_ctor_get(v___y_4159_, 2);
v_stackMap_4181_ = lean_ctor_get(v___y_4159_, 3);
v_lastTime_4182_ = lean_ctor_get_float(v___y_4159_, sizeof(void*)*4);
v_isSharedCheck_4255_ = !lean_is_exclusive(v___y_4159_);
if (v_isSharedCheck_4255_ == 0)
{
lean_object* v_unused_4256_; 
v_unused_4256_ = lean_ctor_get(v___y_4159_, 0);
lean_dec(v_unused_4256_);
v___x_4184_ = v___y_4159_;
v_isShared_4185_ = v_isSharedCheck_4255_;
goto v_resetjp_4183_;
}
else
{
lean_inc(v_stackMap_4181_);
lean_inc(v_funcMap_4180_);
lean_inc(v_stringMap_4179_);
lean_dec(v___y_4159_);
v___x_4184_ = lean_box(0);
v_isShared_4185_ = v_isSharedCheck_4255_;
goto v_resetjp_4183_;
}
v_resetjp_4183_:
{
lean_object* v_name_4186_; lean_object* v_processType_4187_; uint8_t v_isMainThread_4188_; lean_object* v_markers_4189_; lean_object* v_stackTable_4190_; lean_object* v_frameTable_4191_; lean_object* v_resourceTable_4192_; lean_object* v_nativeSymbols_4193_; lean_object* v_stringArray_4194_; lean_object* v_funcTable_4195_; lean_object* v___x_4197_; uint8_t v_isShared_4198_; uint8_t v_isSharedCheck_4253_; 
v_name_4186_ = lean_ctor_get(v_toThread_4173_, 0);
v_processType_4187_ = lean_ctor_get(v_toThread_4173_, 1);
v_isMainThread_4188_ = lean_ctor_get_uint8(v_toThread_4173_, sizeof(void*)*10);
v_markers_4189_ = lean_ctor_get(v_toThread_4173_, 3);
v_stackTable_4190_ = lean_ctor_get(v_toThread_4173_, 4);
v_frameTable_4191_ = lean_ctor_get(v_toThread_4173_, 5);
v_resourceTable_4192_ = lean_ctor_get(v_toThread_4173_, 6);
v_nativeSymbols_4193_ = lean_ctor_get(v_toThread_4173_, 7);
v_stringArray_4194_ = lean_ctor_get(v_toThread_4173_, 8);
v_funcTable_4195_ = lean_ctor_get(v_toThread_4173_, 9);
v_isSharedCheck_4253_ = !lean_is_exclusive(v_toThread_4173_);
if (v_isSharedCheck_4253_ == 0)
{
lean_object* v_unused_4254_; 
v_unused_4254_ = lean_ctor_get(v_toThread_4173_, 2);
lean_dec(v_unused_4254_);
v___x_4197_ = v_toThread_4173_;
v_isShared_4198_ = v_isSharedCheck_4253_;
goto v_resetjp_4196_;
}
else
{
lean_inc(v_funcTable_4195_);
lean_inc(v_stringArray_4194_);
lean_inc(v_nativeSymbols_4193_);
lean_inc(v_resourceTable_4192_);
lean_inc(v_frameTable_4191_);
lean_inc(v_stackTable_4190_);
lean_inc(v_markers_4189_);
lean_inc(v_processType_4187_);
lean_inc(v_name_4186_);
lean_dec(v_toThread_4173_);
v___x_4197_ = lean_box(0);
v_isShared_4198_ = v_isSharedCheck_4253_;
goto v_resetjp_4196_;
}
v_resetjp_4196_:
{
lean_object* v_stack_4199_; lean_object* v_time_4200_; lean_object* v_weight_4201_; lean_object* v_threadCPUDelta_4202_; lean_object* v_length_4203_; lean_object* v___x_4205_; uint8_t v_isShared_4206_; uint8_t v_isSharedCheck_4251_; 
v_stack_4199_ = lean_ctor_get(v_samples_4174_, 0);
v_time_4200_ = lean_ctor_get(v_samples_4174_, 1);
v_weight_4201_ = lean_ctor_get(v_samples_4174_, 2);
v_threadCPUDelta_4202_ = lean_ctor_get(v_samples_4174_, 4);
v_length_4203_ = lean_ctor_get(v_samples_4174_, 5);
v_isSharedCheck_4251_ = !lean_is_exclusive(v_samples_4174_);
if (v_isSharedCheck_4251_ == 0)
{
lean_object* v_unused_4252_; 
v_unused_4252_ = lean_ctor_get(v_samples_4174_, 3);
lean_dec(v_unused_4252_);
v___x_4205_ = v_samples_4174_;
v_isShared_4206_ = v_isSharedCheck_4251_;
goto v_resetjp_4204_;
}
else
{
lean_inc(v_length_4203_);
lean_inc(v_threadCPUDelta_4202_);
lean_inc(v_weight_4201_);
lean_inc(v_time_4200_);
lean_inc(v_stack_4199_);
lean_dec(v_samples_4174_);
v___x_4205_ = lean_box(0);
v_isShared_4206_ = v_isSharedCheck_4251_;
goto v_resetjp_4204_;
}
v_resetjp_4204_:
{
lean_object* v___x_4207_; lean_object* v___x_4208_; lean_object* v___x_4209_; double v___x_4210_; double v___x_4211_; lean_object* v___x_4212_; lean_object* v___x_4213_; double v___x_4214_; double v___x_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; lean_object* v___x_4218_; double v___x_4219_; lean_object* v___x_4220_; lean_object* v___x_4221_; double v___x_4222_; double v___x_4223_; double v___x_4224_; lean_object* v___x_4225_; lean_object* v___x_4226_; lean_object* v___x_4227_; lean_object* v___x_4228_; lean_object* v___x_4229_; double v___x_4230_; double v___x_4231_; lean_object* v___x_4232_; lean_object* v___x_4233_; lean_object* v___x_4234_; lean_object* v___x_4235_; lean_object* v___x_4237_; 
v___x_4207_ = lean_unsigned_to_nat(0u);
lean_inc_n(v_fst_4152_, 2);
v___x_4208_ = lean_array_push(v_stack_4199_, v_fst_4152_);
v___x_4209_ = lean_array_push(v___x_4208_, v_fst_4152_);
v___x_4210_ = lean_float_once(&l_Lean_Firefox_instCoeFloatMilliseconds___lam__0___closed__0, &l_Lean_Firefox_instCoeFloatMilliseconds___lam__0___closed__0_once, _init_l_Lean_Firefox_instCoeFloatMilliseconds___lam__0___closed__0);
v___x_4211_ = lean_float_mul(v_lastTime_4182_, v___x_4210_);
v___x_4212_ = lean_box_float(v___x_4211_);
v___x_4213_ = lean_array_push(v_time_4200_, v___x_4212_);
v___x_4214_ = lean_unbox_float(v_val_4175_);
v___x_4215_ = lean_float_mul(v___x_4214_, v___x_4210_);
v___x_4216_ = lean_box_float(v___x_4215_);
v___x_4217_ = lean_array_push(v___x_4213_, v___x_4216_);
v___x_4218_ = lean_unsigned_to_nat(1u);
v___x_4219_ = l_Float_ofScientific(v___x_4207_, v___x_4167_, v___x_4218_);
v___x_4220_ = lean_box_float(v___x_4219_);
v___x_4221_ = lean_array_push(v_weight_4201_, v___x_4220_);
v___x_4222_ = lean_unbox_float(v_val_4175_);
lean_dec(v_val_4175_);
v___x_4223_ = lean_float_sub(v___x_4222_, v_lastTime_4182_);
v___x_4224_ = lean_float_mul(v___x_4223_, v___x_4210_);
v___x_4225_ = lean_box_float(v___x_4224_);
v___x_4226_ = lean_array_push(v___x_4221_, v___x_4225_);
v___x_4227_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__0___closed__0));
v___x_4228_ = lean_box_float(v___x_4219_);
v___x_4229_ = lean_array_push(v_threadCPUDelta_4202_, v___x_4228_);
v___x_4230_ = lean_float_once(&l_Lean_Firefox_instCoeFloatMicroseconds___lam__0___closed__0, &l_Lean_Firefox_instCoeFloatMicroseconds___lam__0___closed__0_once, _init_l_Lean_Firefox_instCoeFloatMicroseconds___lam__0___closed__0);
v___x_4231_ = lean_float_mul(v___x_4223_, v___x_4230_);
v___x_4232_ = lean_box_float(v___x_4231_);
v___x_4233_ = lean_array_push(v___x_4229_, v___x_4232_);
v___x_4234_ = lean_unsigned_to_nat(2u);
v___x_4235_ = lean_nat_add(v_length_4203_, v___x_4234_);
lean_dec(v_length_4203_);
if (v_isShared_4206_ == 0)
{
lean_ctor_set(v___x_4205_, 5, v___x_4235_);
lean_ctor_set(v___x_4205_, 4, v___x_4233_);
lean_ctor_set(v___x_4205_, 3, v___x_4227_);
lean_ctor_set(v___x_4205_, 2, v___x_4226_);
lean_ctor_set(v___x_4205_, 1, v___x_4217_);
lean_ctor_set(v___x_4205_, 0, v___x_4209_);
v___x_4237_ = v___x_4205_;
goto v_reusejp_4236_;
}
else
{
lean_object* v_reuseFailAlloc_4250_; 
v_reuseFailAlloc_4250_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_4250_, 0, v___x_4209_);
lean_ctor_set(v_reuseFailAlloc_4250_, 1, v___x_4217_);
lean_ctor_set(v_reuseFailAlloc_4250_, 2, v___x_4226_);
lean_ctor_set(v_reuseFailAlloc_4250_, 3, v___x_4227_);
lean_ctor_set(v_reuseFailAlloc_4250_, 4, v___x_4233_);
lean_ctor_set(v_reuseFailAlloc_4250_, 5, v___x_4235_);
v___x_4237_ = v_reuseFailAlloc_4250_;
goto v_reusejp_4236_;
}
v_reusejp_4236_:
{
lean_object* v___x_4239_; 
if (v_isShared_4198_ == 0)
{
lean_ctor_set(v___x_4197_, 2, v___x_4237_);
v___x_4239_ = v___x_4197_;
goto v_reusejp_4238_;
}
else
{
lean_object* v_reuseFailAlloc_4249_; 
v_reuseFailAlloc_4249_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_4249_, 0, v_name_4186_);
lean_ctor_set(v_reuseFailAlloc_4249_, 1, v_processType_4187_);
lean_ctor_set(v_reuseFailAlloc_4249_, 2, v___x_4237_);
lean_ctor_set(v_reuseFailAlloc_4249_, 3, v_markers_4189_);
lean_ctor_set(v_reuseFailAlloc_4249_, 4, v_stackTable_4190_);
lean_ctor_set(v_reuseFailAlloc_4249_, 5, v_frameTable_4191_);
lean_ctor_set(v_reuseFailAlloc_4249_, 6, v_resourceTable_4192_);
lean_ctor_set(v_reuseFailAlloc_4249_, 7, v_nativeSymbols_4193_);
lean_ctor_set(v_reuseFailAlloc_4249_, 8, v_stringArray_4194_);
lean_ctor_set(v_reuseFailAlloc_4249_, 9, v_funcTable_4195_);
lean_ctor_set_uint8(v_reuseFailAlloc_4249_, sizeof(void*)*10, v_isMainThread_4188_);
v___x_4239_ = v_reuseFailAlloc_4249_;
goto v_reusejp_4238_;
}
v_reusejp_4238_:
{
lean_object* v___x_4241_; 
if (v_isShared_4185_ == 0)
{
lean_ctor_set(v___x_4184_, 0, v___x_4239_);
v___x_4241_ = v___x_4184_;
goto v_reusejp_4240_;
}
else
{
lean_object* v_reuseFailAlloc_4248_; 
v_reuseFailAlloc_4248_ = lean_alloc_ctor(0, 4, 8);
lean_ctor_set(v_reuseFailAlloc_4248_, 0, v___x_4239_);
lean_ctor_set(v_reuseFailAlloc_4248_, 1, v_stringMap_4179_);
lean_ctor_set(v_reuseFailAlloc_4248_, 2, v_funcMap_4180_);
lean_ctor_set(v_reuseFailAlloc_4248_, 3, v_stackMap_4181_);
lean_ctor_set_float(v_reuseFailAlloc_4248_, sizeof(void*)*4, v_lastTime_4182_);
v___x_4241_ = v_reuseFailAlloc_4248_;
goto v_reusejp_4240_;
}
v_reusejp_4240_:
{
lean_object* v___x_4243_; 
lean_inc(v_fst_4152_);
if (v_isShared_4178_ == 0)
{
lean_ctor_set(v___x_4177_, 0, v_fst_4152_);
v___x_4243_ = v___x_4177_;
goto v_reusejp_4242_;
}
else
{
lean_object* v_reuseFailAlloc_4247_; 
v_reuseFailAlloc_4247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4247_, 0, v_fst_4152_);
v___x_4243_ = v_reuseFailAlloc_4247_;
goto v_reusejp_4242_;
}
v_reusejp_4242_:
{
lean_object* v___x_4244_; 
lean_inc(v_a_4171_);
lean_inc(v_ctx_x3f_4154_);
v___x_4244_ = l___private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go(v_pp_4153_, v___x_4243_, v_ctx_x3f_4154_, v_a_4171_, v___x_4241_);
if (lean_obj_tag(v___x_4244_) == 0)
{
lean_object* v_a_4245_; lean_object* v_snd_4246_; 
v_a_4245_ = lean_ctor_get(v___x_4244_, 0);
lean_inc(v_a_4245_);
lean_dec_ref_known(v___x_4244_, 1);
v_snd_4246_ = lean_ctor_get(v_a_4245_, 1);
lean_inc(v_snd_4246_);
lean_dec(v_a_4245_);
v_a_4162_ = v___x_4170_;
v_snd_4163_ = v_snd_4246_;
goto v___jp_4161_;
}
else
{
lean_dec(v_ctx_x3f_4154_);
lean_dec(v_fst_4152_);
return v___x_4244_;
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
lean_dec(v___x_4172_);
v_a_4162_ = v___x_4170_;
v_snd_4163_ = v___y_4159_;
goto v___jp_4161_;
}
}
v___jp_4161_:
{
size_t v___x_4164_; size_t v___x_4165_; 
v___x_4164_ = ((size_t)1ULL);
v___x_4165_ = lean_usize_add(v_i_4157_, v___x_4164_);
v_i_4157_ = v___x_4165_;
v_b_4158_ = v_a_4162_;
v___y_4159_ = v_snd_4163_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__0___boxed(lean_object* v_fst_4258_, lean_object* v_pp_4259_, lean_object* v_ctx_x3f_4260_, lean_object* v_as_4261_, lean_object* v_sz_4262_, lean_object* v_i_4263_, lean_object* v_b_4264_, lean_object* v___y_4265_, lean_object* v___y_4266_){
_start:
{
uint8_t v_pp_boxed_4267_; size_t v_sz_boxed_4268_; size_t v_i_boxed_4269_; lean_object* v_res_4270_; 
v_pp_boxed_4267_ = lean_unbox(v_pp_4259_);
v_sz_boxed_4268_ = lean_unbox_usize(v_sz_4262_);
lean_dec(v_sz_4262_);
v_i_boxed_4269_ = lean_unbox_usize(v_i_4263_);
lean_dec(v_i_4263_);
v_res_4270_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__0(v_fst_4258_, v_pp_boxed_4267_, v_ctx_x3f_4260_, v_as_4261_, v_sz_boxed_4268_, v_i_boxed_4269_, v_b_4264_, v___y_4265_);
lean_dec_ref(v_as_4261_);
return v_res_4270_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go___boxed(lean_object* v_pp_4271_, lean_object* v_parentStackIdx_x3f_4272_, lean_object* v_ctx_x3f_4273_, lean_object* v_a_4274_, lean_object* v_a_4275_, lean_object* v_a_4276_){
_start:
{
uint8_t v_pp_boxed_4277_; lean_object* v_res_4278_; 
v_pp_boxed_4277_ = lean_unbox(v_pp_4271_);
v_res_4278_ = l___private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go(v_pp_boxed_4277_, v_parentStackIdx_x3f_4272_, v_ctx_x3f_4273_, v_a_4274_, v_a_4275_);
return v_res_4278_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__1(lean_object* v_00_u03b2_4279_, lean_object* v_m_4280_, lean_object* v_a_4281_){
_start:
{
lean_object* v___x_4282_; 
v___x_4282_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__1___redArg(v_m_4280_, v_a_4281_);
return v___x_4282_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__1___boxed(lean_object* v_00_u03b2_4283_, lean_object* v_m_4284_, lean_object* v_a_4285_){
_start:
{
lean_object* v_res_4286_; 
v_res_4286_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__1(v_00_u03b2_4283_, v_m_4284_, v_a_4285_);
lean_dec_ref(v_a_4285_);
lean_dec_ref(v_m_4284_);
return v_res_4286_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__2(lean_object* v_00_u03b2_4287_, lean_object* v_m_4288_, lean_object* v_a_4289_, lean_object* v_b_4290_){
_start:
{
lean_object* v___x_4291_; 
v___x_4291_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__2___redArg(v_m_4288_, v_a_4289_, v_b_4290_);
return v___x_4291_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__3(lean_object* v_00_u03b2_4292_, lean_object* v_m_4293_, lean_object* v_a_4294_){
_start:
{
lean_object* v___x_4295_; 
v___x_4295_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__3___redArg(v_m_4293_, v_a_4294_);
return v___x_4295_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__3___boxed(lean_object* v_00_u03b2_4296_, lean_object* v_m_4297_, lean_object* v_a_4298_){
_start:
{
lean_object* v_res_4299_; 
v_res_4299_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__3(v_00_u03b2_4296_, v_m_4297_, v_a_4298_);
lean_dec(v_a_4298_);
lean_dec_ref(v_m_4297_);
return v_res_4299_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__4(lean_object* v_00_u03b2_4300_, lean_object* v_m_4301_, lean_object* v_a_4302_, lean_object* v_b_4303_){
_start:
{
lean_object* v___x_4304_; 
v___x_4304_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__4___redArg(v_m_4301_, v_a_4302_, v_b_4303_);
return v___x_4304_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__6(lean_object* v_00_u03b2_4305_, lean_object* v_m_4306_, lean_object* v_a_4307_){
_start:
{
lean_object* v___x_4308_; 
v___x_4308_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__6___redArg(v_m_4306_, v_a_4307_);
return v___x_4308_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__6___boxed(lean_object* v_00_u03b2_4309_, lean_object* v_m_4310_, lean_object* v_a_4311_){
_start:
{
lean_object* v_res_4312_; 
v_res_4312_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__6(v_00_u03b2_4309_, v_m_4310_, v_a_4311_);
lean_dec_ref(v_a_4311_);
lean_dec_ref(v_m_4310_);
return v_res_4312_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__7(lean_object* v_00_u03b2_4313_, lean_object* v_m_4314_, lean_object* v_a_4315_, lean_object* v_b_4316_){
_start:
{
lean_object* v___x_4317_; 
v___x_4317_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__7___redArg(v_m_4314_, v_a_4315_, v_b_4316_);
return v___x_4317_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__1_spec__1(lean_object* v_00_u03b2_4318_, lean_object* v_a_4319_, lean_object* v_x_4320_){
_start:
{
lean_object* v___x_4321_; 
v___x_4321_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__1_spec__1___redArg(v_a_4319_, v_x_4320_);
return v___x_4321_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__1_spec__1___boxed(lean_object* v_00_u03b2_4322_, lean_object* v_a_4323_, lean_object* v_x_4324_){
_start:
{
lean_object* v_res_4325_; 
v_res_4325_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__1_spec__1(v_00_u03b2_4322_, v_a_4323_, v_x_4324_);
lean_dec(v_x_4324_);
lean_dec_ref(v_a_4323_);
return v_res_4325_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__2_spec__3(lean_object* v_00_u03b2_4326_, lean_object* v_a_4327_, lean_object* v_x_4328_){
_start:
{
uint8_t v___x_4329_; 
v___x_4329_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__2_spec__3___redArg(v_a_4327_, v_x_4328_);
return v___x_4329_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__2_spec__3___boxed(lean_object* v_00_u03b2_4330_, lean_object* v_a_4331_, lean_object* v_x_4332_){
_start:
{
uint8_t v_res_4333_; lean_object* v_r_4334_; 
v_res_4333_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__2_spec__3(v_00_u03b2_4330_, v_a_4331_, v_x_4332_);
lean_dec(v_x_4332_);
lean_dec_ref(v_a_4331_);
v_r_4334_ = lean_box(v_res_4333_);
return v_r_4334_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__2_spec__4(lean_object* v_00_u03b2_4335_, lean_object* v_data_4336_){
_start:
{
lean_object* v___x_4337_; 
v___x_4337_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__2_spec__4___redArg(v_data_4336_);
return v___x_4337_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__2_spec__5(lean_object* v_00_u03b2_4338_, lean_object* v_a_4339_, lean_object* v_b_4340_, lean_object* v_x_4341_){
_start:
{
lean_object* v___x_4342_; 
v___x_4342_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__2_spec__5___redArg(v_a_4339_, v_b_4340_, v_x_4341_);
return v___x_4342_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__3_spec__7(lean_object* v_00_u03b2_4343_, lean_object* v_a_4344_, lean_object* v_x_4345_){
_start:
{
lean_object* v___x_4346_; 
v___x_4346_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__3_spec__7___redArg(v_a_4344_, v_x_4345_);
return v___x_4346_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__3_spec__7___boxed(lean_object* v_00_u03b2_4347_, lean_object* v_a_4348_, lean_object* v_x_4349_){
_start:
{
lean_object* v_res_4350_; 
v_res_4350_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__3_spec__7(v_00_u03b2_4347_, v_a_4348_, v_x_4349_);
lean_dec(v_x_4349_);
lean_dec(v_a_4348_);
return v_res_4350_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__4_spec__9(lean_object* v_00_u03b2_4351_, lean_object* v_a_4352_, lean_object* v_x_4353_){
_start:
{
uint8_t v___x_4354_; 
v___x_4354_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__4_spec__9___redArg(v_a_4352_, v_x_4353_);
return v___x_4354_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__4_spec__9___boxed(lean_object* v_00_u03b2_4355_, lean_object* v_a_4356_, lean_object* v_x_4357_){
_start:
{
uint8_t v_res_4358_; lean_object* v_r_4359_; 
v_res_4358_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__4_spec__9(v_00_u03b2_4355_, v_a_4356_, v_x_4357_);
lean_dec(v_x_4357_);
lean_dec(v_a_4356_);
v_r_4359_ = lean_box(v_res_4358_);
return v_r_4359_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__4_spec__10(lean_object* v_00_u03b2_4360_, lean_object* v_data_4361_){
_start:
{
lean_object* v___x_4362_; 
v___x_4362_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__4_spec__10___redArg(v_data_4361_);
return v___x_4362_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__4_spec__11(lean_object* v_00_u03b2_4363_, lean_object* v_a_4364_, lean_object* v_b_4365_, lean_object* v_x_4366_){
_start:
{
lean_object* v___x_4367_; 
v___x_4367_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__4_spec__11___redArg(v_a_4364_, v_b_4365_, v_x_4366_);
return v___x_4367_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__6_spec__14(lean_object* v_00_u03b2_4368_, lean_object* v_a_4369_, lean_object* v_x_4370_){
_start:
{
lean_object* v___x_4371_; 
v___x_4371_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__6_spec__14___redArg(v_a_4369_, v_x_4370_);
return v___x_4371_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__6_spec__14___boxed(lean_object* v_00_u03b2_4372_, lean_object* v_a_4373_, lean_object* v_x_4374_){
_start:
{
lean_object* v_res_4375_; 
v_res_4375_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__6_spec__14(v_00_u03b2_4372_, v_a_4373_, v_x_4374_);
lean_dec(v_x_4374_);
lean_dec_ref(v_a_4373_);
return v_res_4375_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__7_spec__16(lean_object* v_00_u03b2_4376_, lean_object* v_a_4377_, lean_object* v_x_4378_){
_start:
{
uint8_t v___x_4379_; 
v___x_4379_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__7_spec__16___redArg(v_a_4377_, v_x_4378_);
return v___x_4379_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__7_spec__16___boxed(lean_object* v_00_u03b2_4380_, lean_object* v_a_4381_, lean_object* v_x_4382_){
_start:
{
uint8_t v_res_4383_; lean_object* v_r_4384_; 
v_res_4383_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__7_spec__16(v_00_u03b2_4380_, v_a_4381_, v_x_4382_);
lean_dec(v_x_4382_);
lean_dec_ref(v_a_4381_);
v_r_4384_ = lean_box(v_res_4383_);
return v_r_4384_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__7_spec__17(lean_object* v_00_u03b2_4385_, lean_object* v_data_4386_){
_start:
{
lean_object* v___x_4387_; 
v___x_4387_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__7_spec__17___redArg(v_data_4386_);
return v___x_4387_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__7_spec__18(lean_object* v_00_u03b2_4388_, lean_object* v_a_4389_, lean_object* v_b_4390_, lean_object* v_x_4391_){
_start:
{
lean_object* v___x_4392_; 
v___x_4392_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__7_spec__18___redArg(v_a_4389_, v_b_4390_, v_x_4391_);
return v___x_4392_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__2_spec__4_spec__6(lean_object* v_00_u03b2_4393_, lean_object* v_i_4394_, lean_object* v_source_4395_, lean_object* v_target_4396_){
_start:
{
lean_object* v___x_4397_; 
v___x_4397_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__2_spec__4_spec__6___redArg(v_i_4394_, v_source_4395_, v_target_4396_);
return v___x_4397_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__4_spec__10_spec__13(lean_object* v_00_u03b2_4398_, lean_object* v_i_4399_, lean_object* v_source_4400_, lean_object* v_target_4401_){
_start:
{
lean_object* v___x_4402_; 
v___x_4402_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__4_spec__10_spec__13___redArg(v_i_4399_, v_source_4400_, v_target_4401_);
return v___x_4402_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__7_spec__17_spec__21(lean_object* v_00_u03b2_4403_, lean_object* v_i_4404_, lean_object* v_source_4405_, lean_object* v_target_4406_){
_start:
{
lean_object* v___x_4407_; 
v___x_4407_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__7_spec__17_spec__21___redArg(v_i_4404_, v_source_4405_, v_target_4406_);
return v___x_4407_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__2_spec__4_spec__6_spec__12(lean_object* v_00_u03b2_4408_, lean_object* v_x_4409_, lean_object* v_x_4410_){
_start:
{
lean_object* v___x_4411_; 
v___x_4411_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__2_spec__4_spec__6_spec__12___redArg(v_x_4409_, v_x_4410_);
return v___x_4411_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__4_spec__10_spec__13_spec__18(lean_object* v_00_u03b2_4412_, lean_object* v_x_4413_, lean_object* v_x_4414_){
_start:
{
lean_object* v___x_4415_; 
v___x_4415_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__4_spec__10_spec__13_spec__18___redArg(v_x_4413_, v_x_4414_);
return v___x_4415_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__7_spec__17_spec__21_spec__24(lean_object* v_00_u03b2_4416_, lean_object* v_x_4417_, lean_object* v_x_4418_){
_start:
{
lean_object* v___x_4419_; 
v___x_4419_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__7_spec__17_spec__21_spec__24___redArg(v_x_4417_, v_x_4418_);
return v___x_4419_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Profiler_0__Lean_Firefox_addTrace(uint8_t v_pp_4420_, lean_object* v_thread_4421_, lean_object* v_trace_4422_){
_start:
{
lean_object* v___x_4424_; lean_object* v___x_4425_; 
v___x_4424_ = lean_box(0);
v___x_4425_ = l___private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go(v_pp_4420_, v___x_4424_, v___x_4424_, v_trace_4422_, v_thread_4421_);
if (lean_obj_tag(v___x_4425_) == 0)
{
lean_object* v_a_4426_; lean_object* v___x_4428_; uint8_t v_isShared_4429_; uint8_t v_isSharedCheck_4434_; 
v_a_4426_ = lean_ctor_get(v___x_4425_, 0);
v_isSharedCheck_4434_ = !lean_is_exclusive(v___x_4425_);
if (v_isSharedCheck_4434_ == 0)
{
v___x_4428_ = v___x_4425_;
v_isShared_4429_ = v_isSharedCheck_4434_;
goto v_resetjp_4427_;
}
else
{
lean_inc(v_a_4426_);
lean_dec(v___x_4425_);
v___x_4428_ = lean_box(0);
v_isShared_4429_ = v_isSharedCheck_4434_;
goto v_resetjp_4427_;
}
v_resetjp_4427_:
{
lean_object* v_snd_4430_; lean_object* v___x_4432_; 
v_snd_4430_ = lean_ctor_get(v_a_4426_, 1);
lean_inc(v_snd_4430_);
lean_dec(v_a_4426_);
if (v_isShared_4429_ == 0)
{
lean_ctor_set(v___x_4428_, 0, v_snd_4430_);
v___x_4432_ = v___x_4428_;
goto v_reusejp_4431_;
}
else
{
lean_object* v_reuseFailAlloc_4433_; 
v_reuseFailAlloc_4433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4433_, 0, v_snd_4430_);
v___x_4432_ = v_reuseFailAlloc_4433_;
goto v_reusejp_4431_;
}
v_reusejp_4431_:
{
return v___x_4432_;
}
}
}
else
{
lean_object* v_a_4435_; lean_object* v___x_4437_; uint8_t v_isShared_4438_; uint8_t v_isSharedCheck_4442_; 
v_a_4435_ = lean_ctor_get(v___x_4425_, 0);
v_isSharedCheck_4442_ = !lean_is_exclusive(v___x_4425_);
if (v_isSharedCheck_4442_ == 0)
{
v___x_4437_ = v___x_4425_;
v_isShared_4438_ = v_isSharedCheck_4442_;
goto v_resetjp_4436_;
}
else
{
lean_inc(v_a_4435_);
lean_dec(v___x_4425_);
v___x_4437_ = lean_box(0);
v_isShared_4438_ = v_isSharedCheck_4442_;
goto v_resetjp_4436_;
}
v_resetjp_4436_:
{
lean_object* v___x_4440_; 
if (v_isShared_4438_ == 0)
{
v___x_4440_ = v___x_4437_;
goto v_reusejp_4439_;
}
else
{
lean_object* v_reuseFailAlloc_4441_; 
v_reuseFailAlloc_4441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4441_, 0, v_a_4435_);
v___x_4440_ = v_reuseFailAlloc_4441_;
goto v_reusejp_4439_;
}
v_reusejp_4439_:
{
return v___x_4440_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Profiler_0__Lean_Firefox_addTrace___boxed(lean_object* v_pp_4443_, lean_object* v_thread_4444_, lean_object* v_trace_4445_, lean_object* v_a_4446_){
_start:
{
uint8_t v_pp_boxed_4447_; lean_object* v_res_4448_; 
v_pp_boxed_4447_ = lean_unbox(v_pp_4443_);
v_res_4448_ = l___private_Lean_Util_Profiler_0__Lean_Firefox_addTrace(v_pp_boxed_4447_, v_thread_4444_, v_trace_4445_);
return v_res_4448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Firefox_Thread_new(lean_object* v_name_4468_){
_start:
{
lean_object* v___x_4469_; uint8_t v___x_4470_; lean_object* v___x_4471_; lean_object* v___x_4472_; lean_object* v___x_4473_; lean_object* v___x_4474_; lean_object* v___x_4475_; lean_object* v___x_4476_; lean_object* v___x_4477_; lean_object* v___x_4478_; 
v___x_4469_ = ((lean_object*)(l_Lean_Firefox_Thread_new___closed__0));
v___x_4470_ = 1;
v___x_4471_ = ((lean_object*)(l_Lean_Firefox_Thread_new___closed__1));
v___x_4472_ = ((lean_object*)(l_Lean_Firefox_Thread_new___closed__2));
v___x_4473_ = ((lean_object*)(l_Lean_Firefox_Thread_new___closed__3));
v___x_4474_ = ((lean_object*)(l_Lean_Firefox_Thread_new___closed__4));
v___x_4475_ = ((lean_object*)(l_Lean_Firefox_instInhabitedFrameTable_default));
v___x_4476_ = ((lean_object*)(l_Lean_Firefox_Thread_new___closed__5));
v___x_4477_ = ((lean_object*)(l_Lean_Firefox_Thread_new___closed__6));
v___x_4478_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_4478_, 0, v_name_4468_);
lean_ctor_set(v___x_4478_, 1, v___x_4469_);
lean_ctor_set(v___x_4478_, 2, v___x_4472_);
lean_ctor_set(v___x_4478_, 3, v___x_4473_);
lean_ctor_set(v___x_4478_, 4, v___x_4474_);
lean_ctor_set(v___x_4478_, 5, v___x_4475_);
lean_ctor_set(v___x_4478_, 6, v___x_4476_);
lean_ctor_set(v___x_4478_, 7, v___x_4476_);
lean_ctor_set(v___x_4478_, 8, v___x_4471_);
lean_ctor_set(v___x_4478_, 9, v___x_4477_);
lean_ctor_set_uint8(v___x_4478_, sizeof(void*)*10, v___x_4470_);
return v___x_4478_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Firefox_Profile_export_spec__2(lean_object* v_opts_4479_, lean_object* v_opt_4480_){
_start:
{
lean_object* v_name_4481_; lean_object* v_defValue_4482_; lean_object* v_map_4483_; lean_object* v___x_4484_; 
v_name_4481_ = lean_ctor_get(v_opt_4480_, 0);
v_defValue_4482_ = lean_ctor_get(v_opt_4480_, 1);
v_map_4483_ = lean_ctor_get(v_opts_4479_, 0);
v___x_4484_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4483_, v_name_4481_);
if (lean_obj_tag(v___x_4484_) == 0)
{
uint8_t v___x_4485_; 
v___x_4485_ = lean_unbox(v_defValue_4482_);
return v___x_4485_;
}
else
{
lean_object* v_val_4486_; 
v_val_4486_ = lean_ctor_get(v___x_4484_, 0);
lean_inc(v_val_4486_);
lean_dec_ref_known(v___x_4484_, 1);
if (lean_obj_tag(v_val_4486_) == 1)
{
uint8_t v_v_4487_; 
v_v_4487_ = lean_ctor_get_uint8(v_val_4486_, 0);
lean_dec_ref_known(v_val_4486_, 0);
return v_v_4487_;
}
else
{
uint8_t v___x_4488_; 
lean_dec(v_val_4486_);
v___x_4488_ = lean_unbox(v_defValue_4482_);
return v___x_4488_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Firefox_Profile_export_spec__2___boxed(lean_object* v_opts_4489_, lean_object* v_opt_4490_){
_start:
{
uint8_t v_res_4491_; lean_object* v_r_4492_; 
v_res_4491_ = l_Lean_Option_get___at___00Lean_Firefox_Profile_export_spec__2(v_opts_4489_, v_opt_4490_);
lean_dec_ref(v_opt_4490_);
lean_dec_ref(v_opts_4489_);
v_r_4492_ = lean_box(v_res_4491_);
return v_r_4492_;
}
}
LEAN_EXPORT uint64_t l_Lean_Firefox_Profile_export___lam__0(lean_object* v_x_4493_){
_start:
{
uint64_t v_tid_4494_; 
v_tid_4494_ = lean_ctor_get_uint64(v_x_4493_, sizeof(void*)*1);
return v_tid_4494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Firefox_Profile_export___lam__0___boxed(lean_object* v_x_4495_){
_start:
{
uint64_t v_res_4496_; lean_object* v_r_4497_; 
v_res_4496_ = l_Lean_Firefox_Profile_export___lam__0(v_x_4495_);
lean_dec_ref(v_x_4495_);
v_r_4497_ = lean_box_uint64(v_res_4496_);
return v_r_4497_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__1(size_t v_sz_4498_, size_t v_i_4499_, lean_object* v_bs_4500_){
_start:
{
uint8_t v___x_4501_; 
v___x_4501_ = lean_usize_dec_lt(v_i_4499_, v_sz_4498_);
if (v___x_4501_ == 0)
{
return v_bs_4500_;
}
else
{
lean_object* v_v_4502_; lean_object* v_traces_4503_; lean_object* v___x_4504_; lean_object* v_bs_x27_4505_; lean_object* v___x_4506_; size_t v___x_4507_; size_t v___x_4508_; lean_object* v___x_4509_; 
v_v_4502_ = lean_array_uget_borrowed(v_bs_4500_, v_i_4499_);
v_traces_4503_ = lean_ctor_get(v_v_4502_, 0);
lean_inc_ref(v_traces_4503_);
v___x_4504_ = lean_unsigned_to_nat(0u);
v_bs_x27_4505_ = lean_array_uset(v_bs_4500_, v_i_4499_, v___x_4504_);
v___x_4506_ = l_Lean_PersistentArray_toArray___redArg(v_traces_4503_);
lean_dec_ref(v_traces_4503_);
v___x_4507_ = ((size_t)1ULL);
v___x_4508_ = lean_usize_add(v_i_4499_, v___x_4507_);
v___x_4509_ = lean_array_uset(v_bs_x27_4505_, v_i_4499_, v___x_4506_);
v_i_4499_ = v___x_4508_;
v_bs_4500_ = v___x_4509_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__1___boxed(lean_object* v_sz_4511_, lean_object* v_i_4512_, lean_object* v_bs_4513_){
_start:
{
size_t v_sz_boxed_4514_; size_t v_i_boxed_4515_; lean_object* v_res_4516_; 
v_sz_boxed_4514_ = lean_unbox_usize(v_sz_4511_);
lean_dec(v_sz_4511_);
v_i_boxed_4515_ = lean_unbox_usize(v_i_4512_);
lean_dec(v_i_4512_);
v_res_4516_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__1(v_sz_boxed_4514_, v_i_boxed_4515_, v_bs_4513_);
return v_res_4516_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__4(size_t v_sz_4517_, size_t v_i_4518_, lean_object* v_bs_4519_){
_start:
{
uint8_t v___x_4520_; 
v___x_4520_ = lean_usize_dec_lt(v_i_4518_, v_sz_4517_);
if (v___x_4520_ == 0)
{
return v_bs_4519_;
}
else
{
lean_object* v_v_4521_; lean_object* v_msg_4522_; lean_object* v___x_4523_; lean_object* v_bs_x27_4524_; size_t v___x_4525_; size_t v___x_4526_; lean_object* v___x_4527_; 
v_v_4521_ = lean_array_uget_borrowed(v_bs_4519_, v_i_4518_);
v_msg_4522_ = lean_ctor_get(v_v_4521_, 1);
lean_inc_ref(v_msg_4522_);
v___x_4523_ = lean_unsigned_to_nat(0u);
v_bs_x27_4524_ = lean_array_uset(v_bs_4519_, v_i_4518_, v___x_4523_);
v___x_4525_ = ((size_t)1ULL);
v___x_4526_ = lean_usize_add(v_i_4518_, v___x_4525_);
v___x_4527_ = lean_array_uset(v_bs_x27_4524_, v_i_4518_, v_msg_4522_);
v_i_4518_ = v___x_4526_;
v_bs_4519_ = v___x_4527_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__4___boxed(lean_object* v_sz_4529_, lean_object* v_i_4530_, lean_object* v_bs_4531_){
_start:
{
size_t v_sz_boxed_4532_; size_t v_i_boxed_4533_; lean_object* v_res_4534_; 
v_sz_boxed_4532_ = lean_unbox_usize(v_sz_4529_);
lean_dec(v_sz_4529_);
v_i_boxed_4533_ = lean_unbox_usize(v_i_4530_);
lean_dec(v_i_4530_);
v_res_4534_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__4(v_sz_boxed_4532_, v_i_boxed_4533_, v_bs_4531_);
return v_res_4534_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Firefox_Profile_export_spec__5(lean_object* v_as_4535_, size_t v_i_4536_, size_t v_stop_4537_, lean_object* v_b_4538_){
_start:
{
uint8_t v___x_4539_; 
v___x_4539_ = lean_usize_dec_eq(v_i_4536_, v_stop_4537_);
if (v___x_4539_ == 0)
{
lean_object* v___x_4540_; lean_object* v___x_4541_; size_t v___x_4542_; size_t v___x_4543_; 
v___x_4540_ = lean_array_uget_borrowed(v_as_4535_, v_i_4536_);
v___x_4541_ = l_Array_append___redArg(v_b_4538_, v___x_4540_);
v___x_4542_ = ((size_t)1ULL);
v___x_4543_ = lean_usize_add(v_i_4536_, v___x_4542_);
v_i_4536_ = v___x_4543_;
v_b_4538_ = v___x_4541_;
goto _start;
}
else
{
return v_b_4538_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Firefox_Profile_export_spec__5___boxed(lean_object* v_as_4545_, lean_object* v_i_4546_, lean_object* v_stop_4547_, lean_object* v_b_4548_){
_start:
{
size_t v_i_boxed_4549_; size_t v_stop_boxed_4550_; lean_object* v_res_4551_; 
v_i_boxed_4549_ = lean_unbox_usize(v_i_4546_);
lean_dec(v_i_4546_);
v_stop_boxed_4550_ = lean_unbox_usize(v_stop_4547_);
lean_dec(v_stop_4547_);
v_res_4551_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Firefox_Profile_export_spec__5(v_as_4545_, v_i_boxed_4549_, v_stop_boxed_4550_, v_b_4548_);
lean_dec_ref(v_as_4545_);
return v_res_4551_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__6___redArg___lam__1(lean_object* v___f_4552_, lean_object* v_tr1_4553_, lean_object* v_tr2_4554_){
_start:
{
lean_object* v___x_4555_; lean_object* v___x_4556_; double v___x_4557_; double v___x_4558_; uint8_t v___x_4559_; 
lean_inc_ref(v___f_4552_);
v___x_4555_ = lean_apply_1(v___f_4552_, v_tr1_4553_);
v___x_4556_ = lean_apply_1(v___f_4552_, v_tr2_4554_);
v___x_4557_ = lean_unbox_float(v___x_4555_);
lean_dec_ref(v___x_4555_);
v___x_4558_ = lean_unbox_float(v___x_4556_);
lean_dec_ref(v___x_4556_);
v___x_4559_ = lean_float_decLt(v___x_4557_, v___x_4558_);
return v___x_4559_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__6___redArg___lam__1___boxed(lean_object* v___f_4560_, lean_object* v_tr1_4561_, lean_object* v_tr2_4562_){
_start:
{
uint8_t v_res_4563_; lean_object* v_r_4564_; 
v_res_4563_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__6___redArg___lam__1(v___f_4560_, v_tr1_4561_, v_tr2_4562_);
v_r_4564_ = lean_box(v_res_4563_);
return v_r_4564_;
}
}
LEAN_EXPORT double l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__6___redArg___lam__0(lean_object* v___x_4565_, double v___x_4566_, lean_object* v_tr_4567_){
_start:
{
lean_object* v___x_4568_; uint8_t v___x_4569_; 
v___x_4568_ = lean_array_get_size(v_tr_4567_);
v___x_4569_ = lean_nat_dec_lt(v___x_4565_, v___x_4568_);
if (v___x_4569_ == 0)
{
return v___x_4566_;
}
else
{
lean_object* v___x_4570_; lean_object* v_msg_4571_; lean_object* v___x_4572_; 
v___x_4570_ = lean_array_fget_borrowed(v_tr_4567_, v___x_4565_);
v_msg_4571_ = lean_ctor_get(v___x_4570_, 1);
v___x_4572_ = l___private_Lean_Util_Profiler_0__Lean_Firefox_getFirstStart_x3f(v_msg_4571_);
if (lean_obj_tag(v___x_4572_) == 0)
{
return v___x_4566_;
}
else
{
lean_object* v_val_4573_; double v___x_4574_; 
v_val_4573_ = lean_ctor_get(v___x_4572_, 0);
lean_inc(v_val_4573_);
lean_dec_ref_known(v___x_4572_, 1);
v___x_4574_ = lean_unbox_float(v_val_4573_);
lean_dec(v_val_4573_);
return v___x_4574_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__6___redArg___lam__0___boxed(lean_object* v___x_4575_, lean_object* v___x_4576_, lean_object* v_tr_4577_){
_start:
{
double v___x_4339__boxed_4578_; double v_res_4579_; lean_object* v_r_4580_; 
v___x_4339__boxed_4578_ = lean_unbox_float(v___x_4576_);
lean_dec_ref(v___x_4576_);
v_res_4579_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__6___redArg___lam__0(v___x_4575_, v___x_4339__boxed_4578_, v_tr_4577_);
lean_dec_ref(v_tr_4577_);
lean_dec(v___x_4575_);
v_r_4580_ = lean_box_float(v_res_4579_);
return v_r_4580_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__6_spec__8___redArg(lean_object* v_hi_4581_, lean_object* v_pivot_4582_, lean_object* v_as_4583_, lean_object* v_i_4584_, lean_object* v_k_4585_){
_start:
{
uint8_t v___x_4586_; 
v___x_4586_ = lean_nat_dec_lt(v_k_4585_, v_hi_4581_);
if (v___x_4586_ == 0)
{
lean_object* v___x_4587_; lean_object* v___x_4588_; 
lean_dec(v_k_4585_);
v___x_4587_ = lean_array_fswap(v_as_4583_, v_i_4584_, v_hi_4581_);
v___x_4588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4588_, 0, v_i_4584_);
lean_ctor_set(v___x_4588_, 1, v___x_4587_);
return v___x_4588_;
}
else
{
lean_object* v___x_4589_; double v___x_4590_; lean_object* v___x_4591_; double v___x_4592_; double v___x_4593_; uint8_t v___x_4594_; 
v___x_4589_ = lean_unsigned_to_nat(0u);
v___x_4590_ = lean_float_once(&l___private_Lean_Util_Profiler_0__Lean_Firefox_getFirstStart_x3f___closed__0, &l___private_Lean_Util_Profiler_0__Lean_Firefox_getFirstStart_x3f___closed__0_once, _init_l___private_Lean_Util_Profiler_0__Lean_Firefox_getFirstStart_x3f___closed__0);
v___x_4591_ = lean_array_fget_borrowed(v_as_4583_, v_k_4585_);
v___x_4592_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__6___redArg___lam__0(v___x_4589_, v___x_4590_, v___x_4591_);
v___x_4593_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__6___redArg___lam__0(v___x_4589_, v___x_4590_, v_pivot_4582_);
v___x_4594_ = lean_float_decLt(v___x_4592_, v___x_4593_);
if (v___x_4594_ == 0)
{
lean_object* v___x_4595_; lean_object* v___x_4596_; 
v___x_4595_ = lean_unsigned_to_nat(1u);
v___x_4596_ = lean_nat_add(v_k_4585_, v___x_4595_);
lean_dec(v_k_4585_);
v_k_4585_ = v___x_4596_;
goto _start;
}
else
{
lean_object* v___x_4598_; lean_object* v___x_4599_; lean_object* v___x_4600_; lean_object* v___x_4601_; 
v___x_4598_ = lean_array_fswap(v_as_4583_, v_i_4584_, v_k_4585_);
v___x_4599_ = lean_unsigned_to_nat(1u);
v___x_4600_ = lean_nat_add(v_i_4584_, v___x_4599_);
lean_dec(v_i_4584_);
v___x_4601_ = lean_nat_add(v_k_4585_, v___x_4599_);
lean_dec(v_k_4585_);
v_as_4583_ = v___x_4598_;
v_i_4584_ = v___x_4600_;
v_k_4585_ = v___x_4601_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__6_spec__8___redArg___boxed(lean_object* v_hi_4603_, lean_object* v_pivot_4604_, lean_object* v_as_4605_, lean_object* v_i_4606_, lean_object* v_k_4607_){
_start:
{
lean_object* v_res_4608_; 
v_res_4608_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__6_spec__8___redArg(v_hi_4603_, v_pivot_4604_, v_as_4605_, v_i_4606_, v_k_4607_);
lean_dec_ref(v_pivot_4604_);
lean_dec(v_hi_4603_);
return v_res_4608_;
}
}
static lean_object* _init_l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__6___redArg___closed__0___boxed__const__1(void){
_start:
{
double v___x_4609_; lean_object* v___x_4610_; 
v___x_4609_ = lean_float_once(&l___private_Lean_Util_Profiler_0__Lean_Firefox_getFirstStart_x3f___closed__0, &l___private_Lean_Util_Profiler_0__Lean_Firefox_getFirstStart_x3f___closed__0_once, _init_l___private_Lean_Util_Profiler_0__Lean_Firefox_getFirstStart_x3f___closed__0);
v___x_4610_ = lean_box_float(v___x_4609_);
return v___x_4610_;
}
}
static lean_object* _init_l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_4611_; lean_object* v___x_4612_; lean_object* v___f_4613_; 
v___x_4611_ = lean_unsigned_to_nat(0u);
v___x_4612_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__6___redArg___closed__0___boxed__const__1;
v___f_4613_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__6___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_4613_, 0, v___x_4611_);
lean_closure_set(v___f_4613_, 1, v___x_4612_);
return v___f_4613_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__6___redArg(lean_object* v_n_4614_, lean_object* v_as_4615_, lean_object* v_lo_4616_, lean_object* v_hi_4617_){
_start:
{
lean_object* v___y_4619_; uint8_t v___x_4629_; 
v___x_4629_ = lean_nat_dec_lt(v_lo_4616_, v_hi_4617_);
if (v___x_4629_ == 0)
{
lean_dec(v_lo_4616_);
return v_as_4615_;
}
else
{
lean_object* v___f_4630_; lean_object* v___x_4631_; lean_object* v___x_4632_; lean_object* v_mid_4633_; lean_object* v___y_4635_; lean_object* v___y_4641_; lean_object* v___x_4646_; lean_object* v___x_4647_; uint8_t v___x_4648_; 
v___f_4630_ = lean_obj_once(&l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__6___redArg___closed__0, &l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__6___redArg___closed__0_once, _init_l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__6___redArg___closed__0);
v___x_4631_ = lean_nat_add(v_lo_4616_, v_hi_4617_);
v___x_4632_ = lean_unsigned_to_nat(1u);
v_mid_4633_ = lean_nat_shiftr(v___x_4631_, v___x_4632_);
lean_dec(v___x_4631_);
v___x_4646_ = lean_array_fget_borrowed(v_as_4615_, v_mid_4633_);
v___x_4647_ = lean_array_fget_borrowed(v_as_4615_, v_lo_4616_);
lean_inc(v___x_4647_);
lean_inc(v___x_4646_);
v___x_4648_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__6___redArg___lam__1(v___f_4630_, v___x_4646_, v___x_4647_);
if (v___x_4648_ == 0)
{
v___y_4641_ = v_as_4615_;
goto v___jp_4640_;
}
else
{
lean_object* v___x_4649_; 
v___x_4649_ = lean_array_fswap(v_as_4615_, v_lo_4616_, v_mid_4633_);
v___y_4641_ = v___x_4649_;
goto v___jp_4640_;
}
v___jp_4634_:
{
lean_object* v___x_4636_; lean_object* v___x_4637_; uint8_t v___x_4638_; 
v___x_4636_ = lean_array_fget_borrowed(v___y_4635_, v_mid_4633_);
v___x_4637_ = lean_array_fget_borrowed(v___y_4635_, v_hi_4617_);
lean_inc(v___x_4637_);
lean_inc(v___x_4636_);
v___x_4638_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__6___redArg___lam__1(v___f_4630_, v___x_4636_, v___x_4637_);
if (v___x_4638_ == 0)
{
lean_dec(v_mid_4633_);
v___y_4619_ = v___y_4635_;
goto v___jp_4618_;
}
else
{
lean_object* v___x_4639_; 
v___x_4639_ = lean_array_fswap(v___y_4635_, v_mid_4633_, v_hi_4617_);
lean_dec(v_mid_4633_);
v___y_4619_ = v___x_4639_;
goto v___jp_4618_;
}
}
v___jp_4640_:
{
lean_object* v___x_4642_; lean_object* v___x_4643_; uint8_t v___x_4644_; 
v___x_4642_ = lean_array_fget_borrowed(v___y_4641_, v_hi_4617_);
v___x_4643_ = lean_array_fget_borrowed(v___y_4641_, v_lo_4616_);
lean_inc(v___x_4643_);
lean_inc(v___x_4642_);
v___x_4644_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__6___redArg___lam__1(v___f_4630_, v___x_4642_, v___x_4643_);
if (v___x_4644_ == 0)
{
v___y_4635_ = v___y_4641_;
goto v___jp_4634_;
}
else
{
lean_object* v___x_4645_; 
v___x_4645_ = lean_array_fswap(v___y_4641_, v_lo_4616_, v_hi_4617_);
v___y_4635_ = v___x_4645_;
goto v___jp_4634_;
}
}
}
v___jp_4618_:
{
lean_object* v_pivot_4620_; lean_object* v___x_4621_; lean_object* v_fst_4622_; lean_object* v_snd_4623_; uint8_t v___x_4624_; 
v_pivot_4620_ = lean_array_fget(v___y_4619_, v_hi_4617_);
lean_inc_n(v_lo_4616_, 2);
v___x_4621_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__6_spec__8___redArg(v_hi_4617_, v_pivot_4620_, v___y_4619_, v_lo_4616_, v_lo_4616_);
lean_dec(v_pivot_4620_);
v_fst_4622_ = lean_ctor_get(v___x_4621_, 0);
lean_inc(v_fst_4622_);
v_snd_4623_ = lean_ctor_get(v___x_4621_, 1);
lean_inc(v_snd_4623_);
lean_dec_ref(v___x_4621_);
v___x_4624_ = lean_nat_dec_le(v_hi_4617_, v_fst_4622_);
if (v___x_4624_ == 0)
{
lean_object* v___x_4625_; lean_object* v___x_4626_; lean_object* v___x_4627_; 
v___x_4625_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__6___redArg(v_n_4614_, v_snd_4623_, v_lo_4616_, v_fst_4622_);
v___x_4626_ = lean_unsigned_to_nat(1u);
v___x_4627_ = lean_nat_add(v_fst_4622_, v___x_4626_);
lean_dec(v_fst_4622_);
v_as_4615_ = v___x_4625_;
v_lo_4616_ = v___x_4627_;
goto _start;
}
else
{
lean_dec(v_fst_4622_);
lean_dec(v_lo_4616_);
return v_snd_4623_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__6___redArg___boxed(lean_object* v_n_4650_, lean_object* v_as_4651_, lean_object* v_lo_4652_, lean_object* v_hi_4653_){
_start:
{
lean_object* v_res_4654_; 
v_res_4654_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__6___redArg(v_n_4650_, v_as_4651_, v_lo_4652_, v_hi_4653_);
lean_dec(v_hi_4653_);
lean_dec(v_n_4650_);
return v_res_4654_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Firefox_Profile_export_spec__3(lean_object* v_opts_4655_, lean_object* v_as_4656_, size_t v_sz_4657_, size_t v_i_4658_, lean_object* v_b_4659_){
_start:
{
uint8_t v___x_4661_; 
v___x_4661_ = lean_usize_dec_lt(v_i_4658_, v_sz_4657_);
if (v___x_4661_ == 0)
{
lean_object* v___x_4662_; 
v___x_4662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4662_, 0, v_b_4659_);
return v___x_4662_;
}
else
{
lean_object* v_toThread_4663_; lean_object* v_stringMap_4664_; lean_object* v_funcMap_4665_; lean_object* v_stackMap_4666_; double v_lastTime_4667_; lean_object* v___x_4668_; lean_object* v___x_4669_; lean_object* v_a_4670_; lean_object* v_thread_4672_; double v___x_4680_; uint8_t v___x_4681_; 
v_toThread_4663_ = lean_ctor_get(v_b_4659_, 0);
lean_inc_ref(v_toThread_4663_);
v_stringMap_4664_ = lean_ctor_get(v_b_4659_, 1);
v_funcMap_4665_ = lean_ctor_get(v_b_4659_, 2);
v_stackMap_4666_ = lean_ctor_get(v_b_4659_, 3);
v_lastTime_4667_ = lean_ctor_get_float(v_b_4659_, sizeof(void*)*4);
v___x_4668_ = lean_unsigned_to_nat(0u);
v___x_4669_ = lean_unsigned_to_nat(1u);
v_a_4670_ = lean_array_uget_borrowed(v_as_4656_, v_i_4658_);
v___x_4680_ = l_Float_ofScientific(v___x_4668_, v___x_4661_, v___x_4669_);
v___x_4681_ = lean_float_decLt(v___x_4680_, v_lastTime_4667_);
if (v___x_4681_ == 0)
{
lean_dec_ref(v_toThread_4663_);
v_thread_4672_ = v_b_4659_;
goto v___jp_4671_;
}
else
{
lean_object* v___x_4682_; 
v___x_4682_ = l___private_Lean_Util_Profiler_0__Lean_Firefox_getFirstStart_x3f(v_a_4670_);
if (lean_obj_tag(v___x_4682_) == 1)
{
lean_object* v___x_4684_; uint8_t v_isShared_4685_; uint8_t v_isSharedCheck_4743_; 
lean_inc_ref(v_stackMap_4666_);
lean_inc_ref(v_funcMap_4665_);
lean_inc_ref(v_stringMap_4664_);
v_isSharedCheck_4743_ = !lean_is_exclusive(v_b_4659_);
if (v_isSharedCheck_4743_ == 0)
{
lean_object* v_unused_4744_; lean_object* v_unused_4745_; lean_object* v_unused_4746_; lean_object* v_unused_4747_; 
v_unused_4744_ = lean_ctor_get(v_b_4659_, 3);
lean_dec(v_unused_4744_);
v_unused_4745_ = lean_ctor_get(v_b_4659_, 2);
lean_dec(v_unused_4745_);
v_unused_4746_ = lean_ctor_get(v_b_4659_, 1);
lean_dec(v_unused_4746_);
v_unused_4747_ = lean_ctor_get(v_b_4659_, 0);
lean_dec(v_unused_4747_);
v___x_4684_ = v_b_4659_;
v_isShared_4685_ = v_isSharedCheck_4743_;
goto v_resetjp_4683_;
}
else
{
lean_dec(v_b_4659_);
v___x_4684_ = lean_box(0);
v_isShared_4685_ = v_isSharedCheck_4743_;
goto v_resetjp_4683_;
}
v_resetjp_4683_:
{
lean_object* v_samples_4686_; lean_object* v_val_4687_; lean_object* v_name_4688_; lean_object* v_processType_4689_; uint8_t v_isMainThread_4690_; lean_object* v_markers_4691_; lean_object* v_stackTable_4692_; lean_object* v_frameTable_4693_; lean_object* v_resourceTable_4694_; lean_object* v_nativeSymbols_4695_; lean_object* v_stringArray_4696_; lean_object* v_funcTable_4697_; lean_object* v___x_4699_; uint8_t v_isShared_4700_; uint8_t v_isSharedCheck_4741_; 
v_samples_4686_ = lean_ctor_get(v_toThread_4663_, 2);
lean_inc_ref(v_samples_4686_);
v_val_4687_ = lean_ctor_get(v___x_4682_, 0);
lean_inc(v_val_4687_);
lean_dec_ref_known(v___x_4682_, 1);
v_name_4688_ = lean_ctor_get(v_toThread_4663_, 0);
v_processType_4689_ = lean_ctor_get(v_toThread_4663_, 1);
v_isMainThread_4690_ = lean_ctor_get_uint8(v_toThread_4663_, sizeof(void*)*10);
v_markers_4691_ = lean_ctor_get(v_toThread_4663_, 3);
v_stackTable_4692_ = lean_ctor_get(v_toThread_4663_, 4);
v_frameTable_4693_ = lean_ctor_get(v_toThread_4663_, 5);
v_resourceTable_4694_ = lean_ctor_get(v_toThread_4663_, 6);
v_nativeSymbols_4695_ = lean_ctor_get(v_toThread_4663_, 7);
v_stringArray_4696_ = lean_ctor_get(v_toThread_4663_, 8);
v_funcTable_4697_ = lean_ctor_get(v_toThread_4663_, 9);
v_isSharedCheck_4741_ = !lean_is_exclusive(v_toThread_4663_);
if (v_isSharedCheck_4741_ == 0)
{
lean_object* v_unused_4742_; 
v_unused_4742_ = lean_ctor_get(v_toThread_4663_, 2);
lean_dec(v_unused_4742_);
v___x_4699_ = v_toThread_4663_;
v_isShared_4700_ = v_isSharedCheck_4741_;
goto v_resetjp_4698_;
}
else
{
lean_inc(v_funcTable_4697_);
lean_inc(v_stringArray_4696_);
lean_inc(v_nativeSymbols_4695_);
lean_inc(v_resourceTable_4694_);
lean_inc(v_frameTable_4693_);
lean_inc(v_stackTable_4692_);
lean_inc(v_markers_4691_);
lean_inc(v_processType_4689_);
lean_inc(v_name_4688_);
lean_dec(v_toThread_4663_);
v___x_4699_ = lean_box(0);
v_isShared_4700_ = v_isSharedCheck_4741_;
goto v_resetjp_4698_;
}
v_resetjp_4698_:
{
lean_object* v_stack_4701_; lean_object* v_time_4702_; lean_object* v_weight_4703_; lean_object* v_threadCPUDelta_4704_; lean_object* v_length_4705_; lean_object* v___x_4707_; uint8_t v_isShared_4708_; uint8_t v_isSharedCheck_4739_; 
v_stack_4701_ = lean_ctor_get(v_samples_4686_, 0);
v_time_4702_ = lean_ctor_get(v_samples_4686_, 1);
v_weight_4703_ = lean_ctor_get(v_samples_4686_, 2);
v_threadCPUDelta_4704_ = lean_ctor_get(v_samples_4686_, 4);
v_length_4705_ = lean_ctor_get(v_samples_4686_, 5);
v_isSharedCheck_4739_ = !lean_is_exclusive(v_samples_4686_);
if (v_isSharedCheck_4739_ == 0)
{
lean_object* v_unused_4740_; 
v_unused_4740_ = lean_ctor_get(v_samples_4686_, 3);
lean_dec(v_unused_4740_);
v___x_4707_ = v_samples_4686_;
v_isShared_4708_ = v_isSharedCheck_4739_;
goto v_resetjp_4706_;
}
else
{
lean_inc(v_length_4705_);
lean_inc(v_threadCPUDelta_4704_);
lean_inc(v_weight_4703_);
lean_inc(v_time_4702_);
lean_inc(v_stack_4701_);
lean_dec(v_samples_4686_);
v___x_4707_ = lean_box(0);
v_isShared_4708_ = v_isSharedCheck_4739_;
goto v_resetjp_4706_;
}
v_resetjp_4706_:
{
lean_object* v___x_4709_; lean_object* v___x_4710_; double v___x_4711_; double v___x_4712_; lean_object* v___x_4713_; lean_object* v___x_4714_; double v___x_4715_; double v___x_4716_; lean_object* v___x_4717_; lean_object* v___x_4718_; lean_object* v___x_4719_; lean_object* v___x_4720_; lean_object* v___x_4721_; lean_object* v___x_4722_; lean_object* v___x_4723_; lean_object* v___x_4724_; lean_object* v___x_4725_; lean_object* v___x_4726_; lean_object* v___x_4727_; lean_object* v___x_4728_; lean_object* v___x_4729_; lean_object* v___x_4731_; 
v___x_4709_ = lean_array_push(v_stack_4701_, v___x_4668_);
v___x_4710_ = lean_array_push(v___x_4709_, v___x_4668_);
v___x_4711_ = lean_float_once(&l_Lean_Firefox_instCoeFloatMilliseconds___lam__0___closed__0, &l_Lean_Firefox_instCoeFloatMilliseconds___lam__0___closed__0_once, _init_l_Lean_Firefox_instCoeFloatMilliseconds___lam__0___closed__0);
v___x_4712_ = lean_float_mul(v_lastTime_4667_, v___x_4711_);
v___x_4713_ = lean_box_float(v___x_4712_);
v___x_4714_ = lean_array_push(v_time_4702_, v___x_4713_);
v___x_4715_ = lean_unbox_float(v_val_4687_);
lean_dec(v_val_4687_);
v___x_4716_ = lean_float_mul(v___x_4715_, v___x_4711_);
v___x_4717_ = lean_box_float(v___x_4716_);
v___x_4718_ = lean_array_push(v___x_4714_, v___x_4717_);
v___x_4719_ = lean_box_float(v___x_4680_);
v___x_4720_ = lean_array_push(v_weight_4703_, v___x_4719_);
v___x_4721_ = lean_box_float(v___x_4680_);
v___x_4722_ = lean_array_push(v___x_4720_, v___x_4721_);
v___x_4723_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__0___closed__0));
v___x_4724_ = lean_box_float(v___x_4680_);
v___x_4725_ = lean_array_push(v_threadCPUDelta_4704_, v___x_4724_);
v___x_4726_ = lean_box_float(v___x_4680_);
v___x_4727_ = lean_array_push(v___x_4725_, v___x_4726_);
v___x_4728_ = lean_unsigned_to_nat(2u);
v___x_4729_ = lean_nat_add(v_length_4705_, v___x_4728_);
lean_dec(v_length_4705_);
if (v_isShared_4708_ == 0)
{
lean_ctor_set(v___x_4707_, 5, v___x_4729_);
lean_ctor_set(v___x_4707_, 4, v___x_4727_);
lean_ctor_set(v___x_4707_, 3, v___x_4723_);
lean_ctor_set(v___x_4707_, 2, v___x_4722_);
lean_ctor_set(v___x_4707_, 1, v___x_4718_);
lean_ctor_set(v___x_4707_, 0, v___x_4710_);
v___x_4731_ = v___x_4707_;
goto v_reusejp_4730_;
}
else
{
lean_object* v_reuseFailAlloc_4738_; 
v_reuseFailAlloc_4738_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_4738_, 0, v___x_4710_);
lean_ctor_set(v_reuseFailAlloc_4738_, 1, v___x_4718_);
lean_ctor_set(v_reuseFailAlloc_4738_, 2, v___x_4722_);
lean_ctor_set(v_reuseFailAlloc_4738_, 3, v___x_4723_);
lean_ctor_set(v_reuseFailAlloc_4738_, 4, v___x_4727_);
lean_ctor_set(v_reuseFailAlloc_4738_, 5, v___x_4729_);
v___x_4731_ = v_reuseFailAlloc_4738_;
goto v_reusejp_4730_;
}
v_reusejp_4730_:
{
lean_object* v___x_4733_; 
if (v_isShared_4700_ == 0)
{
lean_ctor_set(v___x_4699_, 2, v___x_4731_);
v___x_4733_ = v___x_4699_;
goto v_reusejp_4732_;
}
else
{
lean_object* v_reuseFailAlloc_4737_; 
v_reuseFailAlloc_4737_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_4737_, 0, v_name_4688_);
lean_ctor_set(v_reuseFailAlloc_4737_, 1, v_processType_4689_);
lean_ctor_set(v_reuseFailAlloc_4737_, 2, v___x_4731_);
lean_ctor_set(v_reuseFailAlloc_4737_, 3, v_markers_4691_);
lean_ctor_set(v_reuseFailAlloc_4737_, 4, v_stackTable_4692_);
lean_ctor_set(v_reuseFailAlloc_4737_, 5, v_frameTable_4693_);
lean_ctor_set(v_reuseFailAlloc_4737_, 6, v_resourceTable_4694_);
lean_ctor_set(v_reuseFailAlloc_4737_, 7, v_nativeSymbols_4695_);
lean_ctor_set(v_reuseFailAlloc_4737_, 8, v_stringArray_4696_);
lean_ctor_set(v_reuseFailAlloc_4737_, 9, v_funcTable_4697_);
lean_ctor_set_uint8(v_reuseFailAlloc_4737_, sizeof(void*)*10, v_isMainThread_4690_);
v___x_4733_ = v_reuseFailAlloc_4737_;
goto v_reusejp_4732_;
}
v_reusejp_4732_:
{
lean_object* v___x_4735_; 
if (v_isShared_4685_ == 0)
{
lean_ctor_set(v___x_4684_, 0, v___x_4733_);
v___x_4735_ = v___x_4684_;
goto v_reusejp_4734_;
}
else
{
lean_object* v_reuseFailAlloc_4736_; 
v_reuseFailAlloc_4736_ = lean_alloc_ctor(0, 4, 8);
lean_ctor_set(v_reuseFailAlloc_4736_, 0, v___x_4733_);
lean_ctor_set(v_reuseFailAlloc_4736_, 1, v_stringMap_4664_);
lean_ctor_set(v_reuseFailAlloc_4736_, 2, v_funcMap_4665_);
lean_ctor_set(v_reuseFailAlloc_4736_, 3, v_stackMap_4666_);
lean_ctor_set_float(v_reuseFailAlloc_4736_, sizeof(void*)*4, v_lastTime_4667_);
v___x_4735_ = v_reuseFailAlloc_4736_;
goto v_reusejp_4734_;
}
v_reusejp_4734_:
{
v_thread_4672_ = v___x_4735_;
goto v___jp_4671_;
}
}
}
}
}
}
}
else
{
lean_dec(v___x_4682_);
lean_dec_ref(v_toThread_4663_);
v_thread_4672_ = v_b_4659_;
goto v___jp_4671_;
}
}
v___jp_4671_:
{
lean_object* v___x_4673_; uint8_t v___x_4674_; lean_object* v___x_4675_; 
v___x_4673_ = l_Lean_trace_profiler_output_pp;
v___x_4674_ = l_Lean_Option_get___at___00Lean_Firefox_Profile_export_spec__2(v_opts_4655_, v___x_4673_);
lean_inc(v_a_4670_);
v___x_4675_ = l___private_Lean_Util_Profiler_0__Lean_Firefox_addTrace(v___x_4674_, v_thread_4672_, v_a_4670_);
if (lean_obj_tag(v___x_4675_) == 0)
{
lean_object* v_a_4676_; size_t v___x_4677_; size_t v___x_4678_; 
v_a_4676_ = lean_ctor_get(v___x_4675_, 0);
lean_inc(v_a_4676_);
lean_dec_ref_known(v___x_4675_, 1);
v___x_4677_ = ((size_t)1ULL);
v___x_4678_ = lean_usize_add(v_i_4658_, v___x_4677_);
v_i_4658_ = v___x_4678_;
v_b_4659_ = v_a_4676_;
goto _start;
}
else
{
return v___x_4675_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Firefox_Profile_export_spec__3___boxed(lean_object* v_opts_4748_, lean_object* v_as_4749_, lean_object* v_sz_4750_, lean_object* v_i_4751_, lean_object* v_b_4752_, lean_object* v___y_4753_){
_start:
{
size_t v_sz_boxed_4754_; size_t v_i_boxed_4755_; lean_object* v_res_4756_; 
v_sz_boxed_4754_ = lean_unbox_usize(v_sz_4750_);
lean_dec(v_sz_4750_);
v_i_boxed_4755_ = lean_unbox_usize(v_i_4751_);
lean_dec(v_i_4751_);
v_res_4756_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Firefox_Profile_export_spec__3(v_opts_4748_, v_as_4749_, v_sz_boxed_4754_, v_i_boxed_4755_, v_b_4752_);
lean_dec_ref(v_as_4749_);
lean_dec_ref(v_opts_4748_);
return v_res_4756_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__7___closed__4(void){
_start:
{
lean_object* v___x_4763_; lean_object* v___x_4764_; 
v___x_4763_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__7___closed__3));
v___x_4764_ = l_Lean_MessageData_ofFormat(v___x_4763_);
return v___x_4764_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__7___closed__6(void){
_start:
{
lean_object* v___x_4767_; lean_object* v___x_4768_; lean_object* v___x_4769_; 
v___x_4767_ = lean_box(0);
v___x_4768_ = lean_unsigned_to_nat(16u);
v___x_4769_ = lean_mk_array(v___x_4768_, v___x_4767_);
return v___x_4769_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__7___closed__7(void){
_start:
{
lean_object* v___x_4770_; lean_object* v___x_4771_; lean_object* v___x_4772_; 
v___x_4770_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__7___closed__6, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__7___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__7___closed__6);
v___x_4771_ = lean_unsigned_to_nat(0u);
v___x_4772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4772_, 0, v___x_4771_);
lean_ctor_set(v___x_4772_, 1, v___x_4770_);
return v___x_4772_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__7(lean_object* v_opts_4773_, double v_startTime_4774_, double v___x_4775_, lean_object* v_name_4776_, size_t v_sz_4777_, size_t v_i_4778_, lean_object* v_bs_4779_){
_start:
{
uint8_t v___x_4781_; 
v___x_4781_ = lean_usize_dec_lt(v_i_4778_, v_sz_4777_);
if (v___x_4781_ == 0)
{
lean_object* v___x_4782_; 
lean_dec_ref(v_name_4776_);
v___x_4782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4782_, 0, v_bs_4779_);
return v___x_4782_;
}
else
{
lean_object* v_v_4783_; lean_object* v_fst_4784_; lean_object* v_snd_4785_; lean_object* v___x_4786_; lean_object* v_bs_x27_4787_; lean_object* v___y_4789_; size_t v___y_4790_; lean_object* v_traces_4791_; uint64_t v___x_4807_; uint64_t v___x_4808_; uint8_t v___x_4809_; lean_object* v___y_4811_; lean_object* v___y_4812_; size_t v___y_4813_; lean_object* v___y_4814_; lean_object* v___y_4826_; lean_object* v___y_4827_; size_t v___y_4828_; lean_object* v___y_4829_; lean_object* v___y_4836_; lean_object* v___y_4837_; lean_object* v___y_4838_; lean_object* v___y_4839_; lean_object* v___y_4840_; size_t v___y_4841_; lean_object* v___y_4842_; lean_object* v___y_4845_; lean_object* v___y_4846_; lean_object* v___y_4847_; lean_object* v___y_4848_; size_t v___y_4849_; lean_object* v___y_4850_; lean_object* v___y_4851_; lean_object* v___y_4854_; 
v_v_4783_ = lean_array_uget_borrowed(v_bs_4779_, v_i_4778_);
v_fst_4784_ = lean_ctor_get(v_v_4783_, 0);
lean_inc(v_fst_4784_);
v_snd_4785_ = lean_ctor_get(v_v_4783_, 1);
lean_inc(v_snd_4785_);
v___x_4786_ = lean_unsigned_to_nat(0u);
v_bs_x27_4787_ = lean_array_uset(v_bs_4779_, v_i_4778_, v___x_4786_);
v___x_4807_ = 0ULL;
v___x_4808_ = lean_unbox_uint64(v_fst_4784_);
v___x_4809_ = lean_uint64_dec_eq(v___x_4808_, v___x_4807_);
if (v___x_4809_ == 0)
{
uint64_t v___x_4884_; lean_object* v___x_4885_; lean_object* v___x_4886_; 
v___x_4884_ = lean_unbox_uint64(v_fst_4784_);
lean_dec(v_fst_4784_);
v___x_4885_ = lean_uint64_to_nat(v___x_4884_);
v___x_4886_ = l_Nat_reprFast(v___x_4885_);
v___y_4854_ = v___x_4886_;
goto v___jp_4853_;
}
else
{
lean_dec(v_fst_4784_);
lean_inc_ref(v_name_4776_);
v___y_4854_ = v_name_4776_;
goto v___jp_4853_;
}
v___jp_4788_:
{
size_t v_sz_4792_; lean_object* v___x_4793_; 
v_sz_4792_ = lean_array_size(v_traces_4791_);
v___x_4793_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Firefox_Profile_export_spec__3(v_opts_4773_, v_traces_4791_, v_sz_4792_, v___y_4790_, v___y_4789_);
lean_dec_ref(v_traces_4791_);
if (lean_obj_tag(v___x_4793_) == 0)
{
lean_object* v_a_4794_; size_t v___x_4795_; size_t v___x_4796_; lean_object* v___x_4797_; 
v_a_4794_ = lean_ctor_get(v___x_4793_, 0);
lean_inc(v_a_4794_);
lean_dec_ref_known(v___x_4793_, 1);
v___x_4795_ = ((size_t)1ULL);
v___x_4796_ = lean_usize_add(v_i_4778_, v___x_4795_);
v___x_4797_ = lean_array_uset(v_bs_x27_4787_, v_i_4778_, v_a_4794_);
v_i_4778_ = v___x_4796_;
v_bs_4779_ = v___x_4797_;
goto _start;
}
else
{
lean_object* v_a_4799_; lean_object* v___x_4801_; uint8_t v_isShared_4802_; uint8_t v_isSharedCheck_4806_; 
lean_dec_ref(v_bs_x27_4787_);
lean_dec_ref(v_name_4776_);
v_a_4799_ = lean_ctor_get(v___x_4793_, 0);
v_isSharedCheck_4806_ = !lean_is_exclusive(v___x_4793_);
if (v_isSharedCheck_4806_ == 0)
{
v___x_4801_ = v___x_4793_;
v_isShared_4802_ = v_isSharedCheck_4806_;
goto v_resetjp_4800_;
}
else
{
lean_inc(v_a_4799_);
lean_dec(v___x_4793_);
v___x_4801_ = lean_box(0);
v_isShared_4802_ = v_isSharedCheck_4806_;
goto v_resetjp_4800_;
}
v_resetjp_4800_:
{
lean_object* v___x_4804_; 
if (v_isShared_4802_ == 0)
{
v___x_4804_ = v___x_4801_;
goto v_reusejp_4803_;
}
else
{
lean_object* v_reuseFailAlloc_4805_; 
v_reuseFailAlloc_4805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4805_, 0, v_a_4799_);
v___x_4804_ = v_reuseFailAlloc_4805_;
goto v_reusejp_4803_;
}
v_reusejp_4803_:
{
return v___x_4804_;
}
}
}
}
v___jp_4810_:
{
size_t v_sz_4815_; lean_object* v___x_4816_; 
v_sz_4815_ = lean_array_size(v___y_4814_);
v___x_4816_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__4(v_sz_4815_, v___y_4813_, v___y_4814_);
if (v___x_4809_ == 0)
{
v___y_4789_ = v___y_4812_;
v___y_4790_ = v___y_4813_;
v_traces_4791_ = v___x_4816_;
goto v___jp_4788_;
}
else
{
lean_object* v___x_4817_; lean_object* v___x_4818_; lean_object* v___x_4819_; lean_object* v___x_4820_; lean_object* v___x_4821_; lean_object* v___x_4822_; lean_object* v___x_4823_; lean_object* v___x_4824_; 
v___x_4817_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__7___closed__1));
v___x_4818_ = lean_box(0);
v___x_4819_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__7___closed__2));
v___x_4820_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4820_, 0, v___x_4817_);
lean_ctor_set(v___x_4820_, 1, v___x_4818_);
lean_ctor_set(v___x_4820_, 2, v___x_4819_);
lean_ctor_set_float(v___x_4820_, sizeof(void*)*3, v_startTime_4774_);
lean_ctor_set_float(v___x_4820_, sizeof(void*)*3 + 8, v___x_4775_);
lean_ctor_set_uint8(v___x_4820_, sizeof(void*)*3 + 16, v___x_4809_);
v___x_4821_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__7___closed__4, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__7___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__7___closed__4);
v___x_4822_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4822_, 0, v___x_4820_);
lean_ctor_set(v___x_4822_, 1, v___x_4821_);
lean_ctor_set(v___x_4822_, 2, v___x_4816_);
v___x_4823_ = lean_mk_empty_array_with_capacity(v___y_4811_);
v___x_4824_ = lean_array_push(v___x_4823_, v___x_4822_);
v___y_4789_ = v___y_4812_;
v___y_4790_ = v___y_4813_;
v_traces_4791_ = v___x_4824_;
goto v___jp_4788_;
}
}
v___jp_4825_:
{
lean_object* v___x_4830_; lean_object* v___x_4831_; uint8_t v___x_4832_; 
v___x_4830_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__7___closed__5));
v___x_4831_ = lean_array_get_size(v___y_4829_);
v___x_4832_ = lean_nat_dec_lt(v___x_4786_, v___x_4831_);
if (v___x_4832_ == 0)
{
lean_dec_ref(v___y_4829_);
v___y_4811_ = v___y_4826_;
v___y_4812_ = v___y_4827_;
v___y_4813_ = v___y_4828_;
v___y_4814_ = v___x_4830_;
goto v___jp_4810_;
}
else
{
size_t v___x_4833_; lean_object* v___x_4834_; 
v___x_4833_ = lean_usize_of_nat(v___x_4831_);
v___x_4834_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Firefox_Profile_export_spec__5(v___y_4829_, v___y_4828_, v___x_4833_, v___x_4830_);
lean_dec_ref(v___y_4829_);
v___y_4811_ = v___y_4826_;
v___y_4812_ = v___y_4827_;
v___y_4813_ = v___y_4828_;
v___y_4814_ = v___x_4834_;
goto v___jp_4810_;
}
}
v___jp_4835_:
{
lean_object* v___x_4843_; 
v___x_4843_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__6___redArg(v___y_4840_, v___y_4838_, v___y_4837_, v___y_4842_);
lean_dec(v___y_4842_);
lean_dec(v___y_4840_);
v___y_4826_ = v___y_4836_;
v___y_4827_ = v___y_4839_;
v___y_4828_ = v___y_4841_;
v___y_4829_ = v___x_4843_;
goto v___jp_4825_;
}
v___jp_4844_:
{
uint8_t v___x_4852_; 
v___x_4852_ = lean_nat_dec_le(v___y_4851_, v___y_4850_);
if (v___x_4852_ == 0)
{
lean_dec(v___y_4850_);
lean_inc(v___y_4851_);
v___y_4836_ = v___y_4845_;
v___y_4837_ = v___y_4851_;
v___y_4838_ = v___y_4846_;
v___y_4839_ = v___y_4847_;
v___y_4840_ = v___y_4848_;
v___y_4841_ = v___y_4849_;
v___y_4842_ = v___y_4851_;
goto v___jp_4835_;
}
else
{
v___y_4836_ = v___y_4845_;
v___y_4837_ = v___y_4851_;
v___y_4838_ = v___y_4846_;
v___y_4839_ = v___y_4847_;
v___y_4840_ = v___y_4848_;
v___y_4841_ = v___y_4849_;
v___y_4842_ = v___y_4850_;
goto v___jp_4835_;
}
}
v___jp_4853_:
{
lean_object* v___x_4855_; lean_object* v_name_4856_; lean_object* v_processType_4857_; lean_object* v_samples_4858_; lean_object* v_markers_4859_; lean_object* v_stackTable_4860_; lean_object* v_frameTable_4861_; lean_object* v_resourceTable_4862_; lean_object* v_nativeSymbols_4863_; lean_object* v_stringArray_4864_; lean_object* v_funcTable_4865_; lean_object* v___x_4867_; uint8_t v_isShared_4868_; uint8_t v_isSharedCheck_4883_; 
v___x_4855_ = l_Lean_Firefox_Thread_new(v___y_4854_);
v_name_4856_ = lean_ctor_get(v___x_4855_, 0);
v_processType_4857_ = lean_ctor_get(v___x_4855_, 1);
v_samples_4858_ = lean_ctor_get(v___x_4855_, 2);
v_markers_4859_ = lean_ctor_get(v___x_4855_, 3);
v_stackTable_4860_ = lean_ctor_get(v___x_4855_, 4);
v_frameTable_4861_ = lean_ctor_get(v___x_4855_, 5);
v_resourceTable_4862_ = lean_ctor_get(v___x_4855_, 6);
v_nativeSymbols_4863_ = lean_ctor_get(v___x_4855_, 7);
v_stringArray_4864_ = lean_ctor_get(v___x_4855_, 8);
v_funcTable_4865_ = lean_ctor_get(v___x_4855_, 9);
v_isSharedCheck_4883_ = !lean_is_exclusive(v___x_4855_);
if (v_isSharedCheck_4883_ == 0)
{
v___x_4867_ = v___x_4855_;
v_isShared_4868_ = v_isSharedCheck_4883_;
goto v_resetjp_4866_;
}
else
{
lean_inc(v_funcTable_4865_);
lean_inc(v_stringArray_4864_);
lean_inc(v_nativeSymbols_4863_);
lean_inc(v_resourceTable_4862_);
lean_inc(v_frameTable_4861_);
lean_inc(v_stackTable_4860_);
lean_inc(v_markers_4859_);
lean_inc(v_samples_4858_);
lean_inc(v_processType_4857_);
lean_inc(v_name_4856_);
lean_dec(v___x_4855_);
v___x_4867_ = lean_box(0);
v_isShared_4868_ = v_isSharedCheck_4883_;
goto v_resetjp_4866_;
}
v_resetjp_4866_:
{
lean_object* v___x_4870_; 
if (v_isShared_4868_ == 0)
{
v___x_4870_ = v___x_4867_;
goto v_reusejp_4869_;
}
else
{
lean_object* v_reuseFailAlloc_4882_; 
v_reuseFailAlloc_4882_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_4882_, 0, v_name_4856_);
lean_ctor_set(v_reuseFailAlloc_4882_, 1, v_processType_4857_);
lean_ctor_set(v_reuseFailAlloc_4882_, 2, v_samples_4858_);
lean_ctor_set(v_reuseFailAlloc_4882_, 3, v_markers_4859_);
lean_ctor_set(v_reuseFailAlloc_4882_, 4, v_stackTable_4860_);
lean_ctor_set(v_reuseFailAlloc_4882_, 5, v_frameTable_4861_);
lean_ctor_set(v_reuseFailAlloc_4882_, 6, v_resourceTable_4862_);
lean_ctor_set(v_reuseFailAlloc_4882_, 7, v_nativeSymbols_4863_);
lean_ctor_set(v_reuseFailAlloc_4882_, 8, v_stringArray_4864_);
lean_ctor_set(v_reuseFailAlloc_4882_, 9, v_funcTable_4865_);
v___x_4870_ = v_reuseFailAlloc_4882_;
goto v_reusejp_4869_;
}
v_reusejp_4869_:
{
lean_object* v___x_4871_; double v___x_4872_; lean_object* v___x_4873_; size_t v_sz_4874_; size_t v___x_4875_; lean_object* v___x_4876_; lean_object* v___x_4877_; lean_object* v___x_4878_; uint8_t v___x_4879_; 
lean_ctor_set_uint8(v___x_4870_, sizeof(void*)*10, v___x_4809_);
v___x_4871_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__7___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__7___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__7___closed__7);
v___x_4872_ = lean_float_once(&l___private_Lean_Util_Profiler_0__Lean_Firefox_getFirstStart_x3f___closed__0, &l___private_Lean_Util_Profiler_0__Lean_Firefox_getFirstStart_x3f___closed__0_once, _init_l___private_Lean_Util_Profiler_0__Lean_Firefox_getFirstStart_x3f___closed__0);
v___x_4873_ = lean_alloc_ctor(0, 4, 8);
lean_ctor_set(v___x_4873_, 0, v___x_4870_);
lean_ctor_set(v___x_4873_, 1, v___x_4871_);
lean_ctor_set(v___x_4873_, 2, v___x_4871_);
lean_ctor_set(v___x_4873_, 3, v___x_4871_);
lean_ctor_set_float(v___x_4873_, sizeof(void*)*4, v___x_4872_);
v_sz_4874_ = lean_array_size(v_snd_4785_);
v___x_4875_ = ((size_t)0ULL);
v___x_4876_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__1(v_sz_4874_, v___x_4875_, v_snd_4785_);
v___x_4877_ = lean_unsigned_to_nat(1u);
v___x_4878_ = lean_array_get_size(v___x_4876_);
v___x_4879_ = lean_nat_dec_eq(v___x_4878_, v___x_4786_);
if (v___x_4879_ == 0)
{
lean_object* v___x_4880_; uint8_t v___x_4881_; 
v___x_4880_ = lean_nat_sub(v___x_4878_, v___x_4877_);
v___x_4881_ = lean_nat_dec_le(v___x_4786_, v___x_4880_);
if (v___x_4881_ == 0)
{
lean_inc(v___x_4880_);
v___y_4845_ = v___x_4877_;
v___y_4846_ = v___x_4876_;
v___y_4847_ = v___x_4873_;
v___y_4848_ = v___x_4878_;
v___y_4849_ = v___x_4875_;
v___y_4850_ = v___x_4880_;
v___y_4851_ = v___x_4880_;
goto v___jp_4844_;
}
else
{
v___y_4845_ = v___x_4877_;
v___y_4846_ = v___x_4876_;
v___y_4847_ = v___x_4873_;
v___y_4848_ = v___x_4878_;
v___y_4849_ = v___x_4875_;
v___y_4850_ = v___x_4880_;
v___y_4851_ = v___x_4786_;
goto v___jp_4844_;
}
}
else
{
v___y_4826_ = v___x_4877_;
v___y_4827_ = v___x_4873_;
v___y_4828_ = v___x_4875_;
v___y_4829_ = v___x_4876_;
goto v___jp_4825_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__7___boxed(lean_object* v_opts_4887_, lean_object* v_startTime_4888_, lean_object* v___x_4889_, lean_object* v_name_4890_, lean_object* v_sz_4891_, lean_object* v_i_4892_, lean_object* v_bs_4893_, lean_object* v___y_4894_){
_start:
{
double v_startTime_boxed_4895_; double v___x_4638__boxed_4896_; size_t v_sz_boxed_4897_; size_t v_i_boxed_4898_; lean_object* v_res_4899_; 
v_startTime_boxed_4895_ = lean_unbox_float(v_startTime_4888_);
lean_dec_ref(v_startTime_4888_);
v___x_4638__boxed_4896_ = lean_unbox_float(v___x_4889_);
lean_dec_ref(v___x_4889_);
v_sz_boxed_4897_ = lean_unbox_usize(v_sz_4891_);
lean_dec(v_sz_4891_);
v_i_boxed_4898_ = lean_unbox_usize(v_i_4892_);
lean_dec(v_i_4892_);
v_res_4899_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__7(v_opts_4887_, v_startTime_boxed_4895_, v___x_4638__boxed_4896_, v_name_4890_, v_sz_boxed_4897_, v_i_boxed_4898_, v_bs_4893_);
lean_dec_ref(v_opts_4887_);
return v_res_4899_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__2___redArg(uint64_t v_a_4900_, lean_object* v_x_4901_){
_start:
{
if (lean_obj_tag(v_x_4901_) == 0)
{
uint8_t v___x_4902_; 
v___x_4902_ = 0;
return v___x_4902_;
}
else
{
lean_object* v_key_4903_; lean_object* v_tail_4904_; uint64_t v___x_4905_; uint8_t v___x_4906_; 
v_key_4903_ = lean_ctor_get(v_x_4901_, 0);
v_tail_4904_ = lean_ctor_get(v_x_4901_, 2);
v___x_4905_ = lean_unbox_uint64(v_key_4903_);
v___x_4906_ = lean_uint64_dec_eq(v___x_4905_, v_a_4900_);
if (v___x_4906_ == 0)
{
v_x_4901_ = v_tail_4904_;
goto _start;
}
else
{
return v___x_4906_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_a_4908_, lean_object* v_x_4909_){
_start:
{
uint64_t v_a_boxed_4910_; uint8_t v_res_4911_; lean_object* v_r_4912_; 
v_a_boxed_4910_ = lean_unbox_uint64(v_a_4908_);
lean_dec_ref(v_a_4908_);
v_res_4911_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__2___redArg(v_a_boxed_4910_, v_x_4909_);
lean_dec(v_x_4909_);
v_r_4912_ = lean_box(v_res_4911_);
return v_r_4912_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__4___redArg___lam__0(lean_object* v_a_4915_, lean_object* v_x_4916_){
_start:
{
lean_object* v___y_4918_; 
if (lean_obj_tag(v_x_4916_) == 0)
{
lean_object* v___x_4921_; 
v___x_4921_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__4___redArg___lam__0___closed__0));
v___y_4918_ = v___x_4921_;
goto v___jp_4917_;
}
else
{
lean_object* v_val_4922_; 
v_val_4922_ = lean_ctor_get(v_x_4916_, 0);
lean_inc(v_val_4922_);
lean_dec_ref_known(v_x_4916_, 1);
v___y_4918_ = v_val_4922_;
goto v___jp_4917_;
}
v___jp_4917_:
{
lean_object* v___x_4919_; lean_object* v___x_4920_; 
v___x_4919_ = lean_array_push(v___y_4918_, v_a_4915_);
v___x_4920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4920_, 0, v___x_4919_);
return v___x_4920_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__4___redArg(lean_object* v_a_4923_, uint64_t v_a_4924_, lean_object* v_x_4925_){
_start:
{
if (lean_obj_tag(v_x_4925_) == 0)
{
lean_object* v___x_4926_; lean_object* v___x_4927_; lean_object* v_val_4928_; lean_object* v___x_4929_; lean_object* v___x_4930_; 
v___x_4926_ = lean_box(0);
v___x_4927_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__4___redArg___lam__0(v_a_4923_, v___x_4926_);
v_val_4928_ = lean_ctor_get(v___x_4927_, 0);
lean_inc(v_val_4928_);
lean_dec(v___x_4927_);
v___x_4929_ = lean_box_uint64(v_a_4924_);
v___x_4930_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4930_, 0, v___x_4929_);
lean_ctor_set(v___x_4930_, 1, v_val_4928_);
lean_ctor_set(v___x_4930_, 2, v_x_4925_);
return v___x_4930_;
}
else
{
lean_object* v_key_4931_; lean_object* v_value_4932_; lean_object* v_tail_4933_; lean_object* v___x_4935_; uint8_t v_isShared_4936_; uint8_t v_isSharedCheck_4950_; 
v_key_4931_ = lean_ctor_get(v_x_4925_, 0);
v_value_4932_ = lean_ctor_get(v_x_4925_, 1);
v_tail_4933_ = lean_ctor_get(v_x_4925_, 2);
v_isSharedCheck_4950_ = !lean_is_exclusive(v_x_4925_);
if (v_isSharedCheck_4950_ == 0)
{
v___x_4935_ = v_x_4925_;
v_isShared_4936_ = v_isSharedCheck_4950_;
goto v_resetjp_4934_;
}
else
{
lean_inc(v_tail_4933_);
lean_inc(v_value_4932_);
lean_inc(v_key_4931_);
lean_dec(v_x_4925_);
v___x_4935_ = lean_box(0);
v_isShared_4936_ = v_isSharedCheck_4950_;
goto v_resetjp_4934_;
}
v_resetjp_4934_:
{
uint64_t v___x_4937_; uint8_t v___x_4938_; 
v___x_4937_ = lean_unbox_uint64(v_key_4931_);
v___x_4938_ = lean_uint64_dec_eq(v___x_4937_, v_a_4924_);
if (v___x_4938_ == 0)
{
lean_object* v_tail_4939_; lean_object* v___x_4941_; 
v_tail_4939_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__4___redArg(v_a_4923_, v_a_4924_, v_tail_4933_);
if (v_isShared_4936_ == 0)
{
lean_ctor_set(v___x_4935_, 2, v_tail_4939_);
v___x_4941_ = v___x_4935_;
goto v_reusejp_4940_;
}
else
{
lean_object* v_reuseFailAlloc_4942_; 
v_reuseFailAlloc_4942_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4942_, 0, v_key_4931_);
lean_ctor_set(v_reuseFailAlloc_4942_, 1, v_value_4932_);
lean_ctor_set(v_reuseFailAlloc_4942_, 2, v_tail_4939_);
v___x_4941_ = v_reuseFailAlloc_4942_;
goto v_reusejp_4940_;
}
v_reusejp_4940_:
{
return v___x_4941_;
}
}
else
{
lean_object* v___x_4943_; lean_object* v___x_4944_; lean_object* v_val_4945_; lean_object* v___x_4946_; lean_object* v___x_4948_; 
lean_dec(v_key_4931_);
v___x_4943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4943_, 0, v_value_4932_);
v___x_4944_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__4___redArg___lam__0(v_a_4923_, v___x_4943_);
v_val_4945_ = lean_ctor_get(v___x_4944_, 0);
lean_inc(v_val_4945_);
lean_dec(v___x_4944_);
v___x_4946_ = lean_box_uint64(v_a_4924_);
if (v_isShared_4936_ == 0)
{
lean_ctor_set(v___x_4935_, 1, v_val_4945_);
lean_ctor_set(v___x_4935_, 0, v___x_4946_);
v___x_4948_ = v___x_4935_;
goto v_reusejp_4947_;
}
else
{
lean_object* v_reuseFailAlloc_4949_; 
v_reuseFailAlloc_4949_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4949_, 0, v___x_4946_);
lean_ctor_set(v_reuseFailAlloc_4949_, 1, v_val_4945_);
lean_ctor_set(v_reuseFailAlloc_4949_, 2, v_tail_4933_);
v___x_4948_ = v_reuseFailAlloc_4949_;
goto v_reusejp_4947_;
}
v_reusejp_4947_:
{
return v___x_4948_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_a_4951_, lean_object* v_a_4952_, lean_object* v_x_4953_){
_start:
{
uint64_t v_a_boxed_4954_; lean_object* v_res_4955_; 
v_a_boxed_4954_ = lean_unbox_uint64(v_a_4952_);
lean_dec_ref(v_a_4952_);
v_res_4955_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__4___redArg(v_a_4951_, v_a_boxed_4954_, v_x_4953_);
return v_res_4955_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__3_spec__14_spec__18___redArg(lean_object* v_x_4956_, lean_object* v_x_4957_){
_start:
{
if (lean_obj_tag(v_x_4957_) == 0)
{
return v_x_4956_;
}
else
{
lean_object* v_key_4958_; lean_object* v_value_4959_; lean_object* v_tail_4960_; lean_object* v___x_4962_; uint8_t v_isShared_4963_; uint8_t v_isSharedCheck_4984_; 
v_key_4958_ = lean_ctor_get(v_x_4957_, 0);
v_value_4959_ = lean_ctor_get(v_x_4957_, 1);
v_tail_4960_ = lean_ctor_get(v_x_4957_, 2);
v_isSharedCheck_4984_ = !lean_is_exclusive(v_x_4957_);
if (v_isSharedCheck_4984_ == 0)
{
v___x_4962_ = v_x_4957_;
v_isShared_4963_ = v_isSharedCheck_4984_;
goto v_resetjp_4961_;
}
else
{
lean_inc(v_tail_4960_);
lean_inc(v_value_4959_);
lean_inc(v_key_4958_);
lean_dec(v_x_4957_);
v___x_4962_ = lean_box(0);
v_isShared_4963_ = v_isSharedCheck_4984_;
goto v_resetjp_4961_;
}
v_resetjp_4961_:
{
lean_object* v___x_4964_; uint64_t v___x_4965_; uint64_t v___x_4966_; uint64_t v___x_4967_; uint64_t v___x_4968_; uint64_t v_fold_4969_; uint64_t v___x_4970_; uint64_t v___x_4971_; uint64_t v___x_4972_; size_t v___x_4973_; size_t v___x_4974_; size_t v___x_4975_; size_t v___x_4976_; size_t v___x_4977_; lean_object* v___x_4978_; lean_object* v___x_4980_; 
v___x_4964_ = lean_array_get_size(v_x_4956_);
v___x_4965_ = 32ULL;
v___x_4966_ = lean_unbox_uint64(v_key_4958_);
v___x_4967_ = lean_uint64_shift_right(v___x_4966_, v___x_4965_);
v___x_4968_ = lean_unbox_uint64(v_key_4958_);
v_fold_4969_ = lean_uint64_xor(v___x_4968_, v___x_4967_);
v___x_4970_ = 16ULL;
v___x_4971_ = lean_uint64_shift_right(v_fold_4969_, v___x_4970_);
v___x_4972_ = lean_uint64_xor(v_fold_4969_, v___x_4971_);
v___x_4973_ = lean_uint64_to_usize(v___x_4972_);
v___x_4974_ = lean_usize_of_nat(v___x_4964_);
v___x_4975_ = ((size_t)1ULL);
v___x_4976_ = lean_usize_sub(v___x_4974_, v___x_4975_);
v___x_4977_ = lean_usize_land(v___x_4973_, v___x_4976_);
v___x_4978_ = lean_array_uget_borrowed(v_x_4956_, v___x_4977_);
lean_inc(v___x_4978_);
if (v_isShared_4963_ == 0)
{
lean_ctor_set(v___x_4962_, 2, v___x_4978_);
v___x_4980_ = v___x_4962_;
goto v_reusejp_4979_;
}
else
{
lean_object* v_reuseFailAlloc_4983_; 
v_reuseFailAlloc_4983_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4983_, 0, v_key_4958_);
lean_ctor_set(v_reuseFailAlloc_4983_, 1, v_value_4959_);
lean_ctor_set(v_reuseFailAlloc_4983_, 2, v___x_4978_);
v___x_4980_ = v_reuseFailAlloc_4983_;
goto v_reusejp_4979_;
}
v_reusejp_4979_:
{
lean_object* v___x_4981_; 
v___x_4981_ = lean_array_uset(v_x_4956_, v___x_4977_, v___x_4980_);
v_x_4956_ = v___x_4981_;
v_x_4957_ = v_tail_4960_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__3_spec__14___redArg(lean_object* v_i_4985_, lean_object* v_source_4986_, lean_object* v_target_4987_){
_start:
{
lean_object* v___x_4988_; uint8_t v___x_4989_; 
v___x_4988_ = lean_array_get_size(v_source_4986_);
v___x_4989_ = lean_nat_dec_lt(v_i_4985_, v___x_4988_);
if (v___x_4989_ == 0)
{
lean_dec_ref(v_source_4986_);
lean_dec(v_i_4985_);
return v_target_4987_;
}
else
{
lean_object* v_es_4990_; lean_object* v___x_4991_; lean_object* v_source_4992_; lean_object* v_target_4993_; lean_object* v___x_4994_; lean_object* v___x_4995_; 
v_es_4990_ = lean_array_fget(v_source_4986_, v_i_4985_);
v___x_4991_ = lean_box(0);
v_source_4992_ = lean_array_fset(v_source_4986_, v_i_4985_, v___x_4991_);
v_target_4993_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__3_spec__14_spec__18___redArg(v_target_4987_, v_es_4990_);
v___x_4994_ = lean_unsigned_to_nat(1u);
v___x_4995_ = lean_nat_add(v_i_4985_, v___x_4994_);
lean_dec(v_i_4985_);
v_i_4985_ = v___x_4995_;
v_source_4986_ = v_source_4992_;
v_target_4987_ = v_target_4993_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__3___redArg(lean_object* v_data_4997_){
_start:
{
lean_object* v___x_4998_; lean_object* v___x_4999_; lean_object* v_nbuckets_5000_; lean_object* v___x_5001_; lean_object* v___x_5002_; lean_object* v___x_5003_; lean_object* v___x_5004_; lean_object* v___x_5005_; 
v___x_4998_ = lean_array_get_size(v_data_4997_);
v___x_4999_ = lean_unsigned_to_nat(2u);
v_nbuckets_5000_ = lean_nat_mul(v___x_4998_, v___x_4999_);
v___x_5001_ = lean_unsigned_to_nat(0u);
v___x_5002_ = lean_box(0);
v___x_5003_ = lean_mk_array(v_nbuckets_5000_, v___x_5002_);
v___x_5004_ = lean_array_propagate_mark(v_data_4997_, v___x_5003_);
v___x_5005_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__3_spec__14___redArg(v___x_5001_, v_data_4997_, v___x_5004_);
return v___x_5005_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0___redArg(lean_object* v_a_5006_, lean_object* v_m_5007_, uint64_t v_a_5008_){
_start:
{
lean_object* v_size_5009_; lean_object* v_buckets_5010_; lean_object* v___x_5012_; uint8_t v_isShared_5013_; uint8_t v_isSharedCheck_5060_; 
v_size_5009_ = lean_ctor_get(v_m_5007_, 0);
v_buckets_5010_ = lean_ctor_get(v_m_5007_, 1);
v_isSharedCheck_5060_ = !lean_is_exclusive(v_m_5007_);
if (v_isSharedCheck_5060_ == 0)
{
v___x_5012_ = v_m_5007_;
v_isShared_5013_ = v_isSharedCheck_5060_;
goto v_resetjp_5011_;
}
else
{
lean_inc(v_buckets_5010_);
lean_inc(v_size_5009_);
lean_dec(v_m_5007_);
v___x_5012_ = lean_box(0);
v_isShared_5013_ = v_isSharedCheck_5060_;
goto v_resetjp_5011_;
}
v_resetjp_5011_:
{
lean_object* v___x_5014_; uint64_t v___x_5015_; uint64_t v___x_5016_; uint64_t v_fold_5017_; uint64_t v___x_5018_; uint64_t v___x_5019_; uint64_t v___x_5020_; size_t v___x_5021_; size_t v___x_5022_; size_t v___x_5023_; size_t v___x_5024_; size_t v___x_5025_; lean_object* v_bkt_5026_; uint8_t v___x_5027_; 
v___x_5014_ = lean_array_get_size(v_buckets_5010_);
v___x_5015_ = 32ULL;
v___x_5016_ = lean_uint64_shift_right(v_a_5008_, v___x_5015_);
v_fold_5017_ = lean_uint64_xor(v_a_5008_, v___x_5016_);
v___x_5018_ = 16ULL;
v___x_5019_ = lean_uint64_shift_right(v_fold_5017_, v___x_5018_);
v___x_5020_ = lean_uint64_xor(v_fold_5017_, v___x_5019_);
v___x_5021_ = lean_uint64_to_usize(v___x_5020_);
v___x_5022_ = lean_usize_of_nat(v___x_5014_);
v___x_5023_ = ((size_t)1ULL);
v___x_5024_ = lean_usize_sub(v___x_5022_, v___x_5023_);
v___x_5025_ = lean_usize_land(v___x_5021_, v___x_5024_);
v_bkt_5026_ = lean_array_uget_borrowed(v_buckets_5010_, v___x_5025_);
v___x_5027_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__2___redArg(v_a_5008_, v_bkt_5026_);
if (v___x_5027_ == 0)
{
lean_object* v___x_5028_; lean_object* v___x_5029_; lean_object* v___x_5030_; lean_object* v_size_x27_5031_; lean_object* v___x_5032_; lean_object* v___x_5033_; lean_object* v_buckets_x27_5034_; lean_object* v___x_5035_; lean_object* v___x_5036_; lean_object* v___x_5037_; lean_object* v___x_5038_; lean_object* v___x_5039_; uint8_t v___x_5040_; 
v___x_5028_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__4___redArg___lam__0___closed__0));
v___x_5029_ = lean_array_push(v___x_5028_, v_a_5006_);
v___x_5030_ = lean_unsigned_to_nat(1u);
v_size_x27_5031_ = lean_nat_add(v_size_5009_, v___x_5030_);
lean_dec(v_size_5009_);
v___x_5032_ = lean_box_uint64(v_a_5008_);
lean_inc(v_bkt_5026_);
v___x_5033_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5033_, 0, v___x_5032_);
lean_ctor_set(v___x_5033_, 1, v___x_5029_);
lean_ctor_set(v___x_5033_, 2, v_bkt_5026_);
v_buckets_x27_5034_ = lean_array_uset(v_buckets_5010_, v___x_5025_, v___x_5033_);
v___x_5035_ = lean_unsigned_to_nat(4u);
v___x_5036_ = lean_nat_mul(v_size_x27_5031_, v___x_5035_);
v___x_5037_ = lean_unsigned_to_nat(3u);
v___x_5038_ = lean_nat_div(v___x_5036_, v___x_5037_);
lean_dec(v___x_5036_);
v___x_5039_ = lean_array_get_size(v_buckets_x27_5034_);
v___x_5040_ = lean_nat_dec_le(v___x_5038_, v___x_5039_);
lean_dec(v___x_5038_);
if (v___x_5040_ == 0)
{
lean_object* v_val_5041_; lean_object* v___x_5043_; 
v_val_5041_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__3___redArg(v_buckets_x27_5034_);
if (v_isShared_5013_ == 0)
{
lean_ctor_set(v___x_5012_, 1, v_val_5041_);
lean_ctor_set(v___x_5012_, 0, v_size_x27_5031_);
v___x_5043_ = v___x_5012_;
goto v_reusejp_5042_;
}
else
{
lean_object* v_reuseFailAlloc_5044_; 
v_reuseFailAlloc_5044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5044_, 0, v_size_x27_5031_);
lean_ctor_set(v_reuseFailAlloc_5044_, 1, v_val_5041_);
v___x_5043_ = v_reuseFailAlloc_5044_;
goto v_reusejp_5042_;
}
v_reusejp_5042_:
{
return v___x_5043_;
}
}
else
{
lean_object* v___x_5046_; 
if (v_isShared_5013_ == 0)
{
lean_ctor_set(v___x_5012_, 1, v_buckets_x27_5034_);
lean_ctor_set(v___x_5012_, 0, v_size_x27_5031_);
v___x_5046_ = v___x_5012_;
goto v_reusejp_5045_;
}
else
{
lean_object* v_reuseFailAlloc_5047_; 
v_reuseFailAlloc_5047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5047_, 0, v_size_x27_5031_);
lean_ctor_set(v_reuseFailAlloc_5047_, 1, v_buckets_x27_5034_);
v___x_5046_ = v_reuseFailAlloc_5047_;
goto v_reusejp_5045_;
}
v_reusejp_5045_:
{
return v___x_5046_;
}
}
}
else
{
lean_object* v___x_5048_; lean_object* v_buckets_x27_5049_; lean_object* v_bkt_x27_5050_; lean_object* v___y_5052_; uint8_t v___x_5057_; 
lean_inc(v_bkt_5026_);
v___x_5048_ = lean_box(0);
v_buckets_x27_5049_ = lean_array_uset(v_buckets_5010_, v___x_5025_, v___x_5048_);
v_bkt_x27_5050_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__4___redArg(v_a_5006_, v_a_5008_, v_bkt_5026_);
v___x_5057_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__2___redArg(v_a_5008_, v_bkt_x27_5050_);
if (v___x_5057_ == 0)
{
lean_object* v___x_5058_; lean_object* v___x_5059_; 
v___x_5058_ = lean_unsigned_to_nat(1u);
v___x_5059_ = lean_nat_sub(v_size_5009_, v___x_5058_);
lean_dec(v_size_5009_);
v___y_5052_ = v___x_5059_;
goto v___jp_5051_;
}
else
{
v___y_5052_ = v_size_5009_;
goto v___jp_5051_;
}
v___jp_5051_:
{
lean_object* v___x_5053_; lean_object* v___x_5055_; 
v___x_5053_ = lean_array_uset(v_buckets_x27_5049_, v___x_5025_, v_bkt_x27_5050_);
if (v_isShared_5013_ == 0)
{
lean_ctor_set(v___x_5012_, 1, v___x_5053_);
lean_ctor_set(v___x_5012_, 0, v___y_5052_);
v___x_5055_ = v___x_5012_;
goto v_reusejp_5054_;
}
else
{
lean_object* v_reuseFailAlloc_5056_; 
v_reuseFailAlloc_5056_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5056_, 0, v___y_5052_);
lean_ctor_set(v_reuseFailAlloc_5056_, 1, v___x_5053_);
v___x_5055_ = v_reuseFailAlloc_5056_;
goto v_reusejp_5054_;
}
v_reusejp_5054_:
{
return v___x_5055_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0___redArg___boxed(lean_object* v_a_5061_, lean_object* v_m_5062_, lean_object* v_a_5063_){
_start:
{
uint64_t v_a_boxed_5064_; lean_object* v_res_5065_; 
v_a_boxed_5064_ = lean_unbox_uint64(v_a_5063_);
lean_dec_ref(v_a_5063_);
v_res_5065_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0___redArg(v_a_5061_, v_m_5062_, v_a_boxed_5064_);
return v_res_5065_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__1___redArg(lean_object* v_key_5066_, lean_object* v_as_5067_, size_t v_sz_5068_, size_t v_i_5069_, lean_object* v_b_5070_){
_start:
{
uint8_t v___x_5071_; 
v___x_5071_ = lean_usize_dec_lt(v_i_5069_, v_sz_5068_);
if (v___x_5071_ == 0)
{
lean_dec_ref(v_key_5066_);
return v_b_5070_;
}
else
{
lean_object* v_a_5072_; lean_object* v___x_5073_; uint64_t v___x_5074_; lean_object* v___x_5075_; size_t v___x_5076_; size_t v___x_5077_; 
v_a_5072_ = lean_array_uget_borrowed(v_as_5067_, v_i_5069_);
lean_inc_ref(v_key_5066_);
lean_inc_n(v_a_5072_, 2);
v___x_5073_ = lean_apply_1(v_key_5066_, v_a_5072_);
v___x_5074_ = lean_unbox_uint64(v___x_5073_);
lean_dec_ref(v___x_5073_);
v___x_5075_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0___redArg(v_a_5072_, v_b_5070_, v___x_5074_);
v___x_5076_ = ((size_t)1ULL);
v___x_5077_ = lean_usize_add(v_i_5069_, v___x_5076_);
v_i_5069_ = v___x_5077_;
v_b_5070_ = v___x_5075_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__1___redArg___boxed(lean_object* v_key_5079_, lean_object* v_as_5080_, lean_object* v_sz_5081_, lean_object* v_i_5082_, lean_object* v_b_5083_){
_start:
{
size_t v_sz_boxed_5084_; size_t v_i_boxed_5085_; lean_object* v_res_5086_; 
v_sz_boxed_5084_ = lean_unbox_usize(v_sz_5081_);
lean_dec(v_sz_5081_);
v_i_boxed_5085_ = lean_unbox_usize(v_i_5082_);
lean_dec(v_i_5082_);
v_res_5086_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__1___redArg(v_key_5079_, v_as_5080_, v_sz_boxed_5084_, v_i_boxed_5085_, v_b_5083_);
lean_dec_ref(v_as_5080_);
return v_res_5086_;
}
}
static lean_object* _init_l_Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_5087_; lean_object* v___x_5088_; lean_object* v___x_5089_; 
v___x_5087_ = lean_box(0);
v___x_5088_ = lean_unsigned_to_nat(16u);
v___x_5089_ = lean_mk_array(v___x_5088_, v___x_5087_);
return v___x_5089_;
}
}
static lean_object* _init_l_Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_5090_; lean_object* v___x_5091_; lean_object* v_groups_5092_; 
v___x_5090_ = lean_obj_once(&l_Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0___redArg___closed__0, &l_Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0___redArg___closed__0_once, _init_l_Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0___redArg___closed__0);
v___x_5091_ = lean_unsigned_to_nat(0u);
v_groups_5092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_groups_5092_, 0, v___x_5091_);
lean_ctor_set(v_groups_5092_, 1, v___x_5090_);
return v_groups_5092_;
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0___redArg(lean_object* v_key_5093_, lean_object* v_xs_5094_){
_start:
{
lean_object* v_groups_5095_; size_t v_sz_5096_; size_t v___x_5097_; lean_object* v___x_5098_; 
v_groups_5095_ = lean_obj_once(&l_Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0___redArg___closed__1, &l_Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0___redArg___closed__1_once, _init_l_Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0___redArg___closed__1);
v_sz_5096_ = lean_array_size(v_xs_5094_);
v___x_5097_ = ((size_t)0ULL);
v___x_5098_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__1___redArg(v_key_5093_, v_xs_5094_, v_sz_5096_, v___x_5097_, v_groups_5095_);
return v___x_5098_;
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0___redArg___boxed(lean_object* v_key_5099_, lean_object* v_xs_5100_){
_start:
{
lean_object* v_res_5101_; 
v_res_5101_ = l_Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0___redArg(v_key_5099_, v_xs_5100_);
lean_dec_ref(v_xs_5100_);
return v_res_5101_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__9___redArg___lam__0(lean_object* v_x_5102_, lean_object* v_x_5103_){
_start:
{
lean_object* v_fst_5104_; lean_object* v_fst_5105_; uint64_t v___x_5106_; uint64_t v___x_5107_; uint8_t v___x_5108_; 
v_fst_5104_ = lean_ctor_get(v_x_5102_, 0);
v_fst_5105_ = lean_ctor_get(v_x_5103_, 0);
v___x_5106_ = lean_unbox_uint64(v_fst_5104_);
v___x_5107_ = lean_unbox_uint64(v_fst_5105_);
v___x_5108_ = lean_uint64_dec_lt(v___x_5106_, v___x_5107_);
return v___x_5108_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__9___redArg___lam__0___boxed(lean_object* v_x_5109_, lean_object* v_x_5110_){
_start:
{
uint8_t v_res_5111_; lean_object* v_r_5112_; 
v_res_5111_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__9___redArg___lam__0(v_x_5109_, v_x_5110_);
lean_dec_ref(v_x_5110_);
lean_dec_ref(v_x_5109_);
v_r_5112_ = lean_box(v_res_5111_);
return v_r_5112_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__9_spec__12___redArg(lean_object* v_hi_5113_, lean_object* v_pivot_5114_, lean_object* v_as_5115_, lean_object* v_i_5116_, lean_object* v_k_5117_){
_start:
{
uint8_t v___x_5118_; 
v___x_5118_ = lean_nat_dec_lt(v_k_5117_, v_hi_5113_);
if (v___x_5118_ == 0)
{
lean_object* v___x_5119_; lean_object* v___x_5120_; 
lean_dec(v_k_5117_);
v___x_5119_ = lean_array_fswap(v_as_5115_, v_i_5116_, v_hi_5113_);
v___x_5120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5120_, 0, v_i_5116_);
lean_ctor_set(v___x_5120_, 1, v___x_5119_);
return v___x_5120_;
}
else
{
lean_object* v___x_5121_; lean_object* v_fst_5122_; lean_object* v_fst_5123_; uint64_t v___x_5124_; uint64_t v___x_5125_; uint8_t v___x_5126_; 
v___x_5121_ = lean_array_fget_borrowed(v_as_5115_, v_k_5117_);
v_fst_5122_ = lean_ctor_get(v___x_5121_, 0);
v_fst_5123_ = lean_ctor_get(v_pivot_5114_, 0);
v___x_5124_ = lean_unbox_uint64(v_fst_5122_);
v___x_5125_ = lean_unbox_uint64(v_fst_5123_);
v___x_5126_ = lean_uint64_dec_lt(v___x_5124_, v___x_5125_);
if (v___x_5126_ == 0)
{
lean_object* v___x_5127_; lean_object* v___x_5128_; 
v___x_5127_ = lean_unsigned_to_nat(1u);
v___x_5128_ = lean_nat_add(v_k_5117_, v___x_5127_);
lean_dec(v_k_5117_);
v_k_5117_ = v___x_5128_;
goto _start;
}
else
{
lean_object* v___x_5130_; lean_object* v___x_5131_; lean_object* v___x_5132_; lean_object* v___x_5133_; 
v___x_5130_ = lean_array_fswap(v_as_5115_, v_i_5116_, v_k_5117_);
v___x_5131_ = lean_unsigned_to_nat(1u);
v___x_5132_ = lean_nat_add(v_i_5116_, v___x_5131_);
lean_dec(v_i_5116_);
v___x_5133_ = lean_nat_add(v_k_5117_, v___x_5131_);
lean_dec(v_k_5117_);
v_as_5115_ = v___x_5130_;
v_i_5116_ = v___x_5132_;
v_k_5117_ = v___x_5133_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__9_spec__12___redArg___boxed(lean_object* v_hi_5135_, lean_object* v_pivot_5136_, lean_object* v_as_5137_, lean_object* v_i_5138_, lean_object* v_k_5139_){
_start:
{
lean_object* v_res_5140_; 
v_res_5140_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__9_spec__12___redArg(v_hi_5135_, v_pivot_5136_, v_as_5137_, v_i_5138_, v_k_5139_);
lean_dec_ref(v_pivot_5136_);
lean_dec(v_hi_5135_);
return v_res_5140_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__9___redArg(lean_object* v_n_5141_, lean_object* v_as_5142_, lean_object* v_lo_5143_, lean_object* v_hi_5144_){
_start:
{
lean_object* v___y_5146_; uint8_t v___x_5156_; 
v___x_5156_ = lean_nat_dec_lt(v_lo_5143_, v_hi_5144_);
if (v___x_5156_ == 0)
{
lean_dec(v_lo_5143_);
return v_as_5142_;
}
else
{
lean_object* v___x_5157_; lean_object* v___x_5158_; lean_object* v_mid_5159_; lean_object* v___y_5161_; lean_object* v___y_5167_; lean_object* v___x_5172_; lean_object* v___x_5173_; uint8_t v___x_5174_; 
v___x_5157_ = lean_nat_add(v_lo_5143_, v_hi_5144_);
v___x_5158_ = lean_unsigned_to_nat(1u);
v_mid_5159_ = lean_nat_shiftr(v___x_5157_, v___x_5158_);
lean_dec(v___x_5157_);
v___x_5172_ = lean_array_fget_borrowed(v_as_5142_, v_mid_5159_);
v___x_5173_ = lean_array_fget_borrowed(v_as_5142_, v_lo_5143_);
v___x_5174_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__9___redArg___lam__0(v___x_5172_, v___x_5173_);
if (v___x_5174_ == 0)
{
v___y_5167_ = v_as_5142_;
goto v___jp_5166_;
}
else
{
lean_object* v___x_5175_; 
v___x_5175_ = lean_array_fswap(v_as_5142_, v_lo_5143_, v_mid_5159_);
v___y_5167_ = v___x_5175_;
goto v___jp_5166_;
}
v___jp_5160_:
{
lean_object* v___x_5162_; lean_object* v___x_5163_; uint8_t v___x_5164_; 
v___x_5162_ = lean_array_fget_borrowed(v___y_5161_, v_mid_5159_);
v___x_5163_ = lean_array_fget_borrowed(v___y_5161_, v_hi_5144_);
v___x_5164_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__9___redArg___lam__0(v___x_5162_, v___x_5163_);
if (v___x_5164_ == 0)
{
lean_dec(v_mid_5159_);
v___y_5146_ = v___y_5161_;
goto v___jp_5145_;
}
else
{
lean_object* v___x_5165_; 
v___x_5165_ = lean_array_fswap(v___y_5161_, v_mid_5159_, v_hi_5144_);
lean_dec(v_mid_5159_);
v___y_5146_ = v___x_5165_;
goto v___jp_5145_;
}
}
v___jp_5166_:
{
lean_object* v___x_5168_; lean_object* v___x_5169_; uint8_t v___x_5170_; 
v___x_5168_ = lean_array_fget_borrowed(v___y_5167_, v_hi_5144_);
v___x_5169_ = lean_array_fget_borrowed(v___y_5167_, v_lo_5143_);
v___x_5170_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__9___redArg___lam__0(v___x_5168_, v___x_5169_);
if (v___x_5170_ == 0)
{
v___y_5161_ = v___y_5167_;
goto v___jp_5160_;
}
else
{
lean_object* v___x_5171_; 
v___x_5171_ = lean_array_fswap(v___y_5167_, v_lo_5143_, v_hi_5144_);
v___y_5161_ = v___x_5171_;
goto v___jp_5160_;
}
}
}
v___jp_5145_:
{
lean_object* v_pivot_5147_; lean_object* v___x_5148_; lean_object* v_fst_5149_; lean_object* v_snd_5150_; uint8_t v___x_5151_; 
v_pivot_5147_ = lean_array_fget(v___y_5146_, v_hi_5144_);
lean_inc_n(v_lo_5143_, 2);
v___x_5148_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__9_spec__12___redArg(v_hi_5144_, v_pivot_5147_, v___y_5146_, v_lo_5143_, v_lo_5143_);
lean_dec(v_pivot_5147_);
v_fst_5149_ = lean_ctor_get(v___x_5148_, 0);
lean_inc(v_fst_5149_);
v_snd_5150_ = lean_ctor_get(v___x_5148_, 1);
lean_inc(v_snd_5150_);
lean_dec_ref(v___x_5148_);
v___x_5151_ = lean_nat_dec_le(v_hi_5144_, v_fst_5149_);
if (v___x_5151_ == 0)
{
lean_object* v___x_5152_; lean_object* v___x_5153_; lean_object* v___x_5154_; 
v___x_5152_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__9___redArg(v_n_5141_, v_snd_5150_, v_lo_5143_, v_fst_5149_);
v___x_5153_ = lean_unsigned_to_nat(1u);
v___x_5154_ = lean_nat_add(v_fst_5149_, v___x_5153_);
lean_dec(v_fst_5149_);
v_as_5142_ = v___x_5152_;
v_lo_5143_ = v___x_5154_;
goto _start;
}
else
{
lean_dec(v_fst_5149_);
lean_dec(v_lo_5143_);
return v_snd_5150_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__9___redArg___boxed(lean_object* v_n_5176_, lean_object* v_as_5177_, lean_object* v_lo_5178_, lean_object* v_hi_5179_){
_start:
{
lean_object* v_res_5180_; 
v_res_5180_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__9___redArg(v_n_5176_, v_as_5177_, v_lo_5178_, v_hi_5179_);
lean_dec(v_hi_5179_);
lean_dec(v_n_5176_);
return v_res_5180_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Firefox_Profile_export_spec__10(lean_object* v_x_5181_, lean_object* v_x_5182_){
_start:
{
if (lean_obj_tag(v_x_5182_) == 0)
{
return v_x_5181_;
}
else
{
lean_object* v_key_5183_; lean_object* v_value_5184_; lean_object* v_tail_5185_; lean_object* v___x_5186_; lean_object* v___x_5187_; 
v_key_5183_ = lean_ctor_get(v_x_5182_, 0);
v_value_5184_ = lean_ctor_get(v_x_5182_, 1);
v_tail_5185_ = lean_ctor_get(v_x_5182_, 2);
lean_inc(v_value_5184_);
lean_inc(v_key_5183_);
v___x_5186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5186_, 0, v_key_5183_);
lean_ctor_set(v___x_5186_, 1, v_value_5184_);
v___x_5187_ = lean_array_push(v_x_5181_, v___x_5186_);
v_x_5181_ = v___x_5187_;
v_x_5182_ = v_tail_5185_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Firefox_Profile_export_spec__10___boxed(lean_object* v_x_5189_, lean_object* v_x_5190_){
_start:
{
lean_object* v_res_5191_; 
v_res_5191_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Firefox_Profile_export_spec__10(v_x_5189_, v_x_5190_);
lean_dec(v_x_5190_);
return v_res_5191_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Firefox_Profile_export_spec__11(lean_object* v_as_5192_, size_t v_i_5193_, size_t v_stop_5194_, lean_object* v_b_5195_){
_start:
{
uint8_t v___x_5196_; 
v___x_5196_ = lean_usize_dec_eq(v_i_5193_, v_stop_5194_);
if (v___x_5196_ == 0)
{
lean_object* v___x_5197_; lean_object* v___x_5198_; size_t v___x_5199_; size_t v___x_5200_; 
v___x_5197_ = lean_array_uget_borrowed(v_as_5192_, v_i_5193_);
v___x_5198_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Firefox_Profile_export_spec__10(v_b_5195_, v___x_5197_);
v___x_5199_ = ((size_t)1ULL);
v___x_5200_ = lean_usize_add(v_i_5193_, v___x_5199_);
v_i_5193_ = v___x_5200_;
v_b_5195_ = v___x_5198_;
goto _start;
}
else
{
return v_b_5195_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Firefox_Profile_export_spec__11___boxed(lean_object* v_as_5202_, lean_object* v_i_5203_, lean_object* v_stop_5204_, lean_object* v_b_5205_){
_start:
{
size_t v_i_boxed_5206_; size_t v_stop_boxed_5207_; lean_object* v_res_5208_; 
v_i_boxed_5206_ = lean_unbox_usize(v_i_5203_);
lean_dec(v_i_5203_);
v_stop_boxed_5207_ = lean_unbox_usize(v_stop_5204_);
lean_dec(v_stop_5204_);
v_res_5208_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Firefox_Profile_export_spec__11(v_as_5202_, v_i_boxed_5206_, v_stop_boxed_5207_, v_b_5205_);
lean_dec_ref(v_as_5202_);
return v_res_5208_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__8(size_t v_sz_5209_, size_t v_i_5210_, lean_object* v_bs_5211_){
_start:
{
uint8_t v___x_5212_; 
v___x_5212_ = lean_usize_dec_lt(v_i_5210_, v_sz_5209_);
if (v___x_5212_ == 0)
{
return v_bs_5211_;
}
else
{
lean_object* v_v_5213_; lean_object* v_toThread_5214_; lean_object* v___x_5215_; lean_object* v_bs_x27_5216_; size_t v___x_5217_; size_t v___x_5218_; lean_object* v___x_5219_; 
v_v_5213_ = lean_array_uget_borrowed(v_bs_5211_, v_i_5210_);
v_toThread_5214_ = lean_ctor_get(v_v_5213_, 0);
lean_inc_ref(v_toThread_5214_);
v___x_5215_ = lean_unsigned_to_nat(0u);
v_bs_x27_5216_ = lean_array_uset(v_bs_5211_, v_i_5210_, v___x_5215_);
v___x_5217_ = ((size_t)1ULL);
v___x_5218_ = lean_usize_add(v_i_5210_, v___x_5217_);
v___x_5219_ = lean_array_uset(v_bs_x27_5216_, v_i_5210_, v_toThread_5214_);
v_i_5210_ = v___x_5218_;
v_bs_5211_ = v___x_5219_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__8___boxed(lean_object* v_sz_5221_, lean_object* v_i_5222_, lean_object* v_bs_5223_){
_start:
{
size_t v_sz_boxed_5224_; size_t v_i_boxed_5225_; lean_object* v_res_5226_; 
v_sz_boxed_5224_ = lean_unbox_usize(v_sz_5221_);
lean_dec(v_sz_5221_);
v_i_boxed_5225_ = lean_unbox_usize(v_i_5222_);
lean_dec(v_i_5222_);
v_res_5226_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__8(v_sz_boxed_5224_, v_i_boxed_5225_, v_bs_5223_);
return v_res_5226_;
}
}
static double _init_l_Lean_Firefox_Profile_export___closed__1(void){
_start:
{
lean_object* v___x_5228_; double v___x_5229_; 
v___x_5228_ = lean_unsigned_to_nat(1000000000u);
v___x_5229_ = lean_float_of_nat(v___x_5228_);
return v___x_5229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Firefox_Profile_export(lean_object* v_name_5236_, double v_startTime_5237_, lean_object* v_traceStates_5238_, lean_object* v_opts_5239_){
_start:
{
lean_object* v___f_5241_; lean_object* v_tids_5242_; lean_object* v___x_5243_; lean_object* v_size_5244_; lean_object* v_buckets_5245_; double v___x_5246_; double v___x_5247_; double v___x_5248_; lean_object* v___y_5250_; lean_object* v___y_5251_; lean_object* v___y_5252_; lean_object* v___y_5286_; lean_object* v___y_5287_; lean_object* v___y_5288_; lean_object* v___y_5289_; lean_object* v___y_5290_; lean_object* v___y_5291_; lean_object* v___y_5294_; lean_object* v___y_5295_; lean_object* v___y_5296_; lean_object* v___y_5297_; lean_object* v___y_5298_; lean_object* v___y_5299_; lean_object* v___y_5302_; lean_object* v___x_5309_; lean_object* v___x_5310_; lean_object* v___x_5311_; uint8_t v___x_5312_; 
v___f_5241_ = ((lean_object*)(l_Lean_Firefox_Profile_export___closed__0));
v_tids_5242_ = l_Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0___redArg(v___f_5241_, v_traceStates_5238_);
v___x_5243_ = lean_io_mono_nanos_now();
v_size_5244_ = lean_ctor_get(v_tids_5242_, 0);
lean_inc(v_size_5244_);
v_buckets_5245_ = lean_ctor_get(v_tids_5242_, 1);
lean_inc_ref(v_buckets_5245_);
lean_dec_ref(v_tids_5242_);
v___x_5246_ = lean_float_of_nat(v___x_5243_);
v___x_5247_ = lean_float_once(&l_Lean_Firefox_Profile_export___closed__1, &l_Lean_Firefox_Profile_export___closed__1_once, _init_l_Lean_Firefox_Profile_export___closed__1);
v___x_5248_ = lean_float_div(v___x_5246_, v___x_5247_);
v___x_5309_ = lean_mk_empty_array_with_capacity(v_size_5244_);
lean_dec(v_size_5244_);
v___x_5310_ = lean_unsigned_to_nat(0u);
v___x_5311_ = lean_array_get_size(v_buckets_5245_);
v___x_5312_ = lean_nat_dec_lt(v___x_5310_, v___x_5311_);
if (v___x_5312_ == 0)
{
lean_dec_ref(v_buckets_5245_);
v___y_5302_ = v___x_5309_;
goto v___jp_5301_;
}
else
{
size_t v___x_5313_; size_t v___x_5314_; lean_object* v___x_5315_; 
v___x_5313_ = ((size_t)0ULL);
v___x_5314_ = lean_usize_of_nat(v___x_5311_);
v___x_5315_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Firefox_Profile_export_spec__11(v_buckets_5245_, v___x_5313_, v___x_5314_, v___x_5309_);
lean_dec_ref(v_buckets_5245_);
v___y_5302_ = v___x_5315_;
goto v___jp_5301_;
}
v___jp_5249_:
{
size_t v_sz_5253_; size_t v___x_5254_; lean_object* v___x_5255_; 
v_sz_5253_ = lean_array_size(v___y_5252_);
v___x_5254_ = ((size_t)0ULL);
v___x_5255_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__7(v_opts_5239_, v_startTime_5237_, v___x_5248_, v_name_5236_, v_sz_5253_, v___x_5254_, v___y_5252_);
if (lean_obj_tag(v___x_5255_) == 0)
{
lean_object* v_a_5256_; lean_object* v___x_5258_; uint8_t v_isShared_5259_; uint8_t v_isSharedCheck_5276_; 
v_a_5256_ = lean_ctor_get(v___x_5255_, 0);
v_isSharedCheck_5276_ = !lean_is_exclusive(v___x_5255_);
if (v_isSharedCheck_5276_ == 0)
{
v___x_5258_ = v___x_5255_;
v_isShared_5259_ = v_isSharedCheck_5276_;
goto v_resetjp_5257_;
}
else
{
lean_inc(v_a_5256_);
lean_dec(v___x_5255_);
v___x_5258_ = lean_box(0);
v_isShared_5259_ = v_isSharedCheck_5276_;
goto v_resetjp_5257_;
}
v_resetjp_5257_:
{
uint8_t v___x_5260_; double v___x_5261_; double v___x_5262_; double v___x_5263_; lean_object* v___x_5264_; lean_object* v___x_5265_; lean_object* v___x_5266_; lean_object* v___x_5267_; lean_object* v___x_5268_; lean_object* v___x_5269_; size_t v_sz_5270_; lean_object* v___x_5271_; lean_object* v___x_5272_; lean_object* v___x_5274_; 
v___x_5260_ = 1;
lean_inc(v___y_5251_);
v___x_5261_ = l_Float_ofScientific(v___y_5251_, v___x_5260_, v___y_5250_);
v___x_5262_ = lean_float_once(&l_Lean_Firefox_instCoeFloatMilliseconds___lam__0___closed__0, &l_Lean_Firefox_instCoeFloatMilliseconds___lam__0___closed__0_once, _init_l_Lean_Firefox_instCoeFloatMilliseconds___lam__0___closed__0);
v___x_5263_ = lean_float_mul(v_startTime_5237_, v___x_5262_);
v___x_5264_ = ((lean_object*)(l_Lean_Firefox_categories));
v___x_5265_ = ((lean_object*)(l_Lean_Firefox_Profile_export___closed__2));
v___x_5266_ = lean_unsigned_to_nat(48u);
v___x_5267_ = lean_mk_empty_array_with_capacity(v___y_5251_);
v___x_5268_ = ((lean_object*)(l_Lean_Firefox_Profile_export___closed__5));
lean_inc_ref(v___x_5267_);
v___x_5269_ = lean_alloc_ctor(0, 6, 16);
lean_ctor_set(v___x_5269_, 0, v___x_5264_);
lean_ctor_set(v___x_5269_, 1, v___y_5251_);
lean_ctor_set(v___x_5269_, 2, v___x_5265_);
lean_ctor_set(v___x_5269_, 3, v___x_5266_);
lean_ctor_set(v___x_5269_, 4, v___x_5267_);
lean_ctor_set(v___x_5269_, 5, v___x_5268_);
lean_ctor_set_float(v___x_5269_, sizeof(void*)*6, v___x_5261_);
lean_ctor_set_float(v___x_5269_, sizeof(void*)*6 + 8, v___x_5263_);
v_sz_5270_ = lean_array_size(v_a_5256_);
v___x_5271_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__8(v_sz_5270_, v___x_5254_, v_a_5256_);
v___x_5272_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5272_, 0, v___x_5269_);
lean_ctor_set(v___x_5272_, 1, v___x_5267_);
lean_ctor_set(v___x_5272_, 2, v___x_5271_);
if (v_isShared_5259_ == 0)
{
lean_ctor_set(v___x_5258_, 0, v___x_5272_);
v___x_5274_ = v___x_5258_;
goto v_reusejp_5273_;
}
else
{
lean_object* v_reuseFailAlloc_5275_; 
v_reuseFailAlloc_5275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5275_, 0, v___x_5272_);
v___x_5274_ = v_reuseFailAlloc_5275_;
goto v_reusejp_5273_;
}
v_reusejp_5273_:
{
return v___x_5274_;
}
}
}
else
{
lean_object* v_a_5277_; lean_object* v___x_5279_; uint8_t v_isShared_5280_; uint8_t v_isSharedCheck_5284_; 
lean_dec(v___y_5251_);
lean_dec(v___y_5250_);
v_a_5277_ = lean_ctor_get(v___x_5255_, 0);
v_isSharedCheck_5284_ = !lean_is_exclusive(v___x_5255_);
if (v_isSharedCheck_5284_ == 0)
{
v___x_5279_ = v___x_5255_;
v_isShared_5280_ = v_isSharedCheck_5284_;
goto v_resetjp_5278_;
}
else
{
lean_inc(v_a_5277_);
lean_dec(v___x_5255_);
v___x_5279_ = lean_box(0);
v_isShared_5280_ = v_isSharedCheck_5284_;
goto v_resetjp_5278_;
}
v_resetjp_5278_:
{
lean_object* v___x_5282_; 
if (v_isShared_5280_ == 0)
{
v___x_5282_ = v___x_5279_;
goto v_reusejp_5281_;
}
else
{
lean_object* v_reuseFailAlloc_5283_; 
v_reuseFailAlloc_5283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5283_, 0, v_a_5277_);
v___x_5282_ = v_reuseFailAlloc_5283_;
goto v_reusejp_5281_;
}
v_reusejp_5281_:
{
return v___x_5282_;
}
}
}
}
v___jp_5285_:
{
lean_object* v___x_5292_; 
v___x_5292_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__9___redArg(v___y_5286_, v___y_5290_, v___y_5287_, v___y_5291_);
lean_dec(v___y_5291_);
lean_dec(v___y_5286_);
v___y_5250_ = v___y_5288_;
v___y_5251_ = v___y_5289_;
v___y_5252_ = v___x_5292_;
goto v___jp_5249_;
}
v___jp_5293_:
{
uint8_t v___x_5300_; 
v___x_5300_ = lean_nat_dec_le(v___y_5299_, v___y_5295_);
if (v___x_5300_ == 0)
{
lean_dec(v___y_5295_);
lean_inc(v___y_5299_);
v___y_5286_ = v___y_5294_;
v___y_5287_ = v___y_5299_;
v___y_5288_ = v___y_5296_;
v___y_5289_ = v___y_5297_;
v___y_5290_ = v___y_5298_;
v___y_5291_ = v___y_5299_;
goto v___jp_5285_;
}
else
{
v___y_5286_ = v___y_5294_;
v___y_5287_ = v___y_5299_;
v___y_5288_ = v___y_5296_;
v___y_5289_ = v___y_5297_;
v___y_5290_ = v___y_5298_;
v___y_5291_ = v___y_5295_;
goto v___jp_5285_;
}
}
v___jp_5301_:
{
lean_object* v___x_5303_; lean_object* v___x_5304_; lean_object* v___x_5305_; uint8_t v___x_5306_; 
v___x_5303_ = lean_unsigned_to_nat(0u);
v___x_5304_ = lean_unsigned_to_nat(1u);
v___x_5305_ = lean_array_get_size(v___y_5302_);
v___x_5306_ = lean_nat_dec_eq(v___x_5305_, v___x_5303_);
if (v___x_5306_ == 0)
{
lean_object* v___x_5307_; uint8_t v___x_5308_; 
v___x_5307_ = lean_nat_sub(v___x_5305_, v___x_5304_);
v___x_5308_ = lean_nat_dec_le(v___x_5303_, v___x_5307_);
if (v___x_5308_ == 0)
{
lean_inc(v___x_5307_);
v___y_5294_ = v___x_5305_;
v___y_5295_ = v___x_5307_;
v___y_5296_ = v___x_5304_;
v___y_5297_ = v___x_5303_;
v___y_5298_ = v___y_5302_;
v___y_5299_ = v___x_5307_;
goto v___jp_5293_;
}
else
{
v___y_5294_ = v___x_5305_;
v___y_5295_ = v___x_5307_;
v___y_5296_ = v___x_5304_;
v___y_5297_ = v___x_5303_;
v___y_5298_ = v___y_5302_;
v___y_5299_ = v___x_5303_;
goto v___jp_5293_;
}
}
else
{
v___y_5250_ = v___x_5304_;
v___y_5251_ = v___x_5303_;
v___y_5252_ = v___y_5302_;
goto v___jp_5249_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Firefox_Profile_export___boxed(lean_object* v_name_5316_, lean_object* v_startTime_5317_, lean_object* v_traceStates_5318_, lean_object* v_opts_5319_, lean_object* v_a_5320_){
_start:
{
double v_startTime_boxed_5321_; lean_object* v_res_5322_; 
v_startTime_boxed_5321_ = lean_unbox_float(v_startTime_5317_);
lean_dec_ref(v_startTime_5317_);
v_res_5322_ = l_Lean_Firefox_Profile_export(v_name_5316_, v_startTime_boxed_5321_, v_traceStates_5318_, v_opts_5319_);
lean_dec_ref(v_opts_5319_);
lean_dec_ref(v_traceStates_5318_);
return v_res_5322_;
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0(lean_object* v_00_u03b2_5323_, lean_object* v_key_5324_, lean_object* v_xs_5325_){
_start:
{
lean_object* v___x_5326_; 
v___x_5326_ = l_Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0___redArg(v_key_5324_, v_xs_5325_);
return v___x_5326_;
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0___boxed(lean_object* v_00_u03b2_5327_, lean_object* v_key_5328_, lean_object* v_xs_5329_){
_start:
{
lean_object* v_res_5330_; 
v_res_5330_ = l_Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0(v_00_u03b2_5327_, v_key_5328_, v_xs_5329_);
lean_dec_ref(v_xs_5329_);
return v_res_5330_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__6(lean_object* v_n_5331_, lean_object* v_as_5332_, lean_object* v_lo_5333_, lean_object* v_hi_5334_, lean_object* v_w_5335_, lean_object* v_hlo_5336_, lean_object* v_hhi_5337_){
_start:
{
lean_object* v___x_5338_; 
v___x_5338_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__6___redArg(v_n_5331_, v_as_5332_, v_lo_5333_, v_hi_5334_);
return v___x_5338_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__6___boxed(lean_object* v_n_5339_, lean_object* v_as_5340_, lean_object* v_lo_5341_, lean_object* v_hi_5342_, lean_object* v_w_5343_, lean_object* v_hlo_5344_, lean_object* v_hhi_5345_){
_start:
{
lean_object* v_res_5346_; 
v_res_5346_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__6(v_n_5339_, v_as_5340_, v_lo_5341_, v_hi_5342_, v_w_5343_, v_hlo_5344_, v_hhi_5345_);
lean_dec(v_hi_5342_);
lean_dec(v_n_5339_);
return v_res_5346_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__9(lean_object* v_n_5347_, lean_object* v_as_5348_, lean_object* v_lo_5349_, lean_object* v_hi_5350_, lean_object* v_w_5351_, lean_object* v_hlo_5352_, lean_object* v_hhi_5353_){
_start:
{
lean_object* v___x_5354_; 
v___x_5354_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__9___redArg(v_n_5347_, v_as_5348_, v_lo_5349_, v_hi_5350_);
return v___x_5354_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__9___boxed(lean_object* v_n_5355_, lean_object* v_as_5356_, lean_object* v_lo_5357_, lean_object* v_hi_5358_, lean_object* v_w_5359_, lean_object* v_hlo_5360_, lean_object* v_hhi_5361_){
_start:
{
lean_object* v_res_5362_; 
v_res_5362_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__9(v_n_5355_, v_as_5356_, v_lo_5357_, v_hi_5358_, v_w_5359_, v_hlo_5360_, v_hhi_5361_);
lean_dec(v_hi_5358_);
lean_dec(v_n_5355_);
return v_res_5362_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0(lean_object* v_00_u03b2_5363_, lean_object* v_a_5364_, lean_object* v_m_5365_, uint64_t v_a_5366_){
_start:
{
lean_object* v___x_5367_; 
v___x_5367_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0___redArg(v_a_5364_, v_m_5365_, v_a_5366_);
return v___x_5367_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0___boxed(lean_object* v_00_u03b2_5368_, lean_object* v_a_5369_, lean_object* v_m_5370_, lean_object* v_a_5371_){
_start:
{
uint64_t v_a_boxed_5372_; lean_object* v_res_5373_; 
v_a_boxed_5372_ = lean_unbox_uint64(v_a_5371_);
lean_dec_ref(v_a_5371_);
v_res_5373_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0(v_00_u03b2_5368_, v_a_5369_, v_m_5370_, v_a_boxed_5372_);
return v_res_5373_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__1(lean_object* v_00_u03b2_5374_, lean_object* v_key_5375_, lean_object* v_as_5376_, size_t v_sz_5377_, size_t v_i_5378_, lean_object* v_b_5379_){
_start:
{
lean_object* v___x_5380_; 
v___x_5380_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__1___redArg(v_key_5375_, v_as_5376_, v_sz_5377_, v_i_5378_, v_b_5379_);
return v___x_5380_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__1___boxed(lean_object* v_00_u03b2_5381_, lean_object* v_key_5382_, lean_object* v_as_5383_, lean_object* v_sz_5384_, lean_object* v_i_5385_, lean_object* v_b_5386_){
_start:
{
size_t v_sz_boxed_5387_; size_t v_i_boxed_5388_; lean_object* v_res_5389_; 
v_sz_boxed_5387_ = lean_unbox_usize(v_sz_5384_);
lean_dec(v_sz_5384_);
v_i_boxed_5388_ = lean_unbox_usize(v_i_5385_);
lean_dec(v_i_5385_);
v_res_5389_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__1(v_00_u03b2_5381_, v_key_5382_, v_as_5383_, v_sz_boxed_5387_, v_i_boxed_5388_, v_b_5386_);
lean_dec_ref(v_as_5383_);
return v_res_5389_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__6_spec__8(lean_object* v_n_5390_, lean_object* v_lo_5391_, lean_object* v_hi_5392_, lean_object* v_hhi_5393_, lean_object* v_pivot_5394_, lean_object* v_as_5395_, lean_object* v_i_5396_, lean_object* v_k_5397_, lean_object* v_ilo_5398_, lean_object* v_ik_5399_, lean_object* v_w_5400_){
_start:
{
lean_object* v___x_5401_; 
v___x_5401_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__6_spec__8___redArg(v_hi_5392_, v_pivot_5394_, v_as_5395_, v_i_5396_, v_k_5397_);
return v___x_5401_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__6_spec__8___boxed(lean_object* v_n_5402_, lean_object* v_lo_5403_, lean_object* v_hi_5404_, lean_object* v_hhi_5405_, lean_object* v_pivot_5406_, lean_object* v_as_5407_, lean_object* v_i_5408_, lean_object* v_k_5409_, lean_object* v_ilo_5410_, lean_object* v_ik_5411_, lean_object* v_w_5412_){
_start:
{
lean_object* v_res_5413_; 
v_res_5413_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__6_spec__8(v_n_5402_, v_lo_5403_, v_hi_5404_, v_hhi_5405_, v_pivot_5406_, v_as_5407_, v_i_5408_, v_k_5409_, v_ilo_5410_, v_ik_5411_, v_w_5412_);
lean_dec_ref(v_pivot_5406_);
lean_dec(v_hi_5404_);
lean_dec(v_lo_5403_);
lean_dec(v_n_5402_);
return v_res_5413_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__9_spec__12(lean_object* v_n_5414_, lean_object* v_lo_5415_, lean_object* v_hi_5416_, lean_object* v_hhi_5417_, lean_object* v_pivot_5418_, lean_object* v_as_5419_, lean_object* v_i_5420_, lean_object* v_k_5421_, lean_object* v_ilo_5422_, lean_object* v_ik_5423_, lean_object* v_w_5424_){
_start:
{
lean_object* v___x_5425_; 
v___x_5425_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__9_spec__12___redArg(v_hi_5416_, v_pivot_5418_, v_as_5419_, v_i_5420_, v_k_5421_);
return v___x_5425_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__9_spec__12___boxed(lean_object* v_n_5426_, lean_object* v_lo_5427_, lean_object* v_hi_5428_, lean_object* v_hhi_5429_, lean_object* v_pivot_5430_, lean_object* v_as_5431_, lean_object* v_i_5432_, lean_object* v_k_5433_, lean_object* v_ilo_5434_, lean_object* v_ik_5435_, lean_object* v_w_5436_){
_start:
{
lean_object* v_res_5437_; 
v_res_5437_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Firefox_Profile_export_spec__9_spec__12(v_n_5426_, v_lo_5427_, v_hi_5428_, v_hhi_5429_, v_pivot_5430_, v_as_5431_, v_i_5432_, v_k_5433_, v_ilo_5434_, v_ik_5435_, v_w_5436_);
lean_dec_ref(v_pivot_5430_);
lean_dec(v_hi_5428_);
lean_dec(v_lo_5427_);
lean_dec(v_n_5426_);
return v_res_5437_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_5438_, uint64_t v_a_5439_, lean_object* v_x_5440_){
_start:
{
uint8_t v___x_5441_; 
v___x_5441_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__2___redArg(v_a_5439_, v_x_5440_);
return v___x_5441_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_5442_, lean_object* v_a_5443_, lean_object* v_x_5444_){
_start:
{
uint64_t v_a_boxed_5445_; uint8_t v_res_5446_; lean_object* v_r_5447_; 
v_a_boxed_5445_ = lean_unbox_uint64(v_a_5443_);
lean_dec_ref(v_a_5443_);
v_res_5446_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__2(v_00_u03b2_5442_, v_a_boxed_5445_, v_x_5444_);
lean_dec(v_x_5444_);
v_r_5447_ = lean_box(v_res_5446_);
return v_r_5447_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_5448_, lean_object* v_data_5449_){
_start:
{
lean_object* v___x_5450_; 
v___x_5450_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__3___redArg(v_data_5449_);
return v___x_5450_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__4(lean_object* v_00_u03b2_5451_, lean_object* v_a_5452_, uint64_t v_a_5453_, lean_object* v_x_5454_){
_start:
{
lean_object* v___x_5455_; 
v___x_5455_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__4___redArg(v_a_5452_, v_a_5453_, v_x_5454_);
return v___x_5455_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__4___boxed(lean_object* v_00_u03b2_5456_, lean_object* v_a_5457_, lean_object* v_a_5458_, lean_object* v_x_5459_){
_start:
{
uint64_t v_a_boxed_5460_; lean_object* v_res_5461_; 
v_a_boxed_5460_ = lean_unbox_uint64(v_a_5458_);
lean_dec_ref(v_a_5458_);
v_res_5461_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__4(v_00_u03b2_5456_, v_a_5457_, v_a_boxed_5460_, v_x_5459_);
return v_res_5461_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__3_spec__14(lean_object* v_00_u03b2_5462_, lean_object* v_i_5463_, lean_object* v_source_5464_, lean_object* v_target_5465_){
_start:
{
lean_object* v___x_5466_; 
v___x_5466_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__3_spec__14___redArg(v_i_5463_, v_source_5464_, v_target_5465_);
return v___x_5466_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__3_spec__14_spec__18(lean_object* v_00_u03b2_5467_, lean_object* v_x_5468_, lean_object* v_x_5469_){
_start:
{
lean_object* v___x_5470_; 
v___x_5470_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00Lean_Firefox_Profile_export_spec__0_spec__0_spec__3_spec__14_spec__18___redArg(v_x_5468_, v_x_5469_);
return v___x_5470_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Profiler_0__Lean_Firefox_collideThreads_getStrIdx(lean_object* v_s_5471_, lean_object* v_a_5472_){
_start:
{
lean_object* v_toThreadWithMaps_5473_; lean_object* v_sampleMap_5474_; lean_object* v_toThread_5475_; lean_object* v_stringMap_5476_; lean_object* v_funcMap_5477_; lean_object* v_stackMap_5478_; double v_lastTime_5479_; lean_object* v___x_5481_; uint8_t v_isShared_5482_; uint8_t v_isSharedCheck_5520_; 
v_toThreadWithMaps_5473_ = lean_ctor_get(v_a_5472_, 0);
lean_inc_ref(v_toThreadWithMaps_5473_);
v_sampleMap_5474_ = lean_ctor_get(v_a_5472_, 1);
v_toThread_5475_ = lean_ctor_get(v_toThreadWithMaps_5473_, 0);
v_stringMap_5476_ = lean_ctor_get(v_toThreadWithMaps_5473_, 1);
v_funcMap_5477_ = lean_ctor_get(v_toThreadWithMaps_5473_, 2);
v_stackMap_5478_ = lean_ctor_get(v_toThreadWithMaps_5473_, 3);
v_lastTime_5479_ = lean_ctor_get_float(v_toThreadWithMaps_5473_, sizeof(void*)*4);
v_isSharedCheck_5520_ = !lean_is_exclusive(v_toThreadWithMaps_5473_);
if (v_isSharedCheck_5520_ == 0)
{
v___x_5481_ = v_toThreadWithMaps_5473_;
v_isShared_5482_ = v_isSharedCheck_5520_;
goto v_resetjp_5480_;
}
else
{
lean_inc(v_stackMap_5478_);
lean_inc(v_funcMap_5477_);
lean_inc(v_stringMap_5476_);
lean_inc(v_toThread_5475_);
lean_dec(v_toThreadWithMaps_5473_);
v___x_5481_ = lean_box(0);
v_isShared_5482_ = v_isSharedCheck_5520_;
goto v_resetjp_5480_;
}
v_resetjp_5480_:
{
lean_object* v___x_5483_; 
v___x_5483_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__6___redArg(v_stringMap_5476_, v_s_5471_);
if (lean_obj_tag(v___x_5483_) == 1)
{
lean_object* v_val_5484_; lean_object* v___x_5485_; 
lean_del_object(v___x_5481_);
lean_dec_ref(v_stackMap_5478_);
lean_dec_ref(v_funcMap_5477_);
lean_dec_ref(v_stringMap_5476_);
lean_dec_ref(v_toThread_5475_);
lean_dec_ref(v_s_5471_);
v_val_5484_ = lean_ctor_get(v___x_5483_, 0);
lean_inc(v_val_5484_);
lean_dec_ref_known(v___x_5483_, 1);
v___x_5485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5485_, 0, v_val_5484_);
lean_ctor_set(v___x_5485_, 1, v_a_5472_);
return v___x_5485_;
}
else
{
lean_object* v___x_5487_; uint8_t v_isShared_5488_; uint8_t v_isSharedCheck_5517_; 
lean_inc_ref(v_sampleMap_5474_);
lean_dec(v___x_5483_);
v_isSharedCheck_5517_ = !lean_is_exclusive(v_a_5472_);
if (v_isSharedCheck_5517_ == 0)
{
lean_object* v_unused_5518_; lean_object* v_unused_5519_; 
v_unused_5518_ = lean_ctor_get(v_a_5472_, 1);
lean_dec(v_unused_5518_);
v_unused_5519_ = lean_ctor_get(v_a_5472_, 0);
lean_dec(v_unused_5519_);
v___x_5487_ = v_a_5472_;
v_isShared_5488_ = v_isSharedCheck_5517_;
goto v_resetjp_5486_;
}
else
{
lean_dec(v_a_5472_);
v___x_5487_ = lean_box(0);
v_isShared_5488_ = v_isSharedCheck_5517_;
goto v_resetjp_5486_;
}
v_resetjp_5486_:
{
lean_object* v_size_5489_; lean_object* v_name_5490_; lean_object* v_processType_5491_; uint8_t v_isMainThread_5492_; lean_object* v_samples_5493_; lean_object* v_markers_5494_; lean_object* v_stackTable_5495_; lean_object* v_frameTable_5496_; lean_object* v_resourceTable_5497_; lean_object* v_nativeSymbols_5498_; lean_object* v_stringArray_5499_; lean_object* v_funcTable_5500_; lean_object* v___x_5502_; uint8_t v_isShared_5503_; uint8_t v_isSharedCheck_5516_; 
v_size_5489_ = lean_ctor_get(v_stringMap_5476_, 0);
lean_inc(v_size_5489_);
v_name_5490_ = lean_ctor_get(v_toThread_5475_, 0);
v_processType_5491_ = lean_ctor_get(v_toThread_5475_, 1);
v_isMainThread_5492_ = lean_ctor_get_uint8(v_toThread_5475_, sizeof(void*)*10);
v_samples_5493_ = lean_ctor_get(v_toThread_5475_, 2);
v_markers_5494_ = lean_ctor_get(v_toThread_5475_, 3);
v_stackTable_5495_ = lean_ctor_get(v_toThread_5475_, 4);
v_frameTable_5496_ = lean_ctor_get(v_toThread_5475_, 5);
v_resourceTable_5497_ = lean_ctor_get(v_toThread_5475_, 6);
v_nativeSymbols_5498_ = lean_ctor_get(v_toThread_5475_, 7);
v_stringArray_5499_ = lean_ctor_get(v_toThread_5475_, 8);
v_funcTable_5500_ = lean_ctor_get(v_toThread_5475_, 9);
v_isSharedCheck_5516_ = !lean_is_exclusive(v_toThread_5475_);
if (v_isSharedCheck_5516_ == 0)
{
v___x_5502_ = v_toThread_5475_;
v_isShared_5503_ = v_isSharedCheck_5516_;
goto v_resetjp_5501_;
}
else
{
lean_inc(v_funcTable_5500_);
lean_inc(v_stringArray_5499_);
lean_inc(v_nativeSymbols_5498_);
lean_inc(v_resourceTable_5497_);
lean_inc(v_frameTable_5496_);
lean_inc(v_stackTable_5495_);
lean_inc(v_markers_5494_);
lean_inc(v_samples_5493_);
lean_inc(v_processType_5491_);
lean_inc(v_name_5490_);
lean_dec(v_toThread_5475_);
v___x_5502_ = lean_box(0);
v_isShared_5503_ = v_isSharedCheck_5516_;
goto v_resetjp_5501_;
}
v_resetjp_5501_:
{
lean_object* v___x_5504_; lean_object* v___x_5506_; 
lean_inc_ref(v_s_5471_);
v___x_5504_ = lean_array_push(v_stringArray_5499_, v_s_5471_);
if (v_isShared_5503_ == 0)
{
lean_ctor_set(v___x_5502_, 8, v___x_5504_);
v___x_5506_ = v___x_5502_;
goto v_reusejp_5505_;
}
else
{
lean_object* v_reuseFailAlloc_5515_; 
v_reuseFailAlloc_5515_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_5515_, 0, v_name_5490_);
lean_ctor_set(v_reuseFailAlloc_5515_, 1, v_processType_5491_);
lean_ctor_set(v_reuseFailAlloc_5515_, 2, v_samples_5493_);
lean_ctor_set(v_reuseFailAlloc_5515_, 3, v_markers_5494_);
lean_ctor_set(v_reuseFailAlloc_5515_, 4, v_stackTable_5495_);
lean_ctor_set(v_reuseFailAlloc_5515_, 5, v_frameTable_5496_);
lean_ctor_set(v_reuseFailAlloc_5515_, 6, v_resourceTable_5497_);
lean_ctor_set(v_reuseFailAlloc_5515_, 7, v_nativeSymbols_5498_);
lean_ctor_set(v_reuseFailAlloc_5515_, 8, v___x_5504_);
lean_ctor_set(v_reuseFailAlloc_5515_, 9, v_funcTable_5500_);
lean_ctor_set_uint8(v_reuseFailAlloc_5515_, sizeof(void*)*10, v_isMainThread_5492_);
v___x_5506_ = v_reuseFailAlloc_5515_;
goto v_reusejp_5505_;
}
v_reusejp_5505_:
{
lean_object* v___x_5507_; lean_object* v___x_5509_; 
lean_inc(v_size_5489_);
v___x_5507_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__7___redArg(v_stringMap_5476_, v_s_5471_, v_size_5489_);
if (v_isShared_5482_ == 0)
{
lean_ctor_set(v___x_5481_, 1, v___x_5507_);
lean_ctor_set(v___x_5481_, 0, v___x_5506_);
v___x_5509_ = v___x_5481_;
goto v_reusejp_5508_;
}
else
{
lean_object* v_reuseFailAlloc_5514_; 
v_reuseFailAlloc_5514_ = lean_alloc_ctor(0, 4, 8);
lean_ctor_set(v_reuseFailAlloc_5514_, 0, v___x_5506_);
lean_ctor_set(v_reuseFailAlloc_5514_, 1, v___x_5507_);
lean_ctor_set(v_reuseFailAlloc_5514_, 2, v_funcMap_5477_);
lean_ctor_set(v_reuseFailAlloc_5514_, 3, v_stackMap_5478_);
lean_ctor_set_float(v_reuseFailAlloc_5514_, sizeof(void*)*4, v_lastTime_5479_);
v___x_5509_ = v_reuseFailAlloc_5514_;
goto v_reusejp_5508_;
}
v_reusejp_5508_:
{
lean_object* v___x_5511_; 
if (v_isShared_5488_ == 0)
{
lean_ctor_set(v___x_5487_, 0, v___x_5509_);
v___x_5511_ = v___x_5487_;
goto v_reusejp_5510_;
}
else
{
lean_object* v_reuseFailAlloc_5513_; 
v_reuseFailAlloc_5513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5513_, 0, v___x_5509_);
lean_ctor_set(v_reuseFailAlloc_5513_, 1, v_sampleMap_5474_);
v___x_5511_ = v_reuseFailAlloc_5513_;
goto v_reusejp_5510_;
}
v_reusejp_5510_:
{
lean_object* v___x_5512_; 
v___x_5512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5512_, 0, v_size_5489_);
lean_ctor_set(v___x_5512_, 1, v___x_5511_);
return v___x_5512_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Profiler_0__Lean_Firefox_collideThreads_collideStacks(lean_object* v_add_5521_, lean_object* v_oldStackIdx_5522_, lean_object* v_a_5523_){
_start:
{
lean_object* v_stackTable_5524_; lean_object* v_frameTable_5525_; lean_object* v_stringArray_5526_; lean_object* v_funcTable_5527_; lean_object* v_frame_5528_; lean_object* v_category_5529_; lean_object* v_subcategory_5530_; lean_object* v_prefix_5531_; lean_object* v___x_5532_; lean_object* v___x_5533_; lean_object* v___y_5535_; lean_object* v_fst_5536_; lean_object* v_snd_5537_; lean_object* v_toThread_5538_; lean_object* v_stringMap_5539_; lean_object* v_funcMap_5540_; lean_object* v_stackMap_5541_; double v_lastTime_5542_; lean_object* v_sampleMap_5543_; lean_object* v___x_5591_; lean_object* v_fst_5593_; lean_object* v_snd_5594_; lean_object* v_oldParentStackIdx_x3f_5675_; 
v_stackTable_5524_ = lean_ctor_get(v_add_5521_, 4);
v_frameTable_5525_ = lean_ctor_get(v_add_5521_, 5);
v_stringArray_5526_ = lean_ctor_get(v_add_5521_, 8);
v_funcTable_5527_ = lean_ctor_get(v_add_5521_, 9);
v_frame_5528_ = lean_ctor_get(v_stackTable_5524_, 0);
v_category_5529_ = lean_ctor_get(v_stackTable_5524_, 1);
v_subcategory_5530_ = lean_ctor_get(v_stackTable_5524_, 2);
v_prefix_5531_ = lean_ctor_get(v_stackTable_5524_, 3);
v___x_5532_ = lean_box(0);
v___x_5533_ = lean_unsigned_to_nat(0u);
v___x_5591_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__7___closed__2));
v_oldParentStackIdx_x3f_5675_ = lean_array_get(v___x_5532_, v_prefix_5531_, v_oldStackIdx_5522_);
if (lean_obj_tag(v_oldParentStackIdx_x3f_5675_) == 0)
{
v_fst_5593_ = v_oldParentStackIdx_x3f_5675_;
v_snd_5594_ = v_a_5523_;
goto v___jp_5592_;
}
else
{
lean_object* v_val_5676_; lean_object* v___x_5678_; uint8_t v_isShared_5679_; uint8_t v_isSharedCheck_5686_; 
v_val_5676_ = lean_ctor_get(v_oldParentStackIdx_x3f_5675_, 0);
v_isSharedCheck_5686_ = !lean_is_exclusive(v_oldParentStackIdx_x3f_5675_);
if (v_isSharedCheck_5686_ == 0)
{
v___x_5678_ = v_oldParentStackIdx_x3f_5675_;
v_isShared_5679_ = v_isSharedCheck_5686_;
goto v_resetjp_5677_;
}
else
{
lean_inc(v_val_5676_);
lean_dec(v_oldParentStackIdx_x3f_5675_);
v___x_5678_ = lean_box(0);
v_isShared_5679_ = v_isSharedCheck_5686_;
goto v_resetjp_5677_;
}
v_resetjp_5677_:
{
lean_object* v___x_5680_; lean_object* v_fst_5681_; lean_object* v_snd_5682_; lean_object* v___x_5684_; 
v___x_5680_ = l___private_Lean_Util_Profiler_0__Lean_Firefox_collideThreads_collideStacks(v_add_5521_, v_val_5676_, v_a_5523_);
lean_dec(v_val_5676_);
v_fst_5681_ = lean_ctor_get(v___x_5680_, 0);
lean_inc(v_fst_5681_);
v_snd_5682_ = lean_ctor_get(v___x_5680_, 1);
lean_inc(v_snd_5682_);
lean_dec_ref(v___x_5680_);
if (v_isShared_5679_ == 0)
{
lean_ctor_set(v___x_5678_, 0, v_fst_5681_);
v___x_5684_ = v___x_5678_;
goto v_reusejp_5683_;
}
else
{
lean_object* v_reuseFailAlloc_5685_; 
v_reuseFailAlloc_5685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5685_, 0, v_fst_5681_);
v___x_5684_ = v_reuseFailAlloc_5685_;
goto v_reusejp_5683_;
}
v_reusejp_5683_:
{
v_fst_5593_ = v___x_5684_;
v_snd_5594_ = v_snd_5682_;
goto v___jp_5592_;
}
}
}
v___jp_5534_:
{
lean_object* v___x_5544_; lean_object* v___x_5545_; 
lean_inc(v___y_5535_);
lean_inc(v_fst_5536_);
v___x_5544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5544_, 0, v_fst_5536_);
lean_ctor_set(v___x_5544_, 1, v___y_5535_);
v___x_5545_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__1___redArg(v_stackMap_5541_, v___x_5544_);
if (lean_obj_tag(v___x_5545_) == 1)
{
lean_object* v_val_5546_; lean_object* v___x_5547_; 
lean_dec_ref_known(v___x_5544_, 2);
lean_dec_ref(v_sampleMap_5543_);
lean_dec_ref(v_stackMap_5541_);
lean_dec_ref(v_funcMap_5540_);
lean_dec_ref(v_stringMap_5539_);
lean_dec_ref(v_toThread_5538_);
lean_dec(v_fst_5536_);
lean_dec(v___y_5535_);
v_val_5546_ = lean_ctor_get(v___x_5545_, 0);
lean_inc(v_val_5546_);
lean_dec_ref_known(v___x_5545_, 1);
v___x_5547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5547_, 0, v_val_5546_);
lean_ctor_set(v___x_5547_, 1, v_snd_5537_);
return v___x_5547_;
}
else
{
lean_object* v_stackTable_5548_; lean_object* v_name_5549_; lean_object* v_processType_5550_; uint8_t v_isMainThread_5551_; lean_object* v_samples_5552_; lean_object* v_markers_5553_; lean_object* v_frameTable_5554_; lean_object* v_resourceTable_5555_; lean_object* v_nativeSymbols_5556_; lean_object* v_stringArray_5557_; lean_object* v_funcTable_5558_; lean_object* v___x_5560_; uint8_t v_isShared_5561_; uint8_t v_isSharedCheck_5590_; 
lean_dec(v___x_5545_);
lean_dec_ref(v_snd_5537_);
v_stackTable_5548_ = lean_ctor_get(v_toThread_5538_, 4);
v_name_5549_ = lean_ctor_get(v_toThread_5538_, 0);
v_processType_5550_ = lean_ctor_get(v_toThread_5538_, 1);
v_isMainThread_5551_ = lean_ctor_get_uint8(v_toThread_5538_, sizeof(void*)*10);
v_samples_5552_ = lean_ctor_get(v_toThread_5538_, 2);
v_markers_5553_ = lean_ctor_get(v_toThread_5538_, 3);
v_frameTable_5554_ = lean_ctor_get(v_toThread_5538_, 5);
v_resourceTable_5555_ = lean_ctor_get(v_toThread_5538_, 6);
v_nativeSymbols_5556_ = lean_ctor_get(v_toThread_5538_, 7);
v_stringArray_5557_ = lean_ctor_get(v_toThread_5538_, 8);
v_funcTable_5558_ = lean_ctor_get(v_toThread_5538_, 9);
v_isSharedCheck_5590_ = !lean_is_exclusive(v_toThread_5538_);
if (v_isSharedCheck_5590_ == 0)
{
v___x_5560_ = v_toThread_5538_;
v_isShared_5561_ = v_isSharedCheck_5590_;
goto v_resetjp_5559_;
}
else
{
lean_inc(v_funcTable_5558_);
lean_inc(v_stringArray_5557_);
lean_inc(v_nativeSymbols_5556_);
lean_inc(v_resourceTable_5555_);
lean_inc(v_frameTable_5554_);
lean_inc(v_stackTable_5548_);
lean_inc(v_markers_5553_);
lean_inc(v_samples_5552_);
lean_inc(v_processType_5550_);
lean_inc(v_name_5549_);
lean_dec(v_toThread_5538_);
v___x_5560_ = lean_box(0);
v_isShared_5561_ = v_isSharedCheck_5590_;
goto v_resetjp_5559_;
}
v_resetjp_5559_:
{
lean_object* v_frame_5562_; lean_object* v_category_5563_; lean_object* v_subcategory_5564_; lean_object* v_prefix_5565_; lean_object* v_length_5566_; lean_object* v___x_5568_; uint8_t v_isShared_5569_; uint8_t v_isSharedCheck_5589_; 
v_frame_5562_ = lean_ctor_get(v_stackTable_5548_, 0);
v_category_5563_ = lean_ctor_get(v_stackTable_5548_, 1);
v_subcategory_5564_ = lean_ctor_get(v_stackTable_5548_, 2);
v_prefix_5565_ = lean_ctor_get(v_stackTable_5548_, 3);
v_length_5566_ = lean_ctor_get(v_stackTable_5548_, 4);
v_isSharedCheck_5589_ = !lean_is_exclusive(v_stackTable_5548_);
if (v_isSharedCheck_5589_ == 0)
{
v___x_5568_ = v_stackTable_5548_;
v_isShared_5569_ = v_isSharedCheck_5589_;
goto v_resetjp_5567_;
}
else
{
lean_inc(v_length_5566_);
lean_inc(v_prefix_5565_);
lean_inc(v_subcategory_5564_);
lean_inc(v_category_5563_);
lean_inc(v_frame_5562_);
lean_dec(v_stackTable_5548_);
v___x_5568_ = lean_box(0);
v_isShared_5569_ = v_isSharedCheck_5589_;
goto v_resetjp_5567_;
}
v_resetjp_5567_:
{
lean_object* v_size_5570_; lean_object* v___x_5571_; lean_object* v___x_5572_; lean_object* v___x_5573_; lean_object* v___x_5574_; lean_object* v___x_5575_; lean_object* v___x_5576_; lean_object* v___x_5577_; lean_object* v___x_5578_; lean_object* v___x_5580_; 
v_size_5570_ = lean_ctor_get(v_stackMap_5541_, 0);
lean_inc(v_size_5570_);
v___x_5571_ = lean_array_push(v_frame_5562_, v_fst_5536_);
v___x_5572_ = lean_array_get_borrowed(v___x_5533_, v_category_5529_, v_oldStackIdx_5522_);
lean_inc(v___x_5572_);
v___x_5573_ = lean_array_push(v_category_5563_, v___x_5572_);
v___x_5574_ = lean_array_get_borrowed(v___x_5533_, v_subcategory_5530_, v_oldStackIdx_5522_);
lean_inc(v___x_5574_);
v___x_5575_ = lean_array_push(v_subcategory_5564_, v___x_5574_);
v___x_5576_ = lean_array_push(v_prefix_5565_, v___y_5535_);
v___x_5577_ = lean_unsigned_to_nat(1u);
v___x_5578_ = lean_nat_add(v_length_5566_, v___x_5577_);
lean_dec(v_length_5566_);
if (v_isShared_5569_ == 0)
{
lean_ctor_set(v___x_5568_, 4, v___x_5578_);
lean_ctor_set(v___x_5568_, 3, v___x_5576_);
lean_ctor_set(v___x_5568_, 2, v___x_5575_);
lean_ctor_set(v___x_5568_, 1, v___x_5573_);
lean_ctor_set(v___x_5568_, 0, v___x_5571_);
v___x_5580_ = v___x_5568_;
goto v_reusejp_5579_;
}
else
{
lean_object* v_reuseFailAlloc_5588_; 
v_reuseFailAlloc_5588_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5588_, 0, v___x_5571_);
lean_ctor_set(v_reuseFailAlloc_5588_, 1, v___x_5573_);
lean_ctor_set(v_reuseFailAlloc_5588_, 2, v___x_5575_);
lean_ctor_set(v_reuseFailAlloc_5588_, 3, v___x_5576_);
lean_ctor_set(v_reuseFailAlloc_5588_, 4, v___x_5578_);
v___x_5580_ = v_reuseFailAlloc_5588_;
goto v_reusejp_5579_;
}
v_reusejp_5579_:
{
lean_object* v___x_5581_; lean_object* v___x_5583_; 
lean_inc(v_size_5570_);
v___x_5581_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__2___redArg(v_stackMap_5541_, v___x_5544_, v_size_5570_);
if (v_isShared_5561_ == 0)
{
lean_ctor_set(v___x_5560_, 4, v___x_5580_);
v___x_5583_ = v___x_5560_;
goto v_reusejp_5582_;
}
else
{
lean_object* v_reuseFailAlloc_5587_; 
v_reuseFailAlloc_5587_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_5587_, 0, v_name_5549_);
lean_ctor_set(v_reuseFailAlloc_5587_, 1, v_processType_5550_);
lean_ctor_set(v_reuseFailAlloc_5587_, 2, v_samples_5552_);
lean_ctor_set(v_reuseFailAlloc_5587_, 3, v_markers_5553_);
lean_ctor_set(v_reuseFailAlloc_5587_, 4, v___x_5580_);
lean_ctor_set(v_reuseFailAlloc_5587_, 5, v_frameTable_5554_);
lean_ctor_set(v_reuseFailAlloc_5587_, 6, v_resourceTable_5555_);
lean_ctor_set(v_reuseFailAlloc_5587_, 7, v_nativeSymbols_5556_);
lean_ctor_set(v_reuseFailAlloc_5587_, 8, v_stringArray_5557_);
lean_ctor_set(v_reuseFailAlloc_5587_, 9, v_funcTable_5558_);
lean_ctor_set_uint8(v_reuseFailAlloc_5587_, sizeof(void*)*10, v_isMainThread_5551_);
v___x_5583_ = v_reuseFailAlloc_5587_;
goto v_reusejp_5582_;
}
v_reusejp_5582_:
{
lean_object* v___x_5584_; lean_object* v___x_5585_; lean_object* v___x_5586_; 
v___x_5584_ = lean_alloc_ctor(0, 4, 8);
lean_ctor_set(v___x_5584_, 0, v___x_5583_);
lean_ctor_set(v___x_5584_, 1, v_stringMap_5539_);
lean_ctor_set(v___x_5584_, 2, v_funcMap_5540_);
lean_ctor_set(v___x_5584_, 3, v___x_5581_);
lean_ctor_set_float(v___x_5584_, sizeof(void*)*4, v_lastTime_5542_);
v___x_5585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5585_, 0, v___x_5584_);
lean_ctor_set(v___x_5585_, 1, v_sampleMap_5543_);
v___x_5586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5586_, 0, v_size_5570_);
lean_ctor_set(v___x_5586_, 1, v___x_5585_);
return v___x_5586_;
}
}
}
}
}
}
v___jp_5592_:
{
lean_object* v_func_5595_; lean_object* v_name_5596_; lean_object* v___x_5597_; lean_object* v___x_5598_; lean_object* v___x_5599_; lean_object* v___x_5600_; lean_object* v___x_5601_; lean_object* v_snd_5602_; lean_object* v_toThreadWithMaps_5603_; lean_object* v_fst_5604_; lean_object* v_sampleMap_5605_; lean_object* v_toThread_5606_; lean_object* v_stringMap_5607_; lean_object* v_funcMap_5608_; lean_object* v_stackMap_5609_; double v_lastTime_5610_; lean_object* v___x_5612_; uint8_t v_isShared_5613_; uint8_t v_isSharedCheck_5674_; 
v_func_5595_ = lean_ctor_get(v_frameTable_5525_, 4);
v_name_5596_ = lean_ctor_get(v_funcTable_5527_, 0);
v___x_5597_ = lean_array_get_borrowed(v___x_5533_, v_frame_5528_, v_oldStackIdx_5522_);
v___x_5598_ = lean_array_get_borrowed(v___x_5533_, v_func_5595_, v___x_5597_);
v___x_5599_ = lean_array_get_borrowed(v___x_5533_, v_name_5596_, v___x_5598_);
v___x_5600_ = lean_array_get_borrowed(v___x_5591_, v_stringArray_5526_, v___x_5599_);
lean_inc(v___x_5600_);
v___x_5601_ = l___private_Lean_Util_Profiler_0__Lean_Firefox_collideThreads_getStrIdx(v___x_5600_, v_snd_5594_);
v_snd_5602_ = lean_ctor_get(v___x_5601_, 1);
lean_inc(v_snd_5602_);
v_toThreadWithMaps_5603_ = lean_ctor_get(v_snd_5602_, 0);
lean_inc_ref(v_toThreadWithMaps_5603_);
v_fst_5604_ = lean_ctor_get(v___x_5601_, 0);
lean_inc(v_fst_5604_);
lean_dec_ref(v___x_5601_);
v_sampleMap_5605_ = lean_ctor_get(v_snd_5602_, 1);
lean_inc_ref(v_sampleMap_5605_);
v_toThread_5606_ = lean_ctor_get(v_toThreadWithMaps_5603_, 0);
v_stringMap_5607_ = lean_ctor_get(v_toThreadWithMaps_5603_, 1);
v_funcMap_5608_ = lean_ctor_get(v_toThreadWithMaps_5603_, 2);
v_stackMap_5609_ = lean_ctor_get(v_toThreadWithMaps_5603_, 3);
v_lastTime_5610_ = lean_ctor_get_float(v_toThreadWithMaps_5603_, sizeof(void*)*4);
v_isSharedCheck_5674_ = !lean_is_exclusive(v_toThreadWithMaps_5603_);
if (v_isSharedCheck_5674_ == 0)
{
v___x_5612_ = v_toThreadWithMaps_5603_;
v_isShared_5613_ = v_isSharedCheck_5674_;
goto v_resetjp_5611_;
}
else
{
lean_inc(v_stackMap_5609_);
lean_inc(v_funcMap_5608_);
lean_inc(v_stringMap_5607_);
lean_inc(v_toThread_5606_);
lean_dec(v_toThreadWithMaps_5603_);
v___x_5612_ = lean_box(0);
v_isShared_5613_ = v_isSharedCheck_5674_;
goto v_resetjp_5611_;
}
v_resetjp_5611_:
{
lean_object* v___x_5614_; 
v___x_5614_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__3___redArg(v_funcMap_5608_, v_fst_5604_);
if (lean_obj_tag(v___x_5614_) == 1)
{
lean_object* v_val_5615_; 
lean_del_object(v___x_5612_);
lean_dec(v_fst_5604_);
v_val_5615_ = lean_ctor_get(v___x_5614_, 0);
lean_inc(v_val_5615_);
lean_dec_ref_known(v___x_5614_, 1);
v___y_5535_ = v_fst_5593_;
v_fst_5536_ = v_val_5615_;
v_snd_5537_ = v_snd_5602_;
v_toThread_5538_ = v_toThread_5606_;
v_stringMap_5539_ = v_stringMap_5607_;
v_funcMap_5540_ = v_funcMap_5608_;
v_stackMap_5541_ = v_stackMap_5609_;
v_lastTime_5542_ = v_lastTime_5610_;
v_sampleMap_5543_ = v_sampleMap_5605_;
goto v___jp_5534_;
}
else
{
lean_object* v___x_5617_; uint8_t v_isShared_5618_; uint8_t v_isSharedCheck_5671_; 
lean_dec(v___x_5614_);
v_isSharedCheck_5671_ = !lean_is_exclusive(v_snd_5602_);
if (v_isSharedCheck_5671_ == 0)
{
lean_object* v_unused_5672_; lean_object* v_unused_5673_; 
v_unused_5672_ = lean_ctor_get(v_snd_5602_, 1);
lean_dec(v_unused_5672_);
v_unused_5673_ = lean_ctor_get(v_snd_5602_, 0);
lean_dec(v_unused_5673_);
v___x_5617_ = v_snd_5602_;
v_isShared_5618_ = v_isSharedCheck_5671_;
goto v_resetjp_5616_;
}
else
{
lean_dec(v_snd_5602_);
v___x_5617_ = lean_box(0);
v_isShared_5618_ = v_isSharedCheck_5671_;
goto v_resetjp_5616_;
}
v_resetjp_5616_:
{
lean_object* v_size_5619_; lean_object* v_name_5620_; lean_object* v_processType_5621_; uint8_t v_isMainThread_5622_; lean_object* v_samples_5623_; lean_object* v_markers_5624_; lean_object* v_stackTable_5625_; lean_object* v_frameTable_5626_; lean_object* v_resourceTable_5627_; lean_object* v_nativeSymbols_5628_; lean_object* v_stringArray_5629_; lean_object* v_funcTable_5630_; lean_object* v___x_5632_; uint8_t v_isShared_5633_; uint8_t v_isSharedCheck_5670_; 
v_size_5619_ = lean_ctor_get(v_funcMap_5608_, 0);
lean_inc(v_size_5619_);
v_name_5620_ = lean_ctor_get(v_toThread_5606_, 0);
v_processType_5621_ = lean_ctor_get(v_toThread_5606_, 1);
v_isMainThread_5622_ = lean_ctor_get_uint8(v_toThread_5606_, sizeof(void*)*10);
v_samples_5623_ = lean_ctor_get(v_toThread_5606_, 2);
v_markers_5624_ = lean_ctor_get(v_toThread_5606_, 3);
v_stackTable_5625_ = lean_ctor_get(v_toThread_5606_, 4);
v_frameTable_5626_ = lean_ctor_get(v_toThread_5606_, 5);
v_resourceTable_5627_ = lean_ctor_get(v_toThread_5606_, 6);
v_nativeSymbols_5628_ = lean_ctor_get(v_toThread_5606_, 7);
v_stringArray_5629_ = lean_ctor_get(v_toThread_5606_, 8);
v_funcTable_5630_ = lean_ctor_get(v_toThread_5606_, 9);
v_isSharedCheck_5670_ = !lean_is_exclusive(v_toThread_5606_);
if (v_isSharedCheck_5670_ == 0)
{
v___x_5632_ = v_toThread_5606_;
v_isShared_5633_ = v_isSharedCheck_5670_;
goto v_resetjp_5631_;
}
else
{
lean_inc(v_funcTable_5630_);
lean_inc(v_stringArray_5629_);
lean_inc(v_nativeSymbols_5628_);
lean_inc(v_resourceTable_5627_);
lean_inc(v_frameTable_5626_);
lean_inc(v_stackTable_5625_);
lean_inc(v_markers_5624_);
lean_inc(v_samples_5623_);
lean_inc(v_processType_5621_);
lean_inc(v_name_5620_);
lean_dec(v_toThread_5606_);
v___x_5632_ = lean_box(0);
v_isShared_5633_ = v_isSharedCheck_5670_;
goto v_resetjp_5631_;
}
v_resetjp_5631_:
{
lean_object* v___x_5634_; lean_object* v___x_5635_; lean_object* v___x_5636_; lean_object* v_name_5637_; lean_object* v_resource_5638_; lean_object* v_fileName_5639_; lean_object* v_lineNumber_5640_; lean_object* v_columnNumber_5641_; lean_object* v_length_5642_; lean_object* v___x_5644_; uint8_t v_isShared_5645_; uint8_t v_isSharedCheck_5667_; 
v___x_5634_ = lean_unsigned_to_nat(1u);
v___x_5635_ = lean_obj_once(&l___private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go___closed__2, &l___private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go___closed__2_once, _init_l___private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go___closed__2);
lean_inc(v_size_5619_);
v___x_5636_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_5636_, 0, v___x_5635_);
lean_ctor_set(v___x_5636_, 1, v___x_5533_);
lean_ctor_set(v___x_5636_, 2, v___x_5532_);
lean_ctor_set(v___x_5636_, 3, v___x_5532_);
lean_ctor_set(v___x_5636_, 4, v_size_5619_);
lean_ctor_set(v___x_5636_, 5, v___x_5532_);
lean_ctor_set(v___x_5636_, 6, v___x_5532_);
lean_ctor_set(v___x_5636_, 7, v___x_5532_);
lean_ctor_set(v___x_5636_, 8, v___x_5532_);
lean_ctor_set(v___x_5636_, 9, v___x_5532_);
v_name_5637_ = lean_ctor_get(v_funcTable_5630_, 0);
v_resource_5638_ = lean_ctor_get(v_funcTable_5630_, 3);
v_fileName_5639_ = lean_ctor_get(v_funcTable_5630_, 4);
v_lineNumber_5640_ = lean_ctor_get(v_funcTable_5630_, 5);
v_columnNumber_5641_ = lean_ctor_get(v_funcTable_5630_, 6);
v_length_5642_ = lean_ctor_get(v_funcTable_5630_, 7);
v_isSharedCheck_5667_ = !lean_is_exclusive(v_funcTable_5630_);
if (v_isSharedCheck_5667_ == 0)
{
lean_object* v_unused_5668_; lean_object* v_unused_5669_; 
v_unused_5668_ = lean_ctor_get(v_funcTable_5630_, 2);
lean_dec(v_unused_5668_);
v_unused_5669_ = lean_ctor_get(v_funcTable_5630_, 1);
lean_dec(v_unused_5669_);
v___x_5644_ = v_funcTable_5630_;
v_isShared_5645_ = v_isSharedCheck_5667_;
goto v_resetjp_5643_;
}
else
{
lean_inc(v_length_5642_);
lean_inc(v_columnNumber_5641_);
lean_inc(v_lineNumber_5640_);
lean_inc(v_fileName_5639_);
lean_inc(v_resource_5638_);
lean_inc(v_name_5637_);
lean_dec(v_funcTable_5630_);
v___x_5644_ = lean_box(0);
v_isShared_5645_ = v_isSharedCheck_5667_;
goto v_resetjp_5643_;
}
v_resetjp_5643_:
{
lean_object* v___x_5646_; lean_object* v___x_5647_; lean_object* v___x_5648_; lean_object* v___x_5649_; lean_object* v___x_5650_; lean_object* v___x_5651_; lean_object* v___x_5652_; lean_object* v___x_5653_; lean_object* v___x_5655_; 
v___x_5646_ = l_Lean_Firefox_FrameTable_push(v_frameTable_5626_, v___x_5636_);
lean_inc(v_fst_5604_);
v___x_5647_ = lean_array_push(v_name_5637_, v_fst_5604_);
v___x_5648_ = ((lean_object*)(l___private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go___closed__3));
v___x_5649_ = lean_array_push(v_resource_5638_, v___x_5635_);
v___x_5650_ = lean_array_push(v_fileName_5639_, v___x_5532_);
v___x_5651_ = lean_array_push(v_lineNumber_5640_, v___x_5532_);
v___x_5652_ = lean_array_push(v_columnNumber_5641_, v___x_5532_);
v___x_5653_ = lean_nat_add(v_length_5642_, v___x_5634_);
lean_dec(v_length_5642_);
if (v_isShared_5645_ == 0)
{
lean_ctor_set(v___x_5644_, 7, v___x_5653_);
lean_ctor_set(v___x_5644_, 6, v___x_5652_);
lean_ctor_set(v___x_5644_, 5, v___x_5651_);
lean_ctor_set(v___x_5644_, 4, v___x_5650_);
lean_ctor_set(v___x_5644_, 3, v___x_5649_);
lean_ctor_set(v___x_5644_, 2, v___x_5648_);
lean_ctor_set(v___x_5644_, 1, v___x_5648_);
lean_ctor_set(v___x_5644_, 0, v___x_5647_);
v___x_5655_ = v___x_5644_;
goto v_reusejp_5654_;
}
else
{
lean_object* v_reuseFailAlloc_5666_; 
v_reuseFailAlloc_5666_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_5666_, 0, v___x_5647_);
lean_ctor_set(v_reuseFailAlloc_5666_, 1, v___x_5648_);
lean_ctor_set(v_reuseFailAlloc_5666_, 2, v___x_5648_);
lean_ctor_set(v_reuseFailAlloc_5666_, 3, v___x_5649_);
lean_ctor_set(v_reuseFailAlloc_5666_, 4, v___x_5650_);
lean_ctor_set(v_reuseFailAlloc_5666_, 5, v___x_5651_);
lean_ctor_set(v_reuseFailAlloc_5666_, 6, v___x_5652_);
lean_ctor_set(v_reuseFailAlloc_5666_, 7, v___x_5653_);
v___x_5655_ = v_reuseFailAlloc_5666_;
goto v_reusejp_5654_;
}
v_reusejp_5654_:
{
lean_object* v___x_5657_; 
if (v_isShared_5633_ == 0)
{
lean_ctor_set(v___x_5632_, 9, v___x_5655_);
lean_ctor_set(v___x_5632_, 5, v___x_5646_);
v___x_5657_ = v___x_5632_;
goto v_reusejp_5656_;
}
else
{
lean_object* v_reuseFailAlloc_5665_; 
v_reuseFailAlloc_5665_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_5665_, 0, v_name_5620_);
lean_ctor_set(v_reuseFailAlloc_5665_, 1, v_processType_5621_);
lean_ctor_set(v_reuseFailAlloc_5665_, 2, v_samples_5623_);
lean_ctor_set(v_reuseFailAlloc_5665_, 3, v_markers_5624_);
lean_ctor_set(v_reuseFailAlloc_5665_, 4, v_stackTable_5625_);
lean_ctor_set(v_reuseFailAlloc_5665_, 5, v___x_5646_);
lean_ctor_set(v_reuseFailAlloc_5665_, 6, v_resourceTable_5627_);
lean_ctor_set(v_reuseFailAlloc_5665_, 7, v_nativeSymbols_5628_);
lean_ctor_set(v_reuseFailAlloc_5665_, 8, v_stringArray_5629_);
lean_ctor_set(v_reuseFailAlloc_5665_, 9, v___x_5655_);
lean_ctor_set_uint8(v_reuseFailAlloc_5665_, sizeof(void*)*10, v_isMainThread_5622_);
v___x_5657_ = v_reuseFailAlloc_5665_;
goto v_reusejp_5656_;
}
v_reusejp_5656_:
{
lean_object* v___x_5658_; lean_object* v___x_5660_; 
lean_inc(v_size_5619_);
v___x_5658_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__4___redArg(v_funcMap_5608_, v_fst_5604_, v_size_5619_);
lean_inc_ref(v_stackMap_5609_);
lean_inc_ref(v___x_5658_);
lean_inc_ref(v_stringMap_5607_);
lean_inc_ref(v___x_5657_);
if (v_isShared_5613_ == 0)
{
lean_ctor_set(v___x_5612_, 2, v___x_5658_);
lean_ctor_set(v___x_5612_, 0, v___x_5657_);
v___x_5660_ = v___x_5612_;
goto v_reusejp_5659_;
}
else
{
lean_object* v_reuseFailAlloc_5664_; 
v_reuseFailAlloc_5664_ = lean_alloc_ctor(0, 4, 8);
lean_ctor_set(v_reuseFailAlloc_5664_, 0, v___x_5657_);
lean_ctor_set(v_reuseFailAlloc_5664_, 1, v_stringMap_5607_);
lean_ctor_set(v_reuseFailAlloc_5664_, 2, v___x_5658_);
lean_ctor_set(v_reuseFailAlloc_5664_, 3, v_stackMap_5609_);
lean_ctor_set_float(v_reuseFailAlloc_5664_, sizeof(void*)*4, v_lastTime_5610_);
v___x_5660_ = v_reuseFailAlloc_5664_;
goto v_reusejp_5659_;
}
v_reusejp_5659_:
{
lean_object* v___x_5662_; 
lean_inc_ref(v_sampleMap_5605_);
if (v_isShared_5618_ == 0)
{
lean_ctor_set(v___x_5617_, 0, v___x_5660_);
v___x_5662_ = v___x_5617_;
goto v_reusejp_5661_;
}
else
{
lean_object* v_reuseFailAlloc_5663_; 
v_reuseFailAlloc_5663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5663_, 0, v___x_5660_);
lean_ctor_set(v_reuseFailAlloc_5663_, 1, v_sampleMap_5605_);
v___x_5662_ = v_reuseFailAlloc_5663_;
goto v_reusejp_5661_;
}
v_reusejp_5661_:
{
v___y_5535_ = v_fst_5593_;
v_fst_5536_ = v_size_5619_;
v_snd_5537_ = v___x_5662_;
v_toThread_5538_ = v___x_5657_;
v_stringMap_5539_ = v_stringMap_5607_;
v_funcMap_5540_ = v___x_5658_;
v_stackMap_5541_ = v_stackMap_5609_;
v_lastTime_5542_ = v_lastTime_5610_;
v_sampleMap_5543_ = v_sampleMap_5605_;
goto v___jp_5534_;
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
LEAN_EXPORT lean_object* l___private_Lean_Util_Profiler_0__Lean_Firefox_collideThreads_collideStacks___boxed(lean_object* v_add_5687_, lean_object* v_oldStackIdx_5688_, lean_object* v_a_5689_){
_start:
{
lean_object* v_res_5690_; 
v_res_5690_ = l___private_Lean_Util_Profiler_0__Lean_Firefox_collideThreads_collideStacks(v_add_5687_, v_oldStackIdx_5688_, v_a_5689_);
lean_dec(v_oldStackIdx_5688_);
lean_dec_ref(v_add_5687_);
return v_res_5690_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_collideThreads_collideSamples_spec__0___redArg___boxed__const__1(void){
_start:
{
double v___x_5691_; lean_object* v___x_5692_; 
v___x_5691_ = l_Lean_Firefox_instInhabitedMilliseconds_default;
v___x_5692_ = lean_box_float(v___x_5691_);
return v___x_5692_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_collideThreads_collideSamples_spec__0___redArg(lean_object* v_upperBound_5693_, lean_object* v___x_5694_, lean_object* v_add_5695_, lean_object* v_a_5696_, lean_object* v_b_5697_, lean_object* v___y_5698_){
_start:
{
lean_object* v_a_5700_; lean_object* v_snd_5701_; uint8_t v___x_5705_; 
v___x_5705_ = lean_nat_dec_lt(v_a_5696_, v_upperBound_5693_);
if (v___x_5705_ == 0)
{
lean_object* v___x_5706_; 
lean_dec(v_a_5696_);
v___x_5706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5706_, 0, v_b_5697_);
lean_ctor_set(v___x_5706_, 1, v___y_5698_);
return v___x_5706_;
}
else
{
lean_object* v_stack_5707_; lean_object* v_weight_5708_; lean_object* v___x_5709_; lean_object* v___x_5710_; lean_object* v___x_5711_; lean_object* v_snd_5712_; lean_object* v_fst_5713_; lean_object* v_toThreadWithMaps_5714_; lean_object* v_sampleMap_5715_; lean_object* v___x_5717_; uint8_t v_isShared_5718_; uint8_t v_isSharedCheck_5846_; 
v_stack_5707_ = lean_ctor_get(v___x_5694_, 0);
v_weight_5708_ = lean_ctor_get(v___x_5694_, 2);
v___x_5709_ = lean_unsigned_to_nat(0u);
v___x_5710_ = lean_array_get_borrowed(v___x_5709_, v_stack_5707_, v_a_5696_);
v___x_5711_ = l___private_Lean_Util_Profiler_0__Lean_Firefox_collideThreads_collideStacks(v_add_5695_, v___x_5710_, v___y_5698_);
v_snd_5712_ = lean_ctor_get(v___x_5711_, 1);
lean_inc(v_snd_5712_);
v_fst_5713_ = lean_ctor_get(v___x_5711_, 0);
lean_inc(v_fst_5713_);
lean_dec_ref(v___x_5711_);
v_toThreadWithMaps_5714_ = lean_ctor_get(v_snd_5712_, 0);
v_sampleMap_5715_ = lean_ctor_get(v_snd_5712_, 1);
v_isSharedCheck_5846_ = !lean_is_exclusive(v_snd_5712_);
if (v_isSharedCheck_5846_ == 0)
{
v___x_5717_ = v_snd_5712_;
v_isShared_5718_ = v_isSharedCheck_5846_;
goto v_resetjp_5716_;
}
else
{
lean_inc(v_sampleMap_5715_);
lean_inc(v_toThreadWithMaps_5714_);
lean_dec(v_snd_5712_);
v___x_5717_ = lean_box(0);
v_isShared_5718_ = v_isSharedCheck_5846_;
goto v_resetjp_5716_;
}
v_resetjp_5716_:
{
lean_object* v___x_5719_; lean_object* v___x_5720_; 
v___x_5719_ = lean_box(0);
v___x_5720_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__3___redArg(v_sampleMap_5715_, v_fst_5713_);
if (lean_obj_tag(v___x_5720_) == 1)
{
lean_object* v_toThread_5721_; lean_object* v_samples_5722_; lean_object* v_val_5723_; lean_object* v_stringMap_5724_; lean_object* v_funcMap_5725_; lean_object* v_stackMap_5726_; double v_lastTime_5727_; lean_object* v___x_5729_; uint8_t v_isShared_5730_; uint8_t v_isSharedCheck_5777_; 
lean_dec(v_fst_5713_);
v_toThread_5721_ = lean_ctor_get(v_toThreadWithMaps_5714_, 0);
lean_inc_ref(v_toThread_5721_);
v_samples_5722_ = lean_ctor_get(v_toThread_5721_, 2);
lean_inc_ref(v_samples_5722_);
v_val_5723_ = lean_ctor_get(v___x_5720_, 0);
lean_inc(v_val_5723_);
lean_dec_ref_known(v___x_5720_, 1);
v_stringMap_5724_ = lean_ctor_get(v_toThreadWithMaps_5714_, 1);
v_funcMap_5725_ = lean_ctor_get(v_toThreadWithMaps_5714_, 2);
v_stackMap_5726_ = lean_ctor_get(v_toThreadWithMaps_5714_, 3);
v_lastTime_5727_ = lean_ctor_get_float(v_toThreadWithMaps_5714_, sizeof(void*)*4);
v_isSharedCheck_5777_ = !lean_is_exclusive(v_toThreadWithMaps_5714_);
if (v_isSharedCheck_5777_ == 0)
{
lean_object* v_unused_5778_; 
v_unused_5778_ = lean_ctor_get(v_toThreadWithMaps_5714_, 0);
lean_dec(v_unused_5778_);
v___x_5729_ = v_toThreadWithMaps_5714_;
v_isShared_5730_ = v_isSharedCheck_5777_;
goto v_resetjp_5728_;
}
else
{
lean_inc(v_stackMap_5726_);
lean_inc(v_funcMap_5725_);
lean_inc(v_stringMap_5724_);
lean_dec(v_toThreadWithMaps_5714_);
v___x_5729_ = lean_box(0);
v_isShared_5730_ = v_isSharedCheck_5777_;
goto v_resetjp_5728_;
}
v_resetjp_5728_:
{
lean_object* v_name_5731_; lean_object* v_processType_5732_; uint8_t v_isMainThread_5733_; lean_object* v_markers_5734_; lean_object* v_stackTable_5735_; lean_object* v_frameTable_5736_; lean_object* v_resourceTable_5737_; lean_object* v_nativeSymbols_5738_; lean_object* v_stringArray_5739_; lean_object* v_funcTable_5740_; lean_object* v___x_5742_; uint8_t v_isShared_5743_; uint8_t v_isSharedCheck_5775_; 
v_name_5731_ = lean_ctor_get(v_toThread_5721_, 0);
v_processType_5732_ = lean_ctor_get(v_toThread_5721_, 1);
v_isMainThread_5733_ = lean_ctor_get_uint8(v_toThread_5721_, sizeof(void*)*10);
v_markers_5734_ = lean_ctor_get(v_toThread_5721_, 3);
v_stackTable_5735_ = lean_ctor_get(v_toThread_5721_, 4);
v_frameTable_5736_ = lean_ctor_get(v_toThread_5721_, 5);
v_resourceTable_5737_ = lean_ctor_get(v_toThread_5721_, 6);
v_nativeSymbols_5738_ = lean_ctor_get(v_toThread_5721_, 7);
v_stringArray_5739_ = lean_ctor_get(v_toThread_5721_, 8);
v_funcTable_5740_ = lean_ctor_get(v_toThread_5721_, 9);
v_isSharedCheck_5775_ = !lean_is_exclusive(v_toThread_5721_);
if (v_isSharedCheck_5775_ == 0)
{
lean_object* v_unused_5776_; 
v_unused_5776_ = lean_ctor_get(v_toThread_5721_, 2);
lean_dec(v_unused_5776_);
v___x_5742_ = v_toThread_5721_;
v_isShared_5743_ = v_isSharedCheck_5775_;
goto v_resetjp_5741_;
}
else
{
lean_inc(v_funcTable_5740_);
lean_inc(v_stringArray_5739_);
lean_inc(v_nativeSymbols_5738_);
lean_inc(v_resourceTable_5737_);
lean_inc(v_frameTable_5736_);
lean_inc(v_stackTable_5735_);
lean_inc(v_markers_5734_);
lean_inc(v_processType_5732_);
lean_inc(v_name_5731_);
lean_dec(v_toThread_5721_);
v___x_5742_ = lean_box(0);
v_isShared_5743_ = v_isSharedCheck_5775_;
goto v_resetjp_5741_;
}
v_resetjp_5741_:
{
lean_object* v_stack_5744_; lean_object* v_time_5745_; lean_object* v_weight_5746_; lean_object* v_weightType_5747_; lean_object* v_threadCPUDelta_5748_; lean_object* v_length_5749_; lean_object* v___x_5751_; uint8_t v_isShared_5752_; uint8_t v_isSharedCheck_5774_; 
v_stack_5744_ = lean_ctor_get(v_samples_5722_, 0);
v_time_5745_ = lean_ctor_get(v_samples_5722_, 1);
v_weight_5746_ = lean_ctor_get(v_samples_5722_, 2);
v_weightType_5747_ = lean_ctor_get(v_samples_5722_, 3);
v_threadCPUDelta_5748_ = lean_ctor_get(v_samples_5722_, 4);
v_length_5749_ = lean_ctor_get(v_samples_5722_, 5);
v_isSharedCheck_5774_ = !lean_is_exclusive(v_samples_5722_);
if (v_isSharedCheck_5774_ == 0)
{
v___x_5751_ = v_samples_5722_;
v_isShared_5752_ = v_isSharedCheck_5774_;
goto v_resetjp_5750_;
}
else
{
lean_inc(v_length_5749_);
lean_inc(v_threadCPUDelta_5748_);
lean_inc(v_weightType_5747_);
lean_inc(v_weight_5746_);
lean_inc(v_time_5745_);
lean_inc(v_stack_5744_);
lean_dec(v_samples_5722_);
v___x_5751_ = lean_box(0);
v_isShared_5752_ = v_isSharedCheck_5774_;
goto v_resetjp_5750_;
}
v_resetjp_5750_:
{
lean_object* v___x_5753_; lean_object* v___x_5754_; lean_object* v___x_5755_; lean_object* v___x_5756_; double v___x_5757_; double v___x_5758_; double v___x_5759_; lean_object* v___x_5760_; lean_object* v___x_5761_; lean_object* v___x_5763_; 
v___x_5753_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_collideThreads_collideSamples_spec__0___redArg___boxed__const__1;
v___x_5754_ = lean_array_get_borrowed(v___x_5753_, v_weight_5746_, v_val_5723_);
v___x_5755_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_collideThreads_collideSamples_spec__0___redArg___boxed__const__1;
v___x_5756_ = lean_array_get_borrowed(v___x_5755_, v_weight_5708_, v_a_5696_);
v___x_5757_ = lean_unbox_float(v___x_5754_);
v___x_5758_ = lean_unbox_float(v___x_5756_);
v___x_5759_ = lean_float_add(v___x_5757_, v___x_5758_);
v___x_5760_ = lean_box_float(v___x_5759_);
v___x_5761_ = lean_array_set(v_weight_5746_, v_val_5723_, v___x_5760_);
lean_dec(v_val_5723_);
if (v_isShared_5752_ == 0)
{
lean_ctor_set(v___x_5751_, 2, v___x_5761_);
v___x_5763_ = v___x_5751_;
goto v_reusejp_5762_;
}
else
{
lean_object* v_reuseFailAlloc_5773_; 
v_reuseFailAlloc_5773_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_5773_, 0, v_stack_5744_);
lean_ctor_set(v_reuseFailAlloc_5773_, 1, v_time_5745_);
lean_ctor_set(v_reuseFailAlloc_5773_, 2, v___x_5761_);
lean_ctor_set(v_reuseFailAlloc_5773_, 3, v_weightType_5747_);
lean_ctor_set(v_reuseFailAlloc_5773_, 4, v_threadCPUDelta_5748_);
lean_ctor_set(v_reuseFailAlloc_5773_, 5, v_length_5749_);
v___x_5763_ = v_reuseFailAlloc_5773_;
goto v_reusejp_5762_;
}
v_reusejp_5762_:
{
lean_object* v___x_5765_; 
if (v_isShared_5743_ == 0)
{
lean_ctor_set(v___x_5742_, 2, v___x_5763_);
v___x_5765_ = v___x_5742_;
goto v_reusejp_5764_;
}
else
{
lean_object* v_reuseFailAlloc_5772_; 
v_reuseFailAlloc_5772_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_5772_, 0, v_name_5731_);
lean_ctor_set(v_reuseFailAlloc_5772_, 1, v_processType_5732_);
lean_ctor_set(v_reuseFailAlloc_5772_, 2, v___x_5763_);
lean_ctor_set(v_reuseFailAlloc_5772_, 3, v_markers_5734_);
lean_ctor_set(v_reuseFailAlloc_5772_, 4, v_stackTable_5735_);
lean_ctor_set(v_reuseFailAlloc_5772_, 5, v_frameTable_5736_);
lean_ctor_set(v_reuseFailAlloc_5772_, 6, v_resourceTable_5737_);
lean_ctor_set(v_reuseFailAlloc_5772_, 7, v_nativeSymbols_5738_);
lean_ctor_set(v_reuseFailAlloc_5772_, 8, v_stringArray_5739_);
lean_ctor_set(v_reuseFailAlloc_5772_, 9, v_funcTable_5740_);
lean_ctor_set_uint8(v_reuseFailAlloc_5772_, sizeof(void*)*10, v_isMainThread_5733_);
v___x_5765_ = v_reuseFailAlloc_5772_;
goto v_reusejp_5764_;
}
v_reusejp_5764_:
{
lean_object* v___x_5767_; 
if (v_isShared_5730_ == 0)
{
lean_ctor_set(v___x_5729_, 0, v___x_5765_);
v___x_5767_ = v___x_5729_;
goto v_reusejp_5766_;
}
else
{
lean_object* v_reuseFailAlloc_5771_; 
v_reuseFailAlloc_5771_ = lean_alloc_ctor(0, 4, 8);
lean_ctor_set(v_reuseFailAlloc_5771_, 0, v___x_5765_);
lean_ctor_set(v_reuseFailAlloc_5771_, 1, v_stringMap_5724_);
lean_ctor_set(v_reuseFailAlloc_5771_, 2, v_funcMap_5725_);
lean_ctor_set(v_reuseFailAlloc_5771_, 3, v_stackMap_5726_);
lean_ctor_set_float(v_reuseFailAlloc_5771_, sizeof(void*)*4, v_lastTime_5727_);
v___x_5767_ = v_reuseFailAlloc_5771_;
goto v_reusejp_5766_;
}
v_reusejp_5766_:
{
lean_object* v___x_5769_; 
if (v_isShared_5718_ == 0)
{
lean_ctor_set(v___x_5717_, 0, v___x_5767_);
v___x_5769_ = v___x_5717_;
goto v_reusejp_5768_;
}
else
{
lean_object* v_reuseFailAlloc_5770_; 
v_reuseFailAlloc_5770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5770_, 0, v___x_5767_);
lean_ctor_set(v_reuseFailAlloc_5770_, 1, v_sampleMap_5715_);
v___x_5769_ = v_reuseFailAlloc_5770_;
goto v_reusejp_5768_;
}
v_reusejp_5768_:
{
v_a_5700_ = v___x_5719_;
v_snd_5701_ = v___x_5769_;
goto v___jp_5699_;
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
lean_object* v_toThread_5779_; lean_object* v_samples_5780_; lean_object* v_stringMap_5781_; lean_object* v_funcMap_5782_; lean_object* v_stackMap_5783_; double v_lastTime_5784_; lean_object* v___x_5786_; uint8_t v_isShared_5787_; uint8_t v_isSharedCheck_5844_; 
lean_dec(v___x_5720_);
v_toThread_5779_ = lean_ctor_get(v_toThreadWithMaps_5714_, 0);
lean_inc_ref(v_toThread_5779_);
v_samples_5780_ = lean_ctor_get(v_toThread_5779_, 2);
lean_inc_ref(v_samples_5780_);
v_stringMap_5781_ = lean_ctor_get(v_toThreadWithMaps_5714_, 1);
v_funcMap_5782_ = lean_ctor_get(v_toThreadWithMaps_5714_, 2);
v_stackMap_5783_ = lean_ctor_get(v_toThreadWithMaps_5714_, 3);
v_lastTime_5784_ = lean_ctor_get_float(v_toThreadWithMaps_5714_, sizeof(void*)*4);
v_isSharedCheck_5844_ = !lean_is_exclusive(v_toThreadWithMaps_5714_);
if (v_isSharedCheck_5844_ == 0)
{
lean_object* v_unused_5845_; 
v_unused_5845_ = lean_ctor_get(v_toThreadWithMaps_5714_, 0);
lean_dec(v_unused_5845_);
v___x_5786_ = v_toThreadWithMaps_5714_;
v_isShared_5787_ = v_isSharedCheck_5844_;
goto v_resetjp_5785_;
}
else
{
lean_inc(v_stackMap_5783_);
lean_inc(v_funcMap_5782_);
lean_inc(v_stringMap_5781_);
lean_dec(v_toThreadWithMaps_5714_);
v___x_5786_ = lean_box(0);
v_isShared_5787_ = v_isSharedCheck_5844_;
goto v_resetjp_5785_;
}
v_resetjp_5785_:
{
lean_object* v_name_5788_; lean_object* v_processType_5789_; uint8_t v_isMainThread_5790_; lean_object* v_markers_5791_; lean_object* v_stackTable_5792_; lean_object* v_frameTable_5793_; lean_object* v_resourceTable_5794_; lean_object* v_nativeSymbols_5795_; lean_object* v_stringArray_5796_; lean_object* v_funcTable_5797_; lean_object* v___x_5799_; uint8_t v_isShared_5800_; uint8_t v_isSharedCheck_5842_; 
v_name_5788_ = lean_ctor_get(v_toThread_5779_, 0);
v_processType_5789_ = lean_ctor_get(v_toThread_5779_, 1);
v_isMainThread_5790_ = lean_ctor_get_uint8(v_toThread_5779_, sizeof(void*)*10);
v_markers_5791_ = lean_ctor_get(v_toThread_5779_, 3);
v_stackTable_5792_ = lean_ctor_get(v_toThread_5779_, 4);
v_frameTable_5793_ = lean_ctor_get(v_toThread_5779_, 5);
v_resourceTable_5794_ = lean_ctor_get(v_toThread_5779_, 6);
v_nativeSymbols_5795_ = lean_ctor_get(v_toThread_5779_, 7);
v_stringArray_5796_ = lean_ctor_get(v_toThread_5779_, 8);
v_funcTable_5797_ = lean_ctor_get(v_toThread_5779_, 9);
v_isSharedCheck_5842_ = !lean_is_exclusive(v_toThread_5779_);
if (v_isSharedCheck_5842_ == 0)
{
lean_object* v_unused_5843_; 
v_unused_5843_ = lean_ctor_get(v_toThread_5779_, 2);
lean_dec(v_unused_5843_);
v___x_5799_ = v_toThread_5779_;
v_isShared_5800_ = v_isSharedCheck_5842_;
goto v_resetjp_5798_;
}
else
{
lean_inc(v_funcTable_5797_);
lean_inc(v_stringArray_5796_);
lean_inc(v_nativeSymbols_5795_);
lean_inc(v_resourceTable_5794_);
lean_inc(v_frameTable_5793_);
lean_inc(v_stackTable_5792_);
lean_inc(v_markers_5791_);
lean_inc(v_processType_5789_);
lean_inc(v_name_5788_);
lean_dec(v_toThread_5779_);
v___x_5799_ = lean_box(0);
v_isShared_5800_ = v_isSharedCheck_5842_;
goto v_resetjp_5798_;
}
v_resetjp_5798_:
{
lean_object* v_stack_5801_; lean_object* v_time_5802_; lean_object* v_weight_5803_; lean_object* v_threadCPUDelta_5804_; lean_object* v_length_5805_; lean_object* v___x_5807_; uint8_t v_isShared_5808_; uint8_t v_isSharedCheck_5840_; 
v_stack_5801_ = lean_ctor_get(v_samples_5780_, 0);
v_time_5802_ = lean_ctor_get(v_samples_5780_, 1);
v_weight_5803_ = lean_ctor_get(v_samples_5780_, 2);
v_threadCPUDelta_5804_ = lean_ctor_get(v_samples_5780_, 4);
v_length_5805_ = lean_ctor_get(v_samples_5780_, 5);
v_isSharedCheck_5840_ = !lean_is_exclusive(v_samples_5780_);
if (v_isSharedCheck_5840_ == 0)
{
lean_object* v_unused_5841_; 
v_unused_5841_ = lean_ctor_get(v_samples_5780_, 3);
lean_dec(v_unused_5841_);
v___x_5807_ = v_samples_5780_;
v_isShared_5808_ = v_isSharedCheck_5840_;
goto v_resetjp_5806_;
}
else
{
lean_inc(v_length_5805_);
lean_inc(v_threadCPUDelta_5804_);
lean_inc(v_weight_5803_);
lean_inc(v_time_5802_);
lean_inc(v_stack_5801_);
lean_dec(v_samples_5780_);
v___x_5807_ = lean_box(0);
v_isShared_5808_ = v_isSharedCheck_5840_;
goto v_resetjp_5806_;
}
v_resetjp_5806_:
{
lean_object* v_size_5809_; lean_object* v___x_5810_; lean_object* v___x_5811_; double v___x_5812_; double v___x_5813_; double v___x_5814_; lean_object* v___x_5815_; lean_object* v___x_5816_; lean_object* v___x_5817_; lean_object* v___x_5818_; lean_object* v___x_5819_; lean_object* v___x_5820_; lean_object* v___x_5821_; lean_object* v___x_5822_; double v___x_5823_; lean_object* v___x_5824_; lean_object* v___x_5825_; lean_object* v___x_5826_; lean_object* v___x_5828_; 
v_size_5809_ = lean_ctor_get(v_sampleMap_5715_, 0);
lean_inc(v_size_5809_);
v___x_5810_ = lean_array_get_size(v_time_5802_);
lean_inc(v_fst_5713_);
v___x_5811_ = lean_array_push(v_stack_5801_, v_fst_5713_);
v___x_5812_ = lean_float_of_nat(v___x_5810_);
v___x_5813_ = lean_float_once(&l_Lean_Firefox_instCoeFloatMilliseconds___lam__0___closed__0, &l_Lean_Firefox_instCoeFloatMilliseconds___lam__0___closed__0_once, _init_l_Lean_Firefox_instCoeFloatMilliseconds___lam__0___closed__0);
v___x_5814_ = lean_float_mul(v___x_5812_, v___x_5813_);
v___x_5815_ = lean_box_float(v___x_5814_);
v___x_5816_ = lean_array_push(v_time_5802_, v___x_5815_);
v___x_5817_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_collideThreads_collideSamples_spec__0___redArg___boxed__const__1;
v___x_5818_ = lean_array_get_borrowed(v___x_5817_, v_weight_5708_, v_a_5696_);
lean_inc(v___x_5818_);
v___x_5819_ = lean_array_push(v_weight_5803_, v___x_5818_);
v___x_5820_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__0___closed__0));
v___x_5821_ = lean_unsigned_to_nat(10u);
v___x_5822_ = lean_unsigned_to_nat(1u);
v___x_5823_ = l_Float_ofScientific(v___x_5821_, v___x_5705_, v___x_5822_);
v___x_5824_ = lean_box_float(v___x_5823_);
v___x_5825_ = lean_array_push(v_threadCPUDelta_5804_, v___x_5824_);
v___x_5826_ = lean_nat_add(v_length_5805_, v___x_5822_);
lean_dec(v_length_5805_);
if (v_isShared_5808_ == 0)
{
lean_ctor_set(v___x_5807_, 5, v___x_5826_);
lean_ctor_set(v___x_5807_, 4, v___x_5825_);
lean_ctor_set(v___x_5807_, 3, v___x_5820_);
lean_ctor_set(v___x_5807_, 2, v___x_5819_);
lean_ctor_set(v___x_5807_, 1, v___x_5816_);
lean_ctor_set(v___x_5807_, 0, v___x_5811_);
v___x_5828_ = v___x_5807_;
goto v_reusejp_5827_;
}
else
{
lean_object* v_reuseFailAlloc_5839_; 
v_reuseFailAlloc_5839_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_5839_, 0, v___x_5811_);
lean_ctor_set(v_reuseFailAlloc_5839_, 1, v___x_5816_);
lean_ctor_set(v_reuseFailAlloc_5839_, 2, v___x_5819_);
lean_ctor_set(v_reuseFailAlloc_5839_, 3, v___x_5820_);
lean_ctor_set(v_reuseFailAlloc_5839_, 4, v___x_5825_);
lean_ctor_set(v_reuseFailAlloc_5839_, 5, v___x_5826_);
v___x_5828_ = v_reuseFailAlloc_5839_;
goto v_reusejp_5827_;
}
v_reusejp_5827_:
{
lean_object* v___x_5829_; lean_object* v___x_5831_; 
v___x_5829_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_addTrace_go_spec__4___redArg(v_sampleMap_5715_, v_fst_5713_, v_size_5809_);
if (v_isShared_5800_ == 0)
{
lean_ctor_set(v___x_5799_, 2, v___x_5828_);
v___x_5831_ = v___x_5799_;
goto v_reusejp_5830_;
}
else
{
lean_object* v_reuseFailAlloc_5838_; 
v_reuseFailAlloc_5838_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_5838_, 0, v_name_5788_);
lean_ctor_set(v_reuseFailAlloc_5838_, 1, v_processType_5789_);
lean_ctor_set(v_reuseFailAlloc_5838_, 2, v___x_5828_);
lean_ctor_set(v_reuseFailAlloc_5838_, 3, v_markers_5791_);
lean_ctor_set(v_reuseFailAlloc_5838_, 4, v_stackTable_5792_);
lean_ctor_set(v_reuseFailAlloc_5838_, 5, v_frameTable_5793_);
lean_ctor_set(v_reuseFailAlloc_5838_, 6, v_resourceTable_5794_);
lean_ctor_set(v_reuseFailAlloc_5838_, 7, v_nativeSymbols_5795_);
lean_ctor_set(v_reuseFailAlloc_5838_, 8, v_stringArray_5796_);
lean_ctor_set(v_reuseFailAlloc_5838_, 9, v_funcTable_5797_);
lean_ctor_set_uint8(v_reuseFailAlloc_5838_, sizeof(void*)*10, v_isMainThread_5790_);
v___x_5831_ = v_reuseFailAlloc_5838_;
goto v_reusejp_5830_;
}
v_reusejp_5830_:
{
lean_object* v___x_5833_; 
if (v_isShared_5787_ == 0)
{
lean_ctor_set(v___x_5786_, 0, v___x_5831_);
v___x_5833_ = v___x_5786_;
goto v_reusejp_5832_;
}
else
{
lean_object* v_reuseFailAlloc_5837_; 
v_reuseFailAlloc_5837_ = lean_alloc_ctor(0, 4, 8);
lean_ctor_set(v_reuseFailAlloc_5837_, 0, v___x_5831_);
lean_ctor_set(v_reuseFailAlloc_5837_, 1, v_stringMap_5781_);
lean_ctor_set(v_reuseFailAlloc_5837_, 2, v_funcMap_5782_);
lean_ctor_set(v_reuseFailAlloc_5837_, 3, v_stackMap_5783_);
lean_ctor_set_float(v_reuseFailAlloc_5837_, sizeof(void*)*4, v_lastTime_5784_);
v___x_5833_ = v_reuseFailAlloc_5837_;
goto v_reusejp_5832_;
}
v_reusejp_5832_:
{
lean_object* v___x_5835_; 
if (v_isShared_5718_ == 0)
{
lean_ctor_set(v___x_5717_, 1, v___x_5829_);
lean_ctor_set(v___x_5717_, 0, v___x_5833_);
v___x_5835_ = v___x_5717_;
goto v_reusejp_5834_;
}
else
{
lean_object* v_reuseFailAlloc_5836_; 
v_reuseFailAlloc_5836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5836_, 0, v___x_5833_);
lean_ctor_set(v_reuseFailAlloc_5836_, 1, v___x_5829_);
v___x_5835_ = v_reuseFailAlloc_5836_;
goto v_reusejp_5834_;
}
v_reusejp_5834_:
{
v_a_5700_ = v___x_5719_;
v_snd_5701_ = v___x_5835_;
goto v___jp_5699_;
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
v___jp_5699_:
{
lean_object* v___x_5702_; lean_object* v___x_5703_; 
v___x_5702_ = lean_unsigned_to_nat(1u);
v___x_5703_ = lean_nat_add(v_a_5696_, v___x_5702_);
lean_dec(v_a_5696_);
v_a_5696_ = v___x_5703_;
v_b_5697_ = v_a_5700_;
v___y_5698_ = v_snd_5701_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_collideThreads_collideSamples_spec__0___redArg___boxed(lean_object* v_upperBound_5847_, lean_object* v___x_5848_, lean_object* v_add_5849_, lean_object* v_a_5850_, lean_object* v_b_5851_, lean_object* v___y_5852_){
_start:
{
lean_object* v_res_5853_; 
v_res_5853_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_collideThreads_collideSamples_spec__0___redArg(v_upperBound_5847_, v___x_5848_, v_add_5849_, v_a_5850_, v_b_5851_, v___y_5852_);
lean_dec_ref(v_add_5849_);
lean_dec_ref(v___x_5848_);
lean_dec(v_upperBound_5847_);
return v_res_5853_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Profiler_0__Lean_Firefox_collideThreads_collideSamples(lean_object* v_add_5854_, lean_object* v_a_5855_){
_start:
{
lean_object* v_samples_5856_; lean_object* v_length_5857_; lean_object* v___x_5858_; lean_object* v___x_5859_; lean_object* v___x_5860_; lean_object* v_snd_5861_; lean_object* v___x_5863_; uint8_t v_isShared_5864_; uint8_t v_isSharedCheck_5868_; 
v_samples_5856_ = lean_ctor_get(v_add_5854_, 2);
v_length_5857_ = lean_ctor_get(v_samples_5856_, 5);
v___x_5858_ = lean_unsigned_to_nat(0u);
v___x_5859_ = lean_box(0);
v___x_5860_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_collideThreads_collideSamples_spec__0___redArg(v_length_5857_, v_samples_5856_, v_add_5854_, v___x_5858_, v___x_5859_, v_a_5855_);
v_snd_5861_ = lean_ctor_get(v___x_5860_, 1);
v_isSharedCheck_5868_ = !lean_is_exclusive(v___x_5860_);
if (v_isSharedCheck_5868_ == 0)
{
lean_object* v_unused_5869_; 
v_unused_5869_ = lean_ctor_get(v___x_5860_, 0);
lean_dec(v_unused_5869_);
v___x_5863_ = v___x_5860_;
v_isShared_5864_ = v_isSharedCheck_5868_;
goto v_resetjp_5862_;
}
else
{
lean_inc(v_snd_5861_);
lean_dec(v___x_5860_);
v___x_5863_ = lean_box(0);
v_isShared_5864_ = v_isSharedCheck_5868_;
goto v_resetjp_5862_;
}
v_resetjp_5862_:
{
lean_object* v___x_5866_; 
if (v_isShared_5864_ == 0)
{
lean_ctor_set(v___x_5863_, 0, v___x_5859_);
v___x_5866_ = v___x_5863_;
goto v_reusejp_5865_;
}
else
{
lean_object* v_reuseFailAlloc_5867_; 
v_reuseFailAlloc_5867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5867_, 0, v___x_5859_);
lean_ctor_set(v_reuseFailAlloc_5867_, 1, v_snd_5861_);
v___x_5866_ = v_reuseFailAlloc_5867_;
goto v_reusejp_5865_;
}
v_reusejp_5865_:
{
return v___x_5866_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Profiler_0__Lean_Firefox_collideThreads_collideSamples___boxed(lean_object* v_add_5870_, lean_object* v_a_5871_){
_start:
{
lean_object* v_res_5872_; 
v_res_5872_ = l___private_Lean_Util_Profiler_0__Lean_Firefox_collideThreads_collideSamples(v_add_5870_, v_a_5871_);
lean_dec_ref(v_add_5870_);
return v_res_5872_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_collideThreads_collideSamples_spec__0(lean_object* v_upperBound_5873_, lean_object* v___x_5874_, lean_object* v_add_5875_, lean_object* v_inst_5876_, lean_object* v_R_5877_, lean_object* v_a_5878_, lean_object* v_b_5879_, lean_object* v_c_5880_, lean_object* v___y_5881_){
_start:
{
lean_object* v___x_5882_; 
v___x_5882_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_collideThreads_collideSamples_spec__0___redArg(v_upperBound_5873_, v___x_5874_, v_add_5875_, v_a_5878_, v_b_5879_, v___y_5881_);
return v___x_5882_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_collideThreads_collideSamples_spec__0___boxed(lean_object* v_upperBound_5883_, lean_object* v___x_5884_, lean_object* v_add_5885_, lean_object* v_inst_5886_, lean_object* v_R_5887_, lean_object* v_a_5888_, lean_object* v_b_5889_, lean_object* v_c_5890_, lean_object* v___y_5891_){
_start:
{
lean_object* v_res_5892_; 
v_res_5892_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Util_Profiler_0__Lean_Firefox_collideThreads_collideSamples_spec__0(v_upperBound_5883_, v___x_5884_, v_add_5885_, v_inst_5886_, v_R_5887_, v_a_5888_, v_b_5889_, v_c_5890_, v___y_5891_);
lean_dec_ref(v_add_5885_);
lean_dec_ref(v___x_5884_);
lean_dec(v_upperBound_5883_);
return v_res_5892_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Profiler_0__Lean_Firefox_collideThreads(lean_object* v_thread_5893_, lean_object* v_add_5894_){
_start:
{
lean_object* v___x_5895_; lean_object* v_snd_5896_; 
v___x_5895_ = l___private_Lean_Util_Profiler_0__Lean_Firefox_collideThreads_collideSamples(v_add_5894_, v_thread_5893_);
v_snd_5896_ = lean_ctor_get(v___x_5895_, 1);
lean_inc(v_snd_5896_);
lean_dec_ref(v___x_5895_);
return v_snd_5896_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Profiler_0__Lean_Firefox_collideThreads___boxed(lean_object* v_thread_5897_, lean_object* v_add_5898_){
_start:
{
lean_object* v_res_5899_; 
v_res_5899_ = l___private_Lean_Util_Profiler_0__Lean_Firefox_collideThreads(v_thread_5897_, v_add_5898_);
lean_dec_ref(v_add_5898_);
return v_res_5899_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_collide_spec__1(size_t v_sz_5900_, size_t v_i_5901_, lean_object* v_bs_5902_){
_start:
{
uint8_t v___x_5903_; 
v___x_5903_ = lean_usize_dec_lt(v_i_5901_, v_sz_5900_);
if (v___x_5903_ == 0)
{
return v_bs_5902_;
}
else
{
lean_object* v_v_5904_; lean_object* v_threads_5905_; lean_object* v___x_5906_; lean_object* v_bs_x27_5907_; size_t v___x_5908_; size_t v___x_5909_; lean_object* v___x_5910_; 
v_v_5904_ = lean_array_uget_borrowed(v_bs_5902_, v_i_5901_);
v_threads_5905_ = lean_ctor_get(v_v_5904_, 2);
lean_inc_ref(v_threads_5905_);
v___x_5906_ = lean_unsigned_to_nat(0u);
v_bs_x27_5907_ = lean_array_uset(v_bs_5902_, v_i_5901_, v___x_5906_);
v___x_5908_ = ((size_t)1ULL);
v___x_5909_ = lean_usize_add(v_i_5901_, v___x_5908_);
v___x_5910_ = lean_array_uset(v_bs_x27_5907_, v_i_5901_, v_threads_5905_);
v_i_5901_ = v___x_5909_;
v_bs_5902_ = v___x_5910_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_collide_spec__1___boxed(lean_object* v_sz_5912_, lean_object* v_i_5913_, lean_object* v_bs_5914_){
_start:
{
size_t v_sz_boxed_5915_; size_t v_i_boxed_5916_; lean_object* v_res_5917_; 
v_sz_boxed_5915_ = lean_unbox_usize(v_sz_5912_);
lean_dec(v_sz_5912_);
v_i_boxed_5916_ = lean_unbox_usize(v_i_5913_);
lean_dec(v_i_5913_);
v_res_5917_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_collide_spec__1(v_sz_boxed_5915_, v_i_boxed_5916_, v_bs_5914_);
return v_res_5917_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Firefox_Profile_collide_spec__0(lean_object* v_as_5918_, size_t v_i_5919_, size_t v_stop_5920_, lean_object* v_b_5921_){
_start:
{
uint8_t v___x_5922_; 
v___x_5922_ = lean_usize_dec_eq(v_i_5919_, v_stop_5920_);
if (v___x_5922_ == 0)
{
lean_object* v___x_5923_; lean_object* v___x_5924_; size_t v___x_5925_; size_t v___x_5926_; 
v___x_5923_ = lean_array_uget_borrowed(v_as_5918_, v_i_5919_);
v___x_5924_ = l___private_Lean_Util_Profiler_0__Lean_Firefox_collideThreads(v_b_5921_, v___x_5923_);
v___x_5925_ = ((size_t)1ULL);
v___x_5926_ = lean_usize_add(v_i_5919_, v___x_5925_);
v_i_5919_ = v___x_5926_;
v_b_5921_ = v___x_5924_;
goto _start;
}
else
{
return v_b_5921_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Firefox_Profile_collide_spec__0___boxed(lean_object* v_as_5928_, lean_object* v_i_5929_, lean_object* v_stop_5930_, lean_object* v_b_5931_){
_start:
{
size_t v_i_boxed_5932_; size_t v_stop_boxed_5933_; lean_object* v_res_5934_; 
v_i_boxed_5932_ = lean_unbox_usize(v_i_5929_);
lean_dec(v_i_5929_);
v_stop_boxed_5933_ = lean_unbox_usize(v_stop_5930_);
lean_dec(v_stop_5930_);
v_res_5934_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Firefox_Profile_collide_spec__0(v_as_5928_, v_i_boxed_5932_, v_stop_boxed_5933_, v_b_5931_);
lean_dec_ref(v_as_5928_);
return v_res_5934_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Firefox_Profile_collide_spec__2(lean_object* v_as_5935_, size_t v_i_5936_, size_t v_stop_5937_, lean_object* v_b_5938_){
_start:
{
uint8_t v___x_5939_; 
v___x_5939_ = lean_usize_dec_eq(v_i_5936_, v_stop_5937_);
if (v___x_5939_ == 0)
{
lean_object* v___x_5940_; lean_object* v___x_5941_; size_t v___x_5942_; size_t v___x_5943_; 
v___x_5940_ = lean_array_uget_borrowed(v_as_5935_, v_i_5936_);
v___x_5941_ = l_Array_append___redArg(v_b_5938_, v___x_5940_);
v___x_5942_ = ((size_t)1ULL);
v___x_5943_ = lean_usize_add(v_i_5936_, v___x_5942_);
v_i_5936_ = v___x_5943_;
v_b_5938_ = v___x_5941_;
goto _start;
}
else
{
return v_b_5938_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Firefox_Profile_collide_spec__2___boxed(lean_object* v_as_5945_, lean_object* v_i_5946_, lean_object* v_stop_5947_, lean_object* v_b_5948_){
_start:
{
size_t v_i_boxed_5949_; size_t v_stop_boxed_5950_; lean_object* v_res_5951_; 
v_i_boxed_5949_ = lean_unbox_usize(v_i_5946_);
lean_dec(v_i_5946_);
v_stop_boxed_5950_ = lean_unbox_usize(v_stop_5947_);
lean_dec(v_stop_5947_);
v_res_5951_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Firefox_Profile_collide_spec__2(v_as_5945_, v_i_boxed_5949_, v_stop_boxed_5950_, v_b_5948_);
lean_dec_ref(v_as_5945_);
return v_res_5951_;
}
}
static lean_object* _init_l_Lean_Firefox_Profile_collide___closed__1(void){
_start:
{
lean_object* v___x_5953_; lean_object* v___x_5954_; 
v___x_5953_ = ((lean_object*)(l_Lean_Firefox_Profile_collide___closed__0));
v___x_5954_ = l_Lean_Firefox_Thread_new(v___x_5953_);
return v___x_5954_;
}
}
static lean_object* _init_l_Lean_Firefox_Profile_collide___closed__2(void){
_start:
{
double v___x_5955_; lean_object* v___x_5956_; lean_object* v___x_5957_; lean_object* v___x_5958_; 
v___x_5955_ = lean_float_once(&l___private_Lean_Util_Profiler_0__Lean_Firefox_getFirstStart_x3f___closed__0, &l___private_Lean_Util_Profiler_0__Lean_Firefox_getFirstStart_x3f___closed__0_once, _init_l___private_Lean_Util_Profiler_0__Lean_Firefox_getFirstStart_x3f___closed__0);
v___x_5956_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__7___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__7___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__7___closed__7);
v___x_5957_ = lean_obj_once(&l_Lean_Firefox_Profile_collide___closed__1, &l_Lean_Firefox_Profile_collide___closed__1_once, _init_l_Lean_Firefox_Profile_collide___closed__1);
v___x_5958_ = lean_alloc_ctor(0, 4, 8);
lean_ctor_set(v___x_5958_, 0, v___x_5957_);
lean_ctor_set(v___x_5958_, 1, v___x_5956_);
lean_ctor_set(v___x_5958_, 2, v___x_5956_);
lean_ctor_set(v___x_5958_, 3, v___x_5956_);
lean_ctor_set_float(v___x_5958_, sizeof(void*)*4, v___x_5955_);
return v___x_5958_;
}
}
static lean_object* _init_l_Lean_Firefox_Profile_collide___closed__3(void){
_start:
{
lean_object* v___x_5959_; lean_object* v___x_5960_; lean_object* v___x_5961_; 
v___x_5959_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__7___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__7___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_export_spec__7___closed__7);
v___x_5960_ = lean_obj_once(&l_Lean_Firefox_Profile_collide___closed__2, &l_Lean_Firefox_Profile_collide___closed__2_once, _init_l_Lean_Firefox_Profile_collide___closed__2);
v___x_5961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5961_, 0, v___x_5960_);
lean_ctor_set(v___x_5961_, 1, v___x_5959_);
return v___x_5961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Firefox_Profile_collide(lean_object* v_ps_5964_){
_start:
{
lean_object* v___x_5965_; lean_object* v___x_5966_; uint8_t v___x_5967_; 
v___x_5965_ = lean_unsigned_to_nat(0u);
v___x_5966_ = lean_array_get_size(v_ps_5964_);
v___x_5967_ = lean_nat_dec_lt(v___x_5965_, v___x_5966_);
if (v___x_5967_ == 0)
{
lean_object* v___x_5968_; 
lean_dec_ref(v_ps_5964_);
v___x_5968_ = lean_box(0);
return v___x_5968_;
}
else
{
lean_object* v___x_5969_; lean_object* v___y_5971_; lean_object* v___x_5988_; lean_object* v___y_5990_; size_t v_sz_5996_; size_t v___x_5997_; lean_object* v___x_5998_; lean_object* v___x_5999_; lean_object* v___x_6000_; uint8_t v___x_6001_; 
v___x_5969_ = lean_array_fget(v_ps_5964_, v___x_5965_);
v___x_5988_ = lean_obj_once(&l_Lean_Firefox_Profile_collide___closed__3, &l_Lean_Firefox_Profile_collide___closed__3_once, _init_l_Lean_Firefox_Profile_collide___closed__3);
v_sz_5996_ = lean_array_size(v_ps_5964_);
v___x_5997_ = ((size_t)0ULL);
v___x_5998_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Firefox_Profile_collide_spec__1(v_sz_5996_, v___x_5997_, v_ps_5964_);
v___x_5999_ = ((lean_object*)(l_Lean_Firefox_Profile_collide___closed__4));
v___x_6000_ = lean_array_get_size(v___x_5998_);
v___x_6001_ = lean_nat_dec_lt(v___x_5965_, v___x_6000_);
if (v___x_6001_ == 0)
{
lean_dec_ref(v___x_5998_);
v___y_5990_ = v___x_5999_;
goto v___jp_5989_;
}
else
{
size_t v___x_6002_; lean_object* v___x_6003_; 
v___x_6002_ = lean_usize_of_nat(v___x_6000_);
v___x_6003_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Firefox_Profile_collide_spec__2(v___x_5998_, v___x_5997_, v___x_6002_, v___x_5999_);
lean_dec_ref(v___x_5998_);
v___y_5990_ = v___x_6003_;
goto v___jp_5989_;
}
v___jp_5970_:
{
lean_object* v_toThreadWithMaps_5972_; lean_object* v_meta_5973_; lean_object* v_libs_5974_; lean_object* v___x_5976_; uint8_t v_isShared_5977_; uint8_t v_isSharedCheck_5986_; 
v_toThreadWithMaps_5972_ = lean_ctor_get(v___y_5971_, 0);
lean_inc_ref(v_toThreadWithMaps_5972_);
lean_dec_ref(v___y_5971_);
v_meta_5973_ = lean_ctor_get(v___x_5969_, 0);
v_libs_5974_ = lean_ctor_get(v___x_5969_, 1);
v_isSharedCheck_5986_ = !lean_is_exclusive(v___x_5969_);
if (v_isSharedCheck_5986_ == 0)
{
lean_object* v_unused_5987_; 
v_unused_5987_ = lean_ctor_get(v___x_5969_, 2);
lean_dec(v_unused_5987_);
v___x_5976_ = v___x_5969_;
v_isShared_5977_ = v_isSharedCheck_5986_;
goto v_resetjp_5975_;
}
else
{
lean_inc(v_libs_5974_);
lean_inc(v_meta_5973_);
lean_dec(v___x_5969_);
v___x_5976_ = lean_box(0);
v_isShared_5977_ = v_isSharedCheck_5986_;
goto v_resetjp_5975_;
}
v_resetjp_5975_:
{
lean_object* v_toThread_5978_; lean_object* v___x_5979_; lean_object* v___x_5980_; lean_object* v___x_5981_; lean_object* v___x_5983_; 
v_toThread_5978_ = lean_ctor_get(v_toThreadWithMaps_5972_, 0);
lean_inc_ref(v_toThread_5978_);
lean_dec_ref(v_toThreadWithMaps_5972_);
v___x_5979_ = lean_unsigned_to_nat(1u);
v___x_5980_ = lean_mk_empty_array_with_capacity(v___x_5979_);
v___x_5981_ = lean_array_push(v___x_5980_, v_toThread_5978_);
if (v_isShared_5977_ == 0)
{
lean_ctor_set(v___x_5976_, 2, v___x_5981_);
v___x_5983_ = v___x_5976_;
goto v_reusejp_5982_;
}
else
{
lean_object* v_reuseFailAlloc_5985_; 
v_reuseFailAlloc_5985_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5985_, 0, v_meta_5973_);
lean_ctor_set(v_reuseFailAlloc_5985_, 1, v_libs_5974_);
lean_ctor_set(v_reuseFailAlloc_5985_, 2, v___x_5981_);
v___x_5983_ = v_reuseFailAlloc_5985_;
goto v_reusejp_5982_;
}
v_reusejp_5982_:
{
lean_object* v___x_5984_; 
v___x_5984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5984_, 0, v___x_5983_);
return v___x_5984_;
}
}
}
v___jp_5989_:
{
lean_object* v___x_5991_; uint8_t v___x_5992_; 
v___x_5991_ = lean_array_get_size(v___y_5990_);
v___x_5992_ = lean_nat_dec_lt(v___x_5965_, v___x_5991_);
if (v___x_5992_ == 0)
{
lean_dec_ref(v___y_5990_);
v___y_5971_ = v___x_5988_;
goto v___jp_5970_;
}
else
{
size_t v___x_5993_; size_t v___x_5994_; lean_object* v___x_5995_; 
v___x_5993_ = ((size_t)0ULL);
v___x_5994_ = lean_usize_of_nat(v___x_5991_);
v___x_5995_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Firefox_Profile_collide_spec__0(v___y_5990_, v___x_5993_, v___x_5994_, v___x_5988_);
lean_dec_ref(v___y_5990_);
v___y_5971_ = v___x_5995_;
goto v___jp_5970_;
}
}
}
}
}
lean_object* runtime_initialize_Lean_Util_Trace(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Util_Profiler(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Util_Trace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Firefox_instInhabitedMilliseconds_default = _init_l_Lean_Firefox_instInhabitedMilliseconds_default();
l_Lean_Firefox_instInhabitedMilliseconds = _init_l_Lean_Firefox_instInhabitedMilliseconds();
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
res = initialize_Lean_Util_Trace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_Profiler(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Util_Profiler(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Util_Profiler(builtin);
}
#ifdef __cplusplus
}
#endif

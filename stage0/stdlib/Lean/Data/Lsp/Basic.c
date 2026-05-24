// Lean compiler output
// Module: Lean.Data.Lsp.Basic
// Imports: public import Lean.Data.Json public import Lean.Data.Lsp.BasicAux public import Init.Data.Option.Coe
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
lean_object* l_Lean_Lsp_instFromJsonRange_fromJson(lean_object*);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
lean_object* l_Lean_Json_getNat_x3f(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Json_getObjVal_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Json_getBool_x3f(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Lsp_instToJsonRange_toJson(lean_object*);
lean_object* l_Lean_Json_setObjVal_x21(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_JsonNumber_fromNat(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint64_t lean_string_hash(lean_object*);
lean_object* l_Lean_Lsp_instToJsonPosition_toJson(lean_object*);
lean_object* l_String_compare___boxed(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Lsp_instFromJsonPosition_fromJson(lean_object*);
lean_object* l_Array_fromJson_x3f(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Json_getObj_x3f(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* l_Lean_Lsp_instInhabitedRange_default;
uint8_t lean_string_compare(lean_object*, lean_object*);
uint8_t l_Lean_Lsp_instOrdRange_ord(lean_object*, lean_object*);
lean_object* l_Array_toJson(lean_object*, lean_object*, lean_object*);
lean_object* l_id___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_foldl___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Lsp_instBEqRange_beq(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instInhabitedLocation_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_Lsp_instInhabitedLocation_default___closed__0 = (const lean_object*)&l_Lean_Lsp_instInhabitedLocation_default___closed__0_value;
static lean_once_cell_t l_Lean_Lsp_instInhabitedLocation_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instInhabitedLocation_default___closed__1;
LEAN_EXPORT lean_object* l_Lean_Lsp_instInhabitedLocation_default;
LEAN_EXPORT lean_object* l_Lean_Lsp_instInhabitedLocation;
LEAN_EXPORT uint8_t l_Lean_Lsp_instBEqLocation_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqLocation_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_instBEqLocation___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instBEqLocation_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instBEqLocation___closed__0 = (const lean_object*)&l_Lean_Lsp_instBEqLocation___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instBEqLocation = (const lean_object*)&l_Lean_Lsp_instBEqLocation___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLocation_toJson_spec__0(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instToJsonLocation_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "uri"};
static const lean_object* l_Lean_Lsp_instToJsonLocation_toJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonLocation_toJson___closed__0_value;
static const lean_string_object l_Lean_Lsp_instToJsonLocation_toJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "range"};
static const lean_object* l_Lean_Lsp_instToJsonLocation_toJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instToJsonLocation_toJson___closed__1_value;
static const lean_array_object l_Lean_Lsp_instToJsonLocation_toJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Lsp_instToJsonLocation_toJson___closed__2 = (const lean_object*)&l_Lean_Lsp_instToJsonLocation_toJson___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLocation_toJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonLocation___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonLocation_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonLocation___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonLocation___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonLocation = (const lean_object*)&l_Lean_Lsp_instToJsonLocation___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocation_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocation_fromJson_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocation_fromJson_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocation_fromJson_spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instFromJsonLocation_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Lsp_instFromJsonLocation_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonLocation_fromJson___closed__0_value;
static const lean_string_object l_Lean_Lsp_instFromJsonLocation_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Lsp"};
static const lean_object* l_Lean_Lsp_instFromJsonLocation_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonLocation_fromJson___closed__1_value;
static const lean_string_object l_Lean_Lsp_instFromJsonLocation_fromJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Location"};
static const lean_object* l_Lean_Lsp_instFromJsonLocation_fromJson___closed__2 = (const lean_object*)&l_Lean_Lsp_instFromJsonLocation_fromJson___closed__2_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonLocation_fromJson___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonLocation_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonLocation_fromJson___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonLocation_fromJson___closed__3_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonLocation_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonLocation_fromJson___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonLocation_fromJson___closed__3_value_aux_1),((lean_object*)&l_Lean_Lsp_instFromJsonLocation_fromJson___closed__2_value),LEAN_SCALAR_PTR_LITERAL(12, 37, 85, 10, 186, 200, 38, 42)}};
static const lean_object* l_Lean_Lsp_instFromJsonLocation_fromJson___closed__3 = (const lean_object*)&l_Lean_Lsp_instFromJsonLocation_fromJson___closed__3_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLocation_fromJson___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLocation_fromJson___closed__4;
static const lean_string_object l_Lean_Lsp_instFromJsonLocation_fromJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lean_Lsp_instFromJsonLocation_fromJson___closed__5 = (const lean_object*)&l_Lean_Lsp_instFromJsonLocation_fromJson___closed__5_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLocation_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLocation_fromJson___closed__6;
static const lean_ctor_object l_Lean_Lsp_instFromJsonLocation_fromJson___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instToJsonLocation_toJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(102, 169, 49, 149, 57, 117, 3, 84)}};
static const lean_object* l_Lean_Lsp_instFromJsonLocation_fromJson___closed__7 = (const lean_object*)&l_Lean_Lsp_instFromJsonLocation_fromJson___closed__7_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLocation_fromJson___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLocation_fromJson___closed__8;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLocation_fromJson___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLocation_fromJson___closed__9;
static const lean_string_object l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10 = (const lean_object*)&l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLocation_fromJson___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLocation_fromJson___closed__11;
static const lean_ctor_object l_Lean_Lsp_instFromJsonLocation_fromJson___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instToJsonLocation_toJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(113, 10, 234, 83, 106, 95, 218, 176)}};
static const lean_object* l_Lean_Lsp_instFromJsonLocation_fromJson___closed__12 = (const lean_object*)&l_Lean_Lsp_instFromJsonLocation_fromJson___closed__12_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLocation_fromJson___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLocation_fromJson___closed__13;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLocation_fromJson___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLocation_fromJson___closed__14;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLocation_fromJson___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLocation_fromJson___closed__15;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLocation_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonLocation___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonLocation_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonLocation___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonLocation___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonLocation = (const lean_object*)&l_Lean_Lsp_instFromJsonLocation___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Lsp_instOrdLocation_ord(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instOrdLocation_ord___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_instOrdLocation___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instOrdLocation_ord___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instOrdLocation___closed__0 = (const lean_object*)&l_Lean_Lsp_instOrdLocation___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instOrdLocation = (const lean_object*)&l_Lean_Lsp_instOrdLocation___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLocationLink_toJson_spec__0(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instToJsonLocationLink_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "originSelectionRange"};
static const lean_object* l_Lean_Lsp_instToJsonLocationLink_toJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonLocationLink_toJson___closed__0_value;
static const lean_string_object l_Lean_Lsp_instToJsonLocationLink_toJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "targetUri"};
static const lean_object* l_Lean_Lsp_instToJsonLocationLink_toJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instToJsonLocationLink_toJson___closed__1_value;
static const lean_string_object l_Lean_Lsp_instToJsonLocationLink_toJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "targetRange"};
static const lean_object* l_Lean_Lsp_instToJsonLocationLink_toJson___closed__2 = (const lean_object*)&l_Lean_Lsp_instToJsonLocationLink_toJson___closed__2_value;
static const lean_string_object l_Lean_Lsp_instToJsonLocationLink_toJson___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "targetSelectionRange"};
static const lean_object* l_Lean_Lsp_instToJsonLocationLink_toJson___closed__3 = (const lean_object*)&l_Lean_Lsp_instToJsonLocationLink_toJson___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLocationLink_toJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonLocationLink___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonLocationLink_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonLocationLink___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonLocationLink___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonLocationLink = (const lean_object*)&l_Lean_Lsp_instToJsonLocationLink___closed__0_value;
static const lean_ctor_object l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocationLink_fromJson_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocationLink_fromJson_spec__0_spec__0___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocationLink_fromJson_spec__0_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocationLink_fromJson_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocationLink_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocationLink_fromJson_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "LocationLink"};
static const lean_object* l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonLocation_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__1_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonLocation_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__1_value_aux_1),((lean_object*)&l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(140, 124, 242, 62, 124, 12, 27, 89)}};
static const lean_object* l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__1_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__2;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__3;
static const lean_string_object l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "originSelectionRange\?"};
static const lean_object* l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__4 = (const lean_object*)&l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__4_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__4_value),LEAN_SCALAR_PTR_LITERAL(113, 74, 194, 55, 146, 231, 63, 35)}};
static const lean_object* l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__5 = (const lean_object*)&l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__5_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__6;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__7;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__8;
static const lean_ctor_object l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instToJsonLocationLink_toJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(175, 177, 170, 233, 220, 50, 208, 212)}};
static const lean_object* l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__9 = (const lean_object*)&l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__9_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__10;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__11;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__12;
static const lean_ctor_object l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instToJsonLocationLink_toJson___closed__2_value),LEAN_SCALAR_PTR_LITERAL(45, 64, 248, 134, 128, 146, 245, 203)}};
static const lean_object* l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__13 = (const lean_object*)&l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__13_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__14;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__15;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__16;
static const lean_ctor_object l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instToJsonLocationLink_toJson___closed__3_value),LEAN_SCALAR_PTR_LITERAL(152, 179, 191, 7, 212, 29, 154, 211)}};
static const lean_object* l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__17 = (const lean_object*)&l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__17_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__18;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__19;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__20;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLocationLink_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonLocationLink___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonLocationLink_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonLocationLink___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonLocationLink___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonLocationLink = (const lean_object*)&l_Lean_Lsp_instFromJsonLocationLink___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonCommand_toJson_spec__0_spec__0_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonCommand_toJson_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonCommand_toJson_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonCommand_toJson_spec__0(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instToJsonCommand_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "title"};
static const lean_object* l_Lean_Lsp_instToJsonCommand_toJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonCommand_toJson___closed__0_value;
static const lean_string_object l_Lean_Lsp_instToJsonCommand_toJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "command"};
static const lean_object* l_Lean_Lsp_instToJsonCommand_toJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instToJsonCommand_toJson___closed__1_value;
static const lean_string_object l_Lean_Lsp_instToJsonCommand_toJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "arguments"};
static const lean_object* l_Lean_Lsp_instToJsonCommand_toJson___closed__2 = (const lean_object*)&l_Lean_Lsp_instToJsonCommand_toJson___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonCommand_toJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonCommand___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonCommand_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonCommand___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonCommand___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonCommand = (const lean_object*)&l_Lean_Lsp_instToJsonCommand___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCommand_fromJson_spec__0_spec__0_spec__1_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCommand_fromJson_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCommand_fromJson_spec__0_spec__0_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "expected JSON array, got '"};
static const lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCommand_fromJson_spec__0_spec__0_spec__1___closed__0 = (const lean_object*)&l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCommand_fromJson_spec__0_spec__0_spec__1___closed__0_value;
static const lean_string_object l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCommand_fromJson_spec__0_spec__0_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCommand_fromJson_spec__0_spec__0_spec__1___closed__1 = (const lean_object*)&l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCommand_fromJson_spec__0_spec__0_spec__1___closed__1_value;
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCommand_fromJson_spec__0_spec__0_spec__1(lean_object*);
static const lean_ctor_object l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCommand_fromJson_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCommand_fromJson_spec__0_spec__0___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCommand_fromJson_spec__0_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCommand_fromJson_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCommand_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCommand_fromJson_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instFromJsonCommand_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_Lsp_instFromJsonCommand_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonCommand_fromJson___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonCommand_fromJson___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonLocation_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonCommand_fromJson___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonCommand_fromJson___closed__1_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonLocation_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonCommand_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonCommand_fromJson___closed__1_value_aux_1),((lean_object*)&l_Lean_Lsp_instFromJsonCommand_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(167, 221, 30, 152, 116, 110, 187, 228)}};
static const lean_object* l_Lean_Lsp_instFromJsonCommand_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonCommand_fromJson___closed__1_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonCommand_fromJson___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonCommand_fromJson___closed__2;
static lean_once_cell_t l_Lean_Lsp_instFromJsonCommand_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonCommand_fromJson___closed__3;
static const lean_ctor_object l_Lean_Lsp_instFromJsonCommand_fromJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instToJsonCommand_toJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(251, 99, 171, 63, 21, 188, 124, 202)}};
static const lean_object* l_Lean_Lsp_instFromJsonCommand_fromJson___closed__4 = (const lean_object*)&l_Lean_Lsp_instFromJsonCommand_fromJson___closed__4_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonCommand_fromJson___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonCommand_fromJson___closed__5;
static lean_once_cell_t l_Lean_Lsp_instFromJsonCommand_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonCommand_fromJson___closed__6;
static lean_once_cell_t l_Lean_Lsp_instFromJsonCommand_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonCommand_fromJson___closed__7;
static const lean_ctor_object l_Lean_Lsp_instFromJsonCommand_fromJson___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instToJsonCommand_toJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(29, 69, 134, 125, 237, 175, 69, 70)}};
static const lean_object* l_Lean_Lsp_instFromJsonCommand_fromJson___closed__8 = (const lean_object*)&l_Lean_Lsp_instFromJsonCommand_fromJson___closed__8_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonCommand_fromJson___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonCommand_fromJson___closed__9;
static lean_once_cell_t l_Lean_Lsp_instFromJsonCommand_fromJson___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonCommand_fromJson___closed__10;
static lean_once_cell_t l_Lean_Lsp_instFromJsonCommand_fromJson___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonCommand_fromJson___closed__11;
static const lean_string_object l_Lean_Lsp_instFromJsonCommand_fromJson___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "arguments\?"};
static const lean_object* l_Lean_Lsp_instFromJsonCommand_fromJson___closed__12 = (const lean_object*)&l_Lean_Lsp_instFromJsonCommand_fromJson___closed__12_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonCommand_fromJson___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonCommand_fromJson___closed__12_value),LEAN_SCALAR_PTR_LITERAL(221, 101, 169, 240, 246, 136, 10, 251)}};
static const lean_object* l_Lean_Lsp_instFromJsonCommand_fromJson___closed__13 = (const lean_object*)&l_Lean_Lsp_instFromJsonCommand_fromJson___closed__13_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonCommand_fromJson___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonCommand_fromJson___closed__14;
static lean_once_cell_t l_Lean_Lsp_instFromJsonCommand_fromJson___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonCommand_fromJson___closed__15;
static lean_once_cell_t l_Lean_Lsp_instFromJsonCommand_fromJson___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonCommand_fromJson___closed__16;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonCommand_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonCommand___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonCommand_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonCommand___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonCommand___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonCommand = (const lean_object*)&l_Lean_Lsp_instFromJsonCommand___closed__0_value;
static const lean_string_object l_Lean_Lsp_instToJsonSnippetString_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "value"};
static const lean_object* l_Lean_Lsp_instToJsonSnippetString_toJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonSnippetString_toJson___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonSnippetString_toJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonSnippetString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonSnippetString_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonSnippetString___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonSnippetString___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonSnippetString = (const lean_object*)&l_Lean_Lsp_instToJsonSnippetString___closed__0_value;
static const lean_string_object l_Lean_Lsp_instFromJsonSnippetString_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "SnippetString"};
static const lean_object* l_Lean_Lsp_instFromJsonSnippetString_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonSnippetString_fromJson___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonSnippetString_fromJson___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonLocation_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonSnippetString_fromJson___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonSnippetString_fromJson___closed__1_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonLocation_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonSnippetString_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonSnippetString_fromJson___closed__1_value_aux_1),((lean_object*)&l_Lean_Lsp_instFromJsonSnippetString_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(125, 167, 3, 44, 46, 125, 236, 78)}};
static const lean_object* l_Lean_Lsp_instFromJsonSnippetString_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonSnippetString_fromJson___closed__1_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonSnippetString_fromJson___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonSnippetString_fromJson___closed__2;
static lean_once_cell_t l_Lean_Lsp_instFromJsonSnippetString_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonSnippetString_fromJson___closed__3;
static const lean_ctor_object l_Lean_Lsp_instFromJsonSnippetString_fromJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instToJsonSnippetString_toJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(197, 65, 47, 208, 134, 160, 30, 25)}};
static const lean_object* l_Lean_Lsp_instFromJsonSnippetString_fromJson___closed__4 = (const lean_object*)&l_Lean_Lsp_instFromJsonSnippetString_fromJson___closed__4_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonSnippetString_fromJson___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonSnippetString_fromJson___closed__5;
static lean_once_cell_t l_Lean_Lsp_instFromJsonSnippetString_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonSnippetString_fromJson___closed__6;
static lean_once_cell_t l_Lean_Lsp_instFromJsonSnippetString_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonSnippetString_fromJson___closed__7;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonSnippetString_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonSnippetString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonSnippetString_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonSnippetString___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonSnippetString___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonSnippetString = (const lean_object*)&l_Lean_Lsp_instFromJsonSnippetString___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextEdit_toJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextEdit_toJson_spec__1(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instToJsonTextEdit_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "newText"};
static const lean_object* l_Lean_Lsp_instToJsonTextEdit_toJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonTextEdit_toJson___closed__0_value;
static const lean_string_object l_Lean_Lsp_instToJsonTextEdit_toJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "leanExtSnippet"};
static const lean_object* l_Lean_Lsp_instToJsonTextEdit_toJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instToJsonTextEdit_toJson___closed__1_value;
static const lean_string_object l_Lean_Lsp_instToJsonTextEdit_toJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "annotationId"};
static const lean_object* l_Lean_Lsp_instToJsonTextEdit_toJson___closed__2 = (const lean_object*)&l_Lean_Lsp_instToJsonTextEdit_toJson___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonTextEdit_toJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonTextEdit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonTextEdit_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonTextEdit___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonTextEdit___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonTextEdit = (const lean_object*)&l_Lean_Lsp_instToJsonTextEdit___closed__0_value;
static const lean_ctor_object l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextEdit_fromJson_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextEdit_fromJson_spec__0_spec__0___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextEdit_fromJson_spec__0_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextEdit_fromJson_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextEdit_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextEdit_fromJson_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextEdit_fromJson_spec__1_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextEdit_fromJson_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextEdit_fromJson_spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "TextEdit"};
static const lean_object* l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonLocation_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__1_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonLocation_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__1_value_aux_1),((lean_object*)&l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(244, 98, 67, 125, 163, 99, 155, 129)}};
static const lean_object* l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__1_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__2;
static lean_once_cell_t l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__3;
static lean_once_cell_t l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__4;
static lean_once_cell_t l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__5;
static const lean_ctor_object l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instToJsonTextEdit_toJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(220, 243, 28, 135, 144, 87, 14, 78)}};
static const lean_object* l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__6 = (const lean_object*)&l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__6_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__7;
static lean_once_cell_t l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__8;
static lean_once_cell_t l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__9;
static const lean_string_object l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "leanExtSnippet\?"};
static const lean_object* l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__10 = (const lean_object*)&l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__10_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__10_value),LEAN_SCALAR_PTR_LITERAL(177, 115, 84, 239, 31, 238, 106, 122)}};
static const lean_object* l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__11 = (const lean_object*)&l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__11_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__12;
static lean_once_cell_t l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__13;
static lean_once_cell_t l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__14;
static const lean_string_object l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "annotationId\?"};
static const lean_object* l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__15 = (const lean_object*)&l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__15_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__15_value),LEAN_SCALAR_PTR_LITERAL(37, 162, 73, 47, 154, 76, 17, 22)}};
static const lean_object* l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__16 = (const lean_object*)&l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__16_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__17;
static lean_once_cell_t l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__18;
static lean_once_cell_t l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__19;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonTextEdit_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonTextEdit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonTextEdit_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonTextEdit___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonTextEdit___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonTextEdit = (const lean_object*)&l_Lean_Lsp_instFromJsonTextEdit___closed__0_value;
static const lean_closure_object l_Lean_Lsp_instFromJsonTextEditBatch___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Array_fromJson_x3f, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonTextEdit___closed__0_value)} };
static const lean_object* l_Lean_Lsp_instFromJsonTextEditBatch___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonTextEditBatch___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonTextEditBatch = (const lean_object*)&l_Lean_Lsp_instFromJsonTextEditBatch___closed__0_value;
static const lean_closure_object l_Lean_Lsp_instToJsonTextEditBatch___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Array_toJson, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instToJsonTextEdit___closed__0_value)} };
static const lean_object* l_Lean_Lsp_instToJsonTextEditBatch___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonTextEditBatch___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonTextEditBatch = (const lean_object*)&l_Lean_Lsp_instToJsonTextEditBatch___closed__0_value;
static const lean_array_object l_Lean_Lsp_instEmptyCollectionTextEditBatch___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Lsp_instEmptyCollectionTextEditBatch___closed__0 = (const lean_object*)&l_Lean_Lsp_instEmptyCollectionTextEditBatch___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instEmptyCollectionTextEditBatch = (const lean_object*)&l_Lean_Lsp_instEmptyCollectionTextEditBatch___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instAppendTextEditBatch___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instAppendTextEditBatch___aux__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_instAppendTextEditBatch___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instAppendTextEditBatch___aux__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instAppendTextEditBatch___closed__0 = (const lean_object*)&l_Lean_Lsp_instAppendTextEditBatch___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instAppendTextEditBatch = (const lean_object*)&l_Lean_Lsp_instAppendTextEditBatch___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instCoeTextEditTextEditBatch___lam__0(lean_object*);
static const lean_closure_object l_Lean_Lsp_instCoeTextEditTextEditBatch___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instCoeTextEditTextEditBatch___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instCoeTextEditTextEditBatch___closed__0 = (const lean_object*)&l_Lean_Lsp_instCoeTextEditTextEditBatch___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instCoeTextEditTextEditBatch = (const lean_object*)&l_Lean_Lsp_instCoeTextEditTextEditBatch___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonTextDocumentIdentifier_toJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonTextDocumentIdentifier___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonTextDocumentIdentifier_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonTextDocumentIdentifier___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonTextDocumentIdentifier___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonTextDocumentIdentifier = (const lean_object*)&l_Lean_Lsp_instToJsonTextDocumentIdentifier___closed__0_value;
static const lean_string_object l_Lean_Lsp_instFromJsonTextDocumentIdentifier_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "TextDocumentIdentifier"};
static const lean_object* l_Lean_Lsp_instFromJsonTextDocumentIdentifier_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentIdentifier_fromJson___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonTextDocumentIdentifier_fromJson___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonLocation_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonTextDocumentIdentifier_fromJson___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentIdentifier_fromJson___closed__1_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonLocation_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonTextDocumentIdentifier_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentIdentifier_fromJson___closed__1_value_aux_1),((lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentIdentifier_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(81, 38, 97, 8, 168, 165, 246, 123)}};
static const lean_object* l_Lean_Lsp_instFromJsonTextDocumentIdentifier_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentIdentifier_fromJson___closed__1_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonTextDocumentIdentifier_fromJson___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonTextDocumentIdentifier_fromJson___closed__2;
static lean_once_cell_t l_Lean_Lsp_instFromJsonTextDocumentIdentifier_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonTextDocumentIdentifier_fromJson___closed__3;
static lean_once_cell_t l_Lean_Lsp_instFromJsonTextDocumentIdentifier_fromJson___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonTextDocumentIdentifier_fromJson___closed__4;
static lean_once_cell_t l_Lean_Lsp_instFromJsonTextDocumentIdentifier_fromJson___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonTextDocumentIdentifier_fromJson___closed__5;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonTextDocumentIdentifier_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonTextDocumentIdentifier___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonTextDocumentIdentifier_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonTextDocumentIdentifier___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentIdentifier___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonTextDocumentIdentifier = (const lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentIdentifier___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonVersionedTextDocumentIdentifier_toJson_spec__0(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instToJsonVersionedTextDocumentIdentifier_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "version"};
static const lean_object* l_Lean_Lsp_instToJsonVersionedTextDocumentIdentifier_toJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonVersionedTextDocumentIdentifier_toJson___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonVersionedTextDocumentIdentifier_toJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonVersionedTextDocumentIdentifier___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonVersionedTextDocumentIdentifier_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonVersionedTextDocumentIdentifier___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonVersionedTextDocumentIdentifier___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonVersionedTextDocumentIdentifier = (const lean_object*)&l_Lean_Lsp_instToJsonVersionedTextDocumentIdentifier___closed__0_value;
static const lean_ctor_object l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson_spec__0_spec__0___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson_spec__0_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "VersionedTextDocumentIdentifier"};
static const lean_object* l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonLocation_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__1_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonLocation_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__1_value_aux_1),((lean_object*)&l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(240, 213, 117, 64, 157, 88, 14, 128)}};
static const lean_object* l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__1_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__2;
static lean_once_cell_t l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__3;
static lean_once_cell_t l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__4;
static lean_once_cell_t l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__5;
static const lean_string_object l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "version\?"};
static const lean_object* l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__6 = (const lean_object*)&l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__6_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__6_value),LEAN_SCALAR_PTR_LITERAL(251, 148, 229, 74, 154, 149, 54, 79)}};
static const lean_object* l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__7 = (const lean_object*)&l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__7_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__8;
static lean_once_cell_t l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__9;
static lean_once_cell_t l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__10;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier = (const lean_object*)&l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonTextDocumentEdit_toJson_spec__0_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonTextDocumentEdit_toJson_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Lsp_instToJsonTextDocumentEdit_toJson_spec__0(lean_object*);
static const lean_string_object l_Lean_Lsp_instToJsonTextDocumentEdit_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "textDocument"};
static const lean_object* l_Lean_Lsp_instToJsonTextDocumentEdit_toJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonTextDocumentEdit_toJson___closed__0_value;
static const lean_string_object l_Lean_Lsp_instToJsonTextDocumentEdit_toJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "edits"};
static const lean_object* l_Lean_Lsp_instToJsonTextDocumentEdit_toJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instToJsonTextDocumentEdit_toJson___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonTextDocumentEdit_toJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonTextDocumentEdit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonTextDocumentEdit_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonTextDocumentEdit___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonTextDocumentEdit___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonTextDocumentEdit = (const lean_object*)&l_Lean_Lsp_instToJsonTextDocumentEdit___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentEdit_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentEdit_fromJson_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentEdit_fromJson_spec__1_spec__1_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentEdit_fromJson_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentEdit_fromJson_spec__1_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentEdit_fromJson_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentEdit_fromJson_spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "TextDocumentEdit"};
static const lean_object* l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonLocation_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__1_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonLocation_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__1_value_aux_1),((lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(221, 209, 213, 215, 209, 99, 14, 164)}};
static const lean_object* l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__1_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__2;
static lean_once_cell_t l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__3;
static const lean_ctor_object l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instToJsonTextDocumentEdit_toJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(215, 223, 21, 223, 122, 31, 128, 254)}};
static const lean_object* l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__4 = (const lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__4_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__5;
static lean_once_cell_t l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__6;
static lean_once_cell_t l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__7;
static const lean_ctor_object l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instToJsonTextDocumentEdit_toJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(31, 84, 119, 36, 206, 155, 200, 147)}};
static const lean_object* l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__8 = (const lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__8_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__9;
static lean_once_cell_t l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__10;
static lean_once_cell_t l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__11;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonTextDocumentEdit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonTextDocumentEdit___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentEdit___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonTextDocumentEdit = (const lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentEdit___closed__0_value;
static const lean_string_object l_Lean_Lsp_instToJsonChangeAnnotation_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "label"};
static const lean_object* l_Lean_Lsp_instToJsonChangeAnnotation_toJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonChangeAnnotation_toJson___closed__0_value;
static const lean_string_object l_Lean_Lsp_instToJsonChangeAnnotation_toJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "needsConfirmation"};
static const lean_object* l_Lean_Lsp_instToJsonChangeAnnotation_toJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instToJsonChangeAnnotation_toJson___closed__1_value;
static const lean_string_object l_Lean_Lsp_instToJsonChangeAnnotation_toJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "description"};
static const lean_object* l_Lean_Lsp_instToJsonChangeAnnotation_toJson___closed__2 = (const lean_object*)&l_Lean_Lsp_instToJsonChangeAnnotation_toJson___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonChangeAnnotation_toJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonChangeAnnotation___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonChangeAnnotation_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonChangeAnnotation___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonChangeAnnotation___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonChangeAnnotation = (const lean_object*)&l_Lean_Lsp_instToJsonChangeAnnotation___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonChangeAnnotation_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonChangeAnnotation_fromJson_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "ChangeAnnotation"};
static const lean_object* l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonLocation_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__1_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonLocation_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__1_value_aux_1),((lean_object*)&l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(82, 29, 38, 56, 166, 211, 67, 130)}};
static const lean_object* l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__1_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__2;
static lean_once_cell_t l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__3;
static const lean_ctor_object l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instToJsonChangeAnnotation_toJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(16, 195, 177, 11, 70, 212, 216, 195)}};
static const lean_object* l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__4 = (const lean_object*)&l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__4_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__5;
static lean_once_cell_t l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__6;
static lean_once_cell_t l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__7;
static const lean_ctor_object l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instToJsonChangeAnnotation_toJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(13, 228, 249, 245, 195, 42, 25, 231)}};
static const lean_object* l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__8 = (const lean_object*)&l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__8_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__9;
static lean_once_cell_t l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__10;
static lean_once_cell_t l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__11;
static const lean_string_object l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "description\?"};
static const lean_object* l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__12 = (const lean_object*)&l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__12_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__12_value),LEAN_SCALAR_PTR_LITERAL(153, 157, 232, 40, 135, 180, 81, 193)}};
static const lean_object* l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__13 = (const lean_object*)&l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__13_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__14;
static lean_once_cell_t l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__15;
static lean_once_cell_t l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__16;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonChangeAnnotation___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonChangeAnnotation___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonChangeAnnotation___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonChangeAnnotation = (const lean_object*)&l_Lean_Lsp_instFromJsonChangeAnnotation___closed__0_value;
static const lean_string_object l_Lean_Lsp_CreateFile_instToJsonOptions_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "overwrite"};
static const lean_object* l_Lean_Lsp_CreateFile_instToJsonOptions_toJson___closed__0 = (const lean_object*)&l_Lean_Lsp_CreateFile_instToJsonOptions_toJson___closed__0_value;
static const lean_string_object l_Lean_Lsp_CreateFile_instToJsonOptions_toJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "ignoreIfExists"};
static const lean_object* l_Lean_Lsp_CreateFile_instToJsonOptions_toJson___closed__1 = (const lean_object*)&l_Lean_Lsp_CreateFile_instToJsonOptions_toJson___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_CreateFile_instToJsonOptions_toJson(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_CreateFile_instToJsonOptions_toJson___boxed(lean_object*);
static const lean_closure_object l_Lean_Lsp_CreateFile_instToJsonOptions___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_CreateFile_instToJsonOptions_toJson___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_CreateFile_instToJsonOptions___closed__0 = (const lean_object*)&l_Lean_Lsp_CreateFile_instToJsonOptions___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_CreateFile_instToJsonOptions = (const lean_object*)&l_Lean_Lsp_CreateFile_instToJsonOptions___closed__0_value;
static const lean_string_object l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "CreateFile"};
static const lean_object* l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__0_value;
static const lean_string_object l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Options"};
static const lean_object* l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__1_value;
static const lean_ctor_object l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonLocation_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__2_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonLocation_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__2_value_aux_1),((lean_object*)&l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(222, 28, 133, 85, 52, 115, 205, 71)}};
static const lean_ctor_object l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__2_value_aux_2),((lean_object*)&l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(53, 167, 246, 247, 255, 188, 202, 139)}};
static const lean_object* l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__2 = (const lean_object*)&l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__2_value;
static lean_once_cell_t l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__3;
static lean_once_cell_t l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__4;
static const lean_ctor_object l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_CreateFile_instToJsonOptions_toJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 87, 170, 114, 241, 70, 204, 130)}};
static const lean_object* l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__5 = (const lean_object*)&l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__5_value;
static lean_once_cell_t l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__6;
static lean_once_cell_t l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__7;
static lean_once_cell_t l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__8;
static const lean_ctor_object l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_CreateFile_instToJsonOptions_toJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 134, 117, 77, 156, 66, 145, 205)}};
static const lean_object* l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__9 = (const lean_object*)&l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__9_value;
static lean_once_cell_t l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__10;
static lean_once_cell_t l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__11;
static lean_once_cell_t l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__12;
LEAN_EXPORT lean_object* l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_CreateFile_instFromJsonOptions___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_CreateFile_instFromJsonOptions___closed__0 = (const lean_object*)&l_Lean_Lsp_CreateFile_instFromJsonOptions___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_CreateFile_instFromJsonOptions = (const lean_object*)&l_Lean_Lsp_CreateFile_instFromJsonOptions___closed__0_value;
static const lean_string_object l_Lean_Lsp_DeleteFile_instToJsonOptions_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "recursive"};
static const lean_object* l_Lean_Lsp_DeleteFile_instToJsonOptions_toJson___closed__0 = (const lean_object*)&l_Lean_Lsp_DeleteFile_instToJsonOptions_toJson___closed__0_value;
static const lean_string_object l_Lean_Lsp_DeleteFile_instToJsonOptions_toJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "ignoreIfNotExists"};
static const lean_object* l_Lean_Lsp_DeleteFile_instToJsonOptions_toJson___closed__1 = (const lean_object*)&l_Lean_Lsp_DeleteFile_instToJsonOptions_toJson___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_DeleteFile_instToJsonOptions_toJson(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DeleteFile_instToJsonOptions_toJson___boxed(lean_object*);
static const lean_closure_object l_Lean_Lsp_DeleteFile_instToJsonOptions___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_DeleteFile_instToJsonOptions_toJson___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_DeleteFile_instToJsonOptions___closed__0 = (const lean_object*)&l_Lean_Lsp_DeleteFile_instToJsonOptions___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_DeleteFile_instToJsonOptions = (const lean_object*)&l_Lean_Lsp_DeleteFile_instToJsonOptions___closed__0_value;
static const lean_string_object l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "DeleteFile"};
static const lean_object* l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonLocation_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__1_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonLocation_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__1_value_aux_1),((lean_object*)&l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(144, 6, 170, 69, 207, 171, 46, 13)}};
static const lean_ctor_object l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__1_value_aux_2),((lean_object*)&l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(155, 176, 229, 133, 131, 198, 118, 8)}};
static const lean_object* l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__1_value;
static lean_once_cell_t l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__2;
static lean_once_cell_t l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__3;
static const lean_ctor_object l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_DeleteFile_instToJsonOptions_toJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(56, 70, 223, 116, 74, 127, 72, 80)}};
static const lean_object* l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__4 = (const lean_object*)&l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__4_value;
static lean_once_cell_t l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__5;
static lean_once_cell_t l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__6;
static lean_once_cell_t l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__7;
static const lean_ctor_object l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_DeleteFile_instToJsonOptions_toJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(4, 158, 228, 176, 92, 223, 55, 182)}};
static const lean_object* l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__8 = (const lean_object*)&l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__8_value;
static lean_once_cell_t l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__9;
static lean_once_cell_t l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__10;
static lean_once_cell_t l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__11;
LEAN_EXPORT lean_object* l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_DeleteFile_instFromJsonOptions___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_DeleteFile_instFromJsonOptions___closed__0 = (const lean_object*)&l_Lean_Lsp_DeleteFile_instFromJsonOptions___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_DeleteFile_instFromJsonOptions = (const lean_object*)&l_Lean_Lsp_DeleteFile_instFromJsonOptions___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonCreateFile_toJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonCreateFile_toJson_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instToJsonCreateFile_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "options"};
static const lean_object* l_Lean_Lsp_instToJsonCreateFile_toJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonCreateFile_toJson___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonCreateFile_toJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonCreateFile___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonCreateFile_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonCreateFile___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonCreateFile___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonCreateFile = (const lean_object*)&l_Lean_Lsp_instToJsonCreateFile___closed__0_value;
static const lean_ctor_object l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCreateFile_fromJson_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCreateFile_fromJson_spec__0_spec__0___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCreateFile_fromJson_spec__0_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCreateFile_fromJson_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCreateFile_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCreateFile_fromJson_spec__0___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonLocation_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__0_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonLocation_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__0_value_aux_1),((lean_object*)&l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(222, 28, 133, 85, 52, 115, 205, 71)}};
static const lean_object* l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__0_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__1;
static lean_once_cell_t l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__2;
static lean_once_cell_t l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__3;
static lean_once_cell_t l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__4;
static const lean_string_object l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "options\?"};
static const lean_object* l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__5 = (const lean_object*)&l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__5_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__5_value),LEAN_SCALAR_PTR_LITERAL(86, 227, 221, 148, 173, 251, 188, 232)}};
static const lean_object* l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__6 = (const lean_object*)&l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__6_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__7;
static lean_once_cell_t l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__8;
static lean_once_cell_t l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__9;
static lean_once_cell_t l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__10;
static lean_once_cell_t l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__11;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonCreateFile_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonCreateFile___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonCreateFile_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonCreateFile___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonCreateFile___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonCreateFile = (const lean_object*)&l_Lean_Lsp_instFromJsonCreateFile___closed__0_value;
static const lean_string_object l_Lean_Lsp_instToJsonRenameFile_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "oldUri"};
static const lean_object* l_Lean_Lsp_instToJsonRenameFile_toJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonRenameFile_toJson___closed__0_value;
static const lean_string_object l_Lean_Lsp_instToJsonRenameFile_toJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "newUri"};
static const lean_object* l_Lean_Lsp_instToJsonRenameFile_toJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instToJsonRenameFile_toJson___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRenameFile_toJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonRenameFile___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonRenameFile_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonRenameFile___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonRenameFile___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonRenameFile = (const lean_object*)&l_Lean_Lsp_instToJsonRenameFile___closed__0_value;
static const lean_string_object l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "RenameFile"};
static const lean_object* l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonLocation_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__1_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonLocation_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__1_value_aux_1),((lean_object*)&l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(162, 122, 246, 46, 146, 210, 110, 79)}};
static const lean_object* l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__1_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__2;
static lean_once_cell_t l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__3;
static const lean_ctor_object l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instToJsonRenameFile_toJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(232, 34, 198, 243, 229, 35, 216, 220)}};
static const lean_object* l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__4 = (const lean_object*)&l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__4_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__5;
static lean_once_cell_t l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__6;
static lean_once_cell_t l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__7;
static const lean_ctor_object l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instToJsonRenameFile_toJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(124, 1, 162, 227, 227, 137, 70, 155)}};
static const lean_object* l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__8 = (const lean_object*)&l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__8_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__9;
static lean_once_cell_t l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__10;
static lean_once_cell_t l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__11;
static lean_once_cell_t l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__12;
static lean_once_cell_t l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__13;
static lean_once_cell_t l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__14;
static lean_once_cell_t l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__15;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonRenameFile_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonRenameFile___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonRenameFile_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonRenameFile___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonRenameFile___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonRenameFile = (const lean_object*)&l_Lean_Lsp_instFromJsonRenameFile___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDeleteFile_toJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDeleteFile_toJson_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDeleteFile_toJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonDeleteFile___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonDeleteFile_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonDeleteFile___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonDeleteFile___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonDeleteFile = (const lean_object*)&l_Lean_Lsp_instToJsonDeleteFile___closed__0_value;
static const lean_ctor_object l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDeleteFile_fromJson_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDeleteFile_fromJson_spec__0_spec__0___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDeleteFile_fromJson_spec__0_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDeleteFile_fromJson_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDeleteFile_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDeleteFile_fromJson_spec__0___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonLocation_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__0_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonLocation_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__0_value_aux_1),((lean_object*)&l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(144, 6, 170, 69, 207, 171, 46, 13)}};
static const lean_object* l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__0_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__1;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__2;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__3;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__4;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__5;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__6;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__7;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__8;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDeleteFile_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonDeleteFile___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonDeleteFile_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonDeleteFile___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonDeleteFile___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonDeleteFile = (const lean_object*)&l_Lean_Lsp_instFromJsonDeleteFile___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_DocumentChange_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DocumentChange_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DocumentChange_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DocumentChange_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DocumentChange_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DocumentChange_create_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DocumentChange_create_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DocumentChange_rename_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DocumentChange_rename_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DocumentChange_delete_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DocumentChange_delete_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DocumentChange_edit_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DocumentChange_edit_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instToJsonDocumentChange___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "kind"};
static const lean_object* l_Lean_Lsp_instToJsonDocumentChange___lam__0___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonDocumentChange___lam__0___closed__0_value;
static const lean_string_object l_Lean_Lsp_instToJsonDocumentChange___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "create"};
static const lean_object* l_Lean_Lsp_instToJsonDocumentChange___lam__0___closed__1 = (const lean_object*)&l_Lean_Lsp_instToJsonDocumentChange___lam__0___closed__1_value;
static const lean_ctor_object l_Lean_Lsp_instToJsonDocumentChange___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Lsp_instToJsonDocumentChange___lam__0___closed__1_value)}};
static const lean_object* l_Lean_Lsp_instToJsonDocumentChange___lam__0___closed__2 = (const lean_object*)&l_Lean_Lsp_instToJsonDocumentChange___lam__0___closed__2_value;
static const lean_string_object l_Lean_Lsp_instToJsonDocumentChange___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "rename"};
static const lean_object* l_Lean_Lsp_instToJsonDocumentChange___lam__0___closed__3 = (const lean_object*)&l_Lean_Lsp_instToJsonDocumentChange___lam__0___closed__3_value;
static const lean_ctor_object l_Lean_Lsp_instToJsonDocumentChange___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Lsp_instToJsonDocumentChange___lam__0___closed__3_value)}};
static const lean_object* l_Lean_Lsp_instToJsonDocumentChange___lam__0___closed__4 = (const lean_object*)&l_Lean_Lsp_instToJsonDocumentChange___lam__0___closed__4_value;
static const lean_string_object l_Lean_Lsp_instToJsonDocumentChange___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "delete"};
static const lean_object* l_Lean_Lsp_instToJsonDocumentChange___lam__0___closed__5 = (const lean_object*)&l_Lean_Lsp_instToJsonDocumentChange___lam__0___closed__5_value;
static const lean_ctor_object l_Lean_Lsp_instToJsonDocumentChange___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Lsp_instToJsonDocumentChange___lam__0___closed__5_value)}};
static const lean_object* l_Lean_Lsp_instToJsonDocumentChange___lam__0___closed__6 = (const lean_object*)&l_Lean_Lsp_instToJsonDocumentChange___lam__0___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDocumentChange___lam__0(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonDocumentChange___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonDocumentChange___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonDocumentChange___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonDocumentChange___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonDocumentChange = (const lean_object*)&l_Lean_Lsp_instToJsonDocumentChange___closed__0_value;
static const lean_string_object l_Lean_Lsp_instFromJsonDocumentChange___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Unrecognized kind: "};
static const lean_object* l_Lean_Lsp_instFromJsonDocumentChange___lam__0___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonDocumentChange___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDocumentChange___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDocumentChange___lam__1(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonDocumentChange___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonDocumentChange___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonDocumentChange___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonDocumentChange___closed__0_value;
static const lean_closure_object l_Lean_Lsp_instFromJsonDocumentChange___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonDocumentChange___lam__1, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonDocumentChange___closed__0_value)} };
static const lean_object* l_Lean_Lsp_instFromJsonDocumentChange___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonDocumentChange___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonDocumentChange = (const lean_object*)&l_Lean_Lsp_instFromJsonDocumentChange___closed__1_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_map___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEdit_toJson_spec__2_spec__4_spec__7(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEdit_toJson_spec__2_spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEdit_toJson_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEdit_toJson_spec__1_spec__2_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEdit_toJson_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEdit_toJson_spec__1_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEdit_toJson_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_map___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEdit_toJson_spec__0_spec__0_spec__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEdit_toJson_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEdit_toJson_spec__0(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instToJsonWorkspaceEdit_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "changes"};
static const lean_object* l_Lean_Lsp_instToJsonWorkspaceEdit_toJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonWorkspaceEdit_toJson___closed__0_value;
static const lean_string_object l_Lean_Lsp_instToJsonWorkspaceEdit_toJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "documentChanges"};
static const lean_object* l_Lean_Lsp_instToJsonWorkspaceEdit_toJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instToJsonWorkspaceEdit_toJson___closed__1_value;
static const lean_string_object l_Lean_Lsp_instToJsonWorkspaceEdit_toJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "changeAnnotations"};
static const lean_object* l_Lean_Lsp_instToJsonWorkspaceEdit_toJson___closed__2 = (const lean_object*)&l_Lean_Lsp_instToJsonWorkspaceEdit_toJson___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonWorkspaceEdit_toJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonWorkspaceEdit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonWorkspaceEdit_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonWorkspaceEdit___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonWorkspaceEdit___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonWorkspaceEdit = (const lean_object*)&l_Lean_Lsp_instToJsonWorkspaceEdit___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__1_spec__2_spec__4_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__2_spec__4_spec__7_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__2_spec__4_spec__7(lean_object*, lean_object*);
static const lean_ctor_object l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__2_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__2_spec__4___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__2_spec__4___closed__0_value;
static const lean_closure_object l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__2_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_compare___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__2_spec__4___closed__1 = (const lean_object*)&l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__2_spec__4___closed__1_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__2_spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__1_spec__2_spec__4_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__1_spec__2_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__1_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__0_spec__0_spec__1_spec__4___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__0_spec__0_spec__1_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__0_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__0_spec__0_spec__1(lean_object*);
static const lean_ctor_object l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__0_spec__0___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__0_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "WorkspaceEdit"};
static const lean_object* l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonLocation_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__1_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonLocation_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__1_value_aux_1),((lean_object*)&l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(123, 53, 41, 159, 108, 63, 180, 34)}};
static const lean_object* l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__1_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__2;
static lean_once_cell_t l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__3;
static const lean_string_object l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "changes\?"};
static const lean_object* l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__4 = (const lean_object*)&l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__4_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__4_value),LEAN_SCALAR_PTR_LITERAL(170, 115, 240, 184, 226, 123, 111, 156)}};
static const lean_object* l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__5 = (const lean_object*)&l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__5_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__6;
static lean_once_cell_t l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__7;
static lean_once_cell_t l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__8;
static const lean_string_object l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "documentChanges\?"};
static const lean_object* l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__9 = (const lean_object*)&l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__9_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__9_value),LEAN_SCALAR_PTR_LITERAL(98, 237, 212, 122, 169, 183, 78, 106)}};
static const lean_object* l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__10 = (const lean_object*)&l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__10_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__11;
static lean_once_cell_t l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__12;
static lean_once_cell_t l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__13;
static const lean_string_object l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "changeAnnotations\?"};
static const lean_object* l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__14 = (const lean_object*)&l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__14_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__14_value),LEAN_SCALAR_PTR_LITERAL(173, 82, 27, 192, 32, 217, 85, 156)}};
static const lean_object* l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__15 = (const lean_object*)&l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__15_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__16;
static lean_once_cell_t l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__17;
static lean_once_cell_t l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__18;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__1_spec__2_spec__4_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonWorkspaceEdit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonWorkspaceEdit___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonWorkspaceEdit___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonWorkspaceEdit = (const lean_object*)&l_Lean_Lsp_instFromJsonWorkspaceEdit___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_WorkspaceEdit_instEmptyCollection___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Lsp_WorkspaceEdit_instEmptyCollection___closed__0 = (const lean_object*)&l_Lean_Lsp_WorkspaceEdit_instEmptyCollection___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_WorkspaceEdit_instEmptyCollection = (const lean_object*)&l_Lean_Lsp_WorkspaceEdit_instEmptyCollection___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_WorkspaceEdit_instAppend___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_WorkspaceEdit_instAppend___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_WorkspaceEdit_instAppend___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_WorkspaceEdit_instAppend___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_WorkspaceEdit_instAppend___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_WorkspaceEdit_instAppend___lam__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_WorkspaceEdit_instAppend___lam__1, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__2_spec__4___closed__1_value)} };
static const lean_object* l_Lean_Lsp_WorkspaceEdit_instAppend___lam__4___closed__0 = (const lean_object*)&l_Lean_Lsp_WorkspaceEdit_instAppend___lam__4___closed__0_value;
static const lean_closure_object l_Lean_Lsp_WorkspaceEdit_instAppend___lam__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_WorkspaceEdit_instAppend___lam__3, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__2_spec__4___closed__1_value)} };
static const lean_object* l_Lean_Lsp_WorkspaceEdit_instAppend___lam__4___closed__1 = (const lean_object*)&l_Lean_Lsp_WorkspaceEdit_instAppend___lam__4___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_WorkspaceEdit_instAppend___lam__4(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_WorkspaceEdit_instAppend___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_WorkspaceEdit_instAppend___lam__4, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_WorkspaceEdit_instAppend___closed__0 = (const lean_object*)&l_Lean_Lsp_WorkspaceEdit_instAppend___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_WorkspaceEdit_instAppend = (const lean_object*)&l_Lean_Lsp_WorkspaceEdit_instAppend___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_WorkspaceEdit_ofTextDocumentEdit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_WorkspaceEdit_ofTextEdit(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instToJsonApplyWorkspaceEditParams_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "edit"};
static const lean_object* l_Lean_Lsp_instToJsonApplyWorkspaceEditParams_toJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonApplyWorkspaceEditParams_toJson___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonApplyWorkspaceEditParams_toJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonApplyWorkspaceEditParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonApplyWorkspaceEditParams_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonApplyWorkspaceEditParams___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonApplyWorkspaceEditParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonApplyWorkspaceEditParams = (const lean_object*)&l_Lean_Lsp_instToJsonApplyWorkspaceEditParams___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "ApplyWorkspaceEditParams"};
static const lean_object* l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonLocation_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__1_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonLocation_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__1_value_aux_1),((lean_object*)&l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(60, 203, 7, 144, 87, 77, 77, 21)}};
static const lean_object* l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__1_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__2;
static lean_once_cell_t l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__3;
static const lean_string_object l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "label\?"};
static const lean_object* l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__4 = (const lean_object*)&l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__4_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__4_value),LEAN_SCALAR_PTR_LITERAL(149, 151, 242, 23, 214, 92, 131, 60)}};
static const lean_object* l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__5 = (const lean_object*)&l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__5_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__6;
static lean_once_cell_t l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__7;
static lean_once_cell_t l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__8;
static const lean_ctor_object l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instToJsonApplyWorkspaceEditParams_toJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(195, 25, 214, 57, 9, 124, 16, 157)}};
static const lean_object* l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__9 = (const lean_object*)&l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__9_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__10;
static lean_once_cell_t l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__11;
static lean_once_cell_t l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__12;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams = (const lean_object*)&l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams___closed__0_value;
static const lean_string_object l_Lean_Lsp_instToJsonTextDocumentItem_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "languageId"};
static const lean_object* l_Lean_Lsp_instToJsonTextDocumentItem_toJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonTextDocumentItem_toJson___closed__0_value;
static const lean_string_object l_Lean_Lsp_instToJsonTextDocumentItem_toJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "text"};
static const lean_object* l_Lean_Lsp_instToJsonTextDocumentItem_toJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instToJsonTextDocumentItem_toJson___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonTextDocumentItem_toJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonTextDocumentItem___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonTextDocumentItem_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonTextDocumentItem___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonTextDocumentItem___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonTextDocumentItem = (const lean_object*)&l_Lean_Lsp_instToJsonTextDocumentItem___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentItem_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentItem_fromJson_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "TextDocumentItem"};
static const lean_object* l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonLocation_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__1_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonLocation_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__1_value_aux_1),((lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(89, 222, 104, 203, 181, 123, 142, 128)}};
static const lean_object* l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__1_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__2;
static lean_once_cell_t l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__3;
static lean_once_cell_t l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__4;
static lean_once_cell_t l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__5;
static const lean_ctor_object l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instToJsonTextDocumentItem_toJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(49, 221, 17, 12, 58, 230, 139, 137)}};
static const lean_object* l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__6 = (const lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__6_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__7;
static lean_once_cell_t l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__8;
static lean_once_cell_t l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__9;
static const lean_ctor_object l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instToJsonVersionedTextDocumentIdentifier_toJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(167, 68, 50, 73, 160, 48, 142, 108)}};
static const lean_object* l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__10 = (const lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__10_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__11;
static lean_once_cell_t l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__12;
static lean_once_cell_t l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__13;
static const lean_ctor_object l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instToJsonTextDocumentItem_toJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(26, 32, 191, 158, 22, 157, 236, 165)}};
static const lean_object* l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__14 = (const lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__14_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__15;
static lean_once_cell_t l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__16;
static lean_once_cell_t l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__17;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonTextDocumentItem___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonTextDocumentItem___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentItem___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonTextDocumentItem = (const lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentItem___closed__0_value;
static const lean_string_object l_Lean_Lsp_instToJsonTextDocumentPositionParams_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "position"};
static const lean_object* l_Lean_Lsp_instToJsonTextDocumentPositionParams_toJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonTextDocumentPositionParams_toJson___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonTextDocumentPositionParams_toJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonTextDocumentPositionParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonTextDocumentPositionParams_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonTextDocumentPositionParams___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonTextDocumentPositionParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonTextDocumentPositionParams = (const lean_object*)&l_Lean_Lsp_instToJsonTextDocumentPositionParams___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson_spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "TextDocumentPositionParams"};
static const lean_object* l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonLocation_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__1_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonLocation_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__1_value_aux_1),((lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(21, 35, 84, 107, 140, 105, 155, 176)}};
static const lean_object* l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__1_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__2;
static lean_once_cell_t l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__3;
static lean_once_cell_t l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__4;
static lean_once_cell_t l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__5;
static const lean_ctor_object l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instToJsonTextDocumentPositionParams_toJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(91, 172, 67, 66, 136, 94, 119, 158)}};
static const lean_object* l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__6 = (const lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__6_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__7;
static lean_once_cell_t l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__8;
static lean_once_cell_t l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__9;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonTextDocumentPositionParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonTextDocumentPositionParams___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentPositionParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonTextDocumentPositionParams = (const lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentPositionParams___closed__0_value;
static const lean_string_object l_Lean_Lsp_instToStringTextDocumentPositionParams___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Lean_Lsp_instToStringTextDocumentPositionParams___lam__0___closed__0 = (const lean_object*)&l_Lean_Lsp_instToStringTextDocumentPositionParams___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToStringTextDocumentPositionParams___lam__0(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToStringTextDocumentPositionParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToStringTextDocumentPositionParams___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToStringTextDocumentPositionParams___closed__0 = (const lean_object*)&l_Lean_Lsp_instToStringTextDocumentPositionParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToStringTextDocumentPositionParams = (const lean_object*)&l_Lean_Lsp_instToStringTextDocumentPositionParams___closed__0_value;
static const lean_string_object l_Lean_Lsp_instToJsonDocumentFilter_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "language"};
static const lean_object* l_Lean_Lsp_instToJsonDocumentFilter_toJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonDocumentFilter_toJson___closed__0_value;
static const lean_string_object l_Lean_Lsp_instToJsonDocumentFilter_toJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "scheme"};
static const lean_object* l_Lean_Lsp_instToJsonDocumentFilter_toJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instToJsonDocumentFilter_toJson___closed__1_value;
static const lean_string_object l_Lean_Lsp_instToJsonDocumentFilter_toJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "pattern"};
static const lean_object* l_Lean_Lsp_instToJsonDocumentFilter_toJson___closed__2 = (const lean_object*)&l_Lean_Lsp_instToJsonDocumentFilter_toJson___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDocumentFilter_toJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonDocumentFilter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonDocumentFilter_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonDocumentFilter___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonDocumentFilter___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonDocumentFilter = (const lean_object*)&l_Lean_Lsp_instToJsonDocumentFilter___closed__0_value;
static const lean_string_object l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "DocumentFilter"};
static const lean_object* l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonLocation_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__1_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonLocation_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__1_value_aux_1),((lean_object*)&l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(110, 157, 11, 58, 62, 79, 241, 202)}};
static const lean_object* l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__1_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__2;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__3;
static const lean_string_object l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "language\?"};
static const lean_object* l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__4 = (const lean_object*)&l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__4_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__4_value),LEAN_SCALAR_PTR_LITERAL(233, 71, 114, 86, 193, 11, 227, 251)}};
static const lean_object* l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__5 = (const lean_object*)&l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__5_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__6;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__7;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__8;
static const lean_string_object l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "scheme\?"};
static const lean_object* l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__9 = (const lean_object*)&l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__9_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__9_value),LEAN_SCALAR_PTR_LITERAL(74, 1, 75, 28, 84, 23, 43, 79)}};
static const lean_object* l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__10 = (const lean_object*)&l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__10_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__11;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__12;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__13;
static const lean_string_object l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "pattern\?"};
static const lean_object* l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__14 = (const lean_object*)&l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__14_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__14_value),LEAN_SCALAR_PTR_LITERAL(67, 60, 32, 224, 244, 193, 130, 57)}};
static const lean_object* l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__15 = (const lean_object*)&l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__15_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__16;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__17;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__18;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDocumentFilter_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonDocumentFilter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonDocumentFilter_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonDocumentFilter___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonDocumentFilter___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonDocumentFilter = (const lean_object*)&l_Lean_Lsp_instFromJsonDocumentFilter___closed__0_value;
static const lean_closure_object l_Lean_Lsp_instFromJsonDocumentSelector___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Array_fromJson_x3f, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonDocumentFilter___closed__0_value)} };
static const lean_object* l_Lean_Lsp_instFromJsonDocumentSelector___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonDocumentSelector___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonDocumentSelector = (const lean_object*)&l_Lean_Lsp_instFromJsonDocumentSelector___closed__0_value;
static const lean_closure_object l_Lean_Lsp_instToJsonDocumentSelector___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Array_toJson, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instToJsonDocumentFilter___closed__0_value)} };
static const lean_object* l_Lean_Lsp_instToJsonDocumentSelector___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonDocumentSelector___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonDocumentSelector = (const lean_object*)&l_Lean_Lsp_instToJsonDocumentSelector___closed__0_value;
static const lean_string_object l_Lean_Lsp_instToJsonStaticRegistrationOptions_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "id"};
static const lean_object* l_Lean_Lsp_instToJsonStaticRegistrationOptions_toJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonStaticRegistrationOptions_toJson___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonStaticRegistrationOptions_toJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonStaticRegistrationOptions___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonStaticRegistrationOptions_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonStaticRegistrationOptions___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonStaticRegistrationOptions___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonStaticRegistrationOptions = (const lean_object*)&l_Lean_Lsp_instToJsonStaticRegistrationOptions___closed__0_value;
static const lean_string_object l_Lean_Lsp_instFromJsonStaticRegistrationOptions_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "StaticRegistrationOptions"};
static const lean_object* l_Lean_Lsp_instFromJsonStaticRegistrationOptions_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonStaticRegistrationOptions_fromJson___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonStaticRegistrationOptions_fromJson___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonLocation_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonStaticRegistrationOptions_fromJson___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonStaticRegistrationOptions_fromJson___closed__1_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonLocation_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonStaticRegistrationOptions_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonStaticRegistrationOptions_fromJson___closed__1_value_aux_1),((lean_object*)&l_Lean_Lsp_instFromJsonStaticRegistrationOptions_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(84, 234, 254, 241, 255, 41, 26, 245)}};
static const lean_object* l_Lean_Lsp_instFromJsonStaticRegistrationOptions_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonStaticRegistrationOptions_fromJson___closed__1_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonStaticRegistrationOptions_fromJson___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonStaticRegistrationOptions_fromJson___closed__2;
static lean_once_cell_t l_Lean_Lsp_instFromJsonStaticRegistrationOptions_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonStaticRegistrationOptions_fromJson___closed__3;
static const lean_string_object l_Lean_Lsp_instFromJsonStaticRegistrationOptions_fromJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "id\?"};
static const lean_object* l_Lean_Lsp_instFromJsonStaticRegistrationOptions_fromJson___closed__4 = (const lean_object*)&l_Lean_Lsp_instFromJsonStaticRegistrationOptions_fromJson___closed__4_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonStaticRegistrationOptions_fromJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonStaticRegistrationOptions_fromJson___closed__4_value),LEAN_SCALAR_PTR_LITERAL(119, 56, 220, 73, 171, 75, 97, 56)}};
static const lean_object* l_Lean_Lsp_instFromJsonStaticRegistrationOptions_fromJson___closed__5 = (const lean_object*)&l_Lean_Lsp_instFromJsonStaticRegistrationOptions_fromJson___closed__5_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonStaticRegistrationOptions_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonStaticRegistrationOptions_fromJson___closed__6;
static lean_once_cell_t l_Lean_Lsp_instFromJsonStaticRegistrationOptions_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonStaticRegistrationOptions_fromJson___closed__7;
static lean_once_cell_t l_Lean_Lsp_instFromJsonStaticRegistrationOptions_fromJson___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonStaticRegistrationOptions_fromJson___closed__8;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonStaticRegistrationOptions_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonStaticRegistrationOptions___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonStaticRegistrationOptions_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonStaticRegistrationOptions___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonStaticRegistrationOptions___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonStaticRegistrationOptions = (const lean_object*)&l_Lean_Lsp_instFromJsonStaticRegistrationOptions___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonTextDocumentRegistrationOptions_toJson_spec__0_spec__0_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonTextDocumentRegistrationOptions_toJson_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonTextDocumentRegistrationOptions_toJson_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextDocumentRegistrationOptions_toJson_spec__0(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instToJsonTextDocumentRegistrationOptions_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "documentSelector"};
static const lean_object* l_Lean_Lsp_instToJsonTextDocumentRegistrationOptions_toJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonTextDocumentRegistrationOptions_toJson___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonTextDocumentRegistrationOptions_toJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonTextDocumentRegistrationOptions___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonTextDocumentRegistrationOptions_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonTextDocumentRegistrationOptions___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonTextDocumentRegistrationOptions___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonTextDocumentRegistrationOptions = (const lean_object*)&l_Lean_Lsp_instToJsonTextDocumentRegistrationOptions___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson_spec__0_spec__0_spec__1_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson_spec__0_spec__0_spec__1(lean_object*);
static const lean_ctor_object l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson_spec__0_spec__0___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson_spec__0_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "TextDocumentRegistrationOptions"};
static const lean_object* l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonLocation_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson___closed__1_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonLocation_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson___closed__1_value_aux_1),((lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(104, 175, 91, 79, 225, 82, 151, 24)}};
static const lean_object* l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson___closed__1_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson___closed__2;
static lean_once_cell_t l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson___closed__3;
static const lean_string_object l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "documentSelector\?"};
static const lean_object* l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson___closed__4 = (const lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson___closed__4_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson___closed__4_value),LEAN_SCALAR_PTR_LITERAL(91, 242, 138, 38, 210, 232, 124, 203)}};
static const lean_object* l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson___closed__5 = (const lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson___closed__5_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson___closed__6;
static lean_once_cell_t l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson___closed__7;
static lean_once_cell_t l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson___closed__8;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions = (const lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_MarkupKind_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Lsp_MarkupKind_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_MarkupKind_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Lsp_MarkupKind_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_MarkupKind_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_MarkupKind_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_MarkupKind_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_MarkupKind_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_MarkupKind_plaintext_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_MarkupKind_plaintext_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_MarkupKind_plaintext_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_MarkupKind_plaintext_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_MarkupKind_markdown_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_MarkupKind_markdown_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_MarkupKind_markdown_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_MarkupKind_markdown_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Lsp_MarkupKind_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_MarkupKind_ofNat___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Lsp_instDecidableEqMarkupKind(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Lsp_instDecidableEqMarkupKind___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lean_Lsp_instHashableMarkupKind_hash(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Lsp_instHashableMarkupKind_hash___boxed(lean_object*);
static const lean_closure_object l_Lean_Lsp_instHashableMarkupKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instHashableMarkupKind_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instHashableMarkupKind___closed__0 = (const lean_object*)&l_Lean_Lsp_instHashableMarkupKind___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instHashableMarkupKind = (const lean_object*)&l_Lean_Lsp_instHashableMarkupKind___closed__0_value;
static const lean_string_object l_Lean_Lsp_instFromJsonMarkupKind___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "unknown MarkupKind"};
static const lean_object* l_Lean_Lsp_instFromJsonMarkupKind___lam__0___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonMarkupKind___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonMarkupKind___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonMarkupKind___lam__0___closed__0_value)}};
static const lean_object* l_Lean_Lsp_instFromJsonMarkupKind___lam__0___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonMarkupKind___lam__0___closed__1_value;
static const lean_string_object l_Lean_Lsp_instFromJsonMarkupKind___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "plaintext"};
static const lean_object* l_Lean_Lsp_instFromJsonMarkupKind___lam__0___closed__2 = (const lean_object*)&l_Lean_Lsp_instFromJsonMarkupKind___lam__0___closed__2_value;
static const lean_string_object l_Lean_Lsp_instFromJsonMarkupKind___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "markdown"};
static const lean_object* l_Lean_Lsp_instFromJsonMarkupKind___lam__0___closed__3 = (const lean_object*)&l_Lean_Lsp_instFromJsonMarkupKind___lam__0___closed__3_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonMarkupKind___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Lsp_instFromJsonMarkupKind___lam__0___closed__4 = (const lean_object*)&l_Lean_Lsp_instFromJsonMarkupKind___lam__0___closed__4_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonMarkupKind___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Lsp_instFromJsonMarkupKind___lam__0___closed__5 = (const lean_object*)&l_Lean_Lsp_instFromJsonMarkupKind___lam__0___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonMarkupKind___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonMarkupKind___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonMarkupKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonMarkupKind___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonMarkupKind___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonMarkupKind___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonMarkupKind = (const lean_object*)&l_Lean_Lsp_instFromJsonMarkupKind___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_instToJsonMarkupKind___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonMarkupKind___lam__0___closed__2_value)}};
static const lean_object* l_Lean_Lsp_instToJsonMarkupKind___lam__0___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonMarkupKind___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_instToJsonMarkupKind___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonMarkupKind___lam__0___closed__3_value)}};
static const lean_object* l_Lean_Lsp_instToJsonMarkupKind___lam__0___closed__1 = (const lean_object*)&l_Lean_Lsp_instToJsonMarkupKind___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonMarkupKind___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonMarkupKind___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonMarkupKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonMarkupKind___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonMarkupKind___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonMarkupKind___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonMarkupKind = (const lean_object*)&l_Lean_Lsp_instToJsonMarkupKind___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonMarkupContent_toJson(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonMarkupContent_toJson___boxed(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonMarkupContent___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonMarkupContent_toJson___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonMarkupContent___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonMarkupContent___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonMarkupContent = (const lean_object*)&l_Lean_Lsp_instToJsonMarkupContent___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonMarkupContent_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonMarkupContent_fromJson_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "MarkupContent"};
static const lean_object* l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonLocation_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__1_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonLocation_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__1_value_aux_1),((lean_object*)&l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(255, 181, 133, 8, 53, 221, 67, 106)}};
static const lean_object* l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__1_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__2;
static lean_once_cell_t l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__3;
static const lean_ctor_object l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instToJsonDocumentChange___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(90, 186, 66, 236, 16, 221, 215, 158)}};
static const lean_object* l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__4 = (const lean_object*)&l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__4_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__5;
static lean_once_cell_t l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__6;
static lean_once_cell_t l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__7;
static lean_once_cell_t l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__8;
static lean_once_cell_t l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__9;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonMarkupContent_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonMarkupContent___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonMarkupContent_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonMarkupContent___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonMarkupContent___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonMarkupContent = (const lean_object*)&l_Lean_Lsp_instFromJsonMarkupContent___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Lsp_instDecidableEqMarkupContent_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instDecidableEqMarkupContent_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Lsp_instDecidableEqMarkupContent(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instDecidableEqMarkupContent___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lean_Lsp_instHashableMarkupContent_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instHashableMarkupContent_hash___boxed(lean_object*);
static const lean_closure_object l_Lean_Lsp_instHashableMarkupContent___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instHashableMarkupContent_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instHashableMarkupContent___closed__0 = (const lean_object*)&l_Lean_Lsp_instHashableMarkupContent___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instHashableMarkupContent = (const lean_object*)&l_Lean_Lsp_instHashableMarkupContent___closed__0_value;
static const lean_string_object l_Lean_Lsp_instToJsonProgressParams_toJson___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "token"};
static const lean_object* l_Lean_Lsp_instToJsonProgressParams_toJson___redArg___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonProgressParams_toJson___redArg___closed__0_value;
static const lean_closure_object l_Lean_Lsp_instToJsonProgressParams_toJson___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_id___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Lsp_instToJsonProgressParams_toJson___redArg___closed__1 = (const lean_object*)&l_Lean_Lsp_instToJsonProgressParams_toJson___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonProgressParams_toJson___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonProgressParams_toJson(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonProgressParams___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonProgressParams(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instToJsonWorkDoneProgressReport_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "message"};
static const lean_object* l_Lean_Lsp_instToJsonWorkDoneProgressReport_toJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonWorkDoneProgressReport_toJson___closed__0_value;
static const lean_string_object l_Lean_Lsp_instToJsonWorkDoneProgressReport_toJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "cancellable"};
static const lean_object* l_Lean_Lsp_instToJsonWorkDoneProgressReport_toJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instToJsonWorkDoneProgressReport_toJson___closed__1_value;
static const lean_string_object l_Lean_Lsp_instToJsonWorkDoneProgressReport_toJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "percentage"};
static const lean_object* l_Lean_Lsp_instToJsonWorkDoneProgressReport_toJson___closed__2 = (const lean_object*)&l_Lean_Lsp_instToJsonWorkDoneProgressReport_toJson___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonWorkDoneProgressReport_toJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonWorkDoneProgressReport___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonWorkDoneProgressReport_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonWorkDoneProgressReport___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonWorkDoneProgressReport___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonWorkDoneProgressReport = (const lean_object*)&l_Lean_Lsp_instToJsonWorkDoneProgressReport___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonWorkDoneProgressBegin_toJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonWorkDoneProgressBegin___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonWorkDoneProgressBegin_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonWorkDoneProgressBegin___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonWorkDoneProgressBegin___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonWorkDoneProgressBegin = (const lean_object*)&l_Lean_Lsp_instToJsonWorkDoneProgressBegin___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonWorkDoneProgressEnd_toJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonWorkDoneProgressEnd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonWorkDoneProgressEnd_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonWorkDoneProgressEnd___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonWorkDoneProgressEnd___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonWorkDoneProgressEnd = (const lean_object*)&l_Lean_Lsp_instToJsonWorkDoneProgressEnd___closed__0_value;
static const lean_string_object l_Lean_Lsp_instToJsonWorkDoneProgressParams_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "workDoneToken"};
static const lean_object* l_Lean_Lsp_instToJsonWorkDoneProgressParams_toJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonWorkDoneProgressParams_toJson___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonWorkDoneProgressParams_toJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonWorkDoneProgressParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonWorkDoneProgressParams_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonWorkDoneProgressParams___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonWorkDoneProgressParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonWorkDoneProgressParams = (const lean_object*)&l_Lean_Lsp_instToJsonWorkDoneProgressParams___closed__0_value;
static const lean_string_object l_Lean_Lsp_instFromJsonWorkDoneProgressParams_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "WorkDoneProgressParams"};
static const lean_object* l_Lean_Lsp_instFromJsonWorkDoneProgressParams_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonWorkDoneProgressParams_fromJson___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonWorkDoneProgressParams_fromJson___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonLocation_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonWorkDoneProgressParams_fromJson___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonWorkDoneProgressParams_fromJson___closed__1_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonLocation_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonWorkDoneProgressParams_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonWorkDoneProgressParams_fromJson___closed__1_value_aux_1),((lean_object*)&l_Lean_Lsp_instFromJsonWorkDoneProgressParams_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(63, 48, 2, 139, 191, 231, 94, 9)}};
static const lean_object* l_Lean_Lsp_instFromJsonWorkDoneProgressParams_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonWorkDoneProgressParams_fromJson___closed__1_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonWorkDoneProgressParams_fromJson___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonWorkDoneProgressParams_fromJson___closed__2;
static lean_once_cell_t l_Lean_Lsp_instFromJsonWorkDoneProgressParams_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonWorkDoneProgressParams_fromJson___closed__3;
static const lean_string_object l_Lean_Lsp_instFromJsonWorkDoneProgressParams_fromJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "workDoneToken\?"};
static const lean_object* l_Lean_Lsp_instFromJsonWorkDoneProgressParams_fromJson___closed__4 = (const lean_object*)&l_Lean_Lsp_instFromJsonWorkDoneProgressParams_fromJson___closed__4_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonWorkDoneProgressParams_fromJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonWorkDoneProgressParams_fromJson___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 131, 217, 139, 108, 77, 104, 24)}};
static const lean_object* l_Lean_Lsp_instFromJsonWorkDoneProgressParams_fromJson___closed__5 = (const lean_object*)&l_Lean_Lsp_instFromJsonWorkDoneProgressParams_fromJson___closed__5_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonWorkDoneProgressParams_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonWorkDoneProgressParams_fromJson___closed__6;
static lean_once_cell_t l_Lean_Lsp_instFromJsonWorkDoneProgressParams_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonWorkDoneProgressParams_fromJson___closed__7;
static lean_once_cell_t l_Lean_Lsp_instFromJsonWorkDoneProgressParams_fromJson___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonWorkDoneProgressParams_fromJson___closed__8;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonWorkDoneProgressParams_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonWorkDoneProgressParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonWorkDoneProgressParams_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonWorkDoneProgressParams___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonWorkDoneProgressParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonWorkDoneProgressParams = (const lean_object*)&l_Lean_Lsp_instFromJsonWorkDoneProgressParams___closed__0_value;
static const lean_string_object l_Lean_Lsp_instToJsonPartialResultParams_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "partialResultToken"};
static const lean_object* l_Lean_Lsp_instToJsonPartialResultParams_toJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonPartialResultParams_toJson___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonPartialResultParams_toJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonPartialResultParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonPartialResultParams_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonPartialResultParams___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonPartialResultParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonPartialResultParams = (const lean_object*)&l_Lean_Lsp_instToJsonPartialResultParams___closed__0_value;
static const lean_string_object l_Lean_Lsp_instFromJsonPartialResultParams_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "PartialResultParams"};
static const lean_object* l_Lean_Lsp_instFromJsonPartialResultParams_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonPartialResultParams_fromJson___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonPartialResultParams_fromJson___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonLocation_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonPartialResultParams_fromJson___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonPartialResultParams_fromJson___closed__1_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonLocation_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonPartialResultParams_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonPartialResultParams_fromJson___closed__1_value_aux_1),((lean_object*)&l_Lean_Lsp_instFromJsonPartialResultParams_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(207, 225, 75, 153, 56, 162, 219, 65)}};
static const lean_object* l_Lean_Lsp_instFromJsonPartialResultParams_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonPartialResultParams_fromJson___closed__1_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonPartialResultParams_fromJson___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonPartialResultParams_fromJson___closed__2;
static lean_once_cell_t l_Lean_Lsp_instFromJsonPartialResultParams_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonPartialResultParams_fromJson___closed__3;
static const lean_string_object l_Lean_Lsp_instFromJsonPartialResultParams_fromJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "partialResultToken\?"};
static const lean_object* l_Lean_Lsp_instFromJsonPartialResultParams_fromJson___closed__4 = (const lean_object*)&l_Lean_Lsp_instFromJsonPartialResultParams_fromJson___closed__4_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonPartialResultParams_fromJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonPartialResultParams_fromJson___closed__4_value),LEAN_SCALAR_PTR_LITERAL(29, 35, 64, 120, 46, 112, 112, 255)}};
static const lean_object* l_Lean_Lsp_instFromJsonPartialResultParams_fromJson___closed__5 = (const lean_object*)&l_Lean_Lsp_instFromJsonPartialResultParams_fromJson___closed__5_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonPartialResultParams_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonPartialResultParams_fromJson___closed__6;
static lean_once_cell_t l_Lean_Lsp_instFromJsonPartialResultParams_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonPartialResultParams_fromJson___closed__7;
static lean_once_cell_t l_Lean_Lsp_instFromJsonPartialResultParams_fromJson___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonPartialResultParams_fromJson___closed__8;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonPartialResultParams_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonPartialResultParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonPartialResultParams_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonPartialResultParams___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonPartialResultParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonPartialResultParams = (const lean_object*)&l_Lean_Lsp_instFromJsonPartialResultParams___closed__0_value;
static const lean_string_object l_Lean_Lsp_instToJsonWorkDoneProgressOptions_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "workDoneProgress"};
static const lean_object* l_Lean_Lsp_instToJsonWorkDoneProgressOptions_toJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonWorkDoneProgressOptions_toJson___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonWorkDoneProgressOptions_toJson(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonWorkDoneProgressOptions_toJson___boxed(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonWorkDoneProgressOptions___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonWorkDoneProgressOptions_toJson___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonWorkDoneProgressOptions___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonWorkDoneProgressOptions___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonWorkDoneProgressOptions = (const lean_object*)&l_Lean_Lsp_instToJsonWorkDoneProgressOptions___closed__0_value;
static const lean_string_object l_Lean_Lsp_instFromJsonWorkDoneProgressOptions_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "WorkDoneProgressOptions"};
static const lean_object* l_Lean_Lsp_instFromJsonWorkDoneProgressOptions_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonWorkDoneProgressOptions_fromJson___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonWorkDoneProgressOptions_fromJson___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonLocation_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonWorkDoneProgressOptions_fromJson___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonWorkDoneProgressOptions_fromJson___closed__1_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonLocation_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonWorkDoneProgressOptions_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonWorkDoneProgressOptions_fromJson___closed__1_value_aux_1),((lean_object*)&l_Lean_Lsp_instFromJsonWorkDoneProgressOptions_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(169, 128, 234, 9, 207, 171, 228, 26)}};
static const lean_object* l_Lean_Lsp_instFromJsonWorkDoneProgressOptions_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonWorkDoneProgressOptions_fromJson___closed__1_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonWorkDoneProgressOptions_fromJson___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonWorkDoneProgressOptions_fromJson___closed__2;
static lean_once_cell_t l_Lean_Lsp_instFromJsonWorkDoneProgressOptions_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonWorkDoneProgressOptions_fromJson___closed__3;
static const lean_ctor_object l_Lean_Lsp_instFromJsonWorkDoneProgressOptions_fromJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instToJsonWorkDoneProgressOptions_toJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(30, 28, 234, 148, 40, 91, 235, 8)}};
static const lean_object* l_Lean_Lsp_instFromJsonWorkDoneProgressOptions_fromJson___closed__4 = (const lean_object*)&l_Lean_Lsp_instFromJsonWorkDoneProgressOptions_fromJson___closed__4_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonWorkDoneProgressOptions_fromJson___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonWorkDoneProgressOptions_fromJson___closed__5;
static lean_once_cell_t l_Lean_Lsp_instFromJsonWorkDoneProgressOptions_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonWorkDoneProgressOptions_fromJson___closed__6;
static lean_once_cell_t l_Lean_Lsp_instFromJsonWorkDoneProgressOptions_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonWorkDoneProgressOptions_fromJson___closed__7;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonWorkDoneProgressOptions_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonWorkDoneProgressOptions___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonWorkDoneProgressOptions_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonWorkDoneProgressOptions___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonWorkDoneProgressOptions___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonWorkDoneProgressOptions = (const lean_object*)&l_Lean_Lsp_instFromJsonWorkDoneProgressOptions___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonResolveSupport_fromJson_spec__0_spec__0_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonResolveSupport_fromJson_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonResolveSupport_fromJson_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonResolveSupport_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonResolveSupport_fromJson_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instFromJsonResolveSupport_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "properties"};
static const lean_object* l_Lean_Lsp_instFromJsonResolveSupport_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonResolveSupport_fromJson___closed__0_value;
static const lean_string_object l_Lean_Lsp_instFromJsonResolveSupport_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "ResolveSupport"};
static const lean_object* l_Lean_Lsp_instFromJsonResolveSupport_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonResolveSupport_fromJson___closed__1_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonResolveSupport_fromJson___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonLocation_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonResolveSupport_fromJson___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonResolveSupport_fromJson___closed__2_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonLocation_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonResolveSupport_fromJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonResolveSupport_fromJson___closed__2_value_aux_1),((lean_object*)&l_Lean_Lsp_instFromJsonResolveSupport_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(167, 30, 224, 186, 11, 21, 232, 51)}};
static const lean_object* l_Lean_Lsp_instFromJsonResolveSupport_fromJson___closed__2 = (const lean_object*)&l_Lean_Lsp_instFromJsonResolveSupport_fromJson___closed__2_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonResolveSupport_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonResolveSupport_fromJson___closed__3;
static lean_once_cell_t l_Lean_Lsp_instFromJsonResolveSupport_fromJson___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonResolveSupport_fromJson___closed__4;
static const lean_ctor_object l_Lean_Lsp_instFromJsonResolveSupport_fromJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonResolveSupport_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(15, 175, 253, 162, 13, 144, 103, 64)}};
static const lean_object* l_Lean_Lsp_instFromJsonResolveSupport_fromJson___closed__5 = (const lean_object*)&l_Lean_Lsp_instFromJsonResolveSupport_fromJson___closed__5_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonResolveSupport_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonResolveSupport_fromJson___closed__6;
static lean_once_cell_t l_Lean_Lsp_instFromJsonResolveSupport_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonResolveSupport_fromJson___closed__7;
static lean_once_cell_t l_Lean_Lsp_instFromJsonResolveSupport_fromJson___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonResolveSupport_fromJson___closed__8;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonResolveSupport_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonResolveSupport___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonResolveSupport_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonResolveSupport___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonResolveSupport___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonResolveSupport = (const lean_object*)&l_Lean_Lsp_instFromJsonResolveSupport___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonResolveSupport_toJson_spec__0_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonResolveSupport_toJson_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Lsp_instToJsonResolveSupport_toJson_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonResolveSupport_toJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonResolveSupport___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonResolveSupport_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonResolveSupport___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonResolveSupport___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonResolveSupport = (const lean_object*)&l_Lean_Lsp_instToJsonResolveSupport___closed__0_value;
static lean_object* _init_l_Lean_Lsp_instInhabitedLocation_default___closed__1(void){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_2_ = l_Lean_Lsp_instInhabitedRange_default;
v___x_3_ = ((lean_object*)(l_Lean_Lsp_instInhabitedLocation_default___closed__0));
v___x_4_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4_, 0, v___x_3_);
lean_ctor_set(v___x_4_, 1, v___x_2_);
return v___x_4_;
}
}
static lean_object* _init_l_Lean_Lsp_instInhabitedLocation_default(void){
_start:
{
lean_object* v___x_5_; 
v___x_5_ = lean_obj_once(&l_Lean_Lsp_instInhabitedLocation_default___closed__1, &l_Lean_Lsp_instInhabitedLocation_default___closed__1_once, _init_l_Lean_Lsp_instInhabitedLocation_default___closed__1);
return v___x_5_;
}
}
static lean_object* _init_l_Lean_Lsp_instInhabitedLocation(void){
_start:
{
lean_object* v___x_6_; 
v___x_6_ = l_Lean_Lsp_instInhabitedLocation_default;
return v___x_6_;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_instBEqLocation_beq(lean_object* v_x_7_, lean_object* v_x_8_){
_start:
{
lean_object* v_uri_9_; lean_object* v_range_10_; lean_object* v_uri_11_; lean_object* v_range_12_; uint8_t v___x_13_; 
v_uri_9_ = lean_ctor_get(v_x_7_, 0);
v_range_10_ = lean_ctor_get(v_x_7_, 1);
v_uri_11_ = lean_ctor_get(v_x_8_, 0);
v_range_12_ = lean_ctor_get(v_x_8_, 1);
v___x_13_ = lean_string_dec_eq(v_uri_9_, v_uri_11_);
if (v___x_13_ == 0)
{
return v___x_13_;
}
else
{
uint8_t v___x_14_; 
v___x_14_ = l_Lean_Lsp_instBEqRange_beq(v_range_10_, v_range_12_);
return v___x_14_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqLocation_beq___boxed(lean_object* v_x_15_, lean_object* v_x_16_){
_start:
{
uint8_t v_res_17_; lean_object* v_r_18_; 
v_res_17_ = l_Lean_Lsp_instBEqLocation_beq(v_x_15_, v_x_16_);
lean_dec_ref(v_x_16_);
lean_dec_ref(v_x_15_);
v_r_18_ = lean_box(v_res_17_);
return v_r_18_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLocation_toJson_spec__0(lean_object* v_a_21_, lean_object* v_a_22_){
_start:
{
if (lean_obj_tag(v_a_21_) == 0)
{
lean_object* v___x_23_; 
v___x_23_ = lean_array_to_list(v_a_22_);
return v___x_23_;
}
else
{
lean_object* v_head_24_; lean_object* v_tail_25_; lean_object* v___x_26_; 
v_head_24_ = lean_ctor_get(v_a_21_, 0);
lean_inc(v_head_24_);
v_tail_25_ = lean_ctor_get(v_a_21_, 1);
lean_inc(v_tail_25_);
lean_dec_ref_known(v_a_21_, 2);
v___x_26_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_22_, v_head_24_);
v_a_21_ = v_tail_25_;
v_a_22_ = v___x_26_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLocation_toJson(lean_object* v_x_32_){
_start:
{
lean_object* v_uri_33_; lean_object* v_range_34_; lean_object* v___x_36_; uint8_t v_isShared_37_; uint8_t v_isSharedCheck_54_; 
v_uri_33_ = lean_ctor_get(v_x_32_, 0);
v_range_34_ = lean_ctor_get(v_x_32_, 1);
v_isSharedCheck_54_ = !lean_is_exclusive(v_x_32_);
if (v_isSharedCheck_54_ == 0)
{
v___x_36_ = v_x_32_;
v_isShared_37_ = v_isSharedCheck_54_;
goto v_resetjp_35_;
}
else
{
lean_inc(v_range_34_);
lean_inc(v_uri_33_);
lean_dec(v_x_32_);
v___x_36_ = lean_box(0);
v_isShared_37_ = v_isSharedCheck_54_;
goto v_resetjp_35_;
}
v_resetjp_35_:
{
lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_41_; 
v___x_38_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__0));
v___x_39_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_39_, 0, v_uri_33_);
if (v_isShared_37_ == 0)
{
lean_ctor_set(v___x_36_, 1, v___x_39_);
lean_ctor_set(v___x_36_, 0, v___x_38_);
v___x_41_ = v___x_36_;
goto v_reusejp_40_;
}
else
{
lean_object* v_reuseFailAlloc_53_; 
v_reuseFailAlloc_53_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_53_, 0, v___x_38_);
lean_ctor_set(v_reuseFailAlloc_53_, 1, v___x_39_);
v___x_41_ = v_reuseFailAlloc_53_;
goto v_reusejp_40_;
}
v_reusejp_40_:
{
lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_42_ = lean_box(0);
v___x_43_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_43_, 0, v___x_41_);
lean_ctor_set(v___x_43_, 1, v___x_42_);
v___x_44_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__1));
v___x_45_ = l_Lean_Lsp_instToJsonRange_toJson(v_range_34_);
v___x_46_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_46_, 0, v___x_44_);
lean_ctor_set(v___x_46_, 1, v___x_45_);
v___x_47_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_47_, 0, v___x_46_);
lean_ctor_set(v___x_47_, 1, v___x_42_);
v___x_48_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_48_, 0, v___x_47_);
lean_ctor_set(v___x_48_, 1, v___x_42_);
v___x_49_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_49_, 0, v___x_43_);
lean_ctor_set(v___x_49_, 1, v___x_48_);
v___x_50_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__2));
v___x_51_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLocation_toJson_spec__0(v___x_49_, v___x_50_);
v___x_52_ = l_Lean_Json_mkObj(v___x_51_);
lean_dec(v___x_51_);
return v___x_52_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocation_fromJson_spec__0(lean_object* v_j_57_, lean_object* v_k_58_){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_59_ = l_Lean_Json_getObjValD(v_j_57_, v_k_58_);
v___x_60_ = l_Lean_Json_getStr_x3f(v___x_59_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocation_fromJson_spec__0___boxed(lean_object* v_j_61_, lean_object* v_k_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocation_fromJson_spec__0(v_j_61_, v_k_62_);
lean_dec_ref(v_k_62_);
return v_res_63_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocation_fromJson_spec__1(lean_object* v_j_64_, lean_object* v_k_65_){
_start:
{
lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_66_ = l_Lean_Json_getObjValD(v_j_64_, v_k_65_);
v___x_67_ = l_Lean_Lsp_instFromJsonRange_fromJson(v___x_66_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocation_fromJson_spec__1___boxed(lean_object* v_j_68_, lean_object* v_k_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocation_fromJson_spec__1(v_j_68_, v_k_69_);
lean_dec_ref(v_k_69_);
return v_res_70_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLocation_fromJson___closed__4(void){
_start:
{
uint8_t v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; 
v___x_78_ = 1;
v___x_79_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__3));
v___x_80_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_79_, v___x_78_);
return v___x_80_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLocation_fromJson___closed__6(void){
_start:
{
lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_82_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__5));
v___x_83_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLocation_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLocation_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLocation_fromJson___closed__4);
v___x_84_ = lean_string_append(v___x_83_, v___x_82_);
return v___x_84_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLocation_fromJson___closed__8(void){
_start:
{
uint8_t v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_87_ = 1;
v___x_88_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__7));
v___x_89_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_88_, v___x_87_);
return v___x_89_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLocation_fromJson___closed__9(void){
_start:
{
lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_90_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLocation_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLocation_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLocation_fromJson___closed__8);
v___x_91_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLocation_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLocation_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLocation_fromJson___closed__6);
v___x_92_ = lean_string_append(v___x_91_, v___x_90_);
return v___x_92_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLocation_fromJson___closed__11(void){
_start:
{
lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_94_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_95_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLocation_fromJson___closed__9, &l_Lean_Lsp_instFromJsonLocation_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonLocation_fromJson___closed__9);
v___x_96_ = lean_string_append(v___x_95_, v___x_94_);
return v___x_96_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLocation_fromJson___closed__13(void){
_start:
{
uint8_t v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_99_ = 1;
v___x_100_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__12));
v___x_101_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_100_, v___x_99_);
return v___x_101_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLocation_fromJson___closed__14(void){
_start:
{
lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_102_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLocation_fromJson___closed__13, &l_Lean_Lsp_instFromJsonLocation_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonLocation_fromJson___closed__13);
v___x_103_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLocation_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLocation_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLocation_fromJson___closed__6);
v___x_104_ = lean_string_append(v___x_103_, v___x_102_);
return v___x_104_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLocation_fromJson___closed__15(void){
_start:
{
lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_105_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_106_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLocation_fromJson___closed__14, &l_Lean_Lsp_instFromJsonLocation_fromJson___closed__14_once, _init_l_Lean_Lsp_instFromJsonLocation_fromJson___closed__14);
v___x_107_ = lean_string_append(v___x_106_, v___x_105_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLocation_fromJson(lean_object* v_json_108_){
_start:
{
lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_109_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__0));
lean_inc(v_json_108_);
v___x_110_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocation_fromJson_spec__0(v_json_108_, v___x_109_);
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
v___x_115_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLocation_fromJson___closed__11, &l_Lean_Lsp_instFromJsonLocation_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonLocation_fromJson___closed__11);
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
lean_dec_ref_known(v___x_110_, 1);
v___x_130_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__1));
v___x_131_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocation_fromJson_spec__1(v_json_108_, v___x_130_);
if (lean_obj_tag(v___x_131_) == 0)
{
lean_object* v_a_132_; lean_object* v___x_134_; uint8_t v_isShared_135_; uint8_t v_isSharedCheck_141_; 
lean_dec(v_a_129_);
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
v___x_136_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLocation_fromJson___closed__15, &l_Lean_Lsp_instFromJsonLocation_fromJson___closed__15_once, _init_l_Lean_Lsp_instFromJsonLocation_fromJson___closed__15);
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
lean_object* v_a_150_; lean_object* v___x_152_; uint8_t v_isShared_153_; uint8_t v_isSharedCheck_158_; 
v_a_150_ = lean_ctor_get(v___x_131_, 0);
v_isSharedCheck_158_ = !lean_is_exclusive(v___x_131_);
if (v_isSharedCheck_158_ == 0)
{
v___x_152_ = v___x_131_;
v_isShared_153_ = v_isSharedCheck_158_;
goto v_resetjp_151_;
}
else
{
lean_inc(v_a_150_);
lean_dec(v___x_131_);
v___x_152_ = lean_box(0);
v_isShared_153_ = v_isSharedCheck_158_;
goto v_resetjp_151_;
}
v_resetjp_151_:
{
lean_object* v___x_154_; lean_object* v___x_156_; 
v___x_154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_154_, 0, v_a_129_);
lean_ctor_set(v___x_154_, 1, v_a_150_);
if (v_isShared_153_ == 0)
{
lean_ctor_set(v___x_152_, 0, v___x_154_);
v___x_156_ = v___x_152_;
goto v_reusejp_155_;
}
else
{
lean_object* v_reuseFailAlloc_157_; 
v_reuseFailAlloc_157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_157_, 0, v___x_154_);
v___x_156_ = v_reuseFailAlloc_157_;
goto v_reusejp_155_;
}
v_reusejp_155_:
{
return v___x_156_;
}
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_instOrdLocation_ord(lean_object* v_x_161_, lean_object* v_x_162_){
_start:
{
lean_object* v_uri_163_; lean_object* v_range_164_; lean_object* v_uri_165_; lean_object* v_range_166_; uint8_t v___x_167_; 
v_uri_163_ = lean_ctor_get(v_x_161_, 0);
v_range_164_ = lean_ctor_get(v_x_161_, 1);
v_uri_165_ = lean_ctor_get(v_x_162_, 0);
v_range_166_ = lean_ctor_get(v_x_162_, 1);
v___x_167_ = lean_string_compare(v_uri_163_, v_uri_165_);
if (v___x_167_ == 1)
{
uint8_t v___x_168_; 
v___x_168_ = l_Lean_Lsp_instOrdRange_ord(v_range_164_, v_range_166_);
if (v___x_168_ == 1)
{
return v___x_168_;
}
else
{
return v___x_168_;
}
}
else
{
return v___x_167_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instOrdLocation_ord___boxed(lean_object* v_x_169_, lean_object* v_x_170_){
_start:
{
uint8_t v_res_171_; lean_object* v_r_172_; 
v_res_171_ = l_Lean_Lsp_instOrdLocation_ord(v_x_169_, v_x_170_);
lean_dec_ref(v_x_170_);
lean_dec_ref(v_x_169_);
v_r_172_ = lean_box(v_res_171_);
return v_r_172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLocationLink_toJson_spec__0(lean_object* v_k_175_, lean_object* v_x_176_){
_start:
{
if (lean_obj_tag(v_x_176_) == 0)
{
lean_object* v___x_177_; 
lean_dec_ref(v_k_175_);
v___x_177_ = lean_box(0);
return v___x_177_;
}
else
{
lean_object* v_val_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
v_val_178_ = lean_ctor_get(v_x_176_, 0);
lean_inc(v_val_178_);
lean_dec_ref_known(v_x_176_, 1);
v___x_179_ = l_Lean_Lsp_instToJsonRange_toJson(v_val_178_);
v___x_180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_180_, 0, v_k_175_);
lean_ctor_set(v___x_180_, 1, v___x_179_);
v___x_181_ = lean_box(0);
v___x_182_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_182_, 0, v___x_180_);
lean_ctor_set(v___x_182_, 1, v___x_181_);
return v___x_182_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLocationLink_toJson(lean_object* v_x_187_){
_start:
{
lean_object* v_originSelectionRange_x3f_188_; lean_object* v_targetUri_189_; lean_object* v_targetRange_190_; lean_object* v_targetSelectionRange_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; 
v_originSelectionRange_x3f_188_ = lean_ctor_get(v_x_187_, 0);
lean_inc(v_originSelectionRange_x3f_188_);
v_targetUri_189_ = lean_ctor_get(v_x_187_, 1);
lean_inc_ref(v_targetUri_189_);
v_targetRange_190_ = lean_ctor_get(v_x_187_, 2);
lean_inc_ref(v_targetRange_190_);
v_targetSelectionRange_191_ = lean_ctor_get(v_x_187_, 3);
lean_inc_ref(v_targetSelectionRange_191_);
lean_dec_ref(v_x_187_);
v___x_192_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocationLink_toJson___closed__0));
v___x_193_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLocationLink_toJson_spec__0(v___x_192_, v_originSelectionRange_x3f_188_);
v___x_194_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocationLink_toJson___closed__1));
v___x_195_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_195_, 0, v_targetUri_189_);
v___x_196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_196_, 0, v___x_194_);
lean_ctor_set(v___x_196_, 1, v___x_195_);
v___x_197_ = lean_box(0);
v___x_198_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_198_, 0, v___x_196_);
lean_ctor_set(v___x_198_, 1, v___x_197_);
v___x_199_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocationLink_toJson___closed__2));
v___x_200_ = l_Lean_Lsp_instToJsonRange_toJson(v_targetRange_190_);
v___x_201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_201_, 0, v___x_199_);
lean_ctor_set(v___x_201_, 1, v___x_200_);
v___x_202_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_202_, 0, v___x_201_);
lean_ctor_set(v___x_202_, 1, v___x_197_);
v___x_203_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocationLink_toJson___closed__3));
v___x_204_ = l_Lean_Lsp_instToJsonRange_toJson(v_targetSelectionRange_191_);
v___x_205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_205_, 0, v___x_203_);
lean_ctor_set(v___x_205_, 1, v___x_204_);
v___x_206_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_206_, 0, v___x_205_);
lean_ctor_set(v___x_206_, 1, v___x_197_);
v___x_207_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_207_, 0, v___x_206_);
lean_ctor_set(v___x_207_, 1, v___x_197_);
v___x_208_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_208_, 0, v___x_202_);
lean_ctor_set(v___x_208_, 1, v___x_207_);
v___x_209_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_209_, 0, v___x_198_);
lean_ctor_set(v___x_209_, 1, v___x_208_);
v___x_210_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_210_, 0, v___x_193_);
lean_ctor_set(v___x_210_, 1, v___x_209_);
v___x_211_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__2));
v___x_212_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLocation_toJson_spec__0(v___x_210_, v___x_211_);
v___x_213_ = l_Lean_Json_mkObj(v___x_212_);
lean_dec(v___x_212_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocationLink_fromJson_spec__0_spec__0(lean_object* v_x_218_){
_start:
{
if (lean_obj_tag(v_x_218_) == 0)
{
lean_object* v___x_219_; 
v___x_219_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocationLink_fromJson_spec__0_spec__0___closed__0));
return v___x_219_;
}
else
{
lean_object* v___x_220_; 
v___x_220_ = l_Lean_Lsp_instFromJsonRange_fromJson(v_x_218_);
if (lean_obj_tag(v___x_220_) == 0)
{
lean_object* v_a_221_; lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_228_; 
v_a_221_ = lean_ctor_get(v___x_220_, 0);
v_isSharedCheck_228_ = !lean_is_exclusive(v___x_220_);
if (v_isSharedCheck_228_ == 0)
{
v___x_223_ = v___x_220_;
v_isShared_224_ = v_isSharedCheck_228_;
goto v_resetjp_222_;
}
else
{
lean_inc(v_a_221_);
lean_dec(v___x_220_);
v___x_223_ = lean_box(0);
v_isShared_224_ = v_isSharedCheck_228_;
goto v_resetjp_222_;
}
v_resetjp_222_:
{
lean_object* v___x_226_; 
if (v_isShared_224_ == 0)
{
v___x_226_ = v___x_223_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v_a_221_);
v___x_226_ = v_reuseFailAlloc_227_;
goto v_reusejp_225_;
}
v_reusejp_225_:
{
return v___x_226_;
}
}
}
else
{
lean_object* v_a_229_; lean_object* v___x_231_; uint8_t v_isShared_232_; uint8_t v_isSharedCheck_237_; 
v_a_229_ = lean_ctor_get(v___x_220_, 0);
v_isSharedCheck_237_ = !lean_is_exclusive(v___x_220_);
if (v_isSharedCheck_237_ == 0)
{
v___x_231_ = v___x_220_;
v_isShared_232_ = v_isSharedCheck_237_;
goto v_resetjp_230_;
}
else
{
lean_inc(v_a_229_);
lean_dec(v___x_220_);
v___x_231_ = lean_box(0);
v_isShared_232_ = v_isSharedCheck_237_;
goto v_resetjp_230_;
}
v_resetjp_230_:
{
lean_object* v___x_233_; lean_object* v___x_235_; 
v___x_233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_233_, 0, v_a_229_);
if (v_isShared_232_ == 0)
{
lean_ctor_set(v___x_231_, 0, v___x_233_);
v___x_235_ = v___x_231_;
goto v_reusejp_234_;
}
else
{
lean_object* v_reuseFailAlloc_236_; 
v_reuseFailAlloc_236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v___x_233_);
v___x_235_ = v_reuseFailAlloc_236_;
goto v_reusejp_234_;
}
v_reusejp_234_:
{
return v___x_235_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocationLink_fromJson_spec__0(lean_object* v_j_238_, lean_object* v_k_239_){
_start:
{
lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_240_ = l_Lean_Json_getObjValD(v_j_238_, v_k_239_);
v___x_241_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocationLink_fromJson_spec__0_spec__0(v___x_240_);
return v___x_241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocationLink_fromJson_spec__0___boxed(lean_object* v_j_242_, lean_object* v_k_243_){
_start:
{
lean_object* v_res_244_; 
v_res_244_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocationLink_fromJson_spec__0(v_j_242_, v_k_243_);
lean_dec_ref(v_k_243_);
return v_res_244_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__2(void){
_start:
{
uint8_t v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_250_ = 1;
v___x_251_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__1));
v___x_252_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_251_, v___x_250_);
return v___x_252_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__3(void){
_start:
{
lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_253_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__5));
v___x_254_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__2, &l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__2);
v___x_255_ = lean_string_append(v___x_254_, v___x_253_);
return v___x_255_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__6(void){
_start:
{
uint8_t v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; 
v___x_259_ = 1;
v___x_260_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__5));
v___x_261_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_260_, v___x_259_);
return v___x_261_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__7(void){
_start:
{
lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_262_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__6);
v___x_263_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__3);
v___x_264_ = lean_string_append(v___x_263_, v___x_262_);
return v___x_264_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__8(void){
_start:
{
lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_265_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_266_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__7);
v___x_267_ = lean_string_append(v___x_266_, v___x_265_);
return v___x_267_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__10(void){
_start:
{
uint8_t v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_270_ = 1;
v___x_271_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__9));
v___x_272_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_271_, v___x_270_);
return v___x_272_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__11(void){
_start:
{
lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_273_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__10, &l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__10);
v___x_274_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__3);
v___x_275_ = lean_string_append(v___x_274_, v___x_273_);
return v___x_275_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__12(void){
_start:
{
lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_276_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_277_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__11, &l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__11);
v___x_278_ = lean_string_append(v___x_277_, v___x_276_);
return v___x_278_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__14(void){
_start:
{
uint8_t v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_281_ = 1;
v___x_282_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__13));
v___x_283_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_282_, v___x_281_);
return v___x_283_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__15(void){
_start:
{
lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_284_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__14, &l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__14_once, _init_l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__14);
v___x_285_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__3);
v___x_286_ = lean_string_append(v___x_285_, v___x_284_);
return v___x_286_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__16(void){
_start:
{
lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_287_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_288_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__15, &l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__15_once, _init_l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__15);
v___x_289_ = lean_string_append(v___x_288_, v___x_287_);
return v___x_289_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__18(void){
_start:
{
uint8_t v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_292_ = 1;
v___x_293_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__17));
v___x_294_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_293_, v___x_292_);
return v___x_294_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__19(void){
_start:
{
lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_295_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__18, &l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__18_once, _init_l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__18);
v___x_296_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__3);
v___x_297_ = lean_string_append(v___x_296_, v___x_295_);
return v___x_297_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__20(void){
_start:
{
lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_298_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_299_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__19, &l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__19_once, _init_l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__19);
v___x_300_ = lean_string_append(v___x_299_, v___x_298_);
return v___x_300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLocationLink_fromJson(lean_object* v_json_301_){
_start:
{
lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_302_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocationLink_toJson___closed__0));
lean_inc(v_json_301_);
v___x_303_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocationLink_fromJson_spec__0(v_json_301_, v___x_302_);
if (lean_obj_tag(v___x_303_) == 0)
{
lean_object* v_a_304_; lean_object* v___x_306_; uint8_t v_isShared_307_; uint8_t v_isSharedCheck_313_; 
lean_dec(v_json_301_);
v_a_304_ = lean_ctor_get(v___x_303_, 0);
v_isSharedCheck_313_ = !lean_is_exclusive(v___x_303_);
if (v_isSharedCheck_313_ == 0)
{
v___x_306_ = v___x_303_;
v_isShared_307_ = v_isSharedCheck_313_;
goto v_resetjp_305_;
}
else
{
lean_inc(v_a_304_);
lean_dec(v___x_303_);
v___x_306_ = lean_box(0);
v_isShared_307_ = v_isSharedCheck_313_;
goto v_resetjp_305_;
}
v_resetjp_305_:
{
lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_311_; 
v___x_308_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__8);
v___x_309_ = lean_string_append(v___x_308_, v_a_304_);
lean_dec(v_a_304_);
if (v_isShared_307_ == 0)
{
lean_ctor_set(v___x_306_, 0, v___x_309_);
v___x_311_ = v___x_306_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v___x_309_);
v___x_311_ = v_reuseFailAlloc_312_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
return v___x_311_;
}
}
}
else
{
if (lean_obj_tag(v___x_303_) == 0)
{
lean_object* v_a_314_; lean_object* v___x_316_; uint8_t v_isShared_317_; uint8_t v_isSharedCheck_321_; 
lean_dec(v_json_301_);
v_a_314_ = lean_ctor_get(v___x_303_, 0);
v_isSharedCheck_321_ = !lean_is_exclusive(v___x_303_);
if (v_isSharedCheck_321_ == 0)
{
v___x_316_ = v___x_303_;
v_isShared_317_ = v_isSharedCheck_321_;
goto v_resetjp_315_;
}
else
{
lean_inc(v_a_314_);
lean_dec(v___x_303_);
v___x_316_ = lean_box(0);
v_isShared_317_ = v_isSharedCheck_321_;
goto v_resetjp_315_;
}
v_resetjp_315_:
{
lean_object* v___x_319_; 
if (v_isShared_317_ == 0)
{
lean_ctor_set_tag(v___x_316_, 0);
v___x_319_ = v___x_316_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v_a_314_);
v___x_319_ = v_reuseFailAlloc_320_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
return v___x_319_;
}
}
}
else
{
lean_object* v_a_322_; lean_object* v___x_323_; lean_object* v___x_324_; 
v_a_322_ = lean_ctor_get(v___x_303_, 0);
lean_inc(v_a_322_);
lean_dec_ref_known(v___x_303_, 1);
v___x_323_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocationLink_toJson___closed__1));
lean_inc(v_json_301_);
v___x_324_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocation_fromJson_spec__0(v_json_301_, v___x_323_);
if (lean_obj_tag(v___x_324_) == 0)
{
lean_object* v_a_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_334_; 
lean_dec(v_a_322_);
lean_dec(v_json_301_);
v_a_325_ = lean_ctor_get(v___x_324_, 0);
v_isSharedCheck_334_ = !lean_is_exclusive(v___x_324_);
if (v_isSharedCheck_334_ == 0)
{
v___x_327_ = v___x_324_;
v_isShared_328_ = v_isSharedCheck_334_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_a_325_);
lean_dec(v___x_324_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_334_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_332_; 
v___x_329_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__12, &l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__12);
v___x_330_ = lean_string_append(v___x_329_, v_a_325_);
lean_dec(v_a_325_);
if (v_isShared_328_ == 0)
{
lean_ctor_set(v___x_327_, 0, v___x_330_);
v___x_332_ = v___x_327_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v___x_330_);
v___x_332_ = v_reuseFailAlloc_333_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
return v___x_332_;
}
}
}
else
{
if (lean_obj_tag(v___x_324_) == 0)
{
lean_object* v_a_335_; lean_object* v___x_337_; uint8_t v_isShared_338_; uint8_t v_isSharedCheck_342_; 
lean_dec(v_a_322_);
lean_dec(v_json_301_);
v_a_335_ = lean_ctor_get(v___x_324_, 0);
v_isSharedCheck_342_ = !lean_is_exclusive(v___x_324_);
if (v_isSharedCheck_342_ == 0)
{
v___x_337_ = v___x_324_;
v_isShared_338_ = v_isSharedCheck_342_;
goto v_resetjp_336_;
}
else
{
lean_inc(v_a_335_);
lean_dec(v___x_324_);
v___x_337_ = lean_box(0);
v_isShared_338_ = v_isSharedCheck_342_;
goto v_resetjp_336_;
}
v_resetjp_336_:
{
lean_object* v___x_340_; 
if (v_isShared_338_ == 0)
{
lean_ctor_set_tag(v___x_337_, 0);
v___x_340_ = v___x_337_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v_a_335_);
v___x_340_ = v_reuseFailAlloc_341_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
return v___x_340_;
}
}
}
else
{
lean_object* v_a_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
v_a_343_ = lean_ctor_get(v___x_324_, 0);
lean_inc(v_a_343_);
lean_dec_ref_known(v___x_324_, 1);
v___x_344_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocationLink_toJson___closed__2));
lean_inc(v_json_301_);
v___x_345_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocation_fromJson_spec__1(v_json_301_, v___x_344_);
if (lean_obj_tag(v___x_345_) == 0)
{
lean_object* v_a_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_355_; 
lean_dec(v_a_343_);
lean_dec(v_a_322_);
lean_dec(v_json_301_);
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
v___x_350_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__16, &l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__16_once, _init_l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__16);
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
lean_dec(v_a_343_);
lean_dec(v_a_322_);
lean_dec(v_json_301_);
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
lean_object* v_a_364_; lean_object* v___x_365_; lean_object* v___x_366_; 
v_a_364_ = lean_ctor_get(v___x_345_, 0);
lean_inc(v_a_364_);
lean_dec_ref_known(v___x_345_, 1);
v___x_365_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocationLink_toJson___closed__3));
v___x_366_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocation_fromJson_spec__1(v_json_301_, v___x_365_);
if (lean_obj_tag(v___x_366_) == 0)
{
lean_object* v_a_367_; lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_376_; 
lean_dec(v_a_364_);
lean_dec(v_a_343_);
lean_dec(v_a_322_);
v_a_367_ = lean_ctor_get(v___x_366_, 0);
v_isSharedCheck_376_ = !lean_is_exclusive(v___x_366_);
if (v_isSharedCheck_376_ == 0)
{
v___x_369_ = v___x_366_;
v_isShared_370_ = v_isSharedCheck_376_;
goto v_resetjp_368_;
}
else
{
lean_inc(v_a_367_);
lean_dec(v___x_366_);
v___x_369_ = lean_box(0);
v_isShared_370_ = v_isSharedCheck_376_;
goto v_resetjp_368_;
}
v_resetjp_368_:
{
lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_374_; 
v___x_371_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__20, &l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__20_once, _init_l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__20);
v___x_372_ = lean_string_append(v___x_371_, v_a_367_);
lean_dec(v_a_367_);
if (v_isShared_370_ == 0)
{
lean_ctor_set(v___x_369_, 0, v___x_372_);
v___x_374_ = v___x_369_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v___x_372_);
v___x_374_ = v_reuseFailAlloc_375_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
return v___x_374_;
}
}
}
else
{
if (lean_obj_tag(v___x_366_) == 0)
{
lean_object* v_a_377_; lean_object* v___x_379_; uint8_t v_isShared_380_; uint8_t v_isSharedCheck_384_; 
lean_dec(v_a_364_);
lean_dec(v_a_343_);
lean_dec(v_a_322_);
v_a_377_ = lean_ctor_get(v___x_366_, 0);
v_isSharedCheck_384_ = !lean_is_exclusive(v___x_366_);
if (v_isSharedCheck_384_ == 0)
{
v___x_379_ = v___x_366_;
v_isShared_380_ = v_isSharedCheck_384_;
goto v_resetjp_378_;
}
else
{
lean_inc(v_a_377_);
lean_dec(v___x_366_);
v___x_379_ = lean_box(0);
v_isShared_380_ = v_isSharedCheck_384_;
goto v_resetjp_378_;
}
v_resetjp_378_:
{
lean_object* v___x_382_; 
if (v_isShared_380_ == 0)
{
lean_ctor_set_tag(v___x_379_, 0);
v___x_382_ = v___x_379_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v_a_377_);
v___x_382_ = v_reuseFailAlloc_383_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
return v___x_382_;
}
}
}
else
{
lean_object* v_a_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_393_; 
v_a_385_ = lean_ctor_get(v___x_366_, 0);
v_isSharedCheck_393_ = !lean_is_exclusive(v___x_366_);
if (v_isSharedCheck_393_ == 0)
{
v___x_387_ = v___x_366_;
v_isShared_388_ = v_isSharedCheck_393_;
goto v_resetjp_386_;
}
else
{
lean_inc(v_a_385_);
lean_dec(v___x_366_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_393_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
lean_object* v___x_389_; lean_object* v___x_391_; 
v___x_389_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_389_, 0, v_a_322_);
lean_ctor_set(v___x_389_, 1, v_a_343_);
lean_ctor_set(v___x_389_, 2, v_a_364_);
lean_ctor_set(v___x_389_, 3, v_a_385_);
if (v_isShared_388_ == 0)
{
lean_ctor_set(v___x_387_, 0, v___x_389_);
v___x_391_ = v___x_387_;
goto v_reusejp_390_;
}
else
{
lean_object* v_reuseFailAlloc_392_; 
v_reuseFailAlloc_392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_392_, 0, v___x_389_);
v___x_391_ = v_reuseFailAlloc_392_;
goto v_reusejp_390_;
}
v_reusejp_390_:
{
return v___x_391_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonCommand_toJson_spec__0_spec__0_spec__1(size_t v_sz_396_, size_t v_i_397_, lean_object* v_bs_398_){
_start:
{
uint8_t v___x_399_; 
v___x_399_ = lean_usize_dec_lt(v_i_397_, v_sz_396_);
if (v___x_399_ == 0)
{
return v_bs_398_;
}
else
{
lean_object* v_v_400_; lean_object* v___x_401_; lean_object* v_bs_x27_402_; size_t v___x_403_; size_t v___x_404_; lean_object* v___x_405_; 
v_v_400_ = lean_array_uget(v_bs_398_, v_i_397_);
v___x_401_ = lean_unsigned_to_nat(0u);
v_bs_x27_402_ = lean_array_uset(v_bs_398_, v_i_397_, v___x_401_);
v___x_403_ = ((size_t)1ULL);
v___x_404_ = lean_usize_add(v_i_397_, v___x_403_);
v___x_405_ = lean_array_uset(v_bs_x27_402_, v_i_397_, v_v_400_);
v_i_397_ = v___x_404_;
v_bs_398_ = v___x_405_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonCommand_toJson_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_407_, lean_object* v_i_408_, lean_object* v_bs_409_){
_start:
{
size_t v_sz_boxed_410_; size_t v_i_boxed_411_; lean_object* v_res_412_; 
v_sz_boxed_410_ = lean_unbox_usize(v_sz_407_);
lean_dec(v_sz_407_);
v_i_boxed_411_ = lean_unbox_usize(v_i_408_);
lean_dec(v_i_408_);
v_res_412_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonCommand_toJson_spec__0_spec__0_spec__1(v_sz_boxed_410_, v_i_boxed_411_, v_bs_409_);
return v_res_412_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonCommand_toJson_spec__0_spec__0(lean_object* v_a_413_){
_start:
{
size_t v_sz_414_; size_t v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; 
v_sz_414_ = lean_array_size(v_a_413_);
v___x_415_ = ((size_t)0ULL);
v___x_416_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonCommand_toJson_spec__0_spec__0_spec__1(v_sz_414_, v___x_415_, v_a_413_);
v___x_417_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_417_, 0, v___x_416_);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonCommand_toJson_spec__0(lean_object* v_k_418_, lean_object* v_x_419_){
_start:
{
if (lean_obj_tag(v_x_419_) == 0)
{
lean_object* v___x_420_; 
lean_dec_ref(v_k_418_);
v___x_420_ = lean_box(0);
return v___x_420_;
}
else
{
lean_object* v_val_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; 
v_val_421_ = lean_ctor_get(v_x_419_, 0);
lean_inc(v_val_421_);
lean_dec_ref_known(v_x_419_, 1);
v___x_422_ = l_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonCommand_toJson_spec__0_spec__0(v_val_421_);
v___x_423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_423_, 0, v_k_418_);
lean_ctor_set(v___x_423_, 1, v___x_422_);
v___x_424_ = lean_box(0);
v___x_425_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_425_, 0, v___x_423_);
lean_ctor_set(v___x_425_, 1, v___x_424_);
return v___x_425_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonCommand_toJson(lean_object* v_x_429_){
_start:
{
lean_object* v_title_430_; lean_object* v_command_431_; lean_object* v_arguments_x3f_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; 
v_title_430_ = lean_ctor_get(v_x_429_, 0);
lean_inc_ref(v_title_430_);
v_command_431_ = lean_ctor_get(v_x_429_, 1);
lean_inc_ref(v_command_431_);
v_arguments_x3f_432_ = lean_ctor_get(v_x_429_, 2);
lean_inc(v_arguments_x3f_432_);
lean_dec_ref(v_x_429_);
v___x_433_ = ((lean_object*)(l_Lean_Lsp_instToJsonCommand_toJson___closed__0));
v___x_434_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_434_, 0, v_title_430_);
v___x_435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_435_, 0, v___x_433_);
lean_ctor_set(v___x_435_, 1, v___x_434_);
v___x_436_ = lean_box(0);
v___x_437_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_437_, 0, v___x_435_);
lean_ctor_set(v___x_437_, 1, v___x_436_);
v___x_438_ = ((lean_object*)(l_Lean_Lsp_instToJsonCommand_toJson___closed__1));
v___x_439_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_439_, 0, v_command_431_);
v___x_440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_440_, 0, v___x_438_);
lean_ctor_set(v___x_440_, 1, v___x_439_);
v___x_441_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_441_, 0, v___x_440_);
lean_ctor_set(v___x_441_, 1, v___x_436_);
v___x_442_ = ((lean_object*)(l_Lean_Lsp_instToJsonCommand_toJson___closed__2));
v___x_443_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonCommand_toJson_spec__0(v___x_442_, v_arguments_x3f_432_);
v___x_444_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_444_, 0, v___x_443_);
lean_ctor_set(v___x_444_, 1, v___x_436_);
v___x_445_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_445_, 0, v___x_441_);
lean_ctor_set(v___x_445_, 1, v___x_444_);
v___x_446_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_446_, 0, v___x_437_);
lean_ctor_set(v___x_446_, 1, v___x_445_);
v___x_447_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__2));
v___x_448_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLocation_toJson_spec__0(v___x_446_, v___x_447_);
v___x_449_ = l_Lean_Json_mkObj(v___x_448_);
lean_dec(v___x_448_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCommand_fromJson_spec__0_spec__0_spec__1_spec__2(size_t v_sz_452_, size_t v_i_453_, lean_object* v_bs_454_){
_start:
{
uint8_t v___x_455_; 
v___x_455_ = lean_usize_dec_lt(v_i_453_, v_sz_452_);
if (v___x_455_ == 0)
{
lean_object* v___x_456_; 
v___x_456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_456_, 0, v_bs_454_);
return v___x_456_;
}
else
{
lean_object* v_v_457_; lean_object* v___x_458_; lean_object* v_bs_x27_459_; size_t v___x_460_; size_t v___x_461_; lean_object* v___x_462_; 
v_v_457_ = lean_array_uget(v_bs_454_, v_i_453_);
v___x_458_ = lean_unsigned_to_nat(0u);
v_bs_x27_459_ = lean_array_uset(v_bs_454_, v_i_453_, v___x_458_);
v___x_460_ = ((size_t)1ULL);
v___x_461_ = lean_usize_add(v_i_453_, v___x_460_);
v___x_462_ = lean_array_uset(v_bs_x27_459_, v_i_453_, v_v_457_);
v_i_453_ = v___x_461_;
v_bs_454_ = v___x_462_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCommand_fromJson_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_sz_464_, lean_object* v_i_465_, lean_object* v_bs_466_){
_start:
{
size_t v_sz_boxed_467_; size_t v_i_boxed_468_; lean_object* v_res_469_; 
v_sz_boxed_467_ = lean_unbox_usize(v_sz_464_);
lean_dec(v_sz_464_);
v_i_boxed_468_ = lean_unbox_usize(v_i_465_);
lean_dec(v_i_465_);
v_res_469_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCommand_fromJson_spec__0_spec__0_spec__1_spec__2(v_sz_boxed_467_, v_i_boxed_468_, v_bs_466_);
return v_res_469_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCommand_fromJson_spec__0_spec__0_spec__1(lean_object* v_x_472_){
_start:
{
if (lean_obj_tag(v_x_472_) == 4)
{
lean_object* v_elems_473_; size_t v_sz_474_; size_t v___x_475_; lean_object* v___x_476_; 
v_elems_473_ = lean_ctor_get(v_x_472_, 0);
lean_inc_ref(v_elems_473_);
lean_dec_ref_known(v_x_472_, 1);
v_sz_474_ = lean_array_size(v_elems_473_);
v___x_475_ = ((size_t)0ULL);
v___x_476_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCommand_fromJson_spec__0_spec__0_spec__1_spec__2(v_sz_474_, v___x_475_, v_elems_473_);
return v___x_476_;
}
else
{
lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_477_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCommand_fromJson_spec__0_spec__0_spec__1___closed__0));
v___x_478_ = lean_unsigned_to_nat(80u);
v___x_479_ = l_Lean_Json_pretty(v_x_472_, v___x_478_);
v___x_480_ = lean_string_append(v___x_477_, v___x_479_);
lean_dec_ref(v___x_479_);
v___x_481_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCommand_fromJson_spec__0_spec__0_spec__1___closed__1));
v___x_482_ = lean_string_append(v___x_480_, v___x_481_);
v___x_483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_483_, 0, v___x_482_);
return v___x_483_;
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCommand_fromJson_spec__0_spec__0(lean_object* v_x_486_){
_start:
{
if (lean_obj_tag(v_x_486_) == 0)
{
lean_object* v___x_487_; 
v___x_487_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCommand_fromJson_spec__0_spec__0___closed__0));
return v___x_487_;
}
else
{
lean_object* v___x_488_; 
v___x_488_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCommand_fromJson_spec__0_spec__0_spec__1(v_x_486_);
if (lean_obj_tag(v___x_488_) == 0)
{
lean_object* v_a_489_; lean_object* v___x_491_; uint8_t v_isShared_492_; uint8_t v_isSharedCheck_496_; 
v_a_489_ = lean_ctor_get(v___x_488_, 0);
v_isSharedCheck_496_ = !lean_is_exclusive(v___x_488_);
if (v_isSharedCheck_496_ == 0)
{
v___x_491_ = v___x_488_;
v_isShared_492_ = v_isSharedCheck_496_;
goto v_resetjp_490_;
}
else
{
lean_inc(v_a_489_);
lean_dec(v___x_488_);
v___x_491_ = lean_box(0);
v_isShared_492_ = v_isSharedCheck_496_;
goto v_resetjp_490_;
}
v_resetjp_490_:
{
lean_object* v___x_494_; 
if (v_isShared_492_ == 0)
{
v___x_494_ = v___x_491_;
goto v_reusejp_493_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v_a_489_);
v___x_494_ = v_reuseFailAlloc_495_;
goto v_reusejp_493_;
}
v_reusejp_493_:
{
return v___x_494_;
}
}
}
else
{
lean_object* v_a_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_505_; 
v_a_497_ = lean_ctor_get(v___x_488_, 0);
v_isSharedCheck_505_ = !lean_is_exclusive(v___x_488_);
if (v_isSharedCheck_505_ == 0)
{
v___x_499_ = v___x_488_;
v_isShared_500_ = v_isSharedCheck_505_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_a_497_);
lean_dec(v___x_488_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_505_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
lean_object* v___x_501_; lean_object* v___x_503_; 
v___x_501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_501_, 0, v_a_497_);
if (v_isShared_500_ == 0)
{
lean_ctor_set(v___x_499_, 0, v___x_501_);
v___x_503_ = v___x_499_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v___x_501_);
v___x_503_ = v_reuseFailAlloc_504_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
return v___x_503_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCommand_fromJson_spec__0(lean_object* v_j_506_, lean_object* v_k_507_){
_start:
{
lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_508_ = l_Lean_Json_getObjValD(v_j_506_, v_k_507_);
v___x_509_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCommand_fromJson_spec__0_spec__0(v___x_508_);
return v___x_509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCommand_fromJson_spec__0___boxed(lean_object* v_j_510_, lean_object* v_k_511_){
_start:
{
lean_object* v_res_512_; 
v_res_512_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCommand_fromJson_spec__0(v_j_510_, v_k_511_);
lean_dec_ref(v_k_511_);
return v_res_512_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonCommand_fromJson___closed__2(void){
_start:
{
uint8_t v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_518_ = 1;
v___x_519_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCommand_fromJson___closed__1));
v___x_520_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_519_, v___x_518_);
return v___x_520_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonCommand_fromJson___closed__3(void){
_start:
{
lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_521_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__5));
v___x_522_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCommand_fromJson___closed__2, &l_Lean_Lsp_instFromJsonCommand_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonCommand_fromJson___closed__2);
v___x_523_ = lean_string_append(v___x_522_, v___x_521_);
return v___x_523_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonCommand_fromJson___closed__5(void){
_start:
{
uint8_t v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; 
v___x_526_ = 1;
v___x_527_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCommand_fromJson___closed__4));
v___x_528_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_527_, v___x_526_);
return v___x_528_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonCommand_fromJson___closed__6(void){
_start:
{
lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_529_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCommand_fromJson___closed__5, &l_Lean_Lsp_instFromJsonCommand_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonCommand_fromJson___closed__5);
v___x_530_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCommand_fromJson___closed__3, &l_Lean_Lsp_instFromJsonCommand_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonCommand_fromJson___closed__3);
v___x_531_ = lean_string_append(v___x_530_, v___x_529_);
return v___x_531_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonCommand_fromJson___closed__7(void){
_start:
{
lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_532_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_533_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCommand_fromJson___closed__6, &l_Lean_Lsp_instFromJsonCommand_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonCommand_fromJson___closed__6);
v___x_534_ = lean_string_append(v___x_533_, v___x_532_);
return v___x_534_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonCommand_fromJson___closed__9(void){
_start:
{
uint8_t v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_537_ = 1;
v___x_538_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCommand_fromJson___closed__8));
v___x_539_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_538_, v___x_537_);
return v___x_539_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonCommand_fromJson___closed__10(void){
_start:
{
lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_540_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCommand_fromJson___closed__9, &l_Lean_Lsp_instFromJsonCommand_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonCommand_fromJson___closed__9);
v___x_541_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCommand_fromJson___closed__3, &l_Lean_Lsp_instFromJsonCommand_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonCommand_fromJson___closed__3);
v___x_542_ = lean_string_append(v___x_541_, v___x_540_);
return v___x_542_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonCommand_fromJson___closed__11(void){
_start:
{
lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; 
v___x_543_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_544_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCommand_fromJson___closed__10, &l_Lean_Lsp_instFromJsonCommand_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonCommand_fromJson___closed__10);
v___x_545_ = lean_string_append(v___x_544_, v___x_543_);
return v___x_545_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonCommand_fromJson___closed__14(void){
_start:
{
uint8_t v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; 
v___x_549_ = 1;
v___x_550_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCommand_fromJson___closed__13));
v___x_551_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_550_, v___x_549_);
return v___x_551_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonCommand_fromJson___closed__15(void){
_start:
{
lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; 
v___x_552_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCommand_fromJson___closed__14, &l_Lean_Lsp_instFromJsonCommand_fromJson___closed__14_once, _init_l_Lean_Lsp_instFromJsonCommand_fromJson___closed__14);
v___x_553_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCommand_fromJson___closed__3, &l_Lean_Lsp_instFromJsonCommand_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonCommand_fromJson___closed__3);
v___x_554_ = lean_string_append(v___x_553_, v___x_552_);
return v___x_554_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonCommand_fromJson___closed__16(void){
_start:
{
lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; 
v___x_555_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_556_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCommand_fromJson___closed__15, &l_Lean_Lsp_instFromJsonCommand_fromJson___closed__15_once, _init_l_Lean_Lsp_instFromJsonCommand_fromJson___closed__15);
v___x_557_ = lean_string_append(v___x_556_, v___x_555_);
return v___x_557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonCommand_fromJson(lean_object* v_json_558_){
_start:
{
lean_object* v___x_559_; lean_object* v___x_560_; 
v___x_559_ = ((lean_object*)(l_Lean_Lsp_instToJsonCommand_toJson___closed__0));
lean_inc(v_json_558_);
v___x_560_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocation_fromJson_spec__0(v_json_558_, v___x_559_);
if (lean_obj_tag(v___x_560_) == 0)
{
lean_object* v_a_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_570_; 
lean_dec(v_json_558_);
v_a_561_ = lean_ctor_get(v___x_560_, 0);
v_isSharedCheck_570_ = !lean_is_exclusive(v___x_560_);
if (v_isSharedCheck_570_ == 0)
{
v___x_563_ = v___x_560_;
v_isShared_564_ = v_isSharedCheck_570_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_a_561_);
lean_dec(v___x_560_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_570_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_568_; 
v___x_565_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCommand_fromJson___closed__7, &l_Lean_Lsp_instFromJsonCommand_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonCommand_fromJson___closed__7);
v___x_566_ = lean_string_append(v___x_565_, v_a_561_);
lean_dec(v_a_561_);
if (v_isShared_564_ == 0)
{
lean_ctor_set(v___x_563_, 0, v___x_566_);
v___x_568_ = v___x_563_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v___x_566_);
v___x_568_ = v_reuseFailAlloc_569_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
return v___x_568_;
}
}
}
else
{
if (lean_obj_tag(v___x_560_) == 0)
{
lean_object* v_a_571_; lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_578_; 
lean_dec(v_json_558_);
v_a_571_ = lean_ctor_get(v___x_560_, 0);
v_isSharedCheck_578_ = !lean_is_exclusive(v___x_560_);
if (v_isSharedCheck_578_ == 0)
{
v___x_573_ = v___x_560_;
v_isShared_574_ = v_isSharedCheck_578_;
goto v_resetjp_572_;
}
else
{
lean_inc(v_a_571_);
lean_dec(v___x_560_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_578_;
goto v_resetjp_572_;
}
v_resetjp_572_:
{
lean_object* v___x_576_; 
if (v_isShared_574_ == 0)
{
lean_ctor_set_tag(v___x_573_, 0);
v___x_576_ = v___x_573_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v_a_571_);
v___x_576_ = v_reuseFailAlloc_577_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
return v___x_576_;
}
}
}
else
{
lean_object* v_a_579_; lean_object* v___x_580_; lean_object* v___x_581_; 
v_a_579_ = lean_ctor_get(v___x_560_, 0);
lean_inc(v_a_579_);
lean_dec_ref_known(v___x_560_, 1);
v___x_580_ = ((lean_object*)(l_Lean_Lsp_instToJsonCommand_toJson___closed__1));
lean_inc(v_json_558_);
v___x_581_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocation_fromJson_spec__0(v_json_558_, v___x_580_);
if (lean_obj_tag(v___x_581_) == 0)
{
lean_object* v_a_582_; lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_591_; 
lean_dec(v_a_579_);
lean_dec(v_json_558_);
v_a_582_ = lean_ctor_get(v___x_581_, 0);
v_isSharedCheck_591_ = !lean_is_exclusive(v___x_581_);
if (v_isSharedCheck_591_ == 0)
{
v___x_584_ = v___x_581_;
v_isShared_585_ = v_isSharedCheck_591_;
goto v_resetjp_583_;
}
else
{
lean_inc(v_a_582_);
lean_dec(v___x_581_);
v___x_584_ = lean_box(0);
v_isShared_585_ = v_isSharedCheck_591_;
goto v_resetjp_583_;
}
v_resetjp_583_:
{
lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_589_; 
v___x_586_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCommand_fromJson___closed__11, &l_Lean_Lsp_instFromJsonCommand_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonCommand_fromJson___closed__11);
v___x_587_ = lean_string_append(v___x_586_, v_a_582_);
lean_dec(v_a_582_);
if (v_isShared_585_ == 0)
{
lean_ctor_set(v___x_584_, 0, v___x_587_);
v___x_589_ = v___x_584_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v___x_587_);
v___x_589_ = v_reuseFailAlloc_590_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
return v___x_589_;
}
}
}
else
{
if (lean_obj_tag(v___x_581_) == 0)
{
lean_object* v_a_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_599_; 
lean_dec(v_a_579_);
lean_dec(v_json_558_);
v_a_592_ = lean_ctor_get(v___x_581_, 0);
v_isSharedCheck_599_ = !lean_is_exclusive(v___x_581_);
if (v_isSharedCheck_599_ == 0)
{
v___x_594_ = v___x_581_;
v_isShared_595_ = v_isSharedCheck_599_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_a_592_);
lean_dec(v___x_581_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_599_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v___x_597_; 
if (v_isShared_595_ == 0)
{
lean_ctor_set_tag(v___x_594_, 0);
v___x_597_ = v___x_594_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v_a_592_);
v___x_597_ = v_reuseFailAlloc_598_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
return v___x_597_;
}
}
}
else
{
lean_object* v_a_600_; lean_object* v___x_601_; lean_object* v___x_602_; 
v_a_600_ = lean_ctor_get(v___x_581_, 0);
lean_inc(v_a_600_);
lean_dec_ref_known(v___x_581_, 1);
v___x_601_ = ((lean_object*)(l_Lean_Lsp_instToJsonCommand_toJson___closed__2));
v___x_602_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCommand_fromJson_spec__0(v_json_558_, v___x_601_);
if (lean_obj_tag(v___x_602_) == 0)
{
lean_object* v_a_603_; lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_612_; 
lean_dec(v_a_600_);
lean_dec(v_a_579_);
v_a_603_ = lean_ctor_get(v___x_602_, 0);
v_isSharedCheck_612_ = !lean_is_exclusive(v___x_602_);
if (v_isSharedCheck_612_ == 0)
{
v___x_605_ = v___x_602_;
v_isShared_606_ = v_isSharedCheck_612_;
goto v_resetjp_604_;
}
else
{
lean_inc(v_a_603_);
lean_dec(v___x_602_);
v___x_605_ = lean_box(0);
v_isShared_606_ = v_isSharedCheck_612_;
goto v_resetjp_604_;
}
v_resetjp_604_:
{
lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_610_; 
v___x_607_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCommand_fromJson___closed__16, &l_Lean_Lsp_instFromJsonCommand_fromJson___closed__16_once, _init_l_Lean_Lsp_instFromJsonCommand_fromJson___closed__16);
v___x_608_ = lean_string_append(v___x_607_, v_a_603_);
lean_dec(v_a_603_);
if (v_isShared_606_ == 0)
{
lean_ctor_set(v___x_605_, 0, v___x_608_);
v___x_610_ = v___x_605_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v___x_608_);
v___x_610_ = v_reuseFailAlloc_611_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
return v___x_610_;
}
}
}
else
{
if (lean_obj_tag(v___x_602_) == 0)
{
lean_object* v_a_613_; lean_object* v___x_615_; uint8_t v_isShared_616_; uint8_t v_isSharedCheck_620_; 
lean_dec(v_a_600_);
lean_dec(v_a_579_);
v_a_613_ = lean_ctor_get(v___x_602_, 0);
v_isSharedCheck_620_ = !lean_is_exclusive(v___x_602_);
if (v_isSharedCheck_620_ == 0)
{
v___x_615_ = v___x_602_;
v_isShared_616_ = v_isSharedCheck_620_;
goto v_resetjp_614_;
}
else
{
lean_inc(v_a_613_);
lean_dec(v___x_602_);
v___x_615_ = lean_box(0);
v_isShared_616_ = v_isSharedCheck_620_;
goto v_resetjp_614_;
}
v_resetjp_614_:
{
lean_object* v___x_618_; 
if (v_isShared_616_ == 0)
{
lean_ctor_set_tag(v___x_615_, 0);
v___x_618_ = v___x_615_;
goto v_reusejp_617_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v_a_613_);
v___x_618_ = v_reuseFailAlloc_619_;
goto v_reusejp_617_;
}
v_reusejp_617_:
{
return v___x_618_;
}
}
}
else
{
lean_object* v_a_621_; lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_629_; 
v_a_621_ = lean_ctor_get(v___x_602_, 0);
v_isSharedCheck_629_ = !lean_is_exclusive(v___x_602_);
if (v_isSharedCheck_629_ == 0)
{
v___x_623_ = v___x_602_;
v_isShared_624_ = v_isSharedCheck_629_;
goto v_resetjp_622_;
}
else
{
lean_inc(v_a_621_);
lean_dec(v___x_602_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_629_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
lean_object* v___x_625_; lean_object* v___x_627_; 
v___x_625_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_625_, 0, v_a_579_);
lean_ctor_set(v___x_625_, 1, v_a_600_);
lean_ctor_set(v___x_625_, 2, v_a_621_);
if (v_isShared_624_ == 0)
{
lean_ctor_set(v___x_623_, 0, v___x_625_);
v___x_627_ = v___x_623_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v___x_625_);
v___x_627_ = v_reuseFailAlloc_628_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
return v___x_627_;
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
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonSnippetString_toJson(lean_object* v_x_633_){
_start:
{
lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; 
v___x_634_ = ((lean_object*)(l_Lean_Lsp_instToJsonSnippetString_toJson___closed__0));
v___x_635_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_635_, 0, v_x_633_);
v___x_636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_636_, 0, v___x_634_);
lean_ctor_set(v___x_636_, 1, v___x_635_);
v___x_637_ = lean_box(0);
v___x_638_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_638_, 0, v___x_636_);
lean_ctor_set(v___x_638_, 1, v___x_637_);
v___x_639_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_639_, 0, v___x_638_);
lean_ctor_set(v___x_639_, 1, v___x_637_);
v___x_640_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__2));
v___x_641_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLocation_toJson_spec__0(v___x_639_, v___x_640_);
v___x_642_ = l_Lean_Json_mkObj(v___x_641_);
lean_dec(v___x_641_);
return v___x_642_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonSnippetString_fromJson___closed__2(void){
_start:
{
uint8_t v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_650_ = 1;
v___x_651_ = ((lean_object*)(l_Lean_Lsp_instFromJsonSnippetString_fromJson___closed__1));
v___x_652_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_651_, v___x_650_);
return v___x_652_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonSnippetString_fromJson___closed__3(void){
_start:
{
lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_653_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__5));
v___x_654_ = lean_obj_once(&l_Lean_Lsp_instFromJsonSnippetString_fromJson___closed__2, &l_Lean_Lsp_instFromJsonSnippetString_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonSnippetString_fromJson___closed__2);
v___x_655_ = lean_string_append(v___x_654_, v___x_653_);
return v___x_655_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonSnippetString_fromJson___closed__5(void){
_start:
{
uint8_t v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; 
v___x_658_ = 1;
v___x_659_ = ((lean_object*)(l_Lean_Lsp_instFromJsonSnippetString_fromJson___closed__4));
v___x_660_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_659_, v___x_658_);
return v___x_660_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonSnippetString_fromJson___closed__6(void){
_start:
{
lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; 
v___x_661_ = lean_obj_once(&l_Lean_Lsp_instFromJsonSnippetString_fromJson___closed__5, &l_Lean_Lsp_instFromJsonSnippetString_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonSnippetString_fromJson___closed__5);
v___x_662_ = lean_obj_once(&l_Lean_Lsp_instFromJsonSnippetString_fromJson___closed__3, &l_Lean_Lsp_instFromJsonSnippetString_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonSnippetString_fromJson___closed__3);
v___x_663_ = lean_string_append(v___x_662_, v___x_661_);
return v___x_663_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonSnippetString_fromJson___closed__7(void){
_start:
{
lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; 
v___x_664_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_665_ = lean_obj_once(&l_Lean_Lsp_instFromJsonSnippetString_fromJson___closed__6, &l_Lean_Lsp_instFromJsonSnippetString_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonSnippetString_fromJson___closed__6);
v___x_666_ = lean_string_append(v___x_665_, v___x_664_);
return v___x_666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonSnippetString_fromJson(lean_object* v_json_667_){
_start:
{
lean_object* v___x_668_; lean_object* v___x_669_; 
v___x_668_ = ((lean_object*)(l_Lean_Lsp_instToJsonSnippetString_toJson___closed__0));
v___x_669_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocation_fromJson_spec__0(v_json_667_, v___x_668_);
if (lean_obj_tag(v___x_669_) == 0)
{
lean_object* v_a_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_679_; 
v_a_670_ = lean_ctor_get(v___x_669_, 0);
v_isSharedCheck_679_ = !lean_is_exclusive(v___x_669_);
if (v_isSharedCheck_679_ == 0)
{
v___x_672_ = v___x_669_;
v_isShared_673_ = v_isSharedCheck_679_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_a_670_);
lean_dec(v___x_669_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_679_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_677_; 
v___x_674_ = lean_obj_once(&l_Lean_Lsp_instFromJsonSnippetString_fromJson___closed__7, &l_Lean_Lsp_instFromJsonSnippetString_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonSnippetString_fromJson___closed__7);
v___x_675_ = lean_string_append(v___x_674_, v_a_670_);
lean_dec(v_a_670_);
if (v_isShared_673_ == 0)
{
lean_ctor_set(v___x_672_, 0, v___x_675_);
v___x_677_ = v___x_672_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v___x_675_);
v___x_677_ = v_reuseFailAlloc_678_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
return v___x_677_;
}
}
}
else
{
if (lean_obj_tag(v___x_669_) == 0)
{
lean_object* v_a_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_687_; 
v_a_680_ = lean_ctor_get(v___x_669_, 0);
v_isSharedCheck_687_ = !lean_is_exclusive(v___x_669_);
if (v_isSharedCheck_687_ == 0)
{
v___x_682_ = v___x_669_;
v_isShared_683_ = v_isSharedCheck_687_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_a_680_);
lean_dec(v___x_669_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_687_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
lean_object* v___x_685_; 
if (v_isShared_683_ == 0)
{
lean_ctor_set_tag(v___x_682_, 0);
v___x_685_ = v___x_682_;
goto v_reusejp_684_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v_a_680_);
v___x_685_ = v_reuseFailAlloc_686_;
goto v_reusejp_684_;
}
v_reusejp_684_:
{
return v___x_685_;
}
}
}
else
{
lean_object* v_a_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_695_; 
v_a_688_ = lean_ctor_get(v___x_669_, 0);
v_isSharedCheck_695_ = !lean_is_exclusive(v___x_669_);
if (v_isSharedCheck_695_ == 0)
{
v___x_690_ = v___x_669_;
v_isShared_691_ = v_isSharedCheck_695_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_a_688_);
lean_dec(v___x_669_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_695_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
lean_object* v___x_693_; 
if (v_isShared_691_ == 0)
{
v___x_693_ = v___x_690_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v_a_688_);
v___x_693_ = v_reuseFailAlloc_694_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
return v___x_693_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextEdit_toJson_spec__0(lean_object* v_k_698_, lean_object* v_x_699_){
_start:
{
if (lean_obj_tag(v_x_699_) == 0)
{
lean_object* v___x_700_; 
lean_dec_ref(v_k_698_);
v___x_700_ = lean_box(0);
return v___x_700_;
}
else
{
lean_object* v_val_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; 
v_val_701_ = lean_ctor_get(v_x_699_, 0);
lean_inc(v_val_701_);
lean_dec_ref_known(v_x_699_, 1);
v___x_702_ = l_Lean_Lsp_instToJsonSnippetString_toJson(v_val_701_);
v___x_703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_703_, 0, v_k_698_);
lean_ctor_set(v___x_703_, 1, v___x_702_);
v___x_704_ = lean_box(0);
v___x_705_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_705_, 0, v___x_703_);
lean_ctor_set(v___x_705_, 1, v___x_704_);
return v___x_705_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextEdit_toJson_spec__1(lean_object* v_k_706_, lean_object* v_x_707_){
_start:
{
if (lean_obj_tag(v_x_707_) == 0)
{
lean_object* v___x_708_; 
lean_dec_ref(v_k_706_);
v___x_708_ = lean_box(0);
return v___x_708_;
}
else
{
lean_object* v_val_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_719_; 
v_val_709_ = lean_ctor_get(v_x_707_, 0);
v_isSharedCheck_719_ = !lean_is_exclusive(v_x_707_);
if (v_isSharedCheck_719_ == 0)
{
v___x_711_ = v_x_707_;
v_isShared_712_ = v_isSharedCheck_719_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_val_709_);
lean_dec(v_x_707_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_719_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v___x_714_; 
if (v_isShared_712_ == 0)
{
lean_ctor_set_tag(v___x_711_, 3);
v___x_714_ = v___x_711_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v_val_709_);
v___x_714_ = v_reuseFailAlloc_718_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; 
v___x_715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_715_, 0, v_k_706_);
lean_ctor_set(v___x_715_, 1, v___x_714_);
v___x_716_ = lean_box(0);
v___x_717_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_717_, 0, v___x_715_);
lean_ctor_set(v___x_717_, 1, v___x_716_);
return v___x_717_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonTextEdit_toJson(lean_object* v_x_723_){
_start:
{
lean_object* v_range_724_; lean_object* v_newText_725_; lean_object* v_leanExtSnippet_x3f_726_; lean_object* v_annotationId_x3f_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; 
v_range_724_ = lean_ctor_get(v_x_723_, 0);
lean_inc_ref(v_range_724_);
v_newText_725_ = lean_ctor_get(v_x_723_, 1);
lean_inc_ref(v_newText_725_);
v_leanExtSnippet_x3f_726_ = lean_ctor_get(v_x_723_, 2);
lean_inc(v_leanExtSnippet_x3f_726_);
v_annotationId_x3f_727_ = lean_ctor_get(v_x_723_, 3);
lean_inc(v_annotationId_x3f_727_);
lean_dec_ref(v_x_723_);
v___x_728_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__1));
v___x_729_ = l_Lean_Lsp_instToJsonRange_toJson(v_range_724_);
v___x_730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_730_, 0, v___x_728_);
lean_ctor_set(v___x_730_, 1, v___x_729_);
v___x_731_ = lean_box(0);
v___x_732_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_732_, 0, v___x_730_);
lean_ctor_set(v___x_732_, 1, v___x_731_);
v___x_733_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextEdit_toJson___closed__0));
v___x_734_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_734_, 0, v_newText_725_);
v___x_735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_735_, 0, v___x_733_);
lean_ctor_set(v___x_735_, 1, v___x_734_);
v___x_736_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_736_, 0, v___x_735_);
lean_ctor_set(v___x_736_, 1, v___x_731_);
v___x_737_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextEdit_toJson___closed__1));
v___x_738_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextEdit_toJson_spec__0(v___x_737_, v_leanExtSnippet_x3f_726_);
v___x_739_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextEdit_toJson___closed__2));
v___x_740_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextEdit_toJson_spec__1(v___x_739_, v_annotationId_x3f_727_);
v___x_741_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_741_, 0, v___x_740_);
lean_ctor_set(v___x_741_, 1, v___x_731_);
v___x_742_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_742_, 0, v___x_738_);
lean_ctor_set(v___x_742_, 1, v___x_741_);
v___x_743_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_743_, 0, v___x_736_);
lean_ctor_set(v___x_743_, 1, v___x_742_);
v___x_744_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_744_, 0, v___x_732_);
lean_ctor_set(v___x_744_, 1, v___x_743_);
v___x_745_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__2));
v___x_746_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLocation_toJson_spec__0(v___x_744_, v___x_745_);
v___x_747_ = l_Lean_Json_mkObj(v___x_746_);
lean_dec(v___x_746_);
return v___x_747_;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextEdit_fromJson_spec__0_spec__0(lean_object* v_x_752_){
_start:
{
if (lean_obj_tag(v_x_752_) == 0)
{
lean_object* v___x_753_; 
v___x_753_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextEdit_fromJson_spec__0_spec__0___closed__0));
return v___x_753_;
}
else
{
lean_object* v___x_754_; 
v___x_754_ = l_Lean_Lsp_instFromJsonSnippetString_fromJson(v_x_752_);
if (lean_obj_tag(v___x_754_) == 0)
{
lean_object* v_a_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_762_; 
v_a_755_ = lean_ctor_get(v___x_754_, 0);
v_isSharedCheck_762_ = !lean_is_exclusive(v___x_754_);
if (v_isSharedCheck_762_ == 0)
{
v___x_757_ = v___x_754_;
v_isShared_758_ = v_isSharedCheck_762_;
goto v_resetjp_756_;
}
else
{
lean_inc(v_a_755_);
lean_dec(v___x_754_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_762_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
lean_object* v___x_760_; 
if (v_isShared_758_ == 0)
{
v___x_760_ = v___x_757_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v_a_755_);
v___x_760_ = v_reuseFailAlloc_761_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
return v___x_760_;
}
}
}
else
{
lean_object* v_a_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_771_; 
v_a_763_ = lean_ctor_get(v___x_754_, 0);
v_isSharedCheck_771_ = !lean_is_exclusive(v___x_754_);
if (v_isSharedCheck_771_ == 0)
{
v___x_765_ = v___x_754_;
v_isShared_766_ = v_isSharedCheck_771_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_a_763_);
lean_dec(v___x_754_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_771_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
lean_object* v___x_767_; lean_object* v___x_769_; 
v___x_767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_767_, 0, v_a_763_);
if (v_isShared_766_ == 0)
{
lean_ctor_set(v___x_765_, 0, v___x_767_);
v___x_769_ = v___x_765_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v___x_767_);
v___x_769_ = v_reuseFailAlloc_770_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
return v___x_769_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextEdit_fromJson_spec__0(lean_object* v_j_772_, lean_object* v_k_773_){
_start:
{
lean_object* v___x_774_; lean_object* v___x_775_; 
v___x_774_ = l_Lean_Json_getObjValD(v_j_772_, v_k_773_);
v___x_775_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextEdit_fromJson_spec__0_spec__0(v___x_774_);
return v___x_775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextEdit_fromJson_spec__0___boxed(lean_object* v_j_776_, lean_object* v_k_777_){
_start:
{
lean_object* v_res_778_; 
v_res_778_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextEdit_fromJson_spec__0(v_j_776_, v_k_777_);
lean_dec_ref(v_k_777_);
return v_res_778_;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextEdit_fromJson_spec__1_spec__2(lean_object* v_x_779_){
_start:
{
if (lean_obj_tag(v_x_779_) == 0)
{
lean_object* v___x_780_; 
v___x_780_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextEdit_fromJson_spec__0_spec__0___closed__0));
return v___x_780_;
}
else
{
lean_object* v___x_781_; 
v___x_781_ = l_Lean_Json_getStr_x3f(v_x_779_);
if (lean_obj_tag(v___x_781_) == 0)
{
lean_object* v_a_782_; lean_object* v___x_784_; uint8_t v_isShared_785_; uint8_t v_isSharedCheck_789_; 
v_a_782_ = lean_ctor_get(v___x_781_, 0);
v_isSharedCheck_789_ = !lean_is_exclusive(v___x_781_);
if (v_isSharedCheck_789_ == 0)
{
v___x_784_ = v___x_781_;
v_isShared_785_ = v_isSharedCheck_789_;
goto v_resetjp_783_;
}
else
{
lean_inc(v_a_782_);
lean_dec(v___x_781_);
v___x_784_ = lean_box(0);
v_isShared_785_ = v_isSharedCheck_789_;
goto v_resetjp_783_;
}
v_resetjp_783_:
{
lean_object* v___x_787_; 
if (v_isShared_785_ == 0)
{
v___x_787_ = v___x_784_;
goto v_reusejp_786_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v_a_782_);
v___x_787_ = v_reuseFailAlloc_788_;
goto v_reusejp_786_;
}
v_reusejp_786_:
{
return v___x_787_;
}
}
}
else
{
lean_object* v_a_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_798_; 
v_a_790_ = lean_ctor_get(v___x_781_, 0);
v_isSharedCheck_798_ = !lean_is_exclusive(v___x_781_);
if (v_isSharedCheck_798_ == 0)
{
v___x_792_ = v___x_781_;
v_isShared_793_ = v_isSharedCheck_798_;
goto v_resetjp_791_;
}
else
{
lean_inc(v_a_790_);
lean_dec(v___x_781_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_798_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
lean_object* v___x_794_; lean_object* v___x_796_; 
v___x_794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_794_, 0, v_a_790_);
if (v_isShared_793_ == 0)
{
lean_ctor_set(v___x_792_, 0, v___x_794_);
v___x_796_ = v___x_792_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v___x_794_);
v___x_796_ = v_reuseFailAlloc_797_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
return v___x_796_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextEdit_fromJson_spec__1(lean_object* v_j_799_, lean_object* v_k_800_){
_start:
{
lean_object* v___x_801_; lean_object* v___x_802_; 
v___x_801_ = l_Lean_Json_getObjValD(v_j_799_, v_k_800_);
v___x_802_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextEdit_fromJson_spec__1_spec__2(v___x_801_);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextEdit_fromJson_spec__1___boxed(lean_object* v_j_803_, lean_object* v_k_804_){
_start:
{
lean_object* v_res_805_; 
v_res_805_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextEdit_fromJson_spec__1(v_j_803_, v_k_804_);
lean_dec_ref(v_k_804_);
return v_res_805_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__2(void){
_start:
{
uint8_t v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; 
v___x_811_ = 1;
v___x_812_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__1));
v___x_813_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_812_, v___x_811_);
return v___x_813_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__3(void){
_start:
{
lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; 
v___x_814_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__5));
v___x_815_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__2, &l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__2);
v___x_816_ = lean_string_append(v___x_815_, v___x_814_);
return v___x_816_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__4(void){
_start:
{
lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; 
v___x_817_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLocation_fromJson___closed__13, &l_Lean_Lsp_instFromJsonLocation_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonLocation_fromJson___closed__13);
v___x_818_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__3, &l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__3);
v___x_819_ = lean_string_append(v___x_818_, v___x_817_);
return v___x_819_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__5(void){
_start:
{
lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; 
v___x_820_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_821_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__4, &l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__4);
v___x_822_ = lean_string_append(v___x_821_, v___x_820_);
return v___x_822_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__7(void){
_start:
{
uint8_t v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; 
v___x_825_ = 1;
v___x_826_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__6));
v___x_827_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_826_, v___x_825_);
return v___x_827_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__8(void){
_start:
{
lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; 
v___x_828_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__7, &l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__7);
v___x_829_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__3, &l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__3);
v___x_830_ = lean_string_append(v___x_829_, v___x_828_);
return v___x_830_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__9(void){
_start:
{
lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; 
v___x_831_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_832_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__8, &l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__8);
v___x_833_ = lean_string_append(v___x_832_, v___x_831_);
return v___x_833_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__12(void){
_start:
{
uint8_t v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; 
v___x_837_ = 1;
v___x_838_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__11));
v___x_839_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_838_, v___x_837_);
return v___x_839_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__13(void){
_start:
{
lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; 
v___x_840_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__12, &l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__12);
v___x_841_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__3, &l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__3);
v___x_842_ = lean_string_append(v___x_841_, v___x_840_);
return v___x_842_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__14(void){
_start:
{
lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; 
v___x_843_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_844_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__13, &l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__13);
v___x_845_ = lean_string_append(v___x_844_, v___x_843_);
return v___x_845_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__17(void){
_start:
{
uint8_t v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; 
v___x_849_ = 1;
v___x_850_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__16));
v___x_851_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_850_, v___x_849_);
return v___x_851_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__18(void){
_start:
{
lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; 
v___x_852_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__17, &l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__17_once, _init_l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__17);
v___x_853_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__3, &l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__3);
v___x_854_ = lean_string_append(v___x_853_, v___x_852_);
return v___x_854_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__19(void){
_start:
{
lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; 
v___x_855_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_856_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__18, &l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__18_once, _init_l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__18);
v___x_857_ = lean_string_append(v___x_856_, v___x_855_);
return v___x_857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonTextEdit_fromJson(lean_object* v_json_858_){
_start:
{
lean_object* v___x_859_; lean_object* v___x_860_; 
v___x_859_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__1));
lean_inc(v_json_858_);
v___x_860_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocation_fromJson_spec__1(v_json_858_, v___x_859_);
if (lean_obj_tag(v___x_860_) == 0)
{
lean_object* v_a_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_870_; 
lean_dec(v_json_858_);
v_a_861_ = lean_ctor_get(v___x_860_, 0);
v_isSharedCheck_870_ = !lean_is_exclusive(v___x_860_);
if (v_isSharedCheck_870_ == 0)
{
v___x_863_ = v___x_860_;
v_isShared_864_ = v_isSharedCheck_870_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_a_861_);
lean_dec(v___x_860_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_870_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_868_; 
v___x_865_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__5, &l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__5);
v___x_866_ = lean_string_append(v___x_865_, v_a_861_);
lean_dec(v_a_861_);
if (v_isShared_864_ == 0)
{
lean_ctor_set(v___x_863_, 0, v___x_866_);
v___x_868_ = v___x_863_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v___x_866_);
v___x_868_ = v_reuseFailAlloc_869_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
return v___x_868_;
}
}
}
else
{
if (lean_obj_tag(v___x_860_) == 0)
{
lean_object* v_a_871_; lean_object* v___x_873_; uint8_t v_isShared_874_; uint8_t v_isSharedCheck_878_; 
lean_dec(v_json_858_);
v_a_871_ = lean_ctor_get(v___x_860_, 0);
v_isSharedCheck_878_ = !lean_is_exclusive(v___x_860_);
if (v_isSharedCheck_878_ == 0)
{
v___x_873_ = v___x_860_;
v_isShared_874_ = v_isSharedCheck_878_;
goto v_resetjp_872_;
}
else
{
lean_inc(v_a_871_);
lean_dec(v___x_860_);
v___x_873_ = lean_box(0);
v_isShared_874_ = v_isSharedCheck_878_;
goto v_resetjp_872_;
}
v_resetjp_872_:
{
lean_object* v___x_876_; 
if (v_isShared_874_ == 0)
{
lean_ctor_set_tag(v___x_873_, 0);
v___x_876_ = v___x_873_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v_a_871_);
v___x_876_ = v_reuseFailAlloc_877_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
return v___x_876_;
}
}
}
else
{
lean_object* v_a_879_; lean_object* v___x_880_; lean_object* v___x_881_; 
v_a_879_ = lean_ctor_get(v___x_860_, 0);
lean_inc(v_a_879_);
lean_dec_ref_known(v___x_860_, 1);
v___x_880_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextEdit_toJson___closed__0));
lean_inc(v_json_858_);
v___x_881_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocation_fromJson_spec__0(v_json_858_, v___x_880_);
if (lean_obj_tag(v___x_881_) == 0)
{
lean_object* v_a_882_; lean_object* v___x_884_; uint8_t v_isShared_885_; uint8_t v_isSharedCheck_891_; 
lean_dec(v_a_879_);
lean_dec(v_json_858_);
v_a_882_ = lean_ctor_get(v___x_881_, 0);
v_isSharedCheck_891_ = !lean_is_exclusive(v___x_881_);
if (v_isSharedCheck_891_ == 0)
{
v___x_884_ = v___x_881_;
v_isShared_885_ = v_isSharedCheck_891_;
goto v_resetjp_883_;
}
else
{
lean_inc(v_a_882_);
lean_dec(v___x_881_);
v___x_884_ = lean_box(0);
v_isShared_885_ = v_isSharedCheck_891_;
goto v_resetjp_883_;
}
v_resetjp_883_:
{
lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_889_; 
v___x_886_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__9, &l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__9);
v___x_887_ = lean_string_append(v___x_886_, v_a_882_);
lean_dec(v_a_882_);
if (v_isShared_885_ == 0)
{
lean_ctor_set(v___x_884_, 0, v___x_887_);
v___x_889_ = v___x_884_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v___x_887_);
v___x_889_ = v_reuseFailAlloc_890_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
return v___x_889_;
}
}
}
else
{
if (lean_obj_tag(v___x_881_) == 0)
{
lean_object* v_a_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_899_; 
lean_dec(v_a_879_);
lean_dec(v_json_858_);
v_a_892_ = lean_ctor_get(v___x_881_, 0);
v_isSharedCheck_899_ = !lean_is_exclusive(v___x_881_);
if (v_isSharedCheck_899_ == 0)
{
v___x_894_ = v___x_881_;
v_isShared_895_ = v_isSharedCheck_899_;
goto v_resetjp_893_;
}
else
{
lean_inc(v_a_892_);
lean_dec(v___x_881_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_899_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
lean_object* v___x_897_; 
if (v_isShared_895_ == 0)
{
lean_ctor_set_tag(v___x_894_, 0);
v___x_897_ = v___x_894_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v_a_892_);
v___x_897_ = v_reuseFailAlloc_898_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
return v___x_897_;
}
}
}
else
{
lean_object* v_a_900_; lean_object* v___x_901_; lean_object* v___x_902_; 
v_a_900_ = lean_ctor_get(v___x_881_, 0);
lean_inc(v_a_900_);
lean_dec_ref_known(v___x_881_, 1);
v___x_901_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextEdit_toJson___closed__1));
lean_inc(v_json_858_);
v___x_902_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextEdit_fromJson_spec__0(v_json_858_, v___x_901_);
if (lean_obj_tag(v___x_902_) == 0)
{
lean_object* v_a_903_; lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_912_; 
lean_dec(v_a_900_);
lean_dec(v_a_879_);
lean_dec(v_json_858_);
v_a_903_ = lean_ctor_get(v___x_902_, 0);
v_isSharedCheck_912_ = !lean_is_exclusive(v___x_902_);
if (v_isSharedCheck_912_ == 0)
{
v___x_905_ = v___x_902_;
v_isShared_906_ = v_isSharedCheck_912_;
goto v_resetjp_904_;
}
else
{
lean_inc(v_a_903_);
lean_dec(v___x_902_);
v___x_905_ = lean_box(0);
v_isShared_906_ = v_isSharedCheck_912_;
goto v_resetjp_904_;
}
v_resetjp_904_:
{
lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_910_; 
v___x_907_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__14, &l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__14_once, _init_l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__14);
v___x_908_ = lean_string_append(v___x_907_, v_a_903_);
lean_dec(v_a_903_);
if (v_isShared_906_ == 0)
{
lean_ctor_set(v___x_905_, 0, v___x_908_);
v___x_910_ = v___x_905_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v___x_908_);
v___x_910_ = v_reuseFailAlloc_911_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
return v___x_910_;
}
}
}
else
{
if (lean_obj_tag(v___x_902_) == 0)
{
lean_object* v_a_913_; lean_object* v___x_915_; uint8_t v_isShared_916_; uint8_t v_isSharedCheck_920_; 
lean_dec(v_a_900_);
lean_dec(v_a_879_);
lean_dec(v_json_858_);
v_a_913_ = lean_ctor_get(v___x_902_, 0);
v_isSharedCheck_920_ = !lean_is_exclusive(v___x_902_);
if (v_isSharedCheck_920_ == 0)
{
v___x_915_ = v___x_902_;
v_isShared_916_ = v_isSharedCheck_920_;
goto v_resetjp_914_;
}
else
{
lean_inc(v_a_913_);
lean_dec(v___x_902_);
v___x_915_ = lean_box(0);
v_isShared_916_ = v_isSharedCheck_920_;
goto v_resetjp_914_;
}
v_resetjp_914_:
{
lean_object* v___x_918_; 
if (v_isShared_916_ == 0)
{
lean_ctor_set_tag(v___x_915_, 0);
v___x_918_ = v___x_915_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v_a_913_);
v___x_918_ = v_reuseFailAlloc_919_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
return v___x_918_;
}
}
}
else
{
lean_object* v_a_921_; lean_object* v___x_922_; lean_object* v___x_923_; 
v_a_921_ = lean_ctor_get(v___x_902_, 0);
lean_inc(v_a_921_);
lean_dec_ref_known(v___x_902_, 1);
v___x_922_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextEdit_toJson___closed__2));
v___x_923_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextEdit_fromJson_spec__1(v_json_858_, v___x_922_);
if (lean_obj_tag(v___x_923_) == 0)
{
lean_object* v_a_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_933_; 
lean_dec(v_a_921_);
lean_dec(v_a_900_);
lean_dec(v_a_879_);
v_a_924_ = lean_ctor_get(v___x_923_, 0);
v_isSharedCheck_933_ = !lean_is_exclusive(v___x_923_);
if (v_isSharedCheck_933_ == 0)
{
v___x_926_ = v___x_923_;
v_isShared_927_ = v_isSharedCheck_933_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_a_924_);
lean_dec(v___x_923_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_933_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_931_; 
v___x_928_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__19, &l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__19_once, _init_l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__19);
v___x_929_ = lean_string_append(v___x_928_, v_a_924_);
lean_dec(v_a_924_);
if (v_isShared_927_ == 0)
{
lean_ctor_set(v___x_926_, 0, v___x_929_);
v___x_931_ = v___x_926_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v___x_929_);
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
if (lean_obj_tag(v___x_923_) == 0)
{
lean_object* v_a_934_; lean_object* v___x_936_; uint8_t v_isShared_937_; uint8_t v_isSharedCheck_941_; 
lean_dec(v_a_921_);
lean_dec(v_a_900_);
lean_dec(v_a_879_);
v_a_934_ = lean_ctor_get(v___x_923_, 0);
v_isSharedCheck_941_ = !lean_is_exclusive(v___x_923_);
if (v_isSharedCheck_941_ == 0)
{
v___x_936_ = v___x_923_;
v_isShared_937_ = v_isSharedCheck_941_;
goto v_resetjp_935_;
}
else
{
lean_inc(v_a_934_);
lean_dec(v___x_923_);
v___x_936_ = lean_box(0);
v_isShared_937_ = v_isSharedCheck_941_;
goto v_resetjp_935_;
}
v_resetjp_935_:
{
lean_object* v___x_939_; 
if (v_isShared_937_ == 0)
{
lean_ctor_set_tag(v___x_936_, 0);
v___x_939_ = v___x_936_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v_a_934_);
v___x_939_ = v_reuseFailAlloc_940_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
return v___x_939_;
}
}
}
else
{
lean_object* v_a_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_950_; 
v_a_942_ = lean_ctor_get(v___x_923_, 0);
v_isSharedCheck_950_ = !lean_is_exclusive(v___x_923_);
if (v_isSharedCheck_950_ == 0)
{
v___x_944_ = v___x_923_;
v_isShared_945_ = v_isSharedCheck_950_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_a_942_);
lean_dec(v___x_923_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_950_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v___x_946_; lean_object* v___x_948_; 
v___x_946_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_946_, 0, v_a_879_);
lean_ctor_set(v___x_946_, 1, v_a_900_);
lean_ctor_set(v___x_946_, 2, v_a_921_);
lean_ctor_set(v___x_946_, 3, v_a_942_);
if (v_isShared_945_ == 0)
{
lean_ctor_set(v___x_944_, 0, v___x_946_);
v___x_948_ = v___x_944_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v___x_946_);
v___x_948_ = v_reuseFailAlloc_949_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
return v___x_948_;
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
LEAN_EXPORT lean_object* l_Lean_Lsp_instAppendTextEditBatch___aux__1(lean_object* v_as_962_, lean_object* v_bs_963_){
_start:
{
lean_object* v___x_964_; 
v___x_964_ = l_Array_append___redArg(v_as_962_, v_bs_963_);
return v___x_964_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instAppendTextEditBatch___aux__1___boxed(lean_object* v_as_965_, lean_object* v_bs_966_){
_start:
{
lean_object* v_res_967_; 
v_res_967_ = l_Lean_Lsp_instAppendTextEditBatch___aux__1(v_as_965_, v_bs_966_);
lean_dec_ref(v_bs_966_);
return v_res_967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instCoeTextEditTextEditBatch___lam__0(lean_object* v_te_970_){
_start:
{
lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; 
v___x_971_ = lean_unsigned_to_nat(1u);
v___x_972_ = lean_mk_empty_array_with_capacity(v___x_971_);
v___x_973_ = lean_array_push(v___x_972_, v_te_970_);
return v___x_973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonTextDocumentIdentifier_toJson(lean_object* v_x_976_){
_start:
{
lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; 
v___x_977_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__0));
v___x_978_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_978_, 0, v_x_976_);
v___x_979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_979_, 0, v___x_977_);
lean_ctor_set(v___x_979_, 1, v___x_978_);
v___x_980_ = lean_box(0);
v___x_981_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_981_, 0, v___x_979_);
lean_ctor_set(v___x_981_, 1, v___x_980_);
v___x_982_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_982_, 0, v___x_981_);
lean_ctor_set(v___x_982_, 1, v___x_980_);
v___x_983_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__2));
v___x_984_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLocation_toJson_spec__0(v___x_982_, v___x_983_);
v___x_985_ = l_Lean_Json_mkObj(v___x_984_);
lean_dec(v___x_984_);
return v___x_985_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentIdentifier_fromJson___closed__2(void){
_start:
{
uint8_t v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; 
v___x_993_ = 1;
v___x_994_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentIdentifier_fromJson___closed__1));
v___x_995_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_994_, v___x_993_);
return v___x_995_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentIdentifier_fromJson___closed__3(void){
_start:
{
lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; 
v___x_996_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__5));
v___x_997_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentIdentifier_fromJson___closed__2, &l_Lean_Lsp_instFromJsonTextDocumentIdentifier_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonTextDocumentIdentifier_fromJson___closed__2);
v___x_998_ = lean_string_append(v___x_997_, v___x_996_);
return v___x_998_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentIdentifier_fromJson___closed__4(void){
_start:
{
lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; 
v___x_999_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLocation_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLocation_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLocation_fromJson___closed__8);
v___x_1000_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentIdentifier_fromJson___closed__3, &l_Lean_Lsp_instFromJsonTextDocumentIdentifier_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonTextDocumentIdentifier_fromJson___closed__3);
v___x_1001_ = lean_string_append(v___x_1000_, v___x_999_);
return v___x_1001_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentIdentifier_fromJson___closed__5(void){
_start:
{
lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; 
v___x_1002_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_1003_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentIdentifier_fromJson___closed__4, &l_Lean_Lsp_instFromJsonTextDocumentIdentifier_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonTextDocumentIdentifier_fromJson___closed__4);
v___x_1004_ = lean_string_append(v___x_1003_, v___x_1002_);
return v___x_1004_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonTextDocumentIdentifier_fromJson(lean_object* v_json_1005_){
_start:
{
lean_object* v___x_1006_; lean_object* v___x_1007_; 
v___x_1006_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__0));
v___x_1007_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocation_fromJson_spec__0(v_json_1005_, v___x_1006_);
if (lean_obj_tag(v___x_1007_) == 0)
{
lean_object* v_a_1008_; lean_object* v___x_1010_; uint8_t v_isShared_1011_; uint8_t v_isSharedCheck_1017_; 
v_a_1008_ = lean_ctor_get(v___x_1007_, 0);
v_isSharedCheck_1017_ = !lean_is_exclusive(v___x_1007_);
if (v_isSharedCheck_1017_ == 0)
{
v___x_1010_ = v___x_1007_;
v_isShared_1011_ = v_isSharedCheck_1017_;
goto v_resetjp_1009_;
}
else
{
lean_inc(v_a_1008_);
lean_dec(v___x_1007_);
v___x_1010_ = lean_box(0);
v_isShared_1011_ = v_isSharedCheck_1017_;
goto v_resetjp_1009_;
}
v_resetjp_1009_:
{
lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1015_; 
v___x_1012_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentIdentifier_fromJson___closed__5, &l_Lean_Lsp_instFromJsonTextDocumentIdentifier_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonTextDocumentIdentifier_fromJson___closed__5);
v___x_1013_ = lean_string_append(v___x_1012_, v_a_1008_);
lean_dec(v_a_1008_);
if (v_isShared_1011_ == 0)
{
lean_ctor_set(v___x_1010_, 0, v___x_1013_);
v___x_1015_ = v___x_1010_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v___x_1013_);
v___x_1015_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
return v___x_1015_;
}
}
}
else
{
if (lean_obj_tag(v___x_1007_) == 0)
{
lean_object* v_a_1018_; lean_object* v___x_1020_; uint8_t v_isShared_1021_; uint8_t v_isSharedCheck_1025_; 
v_a_1018_ = lean_ctor_get(v___x_1007_, 0);
v_isSharedCheck_1025_ = !lean_is_exclusive(v___x_1007_);
if (v_isSharedCheck_1025_ == 0)
{
v___x_1020_ = v___x_1007_;
v_isShared_1021_ = v_isSharedCheck_1025_;
goto v_resetjp_1019_;
}
else
{
lean_inc(v_a_1018_);
lean_dec(v___x_1007_);
v___x_1020_ = lean_box(0);
v_isShared_1021_ = v_isSharedCheck_1025_;
goto v_resetjp_1019_;
}
v_resetjp_1019_:
{
lean_object* v___x_1023_; 
if (v_isShared_1021_ == 0)
{
lean_ctor_set_tag(v___x_1020_, 0);
v___x_1023_ = v___x_1020_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v_a_1018_);
v___x_1023_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
return v___x_1023_;
}
}
}
else
{
lean_object* v_a_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1033_; 
v_a_1026_ = lean_ctor_get(v___x_1007_, 0);
v_isSharedCheck_1033_ = !lean_is_exclusive(v___x_1007_);
if (v_isSharedCheck_1033_ == 0)
{
v___x_1028_ = v___x_1007_;
v_isShared_1029_ = v_isSharedCheck_1033_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_a_1026_);
lean_dec(v___x_1007_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1033_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
lean_object* v___x_1031_; 
if (v_isShared_1029_ == 0)
{
v___x_1031_ = v___x_1028_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v_a_1026_);
v___x_1031_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
return v___x_1031_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonVersionedTextDocumentIdentifier_toJson_spec__0(lean_object* v_k_1036_, lean_object* v_x_1037_){
_start:
{
if (lean_obj_tag(v_x_1037_) == 0)
{
lean_object* v___x_1038_; 
lean_dec_ref(v_k_1036_);
v___x_1038_ = lean_box(0);
return v___x_1038_;
}
else
{
lean_object* v_val_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1050_; 
v_val_1039_ = lean_ctor_get(v_x_1037_, 0);
v_isSharedCheck_1050_ = !lean_is_exclusive(v_x_1037_);
if (v_isSharedCheck_1050_ == 0)
{
v___x_1041_ = v_x_1037_;
v_isShared_1042_ = v_isSharedCheck_1050_;
goto v_resetjp_1040_;
}
else
{
lean_inc(v_val_1039_);
lean_dec(v_x_1037_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1050_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
lean_object* v___x_1043_; lean_object* v___x_1045_; 
v___x_1043_ = l_Lean_JsonNumber_fromNat(v_val_1039_);
if (v_isShared_1042_ == 0)
{
lean_ctor_set_tag(v___x_1041_, 2);
lean_ctor_set(v___x_1041_, 0, v___x_1043_);
v___x_1045_ = v___x_1041_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v___x_1043_);
v___x_1045_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; 
v___x_1046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1046_, 0, v_k_1036_);
lean_ctor_set(v___x_1046_, 1, v___x_1045_);
v___x_1047_ = lean_box(0);
v___x_1048_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1048_, 0, v___x_1046_);
lean_ctor_set(v___x_1048_, 1, v___x_1047_);
return v___x_1048_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonVersionedTextDocumentIdentifier_toJson(lean_object* v_x_1052_){
_start:
{
lean_object* v_uri_1053_; lean_object* v_version_x3f_1054_; lean_object* v___x_1056_; uint8_t v_isShared_1057_; uint8_t v_isSharedCheck_1072_; 
v_uri_1053_ = lean_ctor_get(v_x_1052_, 0);
v_version_x3f_1054_ = lean_ctor_get(v_x_1052_, 1);
v_isSharedCheck_1072_ = !lean_is_exclusive(v_x_1052_);
if (v_isSharedCheck_1072_ == 0)
{
v___x_1056_ = v_x_1052_;
v_isShared_1057_ = v_isSharedCheck_1072_;
goto v_resetjp_1055_;
}
else
{
lean_inc(v_version_x3f_1054_);
lean_inc(v_uri_1053_);
lean_dec(v_x_1052_);
v___x_1056_ = lean_box(0);
v_isShared_1057_ = v_isSharedCheck_1072_;
goto v_resetjp_1055_;
}
v_resetjp_1055_:
{
lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1061_; 
v___x_1058_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__0));
v___x_1059_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1059_, 0, v_uri_1053_);
if (v_isShared_1057_ == 0)
{
lean_ctor_set(v___x_1056_, 1, v___x_1059_);
lean_ctor_set(v___x_1056_, 0, v___x_1058_);
v___x_1061_ = v___x_1056_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v___x_1058_);
lean_ctor_set(v_reuseFailAlloc_1071_, 1, v___x_1059_);
v___x_1061_ = v_reuseFailAlloc_1071_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___x_1062_ = lean_box(0);
v___x_1063_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1063_, 0, v___x_1061_);
lean_ctor_set(v___x_1063_, 1, v___x_1062_);
v___x_1064_ = ((lean_object*)(l_Lean_Lsp_instToJsonVersionedTextDocumentIdentifier_toJson___closed__0));
v___x_1065_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonVersionedTextDocumentIdentifier_toJson_spec__0(v___x_1064_, v_version_x3f_1054_);
v___x_1066_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1066_, 0, v___x_1065_);
lean_ctor_set(v___x_1066_, 1, v___x_1062_);
v___x_1067_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1067_, 0, v___x_1063_);
lean_ctor_set(v___x_1067_, 1, v___x_1066_);
v___x_1068_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__2));
v___x_1069_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLocation_toJson_spec__0(v___x_1067_, v___x_1068_);
v___x_1070_ = l_Lean_Json_mkObj(v___x_1069_);
lean_dec(v___x_1069_);
return v___x_1070_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson_spec__0_spec__0(lean_object* v_x_1077_){
_start:
{
if (lean_obj_tag(v_x_1077_) == 0)
{
lean_object* v___x_1078_; 
v___x_1078_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson_spec__0_spec__0___closed__0));
return v___x_1078_;
}
else
{
lean_object* v___x_1079_; 
v___x_1079_ = l_Lean_Json_getNat_x3f(v_x_1077_);
if (lean_obj_tag(v___x_1079_) == 0)
{
lean_object* v_a_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1087_; 
v_a_1080_ = lean_ctor_get(v___x_1079_, 0);
v_isSharedCheck_1087_ = !lean_is_exclusive(v___x_1079_);
if (v_isSharedCheck_1087_ == 0)
{
v___x_1082_ = v___x_1079_;
v_isShared_1083_ = v_isSharedCheck_1087_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_a_1080_);
lean_dec(v___x_1079_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1087_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
lean_object* v___x_1085_; 
if (v_isShared_1083_ == 0)
{
v___x_1085_ = v___x_1082_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v_a_1080_);
v___x_1085_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
return v___x_1085_;
}
}
}
else
{
lean_object* v_a_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1096_; 
v_a_1088_ = lean_ctor_get(v___x_1079_, 0);
v_isSharedCheck_1096_ = !lean_is_exclusive(v___x_1079_);
if (v_isSharedCheck_1096_ == 0)
{
v___x_1090_ = v___x_1079_;
v_isShared_1091_ = v_isSharedCheck_1096_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_a_1088_);
lean_dec(v___x_1079_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1096_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v___x_1092_; lean_object* v___x_1094_; 
v___x_1092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1092_, 0, v_a_1088_);
if (v_isShared_1091_ == 0)
{
lean_ctor_set(v___x_1090_, 0, v___x_1092_);
v___x_1094_ = v___x_1090_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v___x_1092_);
v___x_1094_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
return v___x_1094_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson_spec__0(lean_object* v_j_1097_, lean_object* v_k_1098_){
_start:
{
lean_object* v___x_1099_; lean_object* v___x_1100_; 
v___x_1099_ = l_Lean_Json_getObjValD(v_j_1097_, v_k_1098_);
v___x_1100_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson_spec__0_spec__0(v___x_1099_);
return v___x_1100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson_spec__0___boxed(lean_object* v_j_1101_, lean_object* v_k_1102_){
_start:
{
lean_object* v_res_1103_; 
v_res_1103_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson_spec__0(v_j_1101_, v_k_1102_);
lean_dec_ref(v_k_1102_);
return v_res_1103_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__2(void){
_start:
{
uint8_t v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; 
v___x_1109_ = 1;
v___x_1110_ = ((lean_object*)(l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__1));
v___x_1111_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1110_, v___x_1109_);
return v___x_1111_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__3(void){
_start:
{
lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; 
v___x_1112_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__5));
v___x_1113_ = lean_obj_once(&l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__2, &l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__2);
v___x_1114_ = lean_string_append(v___x_1113_, v___x_1112_);
return v___x_1114_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__4(void){
_start:
{
lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; 
v___x_1115_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLocation_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLocation_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLocation_fromJson___closed__8);
v___x_1116_ = lean_obj_once(&l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__3, &l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__3);
v___x_1117_ = lean_string_append(v___x_1116_, v___x_1115_);
return v___x_1117_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__5(void){
_start:
{
lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; 
v___x_1118_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_1119_ = lean_obj_once(&l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__4, &l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__4);
v___x_1120_ = lean_string_append(v___x_1119_, v___x_1118_);
return v___x_1120_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__8(void){
_start:
{
uint8_t v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; 
v___x_1124_ = 1;
v___x_1125_ = ((lean_object*)(l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__7));
v___x_1126_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1125_, v___x_1124_);
return v___x_1126_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__9(void){
_start:
{
lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; 
v___x_1127_ = lean_obj_once(&l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__8, &l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__8);
v___x_1128_ = lean_obj_once(&l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__3, &l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__3);
v___x_1129_ = lean_string_append(v___x_1128_, v___x_1127_);
return v___x_1129_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__10(void){
_start:
{
lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; 
v___x_1130_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_1131_ = lean_obj_once(&l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__9, &l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__9);
v___x_1132_ = lean_string_append(v___x_1131_, v___x_1130_);
return v___x_1132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson(lean_object* v_json_1133_){
_start:
{
lean_object* v___x_1134_; lean_object* v___x_1135_; 
v___x_1134_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__0));
lean_inc(v_json_1133_);
v___x_1135_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocation_fromJson_spec__0(v_json_1133_, v___x_1134_);
if (lean_obj_tag(v___x_1135_) == 0)
{
lean_object* v_a_1136_; lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1145_; 
lean_dec(v_json_1133_);
v_a_1136_ = lean_ctor_get(v___x_1135_, 0);
v_isSharedCheck_1145_ = !lean_is_exclusive(v___x_1135_);
if (v_isSharedCheck_1145_ == 0)
{
v___x_1138_ = v___x_1135_;
v_isShared_1139_ = v_isSharedCheck_1145_;
goto v_resetjp_1137_;
}
else
{
lean_inc(v_a_1136_);
lean_dec(v___x_1135_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1145_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1143_; 
v___x_1140_ = lean_obj_once(&l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__5, &l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__5);
v___x_1141_ = lean_string_append(v___x_1140_, v_a_1136_);
lean_dec(v_a_1136_);
if (v_isShared_1139_ == 0)
{
lean_ctor_set(v___x_1138_, 0, v___x_1141_);
v___x_1143_ = v___x_1138_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v___x_1141_);
v___x_1143_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1142_;
}
v_reusejp_1142_:
{
return v___x_1143_;
}
}
}
else
{
if (lean_obj_tag(v___x_1135_) == 0)
{
lean_object* v_a_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1153_; 
lean_dec(v_json_1133_);
v_a_1146_ = lean_ctor_get(v___x_1135_, 0);
v_isSharedCheck_1153_ = !lean_is_exclusive(v___x_1135_);
if (v_isSharedCheck_1153_ == 0)
{
v___x_1148_ = v___x_1135_;
v_isShared_1149_ = v_isSharedCheck_1153_;
goto v_resetjp_1147_;
}
else
{
lean_inc(v_a_1146_);
lean_dec(v___x_1135_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1153_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
lean_object* v___x_1151_; 
if (v_isShared_1149_ == 0)
{
lean_ctor_set_tag(v___x_1148_, 0);
v___x_1151_ = v___x_1148_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v_a_1146_);
v___x_1151_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
return v___x_1151_;
}
}
}
else
{
lean_object* v_a_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; 
v_a_1154_ = lean_ctor_get(v___x_1135_, 0);
lean_inc(v_a_1154_);
lean_dec_ref_known(v___x_1135_, 1);
v___x_1155_ = ((lean_object*)(l_Lean_Lsp_instToJsonVersionedTextDocumentIdentifier_toJson___closed__0));
v___x_1156_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson_spec__0(v_json_1133_, v___x_1155_);
if (lean_obj_tag(v___x_1156_) == 0)
{
lean_object* v_a_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1166_; 
lean_dec(v_a_1154_);
v_a_1157_ = lean_ctor_get(v___x_1156_, 0);
v_isSharedCheck_1166_ = !lean_is_exclusive(v___x_1156_);
if (v_isSharedCheck_1166_ == 0)
{
v___x_1159_ = v___x_1156_;
v_isShared_1160_ = v_isSharedCheck_1166_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_a_1157_);
lean_dec(v___x_1156_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1166_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1164_; 
v___x_1161_ = lean_obj_once(&l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__10, &l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__10);
v___x_1162_ = lean_string_append(v___x_1161_, v_a_1157_);
lean_dec(v_a_1157_);
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 0, v___x_1162_);
v___x_1164_ = v___x_1159_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v___x_1162_);
v___x_1164_ = v_reuseFailAlloc_1165_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
return v___x_1164_;
}
}
}
else
{
if (lean_obj_tag(v___x_1156_) == 0)
{
lean_object* v_a_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1174_; 
lean_dec(v_a_1154_);
v_a_1167_ = lean_ctor_get(v___x_1156_, 0);
v_isSharedCheck_1174_ = !lean_is_exclusive(v___x_1156_);
if (v_isSharedCheck_1174_ == 0)
{
v___x_1169_ = v___x_1156_;
v_isShared_1170_ = v_isSharedCheck_1174_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_a_1167_);
lean_dec(v___x_1156_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1174_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
lean_object* v___x_1172_; 
if (v_isShared_1170_ == 0)
{
lean_ctor_set_tag(v___x_1169_, 0);
v___x_1172_ = v___x_1169_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v_a_1167_);
v___x_1172_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
return v___x_1172_;
}
}
}
else
{
lean_object* v_a_1175_; lean_object* v___x_1177_; uint8_t v_isShared_1178_; uint8_t v_isSharedCheck_1183_; 
v_a_1175_ = lean_ctor_get(v___x_1156_, 0);
v_isSharedCheck_1183_ = !lean_is_exclusive(v___x_1156_);
if (v_isSharedCheck_1183_ == 0)
{
v___x_1177_ = v___x_1156_;
v_isShared_1178_ = v_isSharedCheck_1183_;
goto v_resetjp_1176_;
}
else
{
lean_inc(v_a_1175_);
lean_dec(v___x_1156_);
v___x_1177_ = lean_box(0);
v_isShared_1178_ = v_isSharedCheck_1183_;
goto v_resetjp_1176_;
}
v_resetjp_1176_:
{
lean_object* v___x_1179_; lean_object* v___x_1181_; 
v___x_1179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1179_, 0, v_a_1154_);
lean_ctor_set(v___x_1179_, 1, v_a_1175_);
if (v_isShared_1178_ == 0)
{
lean_ctor_set(v___x_1177_, 0, v___x_1179_);
v___x_1181_ = v___x_1177_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v___x_1179_);
v___x_1181_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
return v___x_1181_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonTextDocumentEdit_toJson_spec__0_spec__0(size_t v_sz_1186_, size_t v_i_1187_, lean_object* v_bs_1188_){
_start:
{
uint8_t v___x_1189_; 
v___x_1189_ = lean_usize_dec_lt(v_i_1187_, v_sz_1186_);
if (v___x_1189_ == 0)
{
return v_bs_1188_;
}
else
{
lean_object* v_v_1190_; lean_object* v___x_1191_; lean_object* v_bs_x27_1192_; lean_object* v___x_1193_; size_t v___x_1194_; size_t v___x_1195_; lean_object* v___x_1196_; 
v_v_1190_ = lean_array_uget(v_bs_1188_, v_i_1187_);
v___x_1191_ = lean_unsigned_to_nat(0u);
v_bs_x27_1192_ = lean_array_uset(v_bs_1188_, v_i_1187_, v___x_1191_);
v___x_1193_ = l_Lean_Lsp_instToJsonTextEdit_toJson(v_v_1190_);
v___x_1194_ = ((size_t)1ULL);
v___x_1195_ = lean_usize_add(v_i_1187_, v___x_1194_);
v___x_1196_ = lean_array_uset(v_bs_x27_1192_, v_i_1187_, v___x_1193_);
v_i_1187_ = v___x_1195_;
v_bs_1188_ = v___x_1196_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonTextDocumentEdit_toJson_spec__0_spec__0___boxed(lean_object* v_sz_1198_, lean_object* v_i_1199_, lean_object* v_bs_1200_){
_start:
{
size_t v_sz_boxed_1201_; size_t v_i_boxed_1202_; lean_object* v_res_1203_; 
v_sz_boxed_1201_ = lean_unbox_usize(v_sz_1198_);
lean_dec(v_sz_1198_);
v_i_boxed_1202_ = lean_unbox_usize(v_i_1199_);
lean_dec(v_i_1199_);
v_res_1203_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonTextDocumentEdit_toJson_spec__0_spec__0(v_sz_boxed_1201_, v_i_boxed_1202_, v_bs_1200_);
return v_res_1203_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Lsp_instToJsonTextDocumentEdit_toJson_spec__0(lean_object* v_a_1204_){
_start:
{
size_t v_sz_1205_; size_t v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; 
v_sz_1205_ = lean_array_size(v_a_1204_);
v___x_1206_ = ((size_t)0ULL);
v___x_1207_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonTextDocumentEdit_toJson_spec__0_spec__0(v_sz_1205_, v___x_1206_, v_a_1204_);
v___x_1208_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1208_, 0, v___x_1207_);
return v___x_1208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonTextDocumentEdit_toJson(lean_object* v_x_1211_){
_start:
{
lean_object* v_textDocument_1212_; lean_object* v_edits_1213_; lean_object* v___x_1215_; uint8_t v_isShared_1216_; uint8_t v_isSharedCheck_1233_; 
v_textDocument_1212_ = lean_ctor_get(v_x_1211_, 0);
v_edits_1213_ = lean_ctor_get(v_x_1211_, 1);
v_isSharedCheck_1233_ = !lean_is_exclusive(v_x_1211_);
if (v_isSharedCheck_1233_ == 0)
{
v___x_1215_ = v_x_1211_;
v_isShared_1216_ = v_isSharedCheck_1233_;
goto v_resetjp_1214_;
}
else
{
lean_inc(v_edits_1213_);
lean_inc(v_textDocument_1212_);
lean_dec(v_x_1211_);
v___x_1215_ = lean_box(0);
v_isShared_1216_ = v_isSharedCheck_1233_;
goto v_resetjp_1214_;
}
v_resetjp_1214_:
{
lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1220_; 
v___x_1217_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextDocumentEdit_toJson___closed__0));
v___x_1218_ = l_Lean_Lsp_instToJsonVersionedTextDocumentIdentifier_toJson(v_textDocument_1212_);
if (v_isShared_1216_ == 0)
{
lean_ctor_set(v___x_1215_, 1, v___x_1218_);
lean_ctor_set(v___x_1215_, 0, v___x_1217_);
v___x_1220_ = v___x_1215_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v___x_1217_);
lean_ctor_set(v_reuseFailAlloc_1232_, 1, v___x_1218_);
v___x_1220_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; 
v___x_1221_ = lean_box(0);
v___x_1222_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1222_, 0, v___x_1220_);
lean_ctor_set(v___x_1222_, 1, v___x_1221_);
v___x_1223_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextDocumentEdit_toJson___closed__1));
v___x_1224_ = l_Array_toJson___at___00Lean_Lsp_instToJsonTextDocumentEdit_toJson_spec__0(v_edits_1213_);
v___x_1225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1225_, 0, v___x_1223_);
lean_ctor_set(v___x_1225_, 1, v___x_1224_);
v___x_1226_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1226_, 0, v___x_1225_);
lean_ctor_set(v___x_1226_, 1, v___x_1221_);
v___x_1227_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1227_, 0, v___x_1226_);
lean_ctor_set(v___x_1227_, 1, v___x_1221_);
v___x_1228_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1228_, 0, v___x_1222_);
lean_ctor_set(v___x_1228_, 1, v___x_1227_);
v___x_1229_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__2));
v___x_1230_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLocation_toJson_spec__0(v___x_1228_, v___x_1229_);
v___x_1231_ = l_Lean_Json_mkObj(v___x_1230_);
lean_dec(v___x_1230_);
return v___x_1231_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentEdit_fromJson_spec__0(lean_object* v_j_1236_, lean_object* v_k_1237_){
_start:
{
lean_object* v___x_1238_; lean_object* v___x_1239_; 
v___x_1238_ = l_Lean_Json_getObjValD(v_j_1236_, v_k_1237_);
v___x_1239_ = l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson(v___x_1238_);
return v___x_1239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentEdit_fromJson_spec__0___boxed(lean_object* v_j_1240_, lean_object* v_k_1241_){
_start:
{
lean_object* v_res_1242_; 
v_res_1242_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentEdit_fromJson_spec__0(v_j_1240_, v_k_1241_);
lean_dec_ref(v_k_1241_);
return v_res_1242_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentEdit_fromJson_spec__1_spec__1_spec__2(size_t v_sz_1243_, size_t v_i_1244_, lean_object* v_bs_1245_){
_start:
{
uint8_t v___x_1246_; 
v___x_1246_ = lean_usize_dec_lt(v_i_1244_, v_sz_1243_);
if (v___x_1246_ == 0)
{
lean_object* v___x_1247_; 
v___x_1247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1247_, 0, v_bs_1245_);
return v___x_1247_;
}
else
{
lean_object* v_v_1248_; lean_object* v___x_1249_; 
v_v_1248_ = lean_array_uget_borrowed(v_bs_1245_, v_i_1244_);
lean_inc(v_v_1248_);
v___x_1249_ = l_Lean_Lsp_instFromJsonTextEdit_fromJson(v_v_1248_);
if (lean_obj_tag(v___x_1249_) == 0)
{
lean_object* v_a_1250_; lean_object* v___x_1252_; uint8_t v_isShared_1253_; uint8_t v_isSharedCheck_1257_; 
lean_dec_ref(v_bs_1245_);
v_a_1250_ = lean_ctor_get(v___x_1249_, 0);
v_isSharedCheck_1257_ = !lean_is_exclusive(v___x_1249_);
if (v_isSharedCheck_1257_ == 0)
{
v___x_1252_ = v___x_1249_;
v_isShared_1253_ = v_isSharedCheck_1257_;
goto v_resetjp_1251_;
}
else
{
lean_inc(v_a_1250_);
lean_dec(v___x_1249_);
v___x_1252_ = lean_box(0);
v_isShared_1253_ = v_isSharedCheck_1257_;
goto v_resetjp_1251_;
}
v_resetjp_1251_:
{
lean_object* v___x_1255_; 
if (v_isShared_1253_ == 0)
{
v___x_1255_ = v___x_1252_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v_a_1250_);
v___x_1255_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
return v___x_1255_;
}
}
}
else
{
lean_object* v_a_1258_; lean_object* v___x_1259_; lean_object* v_bs_x27_1260_; size_t v___x_1261_; size_t v___x_1262_; lean_object* v___x_1263_; 
v_a_1258_ = lean_ctor_get(v___x_1249_, 0);
lean_inc(v_a_1258_);
lean_dec_ref_known(v___x_1249_, 1);
v___x_1259_ = lean_unsigned_to_nat(0u);
v_bs_x27_1260_ = lean_array_uset(v_bs_1245_, v_i_1244_, v___x_1259_);
v___x_1261_ = ((size_t)1ULL);
v___x_1262_ = lean_usize_add(v_i_1244_, v___x_1261_);
v___x_1263_ = lean_array_uset(v_bs_x27_1260_, v_i_1244_, v_a_1258_);
v_i_1244_ = v___x_1262_;
v_bs_1245_ = v___x_1263_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentEdit_fromJson_spec__1_spec__1_spec__2___boxed(lean_object* v_sz_1265_, lean_object* v_i_1266_, lean_object* v_bs_1267_){
_start:
{
size_t v_sz_boxed_1268_; size_t v_i_boxed_1269_; lean_object* v_res_1270_; 
v_sz_boxed_1268_ = lean_unbox_usize(v_sz_1265_);
lean_dec(v_sz_1265_);
v_i_boxed_1269_ = lean_unbox_usize(v_i_1266_);
lean_dec(v_i_1266_);
v_res_1270_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentEdit_fromJson_spec__1_spec__1_spec__2(v_sz_boxed_1268_, v_i_boxed_1269_, v_bs_1267_);
return v_res_1270_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentEdit_fromJson_spec__1_spec__1(lean_object* v_x_1271_){
_start:
{
if (lean_obj_tag(v_x_1271_) == 4)
{
lean_object* v_elems_1272_; size_t v_sz_1273_; size_t v___x_1274_; lean_object* v___x_1275_; 
v_elems_1272_ = lean_ctor_get(v_x_1271_, 0);
lean_inc_ref(v_elems_1272_);
lean_dec_ref_known(v_x_1271_, 1);
v_sz_1273_ = lean_array_size(v_elems_1272_);
v___x_1274_ = ((size_t)0ULL);
v___x_1275_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentEdit_fromJson_spec__1_spec__1_spec__2(v_sz_1273_, v___x_1274_, v_elems_1272_);
return v___x_1275_;
}
else
{
lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; 
v___x_1276_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCommand_fromJson_spec__0_spec__0_spec__1___closed__0));
v___x_1277_ = lean_unsigned_to_nat(80u);
v___x_1278_ = l_Lean_Json_pretty(v_x_1271_, v___x_1277_);
v___x_1279_ = lean_string_append(v___x_1276_, v___x_1278_);
lean_dec_ref(v___x_1278_);
v___x_1280_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCommand_fromJson_spec__0_spec__0_spec__1___closed__1));
v___x_1281_ = lean_string_append(v___x_1279_, v___x_1280_);
v___x_1282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1282_, 0, v___x_1281_);
return v___x_1282_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentEdit_fromJson_spec__1(lean_object* v_j_1283_, lean_object* v_k_1284_){
_start:
{
lean_object* v___x_1285_; lean_object* v___x_1286_; 
v___x_1285_ = l_Lean_Json_getObjValD(v_j_1283_, v_k_1284_);
v___x_1286_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentEdit_fromJson_spec__1_spec__1(v___x_1285_);
return v___x_1286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentEdit_fromJson_spec__1___boxed(lean_object* v_j_1287_, lean_object* v_k_1288_){
_start:
{
lean_object* v_res_1289_; 
v_res_1289_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentEdit_fromJson_spec__1(v_j_1287_, v_k_1288_);
lean_dec_ref(v_k_1288_);
return v_res_1289_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__2(void){
_start:
{
uint8_t v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; 
v___x_1295_ = 1;
v___x_1296_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__1));
v___x_1297_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1296_, v___x_1295_);
return v___x_1297_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__3(void){
_start:
{
lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; 
v___x_1298_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__5));
v___x_1299_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__2, &l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__2);
v___x_1300_ = lean_string_append(v___x_1299_, v___x_1298_);
return v___x_1300_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__5(void){
_start:
{
uint8_t v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; 
v___x_1303_ = 1;
v___x_1304_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__4));
v___x_1305_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1304_, v___x_1303_);
return v___x_1305_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__6(void){
_start:
{
lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; 
v___x_1306_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__5, &l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__5);
v___x_1307_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__3, &l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__3);
v___x_1308_ = lean_string_append(v___x_1307_, v___x_1306_);
return v___x_1308_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__7(void){
_start:
{
lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; 
v___x_1309_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_1310_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__6, &l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__6);
v___x_1311_ = lean_string_append(v___x_1310_, v___x_1309_);
return v___x_1311_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__9(void){
_start:
{
uint8_t v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; 
v___x_1314_ = 1;
v___x_1315_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__8));
v___x_1316_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1315_, v___x_1314_);
return v___x_1316_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__10(void){
_start:
{
lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; 
v___x_1317_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__9, &l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__9);
v___x_1318_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__3, &l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__3);
v___x_1319_ = lean_string_append(v___x_1318_, v___x_1317_);
return v___x_1319_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__11(void){
_start:
{
lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; 
v___x_1320_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_1321_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__10, &l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__10);
v___x_1322_ = lean_string_append(v___x_1321_, v___x_1320_);
return v___x_1322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson(lean_object* v_json_1323_){
_start:
{
lean_object* v___x_1324_; lean_object* v___x_1325_; 
v___x_1324_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextDocumentEdit_toJson___closed__0));
lean_inc(v_json_1323_);
v___x_1325_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentEdit_fromJson_spec__0(v_json_1323_, v___x_1324_);
if (lean_obj_tag(v___x_1325_) == 0)
{
lean_object* v_a_1326_; lean_object* v___x_1328_; uint8_t v_isShared_1329_; uint8_t v_isSharedCheck_1335_; 
lean_dec(v_json_1323_);
v_a_1326_ = lean_ctor_get(v___x_1325_, 0);
v_isSharedCheck_1335_ = !lean_is_exclusive(v___x_1325_);
if (v_isSharedCheck_1335_ == 0)
{
v___x_1328_ = v___x_1325_;
v_isShared_1329_ = v_isSharedCheck_1335_;
goto v_resetjp_1327_;
}
else
{
lean_inc(v_a_1326_);
lean_dec(v___x_1325_);
v___x_1328_ = lean_box(0);
v_isShared_1329_ = v_isSharedCheck_1335_;
goto v_resetjp_1327_;
}
v_resetjp_1327_:
{
lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1333_; 
v___x_1330_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__7, &l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__7);
v___x_1331_ = lean_string_append(v___x_1330_, v_a_1326_);
lean_dec(v_a_1326_);
if (v_isShared_1329_ == 0)
{
lean_ctor_set(v___x_1328_, 0, v___x_1331_);
v___x_1333_ = v___x_1328_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v___x_1331_);
v___x_1333_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
return v___x_1333_;
}
}
}
else
{
if (lean_obj_tag(v___x_1325_) == 0)
{
lean_object* v_a_1336_; lean_object* v___x_1338_; uint8_t v_isShared_1339_; uint8_t v_isSharedCheck_1343_; 
lean_dec(v_json_1323_);
v_a_1336_ = lean_ctor_get(v___x_1325_, 0);
v_isSharedCheck_1343_ = !lean_is_exclusive(v___x_1325_);
if (v_isSharedCheck_1343_ == 0)
{
v___x_1338_ = v___x_1325_;
v_isShared_1339_ = v_isSharedCheck_1343_;
goto v_resetjp_1337_;
}
else
{
lean_inc(v_a_1336_);
lean_dec(v___x_1325_);
v___x_1338_ = lean_box(0);
v_isShared_1339_ = v_isSharedCheck_1343_;
goto v_resetjp_1337_;
}
v_resetjp_1337_:
{
lean_object* v___x_1341_; 
if (v_isShared_1339_ == 0)
{
lean_ctor_set_tag(v___x_1338_, 0);
v___x_1341_ = v___x_1338_;
goto v_reusejp_1340_;
}
else
{
lean_object* v_reuseFailAlloc_1342_; 
v_reuseFailAlloc_1342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1342_, 0, v_a_1336_);
v___x_1341_ = v_reuseFailAlloc_1342_;
goto v_reusejp_1340_;
}
v_reusejp_1340_:
{
return v___x_1341_;
}
}
}
else
{
lean_object* v_a_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; 
v_a_1344_ = lean_ctor_get(v___x_1325_, 0);
lean_inc(v_a_1344_);
lean_dec_ref_known(v___x_1325_, 1);
v___x_1345_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextDocumentEdit_toJson___closed__1));
v___x_1346_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentEdit_fromJson_spec__1(v_json_1323_, v___x_1345_);
if (lean_obj_tag(v___x_1346_) == 0)
{
lean_object* v_a_1347_; lean_object* v___x_1349_; uint8_t v_isShared_1350_; uint8_t v_isSharedCheck_1356_; 
lean_dec(v_a_1344_);
v_a_1347_ = lean_ctor_get(v___x_1346_, 0);
v_isSharedCheck_1356_ = !lean_is_exclusive(v___x_1346_);
if (v_isSharedCheck_1356_ == 0)
{
v___x_1349_ = v___x_1346_;
v_isShared_1350_ = v_isSharedCheck_1356_;
goto v_resetjp_1348_;
}
else
{
lean_inc(v_a_1347_);
lean_dec(v___x_1346_);
v___x_1349_ = lean_box(0);
v_isShared_1350_ = v_isSharedCheck_1356_;
goto v_resetjp_1348_;
}
v_resetjp_1348_:
{
lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1354_; 
v___x_1351_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__11, &l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__11);
v___x_1352_ = lean_string_append(v___x_1351_, v_a_1347_);
lean_dec(v_a_1347_);
if (v_isShared_1350_ == 0)
{
lean_ctor_set(v___x_1349_, 0, v___x_1352_);
v___x_1354_ = v___x_1349_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v___x_1352_);
v___x_1354_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
return v___x_1354_;
}
}
}
else
{
if (lean_obj_tag(v___x_1346_) == 0)
{
lean_object* v_a_1357_; lean_object* v___x_1359_; uint8_t v_isShared_1360_; uint8_t v_isSharedCheck_1364_; 
lean_dec(v_a_1344_);
v_a_1357_ = lean_ctor_get(v___x_1346_, 0);
v_isSharedCheck_1364_ = !lean_is_exclusive(v___x_1346_);
if (v_isSharedCheck_1364_ == 0)
{
v___x_1359_ = v___x_1346_;
v_isShared_1360_ = v_isSharedCheck_1364_;
goto v_resetjp_1358_;
}
else
{
lean_inc(v_a_1357_);
lean_dec(v___x_1346_);
v___x_1359_ = lean_box(0);
v_isShared_1360_ = v_isSharedCheck_1364_;
goto v_resetjp_1358_;
}
v_resetjp_1358_:
{
lean_object* v___x_1362_; 
if (v_isShared_1360_ == 0)
{
lean_ctor_set_tag(v___x_1359_, 0);
v___x_1362_ = v___x_1359_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v_a_1357_);
v___x_1362_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
return v___x_1362_;
}
}
}
else
{
lean_object* v_a_1365_; lean_object* v___x_1367_; uint8_t v_isShared_1368_; uint8_t v_isSharedCheck_1373_; 
v_a_1365_ = lean_ctor_get(v___x_1346_, 0);
v_isSharedCheck_1373_ = !lean_is_exclusive(v___x_1346_);
if (v_isSharedCheck_1373_ == 0)
{
v___x_1367_ = v___x_1346_;
v_isShared_1368_ = v_isSharedCheck_1373_;
goto v_resetjp_1366_;
}
else
{
lean_inc(v_a_1365_);
lean_dec(v___x_1346_);
v___x_1367_ = lean_box(0);
v_isShared_1368_ = v_isSharedCheck_1373_;
goto v_resetjp_1366_;
}
v_resetjp_1366_:
{
lean_object* v___x_1369_; lean_object* v___x_1371_; 
v___x_1369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1369_, 0, v_a_1344_);
lean_ctor_set(v___x_1369_, 1, v_a_1365_);
if (v_isShared_1368_ == 0)
{
lean_ctor_set(v___x_1367_, 0, v___x_1369_);
v___x_1371_ = v___x_1367_;
goto v_reusejp_1370_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v___x_1369_);
v___x_1371_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1370_;
}
v_reusejp_1370_:
{
return v___x_1371_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonChangeAnnotation_toJson(lean_object* v_x_1379_){
_start:
{
lean_object* v_label_1380_; uint8_t v_needsConfirmation_1381_; lean_object* v_description_x3f_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; 
v_label_1380_ = lean_ctor_get(v_x_1379_, 0);
lean_inc_ref(v_label_1380_);
v_needsConfirmation_1381_ = lean_ctor_get_uint8(v_x_1379_, sizeof(void*)*2);
v_description_x3f_1382_ = lean_ctor_get(v_x_1379_, 1);
lean_inc(v_description_x3f_1382_);
lean_dec_ref(v_x_1379_);
v___x_1383_ = ((lean_object*)(l_Lean_Lsp_instToJsonChangeAnnotation_toJson___closed__0));
v___x_1384_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1384_, 0, v_label_1380_);
v___x_1385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1385_, 0, v___x_1383_);
lean_ctor_set(v___x_1385_, 1, v___x_1384_);
v___x_1386_ = lean_box(0);
v___x_1387_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1387_, 0, v___x_1385_);
lean_ctor_set(v___x_1387_, 1, v___x_1386_);
v___x_1388_ = ((lean_object*)(l_Lean_Lsp_instToJsonChangeAnnotation_toJson___closed__1));
v___x_1389_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1389_, 0, v_needsConfirmation_1381_);
v___x_1390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1390_, 0, v___x_1388_);
lean_ctor_set(v___x_1390_, 1, v___x_1389_);
v___x_1391_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1391_, 0, v___x_1390_);
lean_ctor_set(v___x_1391_, 1, v___x_1386_);
v___x_1392_ = ((lean_object*)(l_Lean_Lsp_instToJsonChangeAnnotation_toJson___closed__2));
v___x_1393_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextEdit_toJson_spec__1(v___x_1392_, v_description_x3f_1382_);
v___x_1394_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1394_, 0, v___x_1393_);
lean_ctor_set(v___x_1394_, 1, v___x_1386_);
v___x_1395_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1395_, 0, v___x_1391_);
lean_ctor_set(v___x_1395_, 1, v___x_1394_);
v___x_1396_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1396_, 0, v___x_1387_);
lean_ctor_set(v___x_1396_, 1, v___x_1395_);
v___x_1397_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__2));
v___x_1398_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLocation_toJson_spec__0(v___x_1396_, v___x_1397_);
v___x_1399_ = l_Lean_Json_mkObj(v___x_1398_);
lean_dec(v___x_1398_);
return v___x_1399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonChangeAnnotation_fromJson_spec__0(lean_object* v_j_1402_, lean_object* v_k_1403_){
_start:
{
lean_object* v___x_1404_; lean_object* v___x_1405_; 
v___x_1404_ = l_Lean_Json_getObjValD(v_j_1402_, v_k_1403_);
v___x_1405_ = l_Lean_Json_getBool_x3f(v___x_1404_);
lean_dec(v___x_1404_);
return v___x_1405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonChangeAnnotation_fromJson_spec__0___boxed(lean_object* v_j_1406_, lean_object* v_k_1407_){
_start:
{
lean_object* v_res_1408_; 
v_res_1408_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonChangeAnnotation_fromJson_spec__0(v_j_1406_, v_k_1407_);
lean_dec_ref(v_k_1407_);
return v_res_1408_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__2(void){
_start:
{
uint8_t v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; 
v___x_1414_ = 1;
v___x_1415_ = ((lean_object*)(l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__1));
v___x_1416_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1415_, v___x_1414_);
return v___x_1416_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__3(void){
_start:
{
lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; 
v___x_1417_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__5));
v___x_1418_ = lean_obj_once(&l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__2, &l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__2);
v___x_1419_ = lean_string_append(v___x_1418_, v___x_1417_);
return v___x_1419_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__5(void){
_start:
{
uint8_t v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; 
v___x_1422_ = 1;
v___x_1423_ = ((lean_object*)(l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__4));
v___x_1424_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1423_, v___x_1422_);
return v___x_1424_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__6(void){
_start:
{
lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; 
v___x_1425_ = lean_obj_once(&l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__5, &l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__5);
v___x_1426_ = lean_obj_once(&l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__3, &l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__3);
v___x_1427_ = lean_string_append(v___x_1426_, v___x_1425_);
return v___x_1427_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__7(void){
_start:
{
lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; 
v___x_1428_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_1429_ = lean_obj_once(&l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__6, &l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__6);
v___x_1430_ = lean_string_append(v___x_1429_, v___x_1428_);
return v___x_1430_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__9(void){
_start:
{
uint8_t v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; 
v___x_1433_ = 1;
v___x_1434_ = ((lean_object*)(l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__8));
v___x_1435_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1434_, v___x_1433_);
return v___x_1435_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__10(void){
_start:
{
lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; 
v___x_1436_ = lean_obj_once(&l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__9, &l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__9);
v___x_1437_ = lean_obj_once(&l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__3, &l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__3);
v___x_1438_ = lean_string_append(v___x_1437_, v___x_1436_);
return v___x_1438_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__11(void){
_start:
{
lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; 
v___x_1439_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_1440_ = lean_obj_once(&l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__10, &l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__10);
v___x_1441_ = lean_string_append(v___x_1440_, v___x_1439_);
return v___x_1441_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__14(void){
_start:
{
uint8_t v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; 
v___x_1445_ = 1;
v___x_1446_ = ((lean_object*)(l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__13));
v___x_1447_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1446_, v___x_1445_);
return v___x_1447_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__15(void){
_start:
{
lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; 
v___x_1448_ = lean_obj_once(&l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__14, &l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__14_once, _init_l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__14);
v___x_1449_ = lean_obj_once(&l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__3, &l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__3);
v___x_1450_ = lean_string_append(v___x_1449_, v___x_1448_);
return v___x_1450_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__16(void){
_start:
{
lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; 
v___x_1451_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_1452_ = lean_obj_once(&l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__15, &l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__15_once, _init_l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__15);
v___x_1453_ = lean_string_append(v___x_1452_, v___x_1451_);
return v___x_1453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson(lean_object* v_json_1454_){
_start:
{
lean_object* v___x_1455_; lean_object* v___x_1456_; 
v___x_1455_ = ((lean_object*)(l_Lean_Lsp_instToJsonChangeAnnotation_toJson___closed__0));
lean_inc(v_json_1454_);
v___x_1456_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocation_fromJson_spec__0(v_json_1454_, v___x_1455_);
if (lean_obj_tag(v___x_1456_) == 0)
{
lean_object* v_a_1457_; lean_object* v___x_1459_; uint8_t v_isShared_1460_; uint8_t v_isSharedCheck_1466_; 
lean_dec(v_json_1454_);
v_a_1457_ = lean_ctor_get(v___x_1456_, 0);
v_isSharedCheck_1466_ = !lean_is_exclusive(v___x_1456_);
if (v_isSharedCheck_1466_ == 0)
{
v___x_1459_ = v___x_1456_;
v_isShared_1460_ = v_isSharedCheck_1466_;
goto v_resetjp_1458_;
}
else
{
lean_inc(v_a_1457_);
lean_dec(v___x_1456_);
v___x_1459_ = lean_box(0);
v_isShared_1460_ = v_isSharedCheck_1466_;
goto v_resetjp_1458_;
}
v_resetjp_1458_:
{
lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1464_; 
v___x_1461_ = lean_obj_once(&l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__7, &l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__7);
v___x_1462_ = lean_string_append(v___x_1461_, v_a_1457_);
lean_dec(v_a_1457_);
if (v_isShared_1460_ == 0)
{
lean_ctor_set(v___x_1459_, 0, v___x_1462_);
v___x_1464_ = v___x_1459_;
goto v_reusejp_1463_;
}
else
{
lean_object* v_reuseFailAlloc_1465_; 
v_reuseFailAlloc_1465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1465_, 0, v___x_1462_);
v___x_1464_ = v_reuseFailAlloc_1465_;
goto v_reusejp_1463_;
}
v_reusejp_1463_:
{
return v___x_1464_;
}
}
}
else
{
if (lean_obj_tag(v___x_1456_) == 0)
{
lean_object* v_a_1467_; lean_object* v___x_1469_; uint8_t v_isShared_1470_; uint8_t v_isSharedCheck_1474_; 
lean_dec(v_json_1454_);
v_a_1467_ = lean_ctor_get(v___x_1456_, 0);
v_isSharedCheck_1474_ = !lean_is_exclusive(v___x_1456_);
if (v_isSharedCheck_1474_ == 0)
{
v___x_1469_ = v___x_1456_;
v_isShared_1470_ = v_isSharedCheck_1474_;
goto v_resetjp_1468_;
}
else
{
lean_inc(v_a_1467_);
lean_dec(v___x_1456_);
v___x_1469_ = lean_box(0);
v_isShared_1470_ = v_isSharedCheck_1474_;
goto v_resetjp_1468_;
}
v_resetjp_1468_:
{
lean_object* v___x_1472_; 
if (v_isShared_1470_ == 0)
{
lean_ctor_set_tag(v___x_1469_, 0);
v___x_1472_ = v___x_1469_;
goto v_reusejp_1471_;
}
else
{
lean_object* v_reuseFailAlloc_1473_; 
v_reuseFailAlloc_1473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1473_, 0, v_a_1467_);
v___x_1472_ = v_reuseFailAlloc_1473_;
goto v_reusejp_1471_;
}
v_reusejp_1471_:
{
return v___x_1472_;
}
}
}
else
{
lean_object* v_a_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; 
v_a_1475_ = lean_ctor_get(v___x_1456_, 0);
lean_inc(v_a_1475_);
lean_dec_ref_known(v___x_1456_, 1);
v___x_1476_ = ((lean_object*)(l_Lean_Lsp_instToJsonChangeAnnotation_toJson___closed__1));
lean_inc(v_json_1454_);
v___x_1477_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonChangeAnnotation_fromJson_spec__0(v_json_1454_, v___x_1476_);
if (lean_obj_tag(v___x_1477_) == 0)
{
lean_object* v_a_1478_; lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1487_; 
lean_dec(v_a_1475_);
lean_dec(v_json_1454_);
v_a_1478_ = lean_ctor_get(v___x_1477_, 0);
v_isSharedCheck_1487_ = !lean_is_exclusive(v___x_1477_);
if (v_isSharedCheck_1487_ == 0)
{
v___x_1480_ = v___x_1477_;
v_isShared_1481_ = v_isSharedCheck_1487_;
goto v_resetjp_1479_;
}
else
{
lean_inc(v_a_1478_);
lean_dec(v___x_1477_);
v___x_1480_ = lean_box(0);
v_isShared_1481_ = v_isSharedCheck_1487_;
goto v_resetjp_1479_;
}
v_resetjp_1479_:
{
lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1485_; 
v___x_1482_ = lean_obj_once(&l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__11, &l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__11);
v___x_1483_ = lean_string_append(v___x_1482_, v_a_1478_);
lean_dec(v_a_1478_);
if (v_isShared_1481_ == 0)
{
lean_ctor_set(v___x_1480_, 0, v___x_1483_);
v___x_1485_ = v___x_1480_;
goto v_reusejp_1484_;
}
else
{
lean_object* v_reuseFailAlloc_1486_; 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v___x_1483_);
v___x_1485_ = v_reuseFailAlloc_1486_;
goto v_reusejp_1484_;
}
v_reusejp_1484_:
{
return v___x_1485_;
}
}
}
else
{
if (lean_obj_tag(v___x_1477_) == 0)
{
lean_object* v_a_1488_; lean_object* v___x_1490_; uint8_t v_isShared_1491_; uint8_t v_isSharedCheck_1495_; 
lean_dec(v_a_1475_);
lean_dec(v_json_1454_);
v_a_1488_ = lean_ctor_get(v___x_1477_, 0);
v_isSharedCheck_1495_ = !lean_is_exclusive(v___x_1477_);
if (v_isSharedCheck_1495_ == 0)
{
v___x_1490_ = v___x_1477_;
v_isShared_1491_ = v_isSharedCheck_1495_;
goto v_resetjp_1489_;
}
else
{
lean_inc(v_a_1488_);
lean_dec(v___x_1477_);
v___x_1490_ = lean_box(0);
v_isShared_1491_ = v_isSharedCheck_1495_;
goto v_resetjp_1489_;
}
v_resetjp_1489_:
{
lean_object* v___x_1493_; 
if (v_isShared_1491_ == 0)
{
lean_ctor_set_tag(v___x_1490_, 0);
v___x_1493_ = v___x_1490_;
goto v_reusejp_1492_;
}
else
{
lean_object* v_reuseFailAlloc_1494_; 
v_reuseFailAlloc_1494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1494_, 0, v_a_1488_);
v___x_1493_ = v_reuseFailAlloc_1494_;
goto v_reusejp_1492_;
}
v_reusejp_1492_:
{
return v___x_1493_;
}
}
}
else
{
lean_object* v_a_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; 
v_a_1496_ = lean_ctor_get(v___x_1477_, 0);
lean_inc(v_a_1496_);
lean_dec_ref_known(v___x_1477_, 1);
v___x_1497_ = ((lean_object*)(l_Lean_Lsp_instToJsonChangeAnnotation_toJson___closed__2));
v___x_1498_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextEdit_fromJson_spec__1(v_json_1454_, v___x_1497_);
if (lean_obj_tag(v___x_1498_) == 0)
{
lean_object* v_a_1499_; lean_object* v___x_1501_; uint8_t v_isShared_1502_; uint8_t v_isSharedCheck_1508_; 
lean_dec(v_a_1496_);
lean_dec(v_a_1475_);
v_a_1499_ = lean_ctor_get(v___x_1498_, 0);
v_isSharedCheck_1508_ = !lean_is_exclusive(v___x_1498_);
if (v_isSharedCheck_1508_ == 0)
{
v___x_1501_ = v___x_1498_;
v_isShared_1502_ = v_isSharedCheck_1508_;
goto v_resetjp_1500_;
}
else
{
lean_inc(v_a_1499_);
lean_dec(v___x_1498_);
v___x_1501_ = lean_box(0);
v_isShared_1502_ = v_isSharedCheck_1508_;
goto v_resetjp_1500_;
}
v_resetjp_1500_:
{
lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1506_; 
v___x_1503_ = lean_obj_once(&l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__16, &l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__16_once, _init_l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__16);
v___x_1504_ = lean_string_append(v___x_1503_, v_a_1499_);
lean_dec(v_a_1499_);
if (v_isShared_1502_ == 0)
{
lean_ctor_set(v___x_1501_, 0, v___x_1504_);
v___x_1506_ = v___x_1501_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v___x_1504_);
v___x_1506_ = v_reuseFailAlloc_1507_;
goto v_reusejp_1505_;
}
v_reusejp_1505_:
{
return v___x_1506_;
}
}
}
else
{
if (lean_obj_tag(v___x_1498_) == 0)
{
lean_object* v_a_1509_; lean_object* v___x_1511_; uint8_t v_isShared_1512_; uint8_t v_isSharedCheck_1516_; 
lean_dec(v_a_1496_);
lean_dec(v_a_1475_);
v_a_1509_ = lean_ctor_get(v___x_1498_, 0);
v_isSharedCheck_1516_ = !lean_is_exclusive(v___x_1498_);
if (v_isSharedCheck_1516_ == 0)
{
v___x_1511_ = v___x_1498_;
v_isShared_1512_ = v_isSharedCheck_1516_;
goto v_resetjp_1510_;
}
else
{
lean_inc(v_a_1509_);
lean_dec(v___x_1498_);
v___x_1511_ = lean_box(0);
v_isShared_1512_ = v_isSharedCheck_1516_;
goto v_resetjp_1510_;
}
v_resetjp_1510_:
{
lean_object* v___x_1514_; 
if (v_isShared_1512_ == 0)
{
lean_ctor_set_tag(v___x_1511_, 0);
v___x_1514_ = v___x_1511_;
goto v_reusejp_1513_;
}
else
{
lean_object* v_reuseFailAlloc_1515_; 
v_reuseFailAlloc_1515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1515_, 0, v_a_1509_);
v___x_1514_ = v_reuseFailAlloc_1515_;
goto v_reusejp_1513_;
}
v_reusejp_1513_:
{
return v___x_1514_;
}
}
}
else
{
lean_object* v_a_1517_; lean_object* v___x_1519_; uint8_t v_isShared_1520_; uint8_t v_isSharedCheck_1526_; 
v_a_1517_ = lean_ctor_get(v___x_1498_, 0);
v_isSharedCheck_1526_ = !lean_is_exclusive(v___x_1498_);
if (v_isSharedCheck_1526_ == 0)
{
v___x_1519_ = v___x_1498_;
v_isShared_1520_ = v_isSharedCheck_1526_;
goto v_resetjp_1518_;
}
else
{
lean_inc(v_a_1517_);
lean_dec(v___x_1498_);
v___x_1519_ = lean_box(0);
v_isShared_1520_ = v_isSharedCheck_1526_;
goto v_resetjp_1518_;
}
v_resetjp_1518_:
{
lean_object* v___x_1521_; uint8_t v___x_1522_; lean_object* v___x_1524_; 
v___x_1521_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1521_, 0, v_a_1475_);
lean_ctor_set(v___x_1521_, 1, v_a_1517_);
v___x_1522_ = lean_unbox(v_a_1496_);
lean_dec(v_a_1496_);
lean_ctor_set_uint8(v___x_1521_, sizeof(void*)*2, v___x_1522_);
if (v_isShared_1520_ == 0)
{
lean_ctor_set(v___x_1519_, 0, v___x_1521_);
v___x_1524_ = v___x_1519_;
goto v_reusejp_1523_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v___x_1521_);
v___x_1524_ = v_reuseFailAlloc_1525_;
goto v_reusejp_1523_;
}
v_reusejp_1523_:
{
return v___x_1524_;
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
LEAN_EXPORT lean_object* l_Lean_Lsp_CreateFile_instToJsonOptions_toJson(lean_object* v_x_1531_){
_start:
{
uint8_t v_overwrite_1532_; uint8_t v_ignoreIfExists_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; 
v_overwrite_1532_ = lean_ctor_get_uint8(v_x_1531_, 0);
v_ignoreIfExists_1533_ = lean_ctor_get_uint8(v_x_1531_, 1);
v___x_1534_ = ((lean_object*)(l_Lean_Lsp_CreateFile_instToJsonOptions_toJson___closed__0));
v___x_1535_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1535_, 0, v_overwrite_1532_);
v___x_1536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1536_, 0, v___x_1534_);
lean_ctor_set(v___x_1536_, 1, v___x_1535_);
v___x_1537_ = lean_box(0);
v___x_1538_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1538_, 0, v___x_1536_);
lean_ctor_set(v___x_1538_, 1, v___x_1537_);
v___x_1539_ = ((lean_object*)(l_Lean_Lsp_CreateFile_instToJsonOptions_toJson___closed__1));
v___x_1540_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1540_, 0, v_ignoreIfExists_1533_);
v___x_1541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1541_, 0, v___x_1539_);
lean_ctor_set(v___x_1541_, 1, v___x_1540_);
v___x_1542_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1542_, 0, v___x_1541_);
lean_ctor_set(v___x_1542_, 1, v___x_1537_);
v___x_1543_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1543_, 0, v___x_1542_);
lean_ctor_set(v___x_1543_, 1, v___x_1537_);
v___x_1544_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1544_, 0, v___x_1538_);
lean_ctor_set(v___x_1544_, 1, v___x_1543_);
v___x_1545_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__2));
v___x_1546_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLocation_toJson_spec__0(v___x_1544_, v___x_1545_);
v___x_1547_ = l_Lean_Json_mkObj(v___x_1546_);
lean_dec(v___x_1546_);
return v___x_1547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_CreateFile_instToJsonOptions_toJson___boxed(lean_object* v_x_1548_){
_start:
{
lean_object* v_res_1549_; 
v_res_1549_ = l_Lean_Lsp_CreateFile_instToJsonOptions_toJson(v_x_1548_);
lean_dec_ref(v_x_1548_);
return v_res_1549_;
}
}
static lean_object* _init_l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__3(void){
_start:
{
uint8_t v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; 
v___x_1559_ = 1;
v___x_1560_ = ((lean_object*)(l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__2));
v___x_1561_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1560_, v___x_1559_);
return v___x_1561_;
}
}
static lean_object* _init_l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__4(void){
_start:
{
lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; 
v___x_1562_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__5));
v___x_1563_ = lean_obj_once(&l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__3, &l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__3_once, _init_l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__3);
v___x_1564_ = lean_string_append(v___x_1563_, v___x_1562_);
return v___x_1564_;
}
}
static lean_object* _init_l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__6(void){
_start:
{
uint8_t v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; 
v___x_1567_ = 1;
v___x_1568_ = ((lean_object*)(l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__5));
v___x_1569_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1568_, v___x_1567_);
return v___x_1569_;
}
}
static lean_object* _init_l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__7(void){
_start:
{
lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; 
v___x_1570_ = lean_obj_once(&l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__6, &l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__6_once, _init_l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__6);
v___x_1571_ = lean_obj_once(&l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__4, &l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__4_once, _init_l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__4);
v___x_1572_ = lean_string_append(v___x_1571_, v___x_1570_);
return v___x_1572_;
}
}
static lean_object* _init_l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__8(void){
_start:
{
lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; 
v___x_1573_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_1574_ = lean_obj_once(&l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__7, &l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__7_once, _init_l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__7);
v___x_1575_ = lean_string_append(v___x_1574_, v___x_1573_);
return v___x_1575_;
}
}
static lean_object* _init_l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__10(void){
_start:
{
uint8_t v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; 
v___x_1578_ = 1;
v___x_1579_ = ((lean_object*)(l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__9));
v___x_1580_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1579_, v___x_1578_);
return v___x_1580_;
}
}
static lean_object* _init_l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__11(void){
_start:
{
lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; 
v___x_1581_ = lean_obj_once(&l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__10, &l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__10_once, _init_l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__10);
v___x_1582_ = lean_obj_once(&l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__4, &l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__4_once, _init_l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__4);
v___x_1583_ = lean_string_append(v___x_1582_, v___x_1581_);
return v___x_1583_;
}
}
static lean_object* _init_l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__12(void){
_start:
{
lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; 
v___x_1584_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_1585_ = lean_obj_once(&l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__11, &l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__11_once, _init_l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__11);
v___x_1586_ = lean_string_append(v___x_1585_, v___x_1584_);
return v___x_1586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson(lean_object* v_json_1587_){
_start:
{
lean_object* v___x_1588_; lean_object* v___x_1589_; 
v___x_1588_ = ((lean_object*)(l_Lean_Lsp_CreateFile_instToJsonOptions_toJson___closed__0));
lean_inc(v_json_1587_);
v___x_1589_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonChangeAnnotation_fromJson_spec__0(v_json_1587_, v___x_1588_);
if (lean_obj_tag(v___x_1589_) == 0)
{
lean_object* v_a_1590_; lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1599_; 
lean_dec(v_json_1587_);
v_a_1590_ = lean_ctor_get(v___x_1589_, 0);
v_isSharedCheck_1599_ = !lean_is_exclusive(v___x_1589_);
if (v_isSharedCheck_1599_ == 0)
{
v___x_1592_ = v___x_1589_;
v_isShared_1593_ = v_isSharedCheck_1599_;
goto v_resetjp_1591_;
}
else
{
lean_inc(v_a_1590_);
lean_dec(v___x_1589_);
v___x_1592_ = lean_box(0);
v_isShared_1593_ = v_isSharedCheck_1599_;
goto v_resetjp_1591_;
}
v_resetjp_1591_:
{
lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1597_; 
v___x_1594_ = lean_obj_once(&l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__8, &l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__8_once, _init_l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__8);
v___x_1595_ = lean_string_append(v___x_1594_, v_a_1590_);
lean_dec(v_a_1590_);
if (v_isShared_1593_ == 0)
{
lean_ctor_set(v___x_1592_, 0, v___x_1595_);
v___x_1597_ = v___x_1592_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1598_; 
v_reuseFailAlloc_1598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1598_, 0, v___x_1595_);
v___x_1597_ = v_reuseFailAlloc_1598_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
return v___x_1597_;
}
}
}
else
{
if (lean_obj_tag(v___x_1589_) == 0)
{
lean_object* v_a_1600_; lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1607_; 
lean_dec(v_json_1587_);
v_a_1600_ = lean_ctor_get(v___x_1589_, 0);
v_isSharedCheck_1607_ = !lean_is_exclusive(v___x_1589_);
if (v_isSharedCheck_1607_ == 0)
{
v___x_1602_ = v___x_1589_;
v_isShared_1603_ = v_isSharedCheck_1607_;
goto v_resetjp_1601_;
}
else
{
lean_inc(v_a_1600_);
lean_dec(v___x_1589_);
v___x_1602_ = lean_box(0);
v_isShared_1603_ = v_isSharedCheck_1607_;
goto v_resetjp_1601_;
}
v_resetjp_1601_:
{
lean_object* v___x_1605_; 
if (v_isShared_1603_ == 0)
{
lean_ctor_set_tag(v___x_1602_, 0);
v___x_1605_ = v___x_1602_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v_a_1600_);
v___x_1605_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
return v___x_1605_;
}
}
}
else
{
lean_object* v_a_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; 
v_a_1608_ = lean_ctor_get(v___x_1589_, 0);
lean_inc(v_a_1608_);
lean_dec_ref_known(v___x_1589_, 1);
v___x_1609_ = ((lean_object*)(l_Lean_Lsp_CreateFile_instToJsonOptions_toJson___closed__1));
v___x_1610_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonChangeAnnotation_fromJson_spec__0(v_json_1587_, v___x_1609_);
if (lean_obj_tag(v___x_1610_) == 0)
{
lean_object* v_a_1611_; lean_object* v___x_1613_; uint8_t v_isShared_1614_; uint8_t v_isSharedCheck_1620_; 
lean_dec(v_a_1608_);
v_a_1611_ = lean_ctor_get(v___x_1610_, 0);
v_isSharedCheck_1620_ = !lean_is_exclusive(v___x_1610_);
if (v_isSharedCheck_1620_ == 0)
{
v___x_1613_ = v___x_1610_;
v_isShared_1614_ = v_isSharedCheck_1620_;
goto v_resetjp_1612_;
}
else
{
lean_inc(v_a_1611_);
lean_dec(v___x_1610_);
v___x_1613_ = lean_box(0);
v_isShared_1614_ = v_isSharedCheck_1620_;
goto v_resetjp_1612_;
}
v_resetjp_1612_:
{
lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1618_; 
v___x_1615_ = lean_obj_once(&l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__12, &l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__12_once, _init_l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__12);
v___x_1616_ = lean_string_append(v___x_1615_, v_a_1611_);
lean_dec(v_a_1611_);
if (v_isShared_1614_ == 0)
{
lean_ctor_set(v___x_1613_, 0, v___x_1616_);
v___x_1618_ = v___x_1613_;
goto v_reusejp_1617_;
}
else
{
lean_object* v_reuseFailAlloc_1619_; 
v_reuseFailAlloc_1619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1619_, 0, v___x_1616_);
v___x_1618_ = v_reuseFailAlloc_1619_;
goto v_reusejp_1617_;
}
v_reusejp_1617_:
{
return v___x_1618_;
}
}
}
else
{
if (lean_obj_tag(v___x_1610_) == 0)
{
lean_object* v_a_1621_; lean_object* v___x_1623_; uint8_t v_isShared_1624_; uint8_t v_isSharedCheck_1628_; 
lean_dec(v_a_1608_);
v_a_1621_ = lean_ctor_get(v___x_1610_, 0);
v_isSharedCheck_1628_ = !lean_is_exclusive(v___x_1610_);
if (v_isSharedCheck_1628_ == 0)
{
v___x_1623_ = v___x_1610_;
v_isShared_1624_ = v_isSharedCheck_1628_;
goto v_resetjp_1622_;
}
else
{
lean_inc(v_a_1621_);
lean_dec(v___x_1610_);
v___x_1623_ = lean_box(0);
v_isShared_1624_ = v_isSharedCheck_1628_;
goto v_resetjp_1622_;
}
v_resetjp_1622_:
{
lean_object* v___x_1626_; 
if (v_isShared_1624_ == 0)
{
lean_ctor_set_tag(v___x_1623_, 0);
v___x_1626_ = v___x_1623_;
goto v_reusejp_1625_;
}
else
{
lean_object* v_reuseFailAlloc_1627_; 
v_reuseFailAlloc_1627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1627_, 0, v_a_1621_);
v___x_1626_ = v_reuseFailAlloc_1627_;
goto v_reusejp_1625_;
}
v_reusejp_1625_:
{
return v___x_1626_;
}
}
}
else
{
lean_object* v_a_1629_; lean_object* v___x_1631_; uint8_t v_isShared_1632_; uint8_t v_isSharedCheck_1639_; 
v_a_1629_ = lean_ctor_get(v___x_1610_, 0);
v_isSharedCheck_1639_ = !lean_is_exclusive(v___x_1610_);
if (v_isSharedCheck_1639_ == 0)
{
v___x_1631_ = v___x_1610_;
v_isShared_1632_ = v_isSharedCheck_1639_;
goto v_resetjp_1630_;
}
else
{
lean_inc(v_a_1629_);
lean_dec(v___x_1610_);
v___x_1631_ = lean_box(0);
v_isShared_1632_ = v_isSharedCheck_1639_;
goto v_resetjp_1630_;
}
v_resetjp_1630_:
{
lean_object* v___x_1633_; uint8_t v___x_1634_; uint8_t v___x_1635_; lean_object* v___x_1637_; 
v___x_1633_ = lean_alloc_ctor(0, 0, 2);
v___x_1634_ = lean_unbox(v_a_1608_);
lean_dec(v_a_1608_);
lean_ctor_set_uint8(v___x_1633_, 0, v___x_1634_);
v___x_1635_ = lean_unbox(v_a_1629_);
lean_dec(v_a_1629_);
lean_ctor_set_uint8(v___x_1633_, 1, v___x_1635_);
if (v_isShared_1632_ == 0)
{
lean_ctor_set(v___x_1631_, 0, v___x_1633_);
v___x_1637_ = v___x_1631_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v___x_1633_);
v___x_1637_ = v_reuseFailAlloc_1638_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
return v___x_1637_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DeleteFile_instToJsonOptions_toJson(lean_object* v_x_1644_){
_start:
{
uint8_t v_recursive_1645_; uint8_t v_ignoreIfNotExists_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; 
v_recursive_1645_ = lean_ctor_get_uint8(v_x_1644_, 0);
v_ignoreIfNotExists_1646_ = lean_ctor_get_uint8(v_x_1644_, 1);
v___x_1647_ = ((lean_object*)(l_Lean_Lsp_DeleteFile_instToJsonOptions_toJson___closed__0));
v___x_1648_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1648_, 0, v_recursive_1645_);
v___x_1649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1649_, 0, v___x_1647_);
lean_ctor_set(v___x_1649_, 1, v___x_1648_);
v___x_1650_ = lean_box(0);
v___x_1651_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1651_, 0, v___x_1649_);
lean_ctor_set(v___x_1651_, 1, v___x_1650_);
v___x_1652_ = ((lean_object*)(l_Lean_Lsp_DeleteFile_instToJsonOptions_toJson___closed__1));
v___x_1653_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1653_, 0, v_ignoreIfNotExists_1646_);
v___x_1654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1654_, 0, v___x_1652_);
lean_ctor_set(v___x_1654_, 1, v___x_1653_);
v___x_1655_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1655_, 0, v___x_1654_);
lean_ctor_set(v___x_1655_, 1, v___x_1650_);
v___x_1656_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1656_, 0, v___x_1655_);
lean_ctor_set(v___x_1656_, 1, v___x_1650_);
v___x_1657_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1657_, 0, v___x_1651_);
lean_ctor_set(v___x_1657_, 1, v___x_1656_);
v___x_1658_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__2));
v___x_1659_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLocation_toJson_spec__0(v___x_1657_, v___x_1658_);
v___x_1660_ = l_Lean_Json_mkObj(v___x_1659_);
lean_dec(v___x_1659_);
return v___x_1660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DeleteFile_instToJsonOptions_toJson___boxed(lean_object* v_x_1661_){
_start:
{
lean_object* v_res_1662_; 
v_res_1662_ = l_Lean_Lsp_DeleteFile_instToJsonOptions_toJson(v_x_1661_);
lean_dec_ref(v_x_1661_);
return v_res_1662_;
}
}
static lean_object* _init_l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__2(void){
_start:
{
uint8_t v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; 
v___x_1671_ = 1;
v___x_1672_ = ((lean_object*)(l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__1));
v___x_1673_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1672_, v___x_1671_);
return v___x_1673_;
}
}
static lean_object* _init_l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__3(void){
_start:
{
lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; 
v___x_1674_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__5));
v___x_1675_ = lean_obj_once(&l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__2, &l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__2_once, _init_l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__2);
v___x_1676_ = lean_string_append(v___x_1675_, v___x_1674_);
return v___x_1676_;
}
}
static lean_object* _init_l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__5(void){
_start:
{
uint8_t v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; 
v___x_1679_ = 1;
v___x_1680_ = ((lean_object*)(l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__4));
v___x_1681_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1680_, v___x_1679_);
return v___x_1681_;
}
}
static lean_object* _init_l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__6(void){
_start:
{
lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; 
v___x_1682_ = lean_obj_once(&l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__5, &l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__5_once, _init_l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__5);
v___x_1683_ = lean_obj_once(&l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__3, &l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__3_once, _init_l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__3);
v___x_1684_ = lean_string_append(v___x_1683_, v___x_1682_);
return v___x_1684_;
}
}
static lean_object* _init_l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__7(void){
_start:
{
lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; 
v___x_1685_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_1686_ = lean_obj_once(&l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__6, &l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__6_once, _init_l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__6);
v___x_1687_ = lean_string_append(v___x_1686_, v___x_1685_);
return v___x_1687_;
}
}
static lean_object* _init_l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__9(void){
_start:
{
uint8_t v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; 
v___x_1690_ = 1;
v___x_1691_ = ((lean_object*)(l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__8));
v___x_1692_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1691_, v___x_1690_);
return v___x_1692_;
}
}
static lean_object* _init_l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__10(void){
_start:
{
lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; 
v___x_1693_ = lean_obj_once(&l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__9, &l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__9_once, _init_l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__9);
v___x_1694_ = lean_obj_once(&l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__3, &l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__3_once, _init_l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__3);
v___x_1695_ = lean_string_append(v___x_1694_, v___x_1693_);
return v___x_1695_;
}
}
static lean_object* _init_l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__11(void){
_start:
{
lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; 
v___x_1696_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_1697_ = lean_obj_once(&l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__10, &l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__10_once, _init_l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__10);
v___x_1698_ = lean_string_append(v___x_1697_, v___x_1696_);
return v___x_1698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson(lean_object* v_json_1699_){
_start:
{
lean_object* v___x_1700_; lean_object* v___x_1701_; 
v___x_1700_ = ((lean_object*)(l_Lean_Lsp_DeleteFile_instToJsonOptions_toJson___closed__0));
lean_inc(v_json_1699_);
v___x_1701_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonChangeAnnotation_fromJson_spec__0(v_json_1699_, v___x_1700_);
if (lean_obj_tag(v___x_1701_) == 0)
{
lean_object* v_a_1702_; lean_object* v___x_1704_; uint8_t v_isShared_1705_; uint8_t v_isSharedCheck_1711_; 
lean_dec(v_json_1699_);
v_a_1702_ = lean_ctor_get(v___x_1701_, 0);
v_isSharedCheck_1711_ = !lean_is_exclusive(v___x_1701_);
if (v_isSharedCheck_1711_ == 0)
{
v___x_1704_ = v___x_1701_;
v_isShared_1705_ = v_isSharedCheck_1711_;
goto v_resetjp_1703_;
}
else
{
lean_inc(v_a_1702_);
lean_dec(v___x_1701_);
v___x_1704_ = lean_box(0);
v_isShared_1705_ = v_isSharedCheck_1711_;
goto v_resetjp_1703_;
}
v_resetjp_1703_:
{
lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1709_; 
v___x_1706_ = lean_obj_once(&l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__7, &l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__7_once, _init_l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__7);
v___x_1707_ = lean_string_append(v___x_1706_, v_a_1702_);
lean_dec(v_a_1702_);
if (v_isShared_1705_ == 0)
{
lean_ctor_set(v___x_1704_, 0, v___x_1707_);
v___x_1709_ = v___x_1704_;
goto v_reusejp_1708_;
}
else
{
lean_object* v_reuseFailAlloc_1710_; 
v_reuseFailAlloc_1710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1710_, 0, v___x_1707_);
v___x_1709_ = v_reuseFailAlloc_1710_;
goto v_reusejp_1708_;
}
v_reusejp_1708_:
{
return v___x_1709_;
}
}
}
else
{
if (lean_obj_tag(v___x_1701_) == 0)
{
lean_object* v_a_1712_; lean_object* v___x_1714_; uint8_t v_isShared_1715_; uint8_t v_isSharedCheck_1719_; 
lean_dec(v_json_1699_);
v_a_1712_ = lean_ctor_get(v___x_1701_, 0);
v_isSharedCheck_1719_ = !lean_is_exclusive(v___x_1701_);
if (v_isSharedCheck_1719_ == 0)
{
v___x_1714_ = v___x_1701_;
v_isShared_1715_ = v_isSharedCheck_1719_;
goto v_resetjp_1713_;
}
else
{
lean_inc(v_a_1712_);
lean_dec(v___x_1701_);
v___x_1714_ = lean_box(0);
v_isShared_1715_ = v_isSharedCheck_1719_;
goto v_resetjp_1713_;
}
v_resetjp_1713_:
{
lean_object* v___x_1717_; 
if (v_isShared_1715_ == 0)
{
lean_ctor_set_tag(v___x_1714_, 0);
v___x_1717_ = v___x_1714_;
goto v_reusejp_1716_;
}
else
{
lean_object* v_reuseFailAlloc_1718_; 
v_reuseFailAlloc_1718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1718_, 0, v_a_1712_);
v___x_1717_ = v_reuseFailAlloc_1718_;
goto v_reusejp_1716_;
}
v_reusejp_1716_:
{
return v___x_1717_;
}
}
}
else
{
lean_object* v_a_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; 
v_a_1720_ = lean_ctor_get(v___x_1701_, 0);
lean_inc(v_a_1720_);
lean_dec_ref_known(v___x_1701_, 1);
v___x_1721_ = ((lean_object*)(l_Lean_Lsp_DeleteFile_instToJsonOptions_toJson___closed__1));
v___x_1722_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonChangeAnnotation_fromJson_spec__0(v_json_1699_, v___x_1721_);
if (lean_obj_tag(v___x_1722_) == 0)
{
lean_object* v_a_1723_; lean_object* v___x_1725_; uint8_t v_isShared_1726_; uint8_t v_isSharedCheck_1732_; 
lean_dec(v_a_1720_);
v_a_1723_ = lean_ctor_get(v___x_1722_, 0);
v_isSharedCheck_1732_ = !lean_is_exclusive(v___x_1722_);
if (v_isSharedCheck_1732_ == 0)
{
v___x_1725_ = v___x_1722_;
v_isShared_1726_ = v_isSharedCheck_1732_;
goto v_resetjp_1724_;
}
else
{
lean_inc(v_a_1723_);
lean_dec(v___x_1722_);
v___x_1725_ = lean_box(0);
v_isShared_1726_ = v_isSharedCheck_1732_;
goto v_resetjp_1724_;
}
v_resetjp_1724_:
{
lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1730_; 
v___x_1727_ = lean_obj_once(&l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__11, &l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__11_once, _init_l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__11);
v___x_1728_ = lean_string_append(v___x_1727_, v_a_1723_);
lean_dec(v_a_1723_);
if (v_isShared_1726_ == 0)
{
lean_ctor_set(v___x_1725_, 0, v___x_1728_);
v___x_1730_ = v___x_1725_;
goto v_reusejp_1729_;
}
else
{
lean_object* v_reuseFailAlloc_1731_; 
v_reuseFailAlloc_1731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1731_, 0, v___x_1728_);
v___x_1730_ = v_reuseFailAlloc_1731_;
goto v_reusejp_1729_;
}
v_reusejp_1729_:
{
return v___x_1730_;
}
}
}
else
{
if (lean_obj_tag(v___x_1722_) == 0)
{
lean_object* v_a_1733_; lean_object* v___x_1735_; uint8_t v_isShared_1736_; uint8_t v_isSharedCheck_1740_; 
lean_dec(v_a_1720_);
v_a_1733_ = lean_ctor_get(v___x_1722_, 0);
v_isSharedCheck_1740_ = !lean_is_exclusive(v___x_1722_);
if (v_isSharedCheck_1740_ == 0)
{
v___x_1735_ = v___x_1722_;
v_isShared_1736_ = v_isSharedCheck_1740_;
goto v_resetjp_1734_;
}
else
{
lean_inc(v_a_1733_);
lean_dec(v___x_1722_);
v___x_1735_ = lean_box(0);
v_isShared_1736_ = v_isSharedCheck_1740_;
goto v_resetjp_1734_;
}
v_resetjp_1734_:
{
lean_object* v___x_1738_; 
if (v_isShared_1736_ == 0)
{
lean_ctor_set_tag(v___x_1735_, 0);
v___x_1738_ = v___x_1735_;
goto v_reusejp_1737_;
}
else
{
lean_object* v_reuseFailAlloc_1739_; 
v_reuseFailAlloc_1739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1739_, 0, v_a_1733_);
v___x_1738_ = v_reuseFailAlloc_1739_;
goto v_reusejp_1737_;
}
v_reusejp_1737_:
{
return v___x_1738_;
}
}
}
else
{
lean_object* v_a_1741_; lean_object* v___x_1743_; uint8_t v_isShared_1744_; uint8_t v_isSharedCheck_1751_; 
v_a_1741_ = lean_ctor_get(v___x_1722_, 0);
v_isSharedCheck_1751_ = !lean_is_exclusive(v___x_1722_);
if (v_isSharedCheck_1751_ == 0)
{
v___x_1743_ = v___x_1722_;
v_isShared_1744_ = v_isSharedCheck_1751_;
goto v_resetjp_1742_;
}
else
{
lean_inc(v_a_1741_);
lean_dec(v___x_1722_);
v___x_1743_ = lean_box(0);
v_isShared_1744_ = v_isSharedCheck_1751_;
goto v_resetjp_1742_;
}
v_resetjp_1742_:
{
lean_object* v___x_1745_; uint8_t v___x_1746_; uint8_t v___x_1747_; lean_object* v___x_1749_; 
v___x_1745_ = lean_alloc_ctor(0, 0, 2);
v___x_1746_ = lean_unbox(v_a_1720_);
lean_dec(v_a_1720_);
lean_ctor_set_uint8(v___x_1745_, 0, v___x_1746_);
v___x_1747_ = lean_unbox(v_a_1741_);
lean_dec(v_a_1741_);
lean_ctor_set_uint8(v___x_1745_, 1, v___x_1747_);
if (v_isShared_1744_ == 0)
{
lean_ctor_set(v___x_1743_, 0, v___x_1745_);
v___x_1749_ = v___x_1743_;
goto v_reusejp_1748_;
}
else
{
lean_object* v_reuseFailAlloc_1750_; 
v_reuseFailAlloc_1750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1750_, 0, v___x_1745_);
v___x_1749_ = v_reuseFailAlloc_1750_;
goto v_reusejp_1748_;
}
v_reusejp_1748_:
{
return v___x_1749_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonCreateFile_toJson_spec__0(lean_object* v_k_1754_, lean_object* v_x_1755_){
_start:
{
if (lean_obj_tag(v_x_1755_) == 0)
{
lean_object* v___x_1756_; 
lean_dec_ref(v_k_1754_);
v___x_1756_ = lean_box(0);
return v___x_1756_;
}
else
{
lean_object* v_val_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; 
v_val_1757_ = lean_ctor_get(v_x_1755_, 0);
v___x_1758_ = l_Lean_Lsp_CreateFile_instToJsonOptions_toJson(v_val_1757_);
v___x_1759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1759_, 0, v_k_1754_);
lean_ctor_set(v___x_1759_, 1, v___x_1758_);
v___x_1760_ = lean_box(0);
v___x_1761_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1761_, 0, v___x_1759_);
lean_ctor_set(v___x_1761_, 1, v___x_1760_);
return v___x_1761_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonCreateFile_toJson_spec__0___boxed(lean_object* v_k_1762_, lean_object* v_x_1763_){
_start:
{
lean_object* v_res_1764_; 
v_res_1764_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonCreateFile_toJson_spec__0(v_k_1762_, v_x_1763_);
lean_dec(v_x_1763_);
return v_res_1764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonCreateFile_toJson(lean_object* v_x_1766_){
_start:
{
lean_object* v_uri_1767_; lean_object* v_options_x3f_1768_; lean_object* v_annotationId_x3f_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; 
v_uri_1767_ = lean_ctor_get(v_x_1766_, 0);
lean_inc_ref(v_uri_1767_);
v_options_x3f_1768_ = lean_ctor_get(v_x_1766_, 1);
lean_inc(v_options_x3f_1768_);
v_annotationId_x3f_1769_ = lean_ctor_get(v_x_1766_, 2);
lean_inc(v_annotationId_x3f_1769_);
lean_dec_ref(v_x_1766_);
v___x_1770_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__0));
v___x_1771_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1771_, 0, v_uri_1767_);
v___x_1772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1772_, 0, v___x_1770_);
lean_ctor_set(v___x_1772_, 1, v___x_1771_);
v___x_1773_ = lean_box(0);
v___x_1774_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1774_, 0, v___x_1772_);
lean_ctor_set(v___x_1774_, 1, v___x_1773_);
v___x_1775_ = ((lean_object*)(l_Lean_Lsp_instToJsonCreateFile_toJson___closed__0));
v___x_1776_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonCreateFile_toJson_spec__0(v___x_1775_, v_options_x3f_1768_);
lean_dec(v_options_x3f_1768_);
v___x_1777_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextEdit_toJson___closed__2));
v___x_1778_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextEdit_toJson_spec__1(v___x_1777_, v_annotationId_x3f_1769_);
v___x_1779_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1779_, 0, v___x_1778_);
lean_ctor_set(v___x_1779_, 1, v___x_1773_);
v___x_1780_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1780_, 0, v___x_1776_);
lean_ctor_set(v___x_1780_, 1, v___x_1779_);
v___x_1781_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1781_, 0, v___x_1774_);
lean_ctor_set(v___x_1781_, 1, v___x_1780_);
v___x_1782_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__2));
v___x_1783_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLocation_toJson_spec__0(v___x_1781_, v___x_1782_);
v___x_1784_ = l_Lean_Json_mkObj(v___x_1783_);
lean_dec(v___x_1783_);
return v___x_1784_;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCreateFile_fromJson_spec__0_spec__0(lean_object* v_x_1789_){
_start:
{
if (lean_obj_tag(v_x_1789_) == 0)
{
lean_object* v___x_1790_; 
v___x_1790_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCreateFile_fromJson_spec__0_spec__0___closed__0));
return v___x_1790_;
}
else
{
lean_object* v___x_1791_; 
v___x_1791_ = l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson(v_x_1789_);
if (lean_obj_tag(v___x_1791_) == 0)
{
lean_object* v_a_1792_; lean_object* v___x_1794_; uint8_t v_isShared_1795_; uint8_t v_isSharedCheck_1799_; 
v_a_1792_ = lean_ctor_get(v___x_1791_, 0);
v_isSharedCheck_1799_ = !lean_is_exclusive(v___x_1791_);
if (v_isSharedCheck_1799_ == 0)
{
v___x_1794_ = v___x_1791_;
v_isShared_1795_ = v_isSharedCheck_1799_;
goto v_resetjp_1793_;
}
else
{
lean_inc(v_a_1792_);
lean_dec(v___x_1791_);
v___x_1794_ = lean_box(0);
v_isShared_1795_ = v_isSharedCheck_1799_;
goto v_resetjp_1793_;
}
v_resetjp_1793_:
{
lean_object* v___x_1797_; 
if (v_isShared_1795_ == 0)
{
v___x_1797_ = v___x_1794_;
goto v_reusejp_1796_;
}
else
{
lean_object* v_reuseFailAlloc_1798_; 
v_reuseFailAlloc_1798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1798_, 0, v_a_1792_);
v___x_1797_ = v_reuseFailAlloc_1798_;
goto v_reusejp_1796_;
}
v_reusejp_1796_:
{
return v___x_1797_;
}
}
}
else
{
lean_object* v_a_1800_; lean_object* v___x_1802_; uint8_t v_isShared_1803_; uint8_t v_isSharedCheck_1808_; 
v_a_1800_ = lean_ctor_get(v___x_1791_, 0);
v_isSharedCheck_1808_ = !lean_is_exclusive(v___x_1791_);
if (v_isSharedCheck_1808_ == 0)
{
v___x_1802_ = v___x_1791_;
v_isShared_1803_ = v_isSharedCheck_1808_;
goto v_resetjp_1801_;
}
else
{
lean_inc(v_a_1800_);
lean_dec(v___x_1791_);
v___x_1802_ = lean_box(0);
v_isShared_1803_ = v_isSharedCheck_1808_;
goto v_resetjp_1801_;
}
v_resetjp_1801_:
{
lean_object* v___x_1804_; lean_object* v___x_1806_; 
v___x_1804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1804_, 0, v_a_1800_);
if (v_isShared_1803_ == 0)
{
lean_ctor_set(v___x_1802_, 0, v___x_1804_);
v___x_1806_ = v___x_1802_;
goto v_reusejp_1805_;
}
else
{
lean_object* v_reuseFailAlloc_1807_; 
v_reuseFailAlloc_1807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1807_, 0, v___x_1804_);
v___x_1806_ = v_reuseFailAlloc_1807_;
goto v_reusejp_1805_;
}
v_reusejp_1805_:
{
return v___x_1806_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCreateFile_fromJson_spec__0(lean_object* v_j_1809_, lean_object* v_k_1810_){
_start:
{
lean_object* v___x_1811_; lean_object* v___x_1812_; 
v___x_1811_ = l_Lean_Json_getObjValD(v_j_1809_, v_k_1810_);
v___x_1812_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCreateFile_fromJson_spec__0_spec__0(v___x_1811_);
return v___x_1812_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCreateFile_fromJson_spec__0___boxed(lean_object* v_j_1813_, lean_object* v_k_1814_){
_start:
{
lean_object* v_res_1815_; 
v_res_1815_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCreateFile_fromJson_spec__0(v_j_1813_, v_k_1814_);
lean_dec_ref(v_k_1814_);
return v_res_1815_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__1(void){
_start:
{
uint8_t v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; 
v___x_1820_ = 1;
v___x_1821_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__0));
v___x_1822_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1821_, v___x_1820_);
return v___x_1822_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__2(void){
_start:
{
lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; 
v___x_1823_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__5));
v___x_1824_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__1, &l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__1_once, _init_l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__1);
v___x_1825_ = lean_string_append(v___x_1824_, v___x_1823_);
return v___x_1825_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__3(void){
_start:
{
lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; 
v___x_1826_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLocation_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLocation_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLocation_fromJson___closed__8);
v___x_1827_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__2, &l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__2);
v___x_1828_ = lean_string_append(v___x_1827_, v___x_1826_);
return v___x_1828_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__4(void){
_start:
{
lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; 
v___x_1829_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_1830_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__3, &l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__3);
v___x_1831_ = lean_string_append(v___x_1830_, v___x_1829_);
return v___x_1831_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__7(void){
_start:
{
uint8_t v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; 
v___x_1835_ = 1;
v___x_1836_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__6));
v___x_1837_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1836_, v___x_1835_);
return v___x_1837_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__8(void){
_start:
{
lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; 
v___x_1838_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__7, &l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__7);
v___x_1839_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__2, &l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__2);
v___x_1840_ = lean_string_append(v___x_1839_, v___x_1838_);
return v___x_1840_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__9(void){
_start:
{
lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; 
v___x_1841_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_1842_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__8, &l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__8);
v___x_1843_ = lean_string_append(v___x_1842_, v___x_1841_);
return v___x_1843_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__10(void){
_start:
{
lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; 
v___x_1844_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__17, &l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__17_once, _init_l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__17);
v___x_1845_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__2, &l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__2);
v___x_1846_ = lean_string_append(v___x_1845_, v___x_1844_);
return v___x_1846_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__11(void){
_start:
{
lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; 
v___x_1847_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_1848_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__10, &l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__10);
v___x_1849_ = lean_string_append(v___x_1848_, v___x_1847_);
return v___x_1849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonCreateFile_fromJson(lean_object* v_json_1850_){
_start:
{
lean_object* v___x_1851_; lean_object* v___x_1852_; 
v___x_1851_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__0));
lean_inc(v_json_1850_);
v___x_1852_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocation_fromJson_spec__0(v_json_1850_, v___x_1851_);
if (lean_obj_tag(v___x_1852_) == 0)
{
lean_object* v_a_1853_; lean_object* v___x_1855_; uint8_t v_isShared_1856_; uint8_t v_isSharedCheck_1862_; 
lean_dec(v_json_1850_);
v_a_1853_ = lean_ctor_get(v___x_1852_, 0);
v_isSharedCheck_1862_ = !lean_is_exclusive(v___x_1852_);
if (v_isSharedCheck_1862_ == 0)
{
v___x_1855_ = v___x_1852_;
v_isShared_1856_ = v_isSharedCheck_1862_;
goto v_resetjp_1854_;
}
else
{
lean_inc(v_a_1853_);
lean_dec(v___x_1852_);
v___x_1855_ = lean_box(0);
v_isShared_1856_ = v_isSharedCheck_1862_;
goto v_resetjp_1854_;
}
v_resetjp_1854_:
{
lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1860_; 
v___x_1857_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__4, &l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__4);
v___x_1858_ = lean_string_append(v___x_1857_, v_a_1853_);
lean_dec(v_a_1853_);
if (v_isShared_1856_ == 0)
{
lean_ctor_set(v___x_1855_, 0, v___x_1858_);
v___x_1860_ = v___x_1855_;
goto v_reusejp_1859_;
}
else
{
lean_object* v_reuseFailAlloc_1861_; 
v_reuseFailAlloc_1861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1861_, 0, v___x_1858_);
v___x_1860_ = v_reuseFailAlloc_1861_;
goto v_reusejp_1859_;
}
v_reusejp_1859_:
{
return v___x_1860_;
}
}
}
else
{
if (lean_obj_tag(v___x_1852_) == 0)
{
lean_object* v_a_1863_; lean_object* v___x_1865_; uint8_t v_isShared_1866_; uint8_t v_isSharedCheck_1870_; 
lean_dec(v_json_1850_);
v_a_1863_ = lean_ctor_get(v___x_1852_, 0);
v_isSharedCheck_1870_ = !lean_is_exclusive(v___x_1852_);
if (v_isSharedCheck_1870_ == 0)
{
v___x_1865_ = v___x_1852_;
v_isShared_1866_ = v_isSharedCheck_1870_;
goto v_resetjp_1864_;
}
else
{
lean_inc(v_a_1863_);
lean_dec(v___x_1852_);
v___x_1865_ = lean_box(0);
v_isShared_1866_ = v_isSharedCheck_1870_;
goto v_resetjp_1864_;
}
v_resetjp_1864_:
{
lean_object* v___x_1868_; 
if (v_isShared_1866_ == 0)
{
lean_ctor_set_tag(v___x_1865_, 0);
v___x_1868_ = v___x_1865_;
goto v_reusejp_1867_;
}
else
{
lean_object* v_reuseFailAlloc_1869_; 
v_reuseFailAlloc_1869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1869_, 0, v_a_1863_);
v___x_1868_ = v_reuseFailAlloc_1869_;
goto v_reusejp_1867_;
}
v_reusejp_1867_:
{
return v___x_1868_;
}
}
}
else
{
lean_object* v_a_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; 
v_a_1871_ = lean_ctor_get(v___x_1852_, 0);
lean_inc(v_a_1871_);
lean_dec_ref_known(v___x_1852_, 1);
v___x_1872_ = ((lean_object*)(l_Lean_Lsp_instToJsonCreateFile_toJson___closed__0));
lean_inc(v_json_1850_);
v___x_1873_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCreateFile_fromJson_spec__0(v_json_1850_, v___x_1872_);
if (lean_obj_tag(v___x_1873_) == 0)
{
lean_object* v_a_1874_; lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1883_; 
lean_dec(v_a_1871_);
lean_dec(v_json_1850_);
v_a_1874_ = lean_ctor_get(v___x_1873_, 0);
v_isSharedCheck_1883_ = !lean_is_exclusive(v___x_1873_);
if (v_isSharedCheck_1883_ == 0)
{
v___x_1876_ = v___x_1873_;
v_isShared_1877_ = v_isSharedCheck_1883_;
goto v_resetjp_1875_;
}
else
{
lean_inc(v_a_1874_);
lean_dec(v___x_1873_);
v___x_1876_ = lean_box(0);
v_isShared_1877_ = v_isSharedCheck_1883_;
goto v_resetjp_1875_;
}
v_resetjp_1875_:
{
lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1881_; 
v___x_1878_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__9, &l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__9);
v___x_1879_ = lean_string_append(v___x_1878_, v_a_1874_);
lean_dec(v_a_1874_);
if (v_isShared_1877_ == 0)
{
lean_ctor_set(v___x_1876_, 0, v___x_1879_);
v___x_1881_ = v___x_1876_;
goto v_reusejp_1880_;
}
else
{
lean_object* v_reuseFailAlloc_1882_; 
v_reuseFailAlloc_1882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1882_, 0, v___x_1879_);
v___x_1881_ = v_reuseFailAlloc_1882_;
goto v_reusejp_1880_;
}
v_reusejp_1880_:
{
return v___x_1881_;
}
}
}
else
{
if (lean_obj_tag(v___x_1873_) == 0)
{
lean_object* v_a_1884_; lean_object* v___x_1886_; uint8_t v_isShared_1887_; uint8_t v_isSharedCheck_1891_; 
lean_dec(v_a_1871_);
lean_dec(v_json_1850_);
v_a_1884_ = lean_ctor_get(v___x_1873_, 0);
v_isSharedCheck_1891_ = !lean_is_exclusive(v___x_1873_);
if (v_isSharedCheck_1891_ == 0)
{
v___x_1886_ = v___x_1873_;
v_isShared_1887_ = v_isSharedCheck_1891_;
goto v_resetjp_1885_;
}
else
{
lean_inc(v_a_1884_);
lean_dec(v___x_1873_);
v___x_1886_ = lean_box(0);
v_isShared_1887_ = v_isSharedCheck_1891_;
goto v_resetjp_1885_;
}
v_resetjp_1885_:
{
lean_object* v___x_1889_; 
if (v_isShared_1887_ == 0)
{
lean_ctor_set_tag(v___x_1886_, 0);
v___x_1889_ = v___x_1886_;
goto v_reusejp_1888_;
}
else
{
lean_object* v_reuseFailAlloc_1890_; 
v_reuseFailAlloc_1890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1890_, 0, v_a_1884_);
v___x_1889_ = v_reuseFailAlloc_1890_;
goto v_reusejp_1888_;
}
v_reusejp_1888_:
{
return v___x_1889_;
}
}
}
else
{
lean_object* v_a_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; 
v_a_1892_ = lean_ctor_get(v___x_1873_, 0);
lean_inc(v_a_1892_);
lean_dec_ref_known(v___x_1873_, 1);
v___x_1893_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextEdit_toJson___closed__2));
v___x_1894_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextEdit_fromJson_spec__1(v_json_1850_, v___x_1893_);
if (lean_obj_tag(v___x_1894_) == 0)
{
lean_object* v_a_1895_; lean_object* v___x_1897_; uint8_t v_isShared_1898_; uint8_t v_isSharedCheck_1904_; 
lean_dec(v_a_1892_);
lean_dec(v_a_1871_);
v_a_1895_ = lean_ctor_get(v___x_1894_, 0);
v_isSharedCheck_1904_ = !lean_is_exclusive(v___x_1894_);
if (v_isSharedCheck_1904_ == 0)
{
v___x_1897_ = v___x_1894_;
v_isShared_1898_ = v_isSharedCheck_1904_;
goto v_resetjp_1896_;
}
else
{
lean_inc(v_a_1895_);
lean_dec(v___x_1894_);
v___x_1897_ = lean_box(0);
v_isShared_1898_ = v_isSharedCheck_1904_;
goto v_resetjp_1896_;
}
v_resetjp_1896_:
{
lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1902_; 
v___x_1899_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__11, &l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__11);
v___x_1900_ = lean_string_append(v___x_1899_, v_a_1895_);
lean_dec(v_a_1895_);
if (v_isShared_1898_ == 0)
{
lean_ctor_set(v___x_1897_, 0, v___x_1900_);
v___x_1902_ = v___x_1897_;
goto v_reusejp_1901_;
}
else
{
lean_object* v_reuseFailAlloc_1903_; 
v_reuseFailAlloc_1903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1903_, 0, v___x_1900_);
v___x_1902_ = v_reuseFailAlloc_1903_;
goto v_reusejp_1901_;
}
v_reusejp_1901_:
{
return v___x_1902_;
}
}
}
else
{
if (lean_obj_tag(v___x_1894_) == 0)
{
lean_object* v_a_1905_; lean_object* v___x_1907_; uint8_t v_isShared_1908_; uint8_t v_isSharedCheck_1912_; 
lean_dec(v_a_1892_);
lean_dec(v_a_1871_);
v_a_1905_ = lean_ctor_get(v___x_1894_, 0);
v_isSharedCheck_1912_ = !lean_is_exclusive(v___x_1894_);
if (v_isSharedCheck_1912_ == 0)
{
v___x_1907_ = v___x_1894_;
v_isShared_1908_ = v_isSharedCheck_1912_;
goto v_resetjp_1906_;
}
else
{
lean_inc(v_a_1905_);
lean_dec(v___x_1894_);
v___x_1907_ = lean_box(0);
v_isShared_1908_ = v_isSharedCheck_1912_;
goto v_resetjp_1906_;
}
v_resetjp_1906_:
{
lean_object* v___x_1910_; 
if (v_isShared_1908_ == 0)
{
lean_ctor_set_tag(v___x_1907_, 0);
v___x_1910_ = v___x_1907_;
goto v_reusejp_1909_;
}
else
{
lean_object* v_reuseFailAlloc_1911_; 
v_reuseFailAlloc_1911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1911_, 0, v_a_1905_);
v___x_1910_ = v_reuseFailAlloc_1911_;
goto v_reusejp_1909_;
}
v_reusejp_1909_:
{
return v___x_1910_;
}
}
}
else
{
lean_object* v_a_1913_; lean_object* v___x_1915_; uint8_t v_isShared_1916_; uint8_t v_isSharedCheck_1921_; 
v_a_1913_ = lean_ctor_get(v___x_1894_, 0);
v_isSharedCheck_1921_ = !lean_is_exclusive(v___x_1894_);
if (v_isSharedCheck_1921_ == 0)
{
v___x_1915_ = v___x_1894_;
v_isShared_1916_ = v_isSharedCheck_1921_;
goto v_resetjp_1914_;
}
else
{
lean_inc(v_a_1913_);
lean_dec(v___x_1894_);
v___x_1915_ = lean_box(0);
v_isShared_1916_ = v_isSharedCheck_1921_;
goto v_resetjp_1914_;
}
v_resetjp_1914_:
{
lean_object* v___x_1917_; lean_object* v___x_1919_; 
v___x_1917_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1917_, 0, v_a_1871_);
lean_ctor_set(v___x_1917_, 1, v_a_1892_);
lean_ctor_set(v___x_1917_, 2, v_a_1913_);
if (v_isShared_1916_ == 0)
{
lean_ctor_set(v___x_1915_, 0, v___x_1917_);
v___x_1919_ = v___x_1915_;
goto v_reusejp_1918_;
}
else
{
lean_object* v_reuseFailAlloc_1920_; 
v_reuseFailAlloc_1920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1920_, 0, v___x_1917_);
v___x_1919_ = v_reuseFailAlloc_1920_;
goto v_reusejp_1918_;
}
v_reusejp_1918_:
{
return v___x_1919_;
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
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRenameFile_toJson(lean_object* v_x_1926_){
_start:
{
lean_object* v_oldUri_1927_; lean_object* v_newUri_1928_; lean_object* v_options_x3f_1929_; lean_object* v_annotationId_x3f_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; 
v_oldUri_1927_ = lean_ctor_get(v_x_1926_, 0);
lean_inc_ref(v_oldUri_1927_);
v_newUri_1928_ = lean_ctor_get(v_x_1926_, 1);
lean_inc_ref(v_newUri_1928_);
v_options_x3f_1929_ = lean_ctor_get(v_x_1926_, 2);
lean_inc(v_options_x3f_1929_);
v_annotationId_x3f_1930_ = lean_ctor_get(v_x_1926_, 3);
lean_inc(v_annotationId_x3f_1930_);
lean_dec_ref(v_x_1926_);
v___x_1931_ = ((lean_object*)(l_Lean_Lsp_instToJsonRenameFile_toJson___closed__0));
v___x_1932_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1932_, 0, v_oldUri_1927_);
v___x_1933_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1933_, 0, v___x_1931_);
lean_ctor_set(v___x_1933_, 1, v___x_1932_);
v___x_1934_ = lean_box(0);
v___x_1935_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1935_, 0, v___x_1933_);
lean_ctor_set(v___x_1935_, 1, v___x_1934_);
v___x_1936_ = ((lean_object*)(l_Lean_Lsp_instToJsonRenameFile_toJson___closed__1));
v___x_1937_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1937_, 0, v_newUri_1928_);
v___x_1938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1938_, 0, v___x_1936_);
lean_ctor_set(v___x_1938_, 1, v___x_1937_);
v___x_1939_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1939_, 0, v___x_1938_);
lean_ctor_set(v___x_1939_, 1, v___x_1934_);
v___x_1940_ = ((lean_object*)(l_Lean_Lsp_instToJsonCreateFile_toJson___closed__0));
v___x_1941_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonCreateFile_toJson_spec__0(v___x_1940_, v_options_x3f_1929_);
lean_dec(v_options_x3f_1929_);
v___x_1942_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextEdit_toJson___closed__2));
v___x_1943_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextEdit_toJson_spec__1(v___x_1942_, v_annotationId_x3f_1930_);
v___x_1944_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1944_, 0, v___x_1943_);
lean_ctor_set(v___x_1944_, 1, v___x_1934_);
v___x_1945_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1945_, 0, v___x_1941_);
lean_ctor_set(v___x_1945_, 1, v___x_1944_);
v___x_1946_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1946_, 0, v___x_1939_);
lean_ctor_set(v___x_1946_, 1, v___x_1945_);
v___x_1947_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1947_, 0, v___x_1935_);
lean_ctor_set(v___x_1947_, 1, v___x_1946_);
v___x_1948_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__2));
v___x_1949_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLocation_toJson_spec__0(v___x_1947_, v___x_1948_);
v___x_1950_ = l_Lean_Json_mkObj(v___x_1949_);
lean_dec(v___x_1949_);
return v___x_1950_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__2(void){
_start:
{
uint8_t v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; 
v___x_1958_ = 1;
v___x_1959_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__1));
v___x_1960_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1959_, v___x_1958_);
return v___x_1960_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__3(void){
_start:
{
lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; 
v___x_1961_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__5));
v___x_1962_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__2, &l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__2);
v___x_1963_ = lean_string_append(v___x_1962_, v___x_1961_);
return v___x_1963_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__5(void){
_start:
{
uint8_t v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; 
v___x_1966_ = 1;
v___x_1967_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__4));
v___x_1968_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1967_, v___x_1966_);
return v___x_1968_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__6(void){
_start:
{
lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; 
v___x_1969_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__5, &l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__5);
v___x_1970_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__3, &l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__3);
v___x_1971_ = lean_string_append(v___x_1970_, v___x_1969_);
return v___x_1971_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__7(void){
_start:
{
lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; 
v___x_1972_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_1973_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__6, &l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__6);
v___x_1974_ = lean_string_append(v___x_1973_, v___x_1972_);
return v___x_1974_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__9(void){
_start:
{
uint8_t v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; 
v___x_1977_ = 1;
v___x_1978_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__8));
v___x_1979_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1978_, v___x_1977_);
return v___x_1979_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__10(void){
_start:
{
lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; 
v___x_1980_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__9, &l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__9);
v___x_1981_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__3, &l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__3);
v___x_1982_ = lean_string_append(v___x_1981_, v___x_1980_);
return v___x_1982_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__11(void){
_start:
{
lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; 
v___x_1983_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_1984_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__10, &l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__10);
v___x_1985_ = lean_string_append(v___x_1984_, v___x_1983_);
return v___x_1985_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__12(void){
_start:
{
lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; 
v___x_1986_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__7, &l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__7);
v___x_1987_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__3, &l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__3);
v___x_1988_ = lean_string_append(v___x_1987_, v___x_1986_);
return v___x_1988_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__13(void){
_start:
{
lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; 
v___x_1989_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_1990_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__12, &l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__12);
v___x_1991_ = lean_string_append(v___x_1990_, v___x_1989_);
return v___x_1991_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__14(void){
_start:
{
lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; 
v___x_1992_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__17, &l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__17_once, _init_l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__17);
v___x_1993_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__3, &l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__3);
v___x_1994_ = lean_string_append(v___x_1993_, v___x_1992_);
return v___x_1994_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__15(void){
_start:
{
lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; 
v___x_1995_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_1996_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__14, &l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__14_once, _init_l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__14);
v___x_1997_ = lean_string_append(v___x_1996_, v___x_1995_);
return v___x_1997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonRenameFile_fromJson(lean_object* v_json_1998_){
_start:
{
lean_object* v___x_1999_; lean_object* v___x_2000_; 
v___x_1999_ = ((lean_object*)(l_Lean_Lsp_instToJsonRenameFile_toJson___closed__0));
lean_inc(v_json_1998_);
v___x_2000_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocation_fromJson_spec__0(v_json_1998_, v___x_1999_);
if (lean_obj_tag(v___x_2000_) == 0)
{
lean_object* v_a_2001_; lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2010_; 
lean_dec(v_json_1998_);
v_a_2001_ = lean_ctor_get(v___x_2000_, 0);
v_isSharedCheck_2010_ = !lean_is_exclusive(v___x_2000_);
if (v_isSharedCheck_2010_ == 0)
{
v___x_2003_ = v___x_2000_;
v_isShared_2004_ = v_isSharedCheck_2010_;
goto v_resetjp_2002_;
}
else
{
lean_inc(v_a_2001_);
lean_dec(v___x_2000_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2010_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2008_; 
v___x_2005_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__7, &l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__7);
v___x_2006_ = lean_string_append(v___x_2005_, v_a_2001_);
lean_dec(v_a_2001_);
if (v_isShared_2004_ == 0)
{
lean_ctor_set(v___x_2003_, 0, v___x_2006_);
v___x_2008_ = v___x_2003_;
goto v_reusejp_2007_;
}
else
{
lean_object* v_reuseFailAlloc_2009_; 
v_reuseFailAlloc_2009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2009_, 0, v___x_2006_);
v___x_2008_ = v_reuseFailAlloc_2009_;
goto v_reusejp_2007_;
}
v_reusejp_2007_:
{
return v___x_2008_;
}
}
}
else
{
if (lean_obj_tag(v___x_2000_) == 0)
{
lean_object* v_a_2011_; lean_object* v___x_2013_; uint8_t v_isShared_2014_; uint8_t v_isSharedCheck_2018_; 
lean_dec(v_json_1998_);
v_a_2011_ = lean_ctor_get(v___x_2000_, 0);
v_isSharedCheck_2018_ = !lean_is_exclusive(v___x_2000_);
if (v_isSharedCheck_2018_ == 0)
{
v___x_2013_ = v___x_2000_;
v_isShared_2014_ = v_isSharedCheck_2018_;
goto v_resetjp_2012_;
}
else
{
lean_inc(v_a_2011_);
lean_dec(v___x_2000_);
v___x_2013_ = lean_box(0);
v_isShared_2014_ = v_isSharedCheck_2018_;
goto v_resetjp_2012_;
}
v_resetjp_2012_:
{
lean_object* v___x_2016_; 
if (v_isShared_2014_ == 0)
{
lean_ctor_set_tag(v___x_2013_, 0);
v___x_2016_ = v___x_2013_;
goto v_reusejp_2015_;
}
else
{
lean_object* v_reuseFailAlloc_2017_; 
v_reuseFailAlloc_2017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2017_, 0, v_a_2011_);
v___x_2016_ = v_reuseFailAlloc_2017_;
goto v_reusejp_2015_;
}
v_reusejp_2015_:
{
return v___x_2016_;
}
}
}
else
{
lean_object* v_a_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; 
v_a_2019_ = lean_ctor_get(v___x_2000_, 0);
lean_inc(v_a_2019_);
lean_dec_ref_known(v___x_2000_, 1);
v___x_2020_ = ((lean_object*)(l_Lean_Lsp_instToJsonRenameFile_toJson___closed__1));
lean_inc(v_json_1998_);
v___x_2021_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocation_fromJson_spec__0(v_json_1998_, v___x_2020_);
if (lean_obj_tag(v___x_2021_) == 0)
{
lean_object* v_a_2022_; lean_object* v___x_2024_; uint8_t v_isShared_2025_; uint8_t v_isSharedCheck_2031_; 
lean_dec(v_a_2019_);
lean_dec(v_json_1998_);
v_a_2022_ = lean_ctor_get(v___x_2021_, 0);
v_isSharedCheck_2031_ = !lean_is_exclusive(v___x_2021_);
if (v_isSharedCheck_2031_ == 0)
{
v___x_2024_ = v___x_2021_;
v_isShared_2025_ = v_isSharedCheck_2031_;
goto v_resetjp_2023_;
}
else
{
lean_inc(v_a_2022_);
lean_dec(v___x_2021_);
v___x_2024_ = lean_box(0);
v_isShared_2025_ = v_isSharedCheck_2031_;
goto v_resetjp_2023_;
}
v_resetjp_2023_:
{
lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2029_; 
v___x_2026_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__11, &l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__11);
v___x_2027_ = lean_string_append(v___x_2026_, v_a_2022_);
lean_dec(v_a_2022_);
if (v_isShared_2025_ == 0)
{
lean_ctor_set(v___x_2024_, 0, v___x_2027_);
v___x_2029_ = v___x_2024_;
goto v_reusejp_2028_;
}
else
{
lean_object* v_reuseFailAlloc_2030_; 
v_reuseFailAlloc_2030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2030_, 0, v___x_2027_);
v___x_2029_ = v_reuseFailAlloc_2030_;
goto v_reusejp_2028_;
}
v_reusejp_2028_:
{
return v___x_2029_;
}
}
}
else
{
if (lean_obj_tag(v___x_2021_) == 0)
{
lean_object* v_a_2032_; lean_object* v___x_2034_; uint8_t v_isShared_2035_; uint8_t v_isSharedCheck_2039_; 
lean_dec(v_a_2019_);
lean_dec(v_json_1998_);
v_a_2032_ = lean_ctor_get(v___x_2021_, 0);
v_isSharedCheck_2039_ = !lean_is_exclusive(v___x_2021_);
if (v_isSharedCheck_2039_ == 0)
{
v___x_2034_ = v___x_2021_;
v_isShared_2035_ = v_isSharedCheck_2039_;
goto v_resetjp_2033_;
}
else
{
lean_inc(v_a_2032_);
lean_dec(v___x_2021_);
v___x_2034_ = lean_box(0);
v_isShared_2035_ = v_isSharedCheck_2039_;
goto v_resetjp_2033_;
}
v_resetjp_2033_:
{
lean_object* v___x_2037_; 
if (v_isShared_2035_ == 0)
{
lean_ctor_set_tag(v___x_2034_, 0);
v___x_2037_ = v___x_2034_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2038_; 
v_reuseFailAlloc_2038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2038_, 0, v_a_2032_);
v___x_2037_ = v_reuseFailAlloc_2038_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
return v___x_2037_;
}
}
}
else
{
lean_object* v_a_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; 
v_a_2040_ = lean_ctor_get(v___x_2021_, 0);
lean_inc(v_a_2040_);
lean_dec_ref_known(v___x_2021_, 1);
v___x_2041_ = ((lean_object*)(l_Lean_Lsp_instToJsonCreateFile_toJson___closed__0));
lean_inc(v_json_1998_);
v___x_2042_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCreateFile_fromJson_spec__0(v_json_1998_, v___x_2041_);
if (lean_obj_tag(v___x_2042_) == 0)
{
lean_object* v_a_2043_; lean_object* v___x_2045_; uint8_t v_isShared_2046_; uint8_t v_isSharedCheck_2052_; 
lean_dec(v_a_2040_);
lean_dec(v_a_2019_);
lean_dec(v_json_1998_);
v_a_2043_ = lean_ctor_get(v___x_2042_, 0);
v_isSharedCheck_2052_ = !lean_is_exclusive(v___x_2042_);
if (v_isSharedCheck_2052_ == 0)
{
v___x_2045_ = v___x_2042_;
v_isShared_2046_ = v_isSharedCheck_2052_;
goto v_resetjp_2044_;
}
else
{
lean_inc(v_a_2043_);
lean_dec(v___x_2042_);
v___x_2045_ = lean_box(0);
v_isShared_2046_ = v_isSharedCheck_2052_;
goto v_resetjp_2044_;
}
v_resetjp_2044_:
{
lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2050_; 
v___x_2047_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__13, &l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__13);
v___x_2048_ = lean_string_append(v___x_2047_, v_a_2043_);
lean_dec(v_a_2043_);
if (v_isShared_2046_ == 0)
{
lean_ctor_set(v___x_2045_, 0, v___x_2048_);
v___x_2050_ = v___x_2045_;
goto v_reusejp_2049_;
}
else
{
lean_object* v_reuseFailAlloc_2051_; 
v_reuseFailAlloc_2051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2051_, 0, v___x_2048_);
v___x_2050_ = v_reuseFailAlloc_2051_;
goto v_reusejp_2049_;
}
v_reusejp_2049_:
{
return v___x_2050_;
}
}
}
else
{
if (lean_obj_tag(v___x_2042_) == 0)
{
lean_object* v_a_2053_; lean_object* v___x_2055_; uint8_t v_isShared_2056_; uint8_t v_isSharedCheck_2060_; 
lean_dec(v_a_2040_);
lean_dec(v_a_2019_);
lean_dec(v_json_1998_);
v_a_2053_ = lean_ctor_get(v___x_2042_, 0);
v_isSharedCheck_2060_ = !lean_is_exclusive(v___x_2042_);
if (v_isSharedCheck_2060_ == 0)
{
v___x_2055_ = v___x_2042_;
v_isShared_2056_ = v_isSharedCheck_2060_;
goto v_resetjp_2054_;
}
else
{
lean_inc(v_a_2053_);
lean_dec(v___x_2042_);
v___x_2055_ = lean_box(0);
v_isShared_2056_ = v_isSharedCheck_2060_;
goto v_resetjp_2054_;
}
v_resetjp_2054_:
{
lean_object* v___x_2058_; 
if (v_isShared_2056_ == 0)
{
lean_ctor_set_tag(v___x_2055_, 0);
v___x_2058_ = v___x_2055_;
goto v_reusejp_2057_;
}
else
{
lean_object* v_reuseFailAlloc_2059_; 
v_reuseFailAlloc_2059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2059_, 0, v_a_2053_);
v___x_2058_ = v_reuseFailAlloc_2059_;
goto v_reusejp_2057_;
}
v_reusejp_2057_:
{
return v___x_2058_;
}
}
}
else
{
lean_object* v_a_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; 
v_a_2061_ = lean_ctor_get(v___x_2042_, 0);
lean_inc(v_a_2061_);
lean_dec_ref_known(v___x_2042_, 1);
v___x_2062_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextEdit_toJson___closed__2));
v___x_2063_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextEdit_fromJson_spec__1(v_json_1998_, v___x_2062_);
if (lean_obj_tag(v___x_2063_) == 0)
{
lean_object* v_a_2064_; lean_object* v___x_2066_; uint8_t v_isShared_2067_; uint8_t v_isSharedCheck_2073_; 
lean_dec(v_a_2061_);
lean_dec(v_a_2040_);
lean_dec(v_a_2019_);
v_a_2064_ = lean_ctor_get(v___x_2063_, 0);
v_isSharedCheck_2073_ = !lean_is_exclusive(v___x_2063_);
if (v_isSharedCheck_2073_ == 0)
{
v___x_2066_ = v___x_2063_;
v_isShared_2067_ = v_isSharedCheck_2073_;
goto v_resetjp_2065_;
}
else
{
lean_inc(v_a_2064_);
lean_dec(v___x_2063_);
v___x_2066_ = lean_box(0);
v_isShared_2067_ = v_isSharedCheck_2073_;
goto v_resetjp_2065_;
}
v_resetjp_2065_:
{
lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2071_; 
v___x_2068_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__15, &l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__15_once, _init_l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__15);
v___x_2069_ = lean_string_append(v___x_2068_, v_a_2064_);
lean_dec(v_a_2064_);
if (v_isShared_2067_ == 0)
{
lean_ctor_set(v___x_2066_, 0, v___x_2069_);
v___x_2071_ = v___x_2066_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2072_; 
v_reuseFailAlloc_2072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2072_, 0, v___x_2069_);
v___x_2071_ = v_reuseFailAlloc_2072_;
goto v_reusejp_2070_;
}
v_reusejp_2070_:
{
return v___x_2071_;
}
}
}
else
{
if (lean_obj_tag(v___x_2063_) == 0)
{
lean_object* v_a_2074_; lean_object* v___x_2076_; uint8_t v_isShared_2077_; uint8_t v_isSharedCheck_2081_; 
lean_dec(v_a_2061_);
lean_dec(v_a_2040_);
lean_dec(v_a_2019_);
v_a_2074_ = lean_ctor_get(v___x_2063_, 0);
v_isSharedCheck_2081_ = !lean_is_exclusive(v___x_2063_);
if (v_isSharedCheck_2081_ == 0)
{
v___x_2076_ = v___x_2063_;
v_isShared_2077_ = v_isSharedCheck_2081_;
goto v_resetjp_2075_;
}
else
{
lean_inc(v_a_2074_);
lean_dec(v___x_2063_);
v___x_2076_ = lean_box(0);
v_isShared_2077_ = v_isSharedCheck_2081_;
goto v_resetjp_2075_;
}
v_resetjp_2075_:
{
lean_object* v___x_2079_; 
if (v_isShared_2077_ == 0)
{
lean_ctor_set_tag(v___x_2076_, 0);
v___x_2079_ = v___x_2076_;
goto v_reusejp_2078_;
}
else
{
lean_object* v_reuseFailAlloc_2080_; 
v_reuseFailAlloc_2080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2080_, 0, v_a_2074_);
v___x_2079_ = v_reuseFailAlloc_2080_;
goto v_reusejp_2078_;
}
v_reusejp_2078_:
{
return v___x_2079_;
}
}
}
else
{
lean_object* v_a_2082_; lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2090_; 
v_a_2082_ = lean_ctor_get(v___x_2063_, 0);
v_isSharedCheck_2090_ = !lean_is_exclusive(v___x_2063_);
if (v_isSharedCheck_2090_ == 0)
{
v___x_2084_ = v___x_2063_;
v_isShared_2085_ = v_isSharedCheck_2090_;
goto v_resetjp_2083_;
}
else
{
lean_inc(v_a_2082_);
lean_dec(v___x_2063_);
v___x_2084_ = lean_box(0);
v_isShared_2085_ = v_isSharedCheck_2090_;
goto v_resetjp_2083_;
}
v_resetjp_2083_:
{
lean_object* v___x_2086_; lean_object* v___x_2088_; 
v___x_2086_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2086_, 0, v_a_2019_);
lean_ctor_set(v___x_2086_, 1, v_a_2040_);
lean_ctor_set(v___x_2086_, 2, v_a_2061_);
lean_ctor_set(v___x_2086_, 3, v_a_2082_);
if (v_isShared_2085_ == 0)
{
lean_ctor_set(v___x_2084_, 0, v___x_2086_);
v___x_2088_ = v___x_2084_;
goto v_reusejp_2087_;
}
else
{
lean_object* v_reuseFailAlloc_2089_; 
v_reuseFailAlloc_2089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2089_, 0, v___x_2086_);
v___x_2088_ = v_reuseFailAlloc_2089_;
goto v_reusejp_2087_;
}
v_reusejp_2087_:
{
return v___x_2088_;
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
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDeleteFile_toJson_spec__0(lean_object* v_k_2093_, lean_object* v_x_2094_){
_start:
{
if (lean_obj_tag(v_x_2094_) == 0)
{
lean_object* v___x_2095_; 
lean_dec_ref(v_k_2093_);
v___x_2095_ = lean_box(0);
return v___x_2095_;
}
else
{
lean_object* v_val_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; 
v_val_2096_ = lean_ctor_get(v_x_2094_, 0);
v___x_2097_ = l_Lean_Lsp_DeleteFile_instToJsonOptions_toJson(v_val_2096_);
v___x_2098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2098_, 0, v_k_2093_);
lean_ctor_set(v___x_2098_, 1, v___x_2097_);
v___x_2099_ = lean_box(0);
v___x_2100_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2100_, 0, v___x_2098_);
lean_ctor_set(v___x_2100_, 1, v___x_2099_);
return v___x_2100_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDeleteFile_toJson_spec__0___boxed(lean_object* v_k_2101_, lean_object* v_x_2102_){
_start:
{
lean_object* v_res_2103_; 
v_res_2103_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDeleteFile_toJson_spec__0(v_k_2101_, v_x_2102_);
lean_dec(v_x_2102_);
return v_res_2103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDeleteFile_toJson(lean_object* v_x_2104_){
_start:
{
lean_object* v_uri_2105_; lean_object* v_options_x3f_2106_; lean_object* v_annotationId_x3f_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; 
v_uri_2105_ = lean_ctor_get(v_x_2104_, 0);
lean_inc_ref(v_uri_2105_);
v_options_x3f_2106_ = lean_ctor_get(v_x_2104_, 1);
lean_inc(v_options_x3f_2106_);
v_annotationId_x3f_2107_ = lean_ctor_get(v_x_2104_, 2);
lean_inc(v_annotationId_x3f_2107_);
lean_dec_ref(v_x_2104_);
v___x_2108_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__0));
v___x_2109_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2109_, 0, v_uri_2105_);
v___x_2110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2110_, 0, v___x_2108_);
lean_ctor_set(v___x_2110_, 1, v___x_2109_);
v___x_2111_ = lean_box(0);
v___x_2112_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2112_, 0, v___x_2110_);
lean_ctor_set(v___x_2112_, 1, v___x_2111_);
v___x_2113_ = ((lean_object*)(l_Lean_Lsp_instToJsonCreateFile_toJson___closed__0));
v___x_2114_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDeleteFile_toJson_spec__0(v___x_2113_, v_options_x3f_2106_);
lean_dec(v_options_x3f_2106_);
v___x_2115_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextEdit_toJson___closed__2));
v___x_2116_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextEdit_toJson_spec__1(v___x_2115_, v_annotationId_x3f_2107_);
v___x_2117_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2117_, 0, v___x_2116_);
lean_ctor_set(v___x_2117_, 1, v___x_2111_);
v___x_2118_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2118_, 0, v___x_2114_);
lean_ctor_set(v___x_2118_, 1, v___x_2117_);
v___x_2119_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2119_, 0, v___x_2112_);
lean_ctor_set(v___x_2119_, 1, v___x_2118_);
v___x_2120_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__2));
v___x_2121_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLocation_toJson_spec__0(v___x_2119_, v___x_2120_);
v___x_2122_ = l_Lean_Json_mkObj(v___x_2121_);
lean_dec(v___x_2121_);
return v___x_2122_;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDeleteFile_fromJson_spec__0_spec__0(lean_object* v_x_2127_){
_start:
{
if (lean_obj_tag(v_x_2127_) == 0)
{
lean_object* v___x_2128_; 
v___x_2128_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDeleteFile_fromJson_spec__0_spec__0___closed__0));
return v___x_2128_;
}
else
{
lean_object* v___x_2129_; 
v___x_2129_ = l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson(v_x_2127_);
if (lean_obj_tag(v___x_2129_) == 0)
{
lean_object* v_a_2130_; lean_object* v___x_2132_; uint8_t v_isShared_2133_; uint8_t v_isSharedCheck_2137_; 
v_a_2130_ = lean_ctor_get(v___x_2129_, 0);
v_isSharedCheck_2137_ = !lean_is_exclusive(v___x_2129_);
if (v_isSharedCheck_2137_ == 0)
{
v___x_2132_ = v___x_2129_;
v_isShared_2133_ = v_isSharedCheck_2137_;
goto v_resetjp_2131_;
}
else
{
lean_inc(v_a_2130_);
lean_dec(v___x_2129_);
v___x_2132_ = lean_box(0);
v_isShared_2133_ = v_isSharedCheck_2137_;
goto v_resetjp_2131_;
}
v_resetjp_2131_:
{
lean_object* v___x_2135_; 
if (v_isShared_2133_ == 0)
{
v___x_2135_ = v___x_2132_;
goto v_reusejp_2134_;
}
else
{
lean_object* v_reuseFailAlloc_2136_; 
v_reuseFailAlloc_2136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2136_, 0, v_a_2130_);
v___x_2135_ = v_reuseFailAlloc_2136_;
goto v_reusejp_2134_;
}
v_reusejp_2134_:
{
return v___x_2135_;
}
}
}
else
{
lean_object* v_a_2138_; lean_object* v___x_2140_; uint8_t v_isShared_2141_; uint8_t v_isSharedCheck_2146_; 
v_a_2138_ = lean_ctor_get(v___x_2129_, 0);
v_isSharedCheck_2146_ = !lean_is_exclusive(v___x_2129_);
if (v_isSharedCheck_2146_ == 0)
{
v___x_2140_ = v___x_2129_;
v_isShared_2141_ = v_isSharedCheck_2146_;
goto v_resetjp_2139_;
}
else
{
lean_inc(v_a_2138_);
lean_dec(v___x_2129_);
v___x_2140_ = lean_box(0);
v_isShared_2141_ = v_isSharedCheck_2146_;
goto v_resetjp_2139_;
}
v_resetjp_2139_:
{
lean_object* v___x_2142_; lean_object* v___x_2144_; 
v___x_2142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2142_, 0, v_a_2138_);
if (v_isShared_2141_ == 0)
{
lean_ctor_set(v___x_2140_, 0, v___x_2142_);
v___x_2144_ = v___x_2140_;
goto v_reusejp_2143_;
}
else
{
lean_object* v_reuseFailAlloc_2145_; 
v_reuseFailAlloc_2145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2145_, 0, v___x_2142_);
v___x_2144_ = v_reuseFailAlloc_2145_;
goto v_reusejp_2143_;
}
v_reusejp_2143_:
{
return v___x_2144_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDeleteFile_fromJson_spec__0(lean_object* v_j_2147_, lean_object* v_k_2148_){
_start:
{
lean_object* v___x_2149_; lean_object* v___x_2150_; 
v___x_2149_ = l_Lean_Json_getObjValD(v_j_2147_, v_k_2148_);
v___x_2150_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDeleteFile_fromJson_spec__0_spec__0(v___x_2149_);
return v___x_2150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDeleteFile_fromJson_spec__0___boxed(lean_object* v_j_2151_, lean_object* v_k_2152_){
_start:
{
lean_object* v_res_2153_; 
v_res_2153_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDeleteFile_fromJson_spec__0(v_j_2151_, v_k_2152_);
lean_dec_ref(v_k_2152_);
return v_res_2153_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__1(void){
_start:
{
uint8_t v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; 
v___x_2158_ = 1;
v___x_2159_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__0));
v___x_2160_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2159_, v___x_2158_);
return v___x_2160_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__2(void){
_start:
{
lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; 
v___x_2161_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__5));
v___x_2162_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__1, &l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__1_once, _init_l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__1);
v___x_2163_ = lean_string_append(v___x_2162_, v___x_2161_);
return v___x_2163_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__3(void){
_start:
{
lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; 
v___x_2164_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLocation_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLocation_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLocation_fromJson___closed__8);
v___x_2165_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__2, &l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__2);
v___x_2166_ = lean_string_append(v___x_2165_, v___x_2164_);
return v___x_2166_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__4(void){
_start:
{
lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; 
v___x_2167_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_2168_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__3, &l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__3);
v___x_2169_ = lean_string_append(v___x_2168_, v___x_2167_);
return v___x_2169_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__5(void){
_start:
{
lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; 
v___x_2170_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__7, &l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__7);
v___x_2171_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__2, &l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__2);
v___x_2172_ = lean_string_append(v___x_2171_, v___x_2170_);
return v___x_2172_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__6(void){
_start:
{
lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; 
v___x_2173_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_2174_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__5, &l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__5);
v___x_2175_ = lean_string_append(v___x_2174_, v___x_2173_);
return v___x_2175_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__7(void){
_start:
{
lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; 
v___x_2176_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__17, &l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__17_once, _init_l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__17);
v___x_2177_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__2, &l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__2);
v___x_2178_ = lean_string_append(v___x_2177_, v___x_2176_);
return v___x_2178_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__8(void){
_start:
{
lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; 
v___x_2179_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_2180_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__7, &l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__7);
v___x_2181_ = lean_string_append(v___x_2180_, v___x_2179_);
return v___x_2181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDeleteFile_fromJson(lean_object* v_json_2182_){
_start:
{
lean_object* v___x_2183_; lean_object* v___x_2184_; 
v___x_2183_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__0));
lean_inc(v_json_2182_);
v___x_2184_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocation_fromJson_spec__0(v_json_2182_, v___x_2183_);
if (lean_obj_tag(v___x_2184_) == 0)
{
lean_object* v_a_2185_; lean_object* v___x_2187_; uint8_t v_isShared_2188_; uint8_t v_isSharedCheck_2194_; 
lean_dec(v_json_2182_);
v_a_2185_ = lean_ctor_get(v___x_2184_, 0);
v_isSharedCheck_2194_ = !lean_is_exclusive(v___x_2184_);
if (v_isSharedCheck_2194_ == 0)
{
v___x_2187_ = v___x_2184_;
v_isShared_2188_ = v_isSharedCheck_2194_;
goto v_resetjp_2186_;
}
else
{
lean_inc(v_a_2185_);
lean_dec(v___x_2184_);
v___x_2187_ = lean_box(0);
v_isShared_2188_ = v_isSharedCheck_2194_;
goto v_resetjp_2186_;
}
v_resetjp_2186_:
{
lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2192_; 
v___x_2189_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__4, &l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__4);
v___x_2190_ = lean_string_append(v___x_2189_, v_a_2185_);
lean_dec(v_a_2185_);
if (v_isShared_2188_ == 0)
{
lean_ctor_set(v___x_2187_, 0, v___x_2190_);
v___x_2192_ = v___x_2187_;
goto v_reusejp_2191_;
}
else
{
lean_object* v_reuseFailAlloc_2193_; 
v_reuseFailAlloc_2193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2193_, 0, v___x_2190_);
v___x_2192_ = v_reuseFailAlloc_2193_;
goto v_reusejp_2191_;
}
v_reusejp_2191_:
{
return v___x_2192_;
}
}
}
else
{
if (lean_obj_tag(v___x_2184_) == 0)
{
lean_object* v_a_2195_; lean_object* v___x_2197_; uint8_t v_isShared_2198_; uint8_t v_isSharedCheck_2202_; 
lean_dec(v_json_2182_);
v_a_2195_ = lean_ctor_get(v___x_2184_, 0);
v_isSharedCheck_2202_ = !lean_is_exclusive(v___x_2184_);
if (v_isSharedCheck_2202_ == 0)
{
v___x_2197_ = v___x_2184_;
v_isShared_2198_ = v_isSharedCheck_2202_;
goto v_resetjp_2196_;
}
else
{
lean_inc(v_a_2195_);
lean_dec(v___x_2184_);
v___x_2197_ = lean_box(0);
v_isShared_2198_ = v_isSharedCheck_2202_;
goto v_resetjp_2196_;
}
v_resetjp_2196_:
{
lean_object* v___x_2200_; 
if (v_isShared_2198_ == 0)
{
lean_ctor_set_tag(v___x_2197_, 0);
v___x_2200_ = v___x_2197_;
goto v_reusejp_2199_;
}
else
{
lean_object* v_reuseFailAlloc_2201_; 
v_reuseFailAlloc_2201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2201_, 0, v_a_2195_);
v___x_2200_ = v_reuseFailAlloc_2201_;
goto v_reusejp_2199_;
}
v_reusejp_2199_:
{
return v___x_2200_;
}
}
}
else
{
lean_object* v_a_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; 
v_a_2203_ = lean_ctor_get(v___x_2184_, 0);
lean_inc(v_a_2203_);
lean_dec_ref_known(v___x_2184_, 1);
v___x_2204_ = ((lean_object*)(l_Lean_Lsp_instToJsonCreateFile_toJson___closed__0));
lean_inc(v_json_2182_);
v___x_2205_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDeleteFile_fromJson_spec__0(v_json_2182_, v___x_2204_);
if (lean_obj_tag(v___x_2205_) == 0)
{
lean_object* v_a_2206_; lean_object* v___x_2208_; uint8_t v_isShared_2209_; uint8_t v_isSharedCheck_2215_; 
lean_dec(v_a_2203_);
lean_dec(v_json_2182_);
v_a_2206_ = lean_ctor_get(v___x_2205_, 0);
v_isSharedCheck_2215_ = !lean_is_exclusive(v___x_2205_);
if (v_isSharedCheck_2215_ == 0)
{
v___x_2208_ = v___x_2205_;
v_isShared_2209_ = v_isSharedCheck_2215_;
goto v_resetjp_2207_;
}
else
{
lean_inc(v_a_2206_);
lean_dec(v___x_2205_);
v___x_2208_ = lean_box(0);
v_isShared_2209_ = v_isSharedCheck_2215_;
goto v_resetjp_2207_;
}
v_resetjp_2207_:
{
lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2213_; 
v___x_2210_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__6, &l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__6);
v___x_2211_ = lean_string_append(v___x_2210_, v_a_2206_);
lean_dec(v_a_2206_);
if (v_isShared_2209_ == 0)
{
lean_ctor_set(v___x_2208_, 0, v___x_2211_);
v___x_2213_ = v___x_2208_;
goto v_reusejp_2212_;
}
else
{
lean_object* v_reuseFailAlloc_2214_; 
v_reuseFailAlloc_2214_ = lean_alloc_ctor(0, 1, 0);
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
else
{
if (lean_obj_tag(v___x_2205_) == 0)
{
lean_object* v_a_2216_; lean_object* v___x_2218_; uint8_t v_isShared_2219_; uint8_t v_isSharedCheck_2223_; 
lean_dec(v_a_2203_);
lean_dec(v_json_2182_);
v_a_2216_ = lean_ctor_get(v___x_2205_, 0);
v_isSharedCheck_2223_ = !lean_is_exclusive(v___x_2205_);
if (v_isSharedCheck_2223_ == 0)
{
v___x_2218_ = v___x_2205_;
v_isShared_2219_ = v_isSharedCheck_2223_;
goto v_resetjp_2217_;
}
else
{
lean_inc(v_a_2216_);
lean_dec(v___x_2205_);
v___x_2218_ = lean_box(0);
v_isShared_2219_ = v_isSharedCheck_2223_;
goto v_resetjp_2217_;
}
v_resetjp_2217_:
{
lean_object* v___x_2221_; 
if (v_isShared_2219_ == 0)
{
lean_ctor_set_tag(v___x_2218_, 0);
v___x_2221_ = v___x_2218_;
goto v_reusejp_2220_;
}
else
{
lean_object* v_reuseFailAlloc_2222_; 
v_reuseFailAlloc_2222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2222_, 0, v_a_2216_);
v___x_2221_ = v_reuseFailAlloc_2222_;
goto v_reusejp_2220_;
}
v_reusejp_2220_:
{
return v___x_2221_;
}
}
}
else
{
lean_object* v_a_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; 
v_a_2224_ = lean_ctor_get(v___x_2205_, 0);
lean_inc(v_a_2224_);
lean_dec_ref_known(v___x_2205_, 1);
v___x_2225_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextEdit_toJson___closed__2));
v___x_2226_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextEdit_fromJson_spec__1(v_json_2182_, v___x_2225_);
if (lean_obj_tag(v___x_2226_) == 0)
{
lean_object* v_a_2227_; lean_object* v___x_2229_; uint8_t v_isShared_2230_; uint8_t v_isSharedCheck_2236_; 
lean_dec(v_a_2224_);
lean_dec(v_a_2203_);
v_a_2227_ = lean_ctor_get(v___x_2226_, 0);
v_isSharedCheck_2236_ = !lean_is_exclusive(v___x_2226_);
if (v_isSharedCheck_2236_ == 0)
{
v___x_2229_ = v___x_2226_;
v_isShared_2230_ = v_isSharedCheck_2236_;
goto v_resetjp_2228_;
}
else
{
lean_inc(v_a_2227_);
lean_dec(v___x_2226_);
v___x_2229_ = lean_box(0);
v_isShared_2230_ = v_isSharedCheck_2236_;
goto v_resetjp_2228_;
}
v_resetjp_2228_:
{
lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2234_; 
v___x_2231_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__8, &l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__8);
v___x_2232_ = lean_string_append(v___x_2231_, v_a_2227_);
lean_dec(v_a_2227_);
if (v_isShared_2230_ == 0)
{
lean_ctor_set(v___x_2229_, 0, v___x_2232_);
v___x_2234_ = v___x_2229_;
goto v_reusejp_2233_;
}
else
{
lean_object* v_reuseFailAlloc_2235_; 
v_reuseFailAlloc_2235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2235_, 0, v___x_2232_);
v___x_2234_ = v_reuseFailAlloc_2235_;
goto v_reusejp_2233_;
}
v_reusejp_2233_:
{
return v___x_2234_;
}
}
}
else
{
if (lean_obj_tag(v___x_2226_) == 0)
{
lean_object* v_a_2237_; lean_object* v___x_2239_; uint8_t v_isShared_2240_; uint8_t v_isSharedCheck_2244_; 
lean_dec(v_a_2224_);
lean_dec(v_a_2203_);
v_a_2237_ = lean_ctor_get(v___x_2226_, 0);
v_isSharedCheck_2244_ = !lean_is_exclusive(v___x_2226_);
if (v_isSharedCheck_2244_ == 0)
{
v___x_2239_ = v___x_2226_;
v_isShared_2240_ = v_isSharedCheck_2244_;
goto v_resetjp_2238_;
}
else
{
lean_inc(v_a_2237_);
lean_dec(v___x_2226_);
v___x_2239_ = lean_box(0);
v_isShared_2240_ = v_isSharedCheck_2244_;
goto v_resetjp_2238_;
}
v_resetjp_2238_:
{
lean_object* v___x_2242_; 
if (v_isShared_2240_ == 0)
{
lean_ctor_set_tag(v___x_2239_, 0);
v___x_2242_ = v___x_2239_;
goto v_reusejp_2241_;
}
else
{
lean_object* v_reuseFailAlloc_2243_; 
v_reuseFailAlloc_2243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2243_, 0, v_a_2237_);
v___x_2242_ = v_reuseFailAlloc_2243_;
goto v_reusejp_2241_;
}
v_reusejp_2241_:
{
return v___x_2242_;
}
}
}
else
{
lean_object* v_a_2245_; lean_object* v___x_2247_; uint8_t v_isShared_2248_; uint8_t v_isSharedCheck_2253_; 
v_a_2245_ = lean_ctor_get(v___x_2226_, 0);
v_isSharedCheck_2253_ = !lean_is_exclusive(v___x_2226_);
if (v_isSharedCheck_2253_ == 0)
{
v___x_2247_ = v___x_2226_;
v_isShared_2248_ = v_isSharedCheck_2253_;
goto v_resetjp_2246_;
}
else
{
lean_inc(v_a_2245_);
lean_dec(v___x_2226_);
v___x_2247_ = lean_box(0);
v_isShared_2248_ = v_isSharedCheck_2253_;
goto v_resetjp_2246_;
}
v_resetjp_2246_:
{
lean_object* v___x_2249_; lean_object* v___x_2251_; 
v___x_2249_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2249_, 0, v_a_2203_);
lean_ctor_set(v___x_2249_, 1, v_a_2224_);
lean_ctor_set(v___x_2249_, 2, v_a_2245_);
if (v_isShared_2248_ == 0)
{
lean_ctor_set(v___x_2247_, 0, v___x_2249_);
v___x_2251_ = v___x_2247_;
goto v_reusejp_2250_;
}
else
{
lean_object* v_reuseFailAlloc_2252_; 
v_reuseFailAlloc_2252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2252_, 0, v___x_2249_);
v___x_2251_ = v_reuseFailAlloc_2252_;
goto v_reusejp_2250_;
}
v_reusejp_2250_:
{
return v___x_2251_;
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
LEAN_EXPORT lean_object* l_Lean_Lsp_DocumentChange_ctorIdx(lean_object* v_x_2256_){
_start:
{
switch(lean_obj_tag(v_x_2256_))
{
case 0:
{
lean_object* v___x_2257_; 
v___x_2257_ = lean_unsigned_to_nat(0u);
return v___x_2257_;
}
case 1:
{
lean_object* v___x_2258_; 
v___x_2258_ = lean_unsigned_to_nat(1u);
return v___x_2258_;
}
case 2:
{
lean_object* v___x_2259_; 
v___x_2259_ = lean_unsigned_to_nat(2u);
return v___x_2259_;
}
default: 
{
lean_object* v___x_2260_; 
v___x_2260_ = lean_unsigned_to_nat(3u);
return v___x_2260_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DocumentChange_ctorIdx___boxed(lean_object* v_x_2261_){
_start:
{
lean_object* v_res_2262_; 
v_res_2262_ = l_Lean_Lsp_DocumentChange_ctorIdx(v_x_2261_);
lean_dec_ref(v_x_2261_);
return v_res_2262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DocumentChange_ctorElim___redArg(lean_object* v_t_2263_, lean_object* v_k_2264_){
_start:
{
lean_object* v_a_2265_; lean_object* v___x_2266_; 
v_a_2265_ = lean_ctor_get(v_t_2263_, 0);
lean_inc_ref(v_a_2265_);
lean_dec_ref(v_t_2263_);
v___x_2266_ = lean_apply_1(v_k_2264_, v_a_2265_);
return v___x_2266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DocumentChange_ctorElim(lean_object* v_motive_2267_, lean_object* v_ctorIdx_2268_, lean_object* v_t_2269_, lean_object* v_h_2270_, lean_object* v_k_2271_){
_start:
{
lean_object* v___x_2272_; 
v___x_2272_ = l_Lean_Lsp_DocumentChange_ctorElim___redArg(v_t_2269_, v_k_2271_);
return v___x_2272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DocumentChange_ctorElim___boxed(lean_object* v_motive_2273_, lean_object* v_ctorIdx_2274_, lean_object* v_t_2275_, lean_object* v_h_2276_, lean_object* v_k_2277_){
_start:
{
lean_object* v_res_2278_; 
v_res_2278_ = l_Lean_Lsp_DocumentChange_ctorElim(v_motive_2273_, v_ctorIdx_2274_, v_t_2275_, v_h_2276_, v_k_2277_);
lean_dec(v_ctorIdx_2274_);
return v_res_2278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DocumentChange_create_elim___redArg(lean_object* v_t_2279_, lean_object* v_create_2280_){
_start:
{
lean_object* v___x_2281_; 
v___x_2281_ = l_Lean_Lsp_DocumentChange_ctorElim___redArg(v_t_2279_, v_create_2280_);
return v___x_2281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DocumentChange_create_elim(lean_object* v_motive_2282_, lean_object* v_t_2283_, lean_object* v_h_2284_, lean_object* v_create_2285_){
_start:
{
lean_object* v___x_2286_; 
v___x_2286_ = l_Lean_Lsp_DocumentChange_ctorElim___redArg(v_t_2283_, v_create_2285_);
return v___x_2286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DocumentChange_rename_elim___redArg(lean_object* v_t_2287_, lean_object* v_rename_2288_){
_start:
{
lean_object* v___x_2289_; 
v___x_2289_ = l_Lean_Lsp_DocumentChange_ctorElim___redArg(v_t_2287_, v_rename_2288_);
return v___x_2289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DocumentChange_rename_elim(lean_object* v_motive_2290_, lean_object* v_t_2291_, lean_object* v_h_2292_, lean_object* v_rename_2293_){
_start:
{
lean_object* v___x_2294_; 
v___x_2294_ = l_Lean_Lsp_DocumentChange_ctorElim___redArg(v_t_2291_, v_rename_2293_);
return v___x_2294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DocumentChange_delete_elim___redArg(lean_object* v_t_2295_, lean_object* v_delete_2296_){
_start:
{
lean_object* v___x_2297_; 
v___x_2297_ = l_Lean_Lsp_DocumentChange_ctorElim___redArg(v_t_2295_, v_delete_2296_);
return v___x_2297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DocumentChange_delete_elim(lean_object* v_motive_2298_, lean_object* v_t_2299_, lean_object* v_h_2300_, lean_object* v_delete_2301_){
_start:
{
lean_object* v___x_2302_; 
v___x_2302_ = l_Lean_Lsp_DocumentChange_ctorElim___redArg(v_t_2299_, v_delete_2301_);
return v___x_2302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DocumentChange_edit_elim___redArg(lean_object* v_t_2303_, lean_object* v_edit_2304_){
_start:
{
lean_object* v___x_2305_; 
v___x_2305_ = l_Lean_Lsp_DocumentChange_ctorElim___redArg(v_t_2303_, v_edit_2304_);
return v___x_2305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DocumentChange_edit_elim(lean_object* v_motive_2306_, lean_object* v_t_2307_, lean_object* v_h_2308_, lean_object* v_edit_2309_){
_start:
{
lean_object* v___x_2310_; 
v___x_2310_ = l_Lean_Lsp_DocumentChange_ctorElim___redArg(v_t_2307_, v_edit_2309_);
return v___x_2310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDocumentChange___lam__0(lean_object* v_x_2321_){
_start:
{
switch(lean_obj_tag(v_x_2321_))
{
case 0:
{
lean_object* v_a_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; 
v_a_2322_ = lean_ctor_get(v_x_2321_, 0);
lean_inc_ref(v_a_2322_);
lean_dec_ref_known(v_x_2321_, 1);
v___x_2323_ = l_Lean_Lsp_instToJsonCreateFile_toJson(v_a_2322_);
v___x_2324_ = ((lean_object*)(l_Lean_Lsp_instToJsonDocumentChange___lam__0___closed__0));
v___x_2325_ = ((lean_object*)(l_Lean_Lsp_instToJsonDocumentChange___lam__0___closed__2));
v___x_2326_ = l_Lean_Json_setObjVal_x21(v___x_2323_, v___x_2324_, v___x_2325_);
return v___x_2326_;
}
case 1:
{
lean_object* v_a_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; 
v_a_2327_ = lean_ctor_get(v_x_2321_, 0);
lean_inc_ref(v_a_2327_);
lean_dec_ref_known(v_x_2321_, 1);
v___x_2328_ = l_Lean_Lsp_instToJsonRenameFile_toJson(v_a_2327_);
v___x_2329_ = ((lean_object*)(l_Lean_Lsp_instToJsonDocumentChange___lam__0___closed__0));
v___x_2330_ = ((lean_object*)(l_Lean_Lsp_instToJsonDocumentChange___lam__0___closed__4));
v___x_2331_ = l_Lean_Json_setObjVal_x21(v___x_2328_, v___x_2329_, v___x_2330_);
return v___x_2331_;
}
case 2:
{
lean_object* v_a_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; 
v_a_2332_ = lean_ctor_get(v_x_2321_, 0);
lean_inc_ref(v_a_2332_);
lean_dec_ref_known(v_x_2321_, 1);
v___x_2333_ = l_Lean_Lsp_instToJsonDeleteFile_toJson(v_a_2332_);
v___x_2334_ = ((lean_object*)(l_Lean_Lsp_instToJsonDocumentChange___lam__0___closed__0));
v___x_2335_ = ((lean_object*)(l_Lean_Lsp_instToJsonDocumentChange___lam__0___closed__6));
v___x_2336_ = l_Lean_Json_setObjVal_x21(v___x_2333_, v___x_2334_, v___x_2335_);
return v___x_2336_;
}
default: 
{
lean_object* v_a_2337_; lean_object* v___x_2338_; 
v_a_2337_ = lean_ctor_get(v_x_2321_, 0);
lean_inc_ref(v_a_2337_);
lean_dec_ref_known(v_x_2321_, 1);
v___x_2338_ = l_Lean_Lsp_instToJsonTextDocumentEdit_toJson(v_a_2337_);
return v___x_2338_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDocumentChange___lam__0(lean_object* v_kind_2342_){
_start:
{
lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; 
v___x_2343_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDocumentChange___lam__0___closed__0));
v___x_2344_ = lean_unsigned_to_nat(80u);
v___x_2345_ = l_Lean_Json_pretty(v_kind_2342_, v___x_2344_);
v___x_2346_ = lean_string_append(v___x_2343_, v___x_2345_);
lean_dec_ref(v___x_2345_);
v___x_2347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2347_, 0, v___x_2346_);
return v___x_2347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDocumentChange___lam__1(lean_object* v___f_2348_, lean_object* v_j_2349_){
_start:
{
lean_object* v___y_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; 
v___x_2371_ = ((lean_object*)(l_Lean_Lsp_instToJsonDocumentChange___lam__0___closed__0));
lean_inc(v_j_2349_);
v___x_2372_ = l_Lean_Json_getObjVal_x3f(v_j_2349_, v___x_2371_);
if (lean_obj_tag(v___x_2372_) == 0)
{
lean_dec_ref_known(v___x_2372_, 1);
lean_dec_ref(v___f_2348_);
goto v___jp_2350_;
}
else
{
lean_object* v_a_2373_; 
v_a_2373_ = lean_ctor_get(v___x_2372_, 0);
lean_inc(v_a_2373_);
lean_dec_ref_known(v___x_2372_, 1);
if (lean_obj_tag(v_a_2373_) == 3)
{
lean_object* v_s_2374_; lean_object* v___x_2375_; uint8_t v___x_2376_; 
v_s_2374_ = lean_ctor_get(v_a_2373_, 0);
v___x_2375_ = ((lean_object*)(l_Lean_Lsp_instToJsonDocumentChange___lam__0___closed__1));
v___x_2376_ = lean_string_dec_eq(v_s_2374_, v___x_2375_);
if (v___x_2376_ == 0)
{
lean_object* v___x_2377_; uint8_t v___x_2378_; 
v___x_2377_ = ((lean_object*)(l_Lean_Lsp_instToJsonDocumentChange___lam__0___closed__3));
v___x_2378_ = lean_string_dec_eq(v_s_2374_, v___x_2377_);
if (v___x_2378_ == 0)
{
lean_object* v___x_2379_; uint8_t v___x_2380_; 
v___x_2379_ = ((lean_object*)(l_Lean_Lsp_instToJsonDocumentChange___lam__0___closed__5));
v___x_2380_ = lean_string_dec_eq(v_s_2374_, v___x_2379_);
if (v___x_2380_ == 0)
{
lean_object* v___x_2381_; 
v___x_2381_ = lean_apply_1(v___f_2348_, v_a_2373_);
v___y_2370_ = v___x_2381_;
goto v___jp_2369_;
}
else
{
lean_object* v___x_2383_; uint8_t v_isShared_2384_; uint8_t v_isSharedCheck_2397_; 
lean_dec_ref(v___f_2348_);
v_isSharedCheck_2397_ = !lean_is_exclusive(v_a_2373_);
if (v_isSharedCheck_2397_ == 0)
{
lean_object* v_unused_2398_; 
v_unused_2398_ = lean_ctor_get(v_a_2373_, 0);
lean_dec(v_unused_2398_);
v___x_2383_ = v_a_2373_;
v_isShared_2384_ = v_isSharedCheck_2397_;
goto v_resetjp_2382_;
}
else
{
lean_dec(v_a_2373_);
v___x_2383_ = lean_box(0);
v_isShared_2384_ = v_isSharedCheck_2397_;
goto v_resetjp_2382_;
}
v_resetjp_2382_:
{
lean_object* v___x_2385_; 
lean_inc(v_j_2349_);
v___x_2385_ = l_Lean_Lsp_instFromJsonDeleteFile_fromJson(v_j_2349_);
if (lean_obj_tag(v___x_2385_) == 0)
{
lean_dec_ref_known(v___x_2385_, 1);
lean_del_object(v___x_2383_);
goto v___jp_2350_;
}
else
{
lean_object* v_a_2386_; lean_object* v___x_2388_; uint8_t v_isShared_2389_; uint8_t v_isSharedCheck_2396_; 
lean_dec(v_j_2349_);
v_a_2386_ = lean_ctor_get(v___x_2385_, 0);
v_isSharedCheck_2396_ = !lean_is_exclusive(v___x_2385_);
if (v_isSharedCheck_2396_ == 0)
{
v___x_2388_ = v___x_2385_;
v_isShared_2389_ = v_isSharedCheck_2396_;
goto v_resetjp_2387_;
}
else
{
lean_inc(v_a_2386_);
lean_dec(v___x_2385_);
v___x_2388_ = lean_box(0);
v_isShared_2389_ = v_isSharedCheck_2396_;
goto v_resetjp_2387_;
}
v_resetjp_2387_:
{
lean_object* v___x_2391_; 
if (v_isShared_2384_ == 0)
{
lean_ctor_set_tag(v___x_2383_, 2);
lean_ctor_set(v___x_2383_, 0, v_a_2386_);
v___x_2391_ = v___x_2383_;
goto v_reusejp_2390_;
}
else
{
lean_object* v_reuseFailAlloc_2395_; 
v_reuseFailAlloc_2395_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2395_, 0, v_a_2386_);
v___x_2391_ = v_reuseFailAlloc_2395_;
goto v_reusejp_2390_;
}
v_reusejp_2390_:
{
lean_object* v___x_2393_; 
if (v_isShared_2389_ == 0)
{
lean_ctor_set(v___x_2388_, 0, v___x_2391_);
v___x_2393_ = v___x_2388_;
goto v_reusejp_2392_;
}
else
{
lean_object* v_reuseFailAlloc_2394_; 
v_reuseFailAlloc_2394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2394_, 0, v___x_2391_);
v___x_2393_ = v_reuseFailAlloc_2394_;
goto v_reusejp_2392_;
}
v_reusejp_2392_:
{
return v___x_2393_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2400_; uint8_t v_isShared_2401_; uint8_t v_isSharedCheck_2414_; 
lean_dec_ref(v___f_2348_);
v_isSharedCheck_2414_ = !lean_is_exclusive(v_a_2373_);
if (v_isSharedCheck_2414_ == 0)
{
lean_object* v_unused_2415_; 
v_unused_2415_ = lean_ctor_get(v_a_2373_, 0);
lean_dec(v_unused_2415_);
v___x_2400_ = v_a_2373_;
v_isShared_2401_ = v_isSharedCheck_2414_;
goto v_resetjp_2399_;
}
else
{
lean_dec(v_a_2373_);
v___x_2400_ = lean_box(0);
v_isShared_2401_ = v_isSharedCheck_2414_;
goto v_resetjp_2399_;
}
v_resetjp_2399_:
{
lean_object* v___x_2402_; 
lean_inc(v_j_2349_);
v___x_2402_ = l_Lean_Lsp_instFromJsonRenameFile_fromJson(v_j_2349_);
if (lean_obj_tag(v___x_2402_) == 0)
{
lean_dec_ref_known(v___x_2402_, 1);
lean_del_object(v___x_2400_);
goto v___jp_2350_;
}
else
{
lean_object* v_a_2403_; lean_object* v___x_2405_; uint8_t v_isShared_2406_; uint8_t v_isSharedCheck_2413_; 
lean_dec(v_j_2349_);
v_a_2403_ = lean_ctor_get(v___x_2402_, 0);
v_isSharedCheck_2413_ = !lean_is_exclusive(v___x_2402_);
if (v_isSharedCheck_2413_ == 0)
{
v___x_2405_ = v___x_2402_;
v_isShared_2406_ = v_isSharedCheck_2413_;
goto v_resetjp_2404_;
}
else
{
lean_inc(v_a_2403_);
lean_dec(v___x_2402_);
v___x_2405_ = lean_box(0);
v_isShared_2406_ = v_isSharedCheck_2413_;
goto v_resetjp_2404_;
}
v_resetjp_2404_:
{
lean_object* v___x_2408_; 
if (v_isShared_2401_ == 0)
{
lean_ctor_set_tag(v___x_2400_, 1);
lean_ctor_set(v___x_2400_, 0, v_a_2403_);
v___x_2408_ = v___x_2400_;
goto v_reusejp_2407_;
}
else
{
lean_object* v_reuseFailAlloc_2412_; 
v_reuseFailAlloc_2412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2412_, 0, v_a_2403_);
v___x_2408_ = v_reuseFailAlloc_2412_;
goto v_reusejp_2407_;
}
v_reusejp_2407_:
{
lean_object* v___x_2410_; 
if (v_isShared_2406_ == 0)
{
lean_ctor_set(v___x_2405_, 0, v___x_2408_);
v___x_2410_ = v___x_2405_;
goto v_reusejp_2409_;
}
else
{
lean_object* v_reuseFailAlloc_2411_; 
v_reuseFailAlloc_2411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2411_, 0, v___x_2408_);
v___x_2410_ = v_reuseFailAlloc_2411_;
goto v_reusejp_2409_;
}
v_reusejp_2409_:
{
return v___x_2410_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2417_; uint8_t v_isShared_2418_; uint8_t v_isSharedCheck_2431_; 
lean_dec_ref(v___f_2348_);
v_isSharedCheck_2431_ = !lean_is_exclusive(v_a_2373_);
if (v_isSharedCheck_2431_ == 0)
{
lean_object* v_unused_2432_; 
v_unused_2432_ = lean_ctor_get(v_a_2373_, 0);
lean_dec(v_unused_2432_);
v___x_2417_ = v_a_2373_;
v_isShared_2418_ = v_isSharedCheck_2431_;
goto v_resetjp_2416_;
}
else
{
lean_dec(v_a_2373_);
v___x_2417_ = lean_box(0);
v_isShared_2418_ = v_isSharedCheck_2431_;
goto v_resetjp_2416_;
}
v_resetjp_2416_:
{
lean_object* v___x_2419_; 
lean_inc(v_j_2349_);
v___x_2419_ = l_Lean_Lsp_instFromJsonCreateFile_fromJson(v_j_2349_);
if (lean_obj_tag(v___x_2419_) == 0)
{
lean_dec_ref_known(v___x_2419_, 1);
lean_del_object(v___x_2417_);
goto v___jp_2350_;
}
else
{
lean_object* v_a_2420_; lean_object* v___x_2422_; uint8_t v_isShared_2423_; uint8_t v_isSharedCheck_2430_; 
lean_dec(v_j_2349_);
v_a_2420_ = lean_ctor_get(v___x_2419_, 0);
v_isSharedCheck_2430_ = !lean_is_exclusive(v___x_2419_);
if (v_isSharedCheck_2430_ == 0)
{
v___x_2422_ = v___x_2419_;
v_isShared_2423_ = v_isSharedCheck_2430_;
goto v_resetjp_2421_;
}
else
{
lean_inc(v_a_2420_);
lean_dec(v___x_2419_);
v___x_2422_ = lean_box(0);
v_isShared_2423_ = v_isSharedCheck_2430_;
goto v_resetjp_2421_;
}
v_resetjp_2421_:
{
lean_object* v___x_2425_; 
if (v_isShared_2418_ == 0)
{
lean_ctor_set_tag(v___x_2417_, 0);
lean_ctor_set(v___x_2417_, 0, v_a_2420_);
v___x_2425_ = v___x_2417_;
goto v_reusejp_2424_;
}
else
{
lean_object* v_reuseFailAlloc_2429_; 
v_reuseFailAlloc_2429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2429_, 0, v_a_2420_);
v___x_2425_ = v_reuseFailAlloc_2429_;
goto v_reusejp_2424_;
}
v_reusejp_2424_:
{
lean_object* v___x_2427_; 
if (v_isShared_2423_ == 0)
{
lean_ctor_set(v___x_2422_, 0, v___x_2425_);
v___x_2427_ = v___x_2422_;
goto v_reusejp_2426_;
}
else
{
lean_object* v_reuseFailAlloc_2428_; 
v_reuseFailAlloc_2428_ = lean_alloc_ctor(1, 1, 0);
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
}
}
}
}
else
{
lean_object* v___x_2433_; 
v___x_2433_ = lean_apply_1(v___f_2348_, v_a_2373_);
v___y_2370_ = v___x_2433_;
goto v___jp_2369_;
}
}
v___jp_2350_:
{
lean_object* v___x_2351_; 
v___x_2351_ = l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson(v_j_2349_);
if (lean_obj_tag(v___x_2351_) == 0)
{
lean_object* v_a_2352_; lean_object* v___x_2354_; uint8_t v_isShared_2355_; uint8_t v_isSharedCheck_2359_; 
v_a_2352_ = lean_ctor_get(v___x_2351_, 0);
v_isSharedCheck_2359_ = !lean_is_exclusive(v___x_2351_);
if (v_isSharedCheck_2359_ == 0)
{
v___x_2354_ = v___x_2351_;
v_isShared_2355_ = v_isSharedCheck_2359_;
goto v_resetjp_2353_;
}
else
{
lean_inc(v_a_2352_);
lean_dec(v___x_2351_);
v___x_2354_ = lean_box(0);
v_isShared_2355_ = v_isSharedCheck_2359_;
goto v_resetjp_2353_;
}
v_resetjp_2353_:
{
lean_object* v___x_2357_; 
if (v_isShared_2355_ == 0)
{
v___x_2357_ = v___x_2354_;
goto v_reusejp_2356_;
}
else
{
lean_object* v_reuseFailAlloc_2358_; 
v_reuseFailAlloc_2358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2358_, 0, v_a_2352_);
v___x_2357_ = v_reuseFailAlloc_2358_;
goto v_reusejp_2356_;
}
v_reusejp_2356_:
{
return v___x_2357_;
}
}
}
else
{
lean_object* v_a_2360_; lean_object* v___x_2362_; uint8_t v_isShared_2363_; uint8_t v_isSharedCheck_2368_; 
v_a_2360_ = lean_ctor_get(v___x_2351_, 0);
v_isSharedCheck_2368_ = !lean_is_exclusive(v___x_2351_);
if (v_isSharedCheck_2368_ == 0)
{
v___x_2362_ = v___x_2351_;
v_isShared_2363_ = v_isSharedCheck_2368_;
goto v_resetjp_2361_;
}
else
{
lean_inc(v_a_2360_);
lean_dec(v___x_2351_);
v___x_2362_ = lean_box(0);
v_isShared_2363_ = v_isSharedCheck_2368_;
goto v_resetjp_2361_;
}
v_resetjp_2361_:
{
lean_object* v___x_2364_; lean_object* v___x_2366_; 
v___x_2364_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2364_, 0, v_a_2360_);
if (v_isShared_2363_ == 0)
{
lean_ctor_set(v___x_2362_, 0, v___x_2364_);
v___x_2366_ = v___x_2362_;
goto v_reusejp_2365_;
}
else
{
lean_object* v_reuseFailAlloc_2367_; 
v_reuseFailAlloc_2367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2367_, 0, v___x_2364_);
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
v___jp_2369_:
{
if (lean_obj_tag(v___y_2370_) == 0)
{
lean_dec_ref_known(v___y_2370_, 1);
goto v___jp_2350_;
}
else
{
lean_dec(v_j_2349_);
return v___y_2370_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_map___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEdit_toJson_spec__2_spec__4_spec__7(lean_object* v_t_2438_){
_start:
{
if (lean_obj_tag(v_t_2438_) == 0)
{
lean_object* v_size_2439_; lean_object* v_k_2440_; lean_object* v_v_2441_; lean_object* v_l_2442_; lean_object* v_r_2443_; lean_object* v___x_2445_; uint8_t v_isShared_2446_; uint8_t v_isSharedCheck_2453_; 
v_size_2439_ = lean_ctor_get(v_t_2438_, 0);
v_k_2440_ = lean_ctor_get(v_t_2438_, 1);
v_v_2441_ = lean_ctor_get(v_t_2438_, 2);
v_l_2442_ = lean_ctor_get(v_t_2438_, 3);
v_r_2443_ = lean_ctor_get(v_t_2438_, 4);
v_isSharedCheck_2453_ = !lean_is_exclusive(v_t_2438_);
if (v_isSharedCheck_2453_ == 0)
{
v___x_2445_ = v_t_2438_;
v_isShared_2446_ = v_isSharedCheck_2453_;
goto v_resetjp_2444_;
}
else
{
lean_inc(v_r_2443_);
lean_inc(v_l_2442_);
lean_inc(v_v_2441_);
lean_inc(v_k_2440_);
lean_inc(v_size_2439_);
lean_dec(v_t_2438_);
v___x_2445_ = lean_box(0);
v_isShared_2446_ = v_isSharedCheck_2453_;
goto v_resetjp_2444_;
}
v_resetjp_2444_:
{
lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2451_; 
v___x_2447_ = l_Lean_Lsp_instToJsonChangeAnnotation_toJson(v_v_2441_);
v___x_2448_ = l_Std_DTreeMap_Internal_Impl_map___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEdit_toJson_spec__2_spec__4_spec__7(v_l_2442_);
v___x_2449_ = l_Std_DTreeMap_Internal_Impl_map___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEdit_toJson_spec__2_spec__4_spec__7(v_r_2443_);
if (v_isShared_2446_ == 0)
{
lean_ctor_set(v___x_2445_, 4, v___x_2449_);
lean_ctor_set(v___x_2445_, 3, v___x_2448_);
lean_ctor_set(v___x_2445_, 2, v___x_2447_);
v___x_2451_ = v___x_2445_;
goto v_reusejp_2450_;
}
else
{
lean_object* v_reuseFailAlloc_2452_; 
v_reuseFailAlloc_2452_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2452_, 0, v_size_2439_);
lean_ctor_set(v_reuseFailAlloc_2452_, 1, v_k_2440_);
lean_ctor_set(v_reuseFailAlloc_2452_, 2, v___x_2447_);
lean_ctor_set(v_reuseFailAlloc_2452_, 3, v___x_2448_);
lean_ctor_set(v_reuseFailAlloc_2452_, 4, v___x_2449_);
v___x_2451_ = v_reuseFailAlloc_2452_;
goto v_reusejp_2450_;
}
v_reusejp_2450_:
{
return v___x_2451_;
}
}
}
else
{
lean_object* v___x_2454_; 
v___x_2454_ = lean_box(1);
return v___x_2454_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEdit_toJson_spec__2_spec__4(lean_object* v_map_2455_){
_start:
{
lean_object* v___x_2456_; lean_object* v___x_2457_; 
v___x_2456_ = l_Std_DTreeMap_Internal_Impl_map___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEdit_toJson_spec__2_spec__4_spec__7(v_map_2455_);
v___x_2457_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_2457_, 0, v___x_2456_);
return v___x_2457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEdit_toJson_spec__2(lean_object* v_k_2458_, lean_object* v_x_2459_){
_start:
{
if (lean_obj_tag(v_x_2459_) == 0)
{
lean_object* v___x_2460_; 
lean_dec_ref(v_k_2458_);
v___x_2460_ = lean_box(0);
return v___x_2460_;
}
else
{
lean_object* v_val_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; 
v_val_2461_ = lean_ctor_get(v_x_2459_, 0);
lean_inc(v_val_2461_);
lean_dec_ref_known(v_x_2459_, 1);
v___x_2462_ = l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEdit_toJson_spec__2_spec__4(v_val_2461_);
v___x_2463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2463_, 0, v_k_2458_);
lean_ctor_set(v___x_2463_, 1, v___x_2462_);
v___x_2464_ = lean_box(0);
v___x_2465_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2465_, 0, v___x_2463_);
lean_ctor_set(v___x_2465_, 1, v___x_2464_);
return v___x_2465_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEdit_toJson_spec__1_spec__2_spec__4(size_t v_sz_2466_, size_t v_i_2467_, lean_object* v_bs_2468_){
_start:
{
uint8_t v___x_2469_; 
v___x_2469_ = lean_usize_dec_lt(v_i_2467_, v_sz_2466_);
if (v___x_2469_ == 0)
{
return v_bs_2468_;
}
else
{
lean_object* v_v_2470_; lean_object* v___x_2471_; lean_object* v_bs_x27_2472_; lean_object* v___y_2474_; 
v_v_2470_ = lean_array_uget(v_bs_2468_, v_i_2467_);
v___x_2471_ = lean_unsigned_to_nat(0u);
v_bs_x27_2472_ = lean_array_uset(v_bs_2468_, v_i_2467_, v___x_2471_);
switch(lean_obj_tag(v_v_2470_))
{
case 0:
{
lean_object* v_a_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; 
v_a_2479_ = lean_ctor_get(v_v_2470_, 0);
lean_inc_ref(v_a_2479_);
lean_dec_ref_known(v_v_2470_, 1);
v___x_2480_ = l_Lean_Lsp_instToJsonCreateFile_toJson(v_a_2479_);
v___x_2481_ = ((lean_object*)(l_Lean_Lsp_instToJsonDocumentChange___lam__0___closed__0));
v___x_2482_ = ((lean_object*)(l_Lean_Lsp_instToJsonDocumentChange___lam__0___closed__2));
v___x_2483_ = l_Lean_Json_setObjVal_x21(v___x_2480_, v___x_2481_, v___x_2482_);
v___y_2474_ = v___x_2483_;
goto v___jp_2473_;
}
case 1:
{
lean_object* v_a_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; 
v_a_2484_ = lean_ctor_get(v_v_2470_, 0);
lean_inc_ref(v_a_2484_);
lean_dec_ref_known(v_v_2470_, 1);
v___x_2485_ = l_Lean_Lsp_instToJsonRenameFile_toJson(v_a_2484_);
v___x_2486_ = ((lean_object*)(l_Lean_Lsp_instToJsonDocumentChange___lam__0___closed__0));
v___x_2487_ = ((lean_object*)(l_Lean_Lsp_instToJsonDocumentChange___lam__0___closed__4));
v___x_2488_ = l_Lean_Json_setObjVal_x21(v___x_2485_, v___x_2486_, v___x_2487_);
v___y_2474_ = v___x_2488_;
goto v___jp_2473_;
}
case 2:
{
lean_object* v_a_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; 
v_a_2489_ = lean_ctor_get(v_v_2470_, 0);
lean_inc_ref(v_a_2489_);
lean_dec_ref_known(v_v_2470_, 1);
v___x_2490_ = l_Lean_Lsp_instToJsonDeleteFile_toJson(v_a_2489_);
v___x_2491_ = ((lean_object*)(l_Lean_Lsp_instToJsonDocumentChange___lam__0___closed__0));
v___x_2492_ = ((lean_object*)(l_Lean_Lsp_instToJsonDocumentChange___lam__0___closed__6));
v___x_2493_ = l_Lean_Json_setObjVal_x21(v___x_2490_, v___x_2491_, v___x_2492_);
v___y_2474_ = v___x_2493_;
goto v___jp_2473_;
}
default: 
{
lean_object* v_a_2494_; lean_object* v___x_2495_; 
v_a_2494_ = lean_ctor_get(v_v_2470_, 0);
lean_inc_ref(v_a_2494_);
lean_dec_ref_known(v_v_2470_, 1);
v___x_2495_ = l_Lean_Lsp_instToJsonTextDocumentEdit_toJson(v_a_2494_);
v___y_2474_ = v___x_2495_;
goto v___jp_2473_;
}
}
v___jp_2473_:
{
size_t v___x_2475_; size_t v___x_2476_; lean_object* v___x_2477_; 
v___x_2475_ = ((size_t)1ULL);
v___x_2476_ = lean_usize_add(v_i_2467_, v___x_2475_);
v___x_2477_ = lean_array_uset(v_bs_x27_2472_, v_i_2467_, v___y_2474_);
v_i_2467_ = v___x_2476_;
v_bs_2468_ = v___x_2477_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEdit_toJson_spec__1_spec__2_spec__4___boxed(lean_object* v_sz_2496_, lean_object* v_i_2497_, lean_object* v_bs_2498_){
_start:
{
size_t v_sz_boxed_2499_; size_t v_i_boxed_2500_; lean_object* v_res_2501_; 
v_sz_boxed_2499_ = lean_unbox_usize(v_sz_2496_);
lean_dec(v_sz_2496_);
v_i_boxed_2500_ = lean_unbox_usize(v_i_2497_);
lean_dec(v_i_2497_);
v_res_2501_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEdit_toJson_spec__1_spec__2_spec__4(v_sz_boxed_2499_, v_i_boxed_2500_, v_bs_2498_);
return v_res_2501_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEdit_toJson_spec__1_spec__2(lean_object* v_a_2502_){
_start:
{
size_t v_sz_2503_; size_t v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; 
v_sz_2503_ = lean_array_size(v_a_2502_);
v___x_2504_ = ((size_t)0ULL);
v___x_2505_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEdit_toJson_spec__1_spec__2_spec__4(v_sz_2503_, v___x_2504_, v_a_2502_);
v___x_2506_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_2506_, 0, v___x_2505_);
return v___x_2506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEdit_toJson_spec__1(lean_object* v_k_2507_, lean_object* v_x_2508_){
_start:
{
if (lean_obj_tag(v_x_2508_) == 0)
{
lean_object* v___x_2509_; 
lean_dec_ref(v_k_2507_);
v___x_2509_ = lean_box(0);
return v___x_2509_;
}
else
{
lean_object* v_val_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; 
v_val_2510_ = lean_ctor_get(v_x_2508_, 0);
lean_inc(v_val_2510_);
lean_dec_ref_known(v_x_2508_, 1);
v___x_2511_ = l_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEdit_toJson_spec__1_spec__2(v_val_2510_);
v___x_2512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2512_, 0, v_k_2507_);
lean_ctor_set(v___x_2512_, 1, v___x_2511_);
v___x_2513_ = lean_box(0);
v___x_2514_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2514_, 0, v___x_2512_);
lean_ctor_set(v___x_2514_, 1, v___x_2513_);
return v___x_2514_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_map___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEdit_toJson_spec__0_spec__0_spec__1(lean_object* v_t_2515_){
_start:
{
if (lean_obj_tag(v_t_2515_) == 0)
{
lean_object* v_size_2516_; lean_object* v_k_2517_; lean_object* v_v_2518_; lean_object* v_l_2519_; lean_object* v_r_2520_; lean_object* v___x_2522_; uint8_t v_isShared_2523_; uint8_t v_isSharedCheck_2530_; 
v_size_2516_ = lean_ctor_get(v_t_2515_, 0);
v_k_2517_ = lean_ctor_get(v_t_2515_, 1);
v_v_2518_ = lean_ctor_get(v_t_2515_, 2);
v_l_2519_ = lean_ctor_get(v_t_2515_, 3);
v_r_2520_ = lean_ctor_get(v_t_2515_, 4);
v_isSharedCheck_2530_ = !lean_is_exclusive(v_t_2515_);
if (v_isSharedCheck_2530_ == 0)
{
v___x_2522_ = v_t_2515_;
v_isShared_2523_ = v_isSharedCheck_2530_;
goto v_resetjp_2521_;
}
else
{
lean_inc(v_r_2520_);
lean_inc(v_l_2519_);
lean_inc(v_v_2518_);
lean_inc(v_k_2517_);
lean_inc(v_size_2516_);
lean_dec(v_t_2515_);
v___x_2522_ = lean_box(0);
v_isShared_2523_ = v_isSharedCheck_2530_;
goto v_resetjp_2521_;
}
v_resetjp_2521_:
{
lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2528_; 
v___x_2524_ = l_Array_toJson___at___00Lean_Lsp_instToJsonTextDocumentEdit_toJson_spec__0(v_v_2518_);
v___x_2525_ = l_Std_DTreeMap_Internal_Impl_map___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEdit_toJson_spec__0_spec__0_spec__1(v_l_2519_);
v___x_2526_ = l_Std_DTreeMap_Internal_Impl_map___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEdit_toJson_spec__0_spec__0_spec__1(v_r_2520_);
if (v_isShared_2523_ == 0)
{
lean_ctor_set(v___x_2522_, 4, v___x_2526_);
lean_ctor_set(v___x_2522_, 3, v___x_2525_);
lean_ctor_set(v___x_2522_, 2, v___x_2524_);
v___x_2528_ = v___x_2522_;
goto v_reusejp_2527_;
}
else
{
lean_object* v_reuseFailAlloc_2529_; 
v_reuseFailAlloc_2529_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2529_, 0, v_size_2516_);
lean_ctor_set(v_reuseFailAlloc_2529_, 1, v_k_2517_);
lean_ctor_set(v_reuseFailAlloc_2529_, 2, v___x_2524_);
lean_ctor_set(v_reuseFailAlloc_2529_, 3, v___x_2525_);
lean_ctor_set(v_reuseFailAlloc_2529_, 4, v___x_2526_);
v___x_2528_ = v_reuseFailAlloc_2529_;
goto v_reusejp_2527_;
}
v_reusejp_2527_:
{
return v___x_2528_;
}
}
}
else
{
lean_object* v___x_2531_; 
v___x_2531_ = lean_box(1);
return v___x_2531_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEdit_toJson_spec__0_spec__0(lean_object* v_map_2532_){
_start:
{
lean_object* v___x_2533_; lean_object* v___x_2534_; 
v___x_2533_ = l_Std_DTreeMap_Internal_Impl_map___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEdit_toJson_spec__0_spec__0_spec__1(v_map_2532_);
v___x_2534_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_2534_, 0, v___x_2533_);
return v___x_2534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEdit_toJson_spec__0(lean_object* v_k_2535_, lean_object* v_x_2536_){
_start:
{
if (lean_obj_tag(v_x_2536_) == 0)
{
lean_object* v___x_2537_; 
lean_dec_ref(v_k_2535_);
v___x_2537_ = lean_box(0);
return v___x_2537_;
}
else
{
lean_object* v_val_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; 
v_val_2538_ = lean_ctor_get(v_x_2536_, 0);
lean_inc(v_val_2538_);
lean_dec_ref_known(v_x_2536_, 1);
v___x_2539_ = l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEdit_toJson_spec__0_spec__0(v_val_2538_);
v___x_2540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2540_, 0, v_k_2535_);
lean_ctor_set(v___x_2540_, 1, v___x_2539_);
v___x_2541_ = lean_box(0);
v___x_2542_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2542_, 0, v___x_2540_);
lean_ctor_set(v___x_2542_, 1, v___x_2541_);
return v___x_2542_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonWorkspaceEdit_toJson(lean_object* v_x_2546_){
_start:
{
lean_object* v_changes_x3f_2547_; lean_object* v_documentChanges_x3f_2548_; lean_object* v_changeAnnotations_x3f_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; 
v_changes_x3f_2547_ = lean_ctor_get(v_x_2546_, 0);
lean_inc(v_changes_x3f_2547_);
v_documentChanges_x3f_2548_ = lean_ctor_get(v_x_2546_, 1);
lean_inc(v_documentChanges_x3f_2548_);
v_changeAnnotations_x3f_2549_ = lean_ctor_get(v_x_2546_, 2);
lean_inc(v_changeAnnotations_x3f_2549_);
lean_dec_ref(v_x_2546_);
v___x_2550_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkspaceEdit_toJson___closed__0));
v___x_2551_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEdit_toJson_spec__0(v___x_2550_, v_changes_x3f_2547_);
v___x_2552_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkspaceEdit_toJson___closed__1));
v___x_2553_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEdit_toJson_spec__1(v___x_2552_, v_documentChanges_x3f_2548_);
v___x_2554_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkspaceEdit_toJson___closed__2));
v___x_2555_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEdit_toJson_spec__2(v___x_2554_, v_changeAnnotations_x3f_2549_);
v___x_2556_ = lean_box(0);
v___x_2557_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2557_, 0, v___x_2555_);
lean_ctor_set(v___x_2557_, 1, v___x_2556_);
v___x_2558_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2558_, 0, v___x_2553_);
lean_ctor_set(v___x_2558_, 1, v___x_2557_);
v___x_2559_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2559_, 0, v___x_2551_);
lean_ctor_set(v___x_2559_, 1, v___x_2558_);
v___x_2560_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__2));
v___x_2561_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLocation_toJson_spec__0(v___x_2559_, v___x_2560_);
v___x_2562_ = l_Lean_Json_mkObj(v___x_2561_);
lean_dec(v___x_2561_);
return v___x_2562_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__1_spec__2_spec__4_spec__7___redArg(lean_object* v_cmp_2565_, lean_object* v_k_2566_, lean_object* v_v_2567_, lean_object* v_t_2568_){
_start:
{
if (lean_obj_tag(v_t_2568_) == 0)
{
lean_object* v_size_2569_; lean_object* v_k_2570_; lean_object* v_v_2571_; lean_object* v_l_2572_; lean_object* v_r_2573_; lean_object* v___x_2575_; uint8_t v_isShared_2576_; uint8_t v_isSharedCheck_2854_; 
v_size_2569_ = lean_ctor_get(v_t_2568_, 0);
v_k_2570_ = lean_ctor_get(v_t_2568_, 1);
v_v_2571_ = lean_ctor_get(v_t_2568_, 2);
v_l_2572_ = lean_ctor_get(v_t_2568_, 3);
v_r_2573_ = lean_ctor_get(v_t_2568_, 4);
v_isSharedCheck_2854_ = !lean_is_exclusive(v_t_2568_);
if (v_isSharedCheck_2854_ == 0)
{
v___x_2575_ = v_t_2568_;
v_isShared_2576_ = v_isSharedCheck_2854_;
goto v_resetjp_2574_;
}
else
{
lean_inc(v_r_2573_);
lean_inc(v_l_2572_);
lean_inc(v_v_2571_);
lean_inc(v_k_2570_);
lean_inc(v_size_2569_);
lean_dec(v_t_2568_);
v___x_2575_ = lean_box(0);
v_isShared_2576_ = v_isSharedCheck_2854_;
goto v_resetjp_2574_;
}
v_resetjp_2574_:
{
lean_object* v___x_2577_; uint8_t v___x_2578_; 
lean_inc_ref(v_cmp_2565_);
lean_inc(v_k_2570_);
lean_inc_ref(v_k_2566_);
v___x_2577_ = lean_apply_2(v_cmp_2565_, v_k_2566_, v_k_2570_);
v___x_2578_ = lean_unbox(v___x_2577_);
switch(v___x_2578_)
{
case 0:
{
lean_object* v_impl_2579_; lean_object* v___x_2580_; 
lean_dec(v_size_2569_);
v_impl_2579_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__1_spec__2_spec__4_spec__7___redArg(v_cmp_2565_, v_k_2566_, v_v_2567_, v_l_2572_);
v___x_2580_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_2573_) == 0)
{
lean_object* v_size_2581_; lean_object* v_size_2582_; lean_object* v_k_2583_; lean_object* v_v_2584_; lean_object* v_l_2585_; lean_object* v_r_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; uint8_t v___x_2589_; 
v_size_2581_ = lean_ctor_get(v_r_2573_, 0);
v_size_2582_ = lean_ctor_get(v_impl_2579_, 0);
lean_inc(v_size_2582_);
v_k_2583_ = lean_ctor_get(v_impl_2579_, 1);
lean_inc(v_k_2583_);
v_v_2584_ = lean_ctor_get(v_impl_2579_, 2);
lean_inc(v_v_2584_);
v_l_2585_ = lean_ctor_get(v_impl_2579_, 3);
lean_inc(v_l_2585_);
v_r_2586_ = lean_ctor_get(v_impl_2579_, 4);
lean_inc(v_r_2586_);
v___x_2587_ = lean_unsigned_to_nat(3u);
v___x_2588_ = lean_nat_mul(v___x_2587_, v_size_2581_);
v___x_2589_ = lean_nat_dec_lt(v___x_2588_, v_size_2582_);
lean_dec(v___x_2588_);
if (v___x_2589_ == 0)
{
lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2593_; 
lean_dec(v_r_2586_);
lean_dec(v_l_2585_);
lean_dec(v_v_2584_);
lean_dec(v_k_2583_);
v___x_2590_ = lean_nat_add(v___x_2580_, v_size_2582_);
lean_dec(v_size_2582_);
v___x_2591_ = lean_nat_add(v___x_2590_, v_size_2581_);
lean_dec(v___x_2590_);
if (v_isShared_2576_ == 0)
{
lean_ctor_set(v___x_2575_, 3, v_impl_2579_);
lean_ctor_set(v___x_2575_, 0, v___x_2591_);
v___x_2593_ = v___x_2575_;
goto v_reusejp_2592_;
}
else
{
lean_object* v_reuseFailAlloc_2594_; 
v_reuseFailAlloc_2594_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2594_, 0, v___x_2591_);
lean_ctor_set(v_reuseFailAlloc_2594_, 1, v_k_2570_);
lean_ctor_set(v_reuseFailAlloc_2594_, 2, v_v_2571_);
lean_ctor_set(v_reuseFailAlloc_2594_, 3, v_impl_2579_);
lean_ctor_set(v_reuseFailAlloc_2594_, 4, v_r_2573_);
v___x_2593_ = v_reuseFailAlloc_2594_;
goto v_reusejp_2592_;
}
v_reusejp_2592_:
{
return v___x_2593_;
}
}
else
{
lean_object* v___x_2596_; uint8_t v_isShared_2597_; uint8_t v_isSharedCheck_2660_; 
v_isSharedCheck_2660_ = !lean_is_exclusive(v_impl_2579_);
if (v_isSharedCheck_2660_ == 0)
{
lean_object* v_unused_2661_; lean_object* v_unused_2662_; lean_object* v_unused_2663_; lean_object* v_unused_2664_; lean_object* v_unused_2665_; 
v_unused_2661_ = lean_ctor_get(v_impl_2579_, 4);
lean_dec(v_unused_2661_);
v_unused_2662_ = lean_ctor_get(v_impl_2579_, 3);
lean_dec(v_unused_2662_);
v_unused_2663_ = lean_ctor_get(v_impl_2579_, 2);
lean_dec(v_unused_2663_);
v_unused_2664_ = lean_ctor_get(v_impl_2579_, 1);
lean_dec(v_unused_2664_);
v_unused_2665_ = lean_ctor_get(v_impl_2579_, 0);
lean_dec(v_unused_2665_);
v___x_2596_ = v_impl_2579_;
v_isShared_2597_ = v_isSharedCheck_2660_;
goto v_resetjp_2595_;
}
else
{
lean_dec(v_impl_2579_);
v___x_2596_ = lean_box(0);
v_isShared_2597_ = v_isSharedCheck_2660_;
goto v_resetjp_2595_;
}
v_resetjp_2595_:
{
lean_object* v_size_2598_; lean_object* v_size_2599_; lean_object* v_k_2600_; lean_object* v_v_2601_; lean_object* v_l_2602_; lean_object* v_r_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; uint8_t v___x_2606_; 
v_size_2598_ = lean_ctor_get(v_l_2585_, 0);
v_size_2599_ = lean_ctor_get(v_r_2586_, 0);
v_k_2600_ = lean_ctor_get(v_r_2586_, 1);
v_v_2601_ = lean_ctor_get(v_r_2586_, 2);
v_l_2602_ = lean_ctor_get(v_r_2586_, 3);
v_r_2603_ = lean_ctor_get(v_r_2586_, 4);
v___x_2604_ = lean_unsigned_to_nat(2u);
v___x_2605_ = lean_nat_mul(v___x_2604_, v_size_2598_);
v___x_2606_ = lean_nat_dec_lt(v_size_2599_, v___x_2605_);
lean_dec(v___x_2605_);
if (v___x_2606_ == 0)
{
lean_object* v___x_2608_; uint8_t v_isShared_2609_; uint8_t v_isSharedCheck_2635_; 
lean_inc(v_r_2603_);
lean_inc(v_l_2602_);
lean_inc(v_v_2601_);
lean_inc(v_k_2600_);
v_isSharedCheck_2635_ = !lean_is_exclusive(v_r_2586_);
if (v_isSharedCheck_2635_ == 0)
{
lean_object* v_unused_2636_; lean_object* v_unused_2637_; lean_object* v_unused_2638_; lean_object* v_unused_2639_; lean_object* v_unused_2640_; 
v_unused_2636_ = lean_ctor_get(v_r_2586_, 4);
lean_dec(v_unused_2636_);
v_unused_2637_ = lean_ctor_get(v_r_2586_, 3);
lean_dec(v_unused_2637_);
v_unused_2638_ = lean_ctor_get(v_r_2586_, 2);
lean_dec(v_unused_2638_);
v_unused_2639_ = lean_ctor_get(v_r_2586_, 1);
lean_dec(v_unused_2639_);
v_unused_2640_ = lean_ctor_get(v_r_2586_, 0);
lean_dec(v_unused_2640_);
v___x_2608_ = v_r_2586_;
v_isShared_2609_ = v_isSharedCheck_2635_;
goto v_resetjp_2607_;
}
else
{
lean_dec(v_r_2586_);
v___x_2608_ = lean_box(0);
v_isShared_2609_ = v_isSharedCheck_2635_;
goto v_resetjp_2607_;
}
v_resetjp_2607_:
{
lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___y_2613_; lean_object* v___y_2614_; lean_object* v___y_2615_; lean_object* v___x_2623_; lean_object* v___y_2625_; 
v___x_2610_ = lean_nat_add(v___x_2580_, v_size_2582_);
lean_dec(v_size_2582_);
v___x_2611_ = lean_nat_add(v___x_2610_, v_size_2581_);
lean_dec(v___x_2610_);
v___x_2623_ = lean_nat_add(v___x_2580_, v_size_2598_);
if (lean_obj_tag(v_l_2602_) == 0)
{
lean_object* v_size_2633_; 
v_size_2633_ = lean_ctor_get(v_l_2602_, 0);
lean_inc(v_size_2633_);
v___y_2625_ = v_size_2633_;
goto v___jp_2624_;
}
else
{
lean_object* v___x_2634_; 
v___x_2634_ = lean_unsigned_to_nat(0u);
v___y_2625_ = v___x_2634_;
goto v___jp_2624_;
}
v___jp_2612_:
{
lean_object* v___x_2616_; lean_object* v___x_2618_; 
v___x_2616_ = lean_nat_add(v___y_2614_, v___y_2615_);
lean_dec(v___y_2615_);
lean_dec(v___y_2614_);
if (v_isShared_2609_ == 0)
{
lean_ctor_set(v___x_2608_, 4, v_r_2573_);
lean_ctor_set(v___x_2608_, 3, v_r_2603_);
lean_ctor_set(v___x_2608_, 2, v_v_2571_);
lean_ctor_set(v___x_2608_, 1, v_k_2570_);
lean_ctor_set(v___x_2608_, 0, v___x_2616_);
v___x_2618_ = v___x_2608_;
goto v_reusejp_2617_;
}
else
{
lean_object* v_reuseFailAlloc_2622_; 
v_reuseFailAlloc_2622_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2622_, 0, v___x_2616_);
lean_ctor_set(v_reuseFailAlloc_2622_, 1, v_k_2570_);
lean_ctor_set(v_reuseFailAlloc_2622_, 2, v_v_2571_);
lean_ctor_set(v_reuseFailAlloc_2622_, 3, v_r_2603_);
lean_ctor_set(v_reuseFailAlloc_2622_, 4, v_r_2573_);
v___x_2618_ = v_reuseFailAlloc_2622_;
goto v_reusejp_2617_;
}
v_reusejp_2617_:
{
lean_object* v___x_2620_; 
if (v_isShared_2597_ == 0)
{
lean_ctor_set(v___x_2596_, 4, v___x_2618_);
lean_ctor_set(v___x_2596_, 3, v___y_2613_);
lean_ctor_set(v___x_2596_, 2, v_v_2601_);
lean_ctor_set(v___x_2596_, 1, v_k_2600_);
lean_ctor_set(v___x_2596_, 0, v___x_2611_);
v___x_2620_ = v___x_2596_;
goto v_reusejp_2619_;
}
else
{
lean_object* v_reuseFailAlloc_2621_; 
v_reuseFailAlloc_2621_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2621_, 0, v___x_2611_);
lean_ctor_set(v_reuseFailAlloc_2621_, 1, v_k_2600_);
lean_ctor_set(v_reuseFailAlloc_2621_, 2, v_v_2601_);
lean_ctor_set(v_reuseFailAlloc_2621_, 3, v___y_2613_);
lean_ctor_set(v_reuseFailAlloc_2621_, 4, v___x_2618_);
v___x_2620_ = v_reuseFailAlloc_2621_;
goto v_reusejp_2619_;
}
v_reusejp_2619_:
{
return v___x_2620_;
}
}
}
v___jp_2624_:
{
lean_object* v___x_2626_; lean_object* v___x_2628_; 
v___x_2626_ = lean_nat_add(v___x_2623_, v___y_2625_);
lean_dec(v___y_2625_);
lean_dec(v___x_2623_);
if (v_isShared_2576_ == 0)
{
lean_ctor_set(v___x_2575_, 4, v_l_2602_);
lean_ctor_set(v___x_2575_, 3, v_l_2585_);
lean_ctor_set(v___x_2575_, 2, v_v_2584_);
lean_ctor_set(v___x_2575_, 1, v_k_2583_);
lean_ctor_set(v___x_2575_, 0, v___x_2626_);
v___x_2628_ = v___x_2575_;
goto v_reusejp_2627_;
}
else
{
lean_object* v_reuseFailAlloc_2632_; 
v_reuseFailAlloc_2632_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2632_, 0, v___x_2626_);
lean_ctor_set(v_reuseFailAlloc_2632_, 1, v_k_2583_);
lean_ctor_set(v_reuseFailAlloc_2632_, 2, v_v_2584_);
lean_ctor_set(v_reuseFailAlloc_2632_, 3, v_l_2585_);
lean_ctor_set(v_reuseFailAlloc_2632_, 4, v_l_2602_);
v___x_2628_ = v_reuseFailAlloc_2632_;
goto v_reusejp_2627_;
}
v_reusejp_2627_:
{
lean_object* v___x_2629_; 
v___x_2629_ = lean_nat_add(v___x_2580_, v_size_2581_);
if (lean_obj_tag(v_r_2603_) == 0)
{
lean_object* v_size_2630_; 
v_size_2630_ = lean_ctor_get(v_r_2603_, 0);
lean_inc(v_size_2630_);
v___y_2613_ = v___x_2628_;
v___y_2614_ = v___x_2629_;
v___y_2615_ = v_size_2630_;
goto v___jp_2612_;
}
else
{
lean_object* v___x_2631_; 
v___x_2631_ = lean_unsigned_to_nat(0u);
v___y_2613_ = v___x_2628_;
v___y_2614_ = v___x_2629_;
v___y_2615_ = v___x_2631_;
goto v___jp_2612_;
}
}
}
}
}
else
{
lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2646_; 
lean_del_object(v___x_2575_);
v___x_2641_ = lean_nat_add(v___x_2580_, v_size_2582_);
lean_dec(v_size_2582_);
v___x_2642_ = lean_nat_add(v___x_2641_, v_size_2581_);
lean_dec(v___x_2641_);
v___x_2643_ = lean_nat_add(v___x_2580_, v_size_2581_);
v___x_2644_ = lean_nat_add(v___x_2643_, v_size_2599_);
lean_dec(v___x_2643_);
lean_inc_ref(v_r_2573_);
if (v_isShared_2597_ == 0)
{
lean_ctor_set(v___x_2596_, 4, v_r_2573_);
lean_ctor_set(v___x_2596_, 3, v_r_2586_);
lean_ctor_set(v___x_2596_, 2, v_v_2571_);
lean_ctor_set(v___x_2596_, 1, v_k_2570_);
lean_ctor_set(v___x_2596_, 0, v___x_2644_);
v___x_2646_ = v___x_2596_;
goto v_reusejp_2645_;
}
else
{
lean_object* v_reuseFailAlloc_2659_; 
v_reuseFailAlloc_2659_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2659_, 0, v___x_2644_);
lean_ctor_set(v_reuseFailAlloc_2659_, 1, v_k_2570_);
lean_ctor_set(v_reuseFailAlloc_2659_, 2, v_v_2571_);
lean_ctor_set(v_reuseFailAlloc_2659_, 3, v_r_2586_);
lean_ctor_set(v_reuseFailAlloc_2659_, 4, v_r_2573_);
v___x_2646_ = v_reuseFailAlloc_2659_;
goto v_reusejp_2645_;
}
v_reusejp_2645_:
{
lean_object* v___x_2648_; uint8_t v_isShared_2649_; uint8_t v_isSharedCheck_2653_; 
v_isSharedCheck_2653_ = !lean_is_exclusive(v_r_2573_);
if (v_isSharedCheck_2653_ == 0)
{
lean_object* v_unused_2654_; lean_object* v_unused_2655_; lean_object* v_unused_2656_; lean_object* v_unused_2657_; lean_object* v_unused_2658_; 
v_unused_2654_ = lean_ctor_get(v_r_2573_, 4);
lean_dec(v_unused_2654_);
v_unused_2655_ = lean_ctor_get(v_r_2573_, 3);
lean_dec(v_unused_2655_);
v_unused_2656_ = lean_ctor_get(v_r_2573_, 2);
lean_dec(v_unused_2656_);
v_unused_2657_ = lean_ctor_get(v_r_2573_, 1);
lean_dec(v_unused_2657_);
v_unused_2658_ = lean_ctor_get(v_r_2573_, 0);
lean_dec(v_unused_2658_);
v___x_2648_ = v_r_2573_;
v_isShared_2649_ = v_isSharedCheck_2653_;
goto v_resetjp_2647_;
}
else
{
lean_dec(v_r_2573_);
v___x_2648_ = lean_box(0);
v_isShared_2649_ = v_isSharedCheck_2653_;
goto v_resetjp_2647_;
}
v_resetjp_2647_:
{
lean_object* v___x_2651_; 
if (v_isShared_2649_ == 0)
{
lean_ctor_set(v___x_2648_, 4, v___x_2646_);
lean_ctor_set(v___x_2648_, 3, v_l_2585_);
lean_ctor_set(v___x_2648_, 2, v_v_2584_);
lean_ctor_set(v___x_2648_, 1, v_k_2583_);
lean_ctor_set(v___x_2648_, 0, v___x_2642_);
v___x_2651_ = v___x_2648_;
goto v_reusejp_2650_;
}
else
{
lean_object* v_reuseFailAlloc_2652_; 
v_reuseFailAlloc_2652_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2652_, 0, v___x_2642_);
lean_ctor_set(v_reuseFailAlloc_2652_, 1, v_k_2583_);
lean_ctor_set(v_reuseFailAlloc_2652_, 2, v_v_2584_);
lean_ctor_set(v_reuseFailAlloc_2652_, 3, v_l_2585_);
lean_ctor_set(v_reuseFailAlloc_2652_, 4, v___x_2646_);
v___x_2651_ = v_reuseFailAlloc_2652_;
goto v_reusejp_2650_;
}
v_reusejp_2650_:
{
return v___x_2651_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2666_; 
v_l_2666_ = lean_ctor_get(v_impl_2579_, 3);
lean_inc(v_l_2666_);
if (lean_obj_tag(v_l_2666_) == 0)
{
lean_object* v_r_2667_; lean_object* v_k_2668_; lean_object* v_v_2669_; lean_object* v___x_2671_; uint8_t v_isShared_2672_; uint8_t v_isSharedCheck_2680_; 
v_r_2667_ = lean_ctor_get(v_impl_2579_, 4);
v_k_2668_ = lean_ctor_get(v_impl_2579_, 1);
v_v_2669_ = lean_ctor_get(v_impl_2579_, 2);
v_isSharedCheck_2680_ = !lean_is_exclusive(v_impl_2579_);
if (v_isSharedCheck_2680_ == 0)
{
lean_object* v_unused_2681_; lean_object* v_unused_2682_; 
v_unused_2681_ = lean_ctor_get(v_impl_2579_, 3);
lean_dec(v_unused_2681_);
v_unused_2682_ = lean_ctor_get(v_impl_2579_, 0);
lean_dec(v_unused_2682_);
v___x_2671_ = v_impl_2579_;
v_isShared_2672_ = v_isSharedCheck_2680_;
goto v_resetjp_2670_;
}
else
{
lean_inc(v_r_2667_);
lean_inc(v_v_2669_);
lean_inc(v_k_2668_);
lean_dec(v_impl_2579_);
v___x_2671_ = lean_box(0);
v_isShared_2672_ = v_isSharedCheck_2680_;
goto v_resetjp_2670_;
}
v_resetjp_2670_:
{
lean_object* v___x_2673_; lean_object* v___x_2675_; 
v___x_2673_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_2667_);
if (v_isShared_2672_ == 0)
{
lean_ctor_set(v___x_2671_, 3, v_r_2667_);
lean_ctor_set(v___x_2671_, 2, v_v_2571_);
lean_ctor_set(v___x_2671_, 1, v_k_2570_);
lean_ctor_set(v___x_2671_, 0, v___x_2580_);
v___x_2675_ = v___x_2671_;
goto v_reusejp_2674_;
}
else
{
lean_object* v_reuseFailAlloc_2679_; 
v_reuseFailAlloc_2679_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2679_, 0, v___x_2580_);
lean_ctor_set(v_reuseFailAlloc_2679_, 1, v_k_2570_);
lean_ctor_set(v_reuseFailAlloc_2679_, 2, v_v_2571_);
lean_ctor_set(v_reuseFailAlloc_2679_, 3, v_r_2667_);
lean_ctor_set(v_reuseFailAlloc_2679_, 4, v_r_2667_);
v___x_2675_ = v_reuseFailAlloc_2679_;
goto v_reusejp_2674_;
}
v_reusejp_2674_:
{
lean_object* v___x_2677_; 
if (v_isShared_2576_ == 0)
{
lean_ctor_set(v___x_2575_, 4, v___x_2675_);
lean_ctor_set(v___x_2575_, 3, v_l_2666_);
lean_ctor_set(v___x_2575_, 2, v_v_2669_);
lean_ctor_set(v___x_2575_, 1, v_k_2668_);
lean_ctor_set(v___x_2575_, 0, v___x_2673_);
v___x_2677_ = v___x_2575_;
goto v_reusejp_2676_;
}
else
{
lean_object* v_reuseFailAlloc_2678_; 
v_reuseFailAlloc_2678_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2678_, 0, v___x_2673_);
lean_ctor_set(v_reuseFailAlloc_2678_, 1, v_k_2668_);
lean_ctor_set(v_reuseFailAlloc_2678_, 2, v_v_2669_);
lean_ctor_set(v_reuseFailAlloc_2678_, 3, v_l_2666_);
lean_ctor_set(v_reuseFailAlloc_2678_, 4, v___x_2675_);
v___x_2677_ = v_reuseFailAlloc_2678_;
goto v_reusejp_2676_;
}
v_reusejp_2676_:
{
return v___x_2677_;
}
}
}
}
else
{
lean_object* v_r_2683_; 
v_r_2683_ = lean_ctor_get(v_impl_2579_, 4);
lean_inc(v_r_2683_);
if (lean_obj_tag(v_r_2683_) == 0)
{
lean_object* v_k_2684_; lean_object* v_v_2685_; lean_object* v___x_2687_; uint8_t v_isShared_2688_; uint8_t v_isSharedCheck_2708_; 
v_k_2684_ = lean_ctor_get(v_impl_2579_, 1);
v_v_2685_ = lean_ctor_get(v_impl_2579_, 2);
v_isSharedCheck_2708_ = !lean_is_exclusive(v_impl_2579_);
if (v_isSharedCheck_2708_ == 0)
{
lean_object* v_unused_2709_; lean_object* v_unused_2710_; lean_object* v_unused_2711_; 
v_unused_2709_ = lean_ctor_get(v_impl_2579_, 4);
lean_dec(v_unused_2709_);
v_unused_2710_ = lean_ctor_get(v_impl_2579_, 3);
lean_dec(v_unused_2710_);
v_unused_2711_ = lean_ctor_get(v_impl_2579_, 0);
lean_dec(v_unused_2711_);
v___x_2687_ = v_impl_2579_;
v_isShared_2688_ = v_isSharedCheck_2708_;
goto v_resetjp_2686_;
}
else
{
lean_inc(v_v_2685_);
lean_inc(v_k_2684_);
lean_dec(v_impl_2579_);
v___x_2687_ = lean_box(0);
v_isShared_2688_ = v_isSharedCheck_2708_;
goto v_resetjp_2686_;
}
v_resetjp_2686_:
{
lean_object* v_k_2689_; lean_object* v_v_2690_; lean_object* v___x_2692_; uint8_t v_isShared_2693_; uint8_t v_isSharedCheck_2704_; 
v_k_2689_ = lean_ctor_get(v_r_2683_, 1);
v_v_2690_ = lean_ctor_get(v_r_2683_, 2);
v_isSharedCheck_2704_ = !lean_is_exclusive(v_r_2683_);
if (v_isSharedCheck_2704_ == 0)
{
lean_object* v_unused_2705_; lean_object* v_unused_2706_; lean_object* v_unused_2707_; 
v_unused_2705_ = lean_ctor_get(v_r_2683_, 4);
lean_dec(v_unused_2705_);
v_unused_2706_ = lean_ctor_get(v_r_2683_, 3);
lean_dec(v_unused_2706_);
v_unused_2707_ = lean_ctor_get(v_r_2683_, 0);
lean_dec(v_unused_2707_);
v___x_2692_ = v_r_2683_;
v_isShared_2693_ = v_isSharedCheck_2704_;
goto v_resetjp_2691_;
}
else
{
lean_inc(v_v_2690_);
lean_inc(v_k_2689_);
lean_dec(v_r_2683_);
v___x_2692_ = lean_box(0);
v_isShared_2693_ = v_isSharedCheck_2704_;
goto v_resetjp_2691_;
}
v_resetjp_2691_:
{
lean_object* v___x_2694_; lean_object* v___x_2696_; 
v___x_2694_ = lean_unsigned_to_nat(3u);
if (v_isShared_2693_ == 0)
{
lean_ctor_set(v___x_2692_, 4, v_l_2666_);
lean_ctor_set(v___x_2692_, 3, v_l_2666_);
lean_ctor_set(v___x_2692_, 2, v_v_2685_);
lean_ctor_set(v___x_2692_, 1, v_k_2684_);
lean_ctor_set(v___x_2692_, 0, v___x_2580_);
v___x_2696_ = v___x_2692_;
goto v_reusejp_2695_;
}
else
{
lean_object* v_reuseFailAlloc_2703_; 
v_reuseFailAlloc_2703_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2703_, 0, v___x_2580_);
lean_ctor_set(v_reuseFailAlloc_2703_, 1, v_k_2684_);
lean_ctor_set(v_reuseFailAlloc_2703_, 2, v_v_2685_);
lean_ctor_set(v_reuseFailAlloc_2703_, 3, v_l_2666_);
lean_ctor_set(v_reuseFailAlloc_2703_, 4, v_l_2666_);
v___x_2696_ = v_reuseFailAlloc_2703_;
goto v_reusejp_2695_;
}
v_reusejp_2695_:
{
lean_object* v___x_2698_; 
if (v_isShared_2688_ == 0)
{
lean_ctor_set(v___x_2687_, 4, v_l_2666_);
lean_ctor_set(v___x_2687_, 2, v_v_2571_);
lean_ctor_set(v___x_2687_, 1, v_k_2570_);
lean_ctor_set(v___x_2687_, 0, v___x_2580_);
v___x_2698_ = v___x_2687_;
goto v_reusejp_2697_;
}
else
{
lean_object* v_reuseFailAlloc_2702_; 
v_reuseFailAlloc_2702_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2702_, 0, v___x_2580_);
lean_ctor_set(v_reuseFailAlloc_2702_, 1, v_k_2570_);
lean_ctor_set(v_reuseFailAlloc_2702_, 2, v_v_2571_);
lean_ctor_set(v_reuseFailAlloc_2702_, 3, v_l_2666_);
lean_ctor_set(v_reuseFailAlloc_2702_, 4, v_l_2666_);
v___x_2698_ = v_reuseFailAlloc_2702_;
goto v_reusejp_2697_;
}
v_reusejp_2697_:
{
lean_object* v___x_2700_; 
if (v_isShared_2576_ == 0)
{
lean_ctor_set(v___x_2575_, 4, v___x_2698_);
lean_ctor_set(v___x_2575_, 3, v___x_2696_);
lean_ctor_set(v___x_2575_, 2, v_v_2690_);
lean_ctor_set(v___x_2575_, 1, v_k_2689_);
lean_ctor_set(v___x_2575_, 0, v___x_2694_);
v___x_2700_ = v___x_2575_;
goto v_reusejp_2699_;
}
else
{
lean_object* v_reuseFailAlloc_2701_; 
v_reuseFailAlloc_2701_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2701_, 0, v___x_2694_);
lean_ctor_set(v_reuseFailAlloc_2701_, 1, v_k_2689_);
lean_ctor_set(v_reuseFailAlloc_2701_, 2, v_v_2690_);
lean_ctor_set(v_reuseFailAlloc_2701_, 3, v___x_2696_);
lean_ctor_set(v_reuseFailAlloc_2701_, 4, v___x_2698_);
v___x_2700_ = v_reuseFailAlloc_2701_;
goto v_reusejp_2699_;
}
v_reusejp_2699_:
{
return v___x_2700_;
}
}
}
}
}
}
else
{
lean_object* v___x_2712_; lean_object* v___x_2714_; 
v___x_2712_ = lean_unsigned_to_nat(2u);
if (v_isShared_2576_ == 0)
{
lean_ctor_set(v___x_2575_, 4, v_r_2683_);
lean_ctor_set(v___x_2575_, 3, v_impl_2579_);
lean_ctor_set(v___x_2575_, 0, v___x_2712_);
v___x_2714_ = v___x_2575_;
goto v_reusejp_2713_;
}
else
{
lean_object* v_reuseFailAlloc_2715_; 
v_reuseFailAlloc_2715_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2715_, 0, v___x_2712_);
lean_ctor_set(v_reuseFailAlloc_2715_, 1, v_k_2570_);
lean_ctor_set(v_reuseFailAlloc_2715_, 2, v_v_2571_);
lean_ctor_set(v_reuseFailAlloc_2715_, 3, v_impl_2579_);
lean_ctor_set(v_reuseFailAlloc_2715_, 4, v_r_2683_);
v___x_2714_ = v_reuseFailAlloc_2715_;
goto v_reusejp_2713_;
}
v_reusejp_2713_:
{
return v___x_2714_;
}
}
}
}
}
case 1:
{
lean_object* v___x_2717_; 
lean_dec(v_v_2571_);
lean_dec(v_k_2570_);
lean_dec_ref(v_cmp_2565_);
if (v_isShared_2576_ == 0)
{
lean_ctor_set(v___x_2575_, 2, v_v_2567_);
lean_ctor_set(v___x_2575_, 1, v_k_2566_);
v___x_2717_ = v___x_2575_;
goto v_reusejp_2716_;
}
else
{
lean_object* v_reuseFailAlloc_2718_; 
v_reuseFailAlloc_2718_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2718_, 0, v_size_2569_);
lean_ctor_set(v_reuseFailAlloc_2718_, 1, v_k_2566_);
lean_ctor_set(v_reuseFailAlloc_2718_, 2, v_v_2567_);
lean_ctor_set(v_reuseFailAlloc_2718_, 3, v_l_2572_);
lean_ctor_set(v_reuseFailAlloc_2718_, 4, v_r_2573_);
v___x_2717_ = v_reuseFailAlloc_2718_;
goto v_reusejp_2716_;
}
v_reusejp_2716_:
{
return v___x_2717_;
}
}
default: 
{
lean_object* v_impl_2719_; lean_object* v___x_2720_; 
lean_dec(v_size_2569_);
v_impl_2719_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__1_spec__2_spec__4_spec__7___redArg(v_cmp_2565_, v_k_2566_, v_v_2567_, v_r_2573_);
v___x_2720_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_2572_) == 0)
{
lean_object* v_size_2721_; lean_object* v_size_2722_; lean_object* v_k_2723_; lean_object* v_v_2724_; lean_object* v_l_2725_; lean_object* v_r_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; uint8_t v___x_2729_; 
v_size_2721_ = lean_ctor_get(v_l_2572_, 0);
v_size_2722_ = lean_ctor_get(v_impl_2719_, 0);
lean_inc(v_size_2722_);
v_k_2723_ = lean_ctor_get(v_impl_2719_, 1);
lean_inc(v_k_2723_);
v_v_2724_ = lean_ctor_get(v_impl_2719_, 2);
lean_inc(v_v_2724_);
v_l_2725_ = lean_ctor_get(v_impl_2719_, 3);
lean_inc(v_l_2725_);
v_r_2726_ = lean_ctor_get(v_impl_2719_, 4);
lean_inc(v_r_2726_);
v___x_2727_ = lean_unsigned_to_nat(3u);
v___x_2728_ = lean_nat_mul(v___x_2727_, v_size_2721_);
v___x_2729_ = lean_nat_dec_lt(v___x_2728_, v_size_2722_);
lean_dec(v___x_2728_);
if (v___x_2729_ == 0)
{
lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2733_; 
lean_dec(v_r_2726_);
lean_dec(v_l_2725_);
lean_dec(v_v_2724_);
lean_dec(v_k_2723_);
v___x_2730_ = lean_nat_add(v___x_2720_, v_size_2721_);
v___x_2731_ = lean_nat_add(v___x_2730_, v_size_2722_);
lean_dec(v_size_2722_);
lean_dec(v___x_2730_);
if (v_isShared_2576_ == 0)
{
lean_ctor_set(v___x_2575_, 4, v_impl_2719_);
lean_ctor_set(v___x_2575_, 0, v___x_2731_);
v___x_2733_ = v___x_2575_;
goto v_reusejp_2732_;
}
else
{
lean_object* v_reuseFailAlloc_2734_; 
v_reuseFailAlloc_2734_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2734_, 0, v___x_2731_);
lean_ctor_set(v_reuseFailAlloc_2734_, 1, v_k_2570_);
lean_ctor_set(v_reuseFailAlloc_2734_, 2, v_v_2571_);
lean_ctor_set(v_reuseFailAlloc_2734_, 3, v_l_2572_);
lean_ctor_set(v_reuseFailAlloc_2734_, 4, v_impl_2719_);
v___x_2733_ = v_reuseFailAlloc_2734_;
goto v_reusejp_2732_;
}
v_reusejp_2732_:
{
return v___x_2733_;
}
}
else
{
lean_object* v___x_2736_; uint8_t v_isShared_2737_; uint8_t v_isSharedCheck_2798_; 
v_isSharedCheck_2798_ = !lean_is_exclusive(v_impl_2719_);
if (v_isSharedCheck_2798_ == 0)
{
lean_object* v_unused_2799_; lean_object* v_unused_2800_; lean_object* v_unused_2801_; lean_object* v_unused_2802_; lean_object* v_unused_2803_; 
v_unused_2799_ = lean_ctor_get(v_impl_2719_, 4);
lean_dec(v_unused_2799_);
v_unused_2800_ = lean_ctor_get(v_impl_2719_, 3);
lean_dec(v_unused_2800_);
v_unused_2801_ = lean_ctor_get(v_impl_2719_, 2);
lean_dec(v_unused_2801_);
v_unused_2802_ = lean_ctor_get(v_impl_2719_, 1);
lean_dec(v_unused_2802_);
v_unused_2803_ = lean_ctor_get(v_impl_2719_, 0);
lean_dec(v_unused_2803_);
v___x_2736_ = v_impl_2719_;
v_isShared_2737_ = v_isSharedCheck_2798_;
goto v_resetjp_2735_;
}
else
{
lean_dec(v_impl_2719_);
v___x_2736_ = lean_box(0);
v_isShared_2737_ = v_isSharedCheck_2798_;
goto v_resetjp_2735_;
}
v_resetjp_2735_:
{
lean_object* v_size_2738_; lean_object* v_k_2739_; lean_object* v_v_2740_; lean_object* v_l_2741_; lean_object* v_r_2742_; lean_object* v_size_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; uint8_t v___x_2746_; 
v_size_2738_ = lean_ctor_get(v_l_2725_, 0);
v_k_2739_ = lean_ctor_get(v_l_2725_, 1);
v_v_2740_ = lean_ctor_get(v_l_2725_, 2);
v_l_2741_ = lean_ctor_get(v_l_2725_, 3);
v_r_2742_ = lean_ctor_get(v_l_2725_, 4);
v_size_2743_ = lean_ctor_get(v_r_2726_, 0);
v___x_2744_ = lean_unsigned_to_nat(2u);
v___x_2745_ = lean_nat_mul(v___x_2744_, v_size_2743_);
v___x_2746_ = lean_nat_dec_lt(v_size_2738_, v___x_2745_);
lean_dec(v___x_2745_);
if (v___x_2746_ == 0)
{
lean_object* v___x_2748_; uint8_t v_isShared_2749_; uint8_t v_isSharedCheck_2774_; 
lean_inc(v_r_2742_);
lean_inc(v_l_2741_);
lean_inc(v_v_2740_);
lean_inc(v_k_2739_);
v_isSharedCheck_2774_ = !lean_is_exclusive(v_l_2725_);
if (v_isSharedCheck_2774_ == 0)
{
lean_object* v_unused_2775_; lean_object* v_unused_2776_; lean_object* v_unused_2777_; lean_object* v_unused_2778_; lean_object* v_unused_2779_; 
v_unused_2775_ = lean_ctor_get(v_l_2725_, 4);
lean_dec(v_unused_2775_);
v_unused_2776_ = lean_ctor_get(v_l_2725_, 3);
lean_dec(v_unused_2776_);
v_unused_2777_ = lean_ctor_get(v_l_2725_, 2);
lean_dec(v_unused_2777_);
v_unused_2778_ = lean_ctor_get(v_l_2725_, 1);
lean_dec(v_unused_2778_);
v_unused_2779_ = lean_ctor_get(v_l_2725_, 0);
lean_dec(v_unused_2779_);
v___x_2748_ = v_l_2725_;
v_isShared_2749_ = v_isSharedCheck_2774_;
goto v_resetjp_2747_;
}
else
{
lean_dec(v_l_2725_);
v___x_2748_ = lean_box(0);
v_isShared_2749_ = v_isSharedCheck_2774_;
goto v_resetjp_2747_;
}
v_resetjp_2747_:
{
lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___y_2753_; lean_object* v___y_2754_; lean_object* v___y_2755_; lean_object* v___y_2764_; 
v___x_2750_ = lean_nat_add(v___x_2720_, v_size_2721_);
v___x_2751_ = lean_nat_add(v___x_2750_, v_size_2722_);
lean_dec(v_size_2722_);
if (lean_obj_tag(v_l_2741_) == 0)
{
lean_object* v_size_2772_; 
v_size_2772_ = lean_ctor_get(v_l_2741_, 0);
lean_inc(v_size_2772_);
v___y_2764_ = v_size_2772_;
goto v___jp_2763_;
}
else
{
lean_object* v___x_2773_; 
v___x_2773_ = lean_unsigned_to_nat(0u);
v___y_2764_ = v___x_2773_;
goto v___jp_2763_;
}
v___jp_2752_:
{
lean_object* v___x_2756_; lean_object* v___x_2758_; 
v___x_2756_ = lean_nat_add(v___y_2753_, v___y_2755_);
lean_dec(v___y_2755_);
lean_dec(v___y_2753_);
if (v_isShared_2749_ == 0)
{
lean_ctor_set(v___x_2748_, 4, v_r_2726_);
lean_ctor_set(v___x_2748_, 3, v_r_2742_);
lean_ctor_set(v___x_2748_, 2, v_v_2724_);
lean_ctor_set(v___x_2748_, 1, v_k_2723_);
lean_ctor_set(v___x_2748_, 0, v___x_2756_);
v___x_2758_ = v___x_2748_;
goto v_reusejp_2757_;
}
else
{
lean_object* v_reuseFailAlloc_2762_; 
v_reuseFailAlloc_2762_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2762_, 0, v___x_2756_);
lean_ctor_set(v_reuseFailAlloc_2762_, 1, v_k_2723_);
lean_ctor_set(v_reuseFailAlloc_2762_, 2, v_v_2724_);
lean_ctor_set(v_reuseFailAlloc_2762_, 3, v_r_2742_);
lean_ctor_set(v_reuseFailAlloc_2762_, 4, v_r_2726_);
v___x_2758_ = v_reuseFailAlloc_2762_;
goto v_reusejp_2757_;
}
v_reusejp_2757_:
{
lean_object* v___x_2760_; 
if (v_isShared_2737_ == 0)
{
lean_ctor_set(v___x_2736_, 4, v___x_2758_);
lean_ctor_set(v___x_2736_, 3, v___y_2754_);
lean_ctor_set(v___x_2736_, 2, v_v_2740_);
lean_ctor_set(v___x_2736_, 1, v_k_2739_);
lean_ctor_set(v___x_2736_, 0, v___x_2751_);
v___x_2760_ = v___x_2736_;
goto v_reusejp_2759_;
}
else
{
lean_object* v_reuseFailAlloc_2761_; 
v_reuseFailAlloc_2761_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2761_, 0, v___x_2751_);
lean_ctor_set(v_reuseFailAlloc_2761_, 1, v_k_2739_);
lean_ctor_set(v_reuseFailAlloc_2761_, 2, v_v_2740_);
lean_ctor_set(v_reuseFailAlloc_2761_, 3, v___y_2754_);
lean_ctor_set(v_reuseFailAlloc_2761_, 4, v___x_2758_);
v___x_2760_ = v_reuseFailAlloc_2761_;
goto v_reusejp_2759_;
}
v_reusejp_2759_:
{
return v___x_2760_;
}
}
}
v___jp_2763_:
{
lean_object* v___x_2765_; lean_object* v___x_2767_; 
v___x_2765_ = lean_nat_add(v___x_2750_, v___y_2764_);
lean_dec(v___y_2764_);
lean_dec(v___x_2750_);
if (v_isShared_2576_ == 0)
{
lean_ctor_set(v___x_2575_, 4, v_l_2741_);
lean_ctor_set(v___x_2575_, 0, v___x_2765_);
v___x_2767_ = v___x_2575_;
goto v_reusejp_2766_;
}
else
{
lean_object* v_reuseFailAlloc_2771_; 
v_reuseFailAlloc_2771_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2771_, 0, v___x_2765_);
lean_ctor_set(v_reuseFailAlloc_2771_, 1, v_k_2570_);
lean_ctor_set(v_reuseFailAlloc_2771_, 2, v_v_2571_);
lean_ctor_set(v_reuseFailAlloc_2771_, 3, v_l_2572_);
lean_ctor_set(v_reuseFailAlloc_2771_, 4, v_l_2741_);
v___x_2767_ = v_reuseFailAlloc_2771_;
goto v_reusejp_2766_;
}
v_reusejp_2766_:
{
lean_object* v___x_2768_; 
v___x_2768_ = lean_nat_add(v___x_2720_, v_size_2743_);
if (lean_obj_tag(v_r_2742_) == 0)
{
lean_object* v_size_2769_; 
v_size_2769_ = lean_ctor_get(v_r_2742_, 0);
lean_inc(v_size_2769_);
v___y_2753_ = v___x_2768_;
v___y_2754_ = v___x_2767_;
v___y_2755_ = v_size_2769_;
goto v___jp_2752_;
}
else
{
lean_object* v___x_2770_; 
v___x_2770_ = lean_unsigned_to_nat(0u);
v___y_2753_ = v___x_2768_;
v___y_2754_ = v___x_2767_;
v___y_2755_ = v___x_2770_;
goto v___jp_2752_;
}
}
}
}
}
else
{
lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2784_; 
lean_del_object(v___x_2575_);
v___x_2780_ = lean_nat_add(v___x_2720_, v_size_2721_);
v___x_2781_ = lean_nat_add(v___x_2780_, v_size_2722_);
lean_dec(v_size_2722_);
v___x_2782_ = lean_nat_add(v___x_2780_, v_size_2738_);
lean_dec(v___x_2780_);
lean_inc_ref(v_l_2572_);
if (v_isShared_2737_ == 0)
{
lean_ctor_set(v___x_2736_, 4, v_l_2725_);
lean_ctor_set(v___x_2736_, 3, v_l_2572_);
lean_ctor_set(v___x_2736_, 2, v_v_2571_);
lean_ctor_set(v___x_2736_, 1, v_k_2570_);
lean_ctor_set(v___x_2736_, 0, v___x_2782_);
v___x_2784_ = v___x_2736_;
goto v_reusejp_2783_;
}
else
{
lean_object* v_reuseFailAlloc_2797_; 
v_reuseFailAlloc_2797_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2797_, 0, v___x_2782_);
lean_ctor_set(v_reuseFailAlloc_2797_, 1, v_k_2570_);
lean_ctor_set(v_reuseFailAlloc_2797_, 2, v_v_2571_);
lean_ctor_set(v_reuseFailAlloc_2797_, 3, v_l_2572_);
lean_ctor_set(v_reuseFailAlloc_2797_, 4, v_l_2725_);
v___x_2784_ = v_reuseFailAlloc_2797_;
goto v_reusejp_2783_;
}
v_reusejp_2783_:
{
lean_object* v___x_2786_; uint8_t v_isShared_2787_; uint8_t v_isSharedCheck_2791_; 
v_isSharedCheck_2791_ = !lean_is_exclusive(v_l_2572_);
if (v_isSharedCheck_2791_ == 0)
{
lean_object* v_unused_2792_; lean_object* v_unused_2793_; lean_object* v_unused_2794_; lean_object* v_unused_2795_; lean_object* v_unused_2796_; 
v_unused_2792_ = lean_ctor_get(v_l_2572_, 4);
lean_dec(v_unused_2792_);
v_unused_2793_ = lean_ctor_get(v_l_2572_, 3);
lean_dec(v_unused_2793_);
v_unused_2794_ = lean_ctor_get(v_l_2572_, 2);
lean_dec(v_unused_2794_);
v_unused_2795_ = lean_ctor_get(v_l_2572_, 1);
lean_dec(v_unused_2795_);
v_unused_2796_ = lean_ctor_get(v_l_2572_, 0);
lean_dec(v_unused_2796_);
v___x_2786_ = v_l_2572_;
v_isShared_2787_ = v_isSharedCheck_2791_;
goto v_resetjp_2785_;
}
else
{
lean_dec(v_l_2572_);
v___x_2786_ = lean_box(0);
v_isShared_2787_ = v_isSharedCheck_2791_;
goto v_resetjp_2785_;
}
v_resetjp_2785_:
{
lean_object* v___x_2789_; 
if (v_isShared_2787_ == 0)
{
lean_ctor_set(v___x_2786_, 4, v_r_2726_);
lean_ctor_set(v___x_2786_, 3, v___x_2784_);
lean_ctor_set(v___x_2786_, 2, v_v_2724_);
lean_ctor_set(v___x_2786_, 1, v_k_2723_);
lean_ctor_set(v___x_2786_, 0, v___x_2781_);
v___x_2789_ = v___x_2786_;
goto v_reusejp_2788_;
}
else
{
lean_object* v_reuseFailAlloc_2790_; 
v_reuseFailAlloc_2790_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2790_, 0, v___x_2781_);
lean_ctor_set(v_reuseFailAlloc_2790_, 1, v_k_2723_);
lean_ctor_set(v_reuseFailAlloc_2790_, 2, v_v_2724_);
lean_ctor_set(v_reuseFailAlloc_2790_, 3, v___x_2784_);
lean_ctor_set(v_reuseFailAlloc_2790_, 4, v_r_2726_);
v___x_2789_ = v_reuseFailAlloc_2790_;
goto v_reusejp_2788_;
}
v_reusejp_2788_:
{
return v___x_2789_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2804_; 
v_l_2804_ = lean_ctor_get(v_impl_2719_, 3);
lean_inc(v_l_2804_);
if (lean_obj_tag(v_l_2804_) == 0)
{
lean_object* v_r_2805_; lean_object* v_k_2806_; lean_object* v_v_2807_; lean_object* v___x_2809_; uint8_t v_isShared_2810_; uint8_t v_isSharedCheck_2830_; 
v_r_2805_ = lean_ctor_get(v_impl_2719_, 4);
v_k_2806_ = lean_ctor_get(v_impl_2719_, 1);
v_v_2807_ = lean_ctor_get(v_impl_2719_, 2);
v_isSharedCheck_2830_ = !lean_is_exclusive(v_impl_2719_);
if (v_isSharedCheck_2830_ == 0)
{
lean_object* v_unused_2831_; lean_object* v_unused_2832_; 
v_unused_2831_ = lean_ctor_get(v_impl_2719_, 3);
lean_dec(v_unused_2831_);
v_unused_2832_ = lean_ctor_get(v_impl_2719_, 0);
lean_dec(v_unused_2832_);
v___x_2809_ = v_impl_2719_;
v_isShared_2810_ = v_isSharedCheck_2830_;
goto v_resetjp_2808_;
}
else
{
lean_inc(v_r_2805_);
lean_inc(v_v_2807_);
lean_inc(v_k_2806_);
lean_dec(v_impl_2719_);
v___x_2809_ = lean_box(0);
v_isShared_2810_ = v_isSharedCheck_2830_;
goto v_resetjp_2808_;
}
v_resetjp_2808_:
{
lean_object* v_k_2811_; lean_object* v_v_2812_; lean_object* v___x_2814_; uint8_t v_isShared_2815_; uint8_t v_isSharedCheck_2826_; 
v_k_2811_ = lean_ctor_get(v_l_2804_, 1);
v_v_2812_ = lean_ctor_get(v_l_2804_, 2);
v_isSharedCheck_2826_ = !lean_is_exclusive(v_l_2804_);
if (v_isSharedCheck_2826_ == 0)
{
lean_object* v_unused_2827_; lean_object* v_unused_2828_; lean_object* v_unused_2829_; 
v_unused_2827_ = lean_ctor_get(v_l_2804_, 4);
lean_dec(v_unused_2827_);
v_unused_2828_ = lean_ctor_get(v_l_2804_, 3);
lean_dec(v_unused_2828_);
v_unused_2829_ = lean_ctor_get(v_l_2804_, 0);
lean_dec(v_unused_2829_);
v___x_2814_ = v_l_2804_;
v_isShared_2815_ = v_isSharedCheck_2826_;
goto v_resetjp_2813_;
}
else
{
lean_inc(v_v_2812_);
lean_inc(v_k_2811_);
lean_dec(v_l_2804_);
v___x_2814_ = lean_box(0);
v_isShared_2815_ = v_isSharedCheck_2826_;
goto v_resetjp_2813_;
}
v_resetjp_2813_:
{
lean_object* v___x_2816_; lean_object* v___x_2818_; 
v___x_2816_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_2805_, 2);
if (v_isShared_2815_ == 0)
{
lean_ctor_set(v___x_2814_, 4, v_r_2805_);
lean_ctor_set(v___x_2814_, 3, v_r_2805_);
lean_ctor_set(v___x_2814_, 2, v_v_2571_);
lean_ctor_set(v___x_2814_, 1, v_k_2570_);
lean_ctor_set(v___x_2814_, 0, v___x_2720_);
v___x_2818_ = v___x_2814_;
goto v_reusejp_2817_;
}
else
{
lean_object* v_reuseFailAlloc_2825_; 
v_reuseFailAlloc_2825_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2825_, 0, v___x_2720_);
lean_ctor_set(v_reuseFailAlloc_2825_, 1, v_k_2570_);
lean_ctor_set(v_reuseFailAlloc_2825_, 2, v_v_2571_);
lean_ctor_set(v_reuseFailAlloc_2825_, 3, v_r_2805_);
lean_ctor_set(v_reuseFailAlloc_2825_, 4, v_r_2805_);
v___x_2818_ = v_reuseFailAlloc_2825_;
goto v_reusejp_2817_;
}
v_reusejp_2817_:
{
lean_object* v___x_2820_; 
lean_inc(v_r_2805_);
if (v_isShared_2810_ == 0)
{
lean_ctor_set(v___x_2809_, 3, v_r_2805_);
lean_ctor_set(v___x_2809_, 0, v___x_2720_);
v___x_2820_ = v___x_2809_;
goto v_reusejp_2819_;
}
else
{
lean_object* v_reuseFailAlloc_2824_; 
v_reuseFailAlloc_2824_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2824_, 0, v___x_2720_);
lean_ctor_set(v_reuseFailAlloc_2824_, 1, v_k_2806_);
lean_ctor_set(v_reuseFailAlloc_2824_, 2, v_v_2807_);
lean_ctor_set(v_reuseFailAlloc_2824_, 3, v_r_2805_);
lean_ctor_set(v_reuseFailAlloc_2824_, 4, v_r_2805_);
v___x_2820_ = v_reuseFailAlloc_2824_;
goto v_reusejp_2819_;
}
v_reusejp_2819_:
{
lean_object* v___x_2822_; 
if (v_isShared_2576_ == 0)
{
lean_ctor_set(v___x_2575_, 4, v___x_2820_);
lean_ctor_set(v___x_2575_, 3, v___x_2818_);
lean_ctor_set(v___x_2575_, 2, v_v_2812_);
lean_ctor_set(v___x_2575_, 1, v_k_2811_);
lean_ctor_set(v___x_2575_, 0, v___x_2816_);
v___x_2822_ = v___x_2575_;
goto v_reusejp_2821_;
}
else
{
lean_object* v_reuseFailAlloc_2823_; 
v_reuseFailAlloc_2823_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2823_, 0, v___x_2816_);
lean_ctor_set(v_reuseFailAlloc_2823_, 1, v_k_2811_);
lean_ctor_set(v_reuseFailAlloc_2823_, 2, v_v_2812_);
lean_ctor_set(v_reuseFailAlloc_2823_, 3, v___x_2818_);
lean_ctor_set(v_reuseFailAlloc_2823_, 4, v___x_2820_);
v___x_2822_ = v_reuseFailAlloc_2823_;
goto v_reusejp_2821_;
}
v_reusejp_2821_:
{
return v___x_2822_;
}
}
}
}
}
}
else
{
lean_object* v_r_2833_; 
v_r_2833_ = lean_ctor_get(v_impl_2719_, 4);
lean_inc(v_r_2833_);
if (lean_obj_tag(v_r_2833_) == 0)
{
lean_object* v_k_2834_; lean_object* v_v_2835_; lean_object* v___x_2837_; uint8_t v_isShared_2838_; uint8_t v_isSharedCheck_2846_; 
v_k_2834_ = lean_ctor_get(v_impl_2719_, 1);
v_v_2835_ = lean_ctor_get(v_impl_2719_, 2);
v_isSharedCheck_2846_ = !lean_is_exclusive(v_impl_2719_);
if (v_isSharedCheck_2846_ == 0)
{
lean_object* v_unused_2847_; lean_object* v_unused_2848_; lean_object* v_unused_2849_; 
v_unused_2847_ = lean_ctor_get(v_impl_2719_, 4);
lean_dec(v_unused_2847_);
v_unused_2848_ = lean_ctor_get(v_impl_2719_, 3);
lean_dec(v_unused_2848_);
v_unused_2849_ = lean_ctor_get(v_impl_2719_, 0);
lean_dec(v_unused_2849_);
v___x_2837_ = v_impl_2719_;
v_isShared_2838_ = v_isSharedCheck_2846_;
goto v_resetjp_2836_;
}
else
{
lean_inc(v_v_2835_);
lean_inc(v_k_2834_);
lean_dec(v_impl_2719_);
v___x_2837_ = lean_box(0);
v_isShared_2838_ = v_isSharedCheck_2846_;
goto v_resetjp_2836_;
}
v_resetjp_2836_:
{
lean_object* v___x_2839_; lean_object* v___x_2841_; 
v___x_2839_ = lean_unsigned_to_nat(3u);
if (v_isShared_2838_ == 0)
{
lean_ctor_set(v___x_2837_, 4, v_l_2804_);
lean_ctor_set(v___x_2837_, 2, v_v_2571_);
lean_ctor_set(v___x_2837_, 1, v_k_2570_);
lean_ctor_set(v___x_2837_, 0, v___x_2720_);
v___x_2841_ = v___x_2837_;
goto v_reusejp_2840_;
}
else
{
lean_object* v_reuseFailAlloc_2845_; 
v_reuseFailAlloc_2845_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2845_, 0, v___x_2720_);
lean_ctor_set(v_reuseFailAlloc_2845_, 1, v_k_2570_);
lean_ctor_set(v_reuseFailAlloc_2845_, 2, v_v_2571_);
lean_ctor_set(v_reuseFailAlloc_2845_, 3, v_l_2804_);
lean_ctor_set(v_reuseFailAlloc_2845_, 4, v_l_2804_);
v___x_2841_ = v_reuseFailAlloc_2845_;
goto v_reusejp_2840_;
}
v_reusejp_2840_:
{
lean_object* v___x_2843_; 
if (v_isShared_2576_ == 0)
{
lean_ctor_set(v___x_2575_, 4, v_r_2833_);
lean_ctor_set(v___x_2575_, 3, v___x_2841_);
lean_ctor_set(v___x_2575_, 2, v_v_2835_);
lean_ctor_set(v___x_2575_, 1, v_k_2834_);
lean_ctor_set(v___x_2575_, 0, v___x_2839_);
v___x_2843_ = v___x_2575_;
goto v_reusejp_2842_;
}
else
{
lean_object* v_reuseFailAlloc_2844_; 
v_reuseFailAlloc_2844_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2844_, 0, v___x_2839_);
lean_ctor_set(v_reuseFailAlloc_2844_, 1, v_k_2834_);
lean_ctor_set(v_reuseFailAlloc_2844_, 2, v_v_2835_);
lean_ctor_set(v_reuseFailAlloc_2844_, 3, v___x_2841_);
lean_ctor_set(v_reuseFailAlloc_2844_, 4, v_r_2833_);
v___x_2843_ = v_reuseFailAlloc_2844_;
goto v_reusejp_2842_;
}
v_reusejp_2842_:
{
return v___x_2843_;
}
}
}
}
else
{
lean_object* v___x_2850_; lean_object* v___x_2852_; 
v___x_2850_ = lean_unsigned_to_nat(2u);
if (v_isShared_2576_ == 0)
{
lean_ctor_set(v___x_2575_, 4, v_impl_2719_);
lean_ctor_set(v___x_2575_, 3, v_r_2833_);
lean_ctor_set(v___x_2575_, 0, v___x_2850_);
v___x_2852_ = v___x_2575_;
goto v_reusejp_2851_;
}
else
{
lean_object* v_reuseFailAlloc_2853_; 
v_reuseFailAlloc_2853_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2853_, 0, v___x_2850_);
lean_ctor_set(v_reuseFailAlloc_2853_, 1, v_k_2570_);
lean_ctor_set(v_reuseFailAlloc_2853_, 2, v_v_2571_);
lean_ctor_set(v_reuseFailAlloc_2853_, 3, v_r_2833_);
lean_ctor_set(v_reuseFailAlloc_2853_, 4, v_impl_2719_);
v___x_2852_ = v_reuseFailAlloc_2853_;
goto v_reusejp_2851_;
}
v_reusejp_2851_:
{
return v___x_2852_;
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
lean_object* v___x_2855_; lean_object* v___x_2856_; 
lean_dec_ref(v_cmp_2565_);
v___x_2855_ = lean_unsigned_to_nat(1u);
v___x_2856_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2856_, 0, v___x_2855_);
lean_ctor_set(v___x_2856_, 1, v_k_2566_);
lean_ctor_set(v___x_2856_, 2, v_v_2567_);
lean_ctor_set(v___x_2856_, 3, v_t_2568_);
lean_ctor_set(v___x_2856_, 4, v_t_2568_);
return v___x_2856_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__2_spec__4_spec__7_spec__11(lean_object* v_cmp_2857_, lean_object* v_init_2858_, lean_object* v_x_2859_){
_start:
{
if (lean_obj_tag(v_x_2859_) == 0)
{
lean_object* v_k_2860_; lean_object* v_v_2861_; lean_object* v_l_2862_; lean_object* v_r_2863_; lean_object* v___x_2864_; 
v_k_2860_ = lean_ctor_get(v_x_2859_, 1);
lean_inc(v_k_2860_);
v_v_2861_ = lean_ctor_get(v_x_2859_, 2);
lean_inc(v_v_2861_);
v_l_2862_ = lean_ctor_get(v_x_2859_, 3);
lean_inc(v_l_2862_);
v_r_2863_ = lean_ctor_get(v_x_2859_, 4);
lean_inc(v_r_2863_);
lean_dec_ref_known(v_x_2859_, 5);
lean_inc_ref(v_cmp_2857_);
v___x_2864_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__2_spec__4_spec__7_spec__11(v_cmp_2857_, v_init_2858_, v_l_2862_);
if (lean_obj_tag(v___x_2864_) == 0)
{
lean_dec(v_r_2863_);
lean_dec(v_v_2861_);
lean_dec(v_k_2860_);
lean_dec_ref(v_cmp_2857_);
return v___x_2864_;
}
else
{
lean_object* v_a_2865_; lean_object* v___x_2866_; 
v_a_2865_ = lean_ctor_get(v___x_2864_, 0);
lean_inc(v_a_2865_);
lean_dec_ref_known(v___x_2864_, 1);
v___x_2866_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentEdit_fromJson_spec__1_spec__1(v_v_2861_);
if (lean_obj_tag(v___x_2866_) == 0)
{
lean_object* v_a_2867_; lean_object* v___x_2869_; uint8_t v_isShared_2870_; uint8_t v_isSharedCheck_2874_; 
lean_dec(v_a_2865_);
lean_dec(v_r_2863_);
lean_dec(v_k_2860_);
lean_dec_ref(v_cmp_2857_);
v_a_2867_ = lean_ctor_get(v___x_2866_, 0);
v_isSharedCheck_2874_ = !lean_is_exclusive(v___x_2866_);
if (v_isSharedCheck_2874_ == 0)
{
v___x_2869_ = v___x_2866_;
v_isShared_2870_ = v_isSharedCheck_2874_;
goto v_resetjp_2868_;
}
else
{
lean_inc(v_a_2867_);
lean_dec(v___x_2866_);
v___x_2869_ = lean_box(0);
v_isShared_2870_ = v_isSharedCheck_2874_;
goto v_resetjp_2868_;
}
v_resetjp_2868_:
{
lean_object* v___x_2872_; 
if (v_isShared_2870_ == 0)
{
v___x_2872_ = v___x_2869_;
goto v_reusejp_2871_;
}
else
{
lean_object* v_reuseFailAlloc_2873_; 
v_reuseFailAlloc_2873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2873_, 0, v_a_2867_);
v___x_2872_ = v_reuseFailAlloc_2873_;
goto v_reusejp_2871_;
}
v_reusejp_2871_:
{
return v___x_2872_;
}
}
}
else
{
lean_object* v_a_2875_; lean_object* v___x_2876_; 
v_a_2875_ = lean_ctor_get(v___x_2866_, 0);
lean_inc(v_a_2875_);
lean_dec_ref_known(v___x_2866_, 1);
lean_inc_ref(v_cmp_2857_);
v___x_2876_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__1_spec__2_spec__4_spec__7___redArg(v_cmp_2857_, v_k_2860_, v_a_2875_, v_a_2865_);
v_init_2858_ = v___x_2876_;
v_x_2859_ = v_r_2863_;
goto _start;
}
}
}
else
{
lean_object* v___x_2878_; 
lean_dec_ref(v_cmp_2857_);
v___x_2878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2878_, 0, v_init_2858_);
return v___x_2878_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__2_spec__4_spec__7(lean_object* v_cmp_2879_, lean_object* v_j_2880_){
_start:
{
lean_object* v___x_2881_; 
v___x_2881_ = l_Lean_Json_getObj_x3f(v_j_2880_);
if (lean_obj_tag(v___x_2881_) == 0)
{
lean_object* v_a_2882_; lean_object* v___x_2884_; uint8_t v_isShared_2885_; uint8_t v_isSharedCheck_2889_; 
lean_dec_ref(v_cmp_2879_);
v_a_2882_ = lean_ctor_get(v___x_2881_, 0);
v_isSharedCheck_2889_ = !lean_is_exclusive(v___x_2881_);
if (v_isSharedCheck_2889_ == 0)
{
v___x_2884_ = v___x_2881_;
v_isShared_2885_ = v_isSharedCheck_2889_;
goto v_resetjp_2883_;
}
else
{
lean_inc(v_a_2882_);
lean_dec(v___x_2881_);
v___x_2884_ = lean_box(0);
v_isShared_2885_ = v_isSharedCheck_2889_;
goto v_resetjp_2883_;
}
v_resetjp_2883_:
{
lean_object* v___x_2887_; 
if (v_isShared_2885_ == 0)
{
v___x_2887_ = v___x_2884_;
goto v_reusejp_2886_;
}
else
{
lean_object* v_reuseFailAlloc_2888_; 
v_reuseFailAlloc_2888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2888_, 0, v_a_2882_);
v___x_2887_ = v_reuseFailAlloc_2888_;
goto v_reusejp_2886_;
}
v_reusejp_2886_:
{
return v___x_2887_;
}
}
}
else
{
lean_object* v_a_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; 
v_a_2890_ = lean_ctor_get(v___x_2881_, 0);
lean_inc(v_a_2890_);
lean_dec_ref_known(v___x_2881_, 1);
v___x_2891_ = lean_box(1);
v___x_2892_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__2_spec__4_spec__7_spec__11(v_cmp_2879_, v___x_2891_, v_a_2890_);
return v___x_2892_;
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__2_spec__4(lean_object* v_x_2896_){
_start:
{
if (lean_obj_tag(v_x_2896_) == 0)
{
lean_object* v___x_2897_; 
v___x_2897_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__2_spec__4___closed__0));
return v___x_2897_;
}
else
{
lean_object* v___x_2898_; lean_object* v___x_2899_; 
v___x_2898_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__2_spec__4___closed__1));
v___x_2899_ = l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__2_spec__4_spec__7(v___x_2898_, v_x_2896_);
if (lean_obj_tag(v___x_2899_) == 0)
{
lean_object* v_a_2900_; lean_object* v___x_2902_; uint8_t v_isShared_2903_; uint8_t v_isSharedCheck_2907_; 
v_a_2900_ = lean_ctor_get(v___x_2899_, 0);
v_isSharedCheck_2907_ = !lean_is_exclusive(v___x_2899_);
if (v_isSharedCheck_2907_ == 0)
{
v___x_2902_ = v___x_2899_;
v_isShared_2903_ = v_isSharedCheck_2907_;
goto v_resetjp_2901_;
}
else
{
lean_inc(v_a_2900_);
lean_dec(v___x_2899_);
v___x_2902_ = lean_box(0);
v_isShared_2903_ = v_isSharedCheck_2907_;
goto v_resetjp_2901_;
}
v_resetjp_2901_:
{
lean_object* v___x_2905_; 
if (v_isShared_2903_ == 0)
{
v___x_2905_ = v___x_2902_;
goto v_reusejp_2904_;
}
else
{
lean_object* v_reuseFailAlloc_2906_; 
v_reuseFailAlloc_2906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2906_, 0, v_a_2900_);
v___x_2905_ = v_reuseFailAlloc_2906_;
goto v_reusejp_2904_;
}
v_reusejp_2904_:
{
return v___x_2905_;
}
}
}
else
{
lean_object* v_a_2908_; lean_object* v___x_2910_; uint8_t v_isShared_2911_; uint8_t v_isSharedCheck_2916_; 
v_a_2908_ = lean_ctor_get(v___x_2899_, 0);
v_isSharedCheck_2916_ = !lean_is_exclusive(v___x_2899_);
if (v_isSharedCheck_2916_ == 0)
{
v___x_2910_ = v___x_2899_;
v_isShared_2911_ = v_isSharedCheck_2916_;
goto v_resetjp_2909_;
}
else
{
lean_inc(v_a_2908_);
lean_dec(v___x_2899_);
v___x_2910_ = lean_box(0);
v_isShared_2911_ = v_isSharedCheck_2916_;
goto v_resetjp_2909_;
}
v_resetjp_2909_:
{
lean_object* v___x_2912_; lean_object* v___x_2914_; 
v___x_2912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2912_, 0, v_a_2908_);
if (v_isShared_2911_ == 0)
{
lean_ctor_set(v___x_2910_, 0, v___x_2912_);
v___x_2914_ = v___x_2910_;
goto v_reusejp_2913_;
}
else
{
lean_object* v_reuseFailAlloc_2915_; 
v_reuseFailAlloc_2915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2915_, 0, v___x_2912_);
v___x_2914_ = v_reuseFailAlloc_2915_;
goto v_reusejp_2913_;
}
v_reusejp_2913_:
{
return v___x_2914_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__2(lean_object* v_j_2917_, lean_object* v_k_2918_){
_start:
{
lean_object* v___x_2919_; lean_object* v___x_2920_; 
v___x_2919_ = l_Lean_Json_getObjValD(v_j_2917_, v_k_2918_);
v___x_2920_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__2_spec__4(v___x_2919_);
return v___x_2920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__2___boxed(lean_object* v_j_2921_, lean_object* v_k_2922_){
_start:
{
lean_object* v_res_2923_; 
v_res_2923_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__2(v_j_2921_, v_k_2922_);
lean_dec_ref(v_k_2922_);
return v_res_2923_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__1_spec__2_spec__4_spec__8(lean_object* v_cmp_2924_, lean_object* v_init_2925_, lean_object* v_x_2926_){
_start:
{
if (lean_obj_tag(v_x_2926_) == 0)
{
lean_object* v_k_2927_; lean_object* v_v_2928_; lean_object* v_l_2929_; lean_object* v_r_2930_; lean_object* v___x_2931_; 
v_k_2927_ = lean_ctor_get(v_x_2926_, 1);
lean_inc(v_k_2927_);
v_v_2928_ = lean_ctor_get(v_x_2926_, 2);
lean_inc(v_v_2928_);
v_l_2929_ = lean_ctor_get(v_x_2926_, 3);
lean_inc(v_l_2929_);
v_r_2930_ = lean_ctor_get(v_x_2926_, 4);
lean_inc(v_r_2930_);
lean_dec_ref_known(v_x_2926_, 5);
lean_inc_ref(v_cmp_2924_);
v___x_2931_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__1_spec__2_spec__4_spec__8(v_cmp_2924_, v_init_2925_, v_l_2929_);
if (lean_obj_tag(v___x_2931_) == 0)
{
lean_dec(v_r_2930_);
lean_dec(v_v_2928_);
lean_dec(v_k_2927_);
lean_dec_ref(v_cmp_2924_);
return v___x_2931_;
}
else
{
lean_object* v_a_2932_; lean_object* v___x_2933_; 
v_a_2932_ = lean_ctor_get(v___x_2931_, 0);
lean_inc(v_a_2932_);
lean_dec_ref_known(v___x_2931_, 1);
v___x_2933_ = l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson(v_v_2928_);
if (lean_obj_tag(v___x_2933_) == 0)
{
lean_object* v_a_2934_; lean_object* v___x_2936_; uint8_t v_isShared_2937_; uint8_t v_isSharedCheck_2941_; 
lean_dec(v_a_2932_);
lean_dec(v_r_2930_);
lean_dec(v_k_2927_);
lean_dec_ref(v_cmp_2924_);
v_a_2934_ = lean_ctor_get(v___x_2933_, 0);
v_isSharedCheck_2941_ = !lean_is_exclusive(v___x_2933_);
if (v_isSharedCheck_2941_ == 0)
{
v___x_2936_ = v___x_2933_;
v_isShared_2937_ = v_isSharedCheck_2941_;
goto v_resetjp_2935_;
}
else
{
lean_inc(v_a_2934_);
lean_dec(v___x_2933_);
v___x_2936_ = lean_box(0);
v_isShared_2937_ = v_isSharedCheck_2941_;
goto v_resetjp_2935_;
}
v_resetjp_2935_:
{
lean_object* v___x_2939_; 
if (v_isShared_2937_ == 0)
{
v___x_2939_ = v___x_2936_;
goto v_reusejp_2938_;
}
else
{
lean_object* v_reuseFailAlloc_2940_; 
v_reuseFailAlloc_2940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2940_, 0, v_a_2934_);
v___x_2939_ = v_reuseFailAlloc_2940_;
goto v_reusejp_2938_;
}
v_reusejp_2938_:
{
return v___x_2939_;
}
}
}
else
{
lean_object* v_a_2942_; lean_object* v___x_2943_; 
v_a_2942_ = lean_ctor_get(v___x_2933_, 0);
lean_inc(v_a_2942_);
lean_dec_ref_known(v___x_2933_, 1);
lean_inc_ref(v_cmp_2924_);
v___x_2943_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__1_spec__2_spec__4_spec__7___redArg(v_cmp_2924_, v_k_2927_, v_a_2942_, v_a_2932_);
v_init_2925_ = v___x_2943_;
v_x_2926_ = v_r_2930_;
goto _start;
}
}
}
else
{
lean_object* v___x_2945_; 
lean_dec_ref(v_cmp_2924_);
v___x_2945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2945_, 0, v_init_2925_);
return v___x_2945_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__1_spec__2_spec__4(lean_object* v_cmp_2946_, lean_object* v_j_2947_){
_start:
{
lean_object* v___x_2948_; 
v___x_2948_ = l_Lean_Json_getObj_x3f(v_j_2947_);
if (lean_obj_tag(v___x_2948_) == 0)
{
lean_object* v_a_2949_; lean_object* v___x_2951_; uint8_t v_isShared_2952_; uint8_t v_isSharedCheck_2956_; 
lean_dec_ref(v_cmp_2946_);
v_a_2949_ = lean_ctor_get(v___x_2948_, 0);
v_isSharedCheck_2956_ = !lean_is_exclusive(v___x_2948_);
if (v_isSharedCheck_2956_ == 0)
{
v___x_2951_ = v___x_2948_;
v_isShared_2952_ = v_isSharedCheck_2956_;
goto v_resetjp_2950_;
}
else
{
lean_inc(v_a_2949_);
lean_dec(v___x_2948_);
v___x_2951_ = lean_box(0);
v_isShared_2952_ = v_isSharedCheck_2956_;
goto v_resetjp_2950_;
}
v_resetjp_2950_:
{
lean_object* v___x_2954_; 
if (v_isShared_2952_ == 0)
{
v___x_2954_ = v___x_2951_;
goto v_reusejp_2953_;
}
else
{
lean_object* v_reuseFailAlloc_2955_; 
v_reuseFailAlloc_2955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2955_, 0, v_a_2949_);
v___x_2954_ = v_reuseFailAlloc_2955_;
goto v_reusejp_2953_;
}
v_reusejp_2953_:
{
return v___x_2954_;
}
}
}
else
{
lean_object* v_a_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; 
v_a_2957_ = lean_ctor_get(v___x_2948_, 0);
lean_inc(v_a_2957_);
lean_dec_ref_known(v___x_2948_, 1);
v___x_2958_ = lean_box(1);
v___x_2959_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__1_spec__2_spec__4_spec__8(v_cmp_2946_, v___x_2958_, v_a_2957_);
return v___x_2959_;
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__1_spec__2(lean_object* v_x_2960_){
_start:
{
if (lean_obj_tag(v_x_2960_) == 0)
{
lean_object* v___x_2961_; 
v___x_2961_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__2_spec__4___closed__0));
return v___x_2961_;
}
else
{
lean_object* v___x_2962_; lean_object* v___x_2963_; 
v___x_2962_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__2_spec__4___closed__1));
v___x_2963_ = l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__1_spec__2_spec__4(v___x_2962_, v_x_2960_);
if (lean_obj_tag(v___x_2963_) == 0)
{
lean_object* v_a_2964_; lean_object* v___x_2966_; uint8_t v_isShared_2967_; uint8_t v_isSharedCheck_2971_; 
v_a_2964_ = lean_ctor_get(v___x_2963_, 0);
v_isSharedCheck_2971_ = !lean_is_exclusive(v___x_2963_);
if (v_isSharedCheck_2971_ == 0)
{
v___x_2966_ = v___x_2963_;
v_isShared_2967_ = v_isSharedCheck_2971_;
goto v_resetjp_2965_;
}
else
{
lean_inc(v_a_2964_);
lean_dec(v___x_2963_);
v___x_2966_ = lean_box(0);
v_isShared_2967_ = v_isSharedCheck_2971_;
goto v_resetjp_2965_;
}
v_resetjp_2965_:
{
lean_object* v___x_2969_; 
if (v_isShared_2967_ == 0)
{
v___x_2969_ = v___x_2966_;
goto v_reusejp_2968_;
}
else
{
lean_object* v_reuseFailAlloc_2970_; 
v_reuseFailAlloc_2970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2970_, 0, v_a_2964_);
v___x_2969_ = v_reuseFailAlloc_2970_;
goto v_reusejp_2968_;
}
v_reusejp_2968_:
{
return v___x_2969_;
}
}
}
else
{
lean_object* v_a_2972_; lean_object* v___x_2974_; uint8_t v_isShared_2975_; uint8_t v_isSharedCheck_2980_; 
v_a_2972_ = lean_ctor_get(v___x_2963_, 0);
v_isSharedCheck_2980_ = !lean_is_exclusive(v___x_2963_);
if (v_isSharedCheck_2980_ == 0)
{
v___x_2974_ = v___x_2963_;
v_isShared_2975_ = v_isSharedCheck_2980_;
goto v_resetjp_2973_;
}
else
{
lean_inc(v_a_2972_);
lean_dec(v___x_2963_);
v___x_2974_ = lean_box(0);
v_isShared_2975_ = v_isSharedCheck_2980_;
goto v_resetjp_2973_;
}
v_resetjp_2973_:
{
lean_object* v___x_2976_; lean_object* v___x_2978_; 
v___x_2976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2976_, 0, v_a_2972_);
if (v_isShared_2975_ == 0)
{
lean_ctor_set(v___x_2974_, 0, v___x_2976_);
v___x_2978_ = v___x_2974_;
goto v_reusejp_2977_;
}
else
{
lean_object* v_reuseFailAlloc_2979_; 
v_reuseFailAlloc_2979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2979_, 0, v___x_2976_);
v___x_2978_ = v_reuseFailAlloc_2979_;
goto v_reusejp_2977_;
}
v_reusejp_2977_:
{
return v___x_2978_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__1(lean_object* v_j_2981_, lean_object* v_k_2982_){
_start:
{
lean_object* v___x_2983_; lean_object* v___x_2984_; 
v___x_2983_ = l_Lean_Json_getObjValD(v_j_2981_, v_k_2982_);
v___x_2984_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__1_spec__2(v___x_2983_);
return v___x_2984_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__1___boxed(lean_object* v_j_2985_, lean_object* v_k_2986_){
_start:
{
lean_object* v_res_2987_; 
v_res_2987_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__1(v_j_2985_, v_k_2986_);
lean_dec_ref(v_k_2986_);
return v_res_2987_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__0_spec__0_spec__1_spec__4___lam__0(lean_object* v_kind_2988_){
_start:
{
lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; 
v___x_2989_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDocumentChange___lam__0___closed__0));
v___x_2990_ = lean_unsigned_to_nat(80u);
v___x_2991_ = l_Lean_Json_pretty(v_kind_2988_, v___x_2990_);
v___x_2992_ = lean_string_append(v___x_2989_, v___x_2991_);
lean_dec_ref(v___x_2991_);
v___x_2993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2993_, 0, v___x_2992_);
return v___x_2993_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__0_spec__0_spec__1_spec__4(size_t v_sz_2994_, size_t v_i_2995_, lean_object* v_bs_2996_){
_start:
{
uint8_t v___x_2997_; 
v___x_2997_ = lean_usize_dec_lt(v_i_2995_, v_sz_2994_);
if (v___x_2997_ == 0)
{
lean_object* v___x_2998_; 
v___x_2998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2998_, 0, v_bs_2996_);
return v___x_2998_;
}
else
{
lean_object* v_v_2999_; lean_object* v___x_3000_; lean_object* v_bs_x27_3001_; lean_object* v_a_3003_; lean_object* v___y_3021_; lean_object* v___x_3023_; lean_object* v___x_3024_; 
v_v_2999_ = lean_array_uget(v_bs_2996_, v_i_2995_);
v___x_3000_ = lean_unsigned_to_nat(0u);
v_bs_x27_3001_ = lean_array_uset(v_bs_2996_, v_i_2995_, v___x_3000_);
v___x_3023_ = ((lean_object*)(l_Lean_Lsp_instToJsonDocumentChange___lam__0___closed__0));
lean_inc(v_v_2999_);
v___x_3024_ = l_Lean_Json_getObjVal_x3f(v_v_2999_, v___x_3023_);
if (lean_obj_tag(v___x_3024_) == 0)
{
lean_dec_ref_known(v___x_3024_, 1);
goto v___jp_3008_;
}
else
{
lean_object* v_a_3025_; 
v_a_3025_ = lean_ctor_get(v___x_3024_, 0);
lean_inc(v_a_3025_);
lean_dec_ref_known(v___x_3024_, 1);
if (lean_obj_tag(v_a_3025_) == 3)
{
lean_object* v_s_3026_; lean_object* v___x_3027_; uint8_t v___x_3028_; 
v_s_3026_ = lean_ctor_get(v_a_3025_, 0);
v___x_3027_ = ((lean_object*)(l_Lean_Lsp_instToJsonDocumentChange___lam__0___closed__1));
v___x_3028_ = lean_string_dec_eq(v_s_3026_, v___x_3027_);
if (v___x_3028_ == 0)
{
lean_object* v___x_3029_; uint8_t v___x_3030_; 
v___x_3029_ = ((lean_object*)(l_Lean_Lsp_instToJsonDocumentChange___lam__0___closed__3));
v___x_3030_ = lean_string_dec_eq(v_s_3026_, v___x_3029_);
if (v___x_3030_ == 0)
{
lean_object* v___x_3031_; uint8_t v___x_3032_; 
v___x_3031_ = ((lean_object*)(l_Lean_Lsp_instToJsonDocumentChange___lam__0___closed__5));
v___x_3032_ = lean_string_dec_eq(v_s_3026_, v___x_3031_);
if (v___x_3032_ == 0)
{
lean_object* v___x_3033_; 
v___x_3033_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__0_spec__0_spec__1_spec__4___lam__0(v_a_3025_);
v___y_3021_ = v___x_3033_;
goto v___jp_3020_;
}
else
{
lean_object* v___x_3034_; 
lean_dec_ref_known(v_a_3025_, 1);
lean_inc(v_v_2999_);
v___x_3034_ = l_Lean_Lsp_instFromJsonDeleteFile_fromJson(v_v_2999_);
if (lean_obj_tag(v___x_3034_) == 0)
{
lean_dec_ref_known(v___x_3034_, 1);
goto v___jp_3008_;
}
else
{
lean_object* v_a_3035_; lean_object* v___x_3037_; uint8_t v_isShared_3038_; uint8_t v_isSharedCheck_3042_; 
lean_dec(v_v_2999_);
v_a_3035_ = lean_ctor_get(v___x_3034_, 0);
v_isSharedCheck_3042_ = !lean_is_exclusive(v___x_3034_);
if (v_isSharedCheck_3042_ == 0)
{
v___x_3037_ = v___x_3034_;
v_isShared_3038_ = v_isSharedCheck_3042_;
goto v_resetjp_3036_;
}
else
{
lean_inc(v_a_3035_);
lean_dec(v___x_3034_);
v___x_3037_ = lean_box(0);
v_isShared_3038_ = v_isSharedCheck_3042_;
goto v_resetjp_3036_;
}
v_resetjp_3036_:
{
lean_object* v___x_3040_; 
if (v_isShared_3038_ == 0)
{
lean_ctor_set_tag(v___x_3037_, 2);
v___x_3040_ = v___x_3037_;
goto v_reusejp_3039_;
}
else
{
lean_object* v_reuseFailAlloc_3041_; 
v_reuseFailAlloc_3041_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3041_, 0, v_a_3035_);
v___x_3040_ = v_reuseFailAlloc_3041_;
goto v_reusejp_3039_;
}
v_reusejp_3039_:
{
v_a_3003_ = v___x_3040_;
goto v___jp_3002_;
}
}
}
}
}
else
{
lean_object* v___x_3043_; 
lean_dec_ref_known(v_a_3025_, 1);
lean_inc(v_v_2999_);
v___x_3043_ = l_Lean_Lsp_instFromJsonRenameFile_fromJson(v_v_2999_);
if (lean_obj_tag(v___x_3043_) == 0)
{
lean_dec_ref_known(v___x_3043_, 1);
goto v___jp_3008_;
}
else
{
lean_object* v_a_3044_; lean_object* v___x_3046_; uint8_t v_isShared_3047_; uint8_t v_isSharedCheck_3051_; 
lean_dec(v_v_2999_);
v_a_3044_ = lean_ctor_get(v___x_3043_, 0);
v_isSharedCheck_3051_ = !lean_is_exclusive(v___x_3043_);
if (v_isSharedCheck_3051_ == 0)
{
v___x_3046_ = v___x_3043_;
v_isShared_3047_ = v_isSharedCheck_3051_;
goto v_resetjp_3045_;
}
else
{
lean_inc(v_a_3044_);
lean_dec(v___x_3043_);
v___x_3046_ = lean_box(0);
v_isShared_3047_ = v_isSharedCheck_3051_;
goto v_resetjp_3045_;
}
v_resetjp_3045_:
{
lean_object* v___x_3049_; 
if (v_isShared_3047_ == 0)
{
v___x_3049_ = v___x_3046_;
goto v_reusejp_3048_;
}
else
{
lean_object* v_reuseFailAlloc_3050_; 
v_reuseFailAlloc_3050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3050_, 0, v_a_3044_);
v___x_3049_ = v_reuseFailAlloc_3050_;
goto v_reusejp_3048_;
}
v_reusejp_3048_:
{
v_a_3003_ = v___x_3049_;
goto v___jp_3002_;
}
}
}
}
}
else
{
lean_object* v___x_3052_; 
lean_dec_ref_known(v_a_3025_, 1);
lean_inc(v_v_2999_);
v___x_3052_ = l_Lean_Lsp_instFromJsonCreateFile_fromJson(v_v_2999_);
if (lean_obj_tag(v___x_3052_) == 0)
{
lean_dec_ref_known(v___x_3052_, 1);
goto v___jp_3008_;
}
else
{
lean_object* v_a_3053_; lean_object* v___x_3055_; uint8_t v_isShared_3056_; uint8_t v_isSharedCheck_3060_; 
lean_dec(v_v_2999_);
v_a_3053_ = lean_ctor_get(v___x_3052_, 0);
v_isSharedCheck_3060_ = !lean_is_exclusive(v___x_3052_);
if (v_isSharedCheck_3060_ == 0)
{
v___x_3055_ = v___x_3052_;
v_isShared_3056_ = v_isSharedCheck_3060_;
goto v_resetjp_3054_;
}
else
{
lean_inc(v_a_3053_);
lean_dec(v___x_3052_);
v___x_3055_ = lean_box(0);
v_isShared_3056_ = v_isSharedCheck_3060_;
goto v_resetjp_3054_;
}
v_resetjp_3054_:
{
lean_object* v___x_3058_; 
if (v_isShared_3056_ == 0)
{
lean_ctor_set_tag(v___x_3055_, 0);
v___x_3058_ = v___x_3055_;
goto v_reusejp_3057_;
}
else
{
lean_object* v_reuseFailAlloc_3059_; 
v_reuseFailAlloc_3059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3059_, 0, v_a_3053_);
v___x_3058_ = v_reuseFailAlloc_3059_;
goto v_reusejp_3057_;
}
v_reusejp_3057_:
{
v_a_3003_ = v___x_3058_;
goto v___jp_3002_;
}
}
}
}
}
else
{
lean_object* v___x_3061_; 
v___x_3061_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__0_spec__0_spec__1_spec__4___lam__0(v_a_3025_);
v___y_3021_ = v___x_3061_;
goto v___jp_3020_;
}
}
v___jp_3002_:
{
size_t v___x_3004_; size_t v___x_3005_; lean_object* v___x_3006_; 
v___x_3004_ = ((size_t)1ULL);
v___x_3005_ = lean_usize_add(v_i_2995_, v___x_3004_);
v___x_3006_ = lean_array_uset(v_bs_x27_3001_, v_i_2995_, v_a_3003_);
v_i_2995_ = v___x_3005_;
v_bs_2996_ = v___x_3006_;
goto _start;
}
v___jp_3008_:
{
lean_object* v___x_3009_; 
v___x_3009_ = l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson(v_v_2999_);
if (lean_obj_tag(v___x_3009_) == 0)
{
lean_object* v_a_3010_; lean_object* v___x_3012_; uint8_t v_isShared_3013_; uint8_t v_isSharedCheck_3017_; 
lean_dec_ref(v_bs_x27_3001_);
v_a_3010_ = lean_ctor_get(v___x_3009_, 0);
v_isSharedCheck_3017_ = !lean_is_exclusive(v___x_3009_);
if (v_isSharedCheck_3017_ == 0)
{
v___x_3012_ = v___x_3009_;
v_isShared_3013_ = v_isSharedCheck_3017_;
goto v_resetjp_3011_;
}
else
{
lean_inc(v_a_3010_);
lean_dec(v___x_3009_);
v___x_3012_ = lean_box(0);
v_isShared_3013_ = v_isSharedCheck_3017_;
goto v_resetjp_3011_;
}
v_resetjp_3011_:
{
lean_object* v___x_3015_; 
if (v_isShared_3013_ == 0)
{
v___x_3015_ = v___x_3012_;
goto v_reusejp_3014_;
}
else
{
lean_object* v_reuseFailAlloc_3016_; 
v_reuseFailAlloc_3016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3016_, 0, v_a_3010_);
v___x_3015_ = v_reuseFailAlloc_3016_;
goto v_reusejp_3014_;
}
v_reusejp_3014_:
{
return v___x_3015_;
}
}
}
else
{
lean_object* v_a_3018_; lean_object* v___x_3019_; 
v_a_3018_ = lean_ctor_get(v___x_3009_, 0);
lean_inc(v_a_3018_);
lean_dec_ref_known(v___x_3009_, 1);
v___x_3019_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3019_, 0, v_a_3018_);
v_a_3003_ = v___x_3019_;
goto v___jp_3002_;
}
}
v___jp_3020_:
{
if (lean_obj_tag(v___y_3021_) == 0)
{
lean_dec_ref_known(v___y_3021_, 1);
goto v___jp_3008_;
}
else
{
lean_object* v_a_3022_; 
lean_dec(v_v_2999_);
v_a_3022_ = lean_ctor_get(v___y_3021_, 0);
lean_inc(v_a_3022_);
lean_dec_ref_known(v___y_3021_, 1);
v_a_3003_ = v_a_3022_;
goto v___jp_3002_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_sz_3062_, lean_object* v_i_3063_, lean_object* v_bs_3064_){
_start:
{
size_t v_sz_boxed_3065_; size_t v_i_boxed_3066_; lean_object* v_res_3067_; 
v_sz_boxed_3065_ = lean_unbox_usize(v_sz_3062_);
lean_dec(v_sz_3062_);
v_i_boxed_3066_ = lean_unbox_usize(v_i_3063_);
lean_dec(v_i_3063_);
v_res_3067_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__0_spec__0_spec__1_spec__4(v_sz_boxed_3065_, v_i_boxed_3066_, v_bs_3064_);
return v_res_3067_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__0_spec__0_spec__1(lean_object* v_x_3068_){
_start:
{
if (lean_obj_tag(v_x_3068_) == 4)
{
lean_object* v_elems_3069_; size_t v_sz_3070_; size_t v___x_3071_; lean_object* v___x_3072_; 
v_elems_3069_ = lean_ctor_get(v_x_3068_, 0);
lean_inc_ref(v_elems_3069_);
lean_dec_ref_known(v_x_3068_, 1);
v_sz_3070_ = lean_array_size(v_elems_3069_);
v___x_3071_ = ((size_t)0ULL);
v___x_3072_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__0_spec__0_spec__1_spec__4(v_sz_3070_, v___x_3071_, v_elems_3069_);
return v___x_3072_;
}
else
{
lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; 
v___x_3073_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCommand_fromJson_spec__0_spec__0_spec__1___closed__0));
v___x_3074_ = lean_unsigned_to_nat(80u);
v___x_3075_ = l_Lean_Json_pretty(v_x_3068_, v___x_3074_);
v___x_3076_ = lean_string_append(v___x_3073_, v___x_3075_);
lean_dec_ref(v___x_3075_);
v___x_3077_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCommand_fromJson_spec__0_spec__0_spec__1___closed__1));
v___x_3078_ = lean_string_append(v___x_3076_, v___x_3077_);
v___x_3079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3079_, 0, v___x_3078_);
return v___x_3079_;
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__0_spec__0(lean_object* v_x_3082_){
_start:
{
if (lean_obj_tag(v_x_3082_) == 0)
{
lean_object* v___x_3083_; 
v___x_3083_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__0_spec__0___closed__0));
return v___x_3083_;
}
else
{
lean_object* v___x_3084_; 
v___x_3084_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__0_spec__0_spec__1(v_x_3082_);
if (lean_obj_tag(v___x_3084_) == 0)
{
lean_object* v_a_3085_; lean_object* v___x_3087_; uint8_t v_isShared_3088_; uint8_t v_isSharedCheck_3092_; 
v_a_3085_ = lean_ctor_get(v___x_3084_, 0);
v_isSharedCheck_3092_ = !lean_is_exclusive(v___x_3084_);
if (v_isSharedCheck_3092_ == 0)
{
v___x_3087_ = v___x_3084_;
v_isShared_3088_ = v_isSharedCheck_3092_;
goto v_resetjp_3086_;
}
else
{
lean_inc(v_a_3085_);
lean_dec(v___x_3084_);
v___x_3087_ = lean_box(0);
v_isShared_3088_ = v_isSharedCheck_3092_;
goto v_resetjp_3086_;
}
v_resetjp_3086_:
{
lean_object* v___x_3090_; 
if (v_isShared_3088_ == 0)
{
v___x_3090_ = v___x_3087_;
goto v_reusejp_3089_;
}
else
{
lean_object* v_reuseFailAlloc_3091_; 
v_reuseFailAlloc_3091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3091_, 0, v_a_3085_);
v___x_3090_ = v_reuseFailAlloc_3091_;
goto v_reusejp_3089_;
}
v_reusejp_3089_:
{
return v___x_3090_;
}
}
}
else
{
lean_object* v_a_3093_; lean_object* v___x_3095_; uint8_t v_isShared_3096_; uint8_t v_isSharedCheck_3101_; 
v_a_3093_ = lean_ctor_get(v___x_3084_, 0);
v_isSharedCheck_3101_ = !lean_is_exclusive(v___x_3084_);
if (v_isSharedCheck_3101_ == 0)
{
v___x_3095_ = v___x_3084_;
v_isShared_3096_ = v_isSharedCheck_3101_;
goto v_resetjp_3094_;
}
else
{
lean_inc(v_a_3093_);
lean_dec(v___x_3084_);
v___x_3095_ = lean_box(0);
v_isShared_3096_ = v_isSharedCheck_3101_;
goto v_resetjp_3094_;
}
v_resetjp_3094_:
{
lean_object* v___x_3097_; lean_object* v___x_3099_; 
v___x_3097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3097_, 0, v_a_3093_);
if (v_isShared_3096_ == 0)
{
lean_ctor_set(v___x_3095_, 0, v___x_3097_);
v___x_3099_ = v___x_3095_;
goto v_reusejp_3098_;
}
else
{
lean_object* v_reuseFailAlloc_3100_; 
v_reuseFailAlloc_3100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3100_, 0, v___x_3097_);
v___x_3099_ = v_reuseFailAlloc_3100_;
goto v_reusejp_3098_;
}
v_reusejp_3098_:
{
return v___x_3099_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__0(lean_object* v_j_3102_, lean_object* v_k_3103_){
_start:
{
lean_object* v___x_3104_; lean_object* v___x_3105_; 
v___x_3104_ = l_Lean_Json_getObjValD(v_j_3102_, v_k_3103_);
v___x_3105_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__0_spec__0(v___x_3104_);
return v___x_3105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__0___boxed(lean_object* v_j_3106_, lean_object* v_k_3107_){
_start:
{
lean_object* v_res_3108_; 
v_res_3108_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__0(v_j_3106_, v_k_3107_);
lean_dec_ref(v_k_3107_);
return v_res_3108_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__2(void){
_start:
{
uint8_t v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; 
v___x_3114_ = 1;
v___x_3115_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__1));
v___x_3116_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3115_, v___x_3114_);
return v___x_3116_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__3(void){
_start:
{
lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; 
v___x_3117_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__5));
v___x_3118_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__2, &l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__2);
v___x_3119_ = lean_string_append(v___x_3118_, v___x_3117_);
return v___x_3119_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__6(void){
_start:
{
uint8_t v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; 
v___x_3123_ = 1;
v___x_3124_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__5));
v___x_3125_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3124_, v___x_3123_);
return v___x_3125_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__7(void){
_start:
{
lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; 
v___x_3126_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__6, &l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__6);
v___x_3127_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__3, &l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__3);
v___x_3128_ = lean_string_append(v___x_3127_, v___x_3126_);
return v___x_3128_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__8(void){
_start:
{
lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; 
v___x_3129_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_3130_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__7, &l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__7);
v___x_3131_ = lean_string_append(v___x_3130_, v___x_3129_);
return v___x_3131_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__11(void){
_start:
{
uint8_t v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; 
v___x_3135_ = 1;
v___x_3136_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__10));
v___x_3137_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3136_, v___x_3135_);
return v___x_3137_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__12(void){
_start:
{
lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; 
v___x_3138_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__11, &l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__11);
v___x_3139_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__3, &l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__3);
v___x_3140_ = lean_string_append(v___x_3139_, v___x_3138_);
return v___x_3140_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__13(void){
_start:
{
lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; 
v___x_3141_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_3142_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__12, &l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__12);
v___x_3143_ = lean_string_append(v___x_3142_, v___x_3141_);
return v___x_3143_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__16(void){
_start:
{
uint8_t v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; 
v___x_3147_ = 1;
v___x_3148_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__15));
v___x_3149_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3148_, v___x_3147_);
return v___x_3149_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__17(void){
_start:
{
lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; 
v___x_3150_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__16, &l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__16_once, _init_l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__16);
v___x_3151_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__3, &l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__3);
v___x_3152_ = lean_string_append(v___x_3151_, v___x_3150_);
return v___x_3152_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__18(void){
_start:
{
lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; 
v___x_3153_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_3154_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__17, &l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__17_once, _init_l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__17);
v___x_3155_ = lean_string_append(v___x_3154_, v___x_3153_);
return v___x_3155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson(lean_object* v_json_3156_){
_start:
{
lean_object* v___x_3157_; lean_object* v___x_3158_; 
v___x_3157_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkspaceEdit_toJson___closed__0));
lean_inc(v_json_3156_);
v___x_3158_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__2(v_json_3156_, v___x_3157_);
if (lean_obj_tag(v___x_3158_) == 0)
{
lean_object* v_a_3159_; lean_object* v___x_3161_; uint8_t v_isShared_3162_; uint8_t v_isSharedCheck_3168_; 
lean_dec(v_json_3156_);
v_a_3159_ = lean_ctor_get(v___x_3158_, 0);
v_isSharedCheck_3168_ = !lean_is_exclusive(v___x_3158_);
if (v_isSharedCheck_3168_ == 0)
{
v___x_3161_ = v___x_3158_;
v_isShared_3162_ = v_isSharedCheck_3168_;
goto v_resetjp_3160_;
}
else
{
lean_inc(v_a_3159_);
lean_dec(v___x_3158_);
v___x_3161_ = lean_box(0);
v_isShared_3162_ = v_isSharedCheck_3168_;
goto v_resetjp_3160_;
}
v_resetjp_3160_:
{
lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3166_; 
v___x_3163_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__8, &l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__8);
v___x_3164_ = lean_string_append(v___x_3163_, v_a_3159_);
lean_dec(v_a_3159_);
if (v_isShared_3162_ == 0)
{
lean_ctor_set(v___x_3161_, 0, v___x_3164_);
v___x_3166_ = v___x_3161_;
goto v_reusejp_3165_;
}
else
{
lean_object* v_reuseFailAlloc_3167_; 
v_reuseFailAlloc_3167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3167_, 0, v___x_3164_);
v___x_3166_ = v_reuseFailAlloc_3167_;
goto v_reusejp_3165_;
}
v_reusejp_3165_:
{
return v___x_3166_;
}
}
}
else
{
if (lean_obj_tag(v___x_3158_) == 0)
{
lean_object* v_a_3169_; lean_object* v___x_3171_; uint8_t v_isShared_3172_; uint8_t v_isSharedCheck_3176_; 
lean_dec(v_json_3156_);
v_a_3169_ = lean_ctor_get(v___x_3158_, 0);
v_isSharedCheck_3176_ = !lean_is_exclusive(v___x_3158_);
if (v_isSharedCheck_3176_ == 0)
{
v___x_3171_ = v___x_3158_;
v_isShared_3172_ = v_isSharedCheck_3176_;
goto v_resetjp_3170_;
}
else
{
lean_inc(v_a_3169_);
lean_dec(v___x_3158_);
v___x_3171_ = lean_box(0);
v_isShared_3172_ = v_isSharedCheck_3176_;
goto v_resetjp_3170_;
}
v_resetjp_3170_:
{
lean_object* v___x_3174_; 
if (v_isShared_3172_ == 0)
{
lean_ctor_set_tag(v___x_3171_, 0);
v___x_3174_ = v___x_3171_;
goto v_reusejp_3173_;
}
else
{
lean_object* v_reuseFailAlloc_3175_; 
v_reuseFailAlloc_3175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3175_, 0, v_a_3169_);
v___x_3174_ = v_reuseFailAlloc_3175_;
goto v_reusejp_3173_;
}
v_reusejp_3173_:
{
return v___x_3174_;
}
}
}
else
{
lean_object* v_a_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; 
v_a_3177_ = lean_ctor_get(v___x_3158_, 0);
lean_inc(v_a_3177_);
lean_dec_ref_known(v___x_3158_, 1);
v___x_3178_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkspaceEdit_toJson___closed__1));
lean_inc(v_json_3156_);
v___x_3179_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__0(v_json_3156_, v___x_3178_);
if (lean_obj_tag(v___x_3179_) == 0)
{
lean_object* v_a_3180_; lean_object* v___x_3182_; uint8_t v_isShared_3183_; uint8_t v_isSharedCheck_3189_; 
lean_dec(v_a_3177_);
lean_dec(v_json_3156_);
v_a_3180_ = lean_ctor_get(v___x_3179_, 0);
v_isSharedCheck_3189_ = !lean_is_exclusive(v___x_3179_);
if (v_isSharedCheck_3189_ == 0)
{
v___x_3182_ = v___x_3179_;
v_isShared_3183_ = v_isSharedCheck_3189_;
goto v_resetjp_3181_;
}
else
{
lean_inc(v_a_3180_);
lean_dec(v___x_3179_);
v___x_3182_ = lean_box(0);
v_isShared_3183_ = v_isSharedCheck_3189_;
goto v_resetjp_3181_;
}
v_resetjp_3181_:
{
lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3187_; 
v___x_3184_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__13, &l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__13);
v___x_3185_ = lean_string_append(v___x_3184_, v_a_3180_);
lean_dec(v_a_3180_);
if (v_isShared_3183_ == 0)
{
lean_ctor_set(v___x_3182_, 0, v___x_3185_);
v___x_3187_ = v___x_3182_;
goto v_reusejp_3186_;
}
else
{
lean_object* v_reuseFailAlloc_3188_; 
v_reuseFailAlloc_3188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3188_, 0, v___x_3185_);
v___x_3187_ = v_reuseFailAlloc_3188_;
goto v_reusejp_3186_;
}
v_reusejp_3186_:
{
return v___x_3187_;
}
}
}
else
{
if (lean_obj_tag(v___x_3179_) == 0)
{
lean_object* v_a_3190_; lean_object* v___x_3192_; uint8_t v_isShared_3193_; uint8_t v_isSharedCheck_3197_; 
lean_dec(v_a_3177_);
lean_dec(v_json_3156_);
v_a_3190_ = lean_ctor_get(v___x_3179_, 0);
v_isSharedCheck_3197_ = !lean_is_exclusive(v___x_3179_);
if (v_isSharedCheck_3197_ == 0)
{
v___x_3192_ = v___x_3179_;
v_isShared_3193_ = v_isSharedCheck_3197_;
goto v_resetjp_3191_;
}
else
{
lean_inc(v_a_3190_);
lean_dec(v___x_3179_);
v___x_3192_ = lean_box(0);
v_isShared_3193_ = v_isSharedCheck_3197_;
goto v_resetjp_3191_;
}
v_resetjp_3191_:
{
lean_object* v___x_3195_; 
if (v_isShared_3193_ == 0)
{
lean_ctor_set_tag(v___x_3192_, 0);
v___x_3195_ = v___x_3192_;
goto v_reusejp_3194_;
}
else
{
lean_object* v_reuseFailAlloc_3196_; 
v_reuseFailAlloc_3196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3196_, 0, v_a_3190_);
v___x_3195_ = v_reuseFailAlloc_3196_;
goto v_reusejp_3194_;
}
v_reusejp_3194_:
{
return v___x_3195_;
}
}
}
else
{
lean_object* v_a_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; 
v_a_3198_ = lean_ctor_get(v___x_3179_, 0);
lean_inc(v_a_3198_);
lean_dec_ref_known(v___x_3179_, 1);
v___x_3199_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkspaceEdit_toJson___closed__2));
v___x_3200_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__1(v_json_3156_, v___x_3199_);
if (lean_obj_tag(v___x_3200_) == 0)
{
lean_object* v_a_3201_; lean_object* v___x_3203_; uint8_t v_isShared_3204_; uint8_t v_isSharedCheck_3210_; 
lean_dec(v_a_3198_);
lean_dec(v_a_3177_);
v_a_3201_ = lean_ctor_get(v___x_3200_, 0);
v_isSharedCheck_3210_ = !lean_is_exclusive(v___x_3200_);
if (v_isSharedCheck_3210_ == 0)
{
v___x_3203_ = v___x_3200_;
v_isShared_3204_ = v_isSharedCheck_3210_;
goto v_resetjp_3202_;
}
else
{
lean_inc(v_a_3201_);
lean_dec(v___x_3200_);
v___x_3203_ = lean_box(0);
v_isShared_3204_ = v_isSharedCheck_3210_;
goto v_resetjp_3202_;
}
v_resetjp_3202_:
{
lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3208_; 
v___x_3205_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__18, &l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__18_once, _init_l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__18);
v___x_3206_ = lean_string_append(v___x_3205_, v_a_3201_);
lean_dec(v_a_3201_);
if (v_isShared_3204_ == 0)
{
lean_ctor_set(v___x_3203_, 0, v___x_3206_);
v___x_3208_ = v___x_3203_;
goto v_reusejp_3207_;
}
else
{
lean_object* v_reuseFailAlloc_3209_; 
v_reuseFailAlloc_3209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3209_, 0, v___x_3206_);
v___x_3208_ = v_reuseFailAlloc_3209_;
goto v_reusejp_3207_;
}
v_reusejp_3207_:
{
return v___x_3208_;
}
}
}
else
{
if (lean_obj_tag(v___x_3200_) == 0)
{
lean_object* v_a_3211_; lean_object* v___x_3213_; uint8_t v_isShared_3214_; uint8_t v_isSharedCheck_3218_; 
lean_dec(v_a_3198_);
lean_dec(v_a_3177_);
v_a_3211_ = lean_ctor_get(v___x_3200_, 0);
v_isSharedCheck_3218_ = !lean_is_exclusive(v___x_3200_);
if (v_isSharedCheck_3218_ == 0)
{
v___x_3213_ = v___x_3200_;
v_isShared_3214_ = v_isSharedCheck_3218_;
goto v_resetjp_3212_;
}
else
{
lean_inc(v_a_3211_);
lean_dec(v___x_3200_);
v___x_3213_ = lean_box(0);
v_isShared_3214_ = v_isSharedCheck_3218_;
goto v_resetjp_3212_;
}
v_resetjp_3212_:
{
lean_object* v___x_3216_; 
if (v_isShared_3214_ == 0)
{
lean_ctor_set_tag(v___x_3213_, 0);
v___x_3216_ = v___x_3213_;
goto v_reusejp_3215_;
}
else
{
lean_object* v_reuseFailAlloc_3217_; 
v_reuseFailAlloc_3217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3217_, 0, v_a_3211_);
v___x_3216_ = v_reuseFailAlloc_3217_;
goto v_reusejp_3215_;
}
v_reusejp_3215_:
{
return v___x_3216_;
}
}
}
else
{
lean_object* v_a_3219_; lean_object* v___x_3221_; uint8_t v_isShared_3222_; uint8_t v_isSharedCheck_3227_; 
v_a_3219_ = lean_ctor_get(v___x_3200_, 0);
v_isSharedCheck_3227_ = !lean_is_exclusive(v___x_3200_);
if (v_isSharedCheck_3227_ == 0)
{
v___x_3221_ = v___x_3200_;
v_isShared_3222_ = v_isSharedCheck_3227_;
goto v_resetjp_3220_;
}
else
{
lean_inc(v_a_3219_);
lean_dec(v___x_3200_);
v___x_3221_ = lean_box(0);
v_isShared_3222_ = v_isSharedCheck_3227_;
goto v_resetjp_3220_;
}
v_resetjp_3220_:
{
lean_object* v___x_3223_; lean_object* v___x_3225_; 
v___x_3223_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3223_, 0, v_a_3177_);
lean_ctor_set(v___x_3223_, 1, v_a_3198_);
lean_ctor_set(v___x_3223_, 2, v_a_3219_);
if (v_isShared_3222_ == 0)
{
lean_ctor_set(v___x_3221_, 0, v___x_3223_);
v___x_3225_ = v___x_3221_;
goto v_reusejp_3224_;
}
else
{
lean_object* v_reuseFailAlloc_3226_; 
v_reuseFailAlloc_3226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3226_, 0, v___x_3223_);
v___x_3225_ = v_reuseFailAlloc_3226_;
goto v_reusejp_3224_;
}
v_reusejp_3224_:
{
return v___x_3225_;
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__1_spec__2_spec__4_spec__7(lean_object* v_cmp_3228_, lean_object* v_00_u03b2_3229_, lean_object* v_k_3230_, lean_object* v_v_3231_, lean_object* v_t_3232_, lean_object* v_hl_3233_){
_start:
{
lean_object* v___x_3234_; 
v___x_3234_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__1_spec__2_spec__4_spec__7___redArg(v_cmp_3228_, v_k_3230_, v_v_3231_, v_t_3232_);
return v___x_3234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_WorkspaceEdit_instAppend___lam__0(lean_object* v_b_u2082_3240_, lean_object* v_x_3241_){
_start:
{
lean_object* v___x_3242_; 
v___x_3242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3242_, 0, v_b_u2082_3240_);
return v___x_3242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_WorkspaceEdit_instAppend___lam__0___boxed(lean_object* v_b_u2082_3243_, lean_object* v_x_3244_){
_start:
{
lean_object* v_res_3245_; 
v_res_3245_ = l_Lean_Lsp_WorkspaceEdit_instAppend___lam__0(v_b_u2082_3243_, v_x_3244_);
lean_dec(v_x_3244_);
return v_res_3245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_WorkspaceEdit_instAppend___lam__1(lean_object* v___x_3246_, lean_object* v_t_3247_, lean_object* v_a_3248_, lean_object* v_b_u2082_3249_){
_start:
{
lean_object* v___f_3250_; lean_object* v___x_3251_; 
v___f_3250_ = lean_alloc_closure((void*)(l_Lean_Lsp_WorkspaceEdit_instAppend___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3250_, 0, v_b_u2082_3249_);
v___x_3251_ = l_Std_DTreeMap_Internal_Impl_Const_alter___redArg(v___x_3246_, v_a_3248_, v___f_3250_, v_t_3247_);
return v___x_3251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_WorkspaceEdit_instAppend___lam__2(lean_object* v_b_u2082_3252_, lean_object* v_x_3253_){
_start:
{
if (lean_obj_tag(v_x_3253_) == 0)
{
lean_object* v___x_3254_; 
v___x_3254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3254_, 0, v_b_u2082_3252_);
return v___x_3254_;
}
else
{
lean_object* v_val_3255_; lean_object* v___x_3257_; uint8_t v_isShared_3258_; uint8_t v_isSharedCheck_3263_; 
v_val_3255_ = lean_ctor_get(v_x_3253_, 0);
v_isSharedCheck_3263_ = !lean_is_exclusive(v_x_3253_);
if (v_isSharedCheck_3263_ == 0)
{
v___x_3257_ = v_x_3253_;
v_isShared_3258_ = v_isSharedCheck_3263_;
goto v_resetjp_3256_;
}
else
{
lean_inc(v_val_3255_);
lean_dec(v_x_3253_);
v___x_3257_ = lean_box(0);
v_isShared_3258_ = v_isSharedCheck_3263_;
goto v_resetjp_3256_;
}
v_resetjp_3256_:
{
lean_object* v___x_3259_; lean_object* v___x_3261_; 
v___x_3259_ = l_Array_append___redArg(v_val_3255_, v_b_u2082_3252_);
lean_dec_ref(v_b_u2082_3252_);
if (v_isShared_3258_ == 0)
{
lean_ctor_set(v___x_3257_, 0, v___x_3259_);
v___x_3261_ = v___x_3257_;
goto v_reusejp_3260_;
}
else
{
lean_object* v_reuseFailAlloc_3262_; 
v_reuseFailAlloc_3262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3262_, 0, v___x_3259_);
v___x_3261_ = v_reuseFailAlloc_3262_;
goto v_reusejp_3260_;
}
v_reusejp_3260_:
{
return v___x_3261_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_WorkspaceEdit_instAppend___lam__3(lean_object* v___x_3264_, lean_object* v_t_3265_, lean_object* v_a_3266_, lean_object* v_b_u2082_3267_){
_start:
{
lean_object* v___f_3268_; lean_object* v___x_3269_; 
v___f_3268_ = lean_alloc_closure((void*)(l_Lean_Lsp_WorkspaceEdit_instAppend___lam__2), 2, 1);
lean_closure_set(v___f_3268_, 0, v_b_u2082_3267_);
v___x_3269_ = l_Std_DTreeMap_Internal_Impl_Const_alter___redArg(v___x_3264_, v_a_3266_, v___f_3268_, v_t_3265_);
return v___x_3269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_WorkspaceEdit_instAppend___lam__4(lean_object* v_x_3274_, lean_object* v_y_3275_){
_start:
{
lean_object* v_changes_x3f_3276_; lean_object* v_documentChanges_x3f_3277_; lean_object* v_changeAnnotations_x3f_3278_; lean_object* v___y_3280_; lean_object* v___y_3281_; lean_object* v___y_3317_; 
v_changes_x3f_3276_ = lean_ctor_get(v_y_3275_, 0);
lean_inc(v_changes_x3f_3276_);
v_documentChanges_x3f_3277_ = lean_ctor_get(v_y_3275_, 1);
lean_inc(v_documentChanges_x3f_3277_);
v_changeAnnotations_x3f_3278_ = lean_ctor_get(v_y_3275_, 2);
lean_inc(v_changeAnnotations_x3f_3278_);
lean_dec_ref(v_y_3275_);
if (lean_obj_tag(v_changes_x3f_3276_) == 0)
{
lean_object* v_changes_x3f_3330_; 
v_changes_x3f_3330_ = lean_ctor_get(v_x_3274_, 0);
lean_inc(v_changes_x3f_3330_);
v___y_3317_ = v_changes_x3f_3330_;
goto v___jp_3316_;
}
else
{
lean_object* v_changes_x3f_3331_; 
v_changes_x3f_3331_ = lean_ctor_get(v_x_3274_, 0);
lean_inc(v_changes_x3f_3331_);
if (lean_obj_tag(v_changes_x3f_3331_) == 0)
{
v___y_3317_ = v_changes_x3f_3276_;
goto v___jp_3316_;
}
else
{
lean_object* v_val_3332_; lean_object* v_val_3333_; lean_object* v___x_3335_; uint8_t v_isShared_3336_; uint8_t v_isSharedCheck_3342_; 
v_val_3332_ = lean_ctor_get(v_changes_x3f_3276_, 0);
lean_inc(v_val_3332_);
lean_dec_ref_known(v_changes_x3f_3276_, 1);
v_val_3333_ = lean_ctor_get(v_changes_x3f_3331_, 0);
v_isSharedCheck_3342_ = !lean_is_exclusive(v_changes_x3f_3331_);
if (v_isSharedCheck_3342_ == 0)
{
v___x_3335_ = v_changes_x3f_3331_;
v_isShared_3336_ = v_isSharedCheck_3342_;
goto v_resetjp_3334_;
}
else
{
lean_inc(v_val_3333_);
lean_dec(v_changes_x3f_3331_);
v___x_3335_ = lean_box(0);
v_isShared_3336_ = v_isSharedCheck_3342_;
goto v_resetjp_3334_;
}
v_resetjp_3334_:
{
lean_object* v___f_3337_; lean_object* v___x_3338_; lean_object* v___x_3340_; 
v___f_3337_ = ((lean_object*)(l_Lean_Lsp_WorkspaceEdit_instAppend___lam__4___closed__1));
v___x_3338_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3337_, v_val_3333_, v_val_3332_);
if (v_isShared_3336_ == 0)
{
lean_ctor_set(v___x_3335_, 0, v___x_3338_);
v___x_3340_ = v___x_3335_;
goto v_reusejp_3339_;
}
else
{
lean_object* v_reuseFailAlloc_3341_; 
v_reuseFailAlloc_3341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3341_, 0, v___x_3338_);
v___x_3340_ = v_reuseFailAlloc_3341_;
goto v_reusejp_3339_;
}
v_reusejp_3339_:
{
v___y_3317_ = v___x_3340_;
goto v___jp_3316_;
}
}
}
}
v___jp_3279_:
{
if (lean_obj_tag(v_changeAnnotations_x3f_3278_) == 0)
{
lean_object* v_changeAnnotations_x3f_3282_; lean_object* v___x_3284_; uint8_t v_isShared_3285_; uint8_t v_isSharedCheck_3289_; 
v_changeAnnotations_x3f_3282_ = lean_ctor_get(v_x_3274_, 2);
v_isSharedCheck_3289_ = !lean_is_exclusive(v_x_3274_);
if (v_isSharedCheck_3289_ == 0)
{
lean_object* v_unused_3290_; lean_object* v_unused_3291_; 
v_unused_3290_ = lean_ctor_get(v_x_3274_, 1);
lean_dec(v_unused_3290_);
v_unused_3291_ = lean_ctor_get(v_x_3274_, 0);
lean_dec(v_unused_3291_);
v___x_3284_ = v_x_3274_;
v_isShared_3285_ = v_isSharedCheck_3289_;
goto v_resetjp_3283_;
}
else
{
lean_inc(v_changeAnnotations_x3f_3282_);
lean_dec(v_x_3274_);
v___x_3284_ = lean_box(0);
v_isShared_3285_ = v_isSharedCheck_3289_;
goto v_resetjp_3283_;
}
v_resetjp_3283_:
{
lean_object* v___x_3287_; 
if (v_isShared_3285_ == 0)
{
lean_ctor_set(v___x_3284_, 1, v___y_3281_);
lean_ctor_set(v___x_3284_, 0, v___y_3280_);
v___x_3287_ = v___x_3284_;
goto v_reusejp_3286_;
}
else
{
lean_object* v_reuseFailAlloc_3288_; 
v_reuseFailAlloc_3288_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3288_, 0, v___y_3280_);
lean_ctor_set(v_reuseFailAlloc_3288_, 1, v___y_3281_);
lean_ctor_set(v_reuseFailAlloc_3288_, 2, v_changeAnnotations_x3f_3282_);
v___x_3287_ = v_reuseFailAlloc_3288_;
goto v_reusejp_3286_;
}
v_reusejp_3286_:
{
return v___x_3287_;
}
}
}
else
{
lean_object* v_changeAnnotations_x3f_3292_; lean_object* v___x_3294_; uint8_t v_isShared_3295_; uint8_t v_isSharedCheck_3313_; 
v_changeAnnotations_x3f_3292_ = lean_ctor_get(v_x_3274_, 2);
v_isSharedCheck_3313_ = !lean_is_exclusive(v_x_3274_);
if (v_isSharedCheck_3313_ == 0)
{
lean_object* v_unused_3314_; lean_object* v_unused_3315_; 
v_unused_3314_ = lean_ctor_get(v_x_3274_, 1);
lean_dec(v_unused_3314_);
v_unused_3315_ = lean_ctor_get(v_x_3274_, 0);
lean_dec(v_unused_3315_);
v___x_3294_ = v_x_3274_;
v_isShared_3295_ = v_isSharedCheck_3313_;
goto v_resetjp_3293_;
}
else
{
lean_inc(v_changeAnnotations_x3f_3292_);
lean_dec(v_x_3274_);
v___x_3294_ = lean_box(0);
v_isShared_3295_ = v_isSharedCheck_3313_;
goto v_resetjp_3293_;
}
v_resetjp_3293_:
{
if (lean_obj_tag(v_changeAnnotations_x3f_3292_) == 0)
{
lean_object* v___x_3297_; 
if (v_isShared_3295_ == 0)
{
lean_ctor_set(v___x_3294_, 2, v_changeAnnotations_x3f_3278_);
lean_ctor_set(v___x_3294_, 1, v___y_3281_);
lean_ctor_set(v___x_3294_, 0, v___y_3280_);
v___x_3297_ = v___x_3294_;
goto v_reusejp_3296_;
}
else
{
lean_object* v_reuseFailAlloc_3298_; 
v_reuseFailAlloc_3298_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3298_, 0, v___y_3280_);
lean_ctor_set(v_reuseFailAlloc_3298_, 1, v___y_3281_);
lean_ctor_set(v_reuseFailAlloc_3298_, 2, v_changeAnnotations_x3f_3278_);
v___x_3297_ = v_reuseFailAlloc_3298_;
goto v_reusejp_3296_;
}
v_reusejp_3296_:
{
return v___x_3297_;
}
}
else
{
lean_object* v_val_3299_; lean_object* v_val_3300_; lean_object* v___x_3302_; uint8_t v_isShared_3303_; uint8_t v_isSharedCheck_3312_; 
v_val_3299_ = lean_ctor_get(v_changeAnnotations_x3f_3278_, 0);
lean_inc(v_val_3299_);
lean_dec_ref_known(v_changeAnnotations_x3f_3278_, 1);
v_val_3300_ = lean_ctor_get(v_changeAnnotations_x3f_3292_, 0);
v_isSharedCheck_3312_ = !lean_is_exclusive(v_changeAnnotations_x3f_3292_);
if (v_isSharedCheck_3312_ == 0)
{
v___x_3302_ = v_changeAnnotations_x3f_3292_;
v_isShared_3303_ = v_isSharedCheck_3312_;
goto v_resetjp_3301_;
}
else
{
lean_inc(v_val_3300_);
lean_dec(v_changeAnnotations_x3f_3292_);
v___x_3302_ = lean_box(0);
v_isShared_3303_ = v_isSharedCheck_3312_;
goto v_resetjp_3301_;
}
v_resetjp_3301_:
{
lean_object* v___f_3304_; lean_object* v___x_3305_; lean_object* v___x_3307_; 
v___f_3304_ = ((lean_object*)(l_Lean_Lsp_WorkspaceEdit_instAppend___lam__4___closed__0));
v___x_3305_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3304_, v_val_3300_, v_val_3299_);
if (v_isShared_3303_ == 0)
{
lean_ctor_set(v___x_3302_, 0, v___x_3305_);
v___x_3307_ = v___x_3302_;
goto v_reusejp_3306_;
}
else
{
lean_object* v_reuseFailAlloc_3311_; 
v_reuseFailAlloc_3311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3311_, 0, v___x_3305_);
v___x_3307_ = v_reuseFailAlloc_3311_;
goto v_reusejp_3306_;
}
v_reusejp_3306_:
{
lean_object* v___x_3309_; 
if (v_isShared_3295_ == 0)
{
lean_ctor_set(v___x_3294_, 2, v___x_3307_);
lean_ctor_set(v___x_3294_, 1, v___y_3281_);
lean_ctor_set(v___x_3294_, 0, v___y_3280_);
v___x_3309_ = v___x_3294_;
goto v_reusejp_3308_;
}
else
{
lean_object* v_reuseFailAlloc_3310_; 
v_reuseFailAlloc_3310_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3310_, 0, v___y_3280_);
lean_ctor_set(v_reuseFailAlloc_3310_, 1, v___y_3281_);
lean_ctor_set(v_reuseFailAlloc_3310_, 2, v___x_3307_);
v___x_3309_ = v_reuseFailAlloc_3310_;
goto v_reusejp_3308_;
}
v_reusejp_3308_:
{
return v___x_3309_;
}
}
}
}
}
}
}
v___jp_3316_:
{
if (lean_obj_tag(v_documentChanges_x3f_3277_) == 0)
{
lean_object* v_documentChanges_x3f_3318_; 
v_documentChanges_x3f_3318_ = lean_ctor_get(v_x_3274_, 1);
lean_inc(v_documentChanges_x3f_3318_);
v___y_3280_ = v___y_3317_;
v___y_3281_ = v_documentChanges_x3f_3318_;
goto v___jp_3279_;
}
else
{
lean_object* v_documentChanges_x3f_3319_; 
v_documentChanges_x3f_3319_ = lean_ctor_get(v_x_3274_, 1);
lean_inc(v_documentChanges_x3f_3319_);
if (lean_obj_tag(v_documentChanges_x3f_3319_) == 0)
{
v___y_3280_ = v___y_3317_;
v___y_3281_ = v_documentChanges_x3f_3277_;
goto v___jp_3279_;
}
else
{
lean_object* v_val_3320_; lean_object* v_val_3321_; lean_object* v___x_3323_; uint8_t v_isShared_3324_; uint8_t v_isSharedCheck_3329_; 
v_val_3320_ = lean_ctor_get(v_documentChanges_x3f_3277_, 0);
lean_inc(v_val_3320_);
lean_dec_ref_known(v_documentChanges_x3f_3277_, 1);
v_val_3321_ = lean_ctor_get(v_documentChanges_x3f_3319_, 0);
v_isSharedCheck_3329_ = !lean_is_exclusive(v_documentChanges_x3f_3319_);
if (v_isSharedCheck_3329_ == 0)
{
v___x_3323_ = v_documentChanges_x3f_3319_;
v_isShared_3324_ = v_isSharedCheck_3329_;
goto v_resetjp_3322_;
}
else
{
lean_inc(v_val_3321_);
lean_dec(v_documentChanges_x3f_3319_);
v___x_3323_ = lean_box(0);
v_isShared_3324_ = v_isSharedCheck_3329_;
goto v_resetjp_3322_;
}
v_resetjp_3322_:
{
lean_object* v___x_3325_; lean_object* v___x_3327_; 
v___x_3325_ = l_Array_append___redArg(v_val_3321_, v_val_3320_);
lean_dec(v_val_3320_);
if (v_isShared_3324_ == 0)
{
lean_ctor_set(v___x_3323_, 0, v___x_3325_);
v___x_3327_ = v___x_3323_;
goto v_reusejp_3326_;
}
else
{
lean_object* v_reuseFailAlloc_3328_; 
v_reuseFailAlloc_3328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3328_, 0, v___x_3325_);
v___x_3327_ = v_reuseFailAlloc_3328_;
goto v_reusejp_3326_;
}
v_reusejp_3326_:
{
v___y_3280_ = v___y_3317_;
v___y_3281_ = v___x_3327_;
goto v___jp_3279_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_WorkspaceEdit_ofTextDocumentEdit(lean_object* v_e_3345_){
_start:
{
lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; 
v___x_3346_ = lean_box(0);
v___x_3347_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3347_, 0, v_e_3345_);
v___x_3348_ = lean_unsigned_to_nat(1u);
v___x_3349_ = lean_mk_empty_array_with_capacity(v___x_3348_);
v___x_3350_ = lean_array_push(v___x_3349_, v___x_3347_);
v___x_3351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3351_, 0, v___x_3350_);
v___x_3352_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3352_, 0, v___x_3346_);
lean_ctor_set(v___x_3352_, 1, v___x_3351_);
lean_ctor_set(v___x_3352_, 2, v___x_3346_);
return v___x_3352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_WorkspaceEdit_ofTextEdit(lean_object* v_doc_3353_, lean_object* v_te_3354_){
_start:
{
lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; 
v___x_3355_ = lean_unsigned_to_nat(1u);
v___x_3356_ = lean_mk_empty_array_with_capacity(v___x_3355_);
v___x_3357_ = lean_array_push(v___x_3356_, v_te_3354_);
v___x_3358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3358_, 0, v_doc_3353_);
lean_ctor_set(v___x_3358_, 1, v___x_3357_);
v___x_3359_ = l_Lean_Lsp_WorkspaceEdit_ofTextDocumentEdit(v___x_3358_);
return v___x_3359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonApplyWorkspaceEditParams_toJson(lean_object* v_x_3361_){
_start:
{
lean_object* v_label_x3f_3362_; lean_object* v_edit_3363_; lean_object* v___x_3365_; uint8_t v_isShared_3366_; uint8_t v_isSharedCheck_3381_; 
v_label_x3f_3362_ = lean_ctor_get(v_x_3361_, 0);
v_edit_3363_ = lean_ctor_get(v_x_3361_, 1);
v_isSharedCheck_3381_ = !lean_is_exclusive(v_x_3361_);
if (v_isSharedCheck_3381_ == 0)
{
v___x_3365_ = v_x_3361_;
v_isShared_3366_ = v_isSharedCheck_3381_;
goto v_resetjp_3364_;
}
else
{
lean_inc(v_edit_3363_);
lean_inc(v_label_x3f_3362_);
lean_dec(v_x_3361_);
v___x_3365_ = lean_box(0);
v_isShared_3366_ = v_isSharedCheck_3381_;
goto v_resetjp_3364_;
}
v_resetjp_3364_:
{
lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3372_; 
v___x_3367_ = ((lean_object*)(l_Lean_Lsp_instToJsonChangeAnnotation_toJson___closed__0));
v___x_3368_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextEdit_toJson_spec__1(v___x_3367_, v_label_x3f_3362_);
v___x_3369_ = ((lean_object*)(l_Lean_Lsp_instToJsonApplyWorkspaceEditParams_toJson___closed__0));
v___x_3370_ = l_Lean_Lsp_instToJsonWorkspaceEdit_toJson(v_edit_3363_);
if (v_isShared_3366_ == 0)
{
lean_ctor_set(v___x_3365_, 1, v___x_3370_);
lean_ctor_set(v___x_3365_, 0, v___x_3369_);
v___x_3372_ = v___x_3365_;
goto v_reusejp_3371_;
}
else
{
lean_object* v_reuseFailAlloc_3380_; 
v_reuseFailAlloc_3380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3380_, 0, v___x_3369_);
lean_ctor_set(v_reuseFailAlloc_3380_, 1, v___x_3370_);
v___x_3372_ = v_reuseFailAlloc_3380_;
goto v_reusejp_3371_;
}
v_reusejp_3371_:
{
lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; 
v___x_3373_ = lean_box(0);
v___x_3374_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3374_, 0, v___x_3372_);
lean_ctor_set(v___x_3374_, 1, v___x_3373_);
v___x_3375_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3375_, 0, v___x_3374_);
lean_ctor_set(v___x_3375_, 1, v___x_3373_);
v___x_3376_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3376_, 0, v___x_3368_);
lean_ctor_set(v___x_3376_, 1, v___x_3375_);
v___x_3377_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__2));
v___x_3378_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLocation_toJson_spec__0(v___x_3376_, v___x_3377_);
v___x_3379_ = l_Lean_Json_mkObj(v___x_3378_);
lean_dec(v___x_3378_);
return v___x_3379_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson_spec__0(lean_object* v_j_3384_, lean_object* v_k_3385_){
_start:
{
lean_object* v___x_3386_; lean_object* v___x_3387_; 
v___x_3386_ = l_Lean_Json_getObjValD(v_j_3384_, v_k_3385_);
v___x_3387_ = l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson(v___x_3386_);
return v___x_3387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson_spec__0___boxed(lean_object* v_j_3388_, lean_object* v_k_3389_){
_start:
{
lean_object* v_res_3390_; 
v_res_3390_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson_spec__0(v_j_3388_, v_k_3389_);
lean_dec_ref(v_k_3389_);
return v_res_3390_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__2(void){
_start:
{
uint8_t v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; 
v___x_3396_ = 1;
v___x_3397_ = ((lean_object*)(l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__1));
v___x_3398_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3397_, v___x_3396_);
return v___x_3398_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__3(void){
_start:
{
lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; 
v___x_3399_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__5));
v___x_3400_ = lean_obj_once(&l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__2, &l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__2);
v___x_3401_ = lean_string_append(v___x_3400_, v___x_3399_);
return v___x_3401_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__6(void){
_start:
{
uint8_t v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; 
v___x_3405_ = 1;
v___x_3406_ = ((lean_object*)(l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__5));
v___x_3407_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3406_, v___x_3405_);
return v___x_3407_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__7(void){
_start:
{
lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; 
v___x_3408_ = lean_obj_once(&l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__6, &l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__6);
v___x_3409_ = lean_obj_once(&l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__3);
v___x_3410_ = lean_string_append(v___x_3409_, v___x_3408_);
return v___x_3410_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__8(void){
_start:
{
lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; 
v___x_3411_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_3412_ = lean_obj_once(&l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__7);
v___x_3413_ = lean_string_append(v___x_3412_, v___x_3411_);
return v___x_3413_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__10(void){
_start:
{
uint8_t v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; 
v___x_3416_ = 1;
v___x_3417_ = ((lean_object*)(l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__9));
v___x_3418_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3417_, v___x_3416_);
return v___x_3418_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__11(void){
_start:
{
lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; 
v___x_3419_ = lean_obj_once(&l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__10, &l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__10);
v___x_3420_ = lean_obj_once(&l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__3);
v___x_3421_ = lean_string_append(v___x_3420_, v___x_3419_);
return v___x_3421_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__12(void){
_start:
{
lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; 
v___x_3422_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_3423_ = lean_obj_once(&l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__11, &l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__11);
v___x_3424_ = lean_string_append(v___x_3423_, v___x_3422_);
return v___x_3424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson(lean_object* v_json_3425_){
_start:
{
lean_object* v___x_3426_; lean_object* v___x_3427_; 
v___x_3426_ = ((lean_object*)(l_Lean_Lsp_instToJsonChangeAnnotation_toJson___closed__0));
lean_inc(v_json_3425_);
v___x_3427_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextEdit_fromJson_spec__1(v_json_3425_, v___x_3426_);
if (lean_obj_tag(v___x_3427_) == 0)
{
lean_object* v_a_3428_; lean_object* v___x_3430_; uint8_t v_isShared_3431_; uint8_t v_isSharedCheck_3437_; 
lean_dec(v_json_3425_);
v_a_3428_ = lean_ctor_get(v___x_3427_, 0);
v_isSharedCheck_3437_ = !lean_is_exclusive(v___x_3427_);
if (v_isSharedCheck_3437_ == 0)
{
v___x_3430_ = v___x_3427_;
v_isShared_3431_ = v_isSharedCheck_3437_;
goto v_resetjp_3429_;
}
else
{
lean_inc(v_a_3428_);
lean_dec(v___x_3427_);
v___x_3430_ = lean_box(0);
v_isShared_3431_ = v_isSharedCheck_3437_;
goto v_resetjp_3429_;
}
v_resetjp_3429_:
{
lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3435_; 
v___x_3432_ = lean_obj_once(&l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__8);
v___x_3433_ = lean_string_append(v___x_3432_, v_a_3428_);
lean_dec(v_a_3428_);
if (v_isShared_3431_ == 0)
{
lean_ctor_set(v___x_3430_, 0, v___x_3433_);
v___x_3435_ = v___x_3430_;
goto v_reusejp_3434_;
}
else
{
lean_object* v_reuseFailAlloc_3436_; 
v_reuseFailAlloc_3436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3436_, 0, v___x_3433_);
v___x_3435_ = v_reuseFailAlloc_3436_;
goto v_reusejp_3434_;
}
v_reusejp_3434_:
{
return v___x_3435_;
}
}
}
else
{
if (lean_obj_tag(v___x_3427_) == 0)
{
lean_object* v_a_3438_; lean_object* v___x_3440_; uint8_t v_isShared_3441_; uint8_t v_isSharedCheck_3445_; 
lean_dec(v_json_3425_);
v_a_3438_ = lean_ctor_get(v___x_3427_, 0);
v_isSharedCheck_3445_ = !lean_is_exclusive(v___x_3427_);
if (v_isSharedCheck_3445_ == 0)
{
v___x_3440_ = v___x_3427_;
v_isShared_3441_ = v_isSharedCheck_3445_;
goto v_resetjp_3439_;
}
else
{
lean_inc(v_a_3438_);
lean_dec(v___x_3427_);
v___x_3440_ = lean_box(0);
v_isShared_3441_ = v_isSharedCheck_3445_;
goto v_resetjp_3439_;
}
v_resetjp_3439_:
{
lean_object* v___x_3443_; 
if (v_isShared_3441_ == 0)
{
lean_ctor_set_tag(v___x_3440_, 0);
v___x_3443_ = v___x_3440_;
goto v_reusejp_3442_;
}
else
{
lean_object* v_reuseFailAlloc_3444_; 
v_reuseFailAlloc_3444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3444_, 0, v_a_3438_);
v___x_3443_ = v_reuseFailAlloc_3444_;
goto v_reusejp_3442_;
}
v_reusejp_3442_:
{
return v___x_3443_;
}
}
}
else
{
lean_object* v_a_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; 
v_a_3446_ = lean_ctor_get(v___x_3427_, 0);
lean_inc(v_a_3446_);
lean_dec_ref_known(v___x_3427_, 1);
v___x_3447_ = ((lean_object*)(l_Lean_Lsp_instToJsonApplyWorkspaceEditParams_toJson___closed__0));
v___x_3448_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson_spec__0(v_json_3425_, v___x_3447_);
if (lean_obj_tag(v___x_3448_) == 0)
{
lean_object* v_a_3449_; lean_object* v___x_3451_; uint8_t v_isShared_3452_; uint8_t v_isSharedCheck_3458_; 
lean_dec(v_a_3446_);
v_a_3449_ = lean_ctor_get(v___x_3448_, 0);
v_isSharedCheck_3458_ = !lean_is_exclusive(v___x_3448_);
if (v_isSharedCheck_3458_ == 0)
{
v___x_3451_ = v___x_3448_;
v_isShared_3452_ = v_isSharedCheck_3458_;
goto v_resetjp_3450_;
}
else
{
lean_inc(v_a_3449_);
lean_dec(v___x_3448_);
v___x_3451_ = lean_box(0);
v_isShared_3452_ = v_isSharedCheck_3458_;
goto v_resetjp_3450_;
}
v_resetjp_3450_:
{
lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3456_; 
v___x_3453_ = lean_obj_once(&l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__12, &l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__12);
v___x_3454_ = lean_string_append(v___x_3453_, v_a_3449_);
lean_dec(v_a_3449_);
if (v_isShared_3452_ == 0)
{
lean_ctor_set(v___x_3451_, 0, v___x_3454_);
v___x_3456_ = v___x_3451_;
goto v_reusejp_3455_;
}
else
{
lean_object* v_reuseFailAlloc_3457_; 
v_reuseFailAlloc_3457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3457_, 0, v___x_3454_);
v___x_3456_ = v_reuseFailAlloc_3457_;
goto v_reusejp_3455_;
}
v_reusejp_3455_:
{
return v___x_3456_;
}
}
}
else
{
if (lean_obj_tag(v___x_3448_) == 0)
{
lean_object* v_a_3459_; lean_object* v___x_3461_; uint8_t v_isShared_3462_; uint8_t v_isSharedCheck_3466_; 
lean_dec(v_a_3446_);
v_a_3459_ = lean_ctor_get(v___x_3448_, 0);
v_isSharedCheck_3466_ = !lean_is_exclusive(v___x_3448_);
if (v_isSharedCheck_3466_ == 0)
{
v___x_3461_ = v___x_3448_;
v_isShared_3462_ = v_isSharedCheck_3466_;
goto v_resetjp_3460_;
}
else
{
lean_inc(v_a_3459_);
lean_dec(v___x_3448_);
v___x_3461_ = lean_box(0);
v_isShared_3462_ = v_isSharedCheck_3466_;
goto v_resetjp_3460_;
}
v_resetjp_3460_:
{
lean_object* v___x_3464_; 
if (v_isShared_3462_ == 0)
{
lean_ctor_set_tag(v___x_3461_, 0);
v___x_3464_ = v___x_3461_;
goto v_reusejp_3463_;
}
else
{
lean_object* v_reuseFailAlloc_3465_; 
v_reuseFailAlloc_3465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3465_, 0, v_a_3459_);
v___x_3464_ = v_reuseFailAlloc_3465_;
goto v_reusejp_3463_;
}
v_reusejp_3463_:
{
return v___x_3464_;
}
}
}
else
{
lean_object* v_a_3467_; lean_object* v___x_3469_; uint8_t v_isShared_3470_; uint8_t v_isSharedCheck_3475_; 
v_a_3467_ = lean_ctor_get(v___x_3448_, 0);
v_isSharedCheck_3475_ = !lean_is_exclusive(v___x_3448_);
if (v_isSharedCheck_3475_ == 0)
{
v___x_3469_ = v___x_3448_;
v_isShared_3470_ = v_isSharedCheck_3475_;
goto v_resetjp_3468_;
}
else
{
lean_inc(v_a_3467_);
lean_dec(v___x_3448_);
v___x_3469_ = lean_box(0);
v_isShared_3470_ = v_isSharedCheck_3475_;
goto v_resetjp_3468_;
}
v_resetjp_3468_:
{
lean_object* v___x_3471_; lean_object* v___x_3473_; 
v___x_3471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3471_, 0, v_a_3446_);
lean_ctor_set(v___x_3471_, 1, v_a_3467_);
if (v_isShared_3470_ == 0)
{
lean_ctor_set(v___x_3469_, 0, v___x_3471_);
v___x_3473_ = v___x_3469_;
goto v_reusejp_3472_;
}
else
{
lean_object* v_reuseFailAlloc_3474_; 
v_reuseFailAlloc_3474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3474_, 0, v___x_3471_);
v___x_3473_ = v_reuseFailAlloc_3474_;
goto v_reusejp_3472_;
}
v_reusejp_3472_:
{
return v___x_3473_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonTextDocumentItem_toJson(lean_object* v_x_3480_){
_start:
{
lean_object* v_uri_3481_; lean_object* v_languageId_3482_; lean_object* v_version_3483_; lean_object* v_text_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; 
v_uri_3481_ = lean_ctor_get(v_x_3480_, 0);
lean_inc_ref(v_uri_3481_);
v_languageId_3482_ = lean_ctor_get(v_x_3480_, 1);
lean_inc_ref(v_languageId_3482_);
v_version_3483_ = lean_ctor_get(v_x_3480_, 2);
lean_inc(v_version_3483_);
v_text_3484_ = lean_ctor_get(v_x_3480_, 3);
lean_inc_ref(v_text_3484_);
lean_dec_ref(v_x_3480_);
v___x_3485_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__0));
v___x_3486_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3486_, 0, v_uri_3481_);
v___x_3487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3487_, 0, v___x_3485_);
lean_ctor_set(v___x_3487_, 1, v___x_3486_);
v___x_3488_ = lean_box(0);
v___x_3489_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3489_, 0, v___x_3487_);
lean_ctor_set(v___x_3489_, 1, v___x_3488_);
v___x_3490_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextDocumentItem_toJson___closed__0));
v___x_3491_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3491_, 0, v_languageId_3482_);
v___x_3492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3492_, 0, v___x_3490_);
lean_ctor_set(v___x_3492_, 1, v___x_3491_);
v___x_3493_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3493_, 0, v___x_3492_);
lean_ctor_set(v___x_3493_, 1, v___x_3488_);
v___x_3494_ = ((lean_object*)(l_Lean_Lsp_instToJsonVersionedTextDocumentIdentifier_toJson___closed__0));
v___x_3495_ = l_Lean_JsonNumber_fromNat(v_version_3483_);
v___x_3496_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3496_, 0, v___x_3495_);
v___x_3497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3497_, 0, v___x_3494_);
lean_ctor_set(v___x_3497_, 1, v___x_3496_);
v___x_3498_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3498_, 0, v___x_3497_);
lean_ctor_set(v___x_3498_, 1, v___x_3488_);
v___x_3499_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextDocumentItem_toJson___closed__1));
v___x_3500_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3500_, 0, v_text_3484_);
v___x_3501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3501_, 0, v___x_3499_);
lean_ctor_set(v___x_3501_, 1, v___x_3500_);
v___x_3502_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3502_, 0, v___x_3501_);
lean_ctor_set(v___x_3502_, 1, v___x_3488_);
v___x_3503_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3503_, 0, v___x_3502_);
lean_ctor_set(v___x_3503_, 1, v___x_3488_);
v___x_3504_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3504_, 0, v___x_3498_);
lean_ctor_set(v___x_3504_, 1, v___x_3503_);
v___x_3505_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3505_, 0, v___x_3493_);
lean_ctor_set(v___x_3505_, 1, v___x_3504_);
v___x_3506_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3506_, 0, v___x_3489_);
lean_ctor_set(v___x_3506_, 1, v___x_3505_);
v___x_3507_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__2));
v___x_3508_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLocation_toJson_spec__0(v___x_3506_, v___x_3507_);
v___x_3509_ = l_Lean_Json_mkObj(v___x_3508_);
lean_dec(v___x_3508_);
return v___x_3509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentItem_fromJson_spec__0(lean_object* v_j_3512_, lean_object* v_k_3513_){
_start:
{
lean_object* v___x_3514_; lean_object* v___x_3515_; 
v___x_3514_ = l_Lean_Json_getObjValD(v_j_3512_, v_k_3513_);
v___x_3515_ = l_Lean_Json_getNat_x3f(v___x_3514_);
return v___x_3515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentItem_fromJson_spec__0___boxed(lean_object* v_j_3516_, lean_object* v_k_3517_){
_start:
{
lean_object* v_res_3518_; 
v_res_3518_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentItem_fromJson_spec__0(v_j_3516_, v_k_3517_);
lean_dec_ref(v_k_3517_);
return v_res_3518_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__2(void){
_start:
{
uint8_t v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; 
v___x_3524_ = 1;
v___x_3525_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__1));
v___x_3526_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3525_, v___x_3524_);
return v___x_3526_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__3(void){
_start:
{
lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; 
v___x_3527_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__5));
v___x_3528_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__2, &l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__2);
v___x_3529_ = lean_string_append(v___x_3528_, v___x_3527_);
return v___x_3529_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__4(void){
_start:
{
lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; 
v___x_3530_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLocation_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLocation_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLocation_fromJson___closed__8);
v___x_3531_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__3, &l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__3);
v___x_3532_ = lean_string_append(v___x_3531_, v___x_3530_);
return v___x_3532_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__5(void){
_start:
{
lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; 
v___x_3533_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_3534_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__4, &l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__4);
v___x_3535_ = lean_string_append(v___x_3534_, v___x_3533_);
return v___x_3535_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__7(void){
_start:
{
uint8_t v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; 
v___x_3538_ = 1;
v___x_3539_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__6));
v___x_3540_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3539_, v___x_3538_);
return v___x_3540_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__8(void){
_start:
{
lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; 
v___x_3541_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__7, &l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__7);
v___x_3542_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__3, &l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__3);
v___x_3543_ = lean_string_append(v___x_3542_, v___x_3541_);
return v___x_3543_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__9(void){
_start:
{
lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; 
v___x_3544_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_3545_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__8, &l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__8);
v___x_3546_ = lean_string_append(v___x_3545_, v___x_3544_);
return v___x_3546_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__11(void){
_start:
{
uint8_t v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; 
v___x_3549_ = 1;
v___x_3550_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__10));
v___x_3551_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3550_, v___x_3549_);
return v___x_3551_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__12(void){
_start:
{
lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; 
v___x_3552_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__11, &l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__11);
v___x_3553_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__3, &l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__3);
v___x_3554_ = lean_string_append(v___x_3553_, v___x_3552_);
return v___x_3554_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__13(void){
_start:
{
lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; 
v___x_3555_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_3556_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__12, &l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__12);
v___x_3557_ = lean_string_append(v___x_3556_, v___x_3555_);
return v___x_3557_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__15(void){
_start:
{
uint8_t v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; 
v___x_3560_ = 1;
v___x_3561_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__14));
v___x_3562_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3561_, v___x_3560_);
return v___x_3562_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__16(void){
_start:
{
lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; 
v___x_3563_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__15, &l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__15_once, _init_l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__15);
v___x_3564_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__3, &l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__3);
v___x_3565_ = lean_string_append(v___x_3564_, v___x_3563_);
return v___x_3565_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__17(void){
_start:
{
lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; 
v___x_3566_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_3567_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__16, &l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__16_once, _init_l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__16);
v___x_3568_ = lean_string_append(v___x_3567_, v___x_3566_);
return v___x_3568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson(lean_object* v_json_3569_){
_start:
{
lean_object* v___x_3570_; lean_object* v___x_3571_; 
v___x_3570_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__0));
lean_inc(v_json_3569_);
v___x_3571_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocation_fromJson_spec__0(v_json_3569_, v___x_3570_);
if (lean_obj_tag(v___x_3571_) == 0)
{
lean_object* v_a_3572_; lean_object* v___x_3574_; uint8_t v_isShared_3575_; uint8_t v_isSharedCheck_3581_; 
lean_dec(v_json_3569_);
v_a_3572_ = lean_ctor_get(v___x_3571_, 0);
v_isSharedCheck_3581_ = !lean_is_exclusive(v___x_3571_);
if (v_isSharedCheck_3581_ == 0)
{
v___x_3574_ = v___x_3571_;
v_isShared_3575_ = v_isSharedCheck_3581_;
goto v_resetjp_3573_;
}
else
{
lean_inc(v_a_3572_);
lean_dec(v___x_3571_);
v___x_3574_ = lean_box(0);
v_isShared_3575_ = v_isSharedCheck_3581_;
goto v_resetjp_3573_;
}
v_resetjp_3573_:
{
lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3579_; 
v___x_3576_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__5, &l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__5);
v___x_3577_ = lean_string_append(v___x_3576_, v_a_3572_);
lean_dec(v_a_3572_);
if (v_isShared_3575_ == 0)
{
lean_ctor_set(v___x_3574_, 0, v___x_3577_);
v___x_3579_ = v___x_3574_;
goto v_reusejp_3578_;
}
else
{
lean_object* v_reuseFailAlloc_3580_; 
v_reuseFailAlloc_3580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3580_, 0, v___x_3577_);
v___x_3579_ = v_reuseFailAlloc_3580_;
goto v_reusejp_3578_;
}
v_reusejp_3578_:
{
return v___x_3579_;
}
}
}
else
{
if (lean_obj_tag(v___x_3571_) == 0)
{
lean_object* v_a_3582_; lean_object* v___x_3584_; uint8_t v_isShared_3585_; uint8_t v_isSharedCheck_3589_; 
lean_dec(v_json_3569_);
v_a_3582_ = lean_ctor_get(v___x_3571_, 0);
v_isSharedCheck_3589_ = !lean_is_exclusive(v___x_3571_);
if (v_isSharedCheck_3589_ == 0)
{
v___x_3584_ = v___x_3571_;
v_isShared_3585_ = v_isSharedCheck_3589_;
goto v_resetjp_3583_;
}
else
{
lean_inc(v_a_3582_);
lean_dec(v___x_3571_);
v___x_3584_ = lean_box(0);
v_isShared_3585_ = v_isSharedCheck_3589_;
goto v_resetjp_3583_;
}
v_resetjp_3583_:
{
lean_object* v___x_3587_; 
if (v_isShared_3585_ == 0)
{
lean_ctor_set_tag(v___x_3584_, 0);
v___x_3587_ = v___x_3584_;
goto v_reusejp_3586_;
}
else
{
lean_object* v_reuseFailAlloc_3588_; 
v_reuseFailAlloc_3588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3588_, 0, v_a_3582_);
v___x_3587_ = v_reuseFailAlloc_3588_;
goto v_reusejp_3586_;
}
v_reusejp_3586_:
{
return v___x_3587_;
}
}
}
else
{
lean_object* v_a_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; 
v_a_3590_ = lean_ctor_get(v___x_3571_, 0);
lean_inc(v_a_3590_);
lean_dec_ref_known(v___x_3571_, 1);
v___x_3591_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextDocumentItem_toJson___closed__0));
lean_inc(v_json_3569_);
v___x_3592_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocation_fromJson_spec__0(v_json_3569_, v___x_3591_);
if (lean_obj_tag(v___x_3592_) == 0)
{
lean_object* v_a_3593_; lean_object* v___x_3595_; uint8_t v_isShared_3596_; uint8_t v_isSharedCheck_3602_; 
lean_dec(v_a_3590_);
lean_dec(v_json_3569_);
v_a_3593_ = lean_ctor_get(v___x_3592_, 0);
v_isSharedCheck_3602_ = !lean_is_exclusive(v___x_3592_);
if (v_isSharedCheck_3602_ == 0)
{
v___x_3595_ = v___x_3592_;
v_isShared_3596_ = v_isSharedCheck_3602_;
goto v_resetjp_3594_;
}
else
{
lean_inc(v_a_3593_);
lean_dec(v___x_3592_);
v___x_3595_ = lean_box(0);
v_isShared_3596_ = v_isSharedCheck_3602_;
goto v_resetjp_3594_;
}
v_resetjp_3594_:
{
lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3600_; 
v___x_3597_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__9, &l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__9);
v___x_3598_ = lean_string_append(v___x_3597_, v_a_3593_);
lean_dec(v_a_3593_);
if (v_isShared_3596_ == 0)
{
lean_ctor_set(v___x_3595_, 0, v___x_3598_);
v___x_3600_ = v___x_3595_;
goto v_reusejp_3599_;
}
else
{
lean_object* v_reuseFailAlloc_3601_; 
v_reuseFailAlloc_3601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3601_, 0, v___x_3598_);
v___x_3600_ = v_reuseFailAlloc_3601_;
goto v_reusejp_3599_;
}
v_reusejp_3599_:
{
return v___x_3600_;
}
}
}
else
{
if (lean_obj_tag(v___x_3592_) == 0)
{
lean_object* v_a_3603_; lean_object* v___x_3605_; uint8_t v_isShared_3606_; uint8_t v_isSharedCheck_3610_; 
lean_dec(v_a_3590_);
lean_dec(v_json_3569_);
v_a_3603_ = lean_ctor_get(v___x_3592_, 0);
v_isSharedCheck_3610_ = !lean_is_exclusive(v___x_3592_);
if (v_isSharedCheck_3610_ == 0)
{
v___x_3605_ = v___x_3592_;
v_isShared_3606_ = v_isSharedCheck_3610_;
goto v_resetjp_3604_;
}
else
{
lean_inc(v_a_3603_);
lean_dec(v___x_3592_);
v___x_3605_ = lean_box(0);
v_isShared_3606_ = v_isSharedCheck_3610_;
goto v_resetjp_3604_;
}
v_resetjp_3604_:
{
lean_object* v___x_3608_; 
if (v_isShared_3606_ == 0)
{
lean_ctor_set_tag(v___x_3605_, 0);
v___x_3608_ = v___x_3605_;
goto v_reusejp_3607_;
}
else
{
lean_object* v_reuseFailAlloc_3609_; 
v_reuseFailAlloc_3609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3609_, 0, v_a_3603_);
v___x_3608_ = v_reuseFailAlloc_3609_;
goto v_reusejp_3607_;
}
v_reusejp_3607_:
{
return v___x_3608_;
}
}
}
else
{
lean_object* v_a_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; 
v_a_3611_ = lean_ctor_get(v___x_3592_, 0);
lean_inc(v_a_3611_);
lean_dec_ref_known(v___x_3592_, 1);
v___x_3612_ = ((lean_object*)(l_Lean_Lsp_instToJsonVersionedTextDocumentIdentifier_toJson___closed__0));
lean_inc(v_json_3569_);
v___x_3613_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentItem_fromJson_spec__0(v_json_3569_, v___x_3612_);
if (lean_obj_tag(v___x_3613_) == 0)
{
lean_object* v_a_3614_; lean_object* v___x_3616_; uint8_t v_isShared_3617_; uint8_t v_isSharedCheck_3623_; 
lean_dec(v_a_3611_);
lean_dec(v_a_3590_);
lean_dec(v_json_3569_);
v_a_3614_ = lean_ctor_get(v___x_3613_, 0);
v_isSharedCheck_3623_ = !lean_is_exclusive(v___x_3613_);
if (v_isSharedCheck_3623_ == 0)
{
v___x_3616_ = v___x_3613_;
v_isShared_3617_ = v_isSharedCheck_3623_;
goto v_resetjp_3615_;
}
else
{
lean_inc(v_a_3614_);
lean_dec(v___x_3613_);
v___x_3616_ = lean_box(0);
v_isShared_3617_ = v_isSharedCheck_3623_;
goto v_resetjp_3615_;
}
v_resetjp_3615_:
{
lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3621_; 
v___x_3618_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__13, &l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__13);
v___x_3619_ = lean_string_append(v___x_3618_, v_a_3614_);
lean_dec(v_a_3614_);
if (v_isShared_3617_ == 0)
{
lean_ctor_set(v___x_3616_, 0, v___x_3619_);
v___x_3621_ = v___x_3616_;
goto v_reusejp_3620_;
}
else
{
lean_object* v_reuseFailAlloc_3622_; 
v_reuseFailAlloc_3622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3622_, 0, v___x_3619_);
v___x_3621_ = v_reuseFailAlloc_3622_;
goto v_reusejp_3620_;
}
v_reusejp_3620_:
{
return v___x_3621_;
}
}
}
else
{
if (lean_obj_tag(v___x_3613_) == 0)
{
lean_object* v_a_3624_; lean_object* v___x_3626_; uint8_t v_isShared_3627_; uint8_t v_isSharedCheck_3631_; 
lean_dec(v_a_3611_);
lean_dec(v_a_3590_);
lean_dec(v_json_3569_);
v_a_3624_ = lean_ctor_get(v___x_3613_, 0);
v_isSharedCheck_3631_ = !lean_is_exclusive(v___x_3613_);
if (v_isSharedCheck_3631_ == 0)
{
v___x_3626_ = v___x_3613_;
v_isShared_3627_ = v_isSharedCheck_3631_;
goto v_resetjp_3625_;
}
else
{
lean_inc(v_a_3624_);
lean_dec(v___x_3613_);
v___x_3626_ = lean_box(0);
v_isShared_3627_ = v_isSharedCheck_3631_;
goto v_resetjp_3625_;
}
v_resetjp_3625_:
{
lean_object* v___x_3629_; 
if (v_isShared_3627_ == 0)
{
lean_ctor_set_tag(v___x_3626_, 0);
v___x_3629_ = v___x_3626_;
goto v_reusejp_3628_;
}
else
{
lean_object* v_reuseFailAlloc_3630_; 
v_reuseFailAlloc_3630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3630_, 0, v_a_3624_);
v___x_3629_ = v_reuseFailAlloc_3630_;
goto v_reusejp_3628_;
}
v_reusejp_3628_:
{
return v___x_3629_;
}
}
}
else
{
lean_object* v_a_3632_; lean_object* v___x_3633_; lean_object* v___x_3634_; 
v_a_3632_ = lean_ctor_get(v___x_3613_, 0);
lean_inc(v_a_3632_);
lean_dec_ref_known(v___x_3613_, 1);
v___x_3633_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextDocumentItem_toJson___closed__1));
v___x_3634_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocation_fromJson_spec__0(v_json_3569_, v___x_3633_);
if (lean_obj_tag(v___x_3634_) == 0)
{
lean_object* v_a_3635_; lean_object* v___x_3637_; uint8_t v_isShared_3638_; uint8_t v_isSharedCheck_3644_; 
lean_dec(v_a_3632_);
lean_dec(v_a_3611_);
lean_dec(v_a_3590_);
v_a_3635_ = lean_ctor_get(v___x_3634_, 0);
v_isSharedCheck_3644_ = !lean_is_exclusive(v___x_3634_);
if (v_isSharedCheck_3644_ == 0)
{
v___x_3637_ = v___x_3634_;
v_isShared_3638_ = v_isSharedCheck_3644_;
goto v_resetjp_3636_;
}
else
{
lean_inc(v_a_3635_);
lean_dec(v___x_3634_);
v___x_3637_ = lean_box(0);
v_isShared_3638_ = v_isSharedCheck_3644_;
goto v_resetjp_3636_;
}
v_resetjp_3636_:
{
lean_object* v___x_3639_; lean_object* v___x_3640_; lean_object* v___x_3642_; 
v___x_3639_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__17, &l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__17_once, _init_l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__17);
v___x_3640_ = lean_string_append(v___x_3639_, v_a_3635_);
lean_dec(v_a_3635_);
if (v_isShared_3638_ == 0)
{
lean_ctor_set(v___x_3637_, 0, v___x_3640_);
v___x_3642_ = v___x_3637_;
goto v_reusejp_3641_;
}
else
{
lean_object* v_reuseFailAlloc_3643_; 
v_reuseFailAlloc_3643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3643_, 0, v___x_3640_);
v___x_3642_ = v_reuseFailAlloc_3643_;
goto v_reusejp_3641_;
}
v_reusejp_3641_:
{
return v___x_3642_;
}
}
}
else
{
if (lean_obj_tag(v___x_3634_) == 0)
{
lean_object* v_a_3645_; lean_object* v___x_3647_; uint8_t v_isShared_3648_; uint8_t v_isSharedCheck_3652_; 
lean_dec(v_a_3632_);
lean_dec(v_a_3611_);
lean_dec(v_a_3590_);
v_a_3645_ = lean_ctor_get(v___x_3634_, 0);
v_isSharedCheck_3652_ = !lean_is_exclusive(v___x_3634_);
if (v_isSharedCheck_3652_ == 0)
{
v___x_3647_ = v___x_3634_;
v_isShared_3648_ = v_isSharedCheck_3652_;
goto v_resetjp_3646_;
}
else
{
lean_inc(v_a_3645_);
lean_dec(v___x_3634_);
v___x_3647_ = lean_box(0);
v_isShared_3648_ = v_isSharedCheck_3652_;
goto v_resetjp_3646_;
}
v_resetjp_3646_:
{
lean_object* v___x_3650_; 
if (v_isShared_3648_ == 0)
{
lean_ctor_set_tag(v___x_3647_, 0);
v___x_3650_ = v___x_3647_;
goto v_reusejp_3649_;
}
else
{
lean_object* v_reuseFailAlloc_3651_; 
v_reuseFailAlloc_3651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3651_, 0, v_a_3645_);
v___x_3650_ = v_reuseFailAlloc_3651_;
goto v_reusejp_3649_;
}
v_reusejp_3649_:
{
return v___x_3650_;
}
}
}
else
{
lean_object* v_a_3653_; lean_object* v___x_3655_; uint8_t v_isShared_3656_; uint8_t v_isSharedCheck_3661_; 
v_a_3653_ = lean_ctor_get(v___x_3634_, 0);
v_isSharedCheck_3661_ = !lean_is_exclusive(v___x_3634_);
if (v_isSharedCheck_3661_ == 0)
{
v___x_3655_ = v___x_3634_;
v_isShared_3656_ = v_isSharedCheck_3661_;
goto v_resetjp_3654_;
}
else
{
lean_inc(v_a_3653_);
lean_dec(v___x_3634_);
v___x_3655_ = lean_box(0);
v_isShared_3656_ = v_isSharedCheck_3661_;
goto v_resetjp_3654_;
}
v_resetjp_3654_:
{
lean_object* v___x_3657_; lean_object* v___x_3659_; 
v___x_3657_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3657_, 0, v_a_3590_);
lean_ctor_set(v___x_3657_, 1, v_a_3611_);
lean_ctor_set(v___x_3657_, 2, v_a_3632_);
lean_ctor_set(v___x_3657_, 3, v_a_3653_);
if (v_isShared_3656_ == 0)
{
lean_ctor_set(v___x_3655_, 0, v___x_3657_);
v___x_3659_ = v___x_3655_;
goto v_reusejp_3658_;
}
else
{
lean_object* v_reuseFailAlloc_3660_; 
v_reuseFailAlloc_3660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3660_, 0, v___x_3657_);
v___x_3659_ = v_reuseFailAlloc_3660_;
goto v_reusejp_3658_;
}
v_reusejp_3658_:
{
return v___x_3659_;
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
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonTextDocumentPositionParams_toJson(lean_object* v_x_3665_){
_start:
{
lean_object* v_textDocument_3666_; lean_object* v_position_3667_; lean_object* v___x_3669_; uint8_t v_isShared_3670_; uint8_t v_isSharedCheck_3687_; 
v_textDocument_3666_ = lean_ctor_get(v_x_3665_, 0);
v_position_3667_ = lean_ctor_get(v_x_3665_, 1);
v_isSharedCheck_3687_ = !lean_is_exclusive(v_x_3665_);
if (v_isSharedCheck_3687_ == 0)
{
v___x_3669_ = v_x_3665_;
v_isShared_3670_ = v_isSharedCheck_3687_;
goto v_resetjp_3668_;
}
else
{
lean_inc(v_position_3667_);
lean_inc(v_textDocument_3666_);
lean_dec(v_x_3665_);
v___x_3669_ = lean_box(0);
v_isShared_3670_ = v_isSharedCheck_3687_;
goto v_resetjp_3668_;
}
v_resetjp_3668_:
{
lean_object* v___x_3671_; lean_object* v___x_3672_; lean_object* v___x_3674_; 
v___x_3671_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextDocumentEdit_toJson___closed__0));
v___x_3672_ = l_Lean_Lsp_instToJsonTextDocumentIdentifier_toJson(v_textDocument_3666_);
if (v_isShared_3670_ == 0)
{
lean_ctor_set(v___x_3669_, 1, v___x_3672_);
lean_ctor_set(v___x_3669_, 0, v___x_3671_);
v___x_3674_ = v___x_3669_;
goto v_reusejp_3673_;
}
else
{
lean_object* v_reuseFailAlloc_3686_; 
v_reuseFailAlloc_3686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3686_, 0, v___x_3671_);
lean_ctor_set(v_reuseFailAlloc_3686_, 1, v___x_3672_);
v___x_3674_ = v_reuseFailAlloc_3686_;
goto v_reusejp_3673_;
}
v_reusejp_3673_:
{
lean_object* v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; 
v___x_3675_ = lean_box(0);
v___x_3676_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3676_, 0, v___x_3674_);
lean_ctor_set(v___x_3676_, 1, v___x_3675_);
v___x_3677_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextDocumentPositionParams_toJson___closed__0));
v___x_3678_ = l_Lean_Lsp_instToJsonPosition_toJson(v_position_3667_);
v___x_3679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3679_, 0, v___x_3677_);
lean_ctor_set(v___x_3679_, 1, v___x_3678_);
v___x_3680_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3680_, 0, v___x_3679_);
lean_ctor_set(v___x_3680_, 1, v___x_3675_);
v___x_3681_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3681_, 0, v___x_3680_);
lean_ctor_set(v___x_3681_, 1, v___x_3675_);
v___x_3682_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3682_, 0, v___x_3676_);
lean_ctor_set(v___x_3682_, 1, v___x_3681_);
v___x_3683_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__2));
v___x_3684_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLocation_toJson_spec__0(v___x_3682_, v___x_3683_);
v___x_3685_ = l_Lean_Json_mkObj(v___x_3684_);
lean_dec(v___x_3684_);
return v___x_3685_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson_spec__0(lean_object* v_j_3690_, lean_object* v_k_3691_){
_start:
{
lean_object* v___x_3692_; lean_object* v___x_3693_; 
v___x_3692_ = l_Lean_Json_getObjValD(v_j_3690_, v_k_3691_);
v___x_3693_ = l_Lean_Lsp_instFromJsonTextDocumentIdentifier_fromJson(v___x_3692_);
return v___x_3693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson_spec__0___boxed(lean_object* v_j_3694_, lean_object* v_k_3695_){
_start:
{
lean_object* v_res_3696_; 
v_res_3696_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson_spec__0(v_j_3694_, v_k_3695_);
lean_dec_ref(v_k_3695_);
return v_res_3696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson_spec__1(lean_object* v_j_3697_, lean_object* v_k_3698_){
_start:
{
lean_object* v___x_3699_; lean_object* v___x_3700_; 
v___x_3699_ = l_Lean_Json_getObjValD(v_j_3697_, v_k_3698_);
v___x_3700_ = l_Lean_Lsp_instFromJsonPosition_fromJson(v___x_3699_);
return v___x_3700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson_spec__1___boxed(lean_object* v_j_3701_, lean_object* v_k_3702_){
_start:
{
lean_object* v_res_3703_; 
v_res_3703_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson_spec__1(v_j_3701_, v_k_3702_);
lean_dec_ref(v_k_3702_);
return v_res_3703_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__2(void){
_start:
{
uint8_t v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; 
v___x_3709_ = 1;
v___x_3710_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__1));
v___x_3711_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3710_, v___x_3709_);
return v___x_3711_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__3(void){
_start:
{
lean_object* v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; 
v___x_3712_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__5));
v___x_3713_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__2, &l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__2);
v___x_3714_ = lean_string_append(v___x_3713_, v___x_3712_);
return v___x_3714_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; 
v___x_3715_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__5, &l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__5);
v___x_3716_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__3);
v___x_3717_ = lean_string_append(v___x_3716_, v___x_3715_);
return v___x_3717_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__5(void){
_start:
{
lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; 
v___x_3718_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_3719_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__4);
v___x_3720_ = lean_string_append(v___x_3719_, v___x_3718_);
return v___x_3720_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__7(void){
_start:
{
uint8_t v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; 
v___x_3723_ = 1;
v___x_3724_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__6));
v___x_3725_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3724_, v___x_3723_);
return v___x_3725_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__8(void){
_start:
{
lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; 
v___x_3726_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__7);
v___x_3727_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__3);
v___x_3728_ = lean_string_append(v___x_3727_, v___x_3726_);
return v___x_3728_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__9(void){
_start:
{
lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; 
v___x_3729_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_3730_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__8);
v___x_3731_ = lean_string_append(v___x_3730_, v___x_3729_);
return v___x_3731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson(lean_object* v_json_3732_){
_start:
{
lean_object* v___x_3733_; lean_object* v___x_3734_; 
v___x_3733_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextDocumentEdit_toJson___closed__0));
lean_inc(v_json_3732_);
v___x_3734_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson_spec__0(v_json_3732_, v___x_3733_);
if (lean_obj_tag(v___x_3734_) == 0)
{
lean_object* v_a_3735_; lean_object* v___x_3737_; uint8_t v_isShared_3738_; uint8_t v_isSharedCheck_3744_; 
lean_dec(v_json_3732_);
v_a_3735_ = lean_ctor_get(v___x_3734_, 0);
v_isSharedCheck_3744_ = !lean_is_exclusive(v___x_3734_);
if (v_isSharedCheck_3744_ == 0)
{
v___x_3737_ = v___x_3734_;
v_isShared_3738_ = v_isSharedCheck_3744_;
goto v_resetjp_3736_;
}
else
{
lean_inc(v_a_3735_);
lean_dec(v___x_3734_);
v___x_3737_ = lean_box(0);
v_isShared_3738_ = v_isSharedCheck_3744_;
goto v_resetjp_3736_;
}
v_resetjp_3736_:
{
lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3742_; 
v___x_3739_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__5, &l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__5);
v___x_3740_ = lean_string_append(v___x_3739_, v_a_3735_);
lean_dec(v_a_3735_);
if (v_isShared_3738_ == 0)
{
lean_ctor_set(v___x_3737_, 0, v___x_3740_);
v___x_3742_ = v___x_3737_;
goto v_reusejp_3741_;
}
else
{
lean_object* v_reuseFailAlloc_3743_; 
v_reuseFailAlloc_3743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3743_, 0, v___x_3740_);
v___x_3742_ = v_reuseFailAlloc_3743_;
goto v_reusejp_3741_;
}
v_reusejp_3741_:
{
return v___x_3742_;
}
}
}
else
{
if (lean_obj_tag(v___x_3734_) == 0)
{
lean_object* v_a_3745_; lean_object* v___x_3747_; uint8_t v_isShared_3748_; uint8_t v_isSharedCheck_3752_; 
lean_dec(v_json_3732_);
v_a_3745_ = lean_ctor_get(v___x_3734_, 0);
v_isSharedCheck_3752_ = !lean_is_exclusive(v___x_3734_);
if (v_isSharedCheck_3752_ == 0)
{
v___x_3747_ = v___x_3734_;
v_isShared_3748_ = v_isSharedCheck_3752_;
goto v_resetjp_3746_;
}
else
{
lean_inc(v_a_3745_);
lean_dec(v___x_3734_);
v___x_3747_ = lean_box(0);
v_isShared_3748_ = v_isSharedCheck_3752_;
goto v_resetjp_3746_;
}
v_resetjp_3746_:
{
lean_object* v___x_3750_; 
if (v_isShared_3748_ == 0)
{
lean_ctor_set_tag(v___x_3747_, 0);
v___x_3750_ = v___x_3747_;
goto v_reusejp_3749_;
}
else
{
lean_object* v_reuseFailAlloc_3751_; 
v_reuseFailAlloc_3751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3751_, 0, v_a_3745_);
v___x_3750_ = v_reuseFailAlloc_3751_;
goto v_reusejp_3749_;
}
v_reusejp_3749_:
{
return v___x_3750_;
}
}
}
else
{
lean_object* v_a_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; 
v_a_3753_ = lean_ctor_get(v___x_3734_, 0);
lean_inc(v_a_3753_);
lean_dec_ref_known(v___x_3734_, 1);
v___x_3754_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextDocumentPositionParams_toJson___closed__0));
v___x_3755_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson_spec__1(v_json_3732_, v___x_3754_);
if (lean_obj_tag(v___x_3755_) == 0)
{
lean_object* v_a_3756_; lean_object* v___x_3758_; uint8_t v_isShared_3759_; uint8_t v_isSharedCheck_3765_; 
lean_dec(v_a_3753_);
v_a_3756_ = lean_ctor_get(v___x_3755_, 0);
v_isSharedCheck_3765_ = !lean_is_exclusive(v___x_3755_);
if (v_isSharedCheck_3765_ == 0)
{
v___x_3758_ = v___x_3755_;
v_isShared_3759_ = v_isSharedCheck_3765_;
goto v_resetjp_3757_;
}
else
{
lean_inc(v_a_3756_);
lean_dec(v___x_3755_);
v___x_3758_ = lean_box(0);
v_isShared_3759_ = v_isSharedCheck_3765_;
goto v_resetjp_3757_;
}
v_resetjp_3757_:
{
lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3763_; 
v___x_3760_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__9, &l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__9);
v___x_3761_ = lean_string_append(v___x_3760_, v_a_3756_);
lean_dec(v_a_3756_);
if (v_isShared_3759_ == 0)
{
lean_ctor_set(v___x_3758_, 0, v___x_3761_);
v___x_3763_ = v___x_3758_;
goto v_reusejp_3762_;
}
else
{
lean_object* v_reuseFailAlloc_3764_; 
v_reuseFailAlloc_3764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3764_, 0, v___x_3761_);
v___x_3763_ = v_reuseFailAlloc_3764_;
goto v_reusejp_3762_;
}
v_reusejp_3762_:
{
return v___x_3763_;
}
}
}
else
{
if (lean_obj_tag(v___x_3755_) == 0)
{
lean_object* v_a_3766_; lean_object* v___x_3768_; uint8_t v_isShared_3769_; uint8_t v_isSharedCheck_3773_; 
lean_dec(v_a_3753_);
v_a_3766_ = lean_ctor_get(v___x_3755_, 0);
v_isSharedCheck_3773_ = !lean_is_exclusive(v___x_3755_);
if (v_isSharedCheck_3773_ == 0)
{
v___x_3768_ = v___x_3755_;
v_isShared_3769_ = v_isSharedCheck_3773_;
goto v_resetjp_3767_;
}
else
{
lean_inc(v_a_3766_);
lean_dec(v___x_3755_);
v___x_3768_ = lean_box(0);
v_isShared_3769_ = v_isSharedCheck_3773_;
goto v_resetjp_3767_;
}
v_resetjp_3767_:
{
lean_object* v___x_3771_; 
if (v_isShared_3769_ == 0)
{
lean_ctor_set_tag(v___x_3768_, 0);
v___x_3771_ = v___x_3768_;
goto v_reusejp_3770_;
}
else
{
lean_object* v_reuseFailAlloc_3772_; 
v_reuseFailAlloc_3772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3772_, 0, v_a_3766_);
v___x_3771_ = v_reuseFailAlloc_3772_;
goto v_reusejp_3770_;
}
v_reusejp_3770_:
{
return v___x_3771_;
}
}
}
else
{
lean_object* v_a_3774_; lean_object* v___x_3776_; uint8_t v_isShared_3777_; uint8_t v_isSharedCheck_3782_; 
v_a_3774_ = lean_ctor_get(v___x_3755_, 0);
v_isSharedCheck_3782_ = !lean_is_exclusive(v___x_3755_);
if (v_isSharedCheck_3782_ == 0)
{
v___x_3776_ = v___x_3755_;
v_isShared_3777_ = v_isSharedCheck_3782_;
goto v_resetjp_3775_;
}
else
{
lean_inc(v_a_3774_);
lean_dec(v___x_3755_);
v___x_3776_ = lean_box(0);
v_isShared_3777_ = v_isSharedCheck_3782_;
goto v_resetjp_3775_;
}
v_resetjp_3775_:
{
lean_object* v___x_3778_; lean_object* v___x_3780_; 
v___x_3778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3778_, 0, v_a_3753_);
lean_ctor_set(v___x_3778_, 1, v_a_3774_);
if (v_isShared_3777_ == 0)
{
lean_ctor_set(v___x_3776_, 0, v___x_3778_);
v___x_3780_ = v___x_3776_;
goto v_reusejp_3779_;
}
else
{
lean_object* v_reuseFailAlloc_3781_; 
v_reuseFailAlloc_3781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3781_, 0, v___x_3778_);
v___x_3780_ = v_reuseFailAlloc_3781_;
goto v_reusejp_3779_;
}
v_reusejp_3779_:
{
return v___x_3780_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToStringTextDocumentPositionParams___lam__0(lean_object* v_p_3786_){
_start:
{
lean_object* v_position_3787_; lean_object* v_textDocument_3788_; lean_object* v_line_3789_; lean_object* v_character_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; 
v_position_3787_ = lean_ctor_get(v_p_3786_, 1);
lean_inc_ref(v_position_3787_);
v_textDocument_3788_ = lean_ctor_get(v_p_3786_, 0);
lean_inc_ref(v_textDocument_3788_);
lean_dec_ref(v_p_3786_);
v_line_3789_ = lean_ctor_get(v_position_3787_, 0);
lean_inc(v_line_3789_);
v_character_3790_ = lean_ctor_get(v_position_3787_, 1);
lean_inc(v_character_3790_);
lean_dec_ref(v_position_3787_);
v___x_3791_ = ((lean_object*)(l_Lean_Lsp_instToStringTextDocumentPositionParams___lam__0___closed__0));
v___x_3792_ = lean_string_append(v_textDocument_3788_, v___x_3791_);
v___x_3793_ = l_Nat_reprFast(v_line_3789_);
v___x_3794_ = lean_string_append(v___x_3792_, v___x_3793_);
lean_dec_ref(v___x_3793_);
v___x_3795_ = lean_string_append(v___x_3794_, v___x_3791_);
v___x_3796_ = l_Nat_reprFast(v_character_3790_);
v___x_3797_ = lean_string_append(v___x_3795_, v___x_3796_);
lean_dec_ref(v___x_3796_);
return v___x_3797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDocumentFilter_toJson(lean_object* v_x_3803_){
_start:
{
lean_object* v_language_x3f_3804_; lean_object* v_scheme_x3f_3805_; lean_object* v_pattern_x3f_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; lean_object* v___x_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; 
v_language_x3f_3804_ = lean_ctor_get(v_x_3803_, 0);
lean_inc(v_language_x3f_3804_);
v_scheme_x3f_3805_ = lean_ctor_get(v_x_3803_, 1);
lean_inc(v_scheme_x3f_3805_);
v_pattern_x3f_3806_ = lean_ctor_get(v_x_3803_, 2);
lean_inc(v_pattern_x3f_3806_);
lean_dec_ref(v_x_3803_);
v___x_3807_ = ((lean_object*)(l_Lean_Lsp_instToJsonDocumentFilter_toJson___closed__0));
v___x_3808_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextEdit_toJson_spec__1(v___x_3807_, v_language_x3f_3804_);
v___x_3809_ = ((lean_object*)(l_Lean_Lsp_instToJsonDocumentFilter_toJson___closed__1));
v___x_3810_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextEdit_toJson_spec__1(v___x_3809_, v_scheme_x3f_3805_);
v___x_3811_ = ((lean_object*)(l_Lean_Lsp_instToJsonDocumentFilter_toJson___closed__2));
v___x_3812_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextEdit_toJson_spec__1(v___x_3811_, v_pattern_x3f_3806_);
v___x_3813_ = lean_box(0);
v___x_3814_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3814_, 0, v___x_3812_);
lean_ctor_set(v___x_3814_, 1, v___x_3813_);
v___x_3815_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3815_, 0, v___x_3810_);
lean_ctor_set(v___x_3815_, 1, v___x_3814_);
v___x_3816_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3816_, 0, v___x_3808_);
lean_ctor_set(v___x_3816_, 1, v___x_3815_);
v___x_3817_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__2));
v___x_3818_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLocation_toJson_spec__0(v___x_3816_, v___x_3817_);
v___x_3819_ = l_Lean_Json_mkObj(v___x_3818_);
lean_dec(v___x_3818_);
return v___x_3819_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__2(void){
_start:
{
uint8_t v___x_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; 
v___x_3827_ = 1;
v___x_3828_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__1));
v___x_3829_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3828_, v___x_3827_);
return v___x_3829_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__3(void){
_start:
{
lean_object* v___x_3830_; lean_object* v___x_3831_; lean_object* v___x_3832_; 
v___x_3830_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__5));
v___x_3831_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__2, &l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__2);
v___x_3832_ = lean_string_append(v___x_3831_, v___x_3830_);
return v___x_3832_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__6(void){
_start:
{
uint8_t v___x_3836_; lean_object* v___x_3837_; lean_object* v___x_3838_; 
v___x_3836_ = 1;
v___x_3837_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__5));
v___x_3838_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3837_, v___x_3836_);
return v___x_3838_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__7(void){
_start:
{
lean_object* v___x_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; 
v___x_3839_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__6, &l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__6);
v___x_3840_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__3, &l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__3);
v___x_3841_ = lean_string_append(v___x_3840_, v___x_3839_);
return v___x_3841_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__8(void){
_start:
{
lean_object* v___x_3842_; lean_object* v___x_3843_; lean_object* v___x_3844_; 
v___x_3842_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_3843_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__7, &l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__7);
v___x_3844_ = lean_string_append(v___x_3843_, v___x_3842_);
return v___x_3844_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__11(void){
_start:
{
uint8_t v___x_3848_; lean_object* v___x_3849_; lean_object* v___x_3850_; 
v___x_3848_ = 1;
v___x_3849_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__10));
v___x_3850_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3849_, v___x_3848_);
return v___x_3850_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__12(void){
_start:
{
lean_object* v___x_3851_; lean_object* v___x_3852_; lean_object* v___x_3853_; 
v___x_3851_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__11, &l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__11);
v___x_3852_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__3, &l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__3);
v___x_3853_ = lean_string_append(v___x_3852_, v___x_3851_);
return v___x_3853_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__13(void){
_start:
{
lean_object* v___x_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; 
v___x_3854_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_3855_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__12, &l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__12);
v___x_3856_ = lean_string_append(v___x_3855_, v___x_3854_);
return v___x_3856_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__16(void){
_start:
{
uint8_t v___x_3860_; lean_object* v___x_3861_; lean_object* v___x_3862_; 
v___x_3860_ = 1;
v___x_3861_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__15));
v___x_3862_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3861_, v___x_3860_);
return v___x_3862_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__17(void){
_start:
{
lean_object* v___x_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; 
v___x_3863_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__16, &l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__16_once, _init_l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__16);
v___x_3864_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__3, &l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__3);
v___x_3865_ = lean_string_append(v___x_3864_, v___x_3863_);
return v___x_3865_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__18(void){
_start:
{
lean_object* v___x_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; 
v___x_3866_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_3867_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__17, &l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__17_once, _init_l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__17);
v___x_3868_ = lean_string_append(v___x_3867_, v___x_3866_);
return v___x_3868_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDocumentFilter_fromJson(lean_object* v_json_3869_){
_start:
{
lean_object* v___x_3870_; lean_object* v___x_3871_; 
v___x_3870_ = ((lean_object*)(l_Lean_Lsp_instToJsonDocumentFilter_toJson___closed__0));
lean_inc(v_json_3869_);
v___x_3871_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextEdit_fromJson_spec__1(v_json_3869_, v___x_3870_);
if (lean_obj_tag(v___x_3871_) == 0)
{
lean_object* v_a_3872_; lean_object* v___x_3874_; uint8_t v_isShared_3875_; uint8_t v_isSharedCheck_3881_; 
lean_dec(v_json_3869_);
v_a_3872_ = lean_ctor_get(v___x_3871_, 0);
v_isSharedCheck_3881_ = !lean_is_exclusive(v___x_3871_);
if (v_isSharedCheck_3881_ == 0)
{
v___x_3874_ = v___x_3871_;
v_isShared_3875_ = v_isSharedCheck_3881_;
goto v_resetjp_3873_;
}
else
{
lean_inc(v_a_3872_);
lean_dec(v___x_3871_);
v___x_3874_ = lean_box(0);
v_isShared_3875_ = v_isSharedCheck_3881_;
goto v_resetjp_3873_;
}
v_resetjp_3873_:
{
lean_object* v___x_3876_; lean_object* v___x_3877_; lean_object* v___x_3879_; 
v___x_3876_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__8, &l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__8);
v___x_3877_ = lean_string_append(v___x_3876_, v_a_3872_);
lean_dec(v_a_3872_);
if (v_isShared_3875_ == 0)
{
lean_ctor_set(v___x_3874_, 0, v___x_3877_);
v___x_3879_ = v___x_3874_;
goto v_reusejp_3878_;
}
else
{
lean_object* v_reuseFailAlloc_3880_; 
v_reuseFailAlloc_3880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3880_, 0, v___x_3877_);
v___x_3879_ = v_reuseFailAlloc_3880_;
goto v_reusejp_3878_;
}
v_reusejp_3878_:
{
return v___x_3879_;
}
}
}
else
{
if (lean_obj_tag(v___x_3871_) == 0)
{
lean_object* v_a_3882_; lean_object* v___x_3884_; uint8_t v_isShared_3885_; uint8_t v_isSharedCheck_3889_; 
lean_dec(v_json_3869_);
v_a_3882_ = lean_ctor_get(v___x_3871_, 0);
v_isSharedCheck_3889_ = !lean_is_exclusive(v___x_3871_);
if (v_isSharedCheck_3889_ == 0)
{
v___x_3884_ = v___x_3871_;
v_isShared_3885_ = v_isSharedCheck_3889_;
goto v_resetjp_3883_;
}
else
{
lean_inc(v_a_3882_);
lean_dec(v___x_3871_);
v___x_3884_ = lean_box(0);
v_isShared_3885_ = v_isSharedCheck_3889_;
goto v_resetjp_3883_;
}
v_resetjp_3883_:
{
lean_object* v___x_3887_; 
if (v_isShared_3885_ == 0)
{
lean_ctor_set_tag(v___x_3884_, 0);
v___x_3887_ = v___x_3884_;
goto v_reusejp_3886_;
}
else
{
lean_object* v_reuseFailAlloc_3888_; 
v_reuseFailAlloc_3888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3888_, 0, v_a_3882_);
v___x_3887_ = v_reuseFailAlloc_3888_;
goto v_reusejp_3886_;
}
v_reusejp_3886_:
{
return v___x_3887_;
}
}
}
else
{
lean_object* v_a_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; 
v_a_3890_ = lean_ctor_get(v___x_3871_, 0);
lean_inc(v_a_3890_);
lean_dec_ref_known(v___x_3871_, 1);
v___x_3891_ = ((lean_object*)(l_Lean_Lsp_instToJsonDocumentFilter_toJson___closed__1));
lean_inc(v_json_3869_);
v___x_3892_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextEdit_fromJson_spec__1(v_json_3869_, v___x_3891_);
if (lean_obj_tag(v___x_3892_) == 0)
{
lean_object* v_a_3893_; lean_object* v___x_3895_; uint8_t v_isShared_3896_; uint8_t v_isSharedCheck_3902_; 
lean_dec(v_a_3890_);
lean_dec(v_json_3869_);
v_a_3893_ = lean_ctor_get(v___x_3892_, 0);
v_isSharedCheck_3902_ = !lean_is_exclusive(v___x_3892_);
if (v_isSharedCheck_3902_ == 0)
{
v___x_3895_ = v___x_3892_;
v_isShared_3896_ = v_isSharedCheck_3902_;
goto v_resetjp_3894_;
}
else
{
lean_inc(v_a_3893_);
lean_dec(v___x_3892_);
v___x_3895_ = lean_box(0);
v_isShared_3896_ = v_isSharedCheck_3902_;
goto v_resetjp_3894_;
}
v_resetjp_3894_:
{
lean_object* v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3900_; 
v___x_3897_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__13, &l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__13);
v___x_3898_ = lean_string_append(v___x_3897_, v_a_3893_);
lean_dec(v_a_3893_);
if (v_isShared_3896_ == 0)
{
lean_ctor_set(v___x_3895_, 0, v___x_3898_);
v___x_3900_ = v___x_3895_;
goto v_reusejp_3899_;
}
else
{
lean_object* v_reuseFailAlloc_3901_; 
v_reuseFailAlloc_3901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3901_, 0, v___x_3898_);
v___x_3900_ = v_reuseFailAlloc_3901_;
goto v_reusejp_3899_;
}
v_reusejp_3899_:
{
return v___x_3900_;
}
}
}
else
{
if (lean_obj_tag(v___x_3892_) == 0)
{
lean_object* v_a_3903_; lean_object* v___x_3905_; uint8_t v_isShared_3906_; uint8_t v_isSharedCheck_3910_; 
lean_dec(v_a_3890_);
lean_dec(v_json_3869_);
v_a_3903_ = lean_ctor_get(v___x_3892_, 0);
v_isSharedCheck_3910_ = !lean_is_exclusive(v___x_3892_);
if (v_isSharedCheck_3910_ == 0)
{
v___x_3905_ = v___x_3892_;
v_isShared_3906_ = v_isSharedCheck_3910_;
goto v_resetjp_3904_;
}
else
{
lean_inc(v_a_3903_);
lean_dec(v___x_3892_);
v___x_3905_ = lean_box(0);
v_isShared_3906_ = v_isSharedCheck_3910_;
goto v_resetjp_3904_;
}
v_resetjp_3904_:
{
lean_object* v___x_3908_; 
if (v_isShared_3906_ == 0)
{
lean_ctor_set_tag(v___x_3905_, 0);
v___x_3908_ = v___x_3905_;
goto v_reusejp_3907_;
}
else
{
lean_object* v_reuseFailAlloc_3909_; 
v_reuseFailAlloc_3909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3909_, 0, v_a_3903_);
v___x_3908_ = v_reuseFailAlloc_3909_;
goto v_reusejp_3907_;
}
v_reusejp_3907_:
{
return v___x_3908_;
}
}
}
else
{
lean_object* v_a_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; 
v_a_3911_ = lean_ctor_get(v___x_3892_, 0);
lean_inc(v_a_3911_);
lean_dec_ref_known(v___x_3892_, 1);
v___x_3912_ = ((lean_object*)(l_Lean_Lsp_instToJsonDocumentFilter_toJson___closed__2));
v___x_3913_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextEdit_fromJson_spec__1(v_json_3869_, v___x_3912_);
if (lean_obj_tag(v___x_3913_) == 0)
{
lean_object* v_a_3914_; lean_object* v___x_3916_; uint8_t v_isShared_3917_; uint8_t v_isSharedCheck_3923_; 
lean_dec(v_a_3911_);
lean_dec(v_a_3890_);
v_a_3914_ = lean_ctor_get(v___x_3913_, 0);
v_isSharedCheck_3923_ = !lean_is_exclusive(v___x_3913_);
if (v_isSharedCheck_3923_ == 0)
{
v___x_3916_ = v___x_3913_;
v_isShared_3917_ = v_isSharedCheck_3923_;
goto v_resetjp_3915_;
}
else
{
lean_inc(v_a_3914_);
lean_dec(v___x_3913_);
v___x_3916_ = lean_box(0);
v_isShared_3917_ = v_isSharedCheck_3923_;
goto v_resetjp_3915_;
}
v_resetjp_3915_:
{
lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3921_; 
v___x_3918_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__18, &l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__18_once, _init_l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__18);
v___x_3919_ = lean_string_append(v___x_3918_, v_a_3914_);
lean_dec(v_a_3914_);
if (v_isShared_3917_ == 0)
{
lean_ctor_set(v___x_3916_, 0, v___x_3919_);
v___x_3921_ = v___x_3916_;
goto v_reusejp_3920_;
}
else
{
lean_object* v_reuseFailAlloc_3922_; 
v_reuseFailAlloc_3922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3922_, 0, v___x_3919_);
v___x_3921_ = v_reuseFailAlloc_3922_;
goto v_reusejp_3920_;
}
v_reusejp_3920_:
{
return v___x_3921_;
}
}
}
else
{
if (lean_obj_tag(v___x_3913_) == 0)
{
lean_object* v_a_3924_; lean_object* v___x_3926_; uint8_t v_isShared_3927_; uint8_t v_isSharedCheck_3931_; 
lean_dec(v_a_3911_);
lean_dec(v_a_3890_);
v_a_3924_ = lean_ctor_get(v___x_3913_, 0);
v_isSharedCheck_3931_ = !lean_is_exclusive(v___x_3913_);
if (v_isSharedCheck_3931_ == 0)
{
v___x_3926_ = v___x_3913_;
v_isShared_3927_ = v_isSharedCheck_3931_;
goto v_resetjp_3925_;
}
else
{
lean_inc(v_a_3924_);
lean_dec(v___x_3913_);
v___x_3926_ = lean_box(0);
v_isShared_3927_ = v_isSharedCheck_3931_;
goto v_resetjp_3925_;
}
v_resetjp_3925_:
{
lean_object* v___x_3929_; 
if (v_isShared_3927_ == 0)
{
lean_ctor_set_tag(v___x_3926_, 0);
v___x_3929_ = v___x_3926_;
goto v_reusejp_3928_;
}
else
{
lean_object* v_reuseFailAlloc_3930_; 
v_reuseFailAlloc_3930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3930_, 0, v_a_3924_);
v___x_3929_ = v_reuseFailAlloc_3930_;
goto v_reusejp_3928_;
}
v_reusejp_3928_:
{
return v___x_3929_;
}
}
}
else
{
lean_object* v_a_3932_; lean_object* v___x_3934_; uint8_t v_isShared_3935_; uint8_t v_isSharedCheck_3940_; 
v_a_3932_ = lean_ctor_get(v___x_3913_, 0);
v_isSharedCheck_3940_ = !lean_is_exclusive(v___x_3913_);
if (v_isSharedCheck_3940_ == 0)
{
v___x_3934_ = v___x_3913_;
v_isShared_3935_ = v_isSharedCheck_3940_;
goto v_resetjp_3933_;
}
else
{
lean_inc(v_a_3932_);
lean_dec(v___x_3913_);
v___x_3934_ = lean_box(0);
v_isShared_3935_ = v_isSharedCheck_3940_;
goto v_resetjp_3933_;
}
v_resetjp_3933_:
{
lean_object* v___x_3936_; lean_object* v___x_3938_; 
v___x_3936_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3936_, 0, v_a_3890_);
lean_ctor_set(v___x_3936_, 1, v_a_3911_);
lean_ctor_set(v___x_3936_, 2, v_a_3932_);
if (v_isShared_3935_ == 0)
{
lean_ctor_set(v___x_3934_, 0, v___x_3936_);
v___x_3938_ = v___x_3934_;
goto v_reusejp_3937_;
}
else
{
lean_object* v_reuseFailAlloc_3939_; 
v_reuseFailAlloc_3939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3939_, 0, v___x_3936_);
v___x_3938_ = v_reuseFailAlloc_3939_;
goto v_reusejp_3937_;
}
v_reusejp_3937_:
{
return v___x_3938_;
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
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonStaticRegistrationOptions_toJson(lean_object* v_x_3950_){
_start:
{
lean_object* v___x_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; 
v___x_3951_ = ((lean_object*)(l_Lean_Lsp_instToJsonStaticRegistrationOptions_toJson___closed__0));
v___x_3952_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextEdit_toJson_spec__1(v___x_3951_, v_x_3950_);
v___x_3953_ = lean_box(0);
v___x_3954_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3954_, 0, v___x_3952_);
lean_ctor_set(v___x_3954_, 1, v___x_3953_);
v___x_3955_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__2));
v___x_3956_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLocation_toJson_spec__0(v___x_3954_, v___x_3955_);
v___x_3957_ = l_Lean_Json_mkObj(v___x_3956_);
lean_dec(v___x_3956_);
return v___x_3957_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonStaticRegistrationOptions_fromJson___closed__2(void){
_start:
{
uint8_t v___x_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; 
v___x_3965_ = 1;
v___x_3966_ = ((lean_object*)(l_Lean_Lsp_instFromJsonStaticRegistrationOptions_fromJson___closed__1));
v___x_3967_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3966_, v___x_3965_);
return v___x_3967_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonStaticRegistrationOptions_fromJson___closed__3(void){
_start:
{
lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; 
v___x_3968_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__5));
v___x_3969_ = lean_obj_once(&l_Lean_Lsp_instFromJsonStaticRegistrationOptions_fromJson___closed__2, &l_Lean_Lsp_instFromJsonStaticRegistrationOptions_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonStaticRegistrationOptions_fromJson___closed__2);
v___x_3970_ = lean_string_append(v___x_3969_, v___x_3968_);
return v___x_3970_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonStaticRegistrationOptions_fromJson___closed__6(void){
_start:
{
uint8_t v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; 
v___x_3974_ = 1;
v___x_3975_ = ((lean_object*)(l_Lean_Lsp_instFromJsonStaticRegistrationOptions_fromJson___closed__5));
v___x_3976_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3975_, v___x_3974_);
return v___x_3976_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonStaticRegistrationOptions_fromJson___closed__7(void){
_start:
{
lean_object* v___x_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; 
v___x_3977_ = lean_obj_once(&l_Lean_Lsp_instFromJsonStaticRegistrationOptions_fromJson___closed__6, &l_Lean_Lsp_instFromJsonStaticRegistrationOptions_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonStaticRegistrationOptions_fromJson___closed__6);
v___x_3978_ = lean_obj_once(&l_Lean_Lsp_instFromJsonStaticRegistrationOptions_fromJson___closed__3, &l_Lean_Lsp_instFromJsonStaticRegistrationOptions_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonStaticRegistrationOptions_fromJson___closed__3);
v___x_3979_ = lean_string_append(v___x_3978_, v___x_3977_);
return v___x_3979_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonStaticRegistrationOptions_fromJson___closed__8(void){
_start:
{
lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; 
v___x_3980_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_3981_ = lean_obj_once(&l_Lean_Lsp_instFromJsonStaticRegistrationOptions_fromJson___closed__7, &l_Lean_Lsp_instFromJsonStaticRegistrationOptions_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonStaticRegistrationOptions_fromJson___closed__7);
v___x_3982_ = lean_string_append(v___x_3981_, v___x_3980_);
return v___x_3982_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonStaticRegistrationOptions_fromJson(lean_object* v_json_3983_){
_start:
{
lean_object* v___x_3984_; lean_object* v___x_3985_; 
v___x_3984_ = ((lean_object*)(l_Lean_Lsp_instToJsonStaticRegistrationOptions_toJson___closed__0));
v___x_3985_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextEdit_fromJson_spec__1(v_json_3983_, v___x_3984_);
if (lean_obj_tag(v___x_3985_) == 0)
{
lean_object* v_a_3986_; lean_object* v___x_3988_; uint8_t v_isShared_3989_; uint8_t v_isSharedCheck_3995_; 
v_a_3986_ = lean_ctor_get(v___x_3985_, 0);
v_isSharedCheck_3995_ = !lean_is_exclusive(v___x_3985_);
if (v_isSharedCheck_3995_ == 0)
{
v___x_3988_ = v___x_3985_;
v_isShared_3989_ = v_isSharedCheck_3995_;
goto v_resetjp_3987_;
}
else
{
lean_inc(v_a_3986_);
lean_dec(v___x_3985_);
v___x_3988_ = lean_box(0);
v_isShared_3989_ = v_isSharedCheck_3995_;
goto v_resetjp_3987_;
}
v_resetjp_3987_:
{
lean_object* v___x_3990_; lean_object* v___x_3991_; lean_object* v___x_3993_; 
v___x_3990_ = lean_obj_once(&l_Lean_Lsp_instFromJsonStaticRegistrationOptions_fromJson___closed__8, &l_Lean_Lsp_instFromJsonStaticRegistrationOptions_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonStaticRegistrationOptions_fromJson___closed__8);
v___x_3991_ = lean_string_append(v___x_3990_, v_a_3986_);
lean_dec(v_a_3986_);
if (v_isShared_3989_ == 0)
{
lean_ctor_set(v___x_3988_, 0, v___x_3991_);
v___x_3993_ = v___x_3988_;
goto v_reusejp_3992_;
}
else
{
lean_object* v_reuseFailAlloc_3994_; 
v_reuseFailAlloc_3994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3994_, 0, v___x_3991_);
v___x_3993_ = v_reuseFailAlloc_3994_;
goto v_reusejp_3992_;
}
v_reusejp_3992_:
{
return v___x_3993_;
}
}
}
else
{
if (lean_obj_tag(v___x_3985_) == 0)
{
lean_object* v_a_3996_; lean_object* v___x_3998_; uint8_t v_isShared_3999_; uint8_t v_isSharedCheck_4003_; 
v_a_3996_ = lean_ctor_get(v___x_3985_, 0);
v_isSharedCheck_4003_ = !lean_is_exclusive(v___x_3985_);
if (v_isSharedCheck_4003_ == 0)
{
v___x_3998_ = v___x_3985_;
v_isShared_3999_ = v_isSharedCheck_4003_;
goto v_resetjp_3997_;
}
else
{
lean_inc(v_a_3996_);
lean_dec(v___x_3985_);
v___x_3998_ = lean_box(0);
v_isShared_3999_ = v_isSharedCheck_4003_;
goto v_resetjp_3997_;
}
v_resetjp_3997_:
{
lean_object* v___x_4001_; 
if (v_isShared_3999_ == 0)
{
lean_ctor_set_tag(v___x_3998_, 0);
v___x_4001_ = v___x_3998_;
goto v_reusejp_4000_;
}
else
{
lean_object* v_reuseFailAlloc_4002_; 
v_reuseFailAlloc_4002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4002_, 0, v_a_3996_);
v___x_4001_ = v_reuseFailAlloc_4002_;
goto v_reusejp_4000_;
}
v_reusejp_4000_:
{
return v___x_4001_;
}
}
}
else
{
lean_object* v_a_4004_; lean_object* v___x_4006_; uint8_t v_isShared_4007_; uint8_t v_isSharedCheck_4011_; 
v_a_4004_ = lean_ctor_get(v___x_3985_, 0);
v_isSharedCheck_4011_ = !lean_is_exclusive(v___x_3985_);
if (v_isSharedCheck_4011_ == 0)
{
v___x_4006_ = v___x_3985_;
v_isShared_4007_ = v_isSharedCheck_4011_;
goto v_resetjp_4005_;
}
else
{
lean_inc(v_a_4004_);
lean_dec(v___x_3985_);
v___x_4006_ = lean_box(0);
v_isShared_4007_ = v_isSharedCheck_4011_;
goto v_resetjp_4005_;
}
v_resetjp_4005_:
{
lean_object* v___x_4009_; 
if (v_isShared_4007_ == 0)
{
v___x_4009_ = v___x_4006_;
goto v_reusejp_4008_;
}
else
{
lean_object* v_reuseFailAlloc_4010_; 
v_reuseFailAlloc_4010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4010_, 0, v_a_4004_);
v___x_4009_ = v_reuseFailAlloc_4010_;
goto v_reusejp_4008_;
}
v_reusejp_4008_:
{
return v___x_4009_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonTextDocumentRegistrationOptions_toJson_spec__0_spec__0_spec__1(size_t v_sz_4014_, size_t v_i_4015_, lean_object* v_bs_4016_){
_start:
{
uint8_t v___x_4017_; 
v___x_4017_ = lean_usize_dec_lt(v_i_4015_, v_sz_4014_);
if (v___x_4017_ == 0)
{
return v_bs_4016_;
}
else
{
lean_object* v_v_4018_; lean_object* v___x_4019_; lean_object* v_bs_x27_4020_; lean_object* v___x_4021_; size_t v___x_4022_; size_t v___x_4023_; lean_object* v___x_4024_; 
v_v_4018_ = lean_array_uget(v_bs_4016_, v_i_4015_);
v___x_4019_ = lean_unsigned_to_nat(0u);
v_bs_x27_4020_ = lean_array_uset(v_bs_4016_, v_i_4015_, v___x_4019_);
v___x_4021_ = l_Lean_Lsp_instToJsonDocumentFilter_toJson(v_v_4018_);
v___x_4022_ = ((size_t)1ULL);
v___x_4023_ = lean_usize_add(v_i_4015_, v___x_4022_);
v___x_4024_ = lean_array_uset(v_bs_x27_4020_, v_i_4015_, v___x_4021_);
v_i_4015_ = v___x_4023_;
v_bs_4016_ = v___x_4024_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonTextDocumentRegistrationOptions_toJson_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_4026_, lean_object* v_i_4027_, lean_object* v_bs_4028_){
_start:
{
size_t v_sz_boxed_4029_; size_t v_i_boxed_4030_; lean_object* v_res_4031_; 
v_sz_boxed_4029_ = lean_unbox_usize(v_sz_4026_);
lean_dec(v_sz_4026_);
v_i_boxed_4030_ = lean_unbox_usize(v_i_4027_);
lean_dec(v_i_4027_);
v_res_4031_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonTextDocumentRegistrationOptions_toJson_spec__0_spec__0_spec__1(v_sz_boxed_4029_, v_i_boxed_4030_, v_bs_4028_);
return v_res_4031_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonTextDocumentRegistrationOptions_toJson_spec__0_spec__0(lean_object* v_a_4032_){
_start:
{
size_t v_sz_4033_; size_t v___x_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; 
v_sz_4033_ = lean_array_size(v_a_4032_);
v___x_4034_ = ((size_t)0ULL);
v___x_4035_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonTextDocumentRegistrationOptions_toJson_spec__0_spec__0_spec__1(v_sz_4033_, v___x_4034_, v_a_4032_);
v___x_4036_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_4036_, 0, v___x_4035_);
return v___x_4036_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextDocumentRegistrationOptions_toJson_spec__0(lean_object* v_k_4037_, lean_object* v_x_4038_){
_start:
{
if (lean_obj_tag(v_x_4038_) == 0)
{
lean_object* v___x_4039_; 
lean_dec_ref(v_k_4037_);
v___x_4039_ = lean_box(0);
return v___x_4039_;
}
else
{
lean_object* v_val_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; 
v_val_4040_ = lean_ctor_get(v_x_4038_, 0);
lean_inc(v_val_4040_);
lean_dec_ref_known(v_x_4038_, 1);
v___x_4041_ = l_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonTextDocumentRegistrationOptions_toJson_spec__0_spec__0(v_val_4040_);
v___x_4042_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4042_, 0, v_k_4037_);
lean_ctor_set(v___x_4042_, 1, v___x_4041_);
v___x_4043_ = lean_box(0);
v___x_4044_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4044_, 0, v___x_4042_);
lean_ctor_set(v___x_4044_, 1, v___x_4043_);
return v___x_4044_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonTextDocumentRegistrationOptions_toJson(lean_object* v_x_4046_){
_start:
{
lean_object* v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; 
v___x_4047_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextDocumentRegistrationOptions_toJson___closed__0));
v___x_4048_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextDocumentRegistrationOptions_toJson_spec__0(v___x_4047_, v_x_4046_);
v___x_4049_ = lean_box(0);
v___x_4050_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4050_, 0, v___x_4048_);
lean_ctor_set(v___x_4050_, 1, v___x_4049_);
v___x_4051_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__2));
v___x_4052_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLocation_toJson_spec__0(v___x_4050_, v___x_4051_);
v___x_4053_ = l_Lean_Json_mkObj(v___x_4052_);
lean_dec(v___x_4052_);
return v___x_4053_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson_spec__0_spec__0_spec__1_spec__2(size_t v_sz_4056_, size_t v_i_4057_, lean_object* v_bs_4058_){
_start:
{
uint8_t v___x_4059_; 
v___x_4059_ = lean_usize_dec_lt(v_i_4057_, v_sz_4056_);
if (v___x_4059_ == 0)
{
lean_object* v___x_4060_; 
v___x_4060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4060_, 0, v_bs_4058_);
return v___x_4060_;
}
else
{
lean_object* v_v_4061_; lean_object* v___x_4062_; 
v_v_4061_ = lean_array_uget_borrowed(v_bs_4058_, v_i_4057_);
lean_inc(v_v_4061_);
v___x_4062_ = l_Lean_Lsp_instFromJsonDocumentFilter_fromJson(v_v_4061_);
if (lean_obj_tag(v___x_4062_) == 0)
{
lean_object* v_a_4063_; lean_object* v___x_4065_; uint8_t v_isShared_4066_; uint8_t v_isSharedCheck_4070_; 
lean_dec_ref(v_bs_4058_);
v_a_4063_ = lean_ctor_get(v___x_4062_, 0);
v_isSharedCheck_4070_ = !lean_is_exclusive(v___x_4062_);
if (v_isSharedCheck_4070_ == 0)
{
v___x_4065_ = v___x_4062_;
v_isShared_4066_ = v_isSharedCheck_4070_;
goto v_resetjp_4064_;
}
else
{
lean_inc(v_a_4063_);
lean_dec(v___x_4062_);
v___x_4065_ = lean_box(0);
v_isShared_4066_ = v_isSharedCheck_4070_;
goto v_resetjp_4064_;
}
v_resetjp_4064_:
{
lean_object* v___x_4068_; 
if (v_isShared_4066_ == 0)
{
v___x_4068_ = v___x_4065_;
goto v_reusejp_4067_;
}
else
{
lean_object* v_reuseFailAlloc_4069_; 
v_reuseFailAlloc_4069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4069_, 0, v_a_4063_);
v___x_4068_ = v_reuseFailAlloc_4069_;
goto v_reusejp_4067_;
}
v_reusejp_4067_:
{
return v___x_4068_;
}
}
}
else
{
lean_object* v_a_4071_; lean_object* v___x_4072_; lean_object* v_bs_x27_4073_; size_t v___x_4074_; size_t v___x_4075_; lean_object* v___x_4076_; 
v_a_4071_ = lean_ctor_get(v___x_4062_, 0);
lean_inc(v_a_4071_);
lean_dec_ref_known(v___x_4062_, 1);
v___x_4072_ = lean_unsigned_to_nat(0u);
v_bs_x27_4073_ = lean_array_uset(v_bs_4058_, v_i_4057_, v___x_4072_);
v___x_4074_ = ((size_t)1ULL);
v___x_4075_ = lean_usize_add(v_i_4057_, v___x_4074_);
v___x_4076_ = lean_array_uset(v_bs_x27_4073_, v_i_4057_, v_a_4071_);
v_i_4057_ = v___x_4075_;
v_bs_4058_ = v___x_4076_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_sz_4078_, lean_object* v_i_4079_, lean_object* v_bs_4080_){
_start:
{
size_t v_sz_boxed_4081_; size_t v_i_boxed_4082_; lean_object* v_res_4083_; 
v_sz_boxed_4081_ = lean_unbox_usize(v_sz_4078_);
lean_dec(v_sz_4078_);
v_i_boxed_4082_ = lean_unbox_usize(v_i_4079_);
lean_dec(v_i_4079_);
v_res_4083_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson_spec__0_spec__0_spec__1_spec__2(v_sz_boxed_4081_, v_i_boxed_4082_, v_bs_4080_);
return v_res_4083_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson_spec__0_spec__0_spec__1(lean_object* v_x_4084_){
_start:
{
if (lean_obj_tag(v_x_4084_) == 4)
{
lean_object* v_elems_4085_; size_t v_sz_4086_; size_t v___x_4087_; lean_object* v___x_4088_; 
v_elems_4085_ = lean_ctor_get(v_x_4084_, 0);
lean_inc_ref(v_elems_4085_);
lean_dec_ref_known(v_x_4084_, 1);
v_sz_4086_ = lean_array_size(v_elems_4085_);
v___x_4087_ = ((size_t)0ULL);
v___x_4088_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson_spec__0_spec__0_spec__1_spec__2(v_sz_4086_, v___x_4087_, v_elems_4085_);
return v___x_4088_;
}
else
{
lean_object* v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; 
v___x_4089_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCommand_fromJson_spec__0_spec__0_spec__1___closed__0));
v___x_4090_ = lean_unsigned_to_nat(80u);
v___x_4091_ = l_Lean_Json_pretty(v_x_4084_, v___x_4090_);
v___x_4092_ = lean_string_append(v___x_4089_, v___x_4091_);
lean_dec_ref(v___x_4091_);
v___x_4093_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCommand_fromJson_spec__0_spec__0_spec__1___closed__1));
v___x_4094_ = lean_string_append(v___x_4092_, v___x_4093_);
v___x_4095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4095_, 0, v___x_4094_);
return v___x_4095_;
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson_spec__0_spec__0(lean_object* v_x_4098_){
_start:
{
if (lean_obj_tag(v_x_4098_) == 0)
{
lean_object* v___x_4099_; 
v___x_4099_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson_spec__0_spec__0___closed__0));
return v___x_4099_;
}
else
{
lean_object* v___x_4100_; 
v___x_4100_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson_spec__0_spec__0_spec__1(v_x_4098_);
if (lean_obj_tag(v___x_4100_) == 0)
{
lean_object* v_a_4101_; lean_object* v___x_4103_; uint8_t v_isShared_4104_; uint8_t v_isSharedCheck_4108_; 
v_a_4101_ = lean_ctor_get(v___x_4100_, 0);
v_isSharedCheck_4108_ = !lean_is_exclusive(v___x_4100_);
if (v_isSharedCheck_4108_ == 0)
{
v___x_4103_ = v___x_4100_;
v_isShared_4104_ = v_isSharedCheck_4108_;
goto v_resetjp_4102_;
}
else
{
lean_inc(v_a_4101_);
lean_dec(v___x_4100_);
v___x_4103_ = lean_box(0);
v_isShared_4104_ = v_isSharedCheck_4108_;
goto v_resetjp_4102_;
}
v_resetjp_4102_:
{
lean_object* v___x_4106_; 
if (v_isShared_4104_ == 0)
{
v___x_4106_ = v___x_4103_;
goto v_reusejp_4105_;
}
else
{
lean_object* v_reuseFailAlloc_4107_; 
v_reuseFailAlloc_4107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4107_, 0, v_a_4101_);
v___x_4106_ = v_reuseFailAlloc_4107_;
goto v_reusejp_4105_;
}
v_reusejp_4105_:
{
return v___x_4106_;
}
}
}
else
{
lean_object* v_a_4109_; lean_object* v___x_4111_; uint8_t v_isShared_4112_; uint8_t v_isSharedCheck_4117_; 
v_a_4109_ = lean_ctor_get(v___x_4100_, 0);
v_isSharedCheck_4117_ = !lean_is_exclusive(v___x_4100_);
if (v_isSharedCheck_4117_ == 0)
{
v___x_4111_ = v___x_4100_;
v_isShared_4112_ = v_isSharedCheck_4117_;
goto v_resetjp_4110_;
}
else
{
lean_inc(v_a_4109_);
lean_dec(v___x_4100_);
v___x_4111_ = lean_box(0);
v_isShared_4112_ = v_isSharedCheck_4117_;
goto v_resetjp_4110_;
}
v_resetjp_4110_:
{
lean_object* v___x_4113_; lean_object* v___x_4115_; 
v___x_4113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4113_, 0, v_a_4109_);
if (v_isShared_4112_ == 0)
{
lean_ctor_set(v___x_4111_, 0, v___x_4113_);
v___x_4115_ = v___x_4111_;
goto v_reusejp_4114_;
}
else
{
lean_object* v_reuseFailAlloc_4116_; 
v_reuseFailAlloc_4116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4116_, 0, v___x_4113_);
v___x_4115_ = v_reuseFailAlloc_4116_;
goto v_reusejp_4114_;
}
v_reusejp_4114_:
{
return v___x_4115_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson_spec__0(lean_object* v_j_4118_, lean_object* v_k_4119_){
_start:
{
lean_object* v___x_4120_; lean_object* v___x_4121_; 
v___x_4120_ = l_Lean_Json_getObjValD(v_j_4118_, v_k_4119_);
v___x_4121_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson_spec__0_spec__0(v___x_4120_);
return v___x_4121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson_spec__0___boxed(lean_object* v_j_4122_, lean_object* v_k_4123_){
_start:
{
lean_object* v_res_4124_; 
v_res_4124_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson_spec__0(v_j_4122_, v_k_4123_);
lean_dec_ref(v_k_4123_);
return v_res_4124_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson___closed__2(void){
_start:
{
uint8_t v___x_4130_; lean_object* v___x_4131_; lean_object* v___x_4132_; 
v___x_4130_ = 1;
v___x_4131_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson___closed__1));
v___x_4132_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4131_, v___x_4130_);
return v___x_4132_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson___closed__3(void){
_start:
{
lean_object* v___x_4133_; lean_object* v___x_4134_; lean_object* v___x_4135_; 
v___x_4133_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__5));
v___x_4134_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson___closed__2, &l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson___closed__2);
v___x_4135_ = lean_string_append(v___x_4134_, v___x_4133_);
return v___x_4135_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson___closed__6(void){
_start:
{
uint8_t v___x_4139_; lean_object* v___x_4140_; lean_object* v___x_4141_; 
v___x_4139_ = 1;
v___x_4140_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson___closed__5));
v___x_4141_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4140_, v___x_4139_);
return v___x_4141_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson___closed__7(void){
_start:
{
lean_object* v___x_4142_; lean_object* v___x_4143_; lean_object* v___x_4144_; 
v___x_4142_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson___closed__6, &l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson___closed__6);
v___x_4143_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson___closed__3, &l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson___closed__3);
v___x_4144_ = lean_string_append(v___x_4143_, v___x_4142_);
return v___x_4144_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson___closed__8(void){
_start:
{
lean_object* v___x_4145_; lean_object* v___x_4146_; lean_object* v___x_4147_; 
v___x_4145_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_4146_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson___closed__7, &l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson___closed__7);
v___x_4147_ = lean_string_append(v___x_4146_, v___x_4145_);
return v___x_4147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson(lean_object* v_json_4148_){
_start:
{
lean_object* v___x_4149_; lean_object* v___x_4150_; 
v___x_4149_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextDocumentRegistrationOptions_toJson___closed__0));
v___x_4150_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson_spec__0(v_json_4148_, v___x_4149_);
if (lean_obj_tag(v___x_4150_) == 0)
{
lean_object* v_a_4151_; lean_object* v___x_4153_; uint8_t v_isShared_4154_; uint8_t v_isSharedCheck_4160_; 
v_a_4151_ = lean_ctor_get(v___x_4150_, 0);
v_isSharedCheck_4160_ = !lean_is_exclusive(v___x_4150_);
if (v_isSharedCheck_4160_ == 0)
{
v___x_4153_ = v___x_4150_;
v_isShared_4154_ = v_isSharedCheck_4160_;
goto v_resetjp_4152_;
}
else
{
lean_inc(v_a_4151_);
lean_dec(v___x_4150_);
v___x_4153_ = lean_box(0);
v_isShared_4154_ = v_isSharedCheck_4160_;
goto v_resetjp_4152_;
}
v_resetjp_4152_:
{
lean_object* v___x_4155_; lean_object* v___x_4156_; lean_object* v___x_4158_; 
v___x_4155_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson___closed__8, &l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson___closed__8);
v___x_4156_ = lean_string_append(v___x_4155_, v_a_4151_);
lean_dec(v_a_4151_);
if (v_isShared_4154_ == 0)
{
lean_ctor_set(v___x_4153_, 0, v___x_4156_);
v___x_4158_ = v___x_4153_;
goto v_reusejp_4157_;
}
else
{
lean_object* v_reuseFailAlloc_4159_; 
v_reuseFailAlloc_4159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4159_, 0, v___x_4156_);
v___x_4158_ = v_reuseFailAlloc_4159_;
goto v_reusejp_4157_;
}
v_reusejp_4157_:
{
return v___x_4158_;
}
}
}
else
{
if (lean_obj_tag(v___x_4150_) == 0)
{
lean_object* v_a_4161_; lean_object* v___x_4163_; uint8_t v_isShared_4164_; uint8_t v_isSharedCheck_4168_; 
v_a_4161_ = lean_ctor_get(v___x_4150_, 0);
v_isSharedCheck_4168_ = !lean_is_exclusive(v___x_4150_);
if (v_isSharedCheck_4168_ == 0)
{
v___x_4163_ = v___x_4150_;
v_isShared_4164_ = v_isSharedCheck_4168_;
goto v_resetjp_4162_;
}
else
{
lean_inc(v_a_4161_);
lean_dec(v___x_4150_);
v___x_4163_ = lean_box(0);
v_isShared_4164_ = v_isSharedCheck_4168_;
goto v_resetjp_4162_;
}
v_resetjp_4162_:
{
lean_object* v___x_4166_; 
if (v_isShared_4164_ == 0)
{
lean_ctor_set_tag(v___x_4163_, 0);
v___x_4166_ = v___x_4163_;
goto v_reusejp_4165_;
}
else
{
lean_object* v_reuseFailAlloc_4167_; 
v_reuseFailAlloc_4167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4167_, 0, v_a_4161_);
v___x_4166_ = v_reuseFailAlloc_4167_;
goto v_reusejp_4165_;
}
v_reusejp_4165_:
{
return v___x_4166_;
}
}
}
else
{
lean_object* v_a_4169_; lean_object* v___x_4171_; uint8_t v_isShared_4172_; uint8_t v_isSharedCheck_4176_; 
v_a_4169_ = lean_ctor_get(v___x_4150_, 0);
v_isSharedCheck_4176_ = !lean_is_exclusive(v___x_4150_);
if (v_isSharedCheck_4176_ == 0)
{
v___x_4171_ = v___x_4150_;
v_isShared_4172_ = v_isSharedCheck_4176_;
goto v_resetjp_4170_;
}
else
{
lean_inc(v_a_4169_);
lean_dec(v___x_4150_);
v___x_4171_ = lean_box(0);
v_isShared_4172_ = v_isSharedCheck_4176_;
goto v_resetjp_4170_;
}
v_resetjp_4170_:
{
lean_object* v___x_4174_; 
if (v_isShared_4172_ == 0)
{
v___x_4174_ = v___x_4171_;
goto v_reusejp_4173_;
}
else
{
lean_object* v_reuseFailAlloc_4175_; 
v_reuseFailAlloc_4175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4175_, 0, v_a_4169_);
v___x_4174_ = v_reuseFailAlloc_4175_;
goto v_reusejp_4173_;
}
v_reusejp_4173_:
{
return v___x_4174_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MarkupKind_ctorIdx(uint8_t v_x_4179_){
_start:
{
if (v_x_4179_ == 0)
{
lean_object* v___x_4180_; 
v___x_4180_ = lean_unsigned_to_nat(0u);
return v___x_4180_;
}
else
{
lean_object* v___x_4181_; 
v___x_4181_ = lean_unsigned_to_nat(1u);
return v___x_4181_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MarkupKind_ctorIdx___boxed(lean_object* v_x_4182_){
_start:
{
uint8_t v_x_boxed_4183_; lean_object* v_res_4184_; 
v_x_boxed_4183_ = lean_unbox(v_x_4182_);
v_res_4184_ = l_Lean_Lsp_MarkupKind_ctorIdx(v_x_boxed_4183_);
return v_res_4184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MarkupKind_toCtorIdx(uint8_t v_x_4185_){
_start:
{
lean_object* v___x_4186_; 
v___x_4186_ = l_Lean_Lsp_MarkupKind_ctorIdx(v_x_4185_);
return v___x_4186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MarkupKind_toCtorIdx___boxed(lean_object* v_x_4187_){
_start:
{
uint8_t v_x_4__boxed_4188_; lean_object* v_res_4189_; 
v_x_4__boxed_4188_ = lean_unbox(v_x_4187_);
v_res_4189_ = l_Lean_Lsp_MarkupKind_toCtorIdx(v_x_4__boxed_4188_);
return v_res_4189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MarkupKind_ctorElim___redArg(lean_object* v_k_4190_){
_start:
{
lean_inc(v_k_4190_);
return v_k_4190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MarkupKind_ctorElim___redArg___boxed(lean_object* v_k_4191_){
_start:
{
lean_object* v_res_4192_; 
v_res_4192_ = l_Lean_Lsp_MarkupKind_ctorElim___redArg(v_k_4191_);
lean_dec(v_k_4191_);
return v_res_4192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MarkupKind_ctorElim(lean_object* v_motive_4193_, lean_object* v_ctorIdx_4194_, uint8_t v_t_4195_, lean_object* v_h_4196_, lean_object* v_k_4197_){
_start:
{
lean_inc(v_k_4197_);
return v_k_4197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MarkupKind_ctorElim___boxed(lean_object* v_motive_4198_, lean_object* v_ctorIdx_4199_, lean_object* v_t_4200_, lean_object* v_h_4201_, lean_object* v_k_4202_){
_start:
{
uint8_t v_t_boxed_4203_; lean_object* v_res_4204_; 
v_t_boxed_4203_ = lean_unbox(v_t_4200_);
v_res_4204_ = l_Lean_Lsp_MarkupKind_ctorElim(v_motive_4198_, v_ctorIdx_4199_, v_t_boxed_4203_, v_h_4201_, v_k_4202_);
lean_dec(v_k_4202_);
lean_dec(v_ctorIdx_4199_);
return v_res_4204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MarkupKind_plaintext_elim___redArg(lean_object* v_plaintext_4205_){
_start:
{
lean_inc(v_plaintext_4205_);
return v_plaintext_4205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MarkupKind_plaintext_elim___redArg___boxed(lean_object* v_plaintext_4206_){
_start:
{
lean_object* v_res_4207_; 
v_res_4207_ = l_Lean_Lsp_MarkupKind_plaintext_elim___redArg(v_plaintext_4206_);
lean_dec(v_plaintext_4206_);
return v_res_4207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MarkupKind_plaintext_elim(lean_object* v_motive_4208_, uint8_t v_t_4209_, lean_object* v_h_4210_, lean_object* v_plaintext_4211_){
_start:
{
lean_inc(v_plaintext_4211_);
return v_plaintext_4211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MarkupKind_plaintext_elim___boxed(lean_object* v_motive_4212_, lean_object* v_t_4213_, lean_object* v_h_4214_, lean_object* v_plaintext_4215_){
_start:
{
uint8_t v_t_boxed_4216_; lean_object* v_res_4217_; 
v_t_boxed_4216_ = lean_unbox(v_t_4213_);
v_res_4217_ = l_Lean_Lsp_MarkupKind_plaintext_elim(v_motive_4212_, v_t_boxed_4216_, v_h_4214_, v_plaintext_4215_);
lean_dec(v_plaintext_4215_);
return v_res_4217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MarkupKind_markdown_elim___redArg(lean_object* v_markdown_4218_){
_start:
{
lean_inc(v_markdown_4218_);
return v_markdown_4218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MarkupKind_markdown_elim___redArg___boxed(lean_object* v_markdown_4219_){
_start:
{
lean_object* v_res_4220_; 
v_res_4220_ = l_Lean_Lsp_MarkupKind_markdown_elim___redArg(v_markdown_4219_);
lean_dec(v_markdown_4219_);
return v_res_4220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MarkupKind_markdown_elim(lean_object* v_motive_4221_, uint8_t v_t_4222_, lean_object* v_h_4223_, lean_object* v_markdown_4224_){
_start:
{
lean_inc(v_markdown_4224_);
return v_markdown_4224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MarkupKind_markdown_elim___boxed(lean_object* v_motive_4225_, lean_object* v_t_4226_, lean_object* v_h_4227_, lean_object* v_markdown_4228_){
_start:
{
uint8_t v_t_boxed_4229_; lean_object* v_res_4230_; 
v_t_boxed_4229_ = lean_unbox(v_t_4226_);
v_res_4230_ = l_Lean_Lsp_MarkupKind_markdown_elim(v_motive_4225_, v_t_boxed_4229_, v_h_4227_, v_markdown_4228_);
lean_dec(v_markdown_4228_);
return v_res_4230_;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_MarkupKind_ofNat(lean_object* v_n_4231_){
_start:
{
lean_object* v___x_4232_; uint8_t v___x_4233_; 
v___x_4232_ = lean_unsigned_to_nat(0u);
v___x_4233_ = lean_nat_dec_le(v_n_4231_, v___x_4232_);
if (v___x_4233_ == 0)
{
uint8_t v___x_4234_; 
v___x_4234_ = 1;
return v___x_4234_;
}
else
{
uint8_t v___x_4235_; 
v___x_4235_ = 0;
return v___x_4235_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MarkupKind_ofNat___boxed(lean_object* v_n_4236_){
_start:
{
uint8_t v_res_4237_; lean_object* v_r_4238_; 
v_res_4237_ = l_Lean_Lsp_MarkupKind_ofNat(v_n_4236_);
lean_dec(v_n_4236_);
v_r_4238_ = lean_box(v_res_4237_);
return v_r_4238_;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_instDecidableEqMarkupKind(uint8_t v_x_4239_, uint8_t v_y_4240_){
_start:
{
lean_object* v___x_4241_; lean_object* v___x_4242_; uint8_t v___x_4243_; 
v___x_4241_ = l_Lean_Lsp_MarkupKind_ctorIdx(v_x_4239_);
v___x_4242_ = l_Lean_Lsp_MarkupKind_ctorIdx(v_y_4240_);
v___x_4243_ = lean_nat_dec_eq(v___x_4241_, v___x_4242_);
lean_dec(v___x_4242_);
lean_dec(v___x_4241_);
return v___x_4243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instDecidableEqMarkupKind___boxed(lean_object* v_x_4244_, lean_object* v_y_4245_){
_start:
{
uint8_t v_x_13__boxed_4246_; uint8_t v_y_14__boxed_4247_; uint8_t v_res_4248_; lean_object* v_r_4249_; 
v_x_13__boxed_4246_ = lean_unbox(v_x_4244_);
v_y_14__boxed_4247_ = lean_unbox(v_y_4245_);
v_res_4248_ = l_Lean_Lsp_instDecidableEqMarkupKind(v_x_13__boxed_4246_, v_y_14__boxed_4247_);
v_r_4249_ = lean_box(v_res_4248_);
return v_r_4249_;
}
}
LEAN_EXPORT uint64_t l_Lean_Lsp_instHashableMarkupKind_hash(uint8_t v_x_4250_){
_start:
{
if (v_x_4250_ == 0)
{
uint64_t v___x_4251_; 
v___x_4251_ = 0ULL;
return v___x_4251_;
}
else
{
uint64_t v___x_4252_; 
v___x_4252_ = 1ULL;
return v___x_4252_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instHashableMarkupKind_hash___boxed(lean_object* v_x_4253_){
_start:
{
uint8_t v_x_28__boxed_4254_; uint64_t v_res_4255_; lean_object* v_r_4256_; 
v_x_28__boxed_4254_ = lean_unbox(v_x_4253_);
v_res_4255_ = l_Lean_Lsp_instHashableMarkupKind_hash(v_x_28__boxed_4254_);
v_r_4256_ = lean_box_uint64(v_res_4255_);
return v_r_4256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonMarkupKind___lam__0(lean_object* v_x_4270_){
_start:
{
if (lean_obj_tag(v_x_4270_) == 3)
{
lean_object* v_s_4273_; lean_object* v___x_4274_; uint8_t v___x_4275_; 
v_s_4273_ = lean_ctor_get(v_x_4270_, 0);
v___x_4274_ = ((lean_object*)(l_Lean_Lsp_instFromJsonMarkupKind___lam__0___closed__2));
v___x_4275_ = lean_string_dec_eq(v_s_4273_, v___x_4274_);
if (v___x_4275_ == 0)
{
lean_object* v___x_4276_; uint8_t v___x_4277_; 
v___x_4276_ = ((lean_object*)(l_Lean_Lsp_instFromJsonMarkupKind___lam__0___closed__3));
v___x_4277_ = lean_string_dec_eq(v_s_4273_, v___x_4276_);
if (v___x_4277_ == 0)
{
goto v___jp_4271_;
}
else
{
lean_object* v___x_4278_; 
v___x_4278_ = ((lean_object*)(l_Lean_Lsp_instFromJsonMarkupKind___lam__0___closed__4));
return v___x_4278_;
}
}
else
{
lean_object* v___x_4279_; 
v___x_4279_ = ((lean_object*)(l_Lean_Lsp_instFromJsonMarkupKind___lam__0___closed__5));
return v___x_4279_;
}
}
else
{
goto v___jp_4271_;
}
v___jp_4271_:
{
lean_object* v___x_4272_; 
v___x_4272_ = ((lean_object*)(l_Lean_Lsp_instFromJsonMarkupKind___lam__0___closed__1));
return v___x_4272_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonMarkupKind___lam__0___boxed(lean_object* v_x_4280_){
_start:
{
lean_object* v_res_4281_; 
v_res_4281_ = l_Lean_Lsp_instFromJsonMarkupKind___lam__0(v_x_4280_);
lean_dec(v_x_4280_);
return v_res_4281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonMarkupKind___lam__0(uint8_t v_x_4288_){
_start:
{
if (v_x_4288_ == 0)
{
lean_object* v___x_4289_; 
v___x_4289_ = ((lean_object*)(l_Lean_Lsp_instToJsonMarkupKind___lam__0___closed__0));
return v___x_4289_;
}
else
{
lean_object* v___x_4290_; 
v___x_4290_ = ((lean_object*)(l_Lean_Lsp_instToJsonMarkupKind___lam__0___closed__1));
return v___x_4290_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonMarkupKind___lam__0___boxed(lean_object* v_x_4291_){
_start:
{
uint8_t v_x_38__boxed_4292_; lean_object* v_res_4293_; 
v_x_38__boxed_4292_ = lean_unbox(v_x_4291_);
v_res_4293_ = l_Lean_Lsp_instToJsonMarkupKind___lam__0(v_x_38__boxed_4292_);
return v_res_4293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonMarkupContent_toJson(lean_object* v_x_4296_){
_start:
{
uint8_t v_kind_4297_; lean_object* v_value_4298_; lean_object* v___x_4299_; lean_object* v___y_4301_; 
v_kind_4297_ = lean_ctor_get_uint8(v_x_4296_, sizeof(void*)*1);
v_value_4298_ = lean_ctor_get(v_x_4296_, 0);
v___x_4299_ = ((lean_object*)(l_Lean_Lsp_instToJsonDocumentChange___lam__0___closed__0));
if (v_kind_4297_ == 0)
{
lean_object* v___x_4314_; 
v___x_4314_ = ((lean_object*)(l_Lean_Lsp_instToJsonMarkupKind___lam__0___closed__0));
v___y_4301_ = v___x_4314_;
goto v___jp_4300_;
}
else
{
lean_object* v___x_4315_; 
v___x_4315_ = ((lean_object*)(l_Lean_Lsp_instToJsonMarkupKind___lam__0___closed__1));
v___y_4301_ = v___x_4315_;
goto v___jp_4300_;
}
v___jp_4300_:
{
lean_object* v___x_4302_; lean_object* v___x_4303_; lean_object* v___x_4304_; lean_object* v___x_4305_; lean_object* v___x_4306_; lean_object* v___x_4307_; lean_object* v___x_4308_; lean_object* v___x_4309_; lean_object* v___x_4310_; lean_object* v___x_4311_; lean_object* v___x_4312_; lean_object* v___x_4313_; 
lean_inc(v___y_4301_);
v___x_4302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4302_, 0, v___x_4299_);
lean_ctor_set(v___x_4302_, 1, v___y_4301_);
v___x_4303_ = lean_box(0);
v___x_4304_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4304_, 0, v___x_4302_);
lean_ctor_set(v___x_4304_, 1, v___x_4303_);
v___x_4305_ = ((lean_object*)(l_Lean_Lsp_instToJsonSnippetString_toJson___closed__0));
lean_inc_ref(v_value_4298_);
v___x_4306_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4306_, 0, v_value_4298_);
v___x_4307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4307_, 0, v___x_4305_);
lean_ctor_set(v___x_4307_, 1, v___x_4306_);
v___x_4308_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4308_, 0, v___x_4307_);
lean_ctor_set(v___x_4308_, 1, v___x_4303_);
v___x_4309_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4309_, 0, v___x_4308_);
lean_ctor_set(v___x_4309_, 1, v___x_4303_);
v___x_4310_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4310_, 0, v___x_4304_);
lean_ctor_set(v___x_4310_, 1, v___x_4309_);
v___x_4311_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__2));
v___x_4312_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLocation_toJson_spec__0(v___x_4310_, v___x_4311_);
v___x_4313_ = l_Lean_Json_mkObj(v___x_4312_);
lean_dec(v___x_4312_);
return v___x_4313_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonMarkupContent_toJson___boxed(lean_object* v_x_4316_){
_start:
{
lean_object* v_res_4317_; 
v_res_4317_ = l_Lean_Lsp_instToJsonMarkupContent_toJson(v_x_4316_);
lean_dec_ref(v_x_4316_);
return v_res_4317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonMarkupContent_fromJson_spec__0(lean_object* v_j_4320_, lean_object* v_k_4321_){
_start:
{
lean_object* v___x_4324_; 
v___x_4324_ = l_Lean_Json_getObjValD(v_j_4320_, v_k_4321_);
if (lean_obj_tag(v___x_4324_) == 3)
{
lean_object* v_s_4325_; lean_object* v___x_4326_; uint8_t v___x_4327_; 
v_s_4325_ = lean_ctor_get(v___x_4324_, 0);
lean_inc_ref(v_s_4325_);
lean_dec_ref_known(v___x_4324_, 1);
v___x_4326_ = ((lean_object*)(l_Lean_Lsp_instFromJsonMarkupKind___lam__0___closed__2));
v___x_4327_ = lean_string_dec_eq(v_s_4325_, v___x_4326_);
if (v___x_4327_ == 0)
{
lean_object* v___x_4328_; uint8_t v___x_4329_; 
v___x_4328_ = ((lean_object*)(l_Lean_Lsp_instFromJsonMarkupKind___lam__0___closed__3));
v___x_4329_ = lean_string_dec_eq(v_s_4325_, v___x_4328_);
lean_dec_ref(v_s_4325_);
if (v___x_4329_ == 0)
{
goto v___jp_4322_;
}
else
{
lean_object* v___x_4330_; 
v___x_4330_ = ((lean_object*)(l_Lean_Lsp_instFromJsonMarkupKind___lam__0___closed__4));
return v___x_4330_;
}
}
else
{
lean_object* v___x_4331_; 
lean_dec_ref(v_s_4325_);
v___x_4331_ = ((lean_object*)(l_Lean_Lsp_instFromJsonMarkupKind___lam__0___closed__5));
return v___x_4331_;
}
}
else
{
lean_dec(v___x_4324_);
goto v___jp_4322_;
}
v___jp_4322_:
{
lean_object* v___x_4323_; 
v___x_4323_ = ((lean_object*)(l_Lean_Lsp_instFromJsonMarkupKind___lam__0___closed__1));
return v___x_4323_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonMarkupContent_fromJson_spec__0___boxed(lean_object* v_j_4332_, lean_object* v_k_4333_){
_start:
{
lean_object* v_res_4334_; 
v_res_4334_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonMarkupContent_fromJson_spec__0(v_j_4332_, v_k_4333_);
lean_dec_ref(v_k_4333_);
return v_res_4334_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__2(void){
_start:
{
uint8_t v___x_4340_; lean_object* v___x_4341_; lean_object* v___x_4342_; 
v___x_4340_ = 1;
v___x_4341_ = ((lean_object*)(l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__1));
v___x_4342_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4341_, v___x_4340_);
return v___x_4342_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__3(void){
_start:
{
lean_object* v___x_4343_; lean_object* v___x_4344_; lean_object* v___x_4345_; 
v___x_4343_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__5));
v___x_4344_ = lean_obj_once(&l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__2, &l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__2);
v___x_4345_ = lean_string_append(v___x_4344_, v___x_4343_);
return v___x_4345_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__5(void){
_start:
{
uint8_t v___x_4348_; lean_object* v___x_4349_; lean_object* v___x_4350_; 
v___x_4348_ = 1;
v___x_4349_ = ((lean_object*)(l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__4));
v___x_4350_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4349_, v___x_4348_);
return v___x_4350_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__6(void){
_start:
{
lean_object* v___x_4351_; lean_object* v___x_4352_; lean_object* v___x_4353_; 
v___x_4351_ = lean_obj_once(&l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__5, &l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__5);
v___x_4352_ = lean_obj_once(&l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__3, &l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__3);
v___x_4353_ = lean_string_append(v___x_4352_, v___x_4351_);
return v___x_4353_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__7(void){
_start:
{
lean_object* v___x_4354_; lean_object* v___x_4355_; lean_object* v___x_4356_; 
v___x_4354_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_4355_ = lean_obj_once(&l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__6, &l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__6);
v___x_4356_ = lean_string_append(v___x_4355_, v___x_4354_);
return v___x_4356_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__8(void){
_start:
{
lean_object* v___x_4357_; lean_object* v___x_4358_; lean_object* v___x_4359_; 
v___x_4357_ = lean_obj_once(&l_Lean_Lsp_instFromJsonSnippetString_fromJson___closed__5, &l_Lean_Lsp_instFromJsonSnippetString_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonSnippetString_fromJson___closed__5);
v___x_4358_ = lean_obj_once(&l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__3, &l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__3);
v___x_4359_ = lean_string_append(v___x_4358_, v___x_4357_);
return v___x_4359_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__9(void){
_start:
{
lean_object* v___x_4360_; lean_object* v___x_4361_; lean_object* v___x_4362_; 
v___x_4360_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_4361_ = lean_obj_once(&l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__8, &l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__8);
v___x_4362_ = lean_string_append(v___x_4361_, v___x_4360_);
return v___x_4362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonMarkupContent_fromJson(lean_object* v_json_4363_){
_start:
{
lean_object* v___x_4364_; lean_object* v___x_4365_; 
v___x_4364_ = ((lean_object*)(l_Lean_Lsp_instToJsonDocumentChange___lam__0___closed__0));
lean_inc(v_json_4363_);
v___x_4365_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonMarkupContent_fromJson_spec__0(v_json_4363_, v___x_4364_);
if (lean_obj_tag(v___x_4365_) == 0)
{
lean_object* v_a_4366_; lean_object* v___x_4368_; uint8_t v_isShared_4369_; uint8_t v_isSharedCheck_4375_; 
lean_dec(v_json_4363_);
v_a_4366_ = lean_ctor_get(v___x_4365_, 0);
v_isSharedCheck_4375_ = !lean_is_exclusive(v___x_4365_);
if (v_isSharedCheck_4375_ == 0)
{
v___x_4368_ = v___x_4365_;
v_isShared_4369_ = v_isSharedCheck_4375_;
goto v_resetjp_4367_;
}
else
{
lean_inc(v_a_4366_);
lean_dec(v___x_4365_);
v___x_4368_ = lean_box(0);
v_isShared_4369_ = v_isSharedCheck_4375_;
goto v_resetjp_4367_;
}
v_resetjp_4367_:
{
lean_object* v___x_4370_; lean_object* v___x_4371_; lean_object* v___x_4373_; 
v___x_4370_ = lean_obj_once(&l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__7, &l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__7);
v___x_4371_ = lean_string_append(v___x_4370_, v_a_4366_);
lean_dec(v_a_4366_);
if (v_isShared_4369_ == 0)
{
lean_ctor_set(v___x_4368_, 0, v___x_4371_);
v___x_4373_ = v___x_4368_;
goto v_reusejp_4372_;
}
else
{
lean_object* v_reuseFailAlloc_4374_; 
v_reuseFailAlloc_4374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4374_, 0, v___x_4371_);
v___x_4373_ = v_reuseFailAlloc_4374_;
goto v_reusejp_4372_;
}
v_reusejp_4372_:
{
return v___x_4373_;
}
}
}
else
{
if (lean_obj_tag(v___x_4365_) == 0)
{
lean_object* v_a_4376_; lean_object* v___x_4378_; uint8_t v_isShared_4379_; uint8_t v_isSharedCheck_4383_; 
lean_dec(v_json_4363_);
v_a_4376_ = lean_ctor_get(v___x_4365_, 0);
v_isSharedCheck_4383_ = !lean_is_exclusive(v___x_4365_);
if (v_isSharedCheck_4383_ == 0)
{
v___x_4378_ = v___x_4365_;
v_isShared_4379_ = v_isSharedCheck_4383_;
goto v_resetjp_4377_;
}
else
{
lean_inc(v_a_4376_);
lean_dec(v___x_4365_);
v___x_4378_ = lean_box(0);
v_isShared_4379_ = v_isSharedCheck_4383_;
goto v_resetjp_4377_;
}
v_resetjp_4377_:
{
lean_object* v___x_4381_; 
if (v_isShared_4379_ == 0)
{
lean_ctor_set_tag(v___x_4378_, 0);
v___x_4381_ = v___x_4378_;
goto v_reusejp_4380_;
}
else
{
lean_object* v_reuseFailAlloc_4382_; 
v_reuseFailAlloc_4382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4382_, 0, v_a_4376_);
v___x_4381_ = v_reuseFailAlloc_4382_;
goto v_reusejp_4380_;
}
v_reusejp_4380_:
{
return v___x_4381_;
}
}
}
else
{
lean_object* v_a_4384_; lean_object* v___x_4385_; lean_object* v___x_4386_; 
v_a_4384_ = lean_ctor_get(v___x_4365_, 0);
lean_inc(v_a_4384_);
lean_dec_ref_known(v___x_4365_, 1);
v___x_4385_ = ((lean_object*)(l_Lean_Lsp_instToJsonSnippetString_toJson___closed__0));
v___x_4386_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocation_fromJson_spec__0(v_json_4363_, v___x_4385_);
if (lean_obj_tag(v___x_4386_) == 0)
{
lean_object* v_a_4387_; lean_object* v___x_4389_; uint8_t v_isShared_4390_; uint8_t v_isSharedCheck_4396_; 
lean_dec(v_a_4384_);
v_a_4387_ = lean_ctor_get(v___x_4386_, 0);
v_isSharedCheck_4396_ = !lean_is_exclusive(v___x_4386_);
if (v_isSharedCheck_4396_ == 0)
{
v___x_4389_ = v___x_4386_;
v_isShared_4390_ = v_isSharedCheck_4396_;
goto v_resetjp_4388_;
}
else
{
lean_inc(v_a_4387_);
lean_dec(v___x_4386_);
v___x_4389_ = lean_box(0);
v_isShared_4390_ = v_isSharedCheck_4396_;
goto v_resetjp_4388_;
}
v_resetjp_4388_:
{
lean_object* v___x_4391_; lean_object* v___x_4392_; lean_object* v___x_4394_; 
v___x_4391_ = lean_obj_once(&l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__9, &l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__9);
v___x_4392_ = lean_string_append(v___x_4391_, v_a_4387_);
lean_dec(v_a_4387_);
if (v_isShared_4390_ == 0)
{
lean_ctor_set(v___x_4389_, 0, v___x_4392_);
v___x_4394_ = v___x_4389_;
goto v_reusejp_4393_;
}
else
{
lean_object* v_reuseFailAlloc_4395_; 
v_reuseFailAlloc_4395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4395_, 0, v___x_4392_);
v___x_4394_ = v_reuseFailAlloc_4395_;
goto v_reusejp_4393_;
}
v_reusejp_4393_:
{
return v___x_4394_;
}
}
}
else
{
if (lean_obj_tag(v___x_4386_) == 0)
{
lean_object* v_a_4397_; lean_object* v___x_4399_; uint8_t v_isShared_4400_; uint8_t v_isSharedCheck_4404_; 
lean_dec(v_a_4384_);
v_a_4397_ = lean_ctor_get(v___x_4386_, 0);
v_isSharedCheck_4404_ = !lean_is_exclusive(v___x_4386_);
if (v_isSharedCheck_4404_ == 0)
{
v___x_4399_ = v___x_4386_;
v_isShared_4400_ = v_isSharedCheck_4404_;
goto v_resetjp_4398_;
}
else
{
lean_inc(v_a_4397_);
lean_dec(v___x_4386_);
v___x_4399_ = lean_box(0);
v_isShared_4400_ = v_isSharedCheck_4404_;
goto v_resetjp_4398_;
}
v_resetjp_4398_:
{
lean_object* v___x_4402_; 
if (v_isShared_4400_ == 0)
{
lean_ctor_set_tag(v___x_4399_, 0);
v___x_4402_ = v___x_4399_;
goto v_reusejp_4401_;
}
else
{
lean_object* v_reuseFailAlloc_4403_; 
v_reuseFailAlloc_4403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4403_, 0, v_a_4397_);
v___x_4402_ = v_reuseFailAlloc_4403_;
goto v_reusejp_4401_;
}
v_reusejp_4401_:
{
return v___x_4402_;
}
}
}
else
{
lean_object* v_a_4405_; lean_object* v___x_4407_; uint8_t v_isShared_4408_; uint8_t v_isSharedCheck_4414_; 
v_a_4405_ = lean_ctor_get(v___x_4386_, 0);
v_isSharedCheck_4414_ = !lean_is_exclusive(v___x_4386_);
if (v_isSharedCheck_4414_ == 0)
{
v___x_4407_ = v___x_4386_;
v_isShared_4408_ = v_isSharedCheck_4414_;
goto v_resetjp_4406_;
}
else
{
lean_inc(v_a_4405_);
lean_dec(v___x_4386_);
v___x_4407_ = lean_box(0);
v_isShared_4408_ = v_isSharedCheck_4414_;
goto v_resetjp_4406_;
}
v_resetjp_4406_:
{
lean_object* v___x_4409_; uint8_t v___x_4410_; lean_object* v___x_4412_; 
v___x_4409_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4409_, 0, v_a_4405_);
v___x_4410_ = lean_unbox(v_a_4384_);
lean_dec(v_a_4384_);
lean_ctor_set_uint8(v___x_4409_, sizeof(void*)*1, v___x_4410_);
if (v_isShared_4408_ == 0)
{
lean_ctor_set(v___x_4407_, 0, v___x_4409_);
v___x_4412_ = v___x_4407_;
goto v_reusejp_4411_;
}
else
{
lean_object* v_reuseFailAlloc_4413_; 
v_reuseFailAlloc_4413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4413_, 0, v___x_4409_);
v___x_4412_ = v_reuseFailAlloc_4413_;
goto v_reusejp_4411_;
}
v_reusejp_4411_:
{
return v___x_4412_;
}
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_instDecidableEqMarkupContent_decEq(lean_object* v_x_4417_, lean_object* v_x_4418_){
_start:
{
uint8_t v_kind_4419_; lean_object* v_value_4420_; uint8_t v_kind_4421_; lean_object* v_value_4422_; uint8_t v___x_4423_; 
v_kind_4419_ = lean_ctor_get_uint8(v_x_4417_, sizeof(void*)*1);
v_value_4420_ = lean_ctor_get(v_x_4417_, 0);
v_kind_4421_ = lean_ctor_get_uint8(v_x_4418_, sizeof(void*)*1);
v_value_4422_ = lean_ctor_get(v_x_4418_, 0);
v___x_4423_ = l_Lean_Lsp_instDecidableEqMarkupKind(v_kind_4419_, v_kind_4421_);
if (v___x_4423_ == 0)
{
return v___x_4423_;
}
else
{
uint8_t v___x_4424_; 
v___x_4424_ = lean_string_dec_eq(v_value_4420_, v_value_4422_);
return v___x_4424_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instDecidableEqMarkupContent_decEq___boxed(lean_object* v_x_4425_, lean_object* v_x_4426_){
_start:
{
uint8_t v_res_4427_; lean_object* v_r_4428_; 
v_res_4427_ = l_Lean_Lsp_instDecidableEqMarkupContent_decEq(v_x_4425_, v_x_4426_);
lean_dec_ref(v_x_4426_);
lean_dec_ref(v_x_4425_);
v_r_4428_ = lean_box(v_res_4427_);
return v_r_4428_;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_instDecidableEqMarkupContent(lean_object* v_x_4429_, lean_object* v_x_4430_){
_start:
{
uint8_t v___x_4431_; 
v___x_4431_ = l_Lean_Lsp_instDecidableEqMarkupContent_decEq(v_x_4429_, v_x_4430_);
return v___x_4431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instDecidableEqMarkupContent___boxed(lean_object* v_x_4432_, lean_object* v_x_4433_){
_start:
{
uint8_t v_res_4434_; lean_object* v_r_4435_; 
v_res_4434_ = l_Lean_Lsp_instDecidableEqMarkupContent(v_x_4432_, v_x_4433_);
lean_dec_ref(v_x_4433_);
lean_dec_ref(v_x_4432_);
v_r_4435_ = lean_box(v_res_4434_);
return v_r_4435_;
}
}
LEAN_EXPORT uint64_t l_Lean_Lsp_instHashableMarkupContent_hash(lean_object* v_x_4436_){
_start:
{
uint8_t v_kind_4437_; lean_object* v_value_4438_; uint64_t v___x_4439_; uint64_t v___x_4440_; uint64_t v___x_4441_; uint64_t v___x_4442_; uint64_t v___x_4443_; 
v_kind_4437_ = lean_ctor_get_uint8(v_x_4436_, sizeof(void*)*1);
v_value_4438_ = lean_ctor_get(v_x_4436_, 0);
v___x_4439_ = 0ULL;
v___x_4440_ = l_Lean_Lsp_instHashableMarkupKind_hash(v_kind_4437_);
v___x_4441_ = lean_uint64_mix_hash(v___x_4439_, v___x_4440_);
v___x_4442_ = lean_string_hash(v_value_4438_);
v___x_4443_ = lean_uint64_mix_hash(v___x_4441_, v___x_4442_);
return v___x_4443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instHashableMarkupContent_hash___boxed(lean_object* v_x_4444_){
_start:
{
uint64_t v_res_4445_; lean_object* v_r_4446_; 
v_res_4445_ = l_Lean_Lsp_instHashableMarkupContent_hash(v_x_4444_);
lean_dec_ref(v_x_4444_);
v_r_4446_ = lean_box_uint64(v_res_4445_);
return v_r_4446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonProgressParams_toJson___redArg(lean_object* v_inst_4451_, lean_object* v_x_4452_){
_start:
{
lean_object* v_token_4453_; lean_object* v_value_4454_; lean_object* v___x_4456_; uint8_t v_isShared_4457_; uint8_t v_isSharedCheck_4475_; 
v_token_4453_ = lean_ctor_get(v_x_4452_, 0);
v_value_4454_ = lean_ctor_get(v_x_4452_, 1);
v_isSharedCheck_4475_ = !lean_is_exclusive(v_x_4452_);
if (v_isSharedCheck_4475_ == 0)
{
v___x_4456_ = v_x_4452_;
v_isShared_4457_ = v_isSharedCheck_4475_;
goto v_resetjp_4455_;
}
else
{
lean_inc(v_value_4454_);
lean_inc(v_token_4453_);
lean_dec(v_x_4452_);
v___x_4456_ = lean_box(0);
v_isShared_4457_ = v_isSharedCheck_4475_;
goto v_resetjp_4455_;
}
v_resetjp_4455_:
{
lean_object* v___x_4458_; lean_object* v___x_4459_; lean_object* v___x_4461_; 
v___x_4458_ = ((lean_object*)(l_Lean_Lsp_instToJsonProgressParams_toJson___redArg___closed__0));
v___x_4459_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4459_, 0, v_token_4453_);
if (v_isShared_4457_ == 0)
{
lean_ctor_set(v___x_4456_, 1, v___x_4459_);
lean_ctor_set(v___x_4456_, 0, v___x_4458_);
v___x_4461_ = v___x_4456_;
goto v_reusejp_4460_;
}
else
{
lean_object* v_reuseFailAlloc_4474_; 
v_reuseFailAlloc_4474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4474_, 0, v___x_4458_);
lean_ctor_set(v_reuseFailAlloc_4474_, 1, v___x_4459_);
v___x_4461_ = v_reuseFailAlloc_4474_;
goto v_reusejp_4460_;
}
v_reusejp_4460_:
{
lean_object* v___x_4462_; lean_object* v___x_4463_; lean_object* v___x_4464_; lean_object* v___x_4465_; lean_object* v___x_4466_; lean_object* v___x_4467_; lean_object* v___x_4468_; lean_object* v___x_4469_; lean_object* v___x_4470_; lean_object* v___x_4471_; lean_object* v___x_4472_; lean_object* v___x_4473_; 
v___x_4462_ = lean_box(0);
v___x_4463_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4463_, 0, v___x_4461_);
lean_ctor_set(v___x_4463_, 1, v___x_4462_);
v___x_4464_ = ((lean_object*)(l_Lean_Lsp_instToJsonSnippetString_toJson___closed__0));
v___x_4465_ = lean_apply_1(v_inst_4451_, v_value_4454_);
v___x_4466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4466_, 0, v___x_4464_);
lean_ctor_set(v___x_4466_, 1, v___x_4465_);
v___x_4467_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4467_, 0, v___x_4466_);
lean_ctor_set(v___x_4467_, 1, v___x_4462_);
v___x_4468_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4468_, 0, v___x_4467_);
lean_ctor_set(v___x_4468_, 1, v___x_4462_);
v___x_4469_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4469_, 0, v___x_4463_);
lean_ctor_set(v___x_4469_, 1, v___x_4468_);
v___x_4470_ = ((lean_object*)(l_Lean_Lsp_instToJsonProgressParams_toJson___redArg___closed__1));
v___x_4471_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__2));
v___x_4472_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go(lean_box(0), lean_box(0), v___x_4470_, v___x_4469_, v___x_4471_);
v___x_4473_ = l_Lean_Json_mkObj(v___x_4472_);
lean_dec(v___x_4472_);
return v___x_4473_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonProgressParams_toJson(lean_object* v_00_u03b1_4476_, lean_object* v_inst_4477_, lean_object* v_x_4478_){
_start:
{
lean_object* v___x_4479_; 
v___x_4479_ = l_Lean_Lsp_instToJsonProgressParams_toJson___redArg(v_inst_4477_, v_x_4478_);
return v___x_4479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonProgressParams___redArg(lean_object* v_inst_4480_){
_start:
{
lean_object* v___x_4481_; 
v___x_4481_ = lean_alloc_closure((void*)(l_Lean_Lsp_instToJsonProgressParams_toJson), 3, 2);
lean_closure_set(v___x_4481_, 0, lean_box(0));
lean_closure_set(v___x_4481_, 1, v_inst_4480_);
return v___x_4481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonProgressParams(lean_object* v_00_u03b1_4482_, lean_object* v_inst_4483_){
_start:
{
lean_object* v___x_4484_; 
v___x_4484_ = lean_alloc_closure((void*)(l_Lean_Lsp_instToJsonProgressParams_toJson), 3, 2);
lean_closure_set(v___x_4484_, 0, lean_box(0));
lean_closure_set(v___x_4484_, 1, v_inst_4483_);
return v___x_4484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonWorkDoneProgressReport_toJson(lean_object* v_x_4488_){
_start:
{
lean_object* v_kind_4489_; lean_object* v_message_x3f_4490_; uint8_t v_cancellable_4491_; lean_object* v_percentage_x3f_4492_; lean_object* v___x_4493_; lean_object* v___x_4494_; lean_object* v___x_4495_; lean_object* v___x_4496_; lean_object* v___x_4497_; lean_object* v___x_4498_; lean_object* v___x_4499_; lean_object* v___x_4500_; lean_object* v___x_4501_; lean_object* v___x_4502_; lean_object* v___x_4503_; lean_object* v___x_4504_; lean_object* v___x_4505_; lean_object* v___x_4506_; lean_object* v___x_4507_; lean_object* v___x_4508_; lean_object* v___x_4509_; lean_object* v___x_4510_; lean_object* v___x_4511_; lean_object* v___x_4512_; 
v_kind_4489_ = lean_ctor_get(v_x_4488_, 0);
lean_inc_ref(v_kind_4489_);
v_message_x3f_4490_ = lean_ctor_get(v_x_4488_, 1);
lean_inc(v_message_x3f_4490_);
v_cancellable_4491_ = lean_ctor_get_uint8(v_x_4488_, sizeof(void*)*3);
v_percentage_x3f_4492_ = lean_ctor_get(v_x_4488_, 2);
lean_inc(v_percentage_x3f_4492_);
lean_dec_ref(v_x_4488_);
v___x_4493_ = ((lean_object*)(l_Lean_Lsp_instToJsonDocumentChange___lam__0___closed__0));
v___x_4494_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4494_, 0, v_kind_4489_);
v___x_4495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4495_, 0, v___x_4493_);
lean_ctor_set(v___x_4495_, 1, v___x_4494_);
v___x_4496_ = lean_box(0);
v___x_4497_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4497_, 0, v___x_4495_);
lean_ctor_set(v___x_4497_, 1, v___x_4496_);
v___x_4498_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkDoneProgressReport_toJson___closed__0));
v___x_4499_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextEdit_toJson_spec__1(v___x_4498_, v_message_x3f_4490_);
v___x_4500_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkDoneProgressReport_toJson___closed__1));
v___x_4501_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_4501_, 0, v_cancellable_4491_);
v___x_4502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4502_, 0, v___x_4500_);
lean_ctor_set(v___x_4502_, 1, v___x_4501_);
v___x_4503_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4503_, 0, v___x_4502_);
lean_ctor_set(v___x_4503_, 1, v___x_4496_);
v___x_4504_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkDoneProgressReport_toJson___closed__2));
v___x_4505_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonVersionedTextDocumentIdentifier_toJson_spec__0(v___x_4504_, v_percentage_x3f_4492_);
v___x_4506_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4506_, 0, v___x_4505_);
lean_ctor_set(v___x_4506_, 1, v___x_4496_);
v___x_4507_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4507_, 0, v___x_4503_);
lean_ctor_set(v___x_4507_, 1, v___x_4506_);
v___x_4508_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4508_, 0, v___x_4499_);
lean_ctor_set(v___x_4508_, 1, v___x_4507_);
v___x_4509_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4509_, 0, v___x_4497_);
lean_ctor_set(v___x_4509_, 1, v___x_4508_);
v___x_4510_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__2));
v___x_4511_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLocation_toJson_spec__0(v___x_4509_, v___x_4510_);
v___x_4512_ = l_Lean_Json_mkObj(v___x_4511_);
lean_dec(v___x_4511_);
return v___x_4512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonWorkDoneProgressBegin_toJson(lean_object* v_x_4515_){
_start:
{
lean_object* v_toWorkDoneProgressReport_4516_; lean_object* v_title_4517_; lean_object* v___x_4519_; uint8_t v_isShared_4520_; uint8_t v_isSharedCheck_4552_; 
v_toWorkDoneProgressReport_4516_ = lean_ctor_get(v_x_4515_, 0);
v_title_4517_ = lean_ctor_get(v_x_4515_, 1);
v_isSharedCheck_4552_ = !lean_is_exclusive(v_x_4515_);
if (v_isSharedCheck_4552_ == 0)
{
v___x_4519_ = v_x_4515_;
v_isShared_4520_ = v_isSharedCheck_4552_;
goto v_resetjp_4518_;
}
else
{
lean_inc(v_title_4517_);
lean_inc(v_toWorkDoneProgressReport_4516_);
lean_dec(v_x_4515_);
v___x_4519_ = lean_box(0);
v_isShared_4520_ = v_isSharedCheck_4552_;
goto v_resetjp_4518_;
}
v_resetjp_4518_:
{
lean_object* v_kind_4521_; lean_object* v_message_x3f_4522_; uint8_t v_cancellable_4523_; lean_object* v_percentage_x3f_4524_; lean_object* v___x_4525_; lean_object* v___x_4526_; lean_object* v___x_4528_; 
v_kind_4521_ = lean_ctor_get(v_toWorkDoneProgressReport_4516_, 0);
lean_inc_ref(v_kind_4521_);
v_message_x3f_4522_ = lean_ctor_get(v_toWorkDoneProgressReport_4516_, 1);
lean_inc(v_message_x3f_4522_);
v_cancellable_4523_ = lean_ctor_get_uint8(v_toWorkDoneProgressReport_4516_, sizeof(void*)*3);
v_percentage_x3f_4524_ = lean_ctor_get(v_toWorkDoneProgressReport_4516_, 2);
lean_inc(v_percentage_x3f_4524_);
lean_dec_ref(v_toWorkDoneProgressReport_4516_);
v___x_4525_ = ((lean_object*)(l_Lean_Lsp_instToJsonDocumentChange___lam__0___closed__0));
v___x_4526_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4526_, 0, v_kind_4521_);
if (v_isShared_4520_ == 0)
{
lean_ctor_set(v___x_4519_, 1, v___x_4526_);
lean_ctor_set(v___x_4519_, 0, v___x_4525_);
v___x_4528_ = v___x_4519_;
goto v_reusejp_4527_;
}
else
{
lean_object* v_reuseFailAlloc_4551_; 
v_reuseFailAlloc_4551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4551_, 0, v___x_4525_);
lean_ctor_set(v_reuseFailAlloc_4551_, 1, v___x_4526_);
v___x_4528_ = v_reuseFailAlloc_4551_;
goto v_reusejp_4527_;
}
v_reusejp_4527_:
{
lean_object* v___x_4529_; lean_object* v___x_4530_; lean_object* v___x_4531_; lean_object* v___x_4532_; lean_object* v___x_4533_; lean_object* v___x_4534_; lean_object* v___x_4535_; lean_object* v___x_4536_; lean_object* v___x_4537_; lean_object* v___x_4538_; lean_object* v___x_4539_; lean_object* v___x_4540_; lean_object* v___x_4541_; lean_object* v___x_4542_; lean_object* v___x_4543_; lean_object* v___x_4544_; lean_object* v___x_4545_; lean_object* v___x_4546_; lean_object* v___x_4547_; lean_object* v___x_4548_; lean_object* v___x_4549_; lean_object* v___x_4550_; 
v___x_4529_ = lean_box(0);
v___x_4530_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4530_, 0, v___x_4528_);
lean_ctor_set(v___x_4530_, 1, v___x_4529_);
v___x_4531_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkDoneProgressReport_toJson___closed__0));
v___x_4532_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextEdit_toJson_spec__1(v___x_4531_, v_message_x3f_4522_);
v___x_4533_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkDoneProgressReport_toJson___closed__1));
v___x_4534_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_4534_, 0, v_cancellable_4523_);
v___x_4535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4535_, 0, v___x_4533_);
lean_ctor_set(v___x_4535_, 1, v___x_4534_);
v___x_4536_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4536_, 0, v___x_4535_);
lean_ctor_set(v___x_4536_, 1, v___x_4529_);
v___x_4537_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkDoneProgressReport_toJson___closed__2));
v___x_4538_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonVersionedTextDocumentIdentifier_toJson_spec__0(v___x_4537_, v_percentage_x3f_4524_);
v___x_4539_ = ((lean_object*)(l_Lean_Lsp_instToJsonCommand_toJson___closed__0));
v___x_4540_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4540_, 0, v_title_4517_);
v___x_4541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4541_, 0, v___x_4539_);
lean_ctor_set(v___x_4541_, 1, v___x_4540_);
v___x_4542_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4542_, 0, v___x_4541_);
lean_ctor_set(v___x_4542_, 1, v___x_4529_);
v___x_4543_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4543_, 0, v___x_4542_);
lean_ctor_set(v___x_4543_, 1, v___x_4529_);
v___x_4544_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4544_, 0, v___x_4538_);
lean_ctor_set(v___x_4544_, 1, v___x_4543_);
v___x_4545_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4545_, 0, v___x_4536_);
lean_ctor_set(v___x_4545_, 1, v___x_4544_);
v___x_4546_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4546_, 0, v___x_4532_);
lean_ctor_set(v___x_4546_, 1, v___x_4545_);
v___x_4547_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4547_, 0, v___x_4530_);
lean_ctor_set(v___x_4547_, 1, v___x_4546_);
v___x_4548_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__2));
v___x_4549_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLocation_toJson_spec__0(v___x_4547_, v___x_4548_);
v___x_4550_ = l_Lean_Json_mkObj(v___x_4549_);
lean_dec(v___x_4549_);
return v___x_4550_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonWorkDoneProgressEnd_toJson(lean_object* v_x_4555_){
_start:
{
lean_object* v_kind_4556_; lean_object* v_message_x3f_4557_; lean_object* v___x_4559_; uint8_t v_isShared_4560_; uint8_t v_isSharedCheck_4575_; 
v_kind_4556_ = lean_ctor_get(v_x_4555_, 0);
v_message_x3f_4557_ = lean_ctor_get(v_x_4555_, 1);
v_isSharedCheck_4575_ = !lean_is_exclusive(v_x_4555_);
if (v_isSharedCheck_4575_ == 0)
{
v___x_4559_ = v_x_4555_;
v_isShared_4560_ = v_isSharedCheck_4575_;
goto v_resetjp_4558_;
}
else
{
lean_inc(v_message_x3f_4557_);
lean_inc(v_kind_4556_);
lean_dec(v_x_4555_);
v___x_4559_ = lean_box(0);
v_isShared_4560_ = v_isSharedCheck_4575_;
goto v_resetjp_4558_;
}
v_resetjp_4558_:
{
lean_object* v___x_4561_; lean_object* v___x_4562_; lean_object* v___x_4564_; 
v___x_4561_ = ((lean_object*)(l_Lean_Lsp_instToJsonDocumentChange___lam__0___closed__0));
v___x_4562_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4562_, 0, v_kind_4556_);
if (v_isShared_4560_ == 0)
{
lean_ctor_set(v___x_4559_, 1, v___x_4562_);
lean_ctor_set(v___x_4559_, 0, v___x_4561_);
v___x_4564_ = v___x_4559_;
goto v_reusejp_4563_;
}
else
{
lean_object* v_reuseFailAlloc_4574_; 
v_reuseFailAlloc_4574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4574_, 0, v___x_4561_);
lean_ctor_set(v_reuseFailAlloc_4574_, 1, v___x_4562_);
v___x_4564_ = v_reuseFailAlloc_4574_;
goto v_reusejp_4563_;
}
v_reusejp_4563_:
{
lean_object* v___x_4565_; lean_object* v___x_4566_; lean_object* v___x_4567_; lean_object* v___x_4568_; lean_object* v___x_4569_; lean_object* v___x_4570_; lean_object* v___x_4571_; lean_object* v___x_4572_; lean_object* v___x_4573_; 
v___x_4565_ = lean_box(0);
v___x_4566_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4566_, 0, v___x_4564_);
lean_ctor_set(v___x_4566_, 1, v___x_4565_);
v___x_4567_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkDoneProgressReport_toJson___closed__0));
v___x_4568_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextEdit_toJson_spec__1(v___x_4567_, v_message_x3f_4557_);
v___x_4569_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4569_, 0, v___x_4568_);
lean_ctor_set(v___x_4569_, 1, v___x_4565_);
v___x_4570_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4570_, 0, v___x_4566_);
lean_ctor_set(v___x_4570_, 1, v___x_4569_);
v___x_4571_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__2));
v___x_4572_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLocation_toJson_spec__0(v___x_4570_, v___x_4571_);
v___x_4573_ = l_Lean_Json_mkObj(v___x_4572_);
lean_dec(v___x_4572_);
return v___x_4573_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonWorkDoneProgressParams_toJson(lean_object* v_x_4579_){
_start:
{
lean_object* v___x_4580_; lean_object* v___x_4581_; lean_object* v___x_4582_; lean_object* v___x_4583_; lean_object* v___x_4584_; lean_object* v___x_4585_; lean_object* v___x_4586_; 
v___x_4580_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkDoneProgressParams_toJson___closed__0));
v___x_4581_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextEdit_toJson_spec__1(v___x_4580_, v_x_4579_);
v___x_4582_ = lean_box(0);
v___x_4583_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4583_, 0, v___x_4581_);
lean_ctor_set(v___x_4583_, 1, v___x_4582_);
v___x_4584_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__2));
v___x_4585_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLocation_toJson_spec__0(v___x_4583_, v___x_4584_);
v___x_4586_ = l_Lean_Json_mkObj(v___x_4585_);
lean_dec(v___x_4585_);
return v___x_4586_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkDoneProgressParams_fromJson___closed__2(void){
_start:
{
uint8_t v___x_4594_; lean_object* v___x_4595_; lean_object* v___x_4596_; 
v___x_4594_ = 1;
v___x_4595_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWorkDoneProgressParams_fromJson___closed__1));
v___x_4596_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4595_, v___x_4594_);
return v___x_4596_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkDoneProgressParams_fromJson___closed__3(void){
_start:
{
lean_object* v___x_4597_; lean_object* v___x_4598_; lean_object* v___x_4599_; 
v___x_4597_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__5));
v___x_4598_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkDoneProgressParams_fromJson___closed__2, &l_Lean_Lsp_instFromJsonWorkDoneProgressParams_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonWorkDoneProgressParams_fromJson___closed__2);
v___x_4599_ = lean_string_append(v___x_4598_, v___x_4597_);
return v___x_4599_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkDoneProgressParams_fromJson___closed__6(void){
_start:
{
uint8_t v___x_4603_; lean_object* v___x_4604_; lean_object* v___x_4605_; 
v___x_4603_ = 1;
v___x_4604_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWorkDoneProgressParams_fromJson___closed__5));
v___x_4605_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4604_, v___x_4603_);
return v___x_4605_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkDoneProgressParams_fromJson___closed__7(void){
_start:
{
lean_object* v___x_4606_; lean_object* v___x_4607_; lean_object* v___x_4608_; 
v___x_4606_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkDoneProgressParams_fromJson___closed__6, &l_Lean_Lsp_instFromJsonWorkDoneProgressParams_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonWorkDoneProgressParams_fromJson___closed__6);
v___x_4607_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkDoneProgressParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonWorkDoneProgressParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonWorkDoneProgressParams_fromJson___closed__3);
v___x_4608_ = lean_string_append(v___x_4607_, v___x_4606_);
return v___x_4608_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkDoneProgressParams_fromJson___closed__8(void){
_start:
{
lean_object* v___x_4609_; lean_object* v___x_4610_; lean_object* v___x_4611_; 
v___x_4609_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_4610_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkDoneProgressParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonWorkDoneProgressParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonWorkDoneProgressParams_fromJson___closed__7);
v___x_4611_ = lean_string_append(v___x_4610_, v___x_4609_);
return v___x_4611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonWorkDoneProgressParams_fromJson(lean_object* v_json_4612_){
_start:
{
lean_object* v___x_4613_; lean_object* v___x_4614_; 
v___x_4613_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkDoneProgressParams_toJson___closed__0));
v___x_4614_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextEdit_fromJson_spec__1(v_json_4612_, v___x_4613_);
if (lean_obj_tag(v___x_4614_) == 0)
{
lean_object* v_a_4615_; lean_object* v___x_4617_; uint8_t v_isShared_4618_; uint8_t v_isSharedCheck_4624_; 
v_a_4615_ = lean_ctor_get(v___x_4614_, 0);
v_isSharedCheck_4624_ = !lean_is_exclusive(v___x_4614_);
if (v_isSharedCheck_4624_ == 0)
{
v___x_4617_ = v___x_4614_;
v_isShared_4618_ = v_isSharedCheck_4624_;
goto v_resetjp_4616_;
}
else
{
lean_inc(v_a_4615_);
lean_dec(v___x_4614_);
v___x_4617_ = lean_box(0);
v_isShared_4618_ = v_isSharedCheck_4624_;
goto v_resetjp_4616_;
}
v_resetjp_4616_:
{
lean_object* v___x_4619_; lean_object* v___x_4620_; lean_object* v___x_4622_; 
v___x_4619_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkDoneProgressParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonWorkDoneProgressParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonWorkDoneProgressParams_fromJson___closed__8);
v___x_4620_ = lean_string_append(v___x_4619_, v_a_4615_);
lean_dec(v_a_4615_);
if (v_isShared_4618_ == 0)
{
lean_ctor_set(v___x_4617_, 0, v___x_4620_);
v___x_4622_ = v___x_4617_;
goto v_reusejp_4621_;
}
else
{
lean_object* v_reuseFailAlloc_4623_; 
v_reuseFailAlloc_4623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4623_, 0, v___x_4620_);
v___x_4622_ = v_reuseFailAlloc_4623_;
goto v_reusejp_4621_;
}
v_reusejp_4621_:
{
return v___x_4622_;
}
}
}
else
{
if (lean_obj_tag(v___x_4614_) == 0)
{
lean_object* v_a_4625_; lean_object* v___x_4627_; uint8_t v_isShared_4628_; uint8_t v_isSharedCheck_4632_; 
v_a_4625_ = lean_ctor_get(v___x_4614_, 0);
v_isSharedCheck_4632_ = !lean_is_exclusive(v___x_4614_);
if (v_isSharedCheck_4632_ == 0)
{
v___x_4627_ = v___x_4614_;
v_isShared_4628_ = v_isSharedCheck_4632_;
goto v_resetjp_4626_;
}
else
{
lean_inc(v_a_4625_);
lean_dec(v___x_4614_);
v___x_4627_ = lean_box(0);
v_isShared_4628_ = v_isSharedCheck_4632_;
goto v_resetjp_4626_;
}
v_resetjp_4626_:
{
lean_object* v___x_4630_; 
if (v_isShared_4628_ == 0)
{
lean_ctor_set_tag(v___x_4627_, 0);
v___x_4630_ = v___x_4627_;
goto v_reusejp_4629_;
}
else
{
lean_object* v_reuseFailAlloc_4631_; 
v_reuseFailAlloc_4631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4631_, 0, v_a_4625_);
v___x_4630_ = v_reuseFailAlloc_4631_;
goto v_reusejp_4629_;
}
v_reusejp_4629_:
{
return v___x_4630_;
}
}
}
else
{
lean_object* v_a_4633_; lean_object* v___x_4635_; uint8_t v_isShared_4636_; uint8_t v_isSharedCheck_4640_; 
v_a_4633_ = lean_ctor_get(v___x_4614_, 0);
v_isSharedCheck_4640_ = !lean_is_exclusive(v___x_4614_);
if (v_isSharedCheck_4640_ == 0)
{
v___x_4635_ = v___x_4614_;
v_isShared_4636_ = v_isSharedCheck_4640_;
goto v_resetjp_4634_;
}
else
{
lean_inc(v_a_4633_);
lean_dec(v___x_4614_);
v___x_4635_ = lean_box(0);
v_isShared_4636_ = v_isSharedCheck_4640_;
goto v_resetjp_4634_;
}
v_resetjp_4634_:
{
lean_object* v___x_4638_; 
if (v_isShared_4636_ == 0)
{
v___x_4638_ = v___x_4635_;
goto v_reusejp_4637_;
}
else
{
lean_object* v_reuseFailAlloc_4639_; 
v_reuseFailAlloc_4639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4639_, 0, v_a_4633_);
v___x_4638_ = v_reuseFailAlloc_4639_;
goto v_reusejp_4637_;
}
v_reusejp_4637_:
{
return v___x_4638_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonPartialResultParams_toJson(lean_object* v_x_4644_){
_start:
{
lean_object* v___x_4645_; lean_object* v___x_4646_; lean_object* v___x_4647_; lean_object* v___x_4648_; lean_object* v___x_4649_; lean_object* v___x_4650_; lean_object* v___x_4651_; 
v___x_4645_ = ((lean_object*)(l_Lean_Lsp_instToJsonPartialResultParams_toJson___closed__0));
v___x_4646_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextEdit_toJson_spec__1(v___x_4645_, v_x_4644_);
v___x_4647_ = lean_box(0);
v___x_4648_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4648_, 0, v___x_4646_);
lean_ctor_set(v___x_4648_, 1, v___x_4647_);
v___x_4649_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__2));
v___x_4650_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLocation_toJson_spec__0(v___x_4648_, v___x_4649_);
v___x_4651_ = l_Lean_Json_mkObj(v___x_4650_);
lean_dec(v___x_4650_);
return v___x_4651_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPartialResultParams_fromJson___closed__2(void){
_start:
{
uint8_t v___x_4659_; lean_object* v___x_4660_; lean_object* v___x_4661_; 
v___x_4659_ = 1;
v___x_4660_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPartialResultParams_fromJson___closed__1));
v___x_4661_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4660_, v___x_4659_);
return v___x_4661_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPartialResultParams_fromJson___closed__3(void){
_start:
{
lean_object* v___x_4662_; lean_object* v___x_4663_; lean_object* v___x_4664_; 
v___x_4662_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__5));
v___x_4663_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPartialResultParams_fromJson___closed__2, &l_Lean_Lsp_instFromJsonPartialResultParams_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonPartialResultParams_fromJson___closed__2);
v___x_4664_ = lean_string_append(v___x_4663_, v___x_4662_);
return v___x_4664_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPartialResultParams_fromJson___closed__6(void){
_start:
{
uint8_t v___x_4668_; lean_object* v___x_4669_; lean_object* v___x_4670_; 
v___x_4668_ = 1;
v___x_4669_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPartialResultParams_fromJson___closed__5));
v___x_4670_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4669_, v___x_4668_);
return v___x_4670_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPartialResultParams_fromJson___closed__7(void){
_start:
{
lean_object* v___x_4671_; lean_object* v___x_4672_; lean_object* v___x_4673_; 
v___x_4671_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPartialResultParams_fromJson___closed__6, &l_Lean_Lsp_instFromJsonPartialResultParams_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonPartialResultParams_fromJson___closed__6);
v___x_4672_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPartialResultParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonPartialResultParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonPartialResultParams_fromJson___closed__3);
v___x_4673_ = lean_string_append(v___x_4672_, v___x_4671_);
return v___x_4673_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPartialResultParams_fromJson___closed__8(void){
_start:
{
lean_object* v___x_4674_; lean_object* v___x_4675_; lean_object* v___x_4676_; 
v___x_4674_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_4675_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPartialResultParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonPartialResultParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonPartialResultParams_fromJson___closed__7);
v___x_4676_ = lean_string_append(v___x_4675_, v___x_4674_);
return v___x_4676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonPartialResultParams_fromJson(lean_object* v_json_4677_){
_start:
{
lean_object* v___x_4678_; lean_object* v___x_4679_; 
v___x_4678_ = ((lean_object*)(l_Lean_Lsp_instToJsonPartialResultParams_toJson___closed__0));
v___x_4679_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextEdit_fromJson_spec__1(v_json_4677_, v___x_4678_);
if (lean_obj_tag(v___x_4679_) == 0)
{
lean_object* v_a_4680_; lean_object* v___x_4682_; uint8_t v_isShared_4683_; uint8_t v_isSharedCheck_4689_; 
v_a_4680_ = lean_ctor_get(v___x_4679_, 0);
v_isSharedCheck_4689_ = !lean_is_exclusive(v___x_4679_);
if (v_isSharedCheck_4689_ == 0)
{
v___x_4682_ = v___x_4679_;
v_isShared_4683_ = v_isSharedCheck_4689_;
goto v_resetjp_4681_;
}
else
{
lean_inc(v_a_4680_);
lean_dec(v___x_4679_);
v___x_4682_ = lean_box(0);
v_isShared_4683_ = v_isSharedCheck_4689_;
goto v_resetjp_4681_;
}
v_resetjp_4681_:
{
lean_object* v___x_4684_; lean_object* v___x_4685_; lean_object* v___x_4687_; 
v___x_4684_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPartialResultParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonPartialResultParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonPartialResultParams_fromJson___closed__8);
v___x_4685_ = lean_string_append(v___x_4684_, v_a_4680_);
lean_dec(v_a_4680_);
if (v_isShared_4683_ == 0)
{
lean_ctor_set(v___x_4682_, 0, v___x_4685_);
v___x_4687_ = v___x_4682_;
goto v_reusejp_4686_;
}
else
{
lean_object* v_reuseFailAlloc_4688_; 
v_reuseFailAlloc_4688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4688_, 0, v___x_4685_);
v___x_4687_ = v_reuseFailAlloc_4688_;
goto v_reusejp_4686_;
}
v_reusejp_4686_:
{
return v___x_4687_;
}
}
}
else
{
if (lean_obj_tag(v___x_4679_) == 0)
{
lean_object* v_a_4690_; lean_object* v___x_4692_; uint8_t v_isShared_4693_; uint8_t v_isSharedCheck_4697_; 
v_a_4690_ = lean_ctor_get(v___x_4679_, 0);
v_isSharedCheck_4697_ = !lean_is_exclusive(v___x_4679_);
if (v_isSharedCheck_4697_ == 0)
{
v___x_4692_ = v___x_4679_;
v_isShared_4693_ = v_isSharedCheck_4697_;
goto v_resetjp_4691_;
}
else
{
lean_inc(v_a_4690_);
lean_dec(v___x_4679_);
v___x_4692_ = lean_box(0);
v_isShared_4693_ = v_isSharedCheck_4697_;
goto v_resetjp_4691_;
}
v_resetjp_4691_:
{
lean_object* v___x_4695_; 
if (v_isShared_4693_ == 0)
{
lean_ctor_set_tag(v___x_4692_, 0);
v___x_4695_ = v___x_4692_;
goto v_reusejp_4694_;
}
else
{
lean_object* v_reuseFailAlloc_4696_; 
v_reuseFailAlloc_4696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4696_, 0, v_a_4690_);
v___x_4695_ = v_reuseFailAlloc_4696_;
goto v_reusejp_4694_;
}
v_reusejp_4694_:
{
return v___x_4695_;
}
}
}
else
{
lean_object* v_a_4698_; lean_object* v___x_4700_; uint8_t v_isShared_4701_; uint8_t v_isSharedCheck_4705_; 
v_a_4698_ = lean_ctor_get(v___x_4679_, 0);
v_isSharedCheck_4705_ = !lean_is_exclusive(v___x_4679_);
if (v_isSharedCheck_4705_ == 0)
{
v___x_4700_ = v___x_4679_;
v_isShared_4701_ = v_isSharedCheck_4705_;
goto v_resetjp_4699_;
}
else
{
lean_inc(v_a_4698_);
lean_dec(v___x_4679_);
v___x_4700_ = lean_box(0);
v_isShared_4701_ = v_isSharedCheck_4705_;
goto v_resetjp_4699_;
}
v_resetjp_4699_:
{
lean_object* v___x_4703_; 
if (v_isShared_4701_ == 0)
{
v___x_4703_ = v___x_4700_;
goto v_reusejp_4702_;
}
else
{
lean_object* v_reuseFailAlloc_4704_; 
v_reuseFailAlloc_4704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4704_, 0, v_a_4698_);
v___x_4703_ = v_reuseFailAlloc_4704_;
goto v_reusejp_4702_;
}
v_reusejp_4702_:
{
return v___x_4703_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonWorkDoneProgressOptions_toJson(uint8_t v_x_4709_){
_start:
{
lean_object* v___x_4710_; lean_object* v___x_4711_; lean_object* v___x_4712_; lean_object* v___x_4713_; lean_object* v___x_4714_; lean_object* v___x_4715_; lean_object* v___x_4716_; lean_object* v___x_4717_; lean_object* v___x_4718_; 
v___x_4710_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkDoneProgressOptions_toJson___closed__0));
v___x_4711_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_4711_, 0, v_x_4709_);
v___x_4712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4712_, 0, v___x_4710_);
lean_ctor_set(v___x_4712_, 1, v___x_4711_);
v___x_4713_ = lean_box(0);
v___x_4714_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4714_, 0, v___x_4712_);
lean_ctor_set(v___x_4714_, 1, v___x_4713_);
v___x_4715_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4715_, 0, v___x_4714_);
lean_ctor_set(v___x_4715_, 1, v___x_4713_);
v___x_4716_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__2));
v___x_4717_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLocation_toJson_spec__0(v___x_4715_, v___x_4716_);
v___x_4718_ = l_Lean_Json_mkObj(v___x_4717_);
lean_dec(v___x_4717_);
return v___x_4718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonWorkDoneProgressOptions_toJson___boxed(lean_object* v_x_4719_){
_start:
{
uint8_t v_x_29__boxed_4720_; lean_object* v_res_4721_; 
v_x_29__boxed_4720_ = lean_unbox(v_x_4719_);
v_res_4721_ = l_Lean_Lsp_instToJsonWorkDoneProgressOptions_toJson(v_x_29__boxed_4720_);
return v_res_4721_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkDoneProgressOptions_fromJson___closed__2(void){
_start:
{
uint8_t v___x_4729_; lean_object* v___x_4730_; lean_object* v___x_4731_; 
v___x_4729_ = 1;
v___x_4730_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWorkDoneProgressOptions_fromJson___closed__1));
v___x_4731_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4730_, v___x_4729_);
return v___x_4731_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkDoneProgressOptions_fromJson___closed__3(void){
_start:
{
lean_object* v___x_4732_; lean_object* v___x_4733_; lean_object* v___x_4734_; 
v___x_4732_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__5));
v___x_4733_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkDoneProgressOptions_fromJson___closed__2, &l_Lean_Lsp_instFromJsonWorkDoneProgressOptions_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonWorkDoneProgressOptions_fromJson___closed__2);
v___x_4734_ = lean_string_append(v___x_4733_, v___x_4732_);
return v___x_4734_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkDoneProgressOptions_fromJson___closed__5(void){
_start:
{
uint8_t v___x_4737_; lean_object* v___x_4738_; lean_object* v___x_4739_; 
v___x_4737_ = 1;
v___x_4738_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWorkDoneProgressOptions_fromJson___closed__4));
v___x_4739_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4738_, v___x_4737_);
return v___x_4739_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkDoneProgressOptions_fromJson___closed__6(void){
_start:
{
lean_object* v___x_4740_; lean_object* v___x_4741_; lean_object* v___x_4742_; 
v___x_4740_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkDoneProgressOptions_fromJson___closed__5, &l_Lean_Lsp_instFromJsonWorkDoneProgressOptions_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonWorkDoneProgressOptions_fromJson___closed__5);
v___x_4741_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkDoneProgressOptions_fromJson___closed__3, &l_Lean_Lsp_instFromJsonWorkDoneProgressOptions_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonWorkDoneProgressOptions_fromJson___closed__3);
v___x_4742_ = lean_string_append(v___x_4741_, v___x_4740_);
return v___x_4742_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkDoneProgressOptions_fromJson___closed__7(void){
_start:
{
lean_object* v___x_4743_; lean_object* v___x_4744_; lean_object* v___x_4745_; 
v___x_4743_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_4744_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkDoneProgressOptions_fromJson___closed__6, &l_Lean_Lsp_instFromJsonWorkDoneProgressOptions_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonWorkDoneProgressOptions_fromJson___closed__6);
v___x_4745_ = lean_string_append(v___x_4744_, v___x_4743_);
return v___x_4745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonWorkDoneProgressOptions_fromJson(lean_object* v_json_4746_){
_start:
{
lean_object* v___x_4747_; lean_object* v___x_4748_; 
v___x_4747_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkDoneProgressOptions_toJson___closed__0));
v___x_4748_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonChangeAnnotation_fromJson_spec__0(v_json_4746_, v___x_4747_);
if (lean_obj_tag(v___x_4748_) == 0)
{
lean_object* v_a_4749_; lean_object* v___x_4751_; uint8_t v_isShared_4752_; uint8_t v_isSharedCheck_4758_; 
v_a_4749_ = lean_ctor_get(v___x_4748_, 0);
v_isSharedCheck_4758_ = !lean_is_exclusive(v___x_4748_);
if (v_isSharedCheck_4758_ == 0)
{
v___x_4751_ = v___x_4748_;
v_isShared_4752_ = v_isSharedCheck_4758_;
goto v_resetjp_4750_;
}
else
{
lean_inc(v_a_4749_);
lean_dec(v___x_4748_);
v___x_4751_ = lean_box(0);
v_isShared_4752_ = v_isSharedCheck_4758_;
goto v_resetjp_4750_;
}
v_resetjp_4750_:
{
lean_object* v___x_4753_; lean_object* v___x_4754_; lean_object* v___x_4756_; 
v___x_4753_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkDoneProgressOptions_fromJson___closed__7, &l_Lean_Lsp_instFromJsonWorkDoneProgressOptions_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonWorkDoneProgressOptions_fromJson___closed__7);
v___x_4754_ = lean_string_append(v___x_4753_, v_a_4749_);
lean_dec(v_a_4749_);
if (v_isShared_4752_ == 0)
{
lean_ctor_set(v___x_4751_, 0, v___x_4754_);
v___x_4756_ = v___x_4751_;
goto v_reusejp_4755_;
}
else
{
lean_object* v_reuseFailAlloc_4757_; 
v_reuseFailAlloc_4757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4757_, 0, v___x_4754_);
v___x_4756_ = v_reuseFailAlloc_4757_;
goto v_reusejp_4755_;
}
v_reusejp_4755_:
{
return v___x_4756_;
}
}
}
else
{
if (lean_obj_tag(v___x_4748_) == 0)
{
lean_object* v_a_4759_; lean_object* v___x_4761_; uint8_t v_isShared_4762_; uint8_t v_isSharedCheck_4766_; 
v_a_4759_ = lean_ctor_get(v___x_4748_, 0);
v_isSharedCheck_4766_ = !lean_is_exclusive(v___x_4748_);
if (v_isSharedCheck_4766_ == 0)
{
v___x_4761_ = v___x_4748_;
v_isShared_4762_ = v_isSharedCheck_4766_;
goto v_resetjp_4760_;
}
else
{
lean_inc(v_a_4759_);
lean_dec(v___x_4748_);
v___x_4761_ = lean_box(0);
v_isShared_4762_ = v_isSharedCheck_4766_;
goto v_resetjp_4760_;
}
v_resetjp_4760_:
{
lean_object* v___x_4764_; 
if (v_isShared_4762_ == 0)
{
lean_ctor_set_tag(v___x_4761_, 0);
v___x_4764_ = v___x_4761_;
goto v_reusejp_4763_;
}
else
{
lean_object* v_reuseFailAlloc_4765_; 
v_reuseFailAlloc_4765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4765_, 0, v_a_4759_);
v___x_4764_ = v_reuseFailAlloc_4765_;
goto v_reusejp_4763_;
}
v_reusejp_4763_:
{
return v___x_4764_;
}
}
}
else
{
lean_object* v_a_4767_; lean_object* v___x_4769_; uint8_t v_isShared_4770_; uint8_t v_isSharedCheck_4774_; 
v_a_4767_ = lean_ctor_get(v___x_4748_, 0);
v_isSharedCheck_4774_ = !lean_is_exclusive(v___x_4748_);
if (v_isSharedCheck_4774_ == 0)
{
v___x_4769_ = v___x_4748_;
v_isShared_4770_ = v_isSharedCheck_4774_;
goto v_resetjp_4768_;
}
else
{
lean_inc(v_a_4767_);
lean_dec(v___x_4748_);
v___x_4769_ = lean_box(0);
v_isShared_4770_ = v_isSharedCheck_4774_;
goto v_resetjp_4768_;
}
v_resetjp_4768_:
{
lean_object* v___x_4772_; 
if (v_isShared_4770_ == 0)
{
v___x_4772_ = v___x_4769_;
goto v_reusejp_4771_;
}
else
{
lean_object* v_reuseFailAlloc_4773_; 
v_reuseFailAlloc_4773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4773_, 0, v_a_4767_);
v___x_4772_ = v_reuseFailAlloc_4773_;
goto v_reusejp_4771_;
}
v_reusejp_4771_:
{
return v___x_4772_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonResolveSupport_fromJson_spec__0_spec__0_spec__1(size_t v_sz_4777_, size_t v_i_4778_, lean_object* v_bs_4779_){
_start:
{
uint8_t v___x_4780_; 
v___x_4780_ = lean_usize_dec_lt(v_i_4778_, v_sz_4777_);
if (v___x_4780_ == 0)
{
lean_object* v___x_4781_; 
v___x_4781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4781_, 0, v_bs_4779_);
return v___x_4781_;
}
else
{
lean_object* v_v_4782_; lean_object* v___x_4783_; 
v_v_4782_ = lean_array_uget_borrowed(v_bs_4779_, v_i_4778_);
lean_inc(v_v_4782_);
v___x_4783_ = l_Lean_Json_getStr_x3f(v_v_4782_);
if (lean_obj_tag(v___x_4783_) == 0)
{
lean_object* v_a_4784_; lean_object* v___x_4786_; uint8_t v_isShared_4787_; uint8_t v_isSharedCheck_4791_; 
lean_dec_ref(v_bs_4779_);
v_a_4784_ = lean_ctor_get(v___x_4783_, 0);
v_isSharedCheck_4791_ = !lean_is_exclusive(v___x_4783_);
if (v_isSharedCheck_4791_ == 0)
{
v___x_4786_ = v___x_4783_;
v_isShared_4787_ = v_isSharedCheck_4791_;
goto v_resetjp_4785_;
}
else
{
lean_inc(v_a_4784_);
lean_dec(v___x_4783_);
v___x_4786_ = lean_box(0);
v_isShared_4787_ = v_isSharedCheck_4791_;
goto v_resetjp_4785_;
}
v_resetjp_4785_:
{
lean_object* v___x_4789_; 
if (v_isShared_4787_ == 0)
{
v___x_4789_ = v___x_4786_;
goto v_reusejp_4788_;
}
else
{
lean_object* v_reuseFailAlloc_4790_; 
v_reuseFailAlloc_4790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4790_, 0, v_a_4784_);
v___x_4789_ = v_reuseFailAlloc_4790_;
goto v_reusejp_4788_;
}
v_reusejp_4788_:
{
return v___x_4789_;
}
}
}
else
{
lean_object* v_a_4792_; lean_object* v___x_4793_; lean_object* v_bs_x27_4794_; size_t v___x_4795_; size_t v___x_4796_; lean_object* v___x_4797_; 
v_a_4792_ = lean_ctor_get(v___x_4783_, 0);
lean_inc(v_a_4792_);
lean_dec_ref_known(v___x_4783_, 1);
v___x_4793_ = lean_unsigned_to_nat(0u);
v_bs_x27_4794_ = lean_array_uset(v_bs_4779_, v_i_4778_, v___x_4793_);
v___x_4795_ = ((size_t)1ULL);
v___x_4796_ = lean_usize_add(v_i_4778_, v___x_4795_);
v___x_4797_ = lean_array_uset(v_bs_x27_4794_, v_i_4778_, v_a_4792_);
v_i_4778_ = v___x_4796_;
v_bs_4779_ = v___x_4797_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonResolveSupport_fromJson_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_4799_, lean_object* v_i_4800_, lean_object* v_bs_4801_){
_start:
{
size_t v_sz_boxed_4802_; size_t v_i_boxed_4803_; lean_object* v_res_4804_; 
v_sz_boxed_4802_ = lean_unbox_usize(v_sz_4799_);
lean_dec(v_sz_4799_);
v_i_boxed_4803_ = lean_unbox_usize(v_i_4800_);
lean_dec(v_i_4800_);
v_res_4804_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonResolveSupport_fromJson_spec__0_spec__0_spec__1(v_sz_boxed_4802_, v_i_boxed_4803_, v_bs_4801_);
return v_res_4804_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonResolveSupport_fromJson_spec__0_spec__0(lean_object* v_x_4805_){
_start:
{
if (lean_obj_tag(v_x_4805_) == 4)
{
lean_object* v_elems_4806_; size_t v_sz_4807_; size_t v___x_4808_; lean_object* v___x_4809_; 
v_elems_4806_ = lean_ctor_get(v_x_4805_, 0);
lean_inc_ref(v_elems_4806_);
lean_dec_ref_known(v_x_4805_, 1);
v_sz_4807_ = lean_array_size(v_elems_4806_);
v___x_4808_ = ((size_t)0ULL);
v___x_4809_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonResolveSupport_fromJson_spec__0_spec__0_spec__1(v_sz_4807_, v___x_4808_, v_elems_4806_);
return v___x_4809_;
}
else
{
lean_object* v___x_4810_; lean_object* v___x_4811_; lean_object* v___x_4812_; lean_object* v___x_4813_; lean_object* v___x_4814_; lean_object* v___x_4815_; lean_object* v___x_4816_; 
v___x_4810_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCommand_fromJson_spec__0_spec__0_spec__1___closed__0));
v___x_4811_ = lean_unsigned_to_nat(80u);
v___x_4812_ = l_Lean_Json_pretty(v_x_4805_, v___x_4811_);
v___x_4813_ = lean_string_append(v___x_4810_, v___x_4812_);
lean_dec_ref(v___x_4812_);
v___x_4814_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCommand_fromJson_spec__0_spec__0_spec__1___closed__1));
v___x_4815_ = lean_string_append(v___x_4813_, v___x_4814_);
v___x_4816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4816_, 0, v___x_4815_);
return v___x_4816_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonResolveSupport_fromJson_spec__0(lean_object* v_j_4817_, lean_object* v_k_4818_){
_start:
{
lean_object* v___x_4819_; lean_object* v___x_4820_; 
v___x_4819_ = l_Lean_Json_getObjValD(v_j_4817_, v_k_4818_);
v___x_4820_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonResolveSupport_fromJson_spec__0_spec__0(v___x_4819_);
return v___x_4820_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonResolveSupport_fromJson_spec__0___boxed(lean_object* v_j_4821_, lean_object* v_k_4822_){
_start:
{
lean_object* v_res_4823_; 
v_res_4823_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonResolveSupport_fromJson_spec__0(v_j_4821_, v_k_4822_);
lean_dec_ref(v_k_4822_);
return v_res_4823_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonResolveSupport_fromJson___closed__3(void){
_start:
{
uint8_t v___x_4830_; lean_object* v___x_4831_; lean_object* v___x_4832_; 
v___x_4830_ = 1;
v___x_4831_ = ((lean_object*)(l_Lean_Lsp_instFromJsonResolveSupport_fromJson___closed__2));
v___x_4832_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4831_, v___x_4830_);
return v___x_4832_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonResolveSupport_fromJson___closed__4(void){
_start:
{
lean_object* v___x_4833_; lean_object* v___x_4834_; lean_object* v___x_4835_; 
v___x_4833_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__5));
v___x_4834_ = lean_obj_once(&l_Lean_Lsp_instFromJsonResolveSupport_fromJson___closed__3, &l_Lean_Lsp_instFromJsonResolveSupport_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonResolveSupport_fromJson___closed__3);
v___x_4835_ = lean_string_append(v___x_4834_, v___x_4833_);
return v___x_4835_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonResolveSupport_fromJson___closed__6(void){
_start:
{
uint8_t v___x_4838_; lean_object* v___x_4839_; lean_object* v___x_4840_; 
v___x_4838_ = 1;
v___x_4839_ = ((lean_object*)(l_Lean_Lsp_instFromJsonResolveSupport_fromJson___closed__5));
v___x_4840_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4839_, v___x_4838_);
return v___x_4840_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonResolveSupport_fromJson___closed__7(void){
_start:
{
lean_object* v___x_4841_; lean_object* v___x_4842_; lean_object* v___x_4843_; 
v___x_4841_ = lean_obj_once(&l_Lean_Lsp_instFromJsonResolveSupport_fromJson___closed__6, &l_Lean_Lsp_instFromJsonResolveSupport_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonResolveSupport_fromJson___closed__6);
v___x_4842_ = lean_obj_once(&l_Lean_Lsp_instFromJsonResolveSupport_fromJson___closed__4, &l_Lean_Lsp_instFromJsonResolveSupport_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonResolveSupport_fromJson___closed__4);
v___x_4843_ = lean_string_append(v___x_4842_, v___x_4841_);
return v___x_4843_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonResolveSupport_fromJson___closed__8(void){
_start:
{
lean_object* v___x_4844_; lean_object* v___x_4845_; lean_object* v___x_4846_; 
v___x_4844_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_4845_ = lean_obj_once(&l_Lean_Lsp_instFromJsonResolveSupport_fromJson___closed__7, &l_Lean_Lsp_instFromJsonResolveSupport_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonResolveSupport_fromJson___closed__7);
v___x_4846_ = lean_string_append(v___x_4845_, v___x_4844_);
return v___x_4846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonResolveSupport_fromJson(lean_object* v_json_4847_){
_start:
{
lean_object* v___x_4848_; lean_object* v___x_4849_; 
v___x_4848_ = ((lean_object*)(l_Lean_Lsp_instFromJsonResolveSupport_fromJson___closed__0));
v___x_4849_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonResolveSupport_fromJson_spec__0(v_json_4847_, v___x_4848_);
if (lean_obj_tag(v___x_4849_) == 0)
{
lean_object* v_a_4850_; lean_object* v___x_4852_; uint8_t v_isShared_4853_; uint8_t v_isSharedCheck_4859_; 
v_a_4850_ = lean_ctor_get(v___x_4849_, 0);
v_isSharedCheck_4859_ = !lean_is_exclusive(v___x_4849_);
if (v_isSharedCheck_4859_ == 0)
{
v___x_4852_ = v___x_4849_;
v_isShared_4853_ = v_isSharedCheck_4859_;
goto v_resetjp_4851_;
}
else
{
lean_inc(v_a_4850_);
lean_dec(v___x_4849_);
v___x_4852_ = lean_box(0);
v_isShared_4853_ = v_isSharedCheck_4859_;
goto v_resetjp_4851_;
}
v_resetjp_4851_:
{
lean_object* v___x_4854_; lean_object* v___x_4855_; lean_object* v___x_4857_; 
v___x_4854_ = lean_obj_once(&l_Lean_Lsp_instFromJsonResolveSupport_fromJson___closed__8, &l_Lean_Lsp_instFromJsonResolveSupport_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonResolveSupport_fromJson___closed__8);
v___x_4855_ = lean_string_append(v___x_4854_, v_a_4850_);
lean_dec(v_a_4850_);
if (v_isShared_4853_ == 0)
{
lean_ctor_set(v___x_4852_, 0, v___x_4855_);
v___x_4857_ = v___x_4852_;
goto v_reusejp_4856_;
}
else
{
lean_object* v_reuseFailAlloc_4858_; 
v_reuseFailAlloc_4858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4858_, 0, v___x_4855_);
v___x_4857_ = v_reuseFailAlloc_4858_;
goto v_reusejp_4856_;
}
v_reusejp_4856_:
{
return v___x_4857_;
}
}
}
else
{
if (lean_obj_tag(v___x_4849_) == 0)
{
lean_object* v_a_4860_; lean_object* v___x_4862_; uint8_t v_isShared_4863_; uint8_t v_isSharedCheck_4867_; 
v_a_4860_ = lean_ctor_get(v___x_4849_, 0);
v_isSharedCheck_4867_ = !lean_is_exclusive(v___x_4849_);
if (v_isSharedCheck_4867_ == 0)
{
v___x_4862_ = v___x_4849_;
v_isShared_4863_ = v_isSharedCheck_4867_;
goto v_resetjp_4861_;
}
else
{
lean_inc(v_a_4860_);
lean_dec(v___x_4849_);
v___x_4862_ = lean_box(0);
v_isShared_4863_ = v_isSharedCheck_4867_;
goto v_resetjp_4861_;
}
v_resetjp_4861_:
{
lean_object* v___x_4865_; 
if (v_isShared_4863_ == 0)
{
lean_ctor_set_tag(v___x_4862_, 0);
v___x_4865_ = v___x_4862_;
goto v_reusejp_4864_;
}
else
{
lean_object* v_reuseFailAlloc_4866_; 
v_reuseFailAlloc_4866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4866_, 0, v_a_4860_);
v___x_4865_ = v_reuseFailAlloc_4866_;
goto v_reusejp_4864_;
}
v_reusejp_4864_:
{
return v___x_4865_;
}
}
}
else
{
lean_object* v_a_4868_; lean_object* v___x_4870_; uint8_t v_isShared_4871_; uint8_t v_isSharedCheck_4875_; 
v_a_4868_ = lean_ctor_get(v___x_4849_, 0);
v_isSharedCheck_4875_ = !lean_is_exclusive(v___x_4849_);
if (v_isSharedCheck_4875_ == 0)
{
v___x_4870_ = v___x_4849_;
v_isShared_4871_ = v_isSharedCheck_4875_;
goto v_resetjp_4869_;
}
else
{
lean_inc(v_a_4868_);
lean_dec(v___x_4849_);
v___x_4870_ = lean_box(0);
v_isShared_4871_ = v_isSharedCheck_4875_;
goto v_resetjp_4869_;
}
v_resetjp_4869_:
{
lean_object* v___x_4873_; 
if (v_isShared_4871_ == 0)
{
v___x_4873_ = v___x_4870_;
goto v_reusejp_4872_;
}
else
{
lean_object* v_reuseFailAlloc_4874_; 
v_reuseFailAlloc_4874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4874_, 0, v_a_4868_);
v___x_4873_ = v_reuseFailAlloc_4874_;
goto v_reusejp_4872_;
}
v_reusejp_4872_:
{
return v___x_4873_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonResolveSupport_toJson_spec__0_spec__0(size_t v_sz_4878_, size_t v_i_4879_, lean_object* v_bs_4880_){
_start:
{
uint8_t v___x_4881_; 
v___x_4881_ = lean_usize_dec_lt(v_i_4879_, v_sz_4878_);
if (v___x_4881_ == 0)
{
return v_bs_4880_;
}
else
{
lean_object* v_v_4882_; lean_object* v___x_4883_; lean_object* v_bs_x27_4884_; lean_object* v___x_4885_; size_t v___x_4886_; size_t v___x_4887_; lean_object* v___x_4888_; 
v_v_4882_ = lean_array_uget(v_bs_4880_, v_i_4879_);
v___x_4883_ = lean_unsigned_to_nat(0u);
v_bs_x27_4884_ = lean_array_uset(v_bs_4880_, v_i_4879_, v___x_4883_);
v___x_4885_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4885_, 0, v_v_4882_);
v___x_4886_ = ((size_t)1ULL);
v___x_4887_ = lean_usize_add(v_i_4879_, v___x_4886_);
v___x_4888_ = lean_array_uset(v_bs_x27_4884_, v_i_4879_, v___x_4885_);
v_i_4879_ = v___x_4887_;
v_bs_4880_ = v___x_4888_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonResolveSupport_toJson_spec__0_spec__0___boxed(lean_object* v_sz_4890_, lean_object* v_i_4891_, lean_object* v_bs_4892_){
_start:
{
size_t v_sz_boxed_4893_; size_t v_i_boxed_4894_; lean_object* v_res_4895_; 
v_sz_boxed_4893_ = lean_unbox_usize(v_sz_4890_);
lean_dec(v_sz_4890_);
v_i_boxed_4894_ = lean_unbox_usize(v_i_4891_);
lean_dec(v_i_4891_);
v_res_4895_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonResolveSupport_toJson_spec__0_spec__0(v_sz_boxed_4893_, v_i_boxed_4894_, v_bs_4892_);
return v_res_4895_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Lsp_instToJsonResolveSupport_toJson_spec__0(lean_object* v_a_4896_){
_start:
{
size_t v_sz_4897_; size_t v___x_4898_; lean_object* v___x_4899_; lean_object* v___x_4900_; 
v_sz_4897_ = lean_array_size(v_a_4896_);
v___x_4898_ = ((size_t)0ULL);
v___x_4899_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonResolveSupport_toJson_spec__0_spec__0(v_sz_4897_, v___x_4898_, v_a_4896_);
v___x_4900_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_4900_, 0, v___x_4899_);
return v___x_4900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonResolveSupport_toJson(lean_object* v_x_4901_){
_start:
{
lean_object* v___x_4902_; lean_object* v___x_4903_; lean_object* v___x_4904_; lean_object* v___x_4905_; lean_object* v___x_4906_; lean_object* v___x_4907_; lean_object* v___x_4908_; lean_object* v___x_4909_; lean_object* v___x_4910_; 
v___x_4902_ = ((lean_object*)(l_Lean_Lsp_instFromJsonResolveSupport_fromJson___closed__0));
v___x_4903_ = l_Array_toJson___at___00Lean_Lsp_instToJsonResolveSupport_toJson_spec__0(v_x_4901_);
v___x_4904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4904_, 0, v___x_4902_);
lean_ctor_set(v___x_4904_, 1, v___x_4903_);
v___x_4905_ = lean_box(0);
v___x_4906_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4906_, 0, v___x_4904_);
lean_ctor_set(v___x_4906_, 1, v___x_4905_);
v___x_4907_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4907_, 0, v___x_4906_);
lean_ctor_set(v___x_4907_, 1, v___x_4905_);
v___x_4908_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__2));
v___x_4909_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLocation_toJson_spec__0(v___x_4907_, v___x_4908_);
v___x_4910_ = l_Lean_Json_mkObj(v___x_4909_);
lean_dec(v___x_4909_);
return v___x_4910_;
}
}
lean_object* runtime_initialize_Lean_Data_Json(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Lsp_BasicAux(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_Coe(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_Lsp_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Data_Json(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Lsp_BasicAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Option_Coe(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Lsp_instInhabitedLocation_default = _init_l_Lean_Lsp_instInhabitedLocation_default();
lean_mark_persistent(l_Lean_Lsp_instInhabitedLocation_default);
l_Lean_Lsp_instInhabitedLocation = _init_l_Lean_Lsp_instInhabitedLocation();
lean_mark_persistent(l_Lean_Lsp_instInhabitedLocation);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Data_Lsp_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Data_Json(uint8_t builtin);
lean_object* initialize_Lean_Data_Lsp_BasicAux(uint8_t builtin);
lean_object* initialize_Init_Data_Option_Coe(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_Lsp_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_Json(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Lsp_BasicAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Coe(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Lsp_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Data_Lsp_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Data_Lsp_Basic(builtin);
}
#ifdef __cplusplus
}
#endif

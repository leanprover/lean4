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
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Lsp_instFromJsonPosition_fromJson(lean_object*);
lean_object* l_Array_fromJson_x3f(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Json_getObj_x3f(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* l_Lean_Lsp_instInhabitedRange_default;
lean_object* l_Array_append___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Lsp_instOrdRange_ord(lean_object*, lean_object*);
lean_object* l_Array_toJson(lean_object*, lean_object*, lean_object*);
lean_object* l_id___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Lsp_instBEqRange_beq(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_foldl___redArg(lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l_Lean_Lsp_instAppendTextEditBatch___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Array_append___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
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
LEAN_EXPORT uint8_t l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__1_spec__2___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__1_spec__2___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__1_spec__2_spec__4_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__2_spec__4_spec__7_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__2_spec__4_spec__7(lean_object*, lean_object*);
static const lean_ctor_object l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__2_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__2_spec__4___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__2_spec__4___closed__0_value;
static const lean_closure_object l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__2_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__1_spec__2___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
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
LEAN_EXPORT lean_object* l_Lean_Lsp_WorkspaceEdit_instAppend___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_WorkspaceEdit_instAppend___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_WorkspaceEdit_instAppend___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_WorkspaceEdit_instAppend___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_WorkspaceEdit_instAppend___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_WorkspaceEdit_instAppend___lam__4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_WorkspaceEdit_instAppend___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_WorkspaceEdit_instAppend___lam__0, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__2_spec__4___closed__1_value)} };
static const lean_object* l_Lean_Lsp_WorkspaceEdit_instAppend___closed__0 = (const lean_object*)&l_Lean_Lsp_WorkspaceEdit_instAppend___closed__0_value;
static const lean_closure_object l_Lean_Lsp_WorkspaceEdit_instAppend___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_WorkspaceEdit_instAppend___lam__3, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__2_spec__4___closed__1_value)} };
static const lean_object* l_Lean_Lsp_WorkspaceEdit_instAppend___closed__1 = (const lean_object*)&l_Lean_Lsp_WorkspaceEdit_instAppend___closed__1_value;
static const lean_closure_object l_Lean_Lsp_WorkspaceEdit_instAppend___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_WorkspaceEdit_instAppend___lam__4, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Lsp_WorkspaceEdit_instAppend___closed__1_value),((lean_object*)&l_Lean_Lsp_WorkspaceEdit_instAppend___closed__0_value)} };
static const lean_object* l_Lean_Lsp_WorkspaceEdit_instAppend___closed__2 = (const lean_object*)&l_Lean_Lsp_WorkspaceEdit_instAppend___closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_WorkspaceEdit_instAppend = (const lean_object*)&l_Lean_Lsp_WorkspaceEdit_instAppend___closed__2_value;
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
lean_dec_ref(v_a_21_);
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
lean_dec_ref(v___x_110_);
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
v___x_167_ = lean_string_dec_lt(v_uri_163_, v_uri_165_);
if (v___x_167_ == 0)
{
uint8_t v___x_168_; 
v___x_168_ = lean_string_dec_eq(v_uri_163_, v_uri_165_);
if (v___x_168_ == 0)
{
uint8_t v___x_169_; 
v___x_169_ = 2;
return v___x_169_;
}
else
{
uint8_t v___x_170_; 
v___x_170_ = l_Lean_Lsp_instOrdRange_ord(v_range_164_, v_range_166_);
if (v___x_170_ == 1)
{
return v___x_170_;
}
else
{
return v___x_170_;
}
}
}
else
{
uint8_t v___x_171_; 
v___x_171_ = 0;
return v___x_171_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instOrdLocation_ord___boxed(lean_object* v_x_172_, lean_object* v_x_173_){
_start:
{
uint8_t v_res_174_; lean_object* v_r_175_; 
v_res_174_ = l_Lean_Lsp_instOrdLocation_ord(v_x_172_, v_x_173_);
lean_dec_ref(v_x_173_);
lean_dec_ref(v_x_172_);
v_r_175_ = lean_box(v_res_174_);
return v_r_175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLocationLink_toJson_spec__0(lean_object* v_k_178_, lean_object* v_x_179_){
_start:
{
if (lean_obj_tag(v_x_179_) == 0)
{
lean_object* v___x_180_; 
lean_dec_ref(v_k_178_);
v___x_180_ = lean_box(0);
return v___x_180_;
}
else
{
lean_object* v_val_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v_val_181_ = lean_ctor_get(v_x_179_, 0);
lean_inc(v_val_181_);
lean_dec_ref(v_x_179_);
v___x_182_ = l_Lean_Lsp_instToJsonRange_toJson(v_val_181_);
v___x_183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_183_, 0, v_k_178_);
lean_ctor_set(v___x_183_, 1, v___x_182_);
v___x_184_ = lean_box(0);
v___x_185_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_185_, 0, v___x_183_);
lean_ctor_set(v___x_185_, 1, v___x_184_);
return v___x_185_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLocationLink_toJson(lean_object* v_x_190_){
_start:
{
lean_object* v_originSelectionRange_x3f_191_; lean_object* v_targetUri_192_; lean_object* v_targetRange_193_; lean_object* v_targetSelectionRange_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; 
v_originSelectionRange_x3f_191_ = lean_ctor_get(v_x_190_, 0);
lean_inc(v_originSelectionRange_x3f_191_);
v_targetUri_192_ = lean_ctor_get(v_x_190_, 1);
lean_inc_ref(v_targetUri_192_);
v_targetRange_193_ = lean_ctor_get(v_x_190_, 2);
lean_inc_ref(v_targetRange_193_);
v_targetSelectionRange_194_ = lean_ctor_get(v_x_190_, 3);
lean_inc_ref(v_targetSelectionRange_194_);
lean_dec_ref(v_x_190_);
v___x_195_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocationLink_toJson___closed__0));
v___x_196_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLocationLink_toJson_spec__0(v___x_195_, v_originSelectionRange_x3f_191_);
v___x_197_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocationLink_toJson___closed__1));
v___x_198_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_198_, 0, v_targetUri_192_);
v___x_199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_199_, 0, v___x_197_);
lean_ctor_set(v___x_199_, 1, v___x_198_);
v___x_200_ = lean_box(0);
v___x_201_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_201_, 0, v___x_199_);
lean_ctor_set(v___x_201_, 1, v___x_200_);
v___x_202_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocationLink_toJson___closed__2));
v___x_203_ = l_Lean_Lsp_instToJsonRange_toJson(v_targetRange_193_);
v___x_204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_204_, 0, v___x_202_);
lean_ctor_set(v___x_204_, 1, v___x_203_);
v___x_205_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_205_, 0, v___x_204_);
lean_ctor_set(v___x_205_, 1, v___x_200_);
v___x_206_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocationLink_toJson___closed__3));
v___x_207_ = l_Lean_Lsp_instToJsonRange_toJson(v_targetSelectionRange_194_);
v___x_208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_208_, 0, v___x_206_);
lean_ctor_set(v___x_208_, 1, v___x_207_);
v___x_209_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_209_, 0, v___x_208_);
lean_ctor_set(v___x_209_, 1, v___x_200_);
v___x_210_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_210_, 0, v___x_209_);
lean_ctor_set(v___x_210_, 1, v___x_200_);
v___x_211_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_211_, 0, v___x_205_);
lean_ctor_set(v___x_211_, 1, v___x_210_);
v___x_212_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_212_, 0, v___x_201_);
lean_ctor_set(v___x_212_, 1, v___x_211_);
v___x_213_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_213_, 0, v___x_196_);
lean_ctor_set(v___x_213_, 1, v___x_212_);
v___x_214_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__2));
v___x_215_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLocation_toJson_spec__0(v___x_213_, v___x_214_);
v___x_216_ = l_Lean_Json_mkObj(v___x_215_);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocationLink_fromJson_spec__0_spec__0(lean_object* v_x_221_){
_start:
{
if (lean_obj_tag(v_x_221_) == 0)
{
lean_object* v___x_222_; 
v___x_222_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocationLink_fromJson_spec__0_spec__0___closed__0));
return v___x_222_;
}
else
{
lean_object* v___x_223_; 
v___x_223_ = l_Lean_Lsp_instFromJsonRange_fromJson(v_x_221_);
if (lean_obj_tag(v___x_223_) == 0)
{
lean_object* v_a_224_; lean_object* v___x_226_; uint8_t v_isShared_227_; uint8_t v_isSharedCheck_231_; 
v_a_224_ = lean_ctor_get(v___x_223_, 0);
v_isSharedCheck_231_ = !lean_is_exclusive(v___x_223_);
if (v_isSharedCheck_231_ == 0)
{
v___x_226_ = v___x_223_;
v_isShared_227_ = v_isSharedCheck_231_;
goto v_resetjp_225_;
}
else
{
lean_inc(v_a_224_);
lean_dec(v___x_223_);
v___x_226_ = lean_box(0);
v_isShared_227_ = v_isSharedCheck_231_;
goto v_resetjp_225_;
}
v_resetjp_225_:
{
lean_object* v___x_229_; 
if (v_isShared_227_ == 0)
{
v___x_229_ = v___x_226_;
goto v_reusejp_228_;
}
else
{
lean_object* v_reuseFailAlloc_230_; 
v_reuseFailAlloc_230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_230_, 0, v_a_224_);
v___x_229_ = v_reuseFailAlloc_230_;
goto v_reusejp_228_;
}
v_reusejp_228_:
{
return v___x_229_;
}
}
}
else
{
lean_object* v_a_232_; lean_object* v___x_234_; uint8_t v_isShared_235_; uint8_t v_isSharedCheck_240_; 
v_a_232_ = lean_ctor_get(v___x_223_, 0);
v_isSharedCheck_240_ = !lean_is_exclusive(v___x_223_);
if (v_isSharedCheck_240_ == 0)
{
v___x_234_ = v___x_223_;
v_isShared_235_ = v_isSharedCheck_240_;
goto v_resetjp_233_;
}
else
{
lean_inc(v_a_232_);
lean_dec(v___x_223_);
v___x_234_ = lean_box(0);
v_isShared_235_ = v_isSharedCheck_240_;
goto v_resetjp_233_;
}
v_resetjp_233_:
{
lean_object* v___x_236_; lean_object* v___x_238_; 
v___x_236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_236_, 0, v_a_232_);
if (v_isShared_235_ == 0)
{
lean_ctor_set(v___x_234_, 0, v___x_236_);
v___x_238_ = v___x_234_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v___x_236_);
v___x_238_ = v_reuseFailAlloc_239_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
return v___x_238_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocationLink_fromJson_spec__0(lean_object* v_j_241_, lean_object* v_k_242_){
_start:
{
lean_object* v___x_243_; lean_object* v___x_244_; 
v___x_243_ = l_Lean_Json_getObjValD(v_j_241_, v_k_242_);
v___x_244_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocationLink_fromJson_spec__0_spec__0(v___x_243_);
return v___x_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocationLink_fromJson_spec__0___boxed(lean_object* v_j_245_, lean_object* v_k_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocationLink_fromJson_spec__0(v_j_245_, v_k_246_);
lean_dec_ref(v_k_246_);
return v_res_247_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__2(void){
_start:
{
uint8_t v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_253_ = 1;
v___x_254_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__1));
v___x_255_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_254_, v___x_253_);
return v___x_255_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__3(void){
_start:
{
lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_256_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__5));
v___x_257_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__2, &l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__2);
v___x_258_ = lean_string_append(v___x_257_, v___x_256_);
return v___x_258_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__6(void){
_start:
{
uint8_t v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_262_ = 1;
v___x_263_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__5));
v___x_264_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_263_, v___x_262_);
return v___x_264_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__7(void){
_start:
{
lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_265_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__6);
v___x_266_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__3);
v___x_267_ = lean_string_append(v___x_266_, v___x_265_);
return v___x_267_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__8(void){
_start:
{
lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_268_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_269_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__7);
v___x_270_ = lean_string_append(v___x_269_, v___x_268_);
return v___x_270_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__10(void){
_start:
{
uint8_t v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_273_ = 1;
v___x_274_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__9));
v___x_275_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_274_, v___x_273_);
return v___x_275_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__11(void){
_start:
{
lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_276_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__10, &l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__10);
v___x_277_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__3);
v___x_278_ = lean_string_append(v___x_277_, v___x_276_);
return v___x_278_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__12(void){
_start:
{
lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_279_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_280_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__11, &l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__11);
v___x_281_ = lean_string_append(v___x_280_, v___x_279_);
return v___x_281_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__14(void){
_start:
{
uint8_t v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_284_ = 1;
v___x_285_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__13));
v___x_286_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_285_, v___x_284_);
return v___x_286_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__15(void){
_start:
{
lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_287_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__14, &l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__14_once, _init_l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__14);
v___x_288_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__3);
v___x_289_ = lean_string_append(v___x_288_, v___x_287_);
return v___x_289_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__16(void){
_start:
{
lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_290_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_291_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__15, &l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__15_once, _init_l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__15);
v___x_292_ = lean_string_append(v___x_291_, v___x_290_);
return v___x_292_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__18(void){
_start:
{
uint8_t v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_295_ = 1;
v___x_296_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__17));
v___x_297_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_296_, v___x_295_);
return v___x_297_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__19(void){
_start:
{
lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_298_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__18, &l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__18_once, _init_l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__18);
v___x_299_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__3);
v___x_300_ = lean_string_append(v___x_299_, v___x_298_);
return v___x_300_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__20(void){
_start:
{
lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_301_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_302_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__19, &l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__19_once, _init_l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__19);
v___x_303_ = lean_string_append(v___x_302_, v___x_301_);
return v___x_303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLocationLink_fromJson(lean_object* v_json_304_){
_start:
{
lean_object* v___x_305_; lean_object* v___x_306_; 
v___x_305_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocationLink_toJson___closed__0));
lean_inc(v_json_304_);
v___x_306_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocationLink_fromJson_spec__0(v_json_304_, v___x_305_);
if (lean_obj_tag(v___x_306_) == 0)
{
lean_object* v_a_307_; lean_object* v___x_309_; uint8_t v_isShared_310_; uint8_t v_isSharedCheck_316_; 
lean_dec(v_json_304_);
v_a_307_ = lean_ctor_get(v___x_306_, 0);
v_isSharedCheck_316_ = !lean_is_exclusive(v___x_306_);
if (v_isSharedCheck_316_ == 0)
{
v___x_309_ = v___x_306_;
v_isShared_310_ = v_isSharedCheck_316_;
goto v_resetjp_308_;
}
else
{
lean_inc(v_a_307_);
lean_dec(v___x_306_);
v___x_309_ = lean_box(0);
v_isShared_310_ = v_isSharedCheck_316_;
goto v_resetjp_308_;
}
v_resetjp_308_:
{
lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_314_; 
v___x_311_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__8);
v___x_312_ = lean_string_append(v___x_311_, v_a_307_);
lean_dec(v_a_307_);
if (v_isShared_310_ == 0)
{
lean_ctor_set(v___x_309_, 0, v___x_312_);
v___x_314_ = v___x_309_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v___x_312_);
v___x_314_ = v_reuseFailAlloc_315_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
return v___x_314_;
}
}
}
else
{
if (lean_obj_tag(v___x_306_) == 0)
{
lean_object* v_a_317_; lean_object* v___x_319_; uint8_t v_isShared_320_; uint8_t v_isSharedCheck_324_; 
lean_dec(v_json_304_);
v_a_317_ = lean_ctor_get(v___x_306_, 0);
v_isSharedCheck_324_ = !lean_is_exclusive(v___x_306_);
if (v_isSharedCheck_324_ == 0)
{
v___x_319_ = v___x_306_;
v_isShared_320_ = v_isSharedCheck_324_;
goto v_resetjp_318_;
}
else
{
lean_inc(v_a_317_);
lean_dec(v___x_306_);
v___x_319_ = lean_box(0);
v_isShared_320_ = v_isSharedCheck_324_;
goto v_resetjp_318_;
}
v_resetjp_318_:
{
lean_object* v___x_322_; 
if (v_isShared_320_ == 0)
{
lean_ctor_set_tag(v___x_319_, 0);
v___x_322_ = v___x_319_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v_a_317_);
v___x_322_ = v_reuseFailAlloc_323_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
return v___x_322_;
}
}
}
else
{
lean_object* v_a_325_; lean_object* v___x_326_; lean_object* v___x_327_; 
v_a_325_ = lean_ctor_get(v___x_306_, 0);
lean_inc(v_a_325_);
lean_dec_ref(v___x_306_);
v___x_326_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocationLink_toJson___closed__1));
lean_inc(v_json_304_);
v___x_327_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocation_fromJson_spec__0(v_json_304_, v___x_326_);
if (lean_obj_tag(v___x_327_) == 0)
{
lean_object* v_a_328_; lean_object* v___x_330_; uint8_t v_isShared_331_; uint8_t v_isSharedCheck_337_; 
lean_dec(v_a_325_);
lean_dec(v_json_304_);
v_a_328_ = lean_ctor_get(v___x_327_, 0);
v_isSharedCheck_337_ = !lean_is_exclusive(v___x_327_);
if (v_isSharedCheck_337_ == 0)
{
v___x_330_ = v___x_327_;
v_isShared_331_ = v_isSharedCheck_337_;
goto v_resetjp_329_;
}
else
{
lean_inc(v_a_328_);
lean_dec(v___x_327_);
v___x_330_ = lean_box(0);
v_isShared_331_ = v_isSharedCheck_337_;
goto v_resetjp_329_;
}
v_resetjp_329_:
{
lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_335_; 
v___x_332_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__12, &l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__12);
v___x_333_ = lean_string_append(v___x_332_, v_a_328_);
lean_dec(v_a_328_);
if (v_isShared_331_ == 0)
{
lean_ctor_set(v___x_330_, 0, v___x_333_);
v___x_335_ = v___x_330_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v___x_333_);
v___x_335_ = v_reuseFailAlloc_336_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
return v___x_335_;
}
}
}
else
{
if (lean_obj_tag(v___x_327_) == 0)
{
lean_object* v_a_338_; lean_object* v___x_340_; uint8_t v_isShared_341_; uint8_t v_isSharedCheck_345_; 
lean_dec(v_a_325_);
lean_dec(v_json_304_);
v_a_338_ = lean_ctor_get(v___x_327_, 0);
v_isSharedCheck_345_ = !lean_is_exclusive(v___x_327_);
if (v_isSharedCheck_345_ == 0)
{
v___x_340_ = v___x_327_;
v_isShared_341_ = v_isSharedCheck_345_;
goto v_resetjp_339_;
}
else
{
lean_inc(v_a_338_);
lean_dec(v___x_327_);
v___x_340_ = lean_box(0);
v_isShared_341_ = v_isSharedCheck_345_;
goto v_resetjp_339_;
}
v_resetjp_339_:
{
lean_object* v___x_343_; 
if (v_isShared_341_ == 0)
{
lean_ctor_set_tag(v___x_340_, 0);
v___x_343_ = v___x_340_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v_a_338_);
v___x_343_ = v_reuseFailAlloc_344_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
return v___x_343_;
}
}
}
else
{
lean_object* v_a_346_; lean_object* v___x_347_; lean_object* v___x_348_; 
v_a_346_ = lean_ctor_get(v___x_327_, 0);
lean_inc(v_a_346_);
lean_dec_ref(v___x_327_);
v___x_347_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocationLink_toJson___closed__2));
lean_inc(v_json_304_);
v___x_348_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocation_fromJson_spec__1(v_json_304_, v___x_347_);
if (lean_obj_tag(v___x_348_) == 0)
{
lean_object* v_a_349_; lean_object* v___x_351_; uint8_t v_isShared_352_; uint8_t v_isSharedCheck_358_; 
lean_dec(v_a_346_);
lean_dec(v_a_325_);
lean_dec(v_json_304_);
v_a_349_ = lean_ctor_get(v___x_348_, 0);
v_isSharedCheck_358_ = !lean_is_exclusive(v___x_348_);
if (v_isSharedCheck_358_ == 0)
{
v___x_351_ = v___x_348_;
v_isShared_352_ = v_isSharedCheck_358_;
goto v_resetjp_350_;
}
else
{
lean_inc(v_a_349_);
lean_dec(v___x_348_);
v___x_351_ = lean_box(0);
v_isShared_352_ = v_isSharedCheck_358_;
goto v_resetjp_350_;
}
v_resetjp_350_:
{
lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_356_; 
v___x_353_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__16, &l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__16_once, _init_l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__16);
v___x_354_ = lean_string_append(v___x_353_, v_a_349_);
lean_dec(v_a_349_);
if (v_isShared_352_ == 0)
{
lean_ctor_set(v___x_351_, 0, v___x_354_);
v___x_356_ = v___x_351_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v___x_354_);
v___x_356_ = v_reuseFailAlloc_357_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
return v___x_356_;
}
}
}
else
{
if (lean_obj_tag(v___x_348_) == 0)
{
lean_object* v_a_359_; lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_366_; 
lean_dec(v_a_346_);
lean_dec(v_a_325_);
lean_dec(v_json_304_);
v_a_359_ = lean_ctor_get(v___x_348_, 0);
v_isSharedCheck_366_ = !lean_is_exclusive(v___x_348_);
if (v_isSharedCheck_366_ == 0)
{
v___x_361_ = v___x_348_;
v_isShared_362_ = v_isSharedCheck_366_;
goto v_resetjp_360_;
}
else
{
lean_inc(v_a_359_);
lean_dec(v___x_348_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_366_;
goto v_resetjp_360_;
}
v_resetjp_360_:
{
lean_object* v___x_364_; 
if (v_isShared_362_ == 0)
{
lean_ctor_set_tag(v___x_361_, 0);
v___x_364_ = v___x_361_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v_a_359_);
v___x_364_ = v_reuseFailAlloc_365_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
return v___x_364_;
}
}
}
else
{
lean_object* v_a_367_; lean_object* v___x_368_; lean_object* v___x_369_; 
v_a_367_ = lean_ctor_get(v___x_348_, 0);
lean_inc(v_a_367_);
lean_dec_ref(v___x_348_);
v___x_368_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocationLink_toJson___closed__3));
v___x_369_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocation_fromJson_spec__1(v_json_304_, v___x_368_);
if (lean_obj_tag(v___x_369_) == 0)
{
lean_object* v_a_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_379_; 
lean_dec(v_a_367_);
lean_dec(v_a_346_);
lean_dec(v_a_325_);
v_a_370_ = lean_ctor_get(v___x_369_, 0);
v_isSharedCheck_379_ = !lean_is_exclusive(v___x_369_);
if (v_isSharedCheck_379_ == 0)
{
v___x_372_ = v___x_369_;
v_isShared_373_ = v_isSharedCheck_379_;
goto v_resetjp_371_;
}
else
{
lean_inc(v_a_370_);
lean_dec(v___x_369_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_379_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_377_; 
v___x_374_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__20, &l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__20_once, _init_l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__20);
v___x_375_ = lean_string_append(v___x_374_, v_a_370_);
lean_dec(v_a_370_);
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 0, v___x_375_);
v___x_377_ = v___x_372_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v___x_375_);
v___x_377_ = v_reuseFailAlloc_378_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
return v___x_377_;
}
}
}
else
{
if (lean_obj_tag(v___x_369_) == 0)
{
lean_object* v_a_380_; lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_387_; 
lean_dec(v_a_367_);
lean_dec(v_a_346_);
lean_dec(v_a_325_);
v_a_380_ = lean_ctor_get(v___x_369_, 0);
v_isSharedCheck_387_ = !lean_is_exclusive(v___x_369_);
if (v_isSharedCheck_387_ == 0)
{
v___x_382_ = v___x_369_;
v_isShared_383_ = v_isSharedCheck_387_;
goto v_resetjp_381_;
}
else
{
lean_inc(v_a_380_);
lean_dec(v___x_369_);
v___x_382_ = lean_box(0);
v_isShared_383_ = v_isSharedCheck_387_;
goto v_resetjp_381_;
}
v_resetjp_381_:
{
lean_object* v___x_385_; 
if (v_isShared_383_ == 0)
{
lean_ctor_set_tag(v___x_382_, 0);
v___x_385_ = v___x_382_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_386_; 
v_reuseFailAlloc_386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_386_, 0, v_a_380_);
v___x_385_ = v_reuseFailAlloc_386_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
return v___x_385_;
}
}
}
else
{
lean_object* v_a_388_; lean_object* v___x_390_; uint8_t v_isShared_391_; uint8_t v_isSharedCheck_396_; 
v_a_388_ = lean_ctor_get(v___x_369_, 0);
v_isSharedCheck_396_ = !lean_is_exclusive(v___x_369_);
if (v_isSharedCheck_396_ == 0)
{
v___x_390_ = v___x_369_;
v_isShared_391_ = v_isSharedCheck_396_;
goto v_resetjp_389_;
}
else
{
lean_inc(v_a_388_);
lean_dec(v___x_369_);
v___x_390_ = lean_box(0);
v_isShared_391_ = v_isSharedCheck_396_;
goto v_resetjp_389_;
}
v_resetjp_389_:
{
lean_object* v___x_392_; lean_object* v___x_394_; 
v___x_392_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_392_, 0, v_a_325_);
lean_ctor_set(v___x_392_, 1, v_a_346_);
lean_ctor_set(v___x_392_, 2, v_a_367_);
lean_ctor_set(v___x_392_, 3, v_a_388_);
if (v_isShared_391_ == 0)
{
lean_ctor_set(v___x_390_, 0, v___x_392_);
v___x_394_ = v___x_390_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v___x_392_);
v___x_394_ = v_reuseFailAlloc_395_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
return v___x_394_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonCommand_toJson_spec__0_spec__0_spec__1(size_t v_sz_399_, size_t v_i_400_, lean_object* v_bs_401_){
_start:
{
uint8_t v___x_402_; 
v___x_402_ = lean_usize_dec_lt(v_i_400_, v_sz_399_);
if (v___x_402_ == 0)
{
return v_bs_401_;
}
else
{
lean_object* v_v_403_; lean_object* v___x_404_; lean_object* v_bs_x27_405_; size_t v___x_406_; size_t v___x_407_; lean_object* v___x_408_; 
v_v_403_ = lean_array_uget(v_bs_401_, v_i_400_);
v___x_404_ = lean_unsigned_to_nat(0u);
v_bs_x27_405_ = lean_array_uset(v_bs_401_, v_i_400_, v___x_404_);
v___x_406_ = ((size_t)1ULL);
v___x_407_ = lean_usize_add(v_i_400_, v___x_406_);
v___x_408_ = lean_array_uset(v_bs_x27_405_, v_i_400_, v_v_403_);
v_i_400_ = v___x_407_;
v_bs_401_ = v___x_408_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonCommand_toJson_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_410_, lean_object* v_i_411_, lean_object* v_bs_412_){
_start:
{
size_t v_sz_boxed_413_; size_t v_i_boxed_414_; lean_object* v_res_415_; 
v_sz_boxed_413_ = lean_unbox_usize(v_sz_410_);
lean_dec(v_sz_410_);
v_i_boxed_414_ = lean_unbox_usize(v_i_411_);
lean_dec(v_i_411_);
v_res_415_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonCommand_toJson_spec__0_spec__0_spec__1(v_sz_boxed_413_, v_i_boxed_414_, v_bs_412_);
return v_res_415_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonCommand_toJson_spec__0_spec__0(lean_object* v_a_416_){
_start:
{
size_t v_sz_417_; size_t v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; 
v_sz_417_ = lean_array_size(v_a_416_);
v___x_418_ = ((size_t)0ULL);
v___x_419_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonCommand_toJson_spec__0_spec__0_spec__1(v_sz_417_, v___x_418_, v_a_416_);
v___x_420_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_420_, 0, v___x_419_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonCommand_toJson_spec__0(lean_object* v_k_421_, lean_object* v_x_422_){
_start:
{
if (lean_obj_tag(v_x_422_) == 0)
{
lean_object* v___x_423_; 
lean_dec_ref(v_k_421_);
v___x_423_ = lean_box(0);
return v___x_423_;
}
else
{
lean_object* v_val_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; 
v_val_424_ = lean_ctor_get(v_x_422_, 0);
lean_inc(v_val_424_);
lean_dec_ref(v_x_422_);
v___x_425_ = l_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonCommand_toJson_spec__0_spec__0(v_val_424_);
v___x_426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_426_, 0, v_k_421_);
lean_ctor_set(v___x_426_, 1, v___x_425_);
v___x_427_ = lean_box(0);
v___x_428_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_428_, 0, v___x_426_);
lean_ctor_set(v___x_428_, 1, v___x_427_);
return v___x_428_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonCommand_toJson(lean_object* v_x_432_){
_start:
{
lean_object* v_title_433_; lean_object* v_command_434_; lean_object* v_arguments_x3f_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; 
v_title_433_ = lean_ctor_get(v_x_432_, 0);
lean_inc_ref(v_title_433_);
v_command_434_ = lean_ctor_get(v_x_432_, 1);
lean_inc_ref(v_command_434_);
v_arguments_x3f_435_ = lean_ctor_get(v_x_432_, 2);
lean_inc(v_arguments_x3f_435_);
lean_dec_ref(v_x_432_);
v___x_436_ = ((lean_object*)(l_Lean_Lsp_instToJsonCommand_toJson___closed__0));
v___x_437_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_437_, 0, v_title_433_);
v___x_438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_438_, 0, v___x_436_);
lean_ctor_set(v___x_438_, 1, v___x_437_);
v___x_439_ = lean_box(0);
v___x_440_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_440_, 0, v___x_438_);
lean_ctor_set(v___x_440_, 1, v___x_439_);
v___x_441_ = ((lean_object*)(l_Lean_Lsp_instToJsonCommand_toJson___closed__1));
v___x_442_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_442_, 0, v_command_434_);
v___x_443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_443_, 0, v___x_441_);
lean_ctor_set(v___x_443_, 1, v___x_442_);
v___x_444_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_444_, 0, v___x_443_);
lean_ctor_set(v___x_444_, 1, v___x_439_);
v___x_445_ = ((lean_object*)(l_Lean_Lsp_instToJsonCommand_toJson___closed__2));
v___x_446_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonCommand_toJson_spec__0(v___x_445_, v_arguments_x3f_435_);
v___x_447_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_447_, 0, v___x_446_);
lean_ctor_set(v___x_447_, 1, v___x_439_);
v___x_448_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_448_, 0, v___x_444_);
lean_ctor_set(v___x_448_, 1, v___x_447_);
v___x_449_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_449_, 0, v___x_440_);
lean_ctor_set(v___x_449_, 1, v___x_448_);
v___x_450_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__2));
v___x_451_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLocation_toJson_spec__0(v___x_449_, v___x_450_);
v___x_452_ = l_Lean_Json_mkObj(v___x_451_);
return v___x_452_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCommand_fromJson_spec__0_spec__0_spec__1_spec__2(size_t v_sz_455_, size_t v_i_456_, lean_object* v_bs_457_){
_start:
{
uint8_t v___x_458_; 
v___x_458_ = lean_usize_dec_lt(v_i_456_, v_sz_455_);
if (v___x_458_ == 0)
{
lean_object* v___x_459_; 
v___x_459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_459_, 0, v_bs_457_);
return v___x_459_;
}
else
{
lean_object* v_v_460_; lean_object* v___x_461_; lean_object* v_bs_x27_462_; size_t v___x_463_; size_t v___x_464_; lean_object* v___x_465_; 
v_v_460_ = lean_array_uget(v_bs_457_, v_i_456_);
v___x_461_ = lean_unsigned_to_nat(0u);
v_bs_x27_462_ = lean_array_uset(v_bs_457_, v_i_456_, v___x_461_);
v___x_463_ = ((size_t)1ULL);
v___x_464_ = lean_usize_add(v_i_456_, v___x_463_);
v___x_465_ = lean_array_uset(v_bs_x27_462_, v_i_456_, v_v_460_);
v_i_456_ = v___x_464_;
v_bs_457_ = v___x_465_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCommand_fromJson_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_sz_467_, lean_object* v_i_468_, lean_object* v_bs_469_){
_start:
{
size_t v_sz_boxed_470_; size_t v_i_boxed_471_; lean_object* v_res_472_; 
v_sz_boxed_470_ = lean_unbox_usize(v_sz_467_);
lean_dec(v_sz_467_);
v_i_boxed_471_ = lean_unbox_usize(v_i_468_);
lean_dec(v_i_468_);
v_res_472_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCommand_fromJson_spec__0_spec__0_spec__1_spec__2(v_sz_boxed_470_, v_i_boxed_471_, v_bs_469_);
return v_res_472_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCommand_fromJson_spec__0_spec__0_spec__1(lean_object* v_x_475_){
_start:
{
if (lean_obj_tag(v_x_475_) == 4)
{
lean_object* v_elems_476_; size_t v_sz_477_; size_t v___x_478_; lean_object* v___x_479_; 
v_elems_476_ = lean_ctor_get(v_x_475_, 0);
lean_inc_ref(v_elems_476_);
lean_dec_ref(v_x_475_);
v_sz_477_ = lean_array_size(v_elems_476_);
v___x_478_ = ((size_t)0ULL);
v___x_479_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCommand_fromJson_spec__0_spec__0_spec__1_spec__2(v_sz_477_, v___x_478_, v_elems_476_);
return v___x_479_;
}
else
{
lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_480_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCommand_fromJson_spec__0_spec__0_spec__1___closed__0));
v___x_481_ = lean_unsigned_to_nat(80u);
v___x_482_ = l_Lean_Json_pretty(v_x_475_, v___x_481_);
v___x_483_ = lean_string_append(v___x_480_, v___x_482_);
lean_dec_ref(v___x_482_);
v___x_484_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCommand_fromJson_spec__0_spec__0_spec__1___closed__1));
v___x_485_ = lean_string_append(v___x_483_, v___x_484_);
v___x_486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_486_, 0, v___x_485_);
return v___x_486_;
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCommand_fromJson_spec__0_spec__0(lean_object* v_x_489_){
_start:
{
if (lean_obj_tag(v_x_489_) == 0)
{
lean_object* v___x_490_; 
v___x_490_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCommand_fromJson_spec__0_spec__0___closed__0));
return v___x_490_;
}
else
{
lean_object* v___x_491_; 
v___x_491_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCommand_fromJson_spec__0_spec__0_spec__1(v_x_489_);
if (lean_obj_tag(v___x_491_) == 0)
{
lean_object* v_a_492_; lean_object* v___x_494_; uint8_t v_isShared_495_; uint8_t v_isSharedCheck_499_; 
v_a_492_ = lean_ctor_get(v___x_491_, 0);
v_isSharedCheck_499_ = !lean_is_exclusive(v___x_491_);
if (v_isSharedCheck_499_ == 0)
{
v___x_494_ = v___x_491_;
v_isShared_495_ = v_isSharedCheck_499_;
goto v_resetjp_493_;
}
else
{
lean_inc(v_a_492_);
lean_dec(v___x_491_);
v___x_494_ = lean_box(0);
v_isShared_495_ = v_isSharedCheck_499_;
goto v_resetjp_493_;
}
v_resetjp_493_:
{
lean_object* v___x_497_; 
if (v_isShared_495_ == 0)
{
v___x_497_ = v___x_494_;
goto v_reusejp_496_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v_a_492_);
v___x_497_ = v_reuseFailAlloc_498_;
goto v_reusejp_496_;
}
v_reusejp_496_:
{
return v___x_497_;
}
}
}
else
{
lean_object* v_a_500_; lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_508_; 
v_a_500_ = lean_ctor_get(v___x_491_, 0);
v_isSharedCheck_508_ = !lean_is_exclusive(v___x_491_);
if (v_isSharedCheck_508_ == 0)
{
v___x_502_ = v___x_491_;
v_isShared_503_ = v_isSharedCheck_508_;
goto v_resetjp_501_;
}
else
{
lean_inc(v_a_500_);
lean_dec(v___x_491_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_508_;
goto v_resetjp_501_;
}
v_resetjp_501_:
{
lean_object* v___x_504_; lean_object* v___x_506_; 
v___x_504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_504_, 0, v_a_500_);
if (v_isShared_503_ == 0)
{
lean_ctor_set(v___x_502_, 0, v___x_504_);
v___x_506_ = v___x_502_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v___x_504_);
v___x_506_ = v_reuseFailAlloc_507_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
return v___x_506_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCommand_fromJson_spec__0(lean_object* v_j_509_, lean_object* v_k_510_){
_start:
{
lean_object* v___x_511_; lean_object* v___x_512_; 
v___x_511_ = l_Lean_Json_getObjValD(v_j_509_, v_k_510_);
v___x_512_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCommand_fromJson_spec__0_spec__0(v___x_511_);
return v___x_512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCommand_fromJson_spec__0___boxed(lean_object* v_j_513_, lean_object* v_k_514_){
_start:
{
lean_object* v_res_515_; 
v_res_515_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCommand_fromJson_spec__0(v_j_513_, v_k_514_);
lean_dec_ref(v_k_514_);
return v_res_515_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonCommand_fromJson___closed__2(void){
_start:
{
uint8_t v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_521_ = 1;
v___x_522_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCommand_fromJson___closed__1));
v___x_523_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_522_, v___x_521_);
return v___x_523_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonCommand_fromJson___closed__3(void){
_start:
{
lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; 
v___x_524_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__5));
v___x_525_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCommand_fromJson___closed__2, &l_Lean_Lsp_instFromJsonCommand_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonCommand_fromJson___closed__2);
v___x_526_ = lean_string_append(v___x_525_, v___x_524_);
return v___x_526_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonCommand_fromJson___closed__5(void){
_start:
{
uint8_t v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_529_ = 1;
v___x_530_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCommand_fromJson___closed__4));
v___x_531_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_530_, v___x_529_);
return v___x_531_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonCommand_fromJson___closed__6(void){
_start:
{
lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_532_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCommand_fromJson___closed__5, &l_Lean_Lsp_instFromJsonCommand_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonCommand_fromJson___closed__5);
v___x_533_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCommand_fromJson___closed__3, &l_Lean_Lsp_instFromJsonCommand_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonCommand_fromJson___closed__3);
v___x_534_ = lean_string_append(v___x_533_, v___x_532_);
return v___x_534_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonCommand_fromJson___closed__7(void){
_start:
{
lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; 
v___x_535_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_536_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCommand_fromJson___closed__6, &l_Lean_Lsp_instFromJsonCommand_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonCommand_fromJson___closed__6);
v___x_537_ = lean_string_append(v___x_536_, v___x_535_);
return v___x_537_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonCommand_fromJson___closed__9(void){
_start:
{
uint8_t v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_540_ = 1;
v___x_541_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCommand_fromJson___closed__8));
v___x_542_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_541_, v___x_540_);
return v___x_542_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonCommand_fromJson___closed__10(void){
_start:
{
lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; 
v___x_543_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCommand_fromJson___closed__9, &l_Lean_Lsp_instFromJsonCommand_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonCommand_fromJson___closed__9);
v___x_544_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCommand_fromJson___closed__3, &l_Lean_Lsp_instFromJsonCommand_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonCommand_fromJson___closed__3);
v___x_545_ = lean_string_append(v___x_544_, v___x_543_);
return v___x_545_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonCommand_fromJson___closed__11(void){
_start:
{
lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; 
v___x_546_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_547_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCommand_fromJson___closed__10, &l_Lean_Lsp_instFromJsonCommand_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonCommand_fromJson___closed__10);
v___x_548_ = lean_string_append(v___x_547_, v___x_546_);
return v___x_548_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonCommand_fromJson___closed__14(void){
_start:
{
uint8_t v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; 
v___x_552_ = 1;
v___x_553_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCommand_fromJson___closed__13));
v___x_554_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_553_, v___x_552_);
return v___x_554_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonCommand_fromJson___closed__15(void){
_start:
{
lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; 
v___x_555_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCommand_fromJson___closed__14, &l_Lean_Lsp_instFromJsonCommand_fromJson___closed__14_once, _init_l_Lean_Lsp_instFromJsonCommand_fromJson___closed__14);
v___x_556_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCommand_fromJson___closed__3, &l_Lean_Lsp_instFromJsonCommand_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonCommand_fromJson___closed__3);
v___x_557_ = lean_string_append(v___x_556_, v___x_555_);
return v___x_557_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonCommand_fromJson___closed__16(void){
_start:
{
lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; 
v___x_558_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_559_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCommand_fromJson___closed__15, &l_Lean_Lsp_instFromJsonCommand_fromJson___closed__15_once, _init_l_Lean_Lsp_instFromJsonCommand_fromJson___closed__15);
v___x_560_ = lean_string_append(v___x_559_, v___x_558_);
return v___x_560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonCommand_fromJson(lean_object* v_json_561_){
_start:
{
lean_object* v___x_562_; lean_object* v___x_563_; 
v___x_562_ = ((lean_object*)(l_Lean_Lsp_instToJsonCommand_toJson___closed__0));
lean_inc(v_json_561_);
v___x_563_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocation_fromJson_spec__0(v_json_561_, v___x_562_);
if (lean_obj_tag(v___x_563_) == 0)
{
lean_object* v_a_564_; lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_573_; 
lean_dec(v_json_561_);
v_a_564_ = lean_ctor_get(v___x_563_, 0);
v_isSharedCheck_573_ = !lean_is_exclusive(v___x_563_);
if (v_isSharedCheck_573_ == 0)
{
v___x_566_ = v___x_563_;
v_isShared_567_ = v_isSharedCheck_573_;
goto v_resetjp_565_;
}
else
{
lean_inc(v_a_564_);
lean_dec(v___x_563_);
v___x_566_ = lean_box(0);
v_isShared_567_ = v_isSharedCheck_573_;
goto v_resetjp_565_;
}
v_resetjp_565_:
{
lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_571_; 
v___x_568_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCommand_fromJson___closed__7, &l_Lean_Lsp_instFromJsonCommand_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonCommand_fromJson___closed__7);
v___x_569_ = lean_string_append(v___x_568_, v_a_564_);
lean_dec(v_a_564_);
if (v_isShared_567_ == 0)
{
lean_ctor_set(v___x_566_, 0, v___x_569_);
v___x_571_ = v___x_566_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v___x_569_);
v___x_571_ = v_reuseFailAlloc_572_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
return v___x_571_;
}
}
}
else
{
if (lean_obj_tag(v___x_563_) == 0)
{
lean_object* v_a_574_; lean_object* v___x_576_; uint8_t v_isShared_577_; uint8_t v_isSharedCheck_581_; 
lean_dec(v_json_561_);
v_a_574_ = lean_ctor_get(v___x_563_, 0);
v_isSharedCheck_581_ = !lean_is_exclusive(v___x_563_);
if (v_isSharedCheck_581_ == 0)
{
v___x_576_ = v___x_563_;
v_isShared_577_ = v_isSharedCheck_581_;
goto v_resetjp_575_;
}
else
{
lean_inc(v_a_574_);
lean_dec(v___x_563_);
v___x_576_ = lean_box(0);
v_isShared_577_ = v_isSharedCheck_581_;
goto v_resetjp_575_;
}
v_resetjp_575_:
{
lean_object* v___x_579_; 
if (v_isShared_577_ == 0)
{
lean_ctor_set_tag(v___x_576_, 0);
v___x_579_ = v___x_576_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_580_; 
v_reuseFailAlloc_580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_580_, 0, v_a_574_);
v___x_579_ = v_reuseFailAlloc_580_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
return v___x_579_;
}
}
}
else
{
lean_object* v_a_582_; lean_object* v___x_583_; lean_object* v___x_584_; 
v_a_582_ = lean_ctor_get(v___x_563_, 0);
lean_inc(v_a_582_);
lean_dec_ref(v___x_563_);
v___x_583_ = ((lean_object*)(l_Lean_Lsp_instToJsonCommand_toJson___closed__1));
lean_inc(v_json_561_);
v___x_584_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocation_fromJson_spec__0(v_json_561_, v___x_583_);
if (lean_obj_tag(v___x_584_) == 0)
{
lean_object* v_a_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_594_; 
lean_dec(v_a_582_);
lean_dec(v_json_561_);
v_a_585_ = lean_ctor_get(v___x_584_, 0);
v_isSharedCheck_594_ = !lean_is_exclusive(v___x_584_);
if (v_isSharedCheck_594_ == 0)
{
v___x_587_ = v___x_584_;
v_isShared_588_ = v_isSharedCheck_594_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_a_585_);
lean_dec(v___x_584_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_594_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_592_; 
v___x_589_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCommand_fromJson___closed__11, &l_Lean_Lsp_instFromJsonCommand_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonCommand_fromJson___closed__11);
v___x_590_ = lean_string_append(v___x_589_, v_a_585_);
lean_dec(v_a_585_);
if (v_isShared_588_ == 0)
{
lean_ctor_set(v___x_587_, 0, v___x_590_);
v___x_592_ = v___x_587_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v___x_590_);
v___x_592_ = v_reuseFailAlloc_593_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
return v___x_592_;
}
}
}
else
{
if (lean_obj_tag(v___x_584_) == 0)
{
lean_object* v_a_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_602_; 
lean_dec(v_a_582_);
lean_dec(v_json_561_);
v_a_595_ = lean_ctor_get(v___x_584_, 0);
v_isSharedCheck_602_ = !lean_is_exclusive(v___x_584_);
if (v_isSharedCheck_602_ == 0)
{
v___x_597_ = v___x_584_;
v_isShared_598_ = v_isSharedCheck_602_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_a_595_);
lean_dec(v___x_584_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_602_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
lean_object* v___x_600_; 
if (v_isShared_598_ == 0)
{
lean_ctor_set_tag(v___x_597_, 0);
v___x_600_ = v___x_597_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v_a_595_);
v___x_600_ = v_reuseFailAlloc_601_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
return v___x_600_;
}
}
}
else
{
lean_object* v_a_603_; lean_object* v___x_604_; lean_object* v___x_605_; 
v_a_603_ = lean_ctor_get(v___x_584_, 0);
lean_inc(v_a_603_);
lean_dec_ref(v___x_584_);
v___x_604_ = ((lean_object*)(l_Lean_Lsp_instToJsonCommand_toJson___closed__2));
v___x_605_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCommand_fromJson_spec__0(v_json_561_, v___x_604_);
if (lean_obj_tag(v___x_605_) == 0)
{
lean_object* v_a_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_615_; 
lean_dec(v_a_603_);
lean_dec(v_a_582_);
v_a_606_ = lean_ctor_get(v___x_605_, 0);
v_isSharedCheck_615_ = !lean_is_exclusive(v___x_605_);
if (v_isSharedCheck_615_ == 0)
{
v___x_608_ = v___x_605_;
v_isShared_609_ = v_isSharedCheck_615_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_a_606_);
lean_dec(v___x_605_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_615_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_613_; 
v___x_610_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCommand_fromJson___closed__16, &l_Lean_Lsp_instFromJsonCommand_fromJson___closed__16_once, _init_l_Lean_Lsp_instFromJsonCommand_fromJson___closed__16);
v___x_611_ = lean_string_append(v___x_610_, v_a_606_);
lean_dec(v_a_606_);
if (v_isShared_609_ == 0)
{
lean_ctor_set(v___x_608_, 0, v___x_611_);
v___x_613_ = v___x_608_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v___x_611_);
v___x_613_ = v_reuseFailAlloc_614_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
return v___x_613_;
}
}
}
else
{
if (lean_obj_tag(v___x_605_) == 0)
{
lean_object* v_a_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_623_; 
lean_dec(v_a_603_);
lean_dec(v_a_582_);
v_a_616_ = lean_ctor_get(v___x_605_, 0);
v_isSharedCheck_623_ = !lean_is_exclusive(v___x_605_);
if (v_isSharedCheck_623_ == 0)
{
v___x_618_ = v___x_605_;
v_isShared_619_ = v_isSharedCheck_623_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_a_616_);
lean_dec(v___x_605_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_623_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
lean_object* v___x_621_; 
if (v_isShared_619_ == 0)
{
lean_ctor_set_tag(v___x_618_, 0);
v___x_621_ = v___x_618_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v_a_616_);
v___x_621_ = v_reuseFailAlloc_622_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
return v___x_621_;
}
}
}
else
{
lean_object* v_a_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_632_; 
v_a_624_ = lean_ctor_get(v___x_605_, 0);
v_isSharedCheck_632_ = !lean_is_exclusive(v___x_605_);
if (v_isSharedCheck_632_ == 0)
{
v___x_626_ = v___x_605_;
v_isShared_627_ = v_isSharedCheck_632_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_a_624_);
lean_dec(v___x_605_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_632_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
lean_object* v___x_628_; lean_object* v___x_630_; 
v___x_628_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_628_, 0, v_a_582_);
lean_ctor_set(v___x_628_, 1, v_a_603_);
lean_ctor_set(v___x_628_, 2, v_a_624_);
if (v_isShared_627_ == 0)
{
lean_ctor_set(v___x_626_, 0, v___x_628_);
v___x_630_ = v___x_626_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v___x_628_);
v___x_630_ = v_reuseFailAlloc_631_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
return v___x_630_;
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
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonSnippetString_toJson(lean_object* v_x_636_){
_start:
{
lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_637_ = ((lean_object*)(l_Lean_Lsp_instToJsonSnippetString_toJson___closed__0));
v___x_638_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_638_, 0, v_x_636_);
v___x_639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_639_, 0, v___x_637_);
lean_ctor_set(v___x_639_, 1, v___x_638_);
v___x_640_ = lean_box(0);
v___x_641_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_641_, 0, v___x_639_);
lean_ctor_set(v___x_641_, 1, v___x_640_);
v___x_642_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_642_, 0, v___x_641_);
lean_ctor_set(v___x_642_, 1, v___x_640_);
v___x_643_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__2));
v___x_644_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLocation_toJson_spec__0(v___x_642_, v___x_643_);
v___x_645_ = l_Lean_Json_mkObj(v___x_644_);
return v___x_645_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonSnippetString_fromJson___closed__2(void){
_start:
{
uint8_t v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_653_ = 1;
v___x_654_ = ((lean_object*)(l_Lean_Lsp_instFromJsonSnippetString_fromJson___closed__1));
v___x_655_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_654_, v___x_653_);
return v___x_655_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonSnippetString_fromJson___closed__3(void){
_start:
{
lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; 
v___x_656_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__5));
v___x_657_ = lean_obj_once(&l_Lean_Lsp_instFromJsonSnippetString_fromJson___closed__2, &l_Lean_Lsp_instFromJsonSnippetString_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonSnippetString_fromJson___closed__2);
v___x_658_ = lean_string_append(v___x_657_, v___x_656_);
return v___x_658_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonSnippetString_fromJson___closed__5(void){
_start:
{
uint8_t v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; 
v___x_661_ = 1;
v___x_662_ = ((lean_object*)(l_Lean_Lsp_instFromJsonSnippetString_fromJson___closed__4));
v___x_663_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_662_, v___x_661_);
return v___x_663_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonSnippetString_fromJson___closed__6(void){
_start:
{
lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; 
v___x_664_ = lean_obj_once(&l_Lean_Lsp_instFromJsonSnippetString_fromJson___closed__5, &l_Lean_Lsp_instFromJsonSnippetString_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonSnippetString_fromJson___closed__5);
v___x_665_ = lean_obj_once(&l_Lean_Lsp_instFromJsonSnippetString_fromJson___closed__3, &l_Lean_Lsp_instFromJsonSnippetString_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonSnippetString_fromJson___closed__3);
v___x_666_ = lean_string_append(v___x_665_, v___x_664_);
return v___x_666_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonSnippetString_fromJson___closed__7(void){
_start:
{
lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; 
v___x_667_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_668_ = lean_obj_once(&l_Lean_Lsp_instFromJsonSnippetString_fromJson___closed__6, &l_Lean_Lsp_instFromJsonSnippetString_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonSnippetString_fromJson___closed__6);
v___x_669_ = lean_string_append(v___x_668_, v___x_667_);
return v___x_669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonSnippetString_fromJson(lean_object* v_json_670_){
_start:
{
lean_object* v___x_671_; lean_object* v___x_672_; 
v___x_671_ = ((lean_object*)(l_Lean_Lsp_instToJsonSnippetString_toJson___closed__0));
v___x_672_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocation_fromJson_spec__0(v_json_670_, v___x_671_);
if (lean_obj_tag(v___x_672_) == 0)
{
lean_object* v_a_673_; lean_object* v___x_675_; uint8_t v_isShared_676_; uint8_t v_isSharedCheck_682_; 
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
v___x_677_ = lean_obj_once(&l_Lean_Lsp_instFromJsonSnippetString_fromJson___closed__7, &l_Lean_Lsp_instFromJsonSnippetString_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonSnippetString_fromJson___closed__7);
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
if (lean_obj_tag(v___x_672_) == 0)
{
lean_object* v_a_683_; lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_690_; 
v_a_683_ = lean_ctor_get(v___x_672_, 0);
v_isSharedCheck_690_ = !lean_is_exclusive(v___x_672_);
if (v_isSharedCheck_690_ == 0)
{
v___x_685_ = v___x_672_;
v_isShared_686_ = v_isSharedCheck_690_;
goto v_resetjp_684_;
}
else
{
lean_inc(v_a_683_);
lean_dec(v___x_672_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_690_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
lean_object* v___x_688_; 
if (v_isShared_686_ == 0)
{
lean_ctor_set_tag(v___x_685_, 0);
v___x_688_ = v___x_685_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v_a_683_);
v___x_688_ = v_reuseFailAlloc_689_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
return v___x_688_;
}
}
}
else
{
lean_object* v_a_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_698_; 
v_a_691_ = lean_ctor_get(v___x_672_, 0);
v_isSharedCheck_698_ = !lean_is_exclusive(v___x_672_);
if (v_isSharedCheck_698_ == 0)
{
v___x_693_ = v___x_672_;
v_isShared_694_ = v_isSharedCheck_698_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_a_691_);
lean_dec(v___x_672_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_698_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v___x_696_; 
if (v_isShared_694_ == 0)
{
v___x_696_ = v___x_693_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v_a_691_);
v___x_696_ = v_reuseFailAlloc_697_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
return v___x_696_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextEdit_toJson_spec__0(lean_object* v_k_701_, lean_object* v_x_702_){
_start:
{
if (lean_obj_tag(v_x_702_) == 0)
{
lean_object* v___x_703_; 
lean_dec_ref(v_k_701_);
v___x_703_ = lean_box(0);
return v___x_703_;
}
else
{
lean_object* v_val_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; 
v_val_704_ = lean_ctor_get(v_x_702_, 0);
lean_inc(v_val_704_);
lean_dec_ref(v_x_702_);
v___x_705_ = l_Lean_Lsp_instToJsonSnippetString_toJson(v_val_704_);
v___x_706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_706_, 0, v_k_701_);
lean_ctor_set(v___x_706_, 1, v___x_705_);
v___x_707_ = lean_box(0);
v___x_708_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_708_, 0, v___x_706_);
lean_ctor_set(v___x_708_, 1, v___x_707_);
return v___x_708_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextEdit_toJson_spec__1(lean_object* v_k_709_, lean_object* v_x_710_){
_start:
{
if (lean_obj_tag(v_x_710_) == 0)
{
lean_object* v___x_711_; 
lean_dec_ref(v_k_709_);
v___x_711_ = lean_box(0);
return v___x_711_;
}
else
{
lean_object* v_val_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_722_; 
v_val_712_ = lean_ctor_get(v_x_710_, 0);
v_isSharedCheck_722_ = !lean_is_exclusive(v_x_710_);
if (v_isSharedCheck_722_ == 0)
{
v___x_714_ = v_x_710_;
v_isShared_715_ = v_isSharedCheck_722_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_val_712_);
lean_dec(v_x_710_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_722_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v___x_717_; 
if (v_isShared_715_ == 0)
{
lean_ctor_set_tag(v___x_714_, 3);
v___x_717_ = v___x_714_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v_val_712_);
v___x_717_ = v_reuseFailAlloc_721_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; 
v___x_718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_718_, 0, v_k_709_);
lean_ctor_set(v___x_718_, 1, v___x_717_);
v___x_719_ = lean_box(0);
v___x_720_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_720_, 0, v___x_718_);
lean_ctor_set(v___x_720_, 1, v___x_719_);
return v___x_720_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonTextEdit_toJson(lean_object* v_x_726_){
_start:
{
lean_object* v_range_727_; lean_object* v_newText_728_; lean_object* v_leanExtSnippet_x3f_729_; lean_object* v_annotationId_x3f_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; 
v_range_727_ = lean_ctor_get(v_x_726_, 0);
lean_inc_ref(v_range_727_);
v_newText_728_ = lean_ctor_get(v_x_726_, 1);
lean_inc_ref(v_newText_728_);
v_leanExtSnippet_x3f_729_ = lean_ctor_get(v_x_726_, 2);
lean_inc(v_leanExtSnippet_x3f_729_);
v_annotationId_x3f_730_ = lean_ctor_get(v_x_726_, 3);
lean_inc(v_annotationId_x3f_730_);
lean_dec_ref(v_x_726_);
v___x_731_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__1));
v___x_732_ = l_Lean_Lsp_instToJsonRange_toJson(v_range_727_);
v___x_733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_733_, 0, v___x_731_);
lean_ctor_set(v___x_733_, 1, v___x_732_);
v___x_734_ = lean_box(0);
v___x_735_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_735_, 0, v___x_733_);
lean_ctor_set(v___x_735_, 1, v___x_734_);
v___x_736_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextEdit_toJson___closed__0));
v___x_737_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_737_, 0, v_newText_728_);
v___x_738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_738_, 0, v___x_736_);
lean_ctor_set(v___x_738_, 1, v___x_737_);
v___x_739_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_739_, 0, v___x_738_);
lean_ctor_set(v___x_739_, 1, v___x_734_);
v___x_740_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextEdit_toJson___closed__1));
v___x_741_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextEdit_toJson_spec__0(v___x_740_, v_leanExtSnippet_x3f_729_);
v___x_742_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextEdit_toJson___closed__2));
v___x_743_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextEdit_toJson_spec__1(v___x_742_, v_annotationId_x3f_730_);
v___x_744_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_744_, 0, v___x_743_);
lean_ctor_set(v___x_744_, 1, v___x_734_);
v___x_745_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_745_, 0, v___x_741_);
lean_ctor_set(v___x_745_, 1, v___x_744_);
v___x_746_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_746_, 0, v___x_739_);
lean_ctor_set(v___x_746_, 1, v___x_745_);
v___x_747_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_747_, 0, v___x_735_);
lean_ctor_set(v___x_747_, 1, v___x_746_);
v___x_748_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__2));
v___x_749_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLocation_toJson_spec__0(v___x_747_, v___x_748_);
v___x_750_ = l_Lean_Json_mkObj(v___x_749_);
return v___x_750_;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextEdit_fromJson_spec__0_spec__0(lean_object* v_x_755_){
_start:
{
if (lean_obj_tag(v_x_755_) == 0)
{
lean_object* v___x_756_; 
v___x_756_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextEdit_fromJson_spec__0_spec__0___closed__0));
return v___x_756_;
}
else
{
lean_object* v___x_757_; 
v___x_757_ = l_Lean_Lsp_instFromJsonSnippetString_fromJson(v_x_755_);
if (lean_obj_tag(v___x_757_) == 0)
{
lean_object* v_a_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_765_; 
v_a_758_ = lean_ctor_get(v___x_757_, 0);
v_isSharedCheck_765_ = !lean_is_exclusive(v___x_757_);
if (v_isSharedCheck_765_ == 0)
{
v___x_760_ = v___x_757_;
v_isShared_761_ = v_isSharedCheck_765_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_a_758_);
lean_dec(v___x_757_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_765_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
lean_object* v___x_763_; 
if (v_isShared_761_ == 0)
{
v___x_763_ = v___x_760_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v_a_758_);
v___x_763_ = v_reuseFailAlloc_764_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
return v___x_763_;
}
}
}
else
{
lean_object* v_a_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_774_; 
v_a_766_ = lean_ctor_get(v___x_757_, 0);
v_isSharedCheck_774_ = !lean_is_exclusive(v___x_757_);
if (v_isSharedCheck_774_ == 0)
{
v___x_768_ = v___x_757_;
v_isShared_769_ = v_isSharedCheck_774_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_a_766_);
lean_dec(v___x_757_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_774_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
lean_object* v___x_770_; lean_object* v___x_772_; 
v___x_770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_770_, 0, v_a_766_);
if (v_isShared_769_ == 0)
{
lean_ctor_set(v___x_768_, 0, v___x_770_);
v___x_772_ = v___x_768_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v___x_770_);
v___x_772_ = v_reuseFailAlloc_773_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
return v___x_772_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextEdit_fromJson_spec__0(lean_object* v_j_775_, lean_object* v_k_776_){
_start:
{
lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_777_ = l_Lean_Json_getObjValD(v_j_775_, v_k_776_);
v___x_778_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextEdit_fromJson_spec__0_spec__0(v___x_777_);
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextEdit_fromJson_spec__0___boxed(lean_object* v_j_779_, lean_object* v_k_780_){
_start:
{
lean_object* v_res_781_; 
v_res_781_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextEdit_fromJson_spec__0(v_j_779_, v_k_780_);
lean_dec_ref(v_k_780_);
return v_res_781_;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextEdit_fromJson_spec__1_spec__2(lean_object* v_x_782_){
_start:
{
if (lean_obj_tag(v_x_782_) == 0)
{
lean_object* v___x_783_; 
v___x_783_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextEdit_fromJson_spec__0_spec__0___closed__0));
return v___x_783_;
}
else
{
lean_object* v___x_784_; 
v___x_784_ = l_Lean_Json_getStr_x3f(v_x_782_);
if (lean_obj_tag(v___x_784_) == 0)
{
lean_object* v_a_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_792_; 
v_a_785_ = lean_ctor_get(v___x_784_, 0);
v_isSharedCheck_792_ = !lean_is_exclusive(v___x_784_);
if (v_isSharedCheck_792_ == 0)
{
v___x_787_ = v___x_784_;
v_isShared_788_ = v_isSharedCheck_792_;
goto v_resetjp_786_;
}
else
{
lean_inc(v_a_785_);
lean_dec(v___x_784_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_792_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
lean_object* v___x_790_; 
if (v_isShared_788_ == 0)
{
v___x_790_ = v___x_787_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v_a_785_);
v___x_790_ = v_reuseFailAlloc_791_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
return v___x_790_;
}
}
}
else
{
lean_object* v_a_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_801_; 
v_a_793_ = lean_ctor_get(v___x_784_, 0);
v_isSharedCheck_801_ = !lean_is_exclusive(v___x_784_);
if (v_isSharedCheck_801_ == 0)
{
v___x_795_ = v___x_784_;
v_isShared_796_ = v_isSharedCheck_801_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_a_793_);
lean_dec(v___x_784_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_801_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v___x_797_; lean_object* v___x_799_; 
v___x_797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_797_, 0, v_a_793_);
if (v_isShared_796_ == 0)
{
lean_ctor_set(v___x_795_, 0, v___x_797_);
v___x_799_ = v___x_795_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v___x_797_);
v___x_799_ = v_reuseFailAlloc_800_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
return v___x_799_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextEdit_fromJson_spec__1(lean_object* v_j_802_, lean_object* v_k_803_){
_start:
{
lean_object* v___x_804_; lean_object* v___x_805_; 
v___x_804_ = l_Lean_Json_getObjValD(v_j_802_, v_k_803_);
v___x_805_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextEdit_fromJson_spec__1_spec__2(v___x_804_);
return v___x_805_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextEdit_fromJson_spec__1___boxed(lean_object* v_j_806_, lean_object* v_k_807_){
_start:
{
lean_object* v_res_808_; 
v_res_808_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextEdit_fromJson_spec__1(v_j_806_, v_k_807_);
lean_dec_ref(v_k_807_);
return v_res_808_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__2(void){
_start:
{
uint8_t v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; 
v___x_814_ = 1;
v___x_815_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__1));
v___x_816_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_815_, v___x_814_);
return v___x_816_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__3(void){
_start:
{
lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; 
v___x_817_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__5));
v___x_818_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__2, &l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__2);
v___x_819_ = lean_string_append(v___x_818_, v___x_817_);
return v___x_819_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__4(void){
_start:
{
lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; 
v___x_820_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLocation_fromJson___closed__13, &l_Lean_Lsp_instFromJsonLocation_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonLocation_fromJson___closed__13);
v___x_821_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__3, &l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__3);
v___x_822_ = lean_string_append(v___x_821_, v___x_820_);
return v___x_822_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__5(void){
_start:
{
lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; 
v___x_823_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_824_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__4, &l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__4);
v___x_825_ = lean_string_append(v___x_824_, v___x_823_);
return v___x_825_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__7(void){
_start:
{
uint8_t v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; 
v___x_828_ = 1;
v___x_829_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__6));
v___x_830_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_829_, v___x_828_);
return v___x_830_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__8(void){
_start:
{
lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; 
v___x_831_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__7, &l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__7);
v___x_832_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__3, &l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__3);
v___x_833_ = lean_string_append(v___x_832_, v___x_831_);
return v___x_833_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__9(void){
_start:
{
lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; 
v___x_834_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_835_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__8, &l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__8);
v___x_836_ = lean_string_append(v___x_835_, v___x_834_);
return v___x_836_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__12(void){
_start:
{
uint8_t v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; 
v___x_840_ = 1;
v___x_841_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__11));
v___x_842_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_841_, v___x_840_);
return v___x_842_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__13(void){
_start:
{
lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; 
v___x_843_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__12, &l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__12);
v___x_844_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__3, &l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__3);
v___x_845_ = lean_string_append(v___x_844_, v___x_843_);
return v___x_845_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__14(void){
_start:
{
lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; 
v___x_846_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_847_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__13, &l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__13);
v___x_848_ = lean_string_append(v___x_847_, v___x_846_);
return v___x_848_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__17(void){
_start:
{
uint8_t v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; 
v___x_852_ = 1;
v___x_853_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__16));
v___x_854_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_853_, v___x_852_);
return v___x_854_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__18(void){
_start:
{
lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; 
v___x_855_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__17, &l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__17_once, _init_l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__17);
v___x_856_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__3, &l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__3);
v___x_857_ = lean_string_append(v___x_856_, v___x_855_);
return v___x_857_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__19(void){
_start:
{
lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; 
v___x_858_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_859_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__18, &l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__18_once, _init_l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__18);
v___x_860_ = lean_string_append(v___x_859_, v___x_858_);
return v___x_860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonTextEdit_fromJson(lean_object* v_json_861_){
_start:
{
lean_object* v___x_862_; lean_object* v___x_863_; 
v___x_862_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__1));
lean_inc(v_json_861_);
v___x_863_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocation_fromJson_spec__1(v_json_861_, v___x_862_);
if (lean_obj_tag(v___x_863_) == 0)
{
lean_object* v_a_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_873_; 
lean_dec(v_json_861_);
v_a_864_ = lean_ctor_get(v___x_863_, 0);
v_isSharedCheck_873_ = !lean_is_exclusive(v___x_863_);
if (v_isSharedCheck_873_ == 0)
{
v___x_866_ = v___x_863_;
v_isShared_867_ = v_isSharedCheck_873_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_a_864_);
lean_dec(v___x_863_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_873_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_871_; 
v___x_868_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__5, &l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__5);
v___x_869_ = lean_string_append(v___x_868_, v_a_864_);
lean_dec(v_a_864_);
if (v_isShared_867_ == 0)
{
lean_ctor_set(v___x_866_, 0, v___x_869_);
v___x_871_ = v___x_866_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v___x_869_);
v___x_871_ = v_reuseFailAlloc_872_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
return v___x_871_;
}
}
}
else
{
if (lean_obj_tag(v___x_863_) == 0)
{
lean_object* v_a_874_; lean_object* v___x_876_; uint8_t v_isShared_877_; uint8_t v_isSharedCheck_881_; 
lean_dec(v_json_861_);
v_a_874_ = lean_ctor_get(v___x_863_, 0);
v_isSharedCheck_881_ = !lean_is_exclusive(v___x_863_);
if (v_isSharedCheck_881_ == 0)
{
v___x_876_ = v___x_863_;
v_isShared_877_ = v_isSharedCheck_881_;
goto v_resetjp_875_;
}
else
{
lean_inc(v_a_874_);
lean_dec(v___x_863_);
v___x_876_ = lean_box(0);
v_isShared_877_ = v_isSharedCheck_881_;
goto v_resetjp_875_;
}
v_resetjp_875_:
{
lean_object* v___x_879_; 
if (v_isShared_877_ == 0)
{
lean_ctor_set_tag(v___x_876_, 0);
v___x_879_ = v___x_876_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v_a_874_);
v___x_879_ = v_reuseFailAlloc_880_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
return v___x_879_;
}
}
}
else
{
lean_object* v_a_882_; lean_object* v___x_883_; lean_object* v___x_884_; 
v_a_882_ = lean_ctor_get(v___x_863_, 0);
lean_inc(v_a_882_);
lean_dec_ref(v___x_863_);
v___x_883_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextEdit_toJson___closed__0));
lean_inc(v_json_861_);
v___x_884_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocation_fromJson_spec__0(v_json_861_, v___x_883_);
if (lean_obj_tag(v___x_884_) == 0)
{
lean_object* v_a_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_894_; 
lean_dec(v_a_882_);
lean_dec(v_json_861_);
v_a_885_ = lean_ctor_get(v___x_884_, 0);
v_isSharedCheck_894_ = !lean_is_exclusive(v___x_884_);
if (v_isSharedCheck_894_ == 0)
{
v___x_887_ = v___x_884_;
v_isShared_888_ = v_isSharedCheck_894_;
goto v_resetjp_886_;
}
else
{
lean_inc(v_a_885_);
lean_dec(v___x_884_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_894_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_892_; 
v___x_889_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__9, &l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__9);
v___x_890_ = lean_string_append(v___x_889_, v_a_885_);
lean_dec(v_a_885_);
if (v_isShared_888_ == 0)
{
lean_ctor_set(v___x_887_, 0, v___x_890_);
v___x_892_ = v___x_887_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v___x_890_);
v___x_892_ = v_reuseFailAlloc_893_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
return v___x_892_;
}
}
}
else
{
if (lean_obj_tag(v___x_884_) == 0)
{
lean_object* v_a_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_902_; 
lean_dec(v_a_882_);
lean_dec(v_json_861_);
v_a_895_ = lean_ctor_get(v___x_884_, 0);
v_isSharedCheck_902_ = !lean_is_exclusive(v___x_884_);
if (v_isSharedCheck_902_ == 0)
{
v___x_897_ = v___x_884_;
v_isShared_898_ = v_isSharedCheck_902_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_a_895_);
lean_dec(v___x_884_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_902_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v___x_900_; 
if (v_isShared_898_ == 0)
{
lean_ctor_set_tag(v___x_897_, 0);
v___x_900_ = v___x_897_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v_a_895_);
v___x_900_ = v_reuseFailAlloc_901_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
return v___x_900_;
}
}
}
else
{
lean_object* v_a_903_; lean_object* v___x_904_; lean_object* v___x_905_; 
v_a_903_ = lean_ctor_get(v___x_884_, 0);
lean_inc(v_a_903_);
lean_dec_ref(v___x_884_);
v___x_904_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextEdit_toJson___closed__1));
lean_inc(v_json_861_);
v___x_905_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextEdit_fromJson_spec__0(v_json_861_, v___x_904_);
if (lean_obj_tag(v___x_905_) == 0)
{
lean_object* v_a_906_; lean_object* v___x_908_; uint8_t v_isShared_909_; uint8_t v_isSharedCheck_915_; 
lean_dec(v_a_903_);
lean_dec(v_a_882_);
lean_dec(v_json_861_);
v_a_906_ = lean_ctor_get(v___x_905_, 0);
v_isSharedCheck_915_ = !lean_is_exclusive(v___x_905_);
if (v_isSharedCheck_915_ == 0)
{
v___x_908_ = v___x_905_;
v_isShared_909_ = v_isSharedCheck_915_;
goto v_resetjp_907_;
}
else
{
lean_inc(v_a_906_);
lean_dec(v___x_905_);
v___x_908_ = lean_box(0);
v_isShared_909_ = v_isSharedCheck_915_;
goto v_resetjp_907_;
}
v_resetjp_907_:
{
lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_913_; 
v___x_910_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__14, &l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__14_once, _init_l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__14);
v___x_911_ = lean_string_append(v___x_910_, v_a_906_);
lean_dec(v_a_906_);
if (v_isShared_909_ == 0)
{
lean_ctor_set(v___x_908_, 0, v___x_911_);
v___x_913_ = v___x_908_;
goto v_reusejp_912_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v___x_911_);
v___x_913_ = v_reuseFailAlloc_914_;
goto v_reusejp_912_;
}
v_reusejp_912_:
{
return v___x_913_;
}
}
}
else
{
if (lean_obj_tag(v___x_905_) == 0)
{
lean_object* v_a_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_923_; 
lean_dec(v_a_903_);
lean_dec(v_a_882_);
lean_dec(v_json_861_);
v_a_916_ = lean_ctor_get(v___x_905_, 0);
v_isSharedCheck_923_ = !lean_is_exclusive(v___x_905_);
if (v_isSharedCheck_923_ == 0)
{
v___x_918_ = v___x_905_;
v_isShared_919_ = v_isSharedCheck_923_;
goto v_resetjp_917_;
}
else
{
lean_inc(v_a_916_);
lean_dec(v___x_905_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_923_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
lean_object* v___x_921_; 
if (v_isShared_919_ == 0)
{
lean_ctor_set_tag(v___x_918_, 0);
v___x_921_ = v___x_918_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v_a_916_);
v___x_921_ = v_reuseFailAlloc_922_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
return v___x_921_;
}
}
}
else
{
lean_object* v_a_924_; lean_object* v___x_925_; lean_object* v___x_926_; 
v_a_924_ = lean_ctor_get(v___x_905_, 0);
lean_inc(v_a_924_);
lean_dec_ref(v___x_905_);
v___x_925_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextEdit_toJson___closed__2));
v___x_926_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextEdit_fromJson_spec__1(v_json_861_, v___x_925_);
if (lean_obj_tag(v___x_926_) == 0)
{
lean_object* v_a_927_; lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_936_; 
lean_dec(v_a_924_);
lean_dec(v_a_903_);
lean_dec(v_a_882_);
v_a_927_ = lean_ctor_get(v___x_926_, 0);
v_isSharedCheck_936_ = !lean_is_exclusive(v___x_926_);
if (v_isSharedCheck_936_ == 0)
{
v___x_929_ = v___x_926_;
v_isShared_930_ = v_isSharedCheck_936_;
goto v_resetjp_928_;
}
else
{
lean_inc(v_a_927_);
lean_dec(v___x_926_);
v___x_929_ = lean_box(0);
v_isShared_930_ = v_isSharedCheck_936_;
goto v_resetjp_928_;
}
v_resetjp_928_:
{
lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_934_; 
v___x_931_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__19, &l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__19_once, _init_l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__19);
v___x_932_ = lean_string_append(v___x_931_, v_a_927_);
lean_dec(v_a_927_);
if (v_isShared_930_ == 0)
{
lean_ctor_set(v___x_929_, 0, v___x_932_);
v___x_934_ = v___x_929_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v___x_932_);
v___x_934_ = v_reuseFailAlloc_935_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
return v___x_934_;
}
}
}
else
{
if (lean_obj_tag(v___x_926_) == 0)
{
lean_object* v_a_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_944_; 
lean_dec(v_a_924_);
lean_dec(v_a_903_);
lean_dec(v_a_882_);
v_a_937_ = lean_ctor_get(v___x_926_, 0);
v_isSharedCheck_944_ = !lean_is_exclusive(v___x_926_);
if (v_isSharedCheck_944_ == 0)
{
v___x_939_ = v___x_926_;
v_isShared_940_ = v_isSharedCheck_944_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_a_937_);
lean_dec(v___x_926_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_944_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v___x_942_; 
if (v_isShared_940_ == 0)
{
lean_ctor_set_tag(v___x_939_, 0);
v___x_942_ = v___x_939_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v_a_937_);
v___x_942_ = v_reuseFailAlloc_943_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
return v___x_942_;
}
}
}
else
{
lean_object* v_a_945_; lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_953_; 
v_a_945_ = lean_ctor_get(v___x_926_, 0);
v_isSharedCheck_953_ = !lean_is_exclusive(v___x_926_);
if (v_isSharedCheck_953_ == 0)
{
v___x_947_ = v___x_926_;
v_isShared_948_ = v_isSharedCheck_953_;
goto v_resetjp_946_;
}
else
{
lean_inc(v_a_945_);
lean_dec(v___x_926_);
v___x_947_ = lean_box(0);
v_isShared_948_ = v_isSharedCheck_953_;
goto v_resetjp_946_;
}
v_resetjp_946_:
{
lean_object* v___x_949_; lean_object* v___x_951_; 
v___x_949_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_949_, 0, v_a_882_);
lean_ctor_set(v___x_949_, 1, v_a_903_);
lean_ctor_set(v___x_949_, 2, v_a_924_);
lean_ctor_set(v___x_949_, 3, v_a_945_);
if (v_isShared_948_ == 0)
{
lean_ctor_set(v___x_947_, 0, v___x_949_);
v___x_951_ = v___x_947_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v___x_949_);
v___x_951_ = v_reuseFailAlloc_952_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
return v___x_951_;
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
LEAN_EXPORT lean_object* l_Lean_Lsp_instCoeTextEditTextEditBatch___lam__0(lean_object* v_te_967_){
_start:
{
lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; 
v___x_968_ = lean_unsigned_to_nat(1u);
v___x_969_ = lean_mk_empty_array_with_capacity(v___x_968_);
v___x_970_ = lean_array_push(v___x_969_, v_te_967_);
return v___x_970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonTextDocumentIdentifier_toJson(lean_object* v_x_973_){
_start:
{
lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; 
v___x_974_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__0));
v___x_975_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_975_, 0, v_x_973_);
v___x_976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_976_, 0, v___x_974_);
lean_ctor_set(v___x_976_, 1, v___x_975_);
v___x_977_ = lean_box(0);
v___x_978_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_978_, 0, v___x_976_);
lean_ctor_set(v___x_978_, 1, v___x_977_);
v___x_979_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_979_, 0, v___x_978_);
lean_ctor_set(v___x_979_, 1, v___x_977_);
v___x_980_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__2));
v___x_981_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLocation_toJson_spec__0(v___x_979_, v___x_980_);
v___x_982_ = l_Lean_Json_mkObj(v___x_981_);
return v___x_982_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentIdentifier_fromJson___closed__2(void){
_start:
{
uint8_t v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; 
v___x_990_ = 1;
v___x_991_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentIdentifier_fromJson___closed__1));
v___x_992_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_991_, v___x_990_);
return v___x_992_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentIdentifier_fromJson___closed__3(void){
_start:
{
lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; 
v___x_993_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__5));
v___x_994_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentIdentifier_fromJson___closed__2, &l_Lean_Lsp_instFromJsonTextDocumentIdentifier_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonTextDocumentIdentifier_fromJson___closed__2);
v___x_995_ = lean_string_append(v___x_994_, v___x_993_);
return v___x_995_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentIdentifier_fromJson___closed__4(void){
_start:
{
lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; 
v___x_996_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLocation_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLocation_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLocation_fromJson___closed__8);
v___x_997_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentIdentifier_fromJson___closed__3, &l_Lean_Lsp_instFromJsonTextDocumentIdentifier_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonTextDocumentIdentifier_fromJson___closed__3);
v___x_998_ = lean_string_append(v___x_997_, v___x_996_);
return v___x_998_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentIdentifier_fromJson___closed__5(void){
_start:
{
lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; 
v___x_999_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_1000_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentIdentifier_fromJson___closed__4, &l_Lean_Lsp_instFromJsonTextDocumentIdentifier_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonTextDocumentIdentifier_fromJson___closed__4);
v___x_1001_ = lean_string_append(v___x_1000_, v___x_999_);
return v___x_1001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonTextDocumentIdentifier_fromJson(lean_object* v_json_1002_){
_start:
{
lean_object* v___x_1003_; lean_object* v___x_1004_; 
v___x_1003_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__0));
v___x_1004_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocation_fromJson_spec__0(v_json_1002_, v___x_1003_);
if (lean_obj_tag(v___x_1004_) == 0)
{
lean_object* v_a_1005_; lean_object* v___x_1007_; uint8_t v_isShared_1008_; uint8_t v_isSharedCheck_1014_; 
v_a_1005_ = lean_ctor_get(v___x_1004_, 0);
v_isSharedCheck_1014_ = !lean_is_exclusive(v___x_1004_);
if (v_isSharedCheck_1014_ == 0)
{
v___x_1007_ = v___x_1004_;
v_isShared_1008_ = v_isSharedCheck_1014_;
goto v_resetjp_1006_;
}
else
{
lean_inc(v_a_1005_);
lean_dec(v___x_1004_);
v___x_1007_ = lean_box(0);
v_isShared_1008_ = v_isSharedCheck_1014_;
goto v_resetjp_1006_;
}
v_resetjp_1006_:
{
lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1012_; 
v___x_1009_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentIdentifier_fromJson___closed__5, &l_Lean_Lsp_instFromJsonTextDocumentIdentifier_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonTextDocumentIdentifier_fromJson___closed__5);
v___x_1010_ = lean_string_append(v___x_1009_, v_a_1005_);
lean_dec(v_a_1005_);
if (v_isShared_1008_ == 0)
{
lean_ctor_set(v___x_1007_, 0, v___x_1010_);
v___x_1012_ = v___x_1007_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v___x_1010_);
v___x_1012_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
return v___x_1012_;
}
}
}
else
{
if (lean_obj_tag(v___x_1004_) == 0)
{
lean_object* v_a_1015_; lean_object* v___x_1017_; uint8_t v_isShared_1018_; uint8_t v_isSharedCheck_1022_; 
v_a_1015_ = lean_ctor_get(v___x_1004_, 0);
v_isSharedCheck_1022_ = !lean_is_exclusive(v___x_1004_);
if (v_isSharedCheck_1022_ == 0)
{
v___x_1017_ = v___x_1004_;
v_isShared_1018_ = v_isSharedCheck_1022_;
goto v_resetjp_1016_;
}
else
{
lean_inc(v_a_1015_);
lean_dec(v___x_1004_);
v___x_1017_ = lean_box(0);
v_isShared_1018_ = v_isSharedCheck_1022_;
goto v_resetjp_1016_;
}
v_resetjp_1016_:
{
lean_object* v___x_1020_; 
if (v_isShared_1018_ == 0)
{
lean_ctor_set_tag(v___x_1017_, 0);
v___x_1020_ = v___x_1017_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v_a_1015_);
v___x_1020_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
return v___x_1020_;
}
}
}
else
{
lean_object* v_a_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1030_; 
v_a_1023_ = lean_ctor_get(v___x_1004_, 0);
v_isSharedCheck_1030_ = !lean_is_exclusive(v___x_1004_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1025_ = v___x_1004_;
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_a_1023_);
lean_dec(v___x_1004_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v___x_1028_; 
if (v_isShared_1026_ == 0)
{
v___x_1028_ = v___x_1025_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v_a_1023_);
v___x_1028_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
return v___x_1028_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonVersionedTextDocumentIdentifier_toJson_spec__0(lean_object* v_k_1033_, lean_object* v_x_1034_){
_start:
{
if (lean_obj_tag(v_x_1034_) == 0)
{
lean_object* v___x_1035_; 
lean_dec_ref(v_k_1033_);
v___x_1035_ = lean_box(0);
return v___x_1035_;
}
else
{
lean_object* v_val_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1047_; 
v_val_1036_ = lean_ctor_get(v_x_1034_, 0);
v_isSharedCheck_1047_ = !lean_is_exclusive(v_x_1034_);
if (v_isSharedCheck_1047_ == 0)
{
v___x_1038_ = v_x_1034_;
v_isShared_1039_ = v_isSharedCheck_1047_;
goto v_resetjp_1037_;
}
else
{
lean_inc(v_val_1036_);
lean_dec(v_x_1034_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1047_;
goto v_resetjp_1037_;
}
v_resetjp_1037_:
{
lean_object* v___x_1040_; lean_object* v___x_1042_; 
v___x_1040_ = l_Lean_JsonNumber_fromNat(v_val_1036_);
if (v_isShared_1039_ == 0)
{
lean_ctor_set_tag(v___x_1038_, 2);
lean_ctor_set(v___x_1038_, 0, v___x_1040_);
v___x_1042_ = v___x_1038_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1046_; 
v_reuseFailAlloc_1046_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1046_, 0, v___x_1040_);
v___x_1042_ = v_reuseFailAlloc_1046_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; 
v___x_1043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1043_, 0, v_k_1033_);
lean_ctor_set(v___x_1043_, 1, v___x_1042_);
v___x_1044_ = lean_box(0);
v___x_1045_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1045_, 0, v___x_1043_);
lean_ctor_set(v___x_1045_, 1, v___x_1044_);
return v___x_1045_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonVersionedTextDocumentIdentifier_toJson(lean_object* v_x_1049_){
_start:
{
lean_object* v_uri_1050_; lean_object* v_version_x3f_1051_; lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1069_; 
v_uri_1050_ = lean_ctor_get(v_x_1049_, 0);
v_version_x3f_1051_ = lean_ctor_get(v_x_1049_, 1);
v_isSharedCheck_1069_ = !lean_is_exclusive(v_x_1049_);
if (v_isSharedCheck_1069_ == 0)
{
v___x_1053_ = v_x_1049_;
v_isShared_1054_ = v_isSharedCheck_1069_;
goto v_resetjp_1052_;
}
else
{
lean_inc(v_version_x3f_1051_);
lean_inc(v_uri_1050_);
lean_dec(v_x_1049_);
v___x_1053_ = lean_box(0);
v_isShared_1054_ = v_isSharedCheck_1069_;
goto v_resetjp_1052_;
}
v_resetjp_1052_:
{
lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1058_; 
v___x_1055_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__0));
v___x_1056_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1056_, 0, v_uri_1050_);
if (v_isShared_1054_ == 0)
{
lean_ctor_set(v___x_1053_, 1, v___x_1056_);
lean_ctor_set(v___x_1053_, 0, v___x_1055_);
v___x_1058_ = v___x_1053_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v___x_1055_);
lean_ctor_set(v_reuseFailAlloc_1068_, 1, v___x_1056_);
v___x_1058_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; 
v___x_1059_ = lean_box(0);
v___x_1060_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1060_, 0, v___x_1058_);
lean_ctor_set(v___x_1060_, 1, v___x_1059_);
v___x_1061_ = ((lean_object*)(l_Lean_Lsp_instToJsonVersionedTextDocumentIdentifier_toJson___closed__0));
v___x_1062_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonVersionedTextDocumentIdentifier_toJson_spec__0(v___x_1061_, v_version_x3f_1051_);
v___x_1063_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1063_, 0, v___x_1062_);
lean_ctor_set(v___x_1063_, 1, v___x_1059_);
v___x_1064_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1064_, 0, v___x_1060_);
lean_ctor_set(v___x_1064_, 1, v___x_1063_);
v___x_1065_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__2));
v___x_1066_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLocation_toJson_spec__0(v___x_1064_, v___x_1065_);
v___x_1067_ = l_Lean_Json_mkObj(v___x_1066_);
return v___x_1067_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson_spec__0_spec__0(lean_object* v_x_1074_){
_start:
{
if (lean_obj_tag(v_x_1074_) == 0)
{
lean_object* v___x_1075_; 
v___x_1075_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson_spec__0_spec__0___closed__0));
return v___x_1075_;
}
else
{
lean_object* v___x_1076_; 
v___x_1076_ = l_Lean_Json_getNat_x3f(v_x_1074_);
if (lean_obj_tag(v___x_1076_) == 0)
{
lean_object* v_a_1077_; lean_object* v___x_1079_; uint8_t v_isShared_1080_; uint8_t v_isSharedCheck_1084_; 
v_a_1077_ = lean_ctor_get(v___x_1076_, 0);
v_isSharedCheck_1084_ = !lean_is_exclusive(v___x_1076_);
if (v_isSharedCheck_1084_ == 0)
{
v___x_1079_ = v___x_1076_;
v_isShared_1080_ = v_isSharedCheck_1084_;
goto v_resetjp_1078_;
}
else
{
lean_inc(v_a_1077_);
lean_dec(v___x_1076_);
v___x_1079_ = lean_box(0);
v_isShared_1080_ = v_isSharedCheck_1084_;
goto v_resetjp_1078_;
}
v_resetjp_1078_:
{
lean_object* v___x_1082_; 
if (v_isShared_1080_ == 0)
{
v___x_1082_ = v___x_1079_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1083_; 
v_reuseFailAlloc_1083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1083_, 0, v_a_1077_);
v___x_1082_ = v_reuseFailAlloc_1083_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
return v___x_1082_;
}
}
}
else
{
lean_object* v_a_1085_; lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1093_; 
v_a_1085_ = lean_ctor_get(v___x_1076_, 0);
v_isSharedCheck_1093_ = !lean_is_exclusive(v___x_1076_);
if (v_isSharedCheck_1093_ == 0)
{
v___x_1087_ = v___x_1076_;
v_isShared_1088_ = v_isSharedCheck_1093_;
goto v_resetjp_1086_;
}
else
{
lean_inc(v_a_1085_);
lean_dec(v___x_1076_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1093_;
goto v_resetjp_1086_;
}
v_resetjp_1086_:
{
lean_object* v___x_1089_; lean_object* v___x_1091_; 
v___x_1089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1089_, 0, v_a_1085_);
if (v_isShared_1088_ == 0)
{
lean_ctor_set(v___x_1087_, 0, v___x_1089_);
v___x_1091_ = v___x_1087_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v___x_1089_);
v___x_1091_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
return v___x_1091_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson_spec__0(lean_object* v_j_1094_, lean_object* v_k_1095_){
_start:
{
lean_object* v___x_1096_; lean_object* v___x_1097_; 
v___x_1096_ = l_Lean_Json_getObjValD(v_j_1094_, v_k_1095_);
v___x_1097_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson_spec__0_spec__0(v___x_1096_);
return v___x_1097_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson_spec__0___boxed(lean_object* v_j_1098_, lean_object* v_k_1099_){
_start:
{
lean_object* v_res_1100_; 
v_res_1100_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson_spec__0(v_j_1098_, v_k_1099_);
lean_dec_ref(v_k_1099_);
return v_res_1100_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__2(void){
_start:
{
uint8_t v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; 
v___x_1106_ = 1;
v___x_1107_ = ((lean_object*)(l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__1));
v___x_1108_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1107_, v___x_1106_);
return v___x_1108_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__3(void){
_start:
{
lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; 
v___x_1109_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__5));
v___x_1110_ = lean_obj_once(&l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__2, &l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__2);
v___x_1111_ = lean_string_append(v___x_1110_, v___x_1109_);
return v___x_1111_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__4(void){
_start:
{
lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; 
v___x_1112_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLocation_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLocation_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLocation_fromJson___closed__8);
v___x_1113_ = lean_obj_once(&l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__3, &l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__3);
v___x_1114_ = lean_string_append(v___x_1113_, v___x_1112_);
return v___x_1114_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__5(void){
_start:
{
lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; 
v___x_1115_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_1116_ = lean_obj_once(&l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__4, &l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__4);
v___x_1117_ = lean_string_append(v___x_1116_, v___x_1115_);
return v___x_1117_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__8(void){
_start:
{
uint8_t v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; 
v___x_1121_ = 1;
v___x_1122_ = ((lean_object*)(l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__7));
v___x_1123_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1122_, v___x_1121_);
return v___x_1123_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__9(void){
_start:
{
lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; 
v___x_1124_ = lean_obj_once(&l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__8, &l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__8);
v___x_1125_ = lean_obj_once(&l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__3, &l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__3);
v___x_1126_ = lean_string_append(v___x_1125_, v___x_1124_);
return v___x_1126_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__10(void){
_start:
{
lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; 
v___x_1127_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_1128_ = lean_obj_once(&l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__9, &l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__9);
v___x_1129_ = lean_string_append(v___x_1128_, v___x_1127_);
return v___x_1129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson(lean_object* v_json_1130_){
_start:
{
lean_object* v___x_1131_; lean_object* v___x_1132_; 
v___x_1131_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__0));
lean_inc(v_json_1130_);
v___x_1132_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocation_fromJson_spec__0(v_json_1130_, v___x_1131_);
if (lean_obj_tag(v___x_1132_) == 0)
{
lean_object* v_a_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1142_; 
lean_dec(v_json_1130_);
v_a_1133_ = lean_ctor_get(v___x_1132_, 0);
v_isSharedCheck_1142_ = !lean_is_exclusive(v___x_1132_);
if (v_isSharedCheck_1142_ == 0)
{
v___x_1135_ = v___x_1132_;
v_isShared_1136_ = v_isSharedCheck_1142_;
goto v_resetjp_1134_;
}
else
{
lean_inc(v_a_1133_);
lean_dec(v___x_1132_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1142_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1140_; 
v___x_1137_ = lean_obj_once(&l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__5, &l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__5);
v___x_1138_ = lean_string_append(v___x_1137_, v_a_1133_);
lean_dec(v_a_1133_);
if (v_isShared_1136_ == 0)
{
lean_ctor_set(v___x_1135_, 0, v___x_1138_);
v___x_1140_ = v___x_1135_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v___x_1138_);
v___x_1140_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
return v___x_1140_;
}
}
}
else
{
if (lean_obj_tag(v___x_1132_) == 0)
{
lean_object* v_a_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1150_; 
lean_dec(v_json_1130_);
v_a_1143_ = lean_ctor_get(v___x_1132_, 0);
v_isSharedCheck_1150_ = !lean_is_exclusive(v___x_1132_);
if (v_isSharedCheck_1150_ == 0)
{
v___x_1145_ = v___x_1132_;
v_isShared_1146_ = v_isSharedCheck_1150_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_a_1143_);
lean_dec(v___x_1132_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1150_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
lean_object* v___x_1148_; 
if (v_isShared_1146_ == 0)
{
lean_ctor_set_tag(v___x_1145_, 0);
v___x_1148_ = v___x_1145_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v_a_1143_);
v___x_1148_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
return v___x_1148_;
}
}
}
else
{
lean_object* v_a_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; 
v_a_1151_ = lean_ctor_get(v___x_1132_, 0);
lean_inc(v_a_1151_);
lean_dec_ref(v___x_1132_);
v___x_1152_ = ((lean_object*)(l_Lean_Lsp_instToJsonVersionedTextDocumentIdentifier_toJson___closed__0));
v___x_1153_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson_spec__0(v_json_1130_, v___x_1152_);
if (lean_obj_tag(v___x_1153_) == 0)
{
lean_object* v_a_1154_; lean_object* v___x_1156_; uint8_t v_isShared_1157_; uint8_t v_isSharedCheck_1163_; 
lean_dec(v_a_1151_);
v_a_1154_ = lean_ctor_get(v___x_1153_, 0);
v_isSharedCheck_1163_ = !lean_is_exclusive(v___x_1153_);
if (v_isSharedCheck_1163_ == 0)
{
v___x_1156_ = v___x_1153_;
v_isShared_1157_ = v_isSharedCheck_1163_;
goto v_resetjp_1155_;
}
else
{
lean_inc(v_a_1154_);
lean_dec(v___x_1153_);
v___x_1156_ = lean_box(0);
v_isShared_1157_ = v_isSharedCheck_1163_;
goto v_resetjp_1155_;
}
v_resetjp_1155_:
{
lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1161_; 
v___x_1158_ = lean_obj_once(&l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__10, &l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__10);
v___x_1159_ = lean_string_append(v___x_1158_, v_a_1154_);
lean_dec(v_a_1154_);
if (v_isShared_1157_ == 0)
{
lean_ctor_set(v___x_1156_, 0, v___x_1159_);
v___x_1161_ = v___x_1156_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v___x_1159_);
v___x_1161_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
return v___x_1161_;
}
}
}
else
{
if (lean_obj_tag(v___x_1153_) == 0)
{
lean_object* v_a_1164_; lean_object* v___x_1166_; uint8_t v_isShared_1167_; uint8_t v_isSharedCheck_1171_; 
lean_dec(v_a_1151_);
v_a_1164_ = lean_ctor_get(v___x_1153_, 0);
v_isSharedCheck_1171_ = !lean_is_exclusive(v___x_1153_);
if (v_isSharedCheck_1171_ == 0)
{
v___x_1166_ = v___x_1153_;
v_isShared_1167_ = v_isSharedCheck_1171_;
goto v_resetjp_1165_;
}
else
{
lean_inc(v_a_1164_);
lean_dec(v___x_1153_);
v___x_1166_ = lean_box(0);
v_isShared_1167_ = v_isSharedCheck_1171_;
goto v_resetjp_1165_;
}
v_resetjp_1165_:
{
lean_object* v___x_1169_; 
if (v_isShared_1167_ == 0)
{
lean_ctor_set_tag(v___x_1166_, 0);
v___x_1169_ = v___x_1166_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v_a_1164_);
v___x_1169_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
return v___x_1169_;
}
}
}
else
{
lean_object* v_a_1172_; lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1180_; 
v_a_1172_ = lean_ctor_get(v___x_1153_, 0);
v_isSharedCheck_1180_ = !lean_is_exclusive(v___x_1153_);
if (v_isSharedCheck_1180_ == 0)
{
v___x_1174_ = v___x_1153_;
v_isShared_1175_ = v_isSharedCheck_1180_;
goto v_resetjp_1173_;
}
else
{
lean_inc(v_a_1172_);
lean_dec(v___x_1153_);
v___x_1174_ = lean_box(0);
v_isShared_1175_ = v_isSharedCheck_1180_;
goto v_resetjp_1173_;
}
v_resetjp_1173_:
{
lean_object* v___x_1176_; lean_object* v___x_1178_; 
v___x_1176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1176_, 0, v_a_1151_);
lean_ctor_set(v___x_1176_, 1, v_a_1172_);
if (v_isShared_1175_ == 0)
{
lean_ctor_set(v___x_1174_, 0, v___x_1176_);
v___x_1178_ = v___x_1174_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v___x_1176_);
v___x_1178_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
return v___x_1178_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonTextDocumentEdit_toJson_spec__0_spec__0(size_t v_sz_1183_, size_t v_i_1184_, lean_object* v_bs_1185_){
_start:
{
uint8_t v___x_1186_; 
v___x_1186_ = lean_usize_dec_lt(v_i_1184_, v_sz_1183_);
if (v___x_1186_ == 0)
{
return v_bs_1185_;
}
else
{
lean_object* v_v_1187_; lean_object* v___x_1188_; lean_object* v_bs_x27_1189_; lean_object* v___x_1190_; size_t v___x_1191_; size_t v___x_1192_; lean_object* v___x_1193_; 
v_v_1187_ = lean_array_uget(v_bs_1185_, v_i_1184_);
v___x_1188_ = lean_unsigned_to_nat(0u);
v_bs_x27_1189_ = lean_array_uset(v_bs_1185_, v_i_1184_, v___x_1188_);
v___x_1190_ = l_Lean_Lsp_instToJsonTextEdit_toJson(v_v_1187_);
v___x_1191_ = ((size_t)1ULL);
v___x_1192_ = lean_usize_add(v_i_1184_, v___x_1191_);
v___x_1193_ = lean_array_uset(v_bs_x27_1189_, v_i_1184_, v___x_1190_);
v_i_1184_ = v___x_1192_;
v_bs_1185_ = v___x_1193_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonTextDocumentEdit_toJson_spec__0_spec__0___boxed(lean_object* v_sz_1195_, lean_object* v_i_1196_, lean_object* v_bs_1197_){
_start:
{
size_t v_sz_boxed_1198_; size_t v_i_boxed_1199_; lean_object* v_res_1200_; 
v_sz_boxed_1198_ = lean_unbox_usize(v_sz_1195_);
lean_dec(v_sz_1195_);
v_i_boxed_1199_ = lean_unbox_usize(v_i_1196_);
lean_dec(v_i_1196_);
v_res_1200_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonTextDocumentEdit_toJson_spec__0_spec__0(v_sz_boxed_1198_, v_i_boxed_1199_, v_bs_1197_);
return v_res_1200_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Lsp_instToJsonTextDocumentEdit_toJson_spec__0(lean_object* v_a_1201_){
_start:
{
size_t v_sz_1202_; size_t v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; 
v_sz_1202_ = lean_array_size(v_a_1201_);
v___x_1203_ = ((size_t)0ULL);
v___x_1204_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonTextDocumentEdit_toJson_spec__0_spec__0(v_sz_1202_, v___x_1203_, v_a_1201_);
v___x_1205_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1205_, 0, v___x_1204_);
return v___x_1205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonTextDocumentEdit_toJson(lean_object* v_x_1208_){
_start:
{
lean_object* v_textDocument_1209_; lean_object* v_edits_1210_; lean_object* v___x_1212_; uint8_t v_isShared_1213_; uint8_t v_isSharedCheck_1230_; 
v_textDocument_1209_ = lean_ctor_get(v_x_1208_, 0);
v_edits_1210_ = lean_ctor_get(v_x_1208_, 1);
v_isSharedCheck_1230_ = !lean_is_exclusive(v_x_1208_);
if (v_isSharedCheck_1230_ == 0)
{
v___x_1212_ = v_x_1208_;
v_isShared_1213_ = v_isSharedCheck_1230_;
goto v_resetjp_1211_;
}
else
{
lean_inc(v_edits_1210_);
lean_inc(v_textDocument_1209_);
lean_dec(v_x_1208_);
v___x_1212_ = lean_box(0);
v_isShared_1213_ = v_isSharedCheck_1230_;
goto v_resetjp_1211_;
}
v_resetjp_1211_:
{
lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1217_; 
v___x_1214_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextDocumentEdit_toJson___closed__0));
v___x_1215_ = l_Lean_Lsp_instToJsonVersionedTextDocumentIdentifier_toJson(v_textDocument_1209_);
if (v_isShared_1213_ == 0)
{
lean_ctor_set(v___x_1212_, 1, v___x_1215_);
lean_ctor_set(v___x_1212_, 0, v___x_1214_);
v___x_1217_ = v___x_1212_;
goto v_reusejp_1216_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v___x_1214_);
lean_ctor_set(v_reuseFailAlloc_1229_, 1, v___x_1215_);
v___x_1217_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1216_;
}
v_reusejp_1216_:
{
lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; 
v___x_1218_ = lean_box(0);
v___x_1219_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1219_, 0, v___x_1217_);
lean_ctor_set(v___x_1219_, 1, v___x_1218_);
v___x_1220_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextDocumentEdit_toJson___closed__1));
v___x_1221_ = l_Array_toJson___at___00Lean_Lsp_instToJsonTextDocumentEdit_toJson_spec__0(v_edits_1210_);
v___x_1222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1222_, 0, v___x_1220_);
lean_ctor_set(v___x_1222_, 1, v___x_1221_);
v___x_1223_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1223_, 0, v___x_1222_);
lean_ctor_set(v___x_1223_, 1, v___x_1218_);
v___x_1224_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1224_, 0, v___x_1223_);
lean_ctor_set(v___x_1224_, 1, v___x_1218_);
v___x_1225_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1225_, 0, v___x_1219_);
lean_ctor_set(v___x_1225_, 1, v___x_1224_);
v___x_1226_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__2));
v___x_1227_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLocation_toJson_spec__0(v___x_1225_, v___x_1226_);
v___x_1228_ = l_Lean_Json_mkObj(v___x_1227_);
return v___x_1228_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentEdit_fromJson_spec__0(lean_object* v_j_1233_, lean_object* v_k_1234_){
_start:
{
lean_object* v___x_1235_; lean_object* v___x_1236_; 
v___x_1235_ = l_Lean_Json_getObjValD(v_j_1233_, v_k_1234_);
v___x_1236_ = l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson(v___x_1235_);
return v___x_1236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentEdit_fromJson_spec__0___boxed(lean_object* v_j_1237_, lean_object* v_k_1238_){
_start:
{
lean_object* v_res_1239_; 
v_res_1239_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentEdit_fromJson_spec__0(v_j_1237_, v_k_1238_);
lean_dec_ref(v_k_1238_);
return v_res_1239_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentEdit_fromJson_spec__1_spec__1_spec__2(size_t v_sz_1240_, size_t v_i_1241_, lean_object* v_bs_1242_){
_start:
{
uint8_t v___x_1243_; 
v___x_1243_ = lean_usize_dec_lt(v_i_1241_, v_sz_1240_);
if (v___x_1243_ == 0)
{
lean_object* v___x_1244_; 
v___x_1244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1244_, 0, v_bs_1242_);
return v___x_1244_;
}
else
{
lean_object* v_v_1245_; lean_object* v___x_1246_; 
v_v_1245_ = lean_array_uget_borrowed(v_bs_1242_, v_i_1241_);
lean_inc(v_v_1245_);
v___x_1246_ = l_Lean_Lsp_instFromJsonTextEdit_fromJson(v_v_1245_);
if (lean_obj_tag(v___x_1246_) == 0)
{
lean_object* v_a_1247_; lean_object* v___x_1249_; uint8_t v_isShared_1250_; uint8_t v_isSharedCheck_1254_; 
lean_dec_ref(v_bs_1242_);
v_a_1247_ = lean_ctor_get(v___x_1246_, 0);
v_isSharedCheck_1254_ = !lean_is_exclusive(v___x_1246_);
if (v_isSharedCheck_1254_ == 0)
{
v___x_1249_ = v___x_1246_;
v_isShared_1250_ = v_isSharedCheck_1254_;
goto v_resetjp_1248_;
}
else
{
lean_inc(v_a_1247_);
lean_dec(v___x_1246_);
v___x_1249_ = lean_box(0);
v_isShared_1250_ = v_isSharedCheck_1254_;
goto v_resetjp_1248_;
}
v_resetjp_1248_:
{
lean_object* v___x_1252_; 
if (v_isShared_1250_ == 0)
{
v___x_1252_ = v___x_1249_;
goto v_reusejp_1251_;
}
else
{
lean_object* v_reuseFailAlloc_1253_; 
v_reuseFailAlloc_1253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1253_, 0, v_a_1247_);
v___x_1252_ = v_reuseFailAlloc_1253_;
goto v_reusejp_1251_;
}
v_reusejp_1251_:
{
return v___x_1252_;
}
}
}
else
{
lean_object* v_a_1255_; lean_object* v___x_1256_; lean_object* v_bs_x27_1257_; size_t v___x_1258_; size_t v___x_1259_; lean_object* v___x_1260_; 
v_a_1255_ = lean_ctor_get(v___x_1246_, 0);
lean_inc(v_a_1255_);
lean_dec_ref(v___x_1246_);
v___x_1256_ = lean_unsigned_to_nat(0u);
v_bs_x27_1257_ = lean_array_uset(v_bs_1242_, v_i_1241_, v___x_1256_);
v___x_1258_ = ((size_t)1ULL);
v___x_1259_ = lean_usize_add(v_i_1241_, v___x_1258_);
v___x_1260_ = lean_array_uset(v_bs_x27_1257_, v_i_1241_, v_a_1255_);
v_i_1241_ = v___x_1259_;
v_bs_1242_ = v___x_1260_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentEdit_fromJson_spec__1_spec__1_spec__2___boxed(lean_object* v_sz_1262_, lean_object* v_i_1263_, lean_object* v_bs_1264_){
_start:
{
size_t v_sz_boxed_1265_; size_t v_i_boxed_1266_; lean_object* v_res_1267_; 
v_sz_boxed_1265_ = lean_unbox_usize(v_sz_1262_);
lean_dec(v_sz_1262_);
v_i_boxed_1266_ = lean_unbox_usize(v_i_1263_);
lean_dec(v_i_1263_);
v_res_1267_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentEdit_fromJson_spec__1_spec__1_spec__2(v_sz_boxed_1265_, v_i_boxed_1266_, v_bs_1264_);
return v_res_1267_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentEdit_fromJson_spec__1_spec__1(lean_object* v_x_1268_){
_start:
{
if (lean_obj_tag(v_x_1268_) == 4)
{
lean_object* v_elems_1269_; size_t v_sz_1270_; size_t v___x_1271_; lean_object* v___x_1272_; 
v_elems_1269_ = lean_ctor_get(v_x_1268_, 0);
lean_inc_ref(v_elems_1269_);
lean_dec_ref(v_x_1268_);
v_sz_1270_ = lean_array_size(v_elems_1269_);
v___x_1271_ = ((size_t)0ULL);
v___x_1272_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentEdit_fromJson_spec__1_spec__1_spec__2(v_sz_1270_, v___x_1271_, v_elems_1269_);
return v___x_1272_;
}
else
{
lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; 
v___x_1273_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCommand_fromJson_spec__0_spec__0_spec__1___closed__0));
v___x_1274_ = lean_unsigned_to_nat(80u);
v___x_1275_ = l_Lean_Json_pretty(v_x_1268_, v___x_1274_);
v___x_1276_ = lean_string_append(v___x_1273_, v___x_1275_);
lean_dec_ref(v___x_1275_);
v___x_1277_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCommand_fromJson_spec__0_spec__0_spec__1___closed__1));
v___x_1278_ = lean_string_append(v___x_1276_, v___x_1277_);
v___x_1279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1279_, 0, v___x_1278_);
return v___x_1279_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentEdit_fromJson_spec__1(lean_object* v_j_1280_, lean_object* v_k_1281_){
_start:
{
lean_object* v___x_1282_; lean_object* v___x_1283_; 
v___x_1282_ = l_Lean_Json_getObjValD(v_j_1280_, v_k_1281_);
v___x_1283_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentEdit_fromJson_spec__1_spec__1(v___x_1282_);
return v___x_1283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentEdit_fromJson_spec__1___boxed(lean_object* v_j_1284_, lean_object* v_k_1285_){
_start:
{
lean_object* v_res_1286_; 
v_res_1286_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentEdit_fromJson_spec__1(v_j_1284_, v_k_1285_);
lean_dec_ref(v_k_1285_);
return v_res_1286_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__2(void){
_start:
{
uint8_t v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; 
v___x_1292_ = 1;
v___x_1293_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__1));
v___x_1294_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1293_, v___x_1292_);
return v___x_1294_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__3(void){
_start:
{
lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; 
v___x_1295_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__5));
v___x_1296_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__2, &l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__2);
v___x_1297_ = lean_string_append(v___x_1296_, v___x_1295_);
return v___x_1297_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__5(void){
_start:
{
uint8_t v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; 
v___x_1300_ = 1;
v___x_1301_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__4));
v___x_1302_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1301_, v___x_1300_);
return v___x_1302_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__6(void){
_start:
{
lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; 
v___x_1303_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__5, &l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__5);
v___x_1304_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__3, &l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__3);
v___x_1305_ = lean_string_append(v___x_1304_, v___x_1303_);
return v___x_1305_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__7(void){
_start:
{
lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; 
v___x_1306_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_1307_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__6, &l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__6);
v___x_1308_ = lean_string_append(v___x_1307_, v___x_1306_);
return v___x_1308_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__9(void){
_start:
{
uint8_t v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; 
v___x_1311_ = 1;
v___x_1312_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__8));
v___x_1313_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1312_, v___x_1311_);
return v___x_1313_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__10(void){
_start:
{
lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; 
v___x_1314_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__9, &l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__9);
v___x_1315_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__3, &l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__3);
v___x_1316_ = lean_string_append(v___x_1315_, v___x_1314_);
return v___x_1316_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__11(void){
_start:
{
lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; 
v___x_1317_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_1318_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__10, &l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__10);
v___x_1319_ = lean_string_append(v___x_1318_, v___x_1317_);
return v___x_1319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson(lean_object* v_json_1320_){
_start:
{
lean_object* v___x_1321_; lean_object* v___x_1322_; 
v___x_1321_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextDocumentEdit_toJson___closed__0));
lean_inc(v_json_1320_);
v___x_1322_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentEdit_fromJson_spec__0(v_json_1320_, v___x_1321_);
if (lean_obj_tag(v___x_1322_) == 0)
{
lean_object* v_a_1323_; lean_object* v___x_1325_; uint8_t v_isShared_1326_; uint8_t v_isSharedCheck_1332_; 
lean_dec(v_json_1320_);
v_a_1323_ = lean_ctor_get(v___x_1322_, 0);
v_isSharedCheck_1332_ = !lean_is_exclusive(v___x_1322_);
if (v_isSharedCheck_1332_ == 0)
{
v___x_1325_ = v___x_1322_;
v_isShared_1326_ = v_isSharedCheck_1332_;
goto v_resetjp_1324_;
}
else
{
lean_inc(v_a_1323_);
lean_dec(v___x_1322_);
v___x_1325_ = lean_box(0);
v_isShared_1326_ = v_isSharedCheck_1332_;
goto v_resetjp_1324_;
}
v_resetjp_1324_:
{
lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1330_; 
v___x_1327_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__7, &l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__7);
v___x_1328_ = lean_string_append(v___x_1327_, v_a_1323_);
lean_dec(v_a_1323_);
if (v_isShared_1326_ == 0)
{
lean_ctor_set(v___x_1325_, 0, v___x_1328_);
v___x_1330_ = v___x_1325_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v___x_1328_);
v___x_1330_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
return v___x_1330_;
}
}
}
else
{
if (lean_obj_tag(v___x_1322_) == 0)
{
lean_object* v_a_1333_; lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1340_; 
lean_dec(v_json_1320_);
v_a_1333_ = lean_ctor_get(v___x_1322_, 0);
v_isSharedCheck_1340_ = !lean_is_exclusive(v___x_1322_);
if (v_isSharedCheck_1340_ == 0)
{
v___x_1335_ = v___x_1322_;
v_isShared_1336_ = v_isSharedCheck_1340_;
goto v_resetjp_1334_;
}
else
{
lean_inc(v_a_1333_);
lean_dec(v___x_1322_);
v___x_1335_ = lean_box(0);
v_isShared_1336_ = v_isSharedCheck_1340_;
goto v_resetjp_1334_;
}
v_resetjp_1334_:
{
lean_object* v___x_1338_; 
if (v_isShared_1336_ == 0)
{
lean_ctor_set_tag(v___x_1335_, 0);
v___x_1338_ = v___x_1335_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v_a_1333_);
v___x_1338_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1337_;
}
v_reusejp_1337_:
{
return v___x_1338_;
}
}
}
else
{
lean_object* v_a_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; 
v_a_1341_ = lean_ctor_get(v___x_1322_, 0);
lean_inc(v_a_1341_);
lean_dec_ref(v___x_1322_);
v___x_1342_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextDocumentEdit_toJson___closed__1));
v___x_1343_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentEdit_fromJson_spec__1(v_json_1320_, v___x_1342_);
if (lean_obj_tag(v___x_1343_) == 0)
{
lean_object* v_a_1344_; lean_object* v___x_1346_; uint8_t v_isShared_1347_; uint8_t v_isSharedCheck_1353_; 
lean_dec(v_a_1341_);
v_a_1344_ = lean_ctor_get(v___x_1343_, 0);
v_isSharedCheck_1353_ = !lean_is_exclusive(v___x_1343_);
if (v_isSharedCheck_1353_ == 0)
{
v___x_1346_ = v___x_1343_;
v_isShared_1347_ = v_isSharedCheck_1353_;
goto v_resetjp_1345_;
}
else
{
lean_inc(v_a_1344_);
lean_dec(v___x_1343_);
v___x_1346_ = lean_box(0);
v_isShared_1347_ = v_isSharedCheck_1353_;
goto v_resetjp_1345_;
}
v_resetjp_1345_:
{
lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1351_; 
v___x_1348_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__11, &l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__11);
v___x_1349_ = lean_string_append(v___x_1348_, v_a_1344_);
lean_dec(v_a_1344_);
if (v_isShared_1347_ == 0)
{
lean_ctor_set(v___x_1346_, 0, v___x_1349_);
v___x_1351_ = v___x_1346_;
goto v_reusejp_1350_;
}
else
{
lean_object* v_reuseFailAlloc_1352_; 
v_reuseFailAlloc_1352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1352_, 0, v___x_1349_);
v___x_1351_ = v_reuseFailAlloc_1352_;
goto v_reusejp_1350_;
}
v_reusejp_1350_:
{
return v___x_1351_;
}
}
}
else
{
if (lean_obj_tag(v___x_1343_) == 0)
{
lean_object* v_a_1354_; lean_object* v___x_1356_; uint8_t v_isShared_1357_; uint8_t v_isSharedCheck_1361_; 
lean_dec(v_a_1341_);
v_a_1354_ = lean_ctor_get(v___x_1343_, 0);
v_isSharedCheck_1361_ = !lean_is_exclusive(v___x_1343_);
if (v_isSharedCheck_1361_ == 0)
{
v___x_1356_ = v___x_1343_;
v_isShared_1357_ = v_isSharedCheck_1361_;
goto v_resetjp_1355_;
}
else
{
lean_inc(v_a_1354_);
lean_dec(v___x_1343_);
v___x_1356_ = lean_box(0);
v_isShared_1357_ = v_isSharedCheck_1361_;
goto v_resetjp_1355_;
}
v_resetjp_1355_:
{
lean_object* v___x_1359_; 
if (v_isShared_1357_ == 0)
{
lean_ctor_set_tag(v___x_1356_, 0);
v___x_1359_ = v___x_1356_;
goto v_reusejp_1358_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v_a_1354_);
v___x_1359_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1358_;
}
v_reusejp_1358_:
{
return v___x_1359_;
}
}
}
else
{
lean_object* v_a_1362_; lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1370_; 
v_a_1362_ = lean_ctor_get(v___x_1343_, 0);
v_isSharedCheck_1370_ = !lean_is_exclusive(v___x_1343_);
if (v_isSharedCheck_1370_ == 0)
{
v___x_1364_ = v___x_1343_;
v_isShared_1365_ = v_isSharedCheck_1370_;
goto v_resetjp_1363_;
}
else
{
lean_inc(v_a_1362_);
lean_dec(v___x_1343_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1370_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
lean_object* v___x_1366_; lean_object* v___x_1368_; 
v___x_1366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1366_, 0, v_a_1341_);
lean_ctor_set(v___x_1366_, 1, v_a_1362_);
if (v_isShared_1365_ == 0)
{
lean_ctor_set(v___x_1364_, 0, v___x_1366_);
v___x_1368_ = v___x_1364_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v___x_1366_);
v___x_1368_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
return v___x_1368_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonChangeAnnotation_toJson(lean_object* v_x_1376_){
_start:
{
lean_object* v_label_1377_; uint8_t v_needsConfirmation_1378_; lean_object* v_description_x3f_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; 
v_label_1377_ = lean_ctor_get(v_x_1376_, 0);
lean_inc_ref(v_label_1377_);
v_needsConfirmation_1378_ = lean_ctor_get_uint8(v_x_1376_, sizeof(void*)*2);
v_description_x3f_1379_ = lean_ctor_get(v_x_1376_, 1);
lean_inc(v_description_x3f_1379_);
lean_dec_ref(v_x_1376_);
v___x_1380_ = ((lean_object*)(l_Lean_Lsp_instToJsonChangeAnnotation_toJson___closed__0));
v___x_1381_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1381_, 0, v_label_1377_);
v___x_1382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1382_, 0, v___x_1380_);
lean_ctor_set(v___x_1382_, 1, v___x_1381_);
v___x_1383_ = lean_box(0);
v___x_1384_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1384_, 0, v___x_1382_);
lean_ctor_set(v___x_1384_, 1, v___x_1383_);
v___x_1385_ = ((lean_object*)(l_Lean_Lsp_instToJsonChangeAnnotation_toJson___closed__1));
v___x_1386_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1386_, 0, v_needsConfirmation_1378_);
v___x_1387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1387_, 0, v___x_1385_);
lean_ctor_set(v___x_1387_, 1, v___x_1386_);
v___x_1388_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1388_, 0, v___x_1387_);
lean_ctor_set(v___x_1388_, 1, v___x_1383_);
v___x_1389_ = ((lean_object*)(l_Lean_Lsp_instToJsonChangeAnnotation_toJson___closed__2));
v___x_1390_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextEdit_toJson_spec__1(v___x_1389_, v_description_x3f_1379_);
v___x_1391_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1391_, 0, v___x_1390_);
lean_ctor_set(v___x_1391_, 1, v___x_1383_);
v___x_1392_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1392_, 0, v___x_1388_);
lean_ctor_set(v___x_1392_, 1, v___x_1391_);
v___x_1393_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1393_, 0, v___x_1384_);
lean_ctor_set(v___x_1393_, 1, v___x_1392_);
v___x_1394_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__2));
v___x_1395_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLocation_toJson_spec__0(v___x_1393_, v___x_1394_);
v___x_1396_ = l_Lean_Json_mkObj(v___x_1395_);
return v___x_1396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonChangeAnnotation_fromJson_spec__0(lean_object* v_j_1399_, lean_object* v_k_1400_){
_start:
{
lean_object* v___x_1401_; lean_object* v___x_1402_; 
v___x_1401_ = l_Lean_Json_getObjValD(v_j_1399_, v_k_1400_);
v___x_1402_ = l_Lean_Json_getBool_x3f(v___x_1401_);
lean_dec(v___x_1401_);
return v___x_1402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonChangeAnnotation_fromJson_spec__0___boxed(lean_object* v_j_1403_, lean_object* v_k_1404_){
_start:
{
lean_object* v_res_1405_; 
v_res_1405_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonChangeAnnotation_fromJson_spec__0(v_j_1403_, v_k_1404_);
lean_dec_ref(v_k_1404_);
return v_res_1405_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__2(void){
_start:
{
uint8_t v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; 
v___x_1411_ = 1;
v___x_1412_ = ((lean_object*)(l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__1));
v___x_1413_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1412_, v___x_1411_);
return v___x_1413_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__3(void){
_start:
{
lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; 
v___x_1414_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__5));
v___x_1415_ = lean_obj_once(&l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__2, &l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__2);
v___x_1416_ = lean_string_append(v___x_1415_, v___x_1414_);
return v___x_1416_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__5(void){
_start:
{
uint8_t v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; 
v___x_1419_ = 1;
v___x_1420_ = ((lean_object*)(l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__4));
v___x_1421_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1420_, v___x_1419_);
return v___x_1421_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__6(void){
_start:
{
lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; 
v___x_1422_ = lean_obj_once(&l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__5, &l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__5);
v___x_1423_ = lean_obj_once(&l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__3, &l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__3);
v___x_1424_ = lean_string_append(v___x_1423_, v___x_1422_);
return v___x_1424_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__7(void){
_start:
{
lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; 
v___x_1425_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_1426_ = lean_obj_once(&l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__6, &l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__6);
v___x_1427_ = lean_string_append(v___x_1426_, v___x_1425_);
return v___x_1427_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__9(void){
_start:
{
uint8_t v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; 
v___x_1430_ = 1;
v___x_1431_ = ((lean_object*)(l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__8));
v___x_1432_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1431_, v___x_1430_);
return v___x_1432_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__10(void){
_start:
{
lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; 
v___x_1433_ = lean_obj_once(&l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__9, &l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__9);
v___x_1434_ = lean_obj_once(&l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__3, &l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__3);
v___x_1435_ = lean_string_append(v___x_1434_, v___x_1433_);
return v___x_1435_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__11(void){
_start:
{
lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; 
v___x_1436_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_1437_ = lean_obj_once(&l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__10, &l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__10);
v___x_1438_ = lean_string_append(v___x_1437_, v___x_1436_);
return v___x_1438_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__14(void){
_start:
{
uint8_t v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; 
v___x_1442_ = 1;
v___x_1443_ = ((lean_object*)(l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__13));
v___x_1444_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1443_, v___x_1442_);
return v___x_1444_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__15(void){
_start:
{
lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; 
v___x_1445_ = lean_obj_once(&l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__14, &l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__14_once, _init_l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__14);
v___x_1446_ = lean_obj_once(&l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__3, &l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__3);
v___x_1447_ = lean_string_append(v___x_1446_, v___x_1445_);
return v___x_1447_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__16(void){
_start:
{
lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; 
v___x_1448_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_1449_ = lean_obj_once(&l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__15, &l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__15_once, _init_l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__15);
v___x_1450_ = lean_string_append(v___x_1449_, v___x_1448_);
return v___x_1450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson(lean_object* v_json_1451_){
_start:
{
lean_object* v___x_1452_; lean_object* v___x_1453_; 
v___x_1452_ = ((lean_object*)(l_Lean_Lsp_instToJsonChangeAnnotation_toJson___closed__0));
lean_inc(v_json_1451_);
v___x_1453_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocation_fromJson_spec__0(v_json_1451_, v___x_1452_);
if (lean_obj_tag(v___x_1453_) == 0)
{
lean_object* v_a_1454_; lean_object* v___x_1456_; uint8_t v_isShared_1457_; uint8_t v_isSharedCheck_1463_; 
lean_dec(v_json_1451_);
v_a_1454_ = lean_ctor_get(v___x_1453_, 0);
v_isSharedCheck_1463_ = !lean_is_exclusive(v___x_1453_);
if (v_isSharedCheck_1463_ == 0)
{
v___x_1456_ = v___x_1453_;
v_isShared_1457_ = v_isSharedCheck_1463_;
goto v_resetjp_1455_;
}
else
{
lean_inc(v_a_1454_);
lean_dec(v___x_1453_);
v___x_1456_ = lean_box(0);
v_isShared_1457_ = v_isSharedCheck_1463_;
goto v_resetjp_1455_;
}
v_resetjp_1455_:
{
lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1461_; 
v___x_1458_ = lean_obj_once(&l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__7, &l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__7);
v___x_1459_ = lean_string_append(v___x_1458_, v_a_1454_);
lean_dec(v_a_1454_);
if (v_isShared_1457_ == 0)
{
lean_ctor_set(v___x_1456_, 0, v___x_1459_);
v___x_1461_ = v___x_1456_;
goto v_reusejp_1460_;
}
else
{
lean_object* v_reuseFailAlloc_1462_; 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v___x_1459_);
v___x_1461_ = v_reuseFailAlloc_1462_;
goto v_reusejp_1460_;
}
v_reusejp_1460_:
{
return v___x_1461_;
}
}
}
else
{
if (lean_obj_tag(v___x_1453_) == 0)
{
lean_object* v_a_1464_; lean_object* v___x_1466_; uint8_t v_isShared_1467_; uint8_t v_isSharedCheck_1471_; 
lean_dec(v_json_1451_);
v_a_1464_ = lean_ctor_get(v___x_1453_, 0);
v_isSharedCheck_1471_ = !lean_is_exclusive(v___x_1453_);
if (v_isSharedCheck_1471_ == 0)
{
v___x_1466_ = v___x_1453_;
v_isShared_1467_ = v_isSharedCheck_1471_;
goto v_resetjp_1465_;
}
else
{
lean_inc(v_a_1464_);
lean_dec(v___x_1453_);
v___x_1466_ = lean_box(0);
v_isShared_1467_ = v_isSharedCheck_1471_;
goto v_resetjp_1465_;
}
v_resetjp_1465_:
{
lean_object* v___x_1469_; 
if (v_isShared_1467_ == 0)
{
lean_ctor_set_tag(v___x_1466_, 0);
v___x_1469_ = v___x_1466_;
goto v_reusejp_1468_;
}
else
{
lean_object* v_reuseFailAlloc_1470_; 
v_reuseFailAlloc_1470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1470_, 0, v_a_1464_);
v___x_1469_ = v_reuseFailAlloc_1470_;
goto v_reusejp_1468_;
}
v_reusejp_1468_:
{
return v___x_1469_;
}
}
}
else
{
lean_object* v_a_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; 
v_a_1472_ = lean_ctor_get(v___x_1453_, 0);
lean_inc(v_a_1472_);
lean_dec_ref(v___x_1453_);
v___x_1473_ = ((lean_object*)(l_Lean_Lsp_instToJsonChangeAnnotation_toJson___closed__1));
lean_inc(v_json_1451_);
v___x_1474_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonChangeAnnotation_fromJson_spec__0(v_json_1451_, v___x_1473_);
if (lean_obj_tag(v___x_1474_) == 0)
{
lean_object* v_a_1475_; lean_object* v___x_1477_; uint8_t v_isShared_1478_; uint8_t v_isSharedCheck_1484_; 
lean_dec(v_a_1472_);
lean_dec(v_json_1451_);
v_a_1475_ = lean_ctor_get(v___x_1474_, 0);
v_isSharedCheck_1484_ = !lean_is_exclusive(v___x_1474_);
if (v_isSharedCheck_1484_ == 0)
{
v___x_1477_ = v___x_1474_;
v_isShared_1478_ = v_isSharedCheck_1484_;
goto v_resetjp_1476_;
}
else
{
lean_inc(v_a_1475_);
lean_dec(v___x_1474_);
v___x_1477_ = lean_box(0);
v_isShared_1478_ = v_isSharedCheck_1484_;
goto v_resetjp_1476_;
}
v_resetjp_1476_:
{
lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1482_; 
v___x_1479_ = lean_obj_once(&l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__11, &l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__11);
v___x_1480_ = lean_string_append(v___x_1479_, v_a_1475_);
lean_dec(v_a_1475_);
if (v_isShared_1478_ == 0)
{
lean_ctor_set(v___x_1477_, 0, v___x_1480_);
v___x_1482_ = v___x_1477_;
goto v_reusejp_1481_;
}
else
{
lean_object* v_reuseFailAlloc_1483_; 
v_reuseFailAlloc_1483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1483_, 0, v___x_1480_);
v___x_1482_ = v_reuseFailAlloc_1483_;
goto v_reusejp_1481_;
}
v_reusejp_1481_:
{
return v___x_1482_;
}
}
}
else
{
if (lean_obj_tag(v___x_1474_) == 0)
{
lean_object* v_a_1485_; lean_object* v___x_1487_; uint8_t v_isShared_1488_; uint8_t v_isSharedCheck_1492_; 
lean_dec(v_a_1472_);
lean_dec(v_json_1451_);
v_a_1485_ = lean_ctor_get(v___x_1474_, 0);
v_isSharedCheck_1492_ = !lean_is_exclusive(v___x_1474_);
if (v_isSharedCheck_1492_ == 0)
{
v___x_1487_ = v___x_1474_;
v_isShared_1488_ = v_isSharedCheck_1492_;
goto v_resetjp_1486_;
}
else
{
lean_inc(v_a_1485_);
lean_dec(v___x_1474_);
v___x_1487_ = lean_box(0);
v_isShared_1488_ = v_isSharedCheck_1492_;
goto v_resetjp_1486_;
}
v_resetjp_1486_:
{
lean_object* v___x_1490_; 
if (v_isShared_1488_ == 0)
{
lean_ctor_set_tag(v___x_1487_, 0);
v___x_1490_ = v___x_1487_;
goto v_reusejp_1489_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v_a_1485_);
v___x_1490_ = v_reuseFailAlloc_1491_;
goto v_reusejp_1489_;
}
v_reusejp_1489_:
{
return v___x_1490_;
}
}
}
else
{
lean_object* v_a_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; 
v_a_1493_ = lean_ctor_get(v___x_1474_, 0);
lean_inc(v_a_1493_);
lean_dec_ref(v___x_1474_);
v___x_1494_ = ((lean_object*)(l_Lean_Lsp_instToJsonChangeAnnotation_toJson___closed__2));
v___x_1495_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextEdit_fromJson_spec__1(v_json_1451_, v___x_1494_);
if (lean_obj_tag(v___x_1495_) == 0)
{
lean_object* v_a_1496_; lean_object* v___x_1498_; uint8_t v_isShared_1499_; uint8_t v_isSharedCheck_1505_; 
lean_dec(v_a_1493_);
lean_dec(v_a_1472_);
v_a_1496_ = lean_ctor_get(v___x_1495_, 0);
v_isSharedCheck_1505_ = !lean_is_exclusive(v___x_1495_);
if (v_isSharedCheck_1505_ == 0)
{
v___x_1498_ = v___x_1495_;
v_isShared_1499_ = v_isSharedCheck_1505_;
goto v_resetjp_1497_;
}
else
{
lean_inc(v_a_1496_);
lean_dec(v___x_1495_);
v___x_1498_ = lean_box(0);
v_isShared_1499_ = v_isSharedCheck_1505_;
goto v_resetjp_1497_;
}
v_resetjp_1497_:
{
lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1503_; 
v___x_1500_ = lean_obj_once(&l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__16, &l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__16_once, _init_l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__16);
v___x_1501_ = lean_string_append(v___x_1500_, v_a_1496_);
lean_dec(v_a_1496_);
if (v_isShared_1499_ == 0)
{
lean_ctor_set(v___x_1498_, 0, v___x_1501_);
v___x_1503_ = v___x_1498_;
goto v_reusejp_1502_;
}
else
{
lean_object* v_reuseFailAlloc_1504_; 
v_reuseFailAlloc_1504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1504_, 0, v___x_1501_);
v___x_1503_ = v_reuseFailAlloc_1504_;
goto v_reusejp_1502_;
}
v_reusejp_1502_:
{
return v___x_1503_;
}
}
}
else
{
if (lean_obj_tag(v___x_1495_) == 0)
{
lean_object* v_a_1506_; lean_object* v___x_1508_; uint8_t v_isShared_1509_; uint8_t v_isSharedCheck_1513_; 
lean_dec(v_a_1493_);
lean_dec(v_a_1472_);
v_a_1506_ = lean_ctor_get(v___x_1495_, 0);
v_isSharedCheck_1513_ = !lean_is_exclusive(v___x_1495_);
if (v_isSharedCheck_1513_ == 0)
{
v___x_1508_ = v___x_1495_;
v_isShared_1509_ = v_isSharedCheck_1513_;
goto v_resetjp_1507_;
}
else
{
lean_inc(v_a_1506_);
lean_dec(v___x_1495_);
v___x_1508_ = lean_box(0);
v_isShared_1509_ = v_isSharedCheck_1513_;
goto v_resetjp_1507_;
}
v_resetjp_1507_:
{
lean_object* v___x_1511_; 
if (v_isShared_1509_ == 0)
{
lean_ctor_set_tag(v___x_1508_, 0);
v___x_1511_ = v___x_1508_;
goto v_reusejp_1510_;
}
else
{
lean_object* v_reuseFailAlloc_1512_; 
v_reuseFailAlloc_1512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1512_, 0, v_a_1506_);
v___x_1511_ = v_reuseFailAlloc_1512_;
goto v_reusejp_1510_;
}
v_reusejp_1510_:
{
return v___x_1511_;
}
}
}
else
{
lean_object* v_a_1514_; lean_object* v___x_1516_; uint8_t v_isShared_1517_; uint8_t v_isSharedCheck_1523_; 
v_a_1514_ = lean_ctor_get(v___x_1495_, 0);
v_isSharedCheck_1523_ = !lean_is_exclusive(v___x_1495_);
if (v_isSharedCheck_1523_ == 0)
{
v___x_1516_ = v___x_1495_;
v_isShared_1517_ = v_isSharedCheck_1523_;
goto v_resetjp_1515_;
}
else
{
lean_inc(v_a_1514_);
lean_dec(v___x_1495_);
v___x_1516_ = lean_box(0);
v_isShared_1517_ = v_isSharedCheck_1523_;
goto v_resetjp_1515_;
}
v_resetjp_1515_:
{
lean_object* v___x_1518_; uint8_t v___x_1519_; lean_object* v___x_1521_; 
v___x_1518_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1518_, 0, v_a_1472_);
lean_ctor_set(v___x_1518_, 1, v_a_1514_);
v___x_1519_ = lean_unbox(v_a_1493_);
lean_dec(v_a_1493_);
lean_ctor_set_uint8(v___x_1518_, sizeof(void*)*2, v___x_1519_);
if (v_isShared_1517_ == 0)
{
lean_ctor_set(v___x_1516_, 0, v___x_1518_);
v___x_1521_ = v___x_1516_;
goto v_reusejp_1520_;
}
else
{
lean_object* v_reuseFailAlloc_1522_; 
v_reuseFailAlloc_1522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1522_, 0, v___x_1518_);
v___x_1521_ = v_reuseFailAlloc_1522_;
goto v_reusejp_1520_;
}
v_reusejp_1520_:
{
return v___x_1521_;
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
LEAN_EXPORT lean_object* l_Lean_Lsp_CreateFile_instToJsonOptions_toJson(lean_object* v_x_1528_){
_start:
{
uint8_t v_overwrite_1529_; uint8_t v_ignoreIfExists_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; 
v_overwrite_1529_ = lean_ctor_get_uint8(v_x_1528_, 0);
v_ignoreIfExists_1530_ = lean_ctor_get_uint8(v_x_1528_, 1);
v___x_1531_ = ((lean_object*)(l_Lean_Lsp_CreateFile_instToJsonOptions_toJson___closed__0));
v___x_1532_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1532_, 0, v_overwrite_1529_);
v___x_1533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1533_, 0, v___x_1531_);
lean_ctor_set(v___x_1533_, 1, v___x_1532_);
v___x_1534_ = lean_box(0);
v___x_1535_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1535_, 0, v___x_1533_);
lean_ctor_set(v___x_1535_, 1, v___x_1534_);
v___x_1536_ = ((lean_object*)(l_Lean_Lsp_CreateFile_instToJsonOptions_toJson___closed__1));
v___x_1537_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1537_, 0, v_ignoreIfExists_1530_);
v___x_1538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1538_, 0, v___x_1536_);
lean_ctor_set(v___x_1538_, 1, v___x_1537_);
v___x_1539_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1539_, 0, v___x_1538_);
lean_ctor_set(v___x_1539_, 1, v___x_1534_);
v___x_1540_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1540_, 0, v___x_1539_);
lean_ctor_set(v___x_1540_, 1, v___x_1534_);
v___x_1541_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1541_, 0, v___x_1535_);
lean_ctor_set(v___x_1541_, 1, v___x_1540_);
v___x_1542_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__2));
v___x_1543_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLocation_toJson_spec__0(v___x_1541_, v___x_1542_);
v___x_1544_ = l_Lean_Json_mkObj(v___x_1543_);
return v___x_1544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_CreateFile_instToJsonOptions_toJson___boxed(lean_object* v_x_1545_){
_start:
{
lean_object* v_res_1546_; 
v_res_1546_ = l_Lean_Lsp_CreateFile_instToJsonOptions_toJson(v_x_1545_);
lean_dec_ref(v_x_1545_);
return v_res_1546_;
}
}
static lean_object* _init_l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__3(void){
_start:
{
uint8_t v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; 
v___x_1556_ = 1;
v___x_1557_ = ((lean_object*)(l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__2));
v___x_1558_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1557_, v___x_1556_);
return v___x_1558_;
}
}
static lean_object* _init_l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__4(void){
_start:
{
lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; 
v___x_1559_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__5));
v___x_1560_ = lean_obj_once(&l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__3, &l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__3_once, _init_l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__3);
v___x_1561_ = lean_string_append(v___x_1560_, v___x_1559_);
return v___x_1561_;
}
}
static lean_object* _init_l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__6(void){
_start:
{
uint8_t v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; 
v___x_1564_ = 1;
v___x_1565_ = ((lean_object*)(l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__5));
v___x_1566_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1565_, v___x_1564_);
return v___x_1566_;
}
}
static lean_object* _init_l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__7(void){
_start:
{
lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; 
v___x_1567_ = lean_obj_once(&l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__6, &l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__6_once, _init_l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__6);
v___x_1568_ = lean_obj_once(&l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__4, &l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__4_once, _init_l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__4);
v___x_1569_ = lean_string_append(v___x_1568_, v___x_1567_);
return v___x_1569_;
}
}
static lean_object* _init_l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__8(void){
_start:
{
lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; 
v___x_1570_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_1571_ = lean_obj_once(&l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__7, &l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__7_once, _init_l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__7);
v___x_1572_ = lean_string_append(v___x_1571_, v___x_1570_);
return v___x_1572_;
}
}
static lean_object* _init_l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__10(void){
_start:
{
uint8_t v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; 
v___x_1575_ = 1;
v___x_1576_ = ((lean_object*)(l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__9));
v___x_1577_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1576_, v___x_1575_);
return v___x_1577_;
}
}
static lean_object* _init_l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__11(void){
_start:
{
lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; 
v___x_1578_ = lean_obj_once(&l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__10, &l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__10_once, _init_l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__10);
v___x_1579_ = lean_obj_once(&l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__4, &l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__4_once, _init_l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__4);
v___x_1580_ = lean_string_append(v___x_1579_, v___x_1578_);
return v___x_1580_;
}
}
static lean_object* _init_l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__12(void){
_start:
{
lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; 
v___x_1581_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_1582_ = lean_obj_once(&l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__11, &l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__11_once, _init_l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__11);
v___x_1583_ = lean_string_append(v___x_1582_, v___x_1581_);
return v___x_1583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson(lean_object* v_json_1584_){
_start:
{
lean_object* v___x_1585_; lean_object* v___x_1586_; 
v___x_1585_ = ((lean_object*)(l_Lean_Lsp_CreateFile_instToJsonOptions_toJson___closed__0));
lean_inc(v_json_1584_);
v___x_1586_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonChangeAnnotation_fromJson_spec__0(v_json_1584_, v___x_1585_);
if (lean_obj_tag(v___x_1586_) == 0)
{
lean_object* v_a_1587_; lean_object* v___x_1589_; uint8_t v_isShared_1590_; uint8_t v_isSharedCheck_1596_; 
lean_dec(v_json_1584_);
v_a_1587_ = lean_ctor_get(v___x_1586_, 0);
v_isSharedCheck_1596_ = !lean_is_exclusive(v___x_1586_);
if (v_isSharedCheck_1596_ == 0)
{
v___x_1589_ = v___x_1586_;
v_isShared_1590_ = v_isSharedCheck_1596_;
goto v_resetjp_1588_;
}
else
{
lean_inc(v_a_1587_);
lean_dec(v___x_1586_);
v___x_1589_ = lean_box(0);
v_isShared_1590_ = v_isSharedCheck_1596_;
goto v_resetjp_1588_;
}
v_resetjp_1588_:
{
lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1594_; 
v___x_1591_ = lean_obj_once(&l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__8, &l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__8_once, _init_l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__8);
v___x_1592_ = lean_string_append(v___x_1591_, v_a_1587_);
lean_dec(v_a_1587_);
if (v_isShared_1590_ == 0)
{
lean_ctor_set(v___x_1589_, 0, v___x_1592_);
v___x_1594_ = v___x_1589_;
goto v_reusejp_1593_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v___x_1592_);
v___x_1594_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1593_;
}
v_reusejp_1593_:
{
return v___x_1594_;
}
}
}
else
{
if (lean_obj_tag(v___x_1586_) == 0)
{
lean_object* v_a_1597_; lean_object* v___x_1599_; uint8_t v_isShared_1600_; uint8_t v_isSharedCheck_1604_; 
lean_dec(v_json_1584_);
v_a_1597_ = lean_ctor_get(v___x_1586_, 0);
v_isSharedCheck_1604_ = !lean_is_exclusive(v___x_1586_);
if (v_isSharedCheck_1604_ == 0)
{
v___x_1599_ = v___x_1586_;
v_isShared_1600_ = v_isSharedCheck_1604_;
goto v_resetjp_1598_;
}
else
{
lean_inc(v_a_1597_);
lean_dec(v___x_1586_);
v___x_1599_ = lean_box(0);
v_isShared_1600_ = v_isSharedCheck_1604_;
goto v_resetjp_1598_;
}
v_resetjp_1598_:
{
lean_object* v___x_1602_; 
if (v_isShared_1600_ == 0)
{
lean_ctor_set_tag(v___x_1599_, 0);
v___x_1602_ = v___x_1599_;
goto v_reusejp_1601_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v_a_1597_);
v___x_1602_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1601_;
}
v_reusejp_1601_:
{
return v___x_1602_;
}
}
}
else
{
lean_object* v_a_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; 
v_a_1605_ = lean_ctor_get(v___x_1586_, 0);
lean_inc(v_a_1605_);
lean_dec_ref(v___x_1586_);
v___x_1606_ = ((lean_object*)(l_Lean_Lsp_CreateFile_instToJsonOptions_toJson___closed__1));
v___x_1607_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonChangeAnnotation_fromJson_spec__0(v_json_1584_, v___x_1606_);
if (lean_obj_tag(v___x_1607_) == 0)
{
lean_object* v_a_1608_; lean_object* v___x_1610_; uint8_t v_isShared_1611_; uint8_t v_isSharedCheck_1617_; 
lean_dec(v_a_1605_);
v_a_1608_ = lean_ctor_get(v___x_1607_, 0);
v_isSharedCheck_1617_ = !lean_is_exclusive(v___x_1607_);
if (v_isSharedCheck_1617_ == 0)
{
v___x_1610_ = v___x_1607_;
v_isShared_1611_ = v_isSharedCheck_1617_;
goto v_resetjp_1609_;
}
else
{
lean_inc(v_a_1608_);
lean_dec(v___x_1607_);
v___x_1610_ = lean_box(0);
v_isShared_1611_ = v_isSharedCheck_1617_;
goto v_resetjp_1609_;
}
v_resetjp_1609_:
{
lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1615_; 
v___x_1612_ = lean_obj_once(&l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__12, &l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__12_once, _init_l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__12);
v___x_1613_ = lean_string_append(v___x_1612_, v_a_1608_);
lean_dec(v_a_1608_);
if (v_isShared_1611_ == 0)
{
lean_ctor_set(v___x_1610_, 0, v___x_1613_);
v___x_1615_ = v___x_1610_;
goto v_reusejp_1614_;
}
else
{
lean_object* v_reuseFailAlloc_1616_; 
v_reuseFailAlloc_1616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1616_, 0, v___x_1613_);
v___x_1615_ = v_reuseFailAlloc_1616_;
goto v_reusejp_1614_;
}
v_reusejp_1614_:
{
return v___x_1615_;
}
}
}
else
{
if (lean_obj_tag(v___x_1607_) == 0)
{
lean_object* v_a_1618_; lean_object* v___x_1620_; uint8_t v_isShared_1621_; uint8_t v_isSharedCheck_1625_; 
lean_dec(v_a_1605_);
v_a_1618_ = lean_ctor_get(v___x_1607_, 0);
v_isSharedCheck_1625_ = !lean_is_exclusive(v___x_1607_);
if (v_isSharedCheck_1625_ == 0)
{
v___x_1620_ = v___x_1607_;
v_isShared_1621_ = v_isSharedCheck_1625_;
goto v_resetjp_1619_;
}
else
{
lean_inc(v_a_1618_);
lean_dec(v___x_1607_);
v___x_1620_ = lean_box(0);
v_isShared_1621_ = v_isSharedCheck_1625_;
goto v_resetjp_1619_;
}
v_resetjp_1619_:
{
lean_object* v___x_1623_; 
if (v_isShared_1621_ == 0)
{
lean_ctor_set_tag(v___x_1620_, 0);
v___x_1623_ = v___x_1620_;
goto v_reusejp_1622_;
}
else
{
lean_object* v_reuseFailAlloc_1624_; 
v_reuseFailAlloc_1624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1624_, 0, v_a_1618_);
v___x_1623_ = v_reuseFailAlloc_1624_;
goto v_reusejp_1622_;
}
v_reusejp_1622_:
{
return v___x_1623_;
}
}
}
else
{
lean_object* v_a_1626_; lean_object* v___x_1628_; uint8_t v_isShared_1629_; uint8_t v_isSharedCheck_1636_; 
v_a_1626_ = lean_ctor_get(v___x_1607_, 0);
v_isSharedCheck_1636_ = !lean_is_exclusive(v___x_1607_);
if (v_isSharedCheck_1636_ == 0)
{
v___x_1628_ = v___x_1607_;
v_isShared_1629_ = v_isSharedCheck_1636_;
goto v_resetjp_1627_;
}
else
{
lean_inc(v_a_1626_);
lean_dec(v___x_1607_);
v___x_1628_ = lean_box(0);
v_isShared_1629_ = v_isSharedCheck_1636_;
goto v_resetjp_1627_;
}
v_resetjp_1627_:
{
lean_object* v___x_1630_; uint8_t v___x_1631_; uint8_t v___x_1632_; lean_object* v___x_1634_; 
v___x_1630_ = lean_alloc_ctor(0, 0, 2);
v___x_1631_ = lean_unbox(v_a_1605_);
lean_dec(v_a_1605_);
lean_ctor_set_uint8(v___x_1630_, 0, v___x_1631_);
v___x_1632_ = lean_unbox(v_a_1626_);
lean_dec(v_a_1626_);
lean_ctor_set_uint8(v___x_1630_, 1, v___x_1632_);
if (v_isShared_1629_ == 0)
{
lean_ctor_set(v___x_1628_, 0, v___x_1630_);
v___x_1634_ = v___x_1628_;
goto v_reusejp_1633_;
}
else
{
lean_object* v_reuseFailAlloc_1635_; 
v_reuseFailAlloc_1635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1635_, 0, v___x_1630_);
v___x_1634_ = v_reuseFailAlloc_1635_;
goto v_reusejp_1633_;
}
v_reusejp_1633_:
{
return v___x_1634_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DeleteFile_instToJsonOptions_toJson(lean_object* v_x_1641_){
_start:
{
uint8_t v_recursive_1642_; uint8_t v_ignoreIfNotExists_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; 
v_recursive_1642_ = lean_ctor_get_uint8(v_x_1641_, 0);
v_ignoreIfNotExists_1643_ = lean_ctor_get_uint8(v_x_1641_, 1);
v___x_1644_ = ((lean_object*)(l_Lean_Lsp_DeleteFile_instToJsonOptions_toJson___closed__0));
v___x_1645_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1645_, 0, v_recursive_1642_);
v___x_1646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1646_, 0, v___x_1644_);
lean_ctor_set(v___x_1646_, 1, v___x_1645_);
v___x_1647_ = lean_box(0);
v___x_1648_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1648_, 0, v___x_1646_);
lean_ctor_set(v___x_1648_, 1, v___x_1647_);
v___x_1649_ = ((lean_object*)(l_Lean_Lsp_DeleteFile_instToJsonOptions_toJson___closed__1));
v___x_1650_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1650_, 0, v_ignoreIfNotExists_1643_);
v___x_1651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1651_, 0, v___x_1649_);
lean_ctor_set(v___x_1651_, 1, v___x_1650_);
v___x_1652_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1652_, 0, v___x_1651_);
lean_ctor_set(v___x_1652_, 1, v___x_1647_);
v___x_1653_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1653_, 0, v___x_1652_);
lean_ctor_set(v___x_1653_, 1, v___x_1647_);
v___x_1654_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1654_, 0, v___x_1648_);
lean_ctor_set(v___x_1654_, 1, v___x_1653_);
v___x_1655_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__2));
v___x_1656_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLocation_toJson_spec__0(v___x_1654_, v___x_1655_);
v___x_1657_ = l_Lean_Json_mkObj(v___x_1656_);
return v___x_1657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DeleteFile_instToJsonOptions_toJson___boxed(lean_object* v_x_1658_){
_start:
{
lean_object* v_res_1659_; 
v_res_1659_ = l_Lean_Lsp_DeleteFile_instToJsonOptions_toJson(v_x_1658_);
lean_dec_ref(v_x_1658_);
return v_res_1659_;
}
}
static lean_object* _init_l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__2(void){
_start:
{
uint8_t v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; 
v___x_1668_ = 1;
v___x_1669_ = ((lean_object*)(l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__1));
v___x_1670_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1669_, v___x_1668_);
return v___x_1670_;
}
}
static lean_object* _init_l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__3(void){
_start:
{
lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; 
v___x_1671_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__5));
v___x_1672_ = lean_obj_once(&l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__2, &l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__2_once, _init_l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__2);
v___x_1673_ = lean_string_append(v___x_1672_, v___x_1671_);
return v___x_1673_;
}
}
static lean_object* _init_l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__5(void){
_start:
{
uint8_t v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; 
v___x_1676_ = 1;
v___x_1677_ = ((lean_object*)(l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__4));
v___x_1678_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1677_, v___x_1676_);
return v___x_1678_;
}
}
static lean_object* _init_l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__6(void){
_start:
{
lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; 
v___x_1679_ = lean_obj_once(&l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__5, &l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__5_once, _init_l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__5);
v___x_1680_ = lean_obj_once(&l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__3, &l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__3_once, _init_l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__3);
v___x_1681_ = lean_string_append(v___x_1680_, v___x_1679_);
return v___x_1681_;
}
}
static lean_object* _init_l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__7(void){
_start:
{
lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; 
v___x_1682_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_1683_ = lean_obj_once(&l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__6, &l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__6_once, _init_l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__6);
v___x_1684_ = lean_string_append(v___x_1683_, v___x_1682_);
return v___x_1684_;
}
}
static lean_object* _init_l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__9(void){
_start:
{
uint8_t v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; 
v___x_1687_ = 1;
v___x_1688_ = ((lean_object*)(l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__8));
v___x_1689_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1688_, v___x_1687_);
return v___x_1689_;
}
}
static lean_object* _init_l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__10(void){
_start:
{
lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; 
v___x_1690_ = lean_obj_once(&l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__9, &l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__9_once, _init_l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__9);
v___x_1691_ = lean_obj_once(&l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__3, &l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__3_once, _init_l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__3);
v___x_1692_ = lean_string_append(v___x_1691_, v___x_1690_);
return v___x_1692_;
}
}
static lean_object* _init_l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__11(void){
_start:
{
lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; 
v___x_1693_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_1694_ = lean_obj_once(&l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__10, &l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__10_once, _init_l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__10);
v___x_1695_ = lean_string_append(v___x_1694_, v___x_1693_);
return v___x_1695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson(lean_object* v_json_1696_){
_start:
{
lean_object* v___x_1697_; lean_object* v___x_1698_; 
v___x_1697_ = ((lean_object*)(l_Lean_Lsp_DeleteFile_instToJsonOptions_toJson___closed__0));
lean_inc(v_json_1696_);
v___x_1698_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonChangeAnnotation_fromJson_spec__0(v_json_1696_, v___x_1697_);
if (lean_obj_tag(v___x_1698_) == 0)
{
lean_object* v_a_1699_; lean_object* v___x_1701_; uint8_t v_isShared_1702_; uint8_t v_isSharedCheck_1708_; 
lean_dec(v_json_1696_);
v_a_1699_ = lean_ctor_get(v___x_1698_, 0);
v_isSharedCheck_1708_ = !lean_is_exclusive(v___x_1698_);
if (v_isSharedCheck_1708_ == 0)
{
v___x_1701_ = v___x_1698_;
v_isShared_1702_ = v_isSharedCheck_1708_;
goto v_resetjp_1700_;
}
else
{
lean_inc(v_a_1699_);
lean_dec(v___x_1698_);
v___x_1701_ = lean_box(0);
v_isShared_1702_ = v_isSharedCheck_1708_;
goto v_resetjp_1700_;
}
v_resetjp_1700_:
{
lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1706_; 
v___x_1703_ = lean_obj_once(&l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__7, &l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__7_once, _init_l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__7);
v___x_1704_ = lean_string_append(v___x_1703_, v_a_1699_);
lean_dec(v_a_1699_);
if (v_isShared_1702_ == 0)
{
lean_ctor_set(v___x_1701_, 0, v___x_1704_);
v___x_1706_ = v___x_1701_;
goto v_reusejp_1705_;
}
else
{
lean_object* v_reuseFailAlloc_1707_; 
v_reuseFailAlloc_1707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1707_, 0, v___x_1704_);
v___x_1706_ = v_reuseFailAlloc_1707_;
goto v_reusejp_1705_;
}
v_reusejp_1705_:
{
return v___x_1706_;
}
}
}
else
{
if (lean_obj_tag(v___x_1698_) == 0)
{
lean_object* v_a_1709_; lean_object* v___x_1711_; uint8_t v_isShared_1712_; uint8_t v_isSharedCheck_1716_; 
lean_dec(v_json_1696_);
v_a_1709_ = lean_ctor_get(v___x_1698_, 0);
v_isSharedCheck_1716_ = !lean_is_exclusive(v___x_1698_);
if (v_isSharedCheck_1716_ == 0)
{
v___x_1711_ = v___x_1698_;
v_isShared_1712_ = v_isSharedCheck_1716_;
goto v_resetjp_1710_;
}
else
{
lean_inc(v_a_1709_);
lean_dec(v___x_1698_);
v___x_1711_ = lean_box(0);
v_isShared_1712_ = v_isSharedCheck_1716_;
goto v_resetjp_1710_;
}
v_resetjp_1710_:
{
lean_object* v___x_1714_; 
if (v_isShared_1712_ == 0)
{
lean_ctor_set_tag(v___x_1711_, 0);
v___x_1714_ = v___x_1711_;
goto v_reusejp_1713_;
}
else
{
lean_object* v_reuseFailAlloc_1715_; 
v_reuseFailAlloc_1715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1715_, 0, v_a_1709_);
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
v_a_1717_ = lean_ctor_get(v___x_1698_, 0);
lean_inc(v_a_1717_);
lean_dec_ref(v___x_1698_);
v___x_1718_ = ((lean_object*)(l_Lean_Lsp_DeleteFile_instToJsonOptions_toJson___closed__1));
v___x_1719_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonChangeAnnotation_fromJson_spec__0(v_json_1696_, v___x_1718_);
if (lean_obj_tag(v___x_1719_) == 0)
{
lean_object* v_a_1720_; lean_object* v___x_1722_; uint8_t v_isShared_1723_; uint8_t v_isSharedCheck_1729_; 
lean_dec(v_a_1717_);
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
v___x_1724_ = lean_obj_once(&l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__11, &l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__11_once, _init_l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__11);
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
if (lean_obj_tag(v___x_1719_) == 0)
{
lean_object* v_a_1730_; lean_object* v___x_1732_; uint8_t v_isShared_1733_; uint8_t v_isSharedCheck_1737_; 
lean_dec(v_a_1717_);
v_a_1730_ = lean_ctor_get(v___x_1719_, 0);
v_isSharedCheck_1737_ = !lean_is_exclusive(v___x_1719_);
if (v_isSharedCheck_1737_ == 0)
{
v___x_1732_ = v___x_1719_;
v_isShared_1733_ = v_isSharedCheck_1737_;
goto v_resetjp_1731_;
}
else
{
lean_inc(v_a_1730_);
lean_dec(v___x_1719_);
v___x_1732_ = lean_box(0);
v_isShared_1733_ = v_isSharedCheck_1737_;
goto v_resetjp_1731_;
}
v_resetjp_1731_:
{
lean_object* v___x_1735_; 
if (v_isShared_1733_ == 0)
{
lean_ctor_set_tag(v___x_1732_, 0);
v___x_1735_ = v___x_1732_;
goto v_reusejp_1734_;
}
else
{
lean_object* v_reuseFailAlloc_1736_; 
v_reuseFailAlloc_1736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1736_, 0, v_a_1730_);
v___x_1735_ = v_reuseFailAlloc_1736_;
goto v_reusejp_1734_;
}
v_reusejp_1734_:
{
return v___x_1735_;
}
}
}
else
{
lean_object* v_a_1738_; lean_object* v___x_1740_; uint8_t v_isShared_1741_; uint8_t v_isSharedCheck_1748_; 
v_a_1738_ = lean_ctor_get(v___x_1719_, 0);
v_isSharedCheck_1748_ = !lean_is_exclusive(v___x_1719_);
if (v_isSharedCheck_1748_ == 0)
{
v___x_1740_ = v___x_1719_;
v_isShared_1741_ = v_isSharedCheck_1748_;
goto v_resetjp_1739_;
}
else
{
lean_inc(v_a_1738_);
lean_dec(v___x_1719_);
v___x_1740_ = lean_box(0);
v_isShared_1741_ = v_isSharedCheck_1748_;
goto v_resetjp_1739_;
}
v_resetjp_1739_:
{
lean_object* v___x_1742_; uint8_t v___x_1743_; uint8_t v___x_1744_; lean_object* v___x_1746_; 
v___x_1742_ = lean_alloc_ctor(0, 0, 2);
v___x_1743_ = lean_unbox(v_a_1717_);
lean_dec(v_a_1717_);
lean_ctor_set_uint8(v___x_1742_, 0, v___x_1743_);
v___x_1744_ = lean_unbox(v_a_1738_);
lean_dec(v_a_1738_);
lean_ctor_set_uint8(v___x_1742_, 1, v___x_1744_);
if (v_isShared_1741_ == 0)
{
lean_ctor_set(v___x_1740_, 0, v___x_1742_);
v___x_1746_ = v___x_1740_;
goto v_reusejp_1745_;
}
else
{
lean_object* v_reuseFailAlloc_1747_; 
v_reuseFailAlloc_1747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1747_, 0, v___x_1742_);
v___x_1746_ = v_reuseFailAlloc_1747_;
goto v_reusejp_1745_;
}
v_reusejp_1745_:
{
return v___x_1746_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonCreateFile_toJson_spec__0(lean_object* v_k_1751_, lean_object* v_x_1752_){
_start:
{
if (lean_obj_tag(v_x_1752_) == 0)
{
lean_object* v___x_1753_; 
lean_dec_ref(v_k_1751_);
v___x_1753_ = lean_box(0);
return v___x_1753_;
}
else
{
lean_object* v_val_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; 
v_val_1754_ = lean_ctor_get(v_x_1752_, 0);
v___x_1755_ = l_Lean_Lsp_CreateFile_instToJsonOptions_toJson(v_val_1754_);
v___x_1756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1756_, 0, v_k_1751_);
lean_ctor_set(v___x_1756_, 1, v___x_1755_);
v___x_1757_ = lean_box(0);
v___x_1758_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1758_, 0, v___x_1756_);
lean_ctor_set(v___x_1758_, 1, v___x_1757_);
return v___x_1758_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonCreateFile_toJson_spec__0___boxed(lean_object* v_k_1759_, lean_object* v_x_1760_){
_start:
{
lean_object* v_res_1761_; 
v_res_1761_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonCreateFile_toJson_spec__0(v_k_1759_, v_x_1760_);
lean_dec(v_x_1760_);
return v_res_1761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonCreateFile_toJson(lean_object* v_x_1763_){
_start:
{
lean_object* v_uri_1764_; lean_object* v_options_x3f_1765_; lean_object* v_annotationId_x3f_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; 
v_uri_1764_ = lean_ctor_get(v_x_1763_, 0);
lean_inc_ref(v_uri_1764_);
v_options_x3f_1765_ = lean_ctor_get(v_x_1763_, 1);
lean_inc(v_options_x3f_1765_);
v_annotationId_x3f_1766_ = lean_ctor_get(v_x_1763_, 2);
lean_inc(v_annotationId_x3f_1766_);
lean_dec_ref(v_x_1763_);
v___x_1767_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__0));
v___x_1768_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1768_, 0, v_uri_1764_);
v___x_1769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1769_, 0, v___x_1767_);
lean_ctor_set(v___x_1769_, 1, v___x_1768_);
v___x_1770_ = lean_box(0);
v___x_1771_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1771_, 0, v___x_1769_);
lean_ctor_set(v___x_1771_, 1, v___x_1770_);
v___x_1772_ = ((lean_object*)(l_Lean_Lsp_instToJsonCreateFile_toJson___closed__0));
v___x_1773_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonCreateFile_toJson_spec__0(v___x_1772_, v_options_x3f_1765_);
lean_dec(v_options_x3f_1765_);
v___x_1774_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextEdit_toJson___closed__2));
v___x_1775_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextEdit_toJson_spec__1(v___x_1774_, v_annotationId_x3f_1766_);
v___x_1776_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1776_, 0, v___x_1775_);
lean_ctor_set(v___x_1776_, 1, v___x_1770_);
v___x_1777_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1777_, 0, v___x_1773_);
lean_ctor_set(v___x_1777_, 1, v___x_1776_);
v___x_1778_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1778_, 0, v___x_1771_);
lean_ctor_set(v___x_1778_, 1, v___x_1777_);
v___x_1779_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__2));
v___x_1780_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLocation_toJson_spec__0(v___x_1778_, v___x_1779_);
v___x_1781_ = l_Lean_Json_mkObj(v___x_1780_);
return v___x_1781_;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCreateFile_fromJson_spec__0_spec__0(lean_object* v_x_1786_){
_start:
{
if (lean_obj_tag(v_x_1786_) == 0)
{
lean_object* v___x_1787_; 
v___x_1787_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCreateFile_fromJson_spec__0_spec__0___closed__0));
return v___x_1787_;
}
else
{
lean_object* v___x_1788_; 
v___x_1788_ = l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson(v_x_1786_);
if (lean_obj_tag(v___x_1788_) == 0)
{
lean_object* v_a_1789_; lean_object* v___x_1791_; uint8_t v_isShared_1792_; uint8_t v_isSharedCheck_1796_; 
v_a_1789_ = lean_ctor_get(v___x_1788_, 0);
v_isSharedCheck_1796_ = !lean_is_exclusive(v___x_1788_);
if (v_isSharedCheck_1796_ == 0)
{
v___x_1791_ = v___x_1788_;
v_isShared_1792_ = v_isSharedCheck_1796_;
goto v_resetjp_1790_;
}
else
{
lean_inc(v_a_1789_);
lean_dec(v___x_1788_);
v___x_1791_ = lean_box(0);
v_isShared_1792_ = v_isSharedCheck_1796_;
goto v_resetjp_1790_;
}
v_resetjp_1790_:
{
lean_object* v___x_1794_; 
if (v_isShared_1792_ == 0)
{
v___x_1794_ = v___x_1791_;
goto v_reusejp_1793_;
}
else
{
lean_object* v_reuseFailAlloc_1795_; 
v_reuseFailAlloc_1795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1795_, 0, v_a_1789_);
v___x_1794_ = v_reuseFailAlloc_1795_;
goto v_reusejp_1793_;
}
v_reusejp_1793_:
{
return v___x_1794_;
}
}
}
else
{
lean_object* v_a_1797_; lean_object* v___x_1799_; uint8_t v_isShared_1800_; uint8_t v_isSharedCheck_1805_; 
v_a_1797_ = lean_ctor_get(v___x_1788_, 0);
v_isSharedCheck_1805_ = !lean_is_exclusive(v___x_1788_);
if (v_isSharedCheck_1805_ == 0)
{
v___x_1799_ = v___x_1788_;
v_isShared_1800_ = v_isSharedCheck_1805_;
goto v_resetjp_1798_;
}
else
{
lean_inc(v_a_1797_);
lean_dec(v___x_1788_);
v___x_1799_ = lean_box(0);
v_isShared_1800_ = v_isSharedCheck_1805_;
goto v_resetjp_1798_;
}
v_resetjp_1798_:
{
lean_object* v___x_1801_; lean_object* v___x_1803_; 
v___x_1801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1801_, 0, v_a_1797_);
if (v_isShared_1800_ == 0)
{
lean_ctor_set(v___x_1799_, 0, v___x_1801_);
v___x_1803_ = v___x_1799_;
goto v_reusejp_1802_;
}
else
{
lean_object* v_reuseFailAlloc_1804_; 
v_reuseFailAlloc_1804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1804_, 0, v___x_1801_);
v___x_1803_ = v_reuseFailAlloc_1804_;
goto v_reusejp_1802_;
}
v_reusejp_1802_:
{
return v___x_1803_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCreateFile_fromJson_spec__0(lean_object* v_j_1806_, lean_object* v_k_1807_){
_start:
{
lean_object* v___x_1808_; lean_object* v___x_1809_; 
v___x_1808_ = l_Lean_Json_getObjValD(v_j_1806_, v_k_1807_);
v___x_1809_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCreateFile_fromJson_spec__0_spec__0(v___x_1808_);
return v___x_1809_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCreateFile_fromJson_spec__0___boxed(lean_object* v_j_1810_, lean_object* v_k_1811_){
_start:
{
lean_object* v_res_1812_; 
v_res_1812_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCreateFile_fromJson_spec__0(v_j_1810_, v_k_1811_);
lean_dec_ref(v_k_1811_);
return v_res_1812_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__1(void){
_start:
{
uint8_t v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; 
v___x_1817_ = 1;
v___x_1818_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__0));
v___x_1819_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1818_, v___x_1817_);
return v___x_1819_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__2(void){
_start:
{
lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; 
v___x_1820_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__5));
v___x_1821_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__1, &l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__1_once, _init_l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__1);
v___x_1822_ = lean_string_append(v___x_1821_, v___x_1820_);
return v___x_1822_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__3(void){
_start:
{
lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; 
v___x_1823_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLocation_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLocation_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLocation_fromJson___closed__8);
v___x_1824_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__2, &l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__2);
v___x_1825_ = lean_string_append(v___x_1824_, v___x_1823_);
return v___x_1825_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__4(void){
_start:
{
lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; 
v___x_1826_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_1827_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__3, &l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__3);
v___x_1828_ = lean_string_append(v___x_1827_, v___x_1826_);
return v___x_1828_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__7(void){
_start:
{
uint8_t v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; 
v___x_1832_ = 1;
v___x_1833_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__6));
v___x_1834_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1833_, v___x_1832_);
return v___x_1834_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__8(void){
_start:
{
lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; 
v___x_1835_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__7, &l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__7);
v___x_1836_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__2, &l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__2);
v___x_1837_ = lean_string_append(v___x_1836_, v___x_1835_);
return v___x_1837_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__9(void){
_start:
{
lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; 
v___x_1838_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_1839_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__8, &l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__8);
v___x_1840_ = lean_string_append(v___x_1839_, v___x_1838_);
return v___x_1840_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__10(void){
_start:
{
lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; 
v___x_1841_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__17, &l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__17_once, _init_l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__17);
v___x_1842_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__2, &l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__2);
v___x_1843_ = lean_string_append(v___x_1842_, v___x_1841_);
return v___x_1843_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__11(void){
_start:
{
lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; 
v___x_1844_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_1845_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__10, &l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__10);
v___x_1846_ = lean_string_append(v___x_1845_, v___x_1844_);
return v___x_1846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonCreateFile_fromJson(lean_object* v_json_1847_){
_start:
{
lean_object* v___x_1848_; lean_object* v___x_1849_; 
v___x_1848_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__0));
lean_inc(v_json_1847_);
v___x_1849_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocation_fromJson_spec__0(v_json_1847_, v___x_1848_);
if (lean_obj_tag(v___x_1849_) == 0)
{
lean_object* v_a_1850_; lean_object* v___x_1852_; uint8_t v_isShared_1853_; uint8_t v_isSharedCheck_1859_; 
lean_dec(v_json_1847_);
v_a_1850_ = lean_ctor_get(v___x_1849_, 0);
v_isSharedCheck_1859_ = !lean_is_exclusive(v___x_1849_);
if (v_isSharedCheck_1859_ == 0)
{
v___x_1852_ = v___x_1849_;
v_isShared_1853_ = v_isSharedCheck_1859_;
goto v_resetjp_1851_;
}
else
{
lean_inc(v_a_1850_);
lean_dec(v___x_1849_);
v___x_1852_ = lean_box(0);
v_isShared_1853_ = v_isSharedCheck_1859_;
goto v_resetjp_1851_;
}
v_resetjp_1851_:
{
lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1857_; 
v___x_1854_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__4, &l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__4);
v___x_1855_ = lean_string_append(v___x_1854_, v_a_1850_);
lean_dec(v_a_1850_);
if (v_isShared_1853_ == 0)
{
lean_ctor_set(v___x_1852_, 0, v___x_1855_);
v___x_1857_ = v___x_1852_;
goto v_reusejp_1856_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v___x_1855_);
v___x_1857_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1856_;
}
v_reusejp_1856_:
{
return v___x_1857_;
}
}
}
else
{
if (lean_obj_tag(v___x_1849_) == 0)
{
lean_object* v_a_1860_; lean_object* v___x_1862_; uint8_t v_isShared_1863_; uint8_t v_isSharedCheck_1867_; 
lean_dec(v_json_1847_);
v_a_1860_ = lean_ctor_get(v___x_1849_, 0);
v_isSharedCheck_1867_ = !lean_is_exclusive(v___x_1849_);
if (v_isSharedCheck_1867_ == 0)
{
v___x_1862_ = v___x_1849_;
v_isShared_1863_ = v_isSharedCheck_1867_;
goto v_resetjp_1861_;
}
else
{
lean_inc(v_a_1860_);
lean_dec(v___x_1849_);
v___x_1862_ = lean_box(0);
v_isShared_1863_ = v_isSharedCheck_1867_;
goto v_resetjp_1861_;
}
v_resetjp_1861_:
{
lean_object* v___x_1865_; 
if (v_isShared_1863_ == 0)
{
lean_ctor_set_tag(v___x_1862_, 0);
v___x_1865_ = v___x_1862_;
goto v_reusejp_1864_;
}
else
{
lean_object* v_reuseFailAlloc_1866_; 
v_reuseFailAlloc_1866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1866_, 0, v_a_1860_);
v___x_1865_ = v_reuseFailAlloc_1866_;
goto v_reusejp_1864_;
}
v_reusejp_1864_:
{
return v___x_1865_;
}
}
}
else
{
lean_object* v_a_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; 
v_a_1868_ = lean_ctor_get(v___x_1849_, 0);
lean_inc(v_a_1868_);
lean_dec_ref(v___x_1849_);
v___x_1869_ = ((lean_object*)(l_Lean_Lsp_instToJsonCreateFile_toJson___closed__0));
lean_inc(v_json_1847_);
v___x_1870_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCreateFile_fromJson_spec__0(v_json_1847_, v___x_1869_);
if (lean_obj_tag(v___x_1870_) == 0)
{
lean_object* v_a_1871_; lean_object* v___x_1873_; uint8_t v_isShared_1874_; uint8_t v_isSharedCheck_1880_; 
lean_dec(v_a_1868_);
lean_dec(v_json_1847_);
v_a_1871_ = lean_ctor_get(v___x_1870_, 0);
v_isSharedCheck_1880_ = !lean_is_exclusive(v___x_1870_);
if (v_isSharedCheck_1880_ == 0)
{
v___x_1873_ = v___x_1870_;
v_isShared_1874_ = v_isSharedCheck_1880_;
goto v_resetjp_1872_;
}
else
{
lean_inc(v_a_1871_);
lean_dec(v___x_1870_);
v___x_1873_ = lean_box(0);
v_isShared_1874_ = v_isSharedCheck_1880_;
goto v_resetjp_1872_;
}
v_resetjp_1872_:
{
lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1878_; 
v___x_1875_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__9, &l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__9);
v___x_1876_ = lean_string_append(v___x_1875_, v_a_1871_);
lean_dec(v_a_1871_);
if (v_isShared_1874_ == 0)
{
lean_ctor_set(v___x_1873_, 0, v___x_1876_);
v___x_1878_ = v___x_1873_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1879_; 
v_reuseFailAlloc_1879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1879_, 0, v___x_1876_);
v___x_1878_ = v_reuseFailAlloc_1879_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
return v___x_1878_;
}
}
}
else
{
if (lean_obj_tag(v___x_1870_) == 0)
{
lean_object* v_a_1881_; lean_object* v___x_1883_; uint8_t v_isShared_1884_; uint8_t v_isSharedCheck_1888_; 
lean_dec(v_a_1868_);
lean_dec(v_json_1847_);
v_a_1881_ = lean_ctor_get(v___x_1870_, 0);
v_isSharedCheck_1888_ = !lean_is_exclusive(v___x_1870_);
if (v_isSharedCheck_1888_ == 0)
{
v___x_1883_ = v___x_1870_;
v_isShared_1884_ = v_isSharedCheck_1888_;
goto v_resetjp_1882_;
}
else
{
lean_inc(v_a_1881_);
lean_dec(v___x_1870_);
v___x_1883_ = lean_box(0);
v_isShared_1884_ = v_isSharedCheck_1888_;
goto v_resetjp_1882_;
}
v_resetjp_1882_:
{
lean_object* v___x_1886_; 
if (v_isShared_1884_ == 0)
{
lean_ctor_set_tag(v___x_1883_, 0);
v___x_1886_ = v___x_1883_;
goto v_reusejp_1885_;
}
else
{
lean_object* v_reuseFailAlloc_1887_; 
v_reuseFailAlloc_1887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1887_, 0, v_a_1881_);
v___x_1886_ = v_reuseFailAlloc_1887_;
goto v_reusejp_1885_;
}
v_reusejp_1885_:
{
return v___x_1886_;
}
}
}
else
{
lean_object* v_a_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; 
v_a_1889_ = lean_ctor_get(v___x_1870_, 0);
lean_inc(v_a_1889_);
lean_dec_ref(v___x_1870_);
v___x_1890_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextEdit_toJson___closed__2));
v___x_1891_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextEdit_fromJson_spec__1(v_json_1847_, v___x_1890_);
if (lean_obj_tag(v___x_1891_) == 0)
{
lean_object* v_a_1892_; lean_object* v___x_1894_; uint8_t v_isShared_1895_; uint8_t v_isSharedCheck_1901_; 
lean_dec(v_a_1889_);
lean_dec(v_a_1868_);
v_a_1892_ = lean_ctor_get(v___x_1891_, 0);
v_isSharedCheck_1901_ = !lean_is_exclusive(v___x_1891_);
if (v_isSharedCheck_1901_ == 0)
{
v___x_1894_ = v___x_1891_;
v_isShared_1895_ = v_isSharedCheck_1901_;
goto v_resetjp_1893_;
}
else
{
lean_inc(v_a_1892_);
lean_dec(v___x_1891_);
v___x_1894_ = lean_box(0);
v_isShared_1895_ = v_isSharedCheck_1901_;
goto v_resetjp_1893_;
}
v_resetjp_1893_:
{
lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1899_; 
v___x_1896_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__11, &l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__11);
v___x_1897_ = lean_string_append(v___x_1896_, v_a_1892_);
lean_dec(v_a_1892_);
if (v_isShared_1895_ == 0)
{
lean_ctor_set(v___x_1894_, 0, v___x_1897_);
v___x_1899_ = v___x_1894_;
goto v_reusejp_1898_;
}
else
{
lean_object* v_reuseFailAlloc_1900_; 
v_reuseFailAlloc_1900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1900_, 0, v___x_1897_);
v___x_1899_ = v_reuseFailAlloc_1900_;
goto v_reusejp_1898_;
}
v_reusejp_1898_:
{
return v___x_1899_;
}
}
}
else
{
if (lean_obj_tag(v___x_1891_) == 0)
{
lean_object* v_a_1902_; lean_object* v___x_1904_; uint8_t v_isShared_1905_; uint8_t v_isSharedCheck_1909_; 
lean_dec(v_a_1889_);
lean_dec(v_a_1868_);
v_a_1902_ = lean_ctor_get(v___x_1891_, 0);
v_isSharedCheck_1909_ = !lean_is_exclusive(v___x_1891_);
if (v_isSharedCheck_1909_ == 0)
{
v___x_1904_ = v___x_1891_;
v_isShared_1905_ = v_isSharedCheck_1909_;
goto v_resetjp_1903_;
}
else
{
lean_inc(v_a_1902_);
lean_dec(v___x_1891_);
v___x_1904_ = lean_box(0);
v_isShared_1905_ = v_isSharedCheck_1909_;
goto v_resetjp_1903_;
}
v_resetjp_1903_:
{
lean_object* v___x_1907_; 
if (v_isShared_1905_ == 0)
{
lean_ctor_set_tag(v___x_1904_, 0);
v___x_1907_ = v___x_1904_;
goto v_reusejp_1906_;
}
else
{
lean_object* v_reuseFailAlloc_1908_; 
v_reuseFailAlloc_1908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1908_, 0, v_a_1902_);
v___x_1907_ = v_reuseFailAlloc_1908_;
goto v_reusejp_1906_;
}
v_reusejp_1906_:
{
return v___x_1907_;
}
}
}
else
{
lean_object* v_a_1910_; lean_object* v___x_1912_; uint8_t v_isShared_1913_; uint8_t v_isSharedCheck_1918_; 
v_a_1910_ = lean_ctor_get(v___x_1891_, 0);
v_isSharedCheck_1918_ = !lean_is_exclusive(v___x_1891_);
if (v_isSharedCheck_1918_ == 0)
{
v___x_1912_ = v___x_1891_;
v_isShared_1913_ = v_isSharedCheck_1918_;
goto v_resetjp_1911_;
}
else
{
lean_inc(v_a_1910_);
lean_dec(v___x_1891_);
v___x_1912_ = lean_box(0);
v_isShared_1913_ = v_isSharedCheck_1918_;
goto v_resetjp_1911_;
}
v_resetjp_1911_:
{
lean_object* v___x_1914_; lean_object* v___x_1916_; 
v___x_1914_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1914_, 0, v_a_1868_);
lean_ctor_set(v___x_1914_, 1, v_a_1889_);
lean_ctor_set(v___x_1914_, 2, v_a_1910_);
if (v_isShared_1913_ == 0)
{
lean_ctor_set(v___x_1912_, 0, v___x_1914_);
v___x_1916_ = v___x_1912_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1917_; 
v_reuseFailAlloc_1917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1917_, 0, v___x_1914_);
v___x_1916_ = v_reuseFailAlloc_1917_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
return v___x_1916_;
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
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRenameFile_toJson(lean_object* v_x_1923_){
_start:
{
lean_object* v_oldUri_1924_; lean_object* v_newUri_1925_; lean_object* v_options_x3f_1926_; lean_object* v_annotationId_x3f_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; 
v_oldUri_1924_ = lean_ctor_get(v_x_1923_, 0);
lean_inc_ref(v_oldUri_1924_);
v_newUri_1925_ = lean_ctor_get(v_x_1923_, 1);
lean_inc_ref(v_newUri_1925_);
v_options_x3f_1926_ = lean_ctor_get(v_x_1923_, 2);
lean_inc(v_options_x3f_1926_);
v_annotationId_x3f_1927_ = lean_ctor_get(v_x_1923_, 3);
lean_inc(v_annotationId_x3f_1927_);
lean_dec_ref(v_x_1923_);
v___x_1928_ = ((lean_object*)(l_Lean_Lsp_instToJsonRenameFile_toJson___closed__0));
v___x_1929_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1929_, 0, v_oldUri_1924_);
v___x_1930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1930_, 0, v___x_1928_);
lean_ctor_set(v___x_1930_, 1, v___x_1929_);
v___x_1931_ = lean_box(0);
v___x_1932_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1932_, 0, v___x_1930_);
lean_ctor_set(v___x_1932_, 1, v___x_1931_);
v___x_1933_ = ((lean_object*)(l_Lean_Lsp_instToJsonRenameFile_toJson___closed__1));
v___x_1934_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1934_, 0, v_newUri_1925_);
v___x_1935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1935_, 0, v___x_1933_);
lean_ctor_set(v___x_1935_, 1, v___x_1934_);
v___x_1936_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1936_, 0, v___x_1935_);
lean_ctor_set(v___x_1936_, 1, v___x_1931_);
v___x_1937_ = ((lean_object*)(l_Lean_Lsp_instToJsonCreateFile_toJson___closed__0));
v___x_1938_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonCreateFile_toJson_spec__0(v___x_1937_, v_options_x3f_1926_);
lean_dec(v_options_x3f_1926_);
v___x_1939_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextEdit_toJson___closed__2));
v___x_1940_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextEdit_toJson_spec__1(v___x_1939_, v_annotationId_x3f_1927_);
v___x_1941_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1941_, 0, v___x_1940_);
lean_ctor_set(v___x_1941_, 1, v___x_1931_);
v___x_1942_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1942_, 0, v___x_1938_);
lean_ctor_set(v___x_1942_, 1, v___x_1941_);
v___x_1943_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1943_, 0, v___x_1936_);
lean_ctor_set(v___x_1943_, 1, v___x_1942_);
v___x_1944_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1944_, 0, v___x_1932_);
lean_ctor_set(v___x_1944_, 1, v___x_1943_);
v___x_1945_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__2));
v___x_1946_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLocation_toJson_spec__0(v___x_1944_, v___x_1945_);
v___x_1947_ = l_Lean_Json_mkObj(v___x_1946_);
return v___x_1947_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__2(void){
_start:
{
uint8_t v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; 
v___x_1955_ = 1;
v___x_1956_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__1));
v___x_1957_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1956_, v___x_1955_);
return v___x_1957_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__3(void){
_start:
{
lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; 
v___x_1958_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__5));
v___x_1959_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__2, &l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__2);
v___x_1960_ = lean_string_append(v___x_1959_, v___x_1958_);
return v___x_1960_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__5(void){
_start:
{
uint8_t v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; 
v___x_1963_ = 1;
v___x_1964_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__4));
v___x_1965_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1964_, v___x_1963_);
return v___x_1965_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__6(void){
_start:
{
lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; 
v___x_1966_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__5, &l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__5);
v___x_1967_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__3, &l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__3);
v___x_1968_ = lean_string_append(v___x_1967_, v___x_1966_);
return v___x_1968_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__7(void){
_start:
{
lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; 
v___x_1969_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_1970_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__6, &l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__6);
v___x_1971_ = lean_string_append(v___x_1970_, v___x_1969_);
return v___x_1971_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__9(void){
_start:
{
uint8_t v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; 
v___x_1974_ = 1;
v___x_1975_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__8));
v___x_1976_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1975_, v___x_1974_);
return v___x_1976_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__10(void){
_start:
{
lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; 
v___x_1977_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__9, &l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__9);
v___x_1978_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__3, &l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__3);
v___x_1979_ = lean_string_append(v___x_1978_, v___x_1977_);
return v___x_1979_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__11(void){
_start:
{
lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; 
v___x_1980_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_1981_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__10, &l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__10);
v___x_1982_ = lean_string_append(v___x_1981_, v___x_1980_);
return v___x_1982_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__12(void){
_start:
{
lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; 
v___x_1983_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__7, &l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__7);
v___x_1984_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__3, &l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__3);
v___x_1985_ = lean_string_append(v___x_1984_, v___x_1983_);
return v___x_1985_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__13(void){
_start:
{
lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; 
v___x_1986_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_1987_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__12, &l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__12);
v___x_1988_ = lean_string_append(v___x_1987_, v___x_1986_);
return v___x_1988_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__14(void){
_start:
{
lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; 
v___x_1989_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__17, &l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__17_once, _init_l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__17);
v___x_1990_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__3, &l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__3);
v___x_1991_ = lean_string_append(v___x_1990_, v___x_1989_);
return v___x_1991_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__15(void){
_start:
{
lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; 
v___x_1992_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_1993_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__14, &l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__14_once, _init_l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__14);
v___x_1994_ = lean_string_append(v___x_1993_, v___x_1992_);
return v___x_1994_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonRenameFile_fromJson(lean_object* v_json_1995_){
_start:
{
lean_object* v___x_1996_; lean_object* v___x_1997_; 
v___x_1996_ = ((lean_object*)(l_Lean_Lsp_instToJsonRenameFile_toJson___closed__0));
lean_inc(v_json_1995_);
v___x_1997_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocation_fromJson_spec__0(v_json_1995_, v___x_1996_);
if (lean_obj_tag(v___x_1997_) == 0)
{
lean_object* v_a_1998_; lean_object* v___x_2000_; uint8_t v_isShared_2001_; uint8_t v_isSharedCheck_2007_; 
lean_dec(v_json_1995_);
v_a_1998_ = lean_ctor_get(v___x_1997_, 0);
v_isSharedCheck_2007_ = !lean_is_exclusive(v___x_1997_);
if (v_isSharedCheck_2007_ == 0)
{
v___x_2000_ = v___x_1997_;
v_isShared_2001_ = v_isSharedCheck_2007_;
goto v_resetjp_1999_;
}
else
{
lean_inc(v_a_1998_);
lean_dec(v___x_1997_);
v___x_2000_ = lean_box(0);
v_isShared_2001_ = v_isSharedCheck_2007_;
goto v_resetjp_1999_;
}
v_resetjp_1999_:
{
lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2005_; 
v___x_2002_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__7, &l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__7);
v___x_2003_ = lean_string_append(v___x_2002_, v_a_1998_);
lean_dec(v_a_1998_);
if (v_isShared_2001_ == 0)
{
lean_ctor_set(v___x_2000_, 0, v___x_2003_);
v___x_2005_ = v___x_2000_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2006_; 
v_reuseFailAlloc_2006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2006_, 0, v___x_2003_);
v___x_2005_ = v_reuseFailAlloc_2006_;
goto v_reusejp_2004_;
}
v_reusejp_2004_:
{
return v___x_2005_;
}
}
}
else
{
if (lean_obj_tag(v___x_1997_) == 0)
{
lean_object* v_a_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2015_; 
lean_dec(v_json_1995_);
v_a_2008_ = lean_ctor_get(v___x_1997_, 0);
v_isSharedCheck_2015_ = !lean_is_exclusive(v___x_1997_);
if (v_isSharedCheck_2015_ == 0)
{
v___x_2010_ = v___x_1997_;
v_isShared_2011_ = v_isSharedCheck_2015_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_a_2008_);
lean_dec(v___x_1997_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2015_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
lean_object* v___x_2013_; 
if (v_isShared_2011_ == 0)
{
lean_ctor_set_tag(v___x_2010_, 0);
v___x_2013_ = v___x_2010_;
goto v_reusejp_2012_;
}
else
{
lean_object* v_reuseFailAlloc_2014_; 
v_reuseFailAlloc_2014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2014_, 0, v_a_2008_);
v___x_2013_ = v_reuseFailAlloc_2014_;
goto v_reusejp_2012_;
}
v_reusejp_2012_:
{
return v___x_2013_;
}
}
}
else
{
lean_object* v_a_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; 
v_a_2016_ = lean_ctor_get(v___x_1997_, 0);
lean_inc(v_a_2016_);
lean_dec_ref(v___x_1997_);
v___x_2017_ = ((lean_object*)(l_Lean_Lsp_instToJsonRenameFile_toJson___closed__1));
lean_inc(v_json_1995_);
v___x_2018_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocation_fromJson_spec__0(v_json_1995_, v___x_2017_);
if (lean_obj_tag(v___x_2018_) == 0)
{
lean_object* v_a_2019_; lean_object* v___x_2021_; uint8_t v_isShared_2022_; uint8_t v_isSharedCheck_2028_; 
lean_dec(v_a_2016_);
lean_dec(v_json_1995_);
v_a_2019_ = lean_ctor_get(v___x_2018_, 0);
v_isSharedCheck_2028_ = !lean_is_exclusive(v___x_2018_);
if (v_isSharedCheck_2028_ == 0)
{
v___x_2021_ = v___x_2018_;
v_isShared_2022_ = v_isSharedCheck_2028_;
goto v_resetjp_2020_;
}
else
{
lean_inc(v_a_2019_);
lean_dec(v___x_2018_);
v___x_2021_ = lean_box(0);
v_isShared_2022_ = v_isSharedCheck_2028_;
goto v_resetjp_2020_;
}
v_resetjp_2020_:
{
lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2026_; 
v___x_2023_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__11, &l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__11);
v___x_2024_ = lean_string_append(v___x_2023_, v_a_2019_);
lean_dec(v_a_2019_);
if (v_isShared_2022_ == 0)
{
lean_ctor_set(v___x_2021_, 0, v___x_2024_);
v___x_2026_ = v___x_2021_;
goto v_reusejp_2025_;
}
else
{
lean_object* v_reuseFailAlloc_2027_; 
v_reuseFailAlloc_2027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2027_, 0, v___x_2024_);
v___x_2026_ = v_reuseFailAlloc_2027_;
goto v_reusejp_2025_;
}
v_reusejp_2025_:
{
return v___x_2026_;
}
}
}
else
{
if (lean_obj_tag(v___x_2018_) == 0)
{
lean_object* v_a_2029_; lean_object* v___x_2031_; uint8_t v_isShared_2032_; uint8_t v_isSharedCheck_2036_; 
lean_dec(v_a_2016_);
lean_dec(v_json_1995_);
v_a_2029_ = lean_ctor_get(v___x_2018_, 0);
v_isSharedCheck_2036_ = !lean_is_exclusive(v___x_2018_);
if (v_isSharedCheck_2036_ == 0)
{
v___x_2031_ = v___x_2018_;
v_isShared_2032_ = v_isSharedCheck_2036_;
goto v_resetjp_2030_;
}
else
{
lean_inc(v_a_2029_);
lean_dec(v___x_2018_);
v___x_2031_ = lean_box(0);
v_isShared_2032_ = v_isSharedCheck_2036_;
goto v_resetjp_2030_;
}
v_resetjp_2030_:
{
lean_object* v___x_2034_; 
if (v_isShared_2032_ == 0)
{
lean_ctor_set_tag(v___x_2031_, 0);
v___x_2034_ = v___x_2031_;
goto v_reusejp_2033_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v_a_2029_);
v___x_2034_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2033_;
}
v_reusejp_2033_:
{
return v___x_2034_;
}
}
}
else
{
lean_object* v_a_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; 
v_a_2037_ = lean_ctor_get(v___x_2018_, 0);
lean_inc(v_a_2037_);
lean_dec_ref(v___x_2018_);
v___x_2038_ = ((lean_object*)(l_Lean_Lsp_instToJsonCreateFile_toJson___closed__0));
lean_inc(v_json_1995_);
v___x_2039_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCreateFile_fromJson_spec__0(v_json_1995_, v___x_2038_);
if (lean_obj_tag(v___x_2039_) == 0)
{
lean_object* v_a_2040_; lean_object* v___x_2042_; uint8_t v_isShared_2043_; uint8_t v_isSharedCheck_2049_; 
lean_dec(v_a_2037_);
lean_dec(v_a_2016_);
lean_dec(v_json_1995_);
v_a_2040_ = lean_ctor_get(v___x_2039_, 0);
v_isSharedCheck_2049_ = !lean_is_exclusive(v___x_2039_);
if (v_isSharedCheck_2049_ == 0)
{
v___x_2042_ = v___x_2039_;
v_isShared_2043_ = v_isSharedCheck_2049_;
goto v_resetjp_2041_;
}
else
{
lean_inc(v_a_2040_);
lean_dec(v___x_2039_);
v___x_2042_ = lean_box(0);
v_isShared_2043_ = v_isSharedCheck_2049_;
goto v_resetjp_2041_;
}
v_resetjp_2041_:
{
lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2047_; 
v___x_2044_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__13, &l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__13);
v___x_2045_ = lean_string_append(v___x_2044_, v_a_2040_);
lean_dec(v_a_2040_);
if (v_isShared_2043_ == 0)
{
lean_ctor_set(v___x_2042_, 0, v___x_2045_);
v___x_2047_ = v___x_2042_;
goto v_reusejp_2046_;
}
else
{
lean_object* v_reuseFailAlloc_2048_; 
v_reuseFailAlloc_2048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2048_, 0, v___x_2045_);
v___x_2047_ = v_reuseFailAlloc_2048_;
goto v_reusejp_2046_;
}
v_reusejp_2046_:
{
return v___x_2047_;
}
}
}
else
{
if (lean_obj_tag(v___x_2039_) == 0)
{
lean_object* v_a_2050_; lean_object* v___x_2052_; uint8_t v_isShared_2053_; uint8_t v_isSharedCheck_2057_; 
lean_dec(v_a_2037_);
lean_dec(v_a_2016_);
lean_dec(v_json_1995_);
v_a_2050_ = lean_ctor_get(v___x_2039_, 0);
v_isSharedCheck_2057_ = !lean_is_exclusive(v___x_2039_);
if (v_isSharedCheck_2057_ == 0)
{
v___x_2052_ = v___x_2039_;
v_isShared_2053_ = v_isSharedCheck_2057_;
goto v_resetjp_2051_;
}
else
{
lean_inc(v_a_2050_);
lean_dec(v___x_2039_);
v___x_2052_ = lean_box(0);
v_isShared_2053_ = v_isSharedCheck_2057_;
goto v_resetjp_2051_;
}
v_resetjp_2051_:
{
lean_object* v___x_2055_; 
if (v_isShared_2053_ == 0)
{
lean_ctor_set_tag(v___x_2052_, 0);
v___x_2055_ = v___x_2052_;
goto v_reusejp_2054_;
}
else
{
lean_object* v_reuseFailAlloc_2056_; 
v_reuseFailAlloc_2056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2056_, 0, v_a_2050_);
v___x_2055_ = v_reuseFailAlloc_2056_;
goto v_reusejp_2054_;
}
v_reusejp_2054_:
{
return v___x_2055_;
}
}
}
else
{
lean_object* v_a_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; 
v_a_2058_ = lean_ctor_get(v___x_2039_, 0);
lean_inc(v_a_2058_);
lean_dec_ref(v___x_2039_);
v___x_2059_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextEdit_toJson___closed__2));
v___x_2060_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextEdit_fromJson_spec__1(v_json_1995_, v___x_2059_);
if (lean_obj_tag(v___x_2060_) == 0)
{
lean_object* v_a_2061_; lean_object* v___x_2063_; uint8_t v_isShared_2064_; uint8_t v_isSharedCheck_2070_; 
lean_dec(v_a_2058_);
lean_dec(v_a_2037_);
lean_dec(v_a_2016_);
v_a_2061_ = lean_ctor_get(v___x_2060_, 0);
v_isSharedCheck_2070_ = !lean_is_exclusive(v___x_2060_);
if (v_isSharedCheck_2070_ == 0)
{
v___x_2063_ = v___x_2060_;
v_isShared_2064_ = v_isSharedCheck_2070_;
goto v_resetjp_2062_;
}
else
{
lean_inc(v_a_2061_);
lean_dec(v___x_2060_);
v___x_2063_ = lean_box(0);
v_isShared_2064_ = v_isSharedCheck_2070_;
goto v_resetjp_2062_;
}
v_resetjp_2062_:
{
lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2068_; 
v___x_2065_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__15, &l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__15_once, _init_l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__15);
v___x_2066_ = lean_string_append(v___x_2065_, v_a_2061_);
lean_dec(v_a_2061_);
if (v_isShared_2064_ == 0)
{
lean_ctor_set(v___x_2063_, 0, v___x_2066_);
v___x_2068_ = v___x_2063_;
goto v_reusejp_2067_;
}
else
{
lean_object* v_reuseFailAlloc_2069_; 
v_reuseFailAlloc_2069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2069_, 0, v___x_2066_);
v___x_2068_ = v_reuseFailAlloc_2069_;
goto v_reusejp_2067_;
}
v_reusejp_2067_:
{
return v___x_2068_;
}
}
}
else
{
if (lean_obj_tag(v___x_2060_) == 0)
{
lean_object* v_a_2071_; lean_object* v___x_2073_; uint8_t v_isShared_2074_; uint8_t v_isSharedCheck_2078_; 
lean_dec(v_a_2058_);
lean_dec(v_a_2037_);
lean_dec(v_a_2016_);
v_a_2071_ = lean_ctor_get(v___x_2060_, 0);
v_isSharedCheck_2078_ = !lean_is_exclusive(v___x_2060_);
if (v_isSharedCheck_2078_ == 0)
{
v___x_2073_ = v___x_2060_;
v_isShared_2074_ = v_isSharedCheck_2078_;
goto v_resetjp_2072_;
}
else
{
lean_inc(v_a_2071_);
lean_dec(v___x_2060_);
v___x_2073_ = lean_box(0);
v_isShared_2074_ = v_isSharedCheck_2078_;
goto v_resetjp_2072_;
}
v_resetjp_2072_:
{
lean_object* v___x_2076_; 
if (v_isShared_2074_ == 0)
{
lean_ctor_set_tag(v___x_2073_, 0);
v___x_2076_ = v___x_2073_;
goto v_reusejp_2075_;
}
else
{
lean_object* v_reuseFailAlloc_2077_; 
v_reuseFailAlloc_2077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2077_, 0, v_a_2071_);
v___x_2076_ = v_reuseFailAlloc_2077_;
goto v_reusejp_2075_;
}
v_reusejp_2075_:
{
return v___x_2076_;
}
}
}
else
{
lean_object* v_a_2079_; lean_object* v___x_2081_; uint8_t v_isShared_2082_; uint8_t v_isSharedCheck_2087_; 
v_a_2079_ = lean_ctor_get(v___x_2060_, 0);
v_isSharedCheck_2087_ = !lean_is_exclusive(v___x_2060_);
if (v_isSharedCheck_2087_ == 0)
{
v___x_2081_ = v___x_2060_;
v_isShared_2082_ = v_isSharedCheck_2087_;
goto v_resetjp_2080_;
}
else
{
lean_inc(v_a_2079_);
lean_dec(v___x_2060_);
v___x_2081_ = lean_box(0);
v_isShared_2082_ = v_isSharedCheck_2087_;
goto v_resetjp_2080_;
}
v_resetjp_2080_:
{
lean_object* v___x_2083_; lean_object* v___x_2085_; 
v___x_2083_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2083_, 0, v_a_2016_);
lean_ctor_set(v___x_2083_, 1, v_a_2037_);
lean_ctor_set(v___x_2083_, 2, v_a_2058_);
lean_ctor_set(v___x_2083_, 3, v_a_2079_);
if (v_isShared_2082_ == 0)
{
lean_ctor_set(v___x_2081_, 0, v___x_2083_);
v___x_2085_ = v___x_2081_;
goto v_reusejp_2084_;
}
else
{
lean_object* v_reuseFailAlloc_2086_; 
v_reuseFailAlloc_2086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2086_, 0, v___x_2083_);
v___x_2085_ = v_reuseFailAlloc_2086_;
goto v_reusejp_2084_;
}
v_reusejp_2084_:
{
return v___x_2085_;
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
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDeleteFile_toJson_spec__0(lean_object* v_k_2090_, lean_object* v_x_2091_){
_start:
{
if (lean_obj_tag(v_x_2091_) == 0)
{
lean_object* v___x_2092_; 
lean_dec_ref(v_k_2090_);
v___x_2092_ = lean_box(0);
return v___x_2092_;
}
else
{
lean_object* v_val_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; 
v_val_2093_ = lean_ctor_get(v_x_2091_, 0);
v___x_2094_ = l_Lean_Lsp_DeleteFile_instToJsonOptions_toJson(v_val_2093_);
v___x_2095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2095_, 0, v_k_2090_);
lean_ctor_set(v___x_2095_, 1, v___x_2094_);
v___x_2096_ = lean_box(0);
v___x_2097_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2097_, 0, v___x_2095_);
lean_ctor_set(v___x_2097_, 1, v___x_2096_);
return v___x_2097_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDeleteFile_toJson_spec__0___boxed(lean_object* v_k_2098_, lean_object* v_x_2099_){
_start:
{
lean_object* v_res_2100_; 
v_res_2100_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDeleteFile_toJson_spec__0(v_k_2098_, v_x_2099_);
lean_dec(v_x_2099_);
return v_res_2100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDeleteFile_toJson(lean_object* v_x_2101_){
_start:
{
lean_object* v_uri_2102_; lean_object* v_options_x3f_2103_; lean_object* v_annotationId_x3f_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; 
v_uri_2102_ = lean_ctor_get(v_x_2101_, 0);
lean_inc_ref(v_uri_2102_);
v_options_x3f_2103_ = lean_ctor_get(v_x_2101_, 1);
lean_inc(v_options_x3f_2103_);
v_annotationId_x3f_2104_ = lean_ctor_get(v_x_2101_, 2);
lean_inc(v_annotationId_x3f_2104_);
lean_dec_ref(v_x_2101_);
v___x_2105_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__0));
v___x_2106_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2106_, 0, v_uri_2102_);
v___x_2107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2107_, 0, v___x_2105_);
lean_ctor_set(v___x_2107_, 1, v___x_2106_);
v___x_2108_ = lean_box(0);
v___x_2109_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2109_, 0, v___x_2107_);
lean_ctor_set(v___x_2109_, 1, v___x_2108_);
v___x_2110_ = ((lean_object*)(l_Lean_Lsp_instToJsonCreateFile_toJson___closed__0));
v___x_2111_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDeleteFile_toJson_spec__0(v___x_2110_, v_options_x3f_2103_);
lean_dec(v_options_x3f_2103_);
v___x_2112_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextEdit_toJson___closed__2));
v___x_2113_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextEdit_toJson_spec__1(v___x_2112_, v_annotationId_x3f_2104_);
v___x_2114_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2114_, 0, v___x_2113_);
lean_ctor_set(v___x_2114_, 1, v___x_2108_);
v___x_2115_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2115_, 0, v___x_2111_);
lean_ctor_set(v___x_2115_, 1, v___x_2114_);
v___x_2116_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2116_, 0, v___x_2109_);
lean_ctor_set(v___x_2116_, 1, v___x_2115_);
v___x_2117_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__2));
v___x_2118_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLocation_toJson_spec__0(v___x_2116_, v___x_2117_);
v___x_2119_ = l_Lean_Json_mkObj(v___x_2118_);
return v___x_2119_;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDeleteFile_fromJson_spec__0_spec__0(lean_object* v_x_2124_){
_start:
{
if (lean_obj_tag(v_x_2124_) == 0)
{
lean_object* v___x_2125_; 
v___x_2125_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDeleteFile_fromJson_spec__0_spec__0___closed__0));
return v___x_2125_;
}
else
{
lean_object* v___x_2126_; 
v___x_2126_ = l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson(v_x_2124_);
if (lean_obj_tag(v___x_2126_) == 0)
{
lean_object* v_a_2127_; lean_object* v___x_2129_; uint8_t v_isShared_2130_; uint8_t v_isSharedCheck_2134_; 
v_a_2127_ = lean_ctor_get(v___x_2126_, 0);
v_isSharedCheck_2134_ = !lean_is_exclusive(v___x_2126_);
if (v_isSharedCheck_2134_ == 0)
{
v___x_2129_ = v___x_2126_;
v_isShared_2130_ = v_isSharedCheck_2134_;
goto v_resetjp_2128_;
}
else
{
lean_inc(v_a_2127_);
lean_dec(v___x_2126_);
v___x_2129_ = lean_box(0);
v_isShared_2130_ = v_isSharedCheck_2134_;
goto v_resetjp_2128_;
}
v_resetjp_2128_:
{
lean_object* v___x_2132_; 
if (v_isShared_2130_ == 0)
{
v___x_2132_ = v___x_2129_;
goto v_reusejp_2131_;
}
else
{
lean_object* v_reuseFailAlloc_2133_; 
v_reuseFailAlloc_2133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2133_, 0, v_a_2127_);
v___x_2132_ = v_reuseFailAlloc_2133_;
goto v_reusejp_2131_;
}
v_reusejp_2131_:
{
return v___x_2132_;
}
}
}
else
{
lean_object* v_a_2135_; lean_object* v___x_2137_; uint8_t v_isShared_2138_; uint8_t v_isSharedCheck_2143_; 
v_a_2135_ = lean_ctor_get(v___x_2126_, 0);
v_isSharedCheck_2143_ = !lean_is_exclusive(v___x_2126_);
if (v_isSharedCheck_2143_ == 0)
{
v___x_2137_ = v___x_2126_;
v_isShared_2138_ = v_isSharedCheck_2143_;
goto v_resetjp_2136_;
}
else
{
lean_inc(v_a_2135_);
lean_dec(v___x_2126_);
v___x_2137_ = lean_box(0);
v_isShared_2138_ = v_isSharedCheck_2143_;
goto v_resetjp_2136_;
}
v_resetjp_2136_:
{
lean_object* v___x_2139_; lean_object* v___x_2141_; 
v___x_2139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2139_, 0, v_a_2135_);
if (v_isShared_2138_ == 0)
{
lean_ctor_set(v___x_2137_, 0, v___x_2139_);
v___x_2141_ = v___x_2137_;
goto v_reusejp_2140_;
}
else
{
lean_object* v_reuseFailAlloc_2142_; 
v_reuseFailAlloc_2142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2142_, 0, v___x_2139_);
v___x_2141_ = v_reuseFailAlloc_2142_;
goto v_reusejp_2140_;
}
v_reusejp_2140_:
{
return v___x_2141_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDeleteFile_fromJson_spec__0(lean_object* v_j_2144_, lean_object* v_k_2145_){
_start:
{
lean_object* v___x_2146_; lean_object* v___x_2147_; 
v___x_2146_ = l_Lean_Json_getObjValD(v_j_2144_, v_k_2145_);
v___x_2147_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDeleteFile_fromJson_spec__0_spec__0(v___x_2146_);
return v___x_2147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDeleteFile_fromJson_spec__0___boxed(lean_object* v_j_2148_, lean_object* v_k_2149_){
_start:
{
lean_object* v_res_2150_; 
v_res_2150_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDeleteFile_fromJson_spec__0(v_j_2148_, v_k_2149_);
lean_dec_ref(v_k_2149_);
return v_res_2150_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__1(void){
_start:
{
uint8_t v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; 
v___x_2155_ = 1;
v___x_2156_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__0));
v___x_2157_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2156_, v___x_2155_);
return v___x_2157_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__2(void){
_start:
{
lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; 
v___x_2158_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__5));
v___x_2159_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__1, &l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__1_once, _init_l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__1);
v___x_2160_ = lean_string_append(v___x_2159_, v___x_2158_);
return v___x_2160_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__3(void){
_start:
{
lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; 
v___x_2161_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLocation_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLocation_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLocation_fromJson___closed__8);
v___x_2162_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__2, &l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__2);
v___x_2163_ = lean_string_append(v___x_2162_, v___x_2161_);
return v___x_2163_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__4(void){
_start:
{
lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; 
v___x_2164_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_2165_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__3, &l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__3);
v___x_2166_ = lean_string_append(v___x_2165_, v___x_2164_);
return v___x_2166_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__5(void){
_start:
{
lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; 
v___x_2167_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__7, &l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__7);
v___x_2168_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__2, &l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__2);
v___x_2169_ = lean_string_append(v___x_2168_, v___x_2167_);
return v___x_2169_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__6(void){
_start:
{
lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; 
v___x_2170_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_2171_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__5, &l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__5);
v___x_2172_ = lean_string_append(v___x_2171_, v___x_2170_);
return v___x_2172_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__7(void){
_start:
{
lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; 
v___x_2173_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__17, &l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__17_once, _init_l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__17);
v___x_2174_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__2, &l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__2);
v___x_2175_ = lean_string_append(v___x_2174_, v___x_2173_);
return v___x_2175_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__8(void){
_start:
{
lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; 
v___x_2176_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_2177_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__7, &l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__7);
v___x_2178_ = lean_string_append(v___x_2177_, v___x_2176_);
return v___x_2178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDeleteFile_fromJson(lean_object* v_json_2179_){
_start:
{
lean_object* v___x_2180_; lean_object* v___x_2181_; 
v___x_2180_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__0));
lean_inc(v_json_2179_);
v___x_2181_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocation_fromJson_spec__0(v_json_2179_, v___x_2180_);
if (lean_obj_tag(v___x_2181_) == 0)
{
lean_object* v_a_2182_; lean_object* v___x_2184_; uint8_t v_isShared_2185_; uint8_t v_isSharedCheck_2191_; 
lean_dec(v_json_2179_);
v_a_2182_ = lean_ctor_get(v___x_2181_, 0);
v_isSharedCheck_2191_ = !lean_is_exclusive(v___x_2181_);
if (v_isSharedCheck_2191_ == 0)
{
v___x_2184_ = v___x_2181_;
v_isShared_2185_ = v_isSharedCheck_2191_;
goto v_resetjp_2183_;
}
else
{
lean_inc(v_a_2182_);
lean_dec(v___x_2181_);
v___x_2184_ = lean_box(0);
v_isShared_2185_ = v_isSharedCheck_2191_;
goto v_resetjp_2183_;
}
v_resetjp_2183_:
{
lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2189_; 
v___x_2186_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__4, &l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__4);
v___x_2187_ = lean_string_append(v___x_2186_, v_a_2182_);
lean_dec(v_a_2182_);
if (v_isShared_2185_ == 0)
{
lean_ctor_set(v___x_2184_, 0, v___x_2187_);
v___x_2189_ = v___x_2184_;
goto v_reusejp_2188_;
}
else
{
lean_object* v_reuseFailAlloc_2190_; 
v_reuseFailAlloc_2190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2190_, 0, v___x_2187_);
v___x_2189_ = v_reuseFailAlloc_2190_;
goto v_reusejp_2188_;
}
v_reusejp_2188_:
{
return v___x_2189_;
}
}
}
else
{
if (lean_obj_tag(v___x_2181_) == 0)
{
lean_object* v_a_2192_; lean_object* v___x_2194_; uint8_t v_isShared_2195_; uint8_t v_isSharedCheck_2199_; 
lean_dec(v_json_2179_);
v_a_2192_ = lean_ctor_get(v___x_2181_, 0);
v_isSharedCheck_2199_ = !lean_is_exclusive(v___x_2181_);
if (v_isSharedCheck_2199_ == 0)
{
v___x_2194_ = v___x_2181_;
v_isShared_2195_ = v_isSharedCheck_2199_;
goto v_resetjp_2193_;
}
else
{
lean_inc(v_a_2192_);
lean_dec(v___x_2181_);
v___x_2194_ = lean_box(0);
v_isShared_2195_ = v_isSharedCheck_2199_;
goto v_resetjp_2193_;
}
v_resetjp_2193_:
{
lean_object* v___x_2197_; 
if (v_isShared_2195_ == 0)
{
lean_ctor_set_tag(v___x_2194_, 0);
v___x_2197_ = v___x_2194_;
goto v_reusejp_2196_;
}
else
{
lean_object* v_reuseFailAlloc_2198_; 
v_reuseFailAlloc_2198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2198_, 0, v_a_2192_);
v___x_2197_ = v_reuseFailAlloc_2198_;
goto v_reusejp_2196_;
}
v_reusejp_2196_:
{
return v___x_2197_;
}
}
}
else
{
lean_object* v_a_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; 
v_a_2200_ = lean_ctor_get(v___x_2181_, 0);
lean_inc(v_a_2200_);
lean_dec_ref(v___x_2181_);
v___x_2201_ = ((lean_object*)(l_Lean_Lsp_instToJsonCreateFile_toJson___closed__0));
lean_inc(v_json_2179_);
v___x_2202_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDeleteFile_fromJson_spec__0(v_json_2179_, v___x_2201_);
if (lean_obj_tag(v___x_2202_) == 0)
{
lean_object* v_a_2203_; lean_object* v___x_2205_; uint8_t v_isShared_2206_; uint8_t v_isSharedCheck_2212_; 
lean_dec(v_a_2200_);
lean_dec(v_json_2179_);
v_a_2203_ = lean_ctor_get(v___x_2202_, 0);
v_isSharedCheck_2212_ = !lean_is_exclusive(v___x_2202_);
if (v_isSharedCheck_2212_ == 0)
{
v___x_2205_ = v___x_2202_;
v_isShared_2206_ = v_isSharedCheck_2212_;
goto v_resetjp_2204_;
}
else
{
lean_inc(v_a_2203_);
lean_dec(v___x_2202_);
v___x_2205_ = lean_box(0);
v_isShared_2206_ = v_isSharedCheck_2212_;
goto v_resetjp_2204_;
}
v_resetjp_2204_:
{
lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2210_; 
v___x_2207_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__6, &l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__6);
v___x_2208_ = lean_string_append(v___x_2207_, v_a_2203_);
lean_dec(v_a_2203_);
if (v_isShared_2206_ == 0)
{
lean_ctor_set(v___x_2205_, 0, v___x_2208_);
v___x_2210_ = v___x_2205_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v___x_2208_);
v___x_2210_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
return v___x_2210_;
}
}
}
else
{
if (lean_obj_tag(v___x_2202_) == 0)
{
lean_object* v_a_2213_; lean_object* v___x_2215_; uint8_t v_isShared_2216_; uint8_t v_isSharedCheck_2220_; 
lean_dec(v_a_2200_);
lean_dec(v_json_2179_);
v_a_2213_ = lean_ctor_get(v___x_2202_, 0);
v_isSharedCheck_2220_ = !lean_is_exclusive(v___x_2202_);
if (v_isSharedCheck_2220_ == 0)
{
v___x_2215_ = v___x_2202_;
v_isShared_2216_ = v_isSharedCheck_2220_;
goto v_resetjp_2214_;
}
else
{
lean_inc(v_a_2213_);
lean_dec(v___x_2202_);
v___x_2215_ = lean_box(0);
v_isShared_2216_ = v_isSharedCheck_2220_;
goto v_resetjp_2214_;
}
v_resetjp_2214_:
{
lean_object* v___x_2218_; 
if (v_isShared_2216_ == 0)
{
lean_ctor_set_tag(v___x_2215_, 0);
v___x_2218_ = v___x_2215_;
goto v_reusejp_2217_;
}
else
{
lean_object* v_reuseFailAlloc_2219_; 
v_reuseFailAlloc_2219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2219_, 0, v_a_2213_);
v___x_2218_ = v_reuseFailAlloc_2219_;
goto v_reusejp_2217_;
}
v_reusejp_2217_:
{
return v___x_2218_;
}
}
}
else
{
lean_object* v_a_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; 
v_a_2221_ = lean_ctor_get(v___x_2202_, 0);
lean_inc(v_a_2221_);
lean_dec_ref(v___x_2202_);
v___x_2222_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextEdit_toJson___closed__2));
v___x_2223_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextEdit_fromJson_spec__1(v_json_2179_, v___x_2222_);
if (lean_obj_tag(v___x_2223_) == 0)
{
lean_object* v_a_2224_; lean_object* v___x_2226_; uint8_t v_isShared_2227_; uint8_t v_isSharedCheck_2233_; 
lean_dec(v_a_2221_);
lean_dec(v_a_2200_);
v_a_2224_ = lean_ctor_get(v___x_2223_, 0);
v_isSharedCheck_2233_ = !lean_is_exclusive(v___x_2223_);
if (v_isSharedCheck_2233_ == 0)
{
v___x_2226_ = v___x_2223_;
v_isShared_2227_ = v_isSharedCheck_2233_;
goto v_resetjp_2225_;
}
else
{
lean_inc(v_a_2224_);
lean_dec(v___x_2223_);
v___x_2226_ = lean_box(0);
v_isShared_2227_ = v_isSharedCheck_2233_;
goto v_resetjp_2225_;
}
v_resetjp_2225_:
{
lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2231_; 
v___x_2228_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__8, &l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__8);
v___x_2229_ = lean_string_append(v___x_2228_, v_a_2224_);
lean_dec(v_a_2224_);
if (v_isShared_2227_ == 0)
{
lean_ctor_set(v___x_2226_, 0, v___x_2229_);
v___x_2231_ = v___x_2226_;
goto v_reusejp_2230_;
}
else
{
lean_object* v_reuseFailAlloc_2232_; 
v_reuseFailAlloc_2232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2232_, 0, v___x_2229_);
v___x_2231_ = v_reuseFailAlloc_2232_;
goto v_reusejp_2230_;
}
v_reusejp_2230_:
{
return v___x_2231_;
}
}
}
else
{
if (lean_obj_tag(v___x_2223_) == 0)
{
lean_object* v_a_2234_; lean_object* v___x_2236_; uint8_t v_isShared_2237_; uint8_t v_isSharedCheck_2241_; 
lean_dec(v_a_2221_);
lean_dec(v_a_2200_);
v_a_2234_ = lean_ctor_get(v___x_2223_, 0);
v_isSharedCheck_2241_ = !lean_is_exclusive(v___x_2223_);
if (v_isSharedCheck_2241_ == 0)
{
v___x_2236_ = v___x_2223_;
v_isShared_2237_ = v_isSharedCheck_2241_;
goto v_resetjp_2235_;
}
else
{
lean_inc(v_a_2234_);
lean_dec(v___x_2223_);
v___x_2236_ = lean_box(0);
v_isShared_2237_ = v_isSharedCheck_2241_;
goto v_resetjp_2235_;
}
v_resetjp_2235_:
{
lean_object* v___x_2239_; 
if (v_isShared_2237_ == 0)
{
lean_ctor_set_tag(v___x_2236_, 0);
v___x_2239_ = v___x_2236_;
goto v_reusejp_2238_;
}
else
{
lean_object* v_reuseFailAlloc_2240_; 
v_reuseFailAlloc_2240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2240_, 0, v_a_2234_);
v___x_2239_ = v_reuseFailAlloc_2240_;
goto v_reusejp_2238_;
}
v_reusejp_2238_:
{
return v___x_2239_;
}
}
}
else
{
lean_object* v_a_2242_; lean_object* v___x_2244_; uint8_t v_isShared_2245_; uint8_t v_isSharedCheck_2250_; 
v_a_2242_ = lean_ctor_get(v___x_2223_, 0);
v_isSharedCheck_2250_ = !lean_is_exclusive(v___x_2223_);
if (v_isSharedCheck_2250_ == 0)
{
v___x_2244_ = v___x_2223_;
v_isShared_2245_ = v_isSharedCheck_2250_;
goto v_resetjp_2243_;
}
else
{
lean_inc(v_a_2242_);
lean_dec(v___x_2223_);
v___x_2244_ = lean_box(0);
v_isShared_2245_ = v_isSharedCheck_2250_;
goto v_resetjp_2243_;
}
v_resetjp_2243_:
{
lean_object* v___x_2246_; lean_object* v___x_2248_; 
v___x_2246_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2246_, 0, v_a_2200_);
lean_ctor_set(v___x_2246_, 1, v_a_2221_);
lean_ctor_set(v___x_2246_, 2, v_a_2242_);
if (v_isShared_2245_ == 0)
{
lean_ctor_set(v___x_2244_, 0, v___x_2246_);
v___x_2248_ = v___x_2244_;
goto v_reusejp_2247_;
}
else
{
lean_object* v_reuseFailAlloc_2249_; 
v_reuseFailAlloc_2249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2249_, 0, v___x_2246_);
v___x_2248_ = v_reuseFailAlloc_2249_;
goto v_reusejp_2247_;
}
v_reusejp_2247_:
{
return v___x_2248_;
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
LEAN_EXPORT lean_object* l_Lean_Lsp_DocumentChange_ctorIdx(lean_object* v_x_2253_){
_start:
{
switch(lean_obj_tag(v_x_2253_))
{
case 0:
{
lean_object* v___x_2254_; 
v___x_2254_ = lean_unsigned_to_nat(0u);
return v___x_2254_;
}
case 1:
{
lean_object* v___x_2255_; 
v___x_2255_ = lean_unsigned_to_nat(1u);
return v___x_2255_;
}
case 2:
{
lean_object* v___x_2256_; 
v___x_2256_ = lean_unsigned_to_nat(2u);
return v___x_2256_;
}
default: 
{
lean_object* v___x_2257_; 
v___x_2257_ = lean_unsigned_to_nat(3u);
return v___x_2257_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DocumentChange_ctorIdx___boxed(lean_object* v_x_2258_){
_start:
{
lean_object* v_res_2259_; 
v_res_2259_ = l_Lean_Lsp_DocumentChange_ctorIdx(v_x_2258_);
lean_dec_ref(v_x_2258_);
return v_res_2259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DocumentChange_ctorElim___redArg(lean_object* v_t_2260_, lean_object* v_k_2261_){
_start:
{
lean_object* v_a_2262_; lean_object* v___x_2263_; 
v_a_2262_ = lean_ctor_get(v_t_2260_, 0);
lean_inc_ref(v_a_2262_);
lean_dec_ref(v_t_2260_);
v___x_2263_ = lean_apply_1(v_k_2261_, v_a_2262_);
return v___x_2263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DocumentChange_ctorElim(lean_object* v_motive_2264_, lean_object* v_ctorIdx_2265_, lean_object* v_t_2266_, lean_object* v_h_2267_, lean_object* v_k_2268_){
_start:
{
lean_object* v___x_2269_; 
v___x_2269_ = l_Lean_Lsp_DocumentChange_ctorElim___redArg(v_t_2266_, v_k_2268_);
return v___x_2269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DocumentChange_ctorElim___boxed(lean_object* v_motive_2270_, lean_object* v_ctorIdx_2271_, lean_object* v_t_2272_, lean_object* v_h_2273_, lean_object* v_k_2274_){
_start:
{
lean_object* v_res_2275_; 
v_res_2275_ = l_Lean_Lsp_DocumentChange_ctorElim(v_motive_2270_, v_ctorIdx_2271_, v_t_2272_, v_h_2273_, v_k_2274_);
lean_dec(v_ctorIdx_2271_);
return v_res_2275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DocumentChange_create_elim___redArg(lean_object* v_t_2276_, lean_object* v_create_2277_){
_start:
{
lean_object* v___x_2278_; 
v___x_2278_ = l_Lean_Lsp_DocumentChange_ctorElim___redArg(v_t_2276_, v_create_2277_);
return v___x_2278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DocumentChange_create_elim(lean_object* v_motive_2279_, lean_object* v_t_2280_, lean_object* v_h_2281_, lean_object* v_create_2282_){
_start:
{
lean_object* v___x_2283_; 
v___x_2283_ = l_Lean_Lsp_DocumentChange_ctorElim___redArg(v_t_2280_, v_create_2282_);
return v___x_2283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DocumentChange_rename_elim___redArg(lean_object* v_t_2284_, lean_object* v_rename_2285_){
_start:
{
lean_object* v___x_2286_; 
v___x_2286_ = l_Lean_Lsp_DocumentChange_ctorElim___redArg(v_t_2284_, v_rename_2285_);
return v___x_2286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DocumentChange_rename_elim(lean_object* v_motive_2287_, lean_object* v_t_2288_, lean_object* v_h_2289_, lean_object* v_rename_2290_){
_start:
{
lean_object* v___x_2291_; 
v___x_2291_ = l_Lean_Lsp_DocumentChange_ctorElim___redArg(v_t_2288_, v_rename_2290_);
return v___x_2291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DocumentChange_delete_elim___redArg(lean_object* v_t_2292_, lean_object* v_delete_2293_){
_start:
{
lean_object* v___x_2294_; 
v___x_2294_ = l_Lean_Lsp_DocumentChange_ctorElim___redArg(v_t_2292_, v_delete_2293_);
return v___x_2294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DocumentChange_delete_elim(lean_object* v_motive_2295_, lean_object* v_t_2296_, lean_object* v_h_2297_, lean_object* v_delete_2298_){
_start:
{
lean_object* v___x_2299_; 
v___x_2299_ = l_Lean_Lsp_DocumentChange_ctorElim___redArg(v_t_2296_, v_delete_2298_);
return v___x_2299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DocumentChange_edit_elim___redArg(lean_object* v_t_2300_, lean_object* v_edit_2301_){
_start:
{
lean_object* v___x_2302_; 
v___x_2302_ = l_Lean_Lsp_DocumentChange_ctorElim___redArg(v_t_2300_, v_edit_2301_);
return v___x_2302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DocumentChange_edit_elim(lean_object* v_motive_2303_, lean_object* v_t_2304_, lean_object* v_h_2305_, lean_object* v_edit_2306_){
_start:
{
lean_object* v___x_2307_; 
v___x_2307_ = l_Lean_Lsp_DocumentChange_ctorElim___redArg(v_t_2304_, v_edit_2306_);
return v___x_2307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDocumentChange___lam__0(lean_object* v_x_2318_){
_start:
{
switch(lean_obj_tag(v_x_2318_))
{
case 0:
{
lean_object* v_a_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; 
v_a_2319_ = lean_ctor_get(v_x_2318_, 0);
lean_inc_ref(v_a_2319_);
lean_dec_ref(v_x_2318_);
v___x_2320_ = l_Lean_Lsp_instToJsonCreateFile_toJson(v_a_2319_);
v___x_2321_ = ((lean_object*)(l_Lean_Lsp_instToJsonDocumentChange___lam__0___closed__0));
v___x_2322_ = ((lean_object*)(l_Lean_Lsp_instToJsonDocumentChange___lam__0___closed__2));
v___x_2323_ = l_Lean_Json_setObjVal_x21(v___x_2320_, v___x_2321_, v___x_2322_);
return v___x_2323_;
}
case 1:
{
lean_object* v_a_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; 
v_a_2324_ = lean_ctor_get(v_x_2318_, 0);
lean_inc_ref(v_a_2324_);
lean_dec_ref(v_x_2318_);
v___x_2325_ = l_Lean_Lsp_instToJsonRenameFile_toJson(v_a_2324_);
v___x_2326_ = ((lean_object*)(l_Lean_Lsp_instToJsonDocumentChange___lam__0___closed__0));
v___x_2327_ = ((lean_object*)(l_Lean_Lsp_instToJsonDocumentChange___lam__0___closed__4));
v___x_2328_ = l_Lean_Json_setObjVal_x21(v___x_2325_, v___x_2326_, v___x_2327_);
return v___x_2328_;
}
case 2:
{
lean_object* v_a_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; 
v_a_2329_ = lean_ctor_get(v_x_2318_, 0);
lean_inc_ref(v_a_2329_);
lean_dec_ref(v_x_2318_);
v___x_2330_ = l_Lean_Lsp_instToJsonDeleteFile_toJson(v_a_2329_);
v___x_2331_ = ((lean_object*)(l_Lean_Lsp_instToJsonDocumentChange___lam__0___closed__0));
v___x_2332_ = ((lean_object*)(l_Lean_Lsp_instToJsonDocumentChange___lam__0___closed__6));
v___x_2333_ = l_Lean_Json_setObjVal_x21(v___x_2330_, v___x_2331_, v___x_2332_);
return v___x_2333_;
}
default: 
{
lean_object* v_a_2334_; lean_object* v___x_2335_; 
v_a_2334_ = lean_ctor_get(v_x_2318_, 0);
lean_inc_ref(v_a_2334_);
lean_dec_ref(v_x_2318_);
v___x_2335_ = l_Lean_Lsp_instToJsonTextDocumentEdit_toJson(v_a_2334_);
return v___x_2335_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDocumentChange___lam__0(lean_object* v_kind_2339_){
_start:
{
lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; 
v___x_2340_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDocumentChange___lam__0___closed__0));
v___x_2341_ = lean_unsigned_to_nat(80u);
v___x_2342_ = l_Lean_Json_pretty(v_kind_2339_, v___x_2341_);
v___x_2343_ = lean_string_append(v___x_2340_, v___x_2342_);
lean_dec_ref(v___x_2342_);
v___x_2344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2344_, 0, v___x_2343_);
return v___x_2344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDocumentChange___lam__1(lean_object* v___f_2345_, lean_object* v_j_2346_){
_start:
{
lean_object* v___y_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; 
v___x_2368_ = ((lean_object*)(l_Lean_Lsp_instToJsonDocumentChange___lam__0___closed__0));
lean_inc(v_j_2346_);
v___x_2369_ = l_Lean_Json_getObjVal_x3f(v_j_2346_, v___x_2368_);
if (lean_obj_tag(v___x_2369_) == 0)
{
lean_dec_ref(v___x_2369_);
lean_dec_ref(v___f_2345_);
goto v___jp_2347_;
}
else
{
lean_object* v_a_2370_; 
v_a_2370_ = lean_ctor_get(v___x_2369_, 0);
lean_inc(v_a_2370_);
lean_dec_ref(v___x_2369_);
if (lean_obj_tag(v_a_2370_) == 3)
{
lean_object* v_s_2371_; lean_object* v___x_2372_; uint8_t v___x_2373_; 
v_s_2371_ = lean_ctor_get(v_a_2370_, 0);
v___x_2372_ = ((lean_object*)(l_Lean_Lsp_instToJsonDocumentChange___lam__0___closed__1));
v___x_2373_ = lean_string_dec_eq(v_s_2371_, v___x_2372_);
if (v___x_2373_ == 0)
{
lean_object* v___x_2374_; uint8_t v___x_2375_; 
v___x_2374_ = ((lean_object*)(l_Lean_Lsp_instToJsonDocumentChange___lam__0___closed__3));
v___x_2375_ = lean_string_dec_eq(v_s_2371_, v___x_2374_);
if (v___x_2375_ == 0)
{
lean_object* v___x_2376_; uint8_t v___x_2377_; 
v___x_2376_ = ((lean_object*)(l_Lean_Lsp_instToJsonDocumentChange___lam__0___closed__5));
v___x_2377_ = lean_string_dec_eq(v_s_2371_, v___x_2376_);
if (v___x_2377_ == 0)
{
lean_object* v___x_2378_; 
v___x_2378_ = lean_apply_1(v___f_2345_, v_a_2370_);
v___y_2367_ = v___x_2378_;
goto v___jp_2366_;
}
else
{
lean_object* v___x_2380_; uint8_t v_isShared_2381_; uint8_t v_isSharedCheck_2394_; 
lean_dec_ref(v___f_2345_);
v_isSharedCheck_2394_ = !lean_is_exclusive(v_a_2370_);
if (v_isSharedCheck_2394_ == 0)
{
lean_object* v_unused_2395_; 
v_unused_2395_ = lean_ctor_get(v_a_2370_, 0);
lean_dec(v_unused_2395_);
v___x_2380_ = v_a_2370_;
v_isShared_2381_ = v_isSharedCheck_2394_;
goto v_resetjp_2379_;
}
else
{
lean_dec(v_a_2370_);
v___x_2380_ = lean_box(0);
v_isShared_2381_ = v_isSharedCheck_2394_;
goto v_resetjp_2379_;
}
v_resetjp_2379_:
{
lean_object* v___x_2382_; 
lean_inc(v_j_2346_);
v___x_2382_ = l_Lean_Lsp_instFromJsonDeleteFile_fromJson(v_j_2346_);
if (lean_obj_tag(v___x_2382_) == 0)
{
lean_dec_ref(v___x_2382_);
lean_del_object(v___x_2380_);
goto v___jp_2347_;
}
else
{
lean_object* v_a_2383_; lean_object* v___x_2385_; uint8_t v_isShared_2386_; uint8_t v_isSharedCheck_2393_; 
lean_dec(v_j_2346_);
v_a_2383_ = lean_ctor_get(v___x_2382_, 0);
v_isSharedCheck_2393_ = !lean_is_exclusive(v___x_2382_);
if (v_isSharedCheck_2393_ == 0)
{
v___x_2385_ = v___x_2382_;
v_isShared_2386_ = v_isSharedCheck_2393_;
goto v_resetjp_2384_;
}
else
{
lean_inc(v_a_2383_);
lean_dec(v___x_2382_);
v___x_2385_ = lean_box(0);
v_isShared_2386_ = v_isSharedCheck_2393_;
goto v_resetjp_2384_;
}
v_resetjp_2384_:
{
lean_object* v___x_2388_; 
if (v_isShared_2381_ == 0)
{
lean_ctor_set_tag(v___x_2380_, 2);
lean_ctor_set(v___x_2380_, 0, v_a_2383_);
v___x_2388_ = v___x_2380_;
goto v_reusejp_2387_;
}
else
{
lean_object* v_reuseFailAlloc_2392_; 
v_reuseFailAlloc_2392_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2392_, 0, v_a_2383_);
v___x_2388_ = v_reuseFailAlloc_2392_;
goto v_reusejp_2387_;
}
v_reusejp_2387_:
{
lean_object* v___x_2390_; 
if (v_isShared_2386_ == 0)
{
lean_ctor_set(v___x_2385_, 0, v___x_2388_);
v___x_2390_ = v___x_2385_;
goto v_reusejp_2389_;
}
else
{
lean_object* v_reuseFailAlloc_2391_; 
v_reuseFailAlloc_2391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2391_, 0, v___x_2388_);
v___x_2390_ = v_reuseFailAlloc_2391_;
goto v_reusejp_2389_;
}
v_reusejp_2389_:
{
return v___x_2390_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2397_; uint8_t v_isShared_2398_; uint8_t v_isSharedCheck_2411_; 
lean_dec_ref(v___f_2345_);
v_isSharedCheck_2411_ = !lean_is_exclusive(v_a_2370_);
if (v_isSharedCheck_2411_ == 0)
{
lean_object* v_unused_2412_; 
v_unused_2412_ = lean_ctor_get(v_a_2370_, 0);
lean_dec(v_unused_2412_);
v___x_2397_ = v_a_2370_;
v_isShared_2398_ = v_isSharedCheck_2411_;
goto v_resetjp_2396_;
}
else
{
lean_dec(v_a_2370_);
v___x_2397_ = lean_box(0);
v_isShared_2398_ = v_isSharedCheck_2411_;
goto v_resetjp_2396_;
}
v_resetjp_2396_:
{
lean_object* v___x_2399_; 
lean_inc(v_j_2346_);
v___x_2399_ = l_Lean_Lsp_instFromJsonRenameFile_fromJson(v_j_2346_);
if (lean_obj_tag(v___x_2399_) == 0)
{
lean_dec_ref(v___x_2399_);
lean_del_object(v___x_2397_);
goto v___jp_2347_;
}
else
{
lean_object* v_a_2400_; lean_object* v___x_2402_; uint8_t v_isShared_2403_; uint8_t v_isSharedCheck_2410_; 
lean_dec(v_j_2346_);
v_a_2400_ = lean_ctor_get(v___x_2399_, 0);
v_isSharedCheck_2410_ = !lean_is_exclusive(v___x_2399_);
if (v_isSharedCheck_2410_ == 0)
{
v___x_2402_ = v___x_2399_;
v_isShared_2403_ = v_isSharedCheck_2410_;
goto v_resetjp_2401_;
}
else
{
lean_inc(v_a_2400_);
lean_dec(v___x_2399_);
v___x_2402_ = lean_box(0);
v_isShared_2403_ = v_isSharedCheck_2410_;
goto v_resetjp_2401_;
}
v_resetjp_2401_:
{
lean_object* v___x_2405_; 
if (v_isShared_2398_ == 0)
{
lean_ctor_set_tag(v___x_2397_, 1);
lean_ctor_set(v___x_2397_, 0, v_a_2400_);
v___x_2405_ = v___x_2397_;
goto v_reusejp_2404_;
}
else
{
lean_object* v_reuseFailAlloc_2409_; 
v_reuseFailAlloc_2409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2409_, 0, v_a_2400_);
v___x_2405_ = v_reuseFailAlloc_2409_;
goto v_reusejp_2404_;
}
v_reusejp_2404_:
{
lean_object* v___x_2407_; 
if (v_isShared_2403_ == 0)
{
lean_ctor_set(v___x_2402_, 0, v___x_2405_);
v___x_2407_ = v___x_2402_;
goto v_reusejp_2406_;
}
else
{
lean_object* v_reuseFailAlloc_2408_; 
v_reuseFailAlloc_2408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2408_, 0, v___x_2405_);
v___x_2407_ = v_reuseFailAlloc_2408_;
goto v_reusejp_2406_;
}
v_reusejp_2406_:
{
return v___x_2407_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2414_; uint8_t v_isShared_2415_; uint8_t v_isSharedCheck_2428_; 
lean_dec_ref(v___f_2345_);
v_isSharedCheck_2428_ = !lean_is_exclusive(v_a_2370_);
if (v_isSharedCheck_2428_ == 0)
{
lean_object* v_unused_2429_; 
v_unused_2429_ = lean_ctor_get(v_a_2370_, 0);
lean_dec(v_unused_2429_);
v___x_2414_ = v_a_2370_;
v_isShared_2415_ = v_isSharedCheck_2428_;
goto v_resetjp_2413_;
}
else
{
lean_dec(v_a_2370_);
v___x_2414_ = lean_box(0);
v_isShared_2415_ = v_isSharedCheck_2428_;
goto v_resetjp_2413_;
}
v_resetjp_2413_:
{
lean_object* v___x_2416_; 
lean_inc(v_j_2346_);
v___x_2416_ = l_Lean_Lsp_instFromJsonCreateFile_fromJson(v_j_2346_);
if (lean_obj_tag(v___x_2416_) == 0)
{
lean_dec_ref(v___x_2416_);
lean_del_object(v___x_2414_);
goto v___jp_2347_;
}
else
{
lean_object* v_a_2417_; lean_object* v___x_2419_; uint8_t v_isShared_2420_; uint8_t v_isSharedCheck_2427_; 
lean_dec(v_j_2346_);
v_a_2417_ = lean_ctor_get(v___x_2416_, 0);
v_isSharedCheck_2427_ = !lean_is_exclusive(v___x_2416_);
if (v_isSharedCheck_2427_ == 0)
{
v___x_2419_ = v___x_2416_;
v_isShared_2420_ = v_isSharedCheck_2427_;
goto v_resetjp_2418_;
}
else
{
lean_inc(v_a_2417_);
lean_dec(v___x_2416_);
v___x_2419_ = lean_box(0);
v_isShared_2420_ = v_isSharedCheck_2427_;
goto v_resetjp_2418_;
}
v_resetjp_2418_:
{
lean_object* v___x_2422_; 
if (v_isShared_2415_ == 0)
{
lean_ctor_set_tag(v___x_2414_, 0);
lean_ctor_set(v___x_2414_, 0, v_a_2417_);
v___x_2422_ = v___x_2414_;
goto v_reusejp_2421_;
}
else
{
lean_object* v_reuseFailAlloc_2426_; 
v_reuseFailAlloc_2426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2426_, 0, v_a_2417_);
v___x_2422_ = v_reuseFailAlloc_2426_;
goto v_reusejp_2421_;
}
v_reusejp_2421_:
{
lean_object* v___x_2424_; 
if (v_isShared_2420_ == 0)
{
lean_ctor_set(v___x_2419_, 0, v___x_2422_);
v___x_2424_ = v___x_2419_;
goto v_reusejp_2423_;
}
else
{
lean_object* v_reuseFailAlloc_2425_; 
v_reuseFailAlloc_2425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2425_, 0, v___x_2422_);
v___x_2424_ = v_reuseFailAlloc_2425_;
goto v_reusejp_2423_;
}
v_reusejp_2423_:
{
return v___x_2424_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2430_; 
v___x_2430_ = lean_apply_1(v___f_2345_, v_a_2370_);
v___y_2367_ = v___x_2430_;
goto v___jp_2366_;
}
}
v___jp_2347_:
{
lean_object* v___x_2348_; 
v___x_2348_ = l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson(v_j_2346_);
if (lean_obj_tag(v___x_2348_) == 0)
{
lean_object* v_a_2349_; lean_object* v___x_2351_; uint8_t v_isShared_2352_; uint8_t v_isSharedCheck_2356_; 
v_a_2349_ = lean_ctor_get(v___x_2348_, 0);
v_isSharedCheck_2356_ = !lean_is_exclusive(v___x_2348_);
if (v_isSharedCheck_2356_ == 0)
{
v___x_2351_ = v___x_2348_;
v_isShared_2352_ = v_isSharedCheck_2356_;
goto v_resetjp_2350_;
}
else
{
lean_inc(v_a_2349_);
lean_dec(v___x_2348_);
v___x_2351_ = lean_box(0);
v_isShared_2352_ = v_isSharedCheck_2356_;
goto v_resetjp_2350_;
}
v_resetjp_2350_:
{
lean_object* v___x_2354_; 
if (v_isShared_2352_ == 0)
{
v___x_2354_ = v___x_2351_;
goto v_reusejp_2353_;
}
else
{
lean_object* v_reuseFailAlloc_2355_; 
v_reuseFailAlloc_2355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2355_, 0, v_a_2349_);
v___x_2354_ = v_reuseFailAlloc_2355_;
goto v_reusejp_2353_;
}
v_reusejp_2353_:
{
return v___x_2354_;
}
}
}
else
{
lean_object* v_a_2357_; lean_object* v___x_2359_; uint8_t v_isShared_2360_; uint8_t v_isSharedCheck_2365_; 
v_a_2357_ = lean_ctor_get(v___x_2348_, 0);
v_isSharedCheck_2365_ = !lean_is_exclusive(v___x_2348_);
if (v_isSharedCheck_2365_ == 0)
{
v___x_2359_ = v___x_2348_;
v_isShared_2360_ = v_isSharedCheck_2365_;
goto v_resetjp_2358_;
}
else
{
lean_inc(v_a_2357_);
lean_dec(v___x_2348_);
v___x_2359_ = lean_box(0);
v_isShared_2360_ = v_isSharedCheck_2365_;
goto v_resetjp_2358_;
}
v_resetjp_2358_:
{
lean_object* v___x_2361_; lean_object* v___x_2363_; 
v___x_2361_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2361_, 0, v_a_2357_);
if (v_isShared_2360_ == 0)
{
lean_ctor_set(v___x_2359_, 0, v___x_2361_);
v___x_2363_ = v___x_2359_;
goto v_reusejp_2362_;
}
else
{
lean_object* v_reuseFailAlloc_2364_; 
v_reuseFailAlloc_2364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2364_, 0, v___x_2361_);
v___x_2363_ = v_reuseFailAlloc_2364_;
goto v_reusejp_2362_;
}
v_reusejp_2362_:
{
return v___x_2363_;
}
}
}
}
v___jp_2366_:
{
if (lean_obj_tag(v___y_2367_) == 0)
{
lean_dec_ref(v___y_2367_);
goto v___jp_2347_;
}
else
{
lean_dec(v_j_2346_);
return v___y_2367_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_map___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEdit_toJson_spec__2_spec__4_spec__7(lean_object* v_t_2435_){
_start:
{
if (lean_obj_tag(v_t_2435_) == 0)
{
lean_object* v_size_2436_; lean_object* v_k_2437_; lean_object* v_v_2438_; lean_object* v_l_2439_; lean_object* v_r_2440_; lean_object* v___x_2442_; uint8_t v_isShared_2443_; uint8_t v_isSharedCheck_2450_; 
v_size_2436_ = lean_ctor_get(v_t_2435_, 0);
v_k_2437_ = lean_ctor_get(v_t_2435_, 1);
v_v_2438_ = lean_ctor_get(v_t_2435_, 2);
v_l_2439_ = lean_ctor_get(v_t_2435_, 3);
v_r_2440_ = lean_ctor_get(v_t_2435_, 4);
v_isSharedCheck_2450_ = !lean_is_exclusive(v_t_2435_);
if (v_isSharedCheck_2450_ == 0)
{
v___x_2442_ = v_t_2435_;
v_isShared_2443_ = v_isSharedCheck_2450_;
goto v_resetjp_2441_;
}
else
{
lean_inc(v_r_2440_);
lean_inc(v_l_2439_);
lean_inc(v_v_2438_);
lean_inc(v_k_2437_);
lean_inc(v_size_2436_);
lean_dec(v_t_2435_);
v___x_2442_ = lean_box(0);
v_isShared_2443_ = v_isSharedCheck_2450_;
goto v_resetjp_2441_;
}
v_resetjp_2441_:
{
lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2448_; 
v___x_2444_ = l_Lean_Lsp_instToJsonChangeAnnotation_toJson(v_v_2438_);
v___x_2445_ = l_Std_DTreeMap_Internal_Impl_map___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEdit_toJson_spec__2_spec__4_spec__7(v_l_2439_);
v___x_2446_ = l_Std_DTreeMap_Internal_Impl_map___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEdit_toJson_spec__2_spec__4_spec__7(v_r_2440_);
if (v_isShared_2443_ == 0)
{
lean_ctor_set(v___x_2442_, 4, v___x_2446_);
lean_ctor_set(v___x_2442_, 3, v___x_2445_);
lean_ctor_set(v___x_2442_, 2, v___x_2444_);
v___x_2448_ = v___x_2442_;
goto v_reusejp_2447_;
}
else
{
lean_object* v_reuseFailAlloc_2449_; 
v_reuseFailAlloc_2449_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2449_, 0, v_size_2436_);
lean_ctor_set(v_reuseFailAlloc_2449_, 1, v_k_2437_);
lean_ctor_set(v_reuseFailAlloc_2449_, 2, v___x_2444_);
lean_ctor_set(v_reuseFailAlloc_2449_, 3, v___x_2445_);
lean_ctor_set(v_reuseFailAlloc_2449_, 4, v___x_2446_);
v___x_2448_ = v_reuseFailAlloc_2449_;
goto v_reusejp_2447_;
}
v_reusejp_2447_:
{
return v___x_2448_;
}
}
}
else
{
lean_object* v___x_2451_; 
v___x_2451_ = lean_box(1);
return v___x_2451_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEdit_toJson_spec__2_spec__4(lean_object* v_map_2452_){
_start:
{
lean_object* v___x_2453_; lean_object* v___x_2454_; 
v___x_2453_ = l_Std_DTreeMap_Internal_Impl_map___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEdit_toJson_spec__2_spec__4_spec__7(v_map_2452_);
v___x_2454_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_2454_, 0, v___x_2453_);
return v___x_2454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEdit_toJson_spec__2(lean_object* v_k_2455_, lean_object* v_x_2456_){
_start:
{
if (lean_obj_tag(v_x_2456_) == 0)
{
lean_object* v___x_2457_; 
lean_dec_ref(v_k_2455_);
v___x_2457_ = lean_box(0);
return v___x_2457_;
}
else
{
lean_object* v_val_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; 
v_val_2458_ = lean_ctor_get(v_x_2456_, 0);
lean_inc(v_val_2458_);
lean_dec_ref(v_x_2456_);
v___x_2459_ = l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEdit_toJson_spec__2_spec__4(v_val_2458_);
v___x_2460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2460_, 0, v_k_2455_);
lean_ctor_set(v___x_2460_, 1, v___x_2459_);
v___x_2461_ = lean_box(0);
v___x_2462_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2462_, 0, v___x_2460_);
lean_ctor_set(v___x_2462_, 1, v___x_2461_);
return v___x_2462_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEdit_toJson_spec__1_spec__2_spec__4(size_t v_sz_2463_, size_t v_i_2464_, lean_object* v_bs_2465_){
_start:
{
uint8_t v___x_2466_; 
v___x_2466_ = lean_usize_dec_lt(v_i_2464_, v_sz_2463_);
if (v___x_2466_ == 0)
{
return v_bs_2465_;
}
else
{
lean_object* v_v_2467_; lean_object* v___x_2468_; lean_object* v_bs_x27_2469_; lean_object* v___y_2471_; 
v_v_2467_ = lean_array_uget(v_bs_2465_, v_i_2464_);
v___x_2468_ = lean_unsigned_to_nat(0u);
v_bs_x27_2469_ = lean_array_uset(v_bs_2465_, v_i_2464_, v___x_2468_);
switch(lean_obj_tag(v_v_2467_))
{
case 0:
{
lean_object* v_a_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; 
v_a_2476_ = lean_ctor_get(v_v_2467_, 0);
lean_inc_ref(v_a_2476_);
lean_dec_ref(v_v_2467_);
v___x_2477_ = l_Lean_Lsp_instToJsonCreateFile_toJson(v_a_2476_);
v___x_2478_ = ((lean_object*)(l_Lean_Lsp_instToJsonDocumentChange___lam__0___closed__0));
v___x_2479_ = ((lean_object*)(l_Lean_Lsp_instToJsonDocumentChange___lam__0___closed__2));
v___x_2480_ = l_Lean_Json_setObjVal_x21(v___x_2477_, v___x_2478_, v___x_2479_);
v___y_2471_ = v___x_2480_;
goto v___jp_2470_;
}
case 1:
{
lean_object* v_a_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; 
v_a_2481_ = lean_ctor_get(v_v_2467_, 0);
lean_inc_ref(v_a_2481_);
lean_dec_ref(v_v_2467_);
v___x_2482_ = l_Lean_Lsp_instToJsonRenameFile_toJson(v_a_2481_);
v___x_2483_ = ((lean_object*)(l_Lean_Lsp_instToJsonDocumentChange___lam__0___closed__0));
v___x_2484_ = ((lean_object*)(l_Lean_Lsp_instToJsonDocumentChange___lam__0___closed__4));
v___x_2485_ = l_Lean_Json_setObjVal_x21(v___x_2482_, v___x_2483_, v___x_2484_);
v___y_2471_ = v___x_2485_;
goto v___jp_2470_;
}
case 2:
{
lean_object* v_a_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; 
v_a_2486_ = lean_ctor_get(v_v_2467_, 0);
lean_inc_ref(v_a_2486_);
lean_dec_ref(v_v_2467_);
v___x_2487_ = l_Lean_Lsp_instToJsonDeleteFile_toJson(v_a_2486_);
v___x_2488_ = ((lean_object*)(l_Lean_Lsp_instToJsonDocumentChange___lam__0___closed__0));
v___x_2489_ = ((lean_object*)(l_Lean_Lsp_instToJsonDocumentChange___lam__0___closed__6));
v___x_2490_ = l_Lean_Json_setObjVal_x21(v___x_2487_, v___x_2488_, v___x_2489_);
v___y_2471_ = v___x_2490_;
goto v___jp_2470_;
}
default: 
{
lean_object* v_a_2491_; lean_object* v___x_2492_; 
v_a_2491_ = lean_ctor_get(v_v_2467_, 0);
lean_inc_ref(v_a_2491_);
lean_dec_ref(v_v_2467_);
v___x_2492_ = l_Lean_Lsp_instToJsonTextDocumentEdit_toJson(v_a_2491_);
v___y_2471_ = v___x_2492_;
goto v___jp_2470_;
}
}
v___jp_2470_:
{
size_t v___x_2472_; size_t v___x_2473_; lean_object* v___x_2474_; 
v___x_2472_ = ((size_t)1ULL);
v___x_2473_ = lean_usize_add(v_i_2464_, v___x_2472_);
v___x_2474_ = lean_array_uset(v_bs_x27_2469_, v_i_2464_, v___y_2471_);
v_i_2464_ = v___x_2473_;
v_bs_2465_ = v___x_2474_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEdit_toJson_spec__1_spec__2_spec__4___boxed(lean_object* v_sz_2493_, lean_object* v_i_2494_, lean_object* v_bs_2495_){
_start:
{
size_t v_sz_boxed_2496_; size_t v_i_boxed_2497_; lean_object* v_res_2498_; 
v_sz_boxed_2496_ = lean_unbox_usize(v_sz_2493_);
lean_dec(v_sz_2493_);
v_i_boxed_2497_ = lean_unbox_usize(v_i_2494_);
lean_dec(v_i_2494_);
v_res_2498_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEdit_toJson_spec__1_spec__2_spec__4(v_sz_boxed_2496_, v_i_boxed_2497_, v_bs_2495_);
return v_res_2498_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEdit_toJson_spec__1_spec__2(lean_object* v_a_2499_){
_start:
{
size_t v_sz_2500_; size_t v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; 
v_sz_2500_ = lean_array_size(v_a_2499_);
v___x_2501_ = ((size_t)0ULL);
v___x_2502_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEdit_toJson_spec__1_spec__2_spec__4(v_sz_2500_, v___x_2501_, v_a_2499_);
v___x_2503_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_2503_, 0, v___x_2502_);
return v___x_2503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEdit_toJson_spec__1(lean_object* v_k_2504_, lean_object* v_x_2505_){
_start:
{
if (lean_obj_tag(v_x_2505_) == 0)
{
lean_object* v___x_2506_; 
lean_dec_ref(v_k_2504_);
v___x_2506_ = lean_box(0);
return v___x_2506_;
}
else
{
lean_object* v_val_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; 
v_val_2507_ = lean_ctor_get(v_x_2505_, 0);
lean_inc(v_val_2507_);
lean_dec_ref(v_x_2505_);
v___x_2508_ = l_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEdit_toJson_spec__1_spec__2(v_val_2507_);
v___x_2509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2509_, 0, v_k_2504_);
lean_ctor_set(v___x_2509_, 1, v___x_2508_);
v___x_2510_ = lean_box(0);
v___x_2511_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2511_, 0, v___x_2509_);
lean_ctor_set(v___x_2511_, 1, v___x_2510_);
return v___x_2511_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_map___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEdit_toJson_spec__0_spec__0_spec__1(lean_object* v_t_2512_){
_start:
{
if (lean_obj_tag(v_t_2512_) == 0)
{
lean_object* v_size_2513_; lean_object* v_k_2514_; lean_object* v_v_2515_; lean_object* v_l_2516_; lean_object* v_r_2517_; lean_object* v___x_2519_; uint8_t v_isShared_2520_; uint8_t v_isSharedCheck_2527_; 
v_size_2513_ = lean_ctor_get(v_t_2512_, 0);
v_k_2514_ = lean_ctor_get(v_t_2512_, 1);
v_v_2515_ = lean_ctor_get(v_t_2512_, 2);
v_l_2516_ = lean_ctor_get(v_t_2512_, 3);
v_r_2517_ = lean_ctor_get(v_t_2512_, 4);
v_isSharedCheck_2527_ = !lean_is_exclusive(v_t_2512_);
if (v_isSharedCheck_2527_ == 0)
{
v___x_2519_ = v_t_2512_;
v_isShared_2520_ = v_isSharedCheck_2527_;
goto v_resetjp_2518_;
}
else
{
lean_inc(v_r_2517_);
lean_inc(v_l_2516_);
lean_inc(v_v_2515_);
lean_inc(v_k_2514_);
lean_inc(v_size_2513_);
lean_dec(v_t_2512_);
v___x_2519_ = lean_box(0);
v_isShared_2520_ = v_isSharedCheck_2527_;
goto v_resetjp_2518_;
}
v_resetjp_2518_:
{
lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2525_; 
v___x_2521_ = l_Array_toJson___at___00Lean_Lsp_instToJsonTextDocumentEdit_toJson_spec__0(v_v_2515_);
v___x_2522_ = l_Std_DTreeMap_Internal_Impl_map___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEdit_toJson_spec__0_spec__0_spec__1(v_l_2516_);
v___x_2523_ = l_Std_DTreeMap_Internal_Impl_map___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEdit_toJson_spec__0_spec__0_spec__1(v_r_2517_);
if (v_isShared_2520_ == 0)
{
lean_ctor_set(v___x_2519_, 4, v___x_2523_);
lean_ctor_set(v___x_2519_, 3, v___x_2522_);
lean_ctor_set(v___x_2519_, 2, v___x_2521_);
v___x_2525_ = v___x_2519_;
goto v_reusejp_2524_;
}
else
{
lean_object* v_reuseFailAlloc_2526_; 
v_reuseFailAlloc_2526_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2526_, 0, v_size_2513_);
lean_ctor_set(v_reuseFailAlloc_2526_, 1, v_k_2514_);
lean_ctor_set(v_reuseFailAlloc_2526_, 2, v___x_2521_);
lean_ctor_set(v_reuseFailAlloc_2526_, 3, v___x_2522_);
lean_ctor_set(v_reuseFailAlloc_2526_, 4, v___x_2523_);
v___x_2525_ = v_reuseFailAlloc_2526_;
goto v_reusejp_2524_;
}
v_reusejp_2524_:
{
return v___x_2525_;
}
}
}
else
{
lean_object* v___x_2528_; 
v___x_2528_ = lean_box(1);
return v___x_2528_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEdit_toJson_spec__0_spec__0(lean_object* v_map_2529_){
_start:
{
lean_object* v___x_2530_; lean_object* v___x_2531_; 
v___x_2530_ = l_Std_DTreeMap_Internal_Impl_map___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEdit_toJson_spec__0_spec__0_spec__1(v_map_2529_);
v___x_2531_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_2531_, 0, v___x_2530_);
return v___x_2531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEdit_toJson_spec__0(lean_object* v_k_2532_, lean_object* v_x_2533_){
_start:
{
if (lean_obj_tag(v_x_2533_) == 0)
{
lean_object* v___x_2534_; 
lean_dec_ref(v_k_2532_);
v___x_2534_ = lean_box(0);
return v___x_2534_;
}
else
{
lean_object* v_val_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; 
v_val_2535_ = lean_ctor_get(v_x_2533_, 0);
lean_inc(v_val_2535_);
lean_dec_ref(v_x_2533_);
v___x_2536_ = l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEdit_toJson_spec__0_spec__0(v_val_2535_);
v___x_2537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2537_, 0, v_k_2532_);
lean_ctor_set(v___x_2537_, 1, v___x_2536_);
v___x_2538_ = lean_box(0);
v___x_2539_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2539_, 0, v___x_2537_);
lean_ctor_set(v___x_2539_, 1, v___x_2538_);
return v___x_2539_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonWorkspaceEdit_toJson(lean_object* v_x_2543_){
_start:
{
lean_object* v_changes_x3f_2544_; lean_object* v_documentChanges_x3f_2545_; lean_object* v_changeAnnotations_x3f_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; 
v_changes_x3f_2544_ = lean_ctor_get(v_x_2543_, 0);
lean_inc(v_changes_x3f_2544_);
v_documentChanges_x3f_2545_ = lean_ctor_get(v_x_2543_, 1);
lean_inc(v_documentChanges_x3f_2545_);
v_changeAnnotations_x3f_2546_ = lean_ctor_get(v_x_2543_, 2);
lean_inc(v_changeAnnotations_x3f_2546_);
lean_dec_ref(v_x_2543_);
v___x_2547_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkspaceEdit_toJson___closed__0));
v___x_2548_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEdit_toJson_spec__0(v___x_2547_, v_changes_x3f_2544_);
v___x_2549_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkspaceEdit_toJson___closed__1));
v___x_2550_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEdit_toJson_spec__1(v___x_2549_, v_documentChanges_x3f_2545_);
v___x_2551_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkspaceEdit_toJson___closed__2));
v___x_2552_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEdit_toJson_spec__2(v___x_2551_, v_changeAnnotations_x3f_2546_);
v___x_2553_ = lean_box(0);
v___x_2554_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2554_, 0, v___x_2552_);
lean_ctor_set(v___x_2554_, 1, v___x_2553_);
v___x_2555_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2555_, 0, v___x_2550_);
lean_ctor_set(v___x_2555_, 1, v___x_2554_);
v___x_2556_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2556_, 0, v___x_2548_);
lean_ctor_set(v___x_2556_, 1, v___x_2555_);
v___x_2557_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__2));
v___x_2558_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLocation_toJson_spec__0(v___x_2556_, v___x_2557_);
v___x_2559_ = l_Lean_Json_mkObj(v___x_2558_);
return v___x_2559_;
}
}
LEAN_EXPORT uint8_t l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__1_spec__2___lam__0(lean_object* v_x_2562_, lean_object* v_y_2563_){
_start:
{
uint8_t v___x_2564_; 
v___x_2564_ = lean_string_dec_lt(v_x_2562_, v_y_2563_);
if (v___x_2564_ == 0)
{
uint8_t v___x_2565_; 
v___x_2565_ = lean_string_dec_eq(v_x_2562_, v_y_2563_);
if (v___x_2565_ == 0)
{
uint8_t v___x_2566_; 
v___x_2566_ = 2;
return v___x_2566_;
}
else
{
uint8_t v___x_2567_; 
v___x_2567_ = 1;
return v___x_2567_;
}
}
else
{
uint8_t v___x_2568_; 
v___x_2568_ = 0;
return v___x_2568_;
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__1_spec__2___lam__0___boxed(lean_object* v_x_2569_, lean_object* v_y_2570_){
_start:
{
uint8_t v_res_2571_; lean_object* v_r_2572_; 
v_res_2571_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__1_spec__2___lam__0(v_x_2569_, v_y_2570_);
lean_dec_ref(v_y_2570_);
lean_dec_ref(v_x_2569_);
v_r_2572_ = lean_box(v_res_2571_);
return v_r_2572_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__1_spec__2_spec__4_spec__7___redArg(lean_object* v_cmp_2573_, lean_object* v_k_2574_, lean_object* v_v_2575_, lean_object* v_t_2576_){
_start:
{
if (lean_obj_tag(v_t_2576_) == 0)
{
lean_object* v_size_2577_; lean_object* v_k_2578_; lean_object* v_v_2579_; lean_object* v_l_2580_; lean_object* v_r_2581_; lean_object* v___x_2583_; uint8_t v_isShared_2584_; uint8_t v_isSharedCheck_2862_; 
v_size_2577_ = lean_ctor_get(v_t_2576_, 0);
v_k_2578_ = lean_ctor_get(v_t_2576_, 1);
v_v_2579_ = lean_ctor_get(v_t_2576_, 2);
v_l_2580_ = lean_ctor_get(v_t_2576_, 3);
v_r_2581_ = lean_ctor_get(v_t_2576_, 4);
v_isSharedCheck_2862_ = !lean_is_exclusive(v_t_2576_);
if (v_isSharedCheck_2862_ == 0)
{
v___x_2583_ = v_t_2576_;
v_isShared_2584_ = v_isSharedCheck_2862_;
goto v_resetjp_2582_;
}
else
{
lean_inc(v_r_2581_);
lean_inc(v_l_2580_);
lean_inc(v_v_2579_);
lean_inc(v_k_2578_);
lean_inc(v_size_2577_);
lean_dec(v_t_2576_);
v___x_2583_ = lean_box(0);
v_isShared_2584_ = v_isSharedCheck_2862_;
goto v_resetjp_2582_;
}
v_resetjp_2582_:
{
lean_object* v___x_2585_; uint8_t v___x_2586_; 
lean_inc_ref(v_cmp_2573_);
lean_inc(v_k_2578_);
lean_inc_ref(v_k_2574_);
v___x_2585_ = lean_apply_2(v_cmp_2573_, v_k_2574_, v_k_2578_);
v___x_2586_ = lean_unbox(v___x_2585_);
switch(v___x_2586_)
{
case 0:
{
lean_object* v_impl_2587_; lean_object* v___x_2588_; 
lean_dec(v_size_2577_);
v_impl_2587_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__1_spec__2_spec__4_spec__7___redArg(v_cmp_2573_, v_k_2574_, v_v_2575_, v_l_2580_);
v___x_2588_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_2581_) == 0)
{
lean_object* v_size_2589_; lean_object* v_size_2590_; lean_object* v_k_2591_; lean_object* v_v_2592_; lean_object* v_l_2593_; lean_object* v_r_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; uint8_t v___x_2597_; 
v_size_2589_ = lean_ctor_get(v_r_2581_, 0);
v_size_2590_ = lean_ctor_get(v_impl_2587_, 0);
lean_inc(v_size_2590_);
v_k_2591_ = lean_ctor_get(v_impl_2587_, 1);
lean_inc(v_k_2591_);
v_v_2592_ = lean_ctor_get(v_impl_2587_, 2);
lean_inc(v_v_2592_);
v_l_2593_ = lean_ctor_get(v_impl_2587_, 3);
lean_inc(v_l_2593_);
v_r_2594_ = lean_ctor_get(v_impl_2587_, 4);
lean_inc(v_r_2594_);
v___x_2595_ = lean_unsigned_to_nat(3u);
v___x_2596_ = lean_nat_mul(v___x_2595_, v_size_2589_);
v___x_2597_ = lean_nat_dec_lt(v___x_2596_, v_size_2590_);
lean_dec(v___x_2596_);
if (v___x_2597_ == 0)
{
lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2601_; 
lean_dec(v_r_2594_);
lean_dec(v_l_2593_);
lean_dec(v_v_2592_);
lean_dec(v_k_2591_);
v___x_2598_ = lean_nat_add(v___x_2588_, v_size_2590_);
lean_dec(v_size_2590_);
v___x_2599_ = lean_nat_add(v___x_2598_, v_size_2589_);
lean_dec(v___x_2598_);
if (v_isShared_2584_ == 0)
{
lean_ctor_set(v___x_2583_, 3, v_impl_2587_);
lean_ctor_set(v___x_2583_, 0, v___x_2599_);
v___x_2601_ = v___x_2583_;
goto v_reusejp_2600_;
}
else
{
lean_object* v_reuseFailAlloc_2602_; 
v_reuseFailAlloc_2602_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2602_, 0, v___x_2599_);
lean_ctor_set(v_reuseFailAlloc_2602_, 1, v_k_2578_);
lean_ctor_set(v_reuseFailAlloc_2602_, 2, v_v_2579_);
lean_ctor_set(v_reuseFailAlloc_2602_, 3, v_impl_2587_);
lean_ctor_set(v_reuseFailAlloc_2602_, 4, v_r_2581_);
v___x_2601_ = v_reuseFailAlloc_2602_;
goto v_reusejp_2600_;
}
v_reusejp_2600_:
{
return v___x_2601_;
}
}
else
{
lean_object* v___x_2604_; uint8_t v_isShared_2605_; uint8_t v_isSharedCheck_2668_; 
v_isSharedCheck_2668_ = !lean_is_exclusive(v_impl_2587_);
if (v_isSharedCheck_2668_ == 0)
{
lean_object* v_unused_2669_; lean_object* v_unused_2670_; lean_object* v_unused_2671_; lean_object* v_unused_2672_; lean_object* v_unused_2673_; 
v_unused_2669_ = lean_ctor_get(v_impl_2587_, 4);
lean_dec(v_unused_2669_);
v_unused_2670_ = lean_ctor_get(v_impl_2587_, 3);
lean_dec(v_unused_2670_);
v_unused_2671_ = lean_ctor_get(v_impl_2587_, 2);
lean_dec(v_unused_2671_);
v_unused_2672_ = lean_ctor_get(v_impl_2587_, 1);
lean_dec(v_unused_2672_);
v_unused_2673_ = lean_ctor_get(v_impl_2587_, 0);
lean_dec(v_unused_2673_);
v___x_2604_ = v_impl_2587_;
v_isShared_2605_ = v_isSharedCheck_2668_;
goto v_resetjp_2603_;
}
else
{
lean_dec(v_impl_2587_);
v___x_2604_ = lean_box(0);
v_isShared_2605_ = v_isSharedCheck_2668_;
goto v_resetjp_2603_;
}
v_resetjp_2603_:
{
lean_object* v_size_2606_; lean_object* v_size_2607_; lean_object* v_k_2608_; lean_object* v_v_2609_; lean_object* v_l_2610_; lean_object* v_r_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; uint8_t v___x_2614_; 
v_size_2606_ = lean_ctor_get(v_l_2593_, 0);
v_size_2607_ = lean_ctor_get(v_r_2594_, 0);
v_k_2608_ = lean_ctor_get(v_r_2594_, 1);
v_v_2609_ = lean_ctor_get(v_r_2594_, 2);
v_l_2610_ = lean_ctor_get(v_r_2594_, 3);
v_r_2611_ = lean_ctor_get(v_r_2594_, 4);
v___x_2612_ = lean_unsigned_to_nat(2u);
v___x_2613_ = lean_nat_mul(v___x_2612_, v_size_2606_);
v___x_2614_ = lean_nat_dec_lt(v_size_2607_, v___x_2613_);
lean_dec(v___x_2613_);
if (v___x_2614_ == 0)
{
lean_object* v___x_2616_; uint8_t v_isShared_2617_; uint8_t v_isSharedCheck_2643_; 
lean_inc(v_r_2611_);
lean_inc(v_l_2610_);
lean_inc(v_v_2609_);
lean_inc(v_k_2608_);
v_isSharedCheck_2643_ = !lean_is_exclusive(v_r_2594_);
if (v_isSharedCheck_2643_ == 0)
{
lean_object* v_unused_2644_; lean_object* v_unused_2645_; lean_object* v_unused_2646_; lean_object* v_unused_2647_; lean_object* v_unused_2648_; 
v_unused_2644_ = lean_ctor_get(v_r_2594_, 4);
lean_dec(v_unused_2644_);
v_unused_2645_ = lean_ctor_get(v_r_2594_, 3);
lean_dec(v_unused_2645_);
v_unused_2646_ = lean_ctor_get(v_r_2594_, 2);
lean_dec(v_unused_2646_);
v_unused_2647_ = lean_ctor_get(v_r_2594_, 1);
lean_dec(v_unused_2647_);
v_unused_2648_ = lean_ctor_get(v_r_2594_, 0);
lean_dec(v_unused_2648_);
v___x_2616_ = v_r_2594_;
v_isShared_2617_ = v_isSharedCheck_2643_;
goto v_resetjp_2615_;
}
else
{
lean_dec(v_r_2594_);
v___x_2616_ = lean_box(0);
v_isShared_2617_ = v_isSharedCheck_2643_;
goto v_resetjp_2615_;
}
v_resetjp_2615_:
{
lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___y_2621_; lean_object* v___y_2622_; lean_object* v___y_2623_; lean_object* v___x_2631_; lean_object* v___y_2633_; 
v___x_2618_ = lean_nat_add(v___x_2588_, v_size_2590_);
lean_dec(v_size_2590_);
v___x_2619_ = lean_nat_add(v___x_2618_, v_size_2589_);
lean_dec(v___x_2618_);
v___x_2631_ = lean_nat_add(v___x_2588_, v_size_2606_);
if (lean_obj_tag(v_l_2610_) == 0)
{
lean_object* v_size_2641_; 
v_size_2641_ = lean_ctor_get(v_l_2610_, 0);
lean_inc(v_size_2641_);
v___y_2633_ = v_size_2641_;
goto v___jp_2632_;
}
else
{
lean_object* v___x_2642_; 
v___x_2642_ = lean_unsigned_to_nat(0u);
v___y_2633_ = v___x_2642_;
goto v___jp_2632_;
}
v___jp_2620_:
{
lean_object* v___x_2624_; lean_object* v___x_2626_; 
v___x_2624_ = lean_nat_add(v___y_2622_, v___y_2623_);
lean_dec(v___y_2623_);
lean_dec(v___y_2622_);
if (v_isShared_2617_ == 0)
{
lean_ctor_set(v___x_2616_, 4, v_r_2581_);
lean_ctor_set(v___x_2616_, 3, v_r_2611_);
lean_ctor_set(v___x_2616_, 2, v_v_2579_);
lean_ctor_set(v___x_2616_, 1, v_k_2578_);
lean_ctor_set(v___x_2616_, 0, v___x_2624_);
v___x_2626_ = v___x_2616_;
goto v_reusejp_2625_;
}
else
{
lean_object* v_reuseFailAlloc_2630_; 
v_reuseFailAlloc_2630_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2630_, 0, v___x_2624_);
lean_ctor_set(v_reuseFailAlloc_2630_, 1, v_k_2578_);
lean_ctor_set(v_reuseFailAlloc_2630_, 2, v_v_2579_);
lean_ctor_set(v_reuseFailAlloc_2630_, 3, v_r_2611_);
lean_ctor_set(v_reuseFailAlloc_2630_, 4, v_r_2581_);
v___x_2626_ = v_reuseFailAlloc_2630_;
goto v_reusejp_2625_;
}
v_reusejp_2625_:
{
lean_object* v___x_2628_; 
if (v_isShared_2605_ == 0)
{
lean_ctor_set(v___x_2604_, 4, v___x_2626_);
lean_ctor_set(v___x_2604_, 3, v___y_2621_);
lean_ctor_set(v___x_2604_, 2, v_v_2609_);
lean_ctor_set(v___x_2604_, 1, v_k_2608_);
lean_ctor_set(v___x_2604_, 0, v___x_2619_);
v___x_2628_ = v___x_2604_;
goto v_reusejp_2627_;
}
else
{
lean_object* v_reuseFailAlloc_2629_; 
v_reuseFailAlloc_2629_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2629_, 0, v___x_2619_);
lean_ctor_set(v_reuseFailAlloc_2629_, 1, v_k_2608_);
lean_ctor_set(v_reuseFailAlloc_2629_, 2, v_v_2609_);
lean_ctor_set(v_reuseFailAlloc_2629_, 3, v___y_2621_);
lean_ctor_set(v_reuseFailAlloc_2629_, 4, v___x_2626_);
v___x_2628_ = v_reuseFailAlloc_2629_;
goto v_reusejp_2627_;
}
v_reusejp_2627_:
{
return v___x_2628_;
}
}
}
v___jp_2632_:
{
lean_object* v___x_2634_; lean_object* v___x_2636_; 
v___x_2634_ = lean_nat_add(v___x_2631_, v___y_2633_);
lean_dec(v___y_2633_);
lean_dec(v___x_2631_);
if (v_isShared_2584_ == 0)
{
lean_ctor_set(v___x_2583_, 4, v_l_2610_);
lean_ctor_set(v___x_2583_, 3, v_l_2593_);
lean_ctor_set(v___x_2583_, 2, v_v_2592_);
lean_ctor_set(v___x_2583_, 1, v_k_2591_);
lean_ctor_set(v___x_2583_, 0, v___x_2634_);
v___x_2636_ = v___x_2583_;
goto v_reusejp_2635_;
}
else
{
lean_object* v_reuseFailAlloc_2640_; 
v_reuseFailAlloc_2640_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2640_, 0, v___x_2634_);
lean_ctor_set(v_reuseFailAlloc_2640_, 1, v_k_2591_);
lean_ctor_set(v_reuseFailAlloc_2640_, 2, v_v_2592_);
lean_ctor_set(v_reuseFailAlloc_2640_, 3, v_l_2593_);
lean_ctor_set(v_reuseFailAlloc_2640_, 4, v_l_2610_);
v___x_2636_ = v_reuseFailAlloc_2640_;
goto v_reusejp_2635_;
}
v_reusejp_2635_:
{
lean_object* v___x_2637_; 
v___x_2637_ = lean_nat_add(v___x_2588_, v_size_2589_);
if (lean_obj_tag(v_r_2611_) == 0)
{
lean_object* v_size_2638_; 
v_size_2638_ = lean_ctor_get(v_r_2611_, 0);
lean_inc(v_size_2638_);
v___y_2621_ = v___x_2636_;
v___y_2622_ = v___x_2637_;
v___y_2623_ = v_size_2638_;
goto v___jp_2620_;
}
else
{
lean_object* v___x_2639_; 
v___x_2639_ = lean_unsigned_to_nat(0u);
v___y_2621_ = v___x_2636_;
v___y_2622_ = v___x_2637_;
v___y_2623_ = v___x_2639_;
goto v___jp_2620_;
}
}
}
}
}
else
{
lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2654_; 
lean_del_object(v___x_2583_);
v___x_2649_ = lean_nat_add(v___x_2588_, v_size_2590_);
lean_dec(v_size_2590_);
v___x_2650_ = lean_nat_add(v___x_2649_, v_size_2589_);
lean_dec(v___x_2649_);
v___x_2651_ = lean_nat_add(v___x_2588_, v_size_2589_);
v___x_2652_ = lean_nat_add(v___x_2651_, v_size_2607_);
lean_dec(v___x_2651_);
lean_inc_ref(v_r_2581_);
if (v_isShared_2605_ == 0)
{
lean_ctor_set(v___x_2604_, 4, v_r_2581_);
lean_ctor_set(v___x_2604_, 3, v_r_2594_);
lean_ctor_set(v___x_2604_, 2, v_v_2579_);
lean_ctor_set(v___x_2604_, 1, v_k_2578_);
lean_ctor_set(v___x_2604_, 0, v___x_2652_);
v___x_2654_ = v___x_2604_;
goto v_reusejp_2653_;
}
else
{
lean_object* v_reuseFailAlloc_2667_; 
v_reuseFailAlloc_2667_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2667_, 0, v___x_2652_);
lean_ctor_set(v_reuseFailAlloc_2667_, 1, v_k_2578_);
lean_ctor_set(v_reuseFailAlloc_2667_, 2, v_v_2579_);
lean_ctor_set(v_reuseFailAlloc_2667_, 3, v_r_2594_);
lean_ctor_set(v_reuseFailAlloc_2667_, 4, v_r_2581_);
v___x_2654_ = v_reuseFailAlloc_2667_;
goto v_reusejp_2653_;
}
v_reusejp_2653_:
{
lean_object* v___x_2656_; uint8_t v_isShared_2657_; uint8_t v_isSharedCheck_2661_; 
v_isSharedCheck_2661_ = !lean_is_exclusive(v_r_2581_);
if (v_isSharedCheck_2661_ == 0)
{
lean_object* v_unused_2662_; lean_object* v_unused_2663_; lean_object* v_unused_2664_; lean_object* v_unused_2665_; lean_object* v_unused_2666_; 
v_unused_2662_ = lean_ctor_get(v_r_2581_, 4);
lean_dec(v_unused_2662_);
v_unused_2663_ = lean_ctor_get(v_r_2581_, 3);
lean_dec(v_unused_2663_);
v_unused_2664_ = lean_ctor_get(v_r_2581_, 2);
lean_dec(v_unused_2664_);
v_unused_2665_ = lean_ctor_get(v_r_2581_, 1);
lean_dec(v_unused_2665_);
v_unused_2666_ = lean_ctor_get(v_r_2581_, 0);
lean_dec(v_unused_2666_);
v___x_2656_ = v_r_2581_;
v_isShared_2657_ = v_isSharedCheck_2661_;
goto v_resetjp_2655_;
}
else
{
lean_dec(v_r_2581_);
v___x_2656_ = lean_box(0);
v_isShared_2657_ = v_isSharedCheck_2661_;
goto v_resetjp_2655_;
}
v_resetjp_2655_:
{
lean_object* v___x_2659_; 
if (v_isShared_2657_ == 0)
{
lean_ctor_set(v___x_2656_, 4, v___x_2654_);
lean_ctor_set(v___x_2656_, 3, v_l_2593_);
lean_ctor_set(v___x_2656_, 2, v_v_2592_);
lean_ctor_set(v___x_2656_, 1, v_k_2591_);
lean_ctor_set(v___x_2656_, 0, v___x_2650_);
v___x_2659_ = v___x_2656_;
goto v_reusejp_2658_;
}
else
{
lean_object* v_reuseFailAlloc_2660_; 
v_reuseFailAlloc_2660_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2660_, 0, v___x_2650_);
lean_ctor_set(v_reuseFailAlloc_2660_, 1, v_k_2591_);
lean_ctor_set(v_reuseFailAlloc_2660_, 2, v_v_2592_);
lean_ctor_set(v_reuseFailAlloc_2660_, 3, v_l_2593_);
lean_ctor_set(v_reuseFailAlloc_2660_, 4, v___x_2654_);
v___x_2659_ = v_reuseFailAlloc_2660_;
goto v_reusejp_2658_;
}
v_reusejp_2658_:
{
return v___x_2659_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2674_; 
v_l_2674_ = lean_ctor_get(v_impl_2587_, 3);
lean_inc(v_l_2674_);
if (lean_obj_tag(v_l_2674_) == 0)
{
lean_object* v_r_2675_; lean_object* v_k_2676_; lean_object* v_v_2677_; lean_object* v___x_2679_; uint8_t v_isShared_2680_; uint8_t v_isSharedCheck_2688_; 
v_r_2675_ = lean_ctor_get(v_impl_2587_, 4);
v_k_2676_ = lean_ctor_get(v_impl_2587_, 1);
v_v_2677_ = lean_ctor_get(v_impl_2587_, 2);
v_isSharedCheck_2688_ = !lean_is_exclusive(v_impl_2587_);
if (v_isSharedCheck_2688_ == 0)
{
lean_object* v_unused_2689_; lean_object* v_unused_2690_; 
v_unused_2689_ = lean_ctor_get(v_impl_2587_, 3);
lean_dec(v_unused_2689_);
v_unused_2690_ = lean_ctor_get(v_impl_2587_, 0);
lean_dec(v_unused_2690_);
v___x_2679_ = v_impl_2587_;
v_isShared_2680_ = v_isSharedCheck_2688_;
goto v_resetjp_2678_;
}
else
{
lean_inc(v_r_2675_);
lean_inc(v_v_2677_);
lean_inc(v_k_2676_);
lean_dec(v_impl_2587_);
v___x_2679_ = lean_box(0);
v_isShared_2680_ = v_isSharedCheck_2688_;
goto v_resetjp_2678_;
}
v_resetjp_2678_:
{
lean_object* v___x_2681_; lean_object* v___x_2683_; 
v___x_2681_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_2675_);
if (v_isShared_2680_ == 0)
{
lean_ctor_set(v___x_2679_, 3, v_r_2675_);
lean_ctor_set(v___x_2679_, 2, v_v_2579_);
lean_ctor_set(v___x_2679_, 1, v_k_2578_);
lean_ctor_set(v___x_2679_, 0, v___x_2588_);
v___x_2683_ = v___x_2679_;
goto v_reusejp_2682_;
}
else
{
lean_object* v_reuseFailAlloc_2687_; 
v_reuseFailAlloc_2687_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2687_, 0, v___x_2588_);
lean_ctor_set(v_reuseFailAlloc_2687_, 1, v_k_2578_);
lean_ctor_set(v_reuseFailAlloc_2687_, 2, v_v_2579_);
lean_ctor_set(v_reuseFailAlloc_2687_, 3, v_r_2675_);
lean_ctor_set(v_reuseFailAlloc_2687_, 4, v_r_2675_);
v___x_2683_ = v_reuseFailAlloc_2687_;
goto v_reusejp_2682_;
}
v_reusejp_2682_:
{
lean_object* v___x_2685_; 
if (v_isShared_2584_ == 0)
{
lean_ctor_set(v___x_2583_, 4, v___x_2683_);
lean_ctor_set(v___x_2583_, 3, v_l_2674_);
lean_ctor_set(v___x_2583_, 2, v_v_2677_);
lean_ctor_set(v___x_2583_, 1, v_k_2676_);
lean_ctor_set(v___x_2583_, 0, v___x_2681_);
v___x_2685_ = v___x_2583_;
goto v_reusejp_2684_;
}
else
{
lean_object* v_reuseFailAlloc_2686_; 
v_reuseFailAlloc_2686_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2686_, 0, v___x_2681_);
lean_ctor_set(v_reuseFailAlloc_2686_, 1, v_k_2676_);
lean_ctor_set(v_reuseFailAlloc_2686_, 2, v_v_2677_);
lean_ctor_set(v_reuseFailAlloc_2686_, 3, v_l_2674_);
lean_ctor_set(v_reuseFailAlloc_2686_, 4, v___x_2683_);
v___x_2685_ = v_reuseFailAlloc_2686_;
goto v_reusejp_2684_;
}
v_reusejp_2684_:
{
return v___x_2685_;
}
}
}
}
else
{
lean_object* v_r_2691_; 
v_r_2691_ = lean_ctor_get(v_impl_2587_, 4);
lean_inc(v_r_2691_);
if (lean_obj_tag(v_r_2691_) == 0)
{
lean_object* v_k_2692_; lean_object* v_v_2693_; lean_object* v___x_2695_; uint8_t v_isShared_2696_; uint8_t v_isSharedCheck_2716_; 
v_k_2692_ = lean_ctor_get(v_impl_2587_, 1);
v_v_2693_ = lean_ctor_get(v_impl_2587_, 2);
v_isSharedCheck_2716_ = !lean_is_exclusive(v_impl_2587_);
if (v_isSharedCheck_2716_ == 0)
{
lean_object* v_unused_2717_; lean_object* v_unused_2718_; lean_object* v_unused_2719_; 
v_unused_2717_ = lean_ctor_get(v_impl_2587_, 4);
lean_dec(v_unused_2717_);
v_unused_2718_ = lean_ctor_get(v_impl_2587_, 3);
lean_dec(v_unused_2718_);
v_unused_2719_ = lean_ctor_get(v_impl_2587_, 0);
lean_dec(v_unused_2719_);
v___x_2695_ = v_impl_2587_;
v_isShared_2696_ = v_isSharedCheck_2716_;
goto v_resetjp_2694_;
}
else
{
lean_inc(v_v_2693_);
lean_inc(v_k_2692_);
lean_dec(v_impl_2587_);
v___x_2695_ = lean_box(0);
v_isShared_2696_ = v_isSharedCheck_2716_;
goto v_resetjp_2694_;
}
v_resetjp_2694_:
{
lean_object* v_k_2697_; lean_object* v_v_2698_; lean_object* v___x_2700_; uint8_t v_isShared_2701_; uint8_t v_isSharedCheck_2712_; 
v_k_2697_ = lean_ctor_get(v_r_2691_, 1);
v_v_2698_ = lean_ctor_get(v_r_2691_, 2);
v_isSharedCheck_2712_ = !lean_is_exclusive(v_r_2691_);
if (v_isSharedCheck_2712_ == 0)
{
lean_object* v_unused_2713_; lean_object* v_unused_2714_; lean_object* v_unused_2715_; 
v_unused_2713_ = lean_ctor_get(v_r_2691_, 4);
lean_dec(v_unused_2713_);
v_unused_2714_ = lean_ctor_get(v_r_2691_, 3);
lean_dec(v_unused_2714_);
v_unused_2715_ = lean_ctor_get(v_r_2691_, 0);
lean_dec(v_unused_2715_);
v___x_2700_ = v_r_2691_;
v_isShared_2701_ = v_isSharedCheck_2712_;
goto v_resetjp_2699_;
}
else
{
lean_inc(v_v_2698_);
lean_inc(v_k_2697_);
lean_dec(v_r_2691_);
v___x_2700_ = lean_box(0);
v_isShared_2701_ = v_isSharedCheck_2712_;
goto v_resetjp_2699_;
}
v_resetjp_2699_:
{
lean_object* v___x_2702_; lean_object* v___x_2704_; 
v___x_2702_ = lean_unsigned_to_nat(3u);
if (v_isShared_2701_ == 0)
{
lean_ctor_set(v___x_2700_, 4, v_l_2674_);
lean_ctor_set(v___x_2700_, 3, v_l_2674_);
lean_ctor_set(v___x_2700_, 2, v_v_2693_);
lean_ctor_set(v___x_2700_, 1, v_k_2692_);
lean_ctor_set(v___x_2700_, 0, v___x_2588_);
v___x_2704_ = v___x_2700_;
goto v_reusejp_2703_;
}
else
{
lean_object* v_reuseFailAlloc_2711_; 
v_reuseFailAlloc_2711_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2711_, 0, v___x_2588_);
lean_ctor_set(v_reuseFailAlloc_2711_, 1, v_k_2692_);
lean_ctor_set(v_reuseFailAlloc_2711_, 2, v_v_2693_);
lean_ctor_set(v_reuseFailAlloc_2711_, 3, v_l_2674_);
lean_ctor_set(v_reuseFailAlloc_2711_, 4, v_l_2674_);
v___x_2704_ = v_reuseFailAlloc_2711_;
goto v_reusejp_2703_;
}
v_reusejp_2703_:
{
lean_object* v___x_2706_; 
if (v_isShared_2696_ == 0)
{
lean_ctor_set(v___x_2695_, 4, v_l_2674_);
lean_ctor_set(v___x_2695_, 2, v_v_2579_);
lean_ctor_set(v___x_2695_, 1, v_k_2578_);
lean_ctor_set(v___x_2695_, 0, v___x_2588_);
v___x_2706_ = v___x_2695_;
goto v_reusejp_2705_;
}
else
{
lean_object* v_reuseFailAlloc_2710_; 
v_reuseFailAlloc_2710_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2710_, 0, v___x_2588_);
lean_ctor_set(v_reuseFailAlloc_2710_, 1, v_k_2578_);
lean_ctor_set(v_reuseFailAlloc_2710_, 2, v_v_2579_);
lean_ctor_set(v_reuseFailAlloc_2710_, 3, v_l_2674_);
lean_ctor_set(v_reuseFailAlloc_2710_, 4, v_l_2674_);
v___x_2706_ = v_reuseFailAlloc_2710_;
goto v_reusejp_2705_;
}
v_reusejp_2705_:
{
lean_object* v___x_2708_; 
if (v_isShared_2584_ == 0)
{
lean_ctor_set(v___x_2583_, 4, v___x_2706_);
lean_ctor_set(v___x_2583_, 3, v___x_2704_);
lean_ctor_set(v___x_2583_, 2, v_v_2698_);
lean_ctor_set(v___x_2583_, 1, v_k_2697_);
lean_ctor_set(v___x_2583_, 0, v___x_2702_);
v___x_2708_ = v___x_2583_;
goto v_reusejp_2707_;
}
else
{
lean_object* v_reuseFailAlloc_2709_; 
v_reuseFailAlloc_2709_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2709_, 0, v___x_2702_);
lean_ctor_set(v_reuseFailAlloc_2709_, 1, v_k_2697_);
lean_ctor_set(v_reuseFailAlloc_2709_, 2, v_v_2698_);
lean_ctor_set(v_reuseFailAlloc_2709_, 3, v___x_2704_);
lean_ctor_set(v_reuseFailAlloc_2709_, 4, v___x_2706_);
v___x_2708_ = v_reuseFailAlloc_2709_;
goto v_reusejp_2707_;
}
v_reusejp_2707_:
{
return v___x_2708_;
}
}
}
}
}
}
else
{
lean_object* v___x_2720_; lean_object* v___x_2722_; 
v___x_2720_ = lean_unsigned_to_nat(2u);
if (v_isShared_2584_ == 0)
{
lean_ctor_set(v___x_2583_, 4, v_r_2691_);
lean_ctor_set(v___x_2583_, 3, v_impl_2587_);
lean_ctor_set(v___x_2583_, 0, v___x_2720_);
v___x_2722_ = v___x_2583_;
goto v_reusejp_2721_;
}
else
{
lean_object* v_reuseFailAlloc_2723_; 
v_reuseFailAlloc_2723_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2723_, 0, v___x_2720_);
lean_ctor_set(v_reuseFailAlloc_2723_, 1, v_k_2578_);
lean_ctor_set(v_reuseFailAlloc_2723_, 2, v_v_2579_);
lean_ctor_set(v_reuseFailAlloc_2723_, 3, v_impl_2587_);
lean_ctor_set(v_reuseFailAlloc_2723_, 4, v_r_2691_);
v___x_2722_ = v_reuseFailAlloc_2723_;
goto v_reusejp_2721_;
}
v_reusejp_2721_:
{
return v___x_2722_;
}
}
}
}
}
case 1:
{
lean_object* v___x_2725_; 
lean_dec(v_v_2579_);
lean_dec(v_k_2578_);
lean_dec_ref(v_cmp_2573_);
if (v_isShared_2584_ == 0)
{
lean_ctor_set(v___x_2583_, 2, v_v_2575_);
lean_ctor_set(v___x_2583_, 1, v_k_2574_);
v___x_2725_ = v___x_2583_;
goto v_reusejp_2724_;
}
else
{
lean_object* v_reuseFailAlloc_2726_; 
v_reuseFailAlloc_2726_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2726_, 0, v_size_2577_);
lean_ctor_set(v_reuseFailAlloc_2726_, 1, v_k_2574_);
lean_ctor_set(v_reuseFailAlloc_2726_, 2, v_v_2575_);
lean_ctor_set(v_reuseFailAlloc_2726_, 3, v_l_2580_);
lean_ctor_set(v_reuseFailAlloc_2726_, 4, v_r_2581_);
v___x_2725_ = v_reuseFailAlloc_2726_;
goto v_reusejp_2724_;
}
v_reusejp_2724_:
{
return v___x_2725_;
}
}
default: 
{
lean_object* v_impl_2727_; lean_object* v___x_2728_; 
lean_dec(v_size_2577_);
v_impl_2727_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__1_spec__2_spec__4_spec__7___redArg(v_cmp_2573_, v_k_2574_, v_v_2575_, v_r_2581_);
v___x_2728_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_2580_) == 0)
{
lean_object* v_size_2729_; lean_object* v_size_2730_; lean_object* v_k_2731_; lean_object* v_v_2732_; lean_object* v_l_2733_; lean_object* v_r_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; uint8_t v___x_2737_; 
v_size_2729_ = lean_ctor_get(v_l_2580_, 0);
v_size_2730_ = lean_ctor_get(v_impl_2727_, 0);
lean_inc(v_size_2730_);
v_k_2731_ = lean_ctor_get(v_impl_2727_, 1);
lean_inc(v_k_2731_);
v_v_2732_ = lean_ctor_get(v_impl_2727_, 2);
lean_inc(v_v_2732_);
v_l_2733_ = lean_ctor_get(v_impl_2727_, 3);
lean_inc(v_l_2733_);
v_r_2734_ = lean_ctor_get(v_impl_2727_, 4);
lean_inc(v_r_2734_);
v___x_2735_ = lean_unsigned_to_nat(3u);
v___x_2736_ = lean_nat_mul(v___x_2735_, v_size_2729_);
v___x_2737_ = lean_nat_dec_lt(v___x_2736_, v_size_2730_);
lean_dec(v___x_2736_);
if (v___x_2737_ == 0)
{
lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2741_; 
lean_dec(v_r_2734_);
lean_dec(v_l_2733_);
lean_dec(v_v_2732_);
lean_dec(v_k_2731_);
v___x_2738_ = lean_nat_add(v___x_2728_, v_size_2729_);
v___x_2739_ = lean_nat_add(v___x_2738_, v_size_2730_);
lean_dec(v_size_2730_);
lean_dec(v___x_2738_);
if (v_isShared_2584_ == 0)
{
lean_ctor_set(v___x_2583_, 4, v_impl_2727_);
lean_ctor_set(v___x_2583_, 0, v___x_2739_);
v___x_2741_ = v___x_2583_;
goto v_reusejp_2740_;
}
else
{
lean_object* v_reuseFailAlloc_2742_; 
v_reuseFailAlloc_2742_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2742_, 0, v___x_2739_);
lean_ctor_set(v_reuseFailAlloc_2742_, 1, v_k_2578_);
lean_ctor_set(v_reuseFailAlloc_2742_, 2, v_v_2579_);
lean_ctor_set(v_reuseFailAlloc_2742_, 3, v_l_2580_);
lean_ctor_set(v_reuseFailAlloc_2742_, 4, v_impl_2727_);
v___x_2741_ = v_reuseFailAlloc_2742_;
goto v_reusejp_2740_;
}
v_reusejp_2740_:
{
return v___x_2741_;
}
}
else
{
lean_object* v___x_2744_; uint8_t v_isShared_2745_; uint8_t v_isSharedCheck_2806_; 
v_isSharedCheck_2806_ = !lean_is_exclusive(v_impl_2727_);
if (v_isSharedCheck_2806_ == 0)
{
lean_object* v_unused_2807_; lean_object* v_unused_2808_; lean_object* v_unused_2809_; lean_object* v_unused_2810_; lean_object* v_unused_2811_; 
v_unused_2807_ = lean_ctor_get(v_impl_2727_, 4);
lean_dec(v_unused_2807_);
v_unused_2808_ = lean_ctor_get(v_impl_2727_, 3);
lean_dec(v_unused_2808_);
v_unused_2809_ = lean_ctor_get(v_impl_2727_, 2);
lean_dec(v_unused_2809_);
v_unused_2810_ = lean_ctor_get(v_impl_2727_, 1);
lean_dec(v_unused_2810_);
v_unused_2811_ = lean_ctor_get(v_impl_2727_, 0);
lean_dec(v_unused_2811_);
v___x_2744_ = v_impl_2727_;
v_isShared_2745_ = v_isSharedCheck_2806_;
goto v_resetjp_2743_;
}
else
{
lean_dec(v_impl_2727_);
v___x_2744_ = lean_box(0);
v_isShared_2745_ = v_isSharedCheck_2806_;
goto v_resetjp_2743_;
}
v_resetjp_2743_:
{
lean_object* v_size_2746_; lean_object* v_k_2747_; lean_object* v_v_2748_; lean_object* v_l_2749_; lean_object* v_r_2750_; lean_object* v_size_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; uint8_t v___x_2754_; 
v_size_2746_ = lean_ctor_get(v_l_2733_, 0);
v_k_2747_ = lean_ctor_get(v_l_2733_, 1);
v_v_2748_ = lean_ctor_get(v_l_2733_, 2);
v_l_2749_ = lean_ctor_get(v_l_2733_, 3);
v_r_2750_ = lean_ctor_get(v_l_2733_, 4);
v_size_2751_ = lean_ctor_get(v_r_2734_, 0);
v___x_2752_ = lean_unsigned_to_nat(2u);
v___x_2753_ = lean_nat_mul(v___x_2752_, v_size_2751_);
v___x_2754_ = lean_nat_dec_lt(v_size_2746_, v___x_2753_);
lean_dec(v___x_2753_);
if (v___x_2754_ == 0)
{
lean_object* v___x_2756_; uint8_t v_isShared_2757_; uint8_t v_isSharedCheck_2782_; 
lean_inc(v_r_2750_);
lean_inc(v_l_2749_);
lean_inc(v_v_2748_);
lean_inc(v_k_2747_);
v_isSharedCheck_2782_ = !lean_is_exclusive(v_l_2733_);
if (v_isSharedCheck_2782_ == 0)
{
lean_object* v_unused_2783_; lean_object* v_unused_2784_; lean_object* v_unused_2785_; lean_object* v_unused_2786_; lean_object* v_unused_2787_; 
v_unused_2783_ = lean_ctor_get(v_l_2733_, 4);
lean_dec(v_unused_2783_);
v_unused_2784_ = lean_ctor_get(v_l_2733_, 3);
lean_dec(v_unused_2784_);
v_unused_2785_ = lean_ctor_get(v_l_2733_, 2);
lean_dec(v_unused_2785_);
v_unused_2786_ = lean_ctor_get(v_l_2733_, 1);
lean_dec(v_unused_2786_);
v_unused_2787_ = lean_ctor_get(v_l_2733_, 0);
lean_dec(v_unused_2787_);
v___x_2756_ = v_l_2733_;
v_isShared_2757_ = v_isSharedCheck_2782_;
goto v_resetjp_2755_;
}
else
{
lean_dec(v_l_2733_);
v___x_2756_ = lean_box(0);
v_isShared_2757_ = v_isSharedCheck_2782_;
goto v_resetjp_2755_;
}
v_resetjp_2755_:
{
lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___y_2761_; lean_object* v___y_2762_; lean_object* v___y_2763_; lean_object* v___y_2772_; 
v___x_2758_ = lean_nat_add(v___x_2728_, v_size_2729_);
v___x_2759_ = lean_nat_add(v___x_2758_, v_size_2730_);
lean_dec(v_size_2730_);
if (lean_obj_tag(v_l_2749_) == 0)
{
lean_object* v_size_2780_; 
v_size_2780_ = lean_ctor_get(v_l_2749_, 0);
lean_inc(v_size_2780_);
v___y_2772_ = v_size_2780_;
goto v___jp_2771_;
}
else
{
lean_object* v___x_2781_; 
v___x_2781_ = lean_unsigned_to_nat(0u);
v___y_2772_ = v___x_2781_;
goto v___jp_2771_;
}
v___jp_2760_:
{
lean_object* v___x_2764_; lean_object* v___x_2766_; 
v___x_2764_ = lean_nat_add(v___y_2762_, v___y_2763_);
lean_dec(v___y_2763_);
lean_dec(v___y_2762_);
if (v_isShared_2757_ == 0)
{
lean_ctor_set(v___x_2756_, 4, v_r_2734_);
lean_ctor_set(v___x_2756_, 3, v_r_2750_);
lean_ctor_set(v___x_2756_, 2, v_v_2732_);
lean_ctor_set(v___x_2756_, 1, v_k_2731_);
lean_ctor_set(v___x_2756_, 0, v___x_2764_);
v___x_2766_ = v___x_2756_;
goto v_reusejp_2765_;
}
else
{
lean_object* v_reuseFailAlloc_2770_; 
v_reuseFailAlloc_2770_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2770_, 0, v___x_2764_);
lean_ctor_set(v_reuseFailAlloc_2770_, 1, v_k_2731_);
lean_ctor_set(v_reuseFailAlloc_2770_, 2, v_v_2732_);
lean_ctor_set(v_reuseFailAlloc_2770_, 3, v_r_2750_);
lean_ctor_set(v_reuseFailAlloc_2770_, 4, v_r_2734_);
v___x_2766_ = v_reuseFailAlloc_2770_;
goto v_reusejp_2765_;
}
v_reusejp_2765_:
{
lean_object* v___x_2768_; 
if (v_isShared_2745_ == 0)
{
lean_ctor_set(v___x_2744_, 4, v___x_2766_);
lean_ctor_set(v___x_2744_, 3, v___y_2761_);
lean_ctor_set(v___x_2744_, 2, v_v_2748_);
lean_ctor_set(v___x_2744_, 1, v_k_2747_);
lean_ctor_set(v___x_2744_, 0, v___x_2759_);
v___x_2768_ = v___x_2744_;
goto v_reusejp_2767_;
}
else
{
lean_object* v_reuseFailAlloc_2769_; 
v_reuseFailAlloc_2769_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2769_, 0, v___x_2759_);
lean_ctor_set(v_reuseFailAlloc_2769_, 1, v_k_2747_);
lean_ctor_set(v_reuseFailAlloc_2769_, 2, v_v_2748_);
lean_ctor_set(v_reuseFailAlloc_2769_, 3, v___y_2761_);
lean_ctor_set(v_reuseFailAlloc_2769_, 4, v___x_2766_);
v___x_2768_ = v_reuseFailAlloc_2769_;
goto v_reusejp_2767_;
}
v_reusejp_2767_:
{
return v___x_2768_;
}
}
}
v___jp_2771_:
{
lean_object* v___x_2773_; lean_object* v___x_2775_; 
v___x_2773_ = lean_nat_add(v___x_2758_, v___y_2772_);
lean_dec(v___y_2772_);
lean_dec(v___x_2758_);
if (v_isShared_2584_ == 0)
{
lean_ctor_set(v___x_2583_, 4, v_l_2749_);
lean_ctor_set(v___x_2583_, 0, v___x_2773_);
v___x_2775_ = v___x_2583_;
goto v_reusejp_2774_;
}
else
{
lean_object* v_reuseFailAlloc_2779_; 
v_reuseFailAlloc_2779_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2779_, 0, v___x_2773_);
lean_ctor_set(v_reuseFailAlloc_2779_, 1, v_k_2578_);
lean_ctor_set(v_reuseFailAlloc_2779_, 2, v_v_2579_);
lean_ctor_set(v_reuseFailAlloc_2779_, 3, v_l_2580_);
lean_ctor_set(v_reuseFailAlloc_2779_, 4, v_l_2749_);
v___x_2775_ = v_reuseFailAlloc_2779_;
goto v_reusejp_2774_;
}
v_reusejp_2774_:
{
lean_object* v___x_2776_; 
v___x_2776_ = lean_nat_add(v___x_2728_, v_size_2751_);
if (lean_obj_tag(v_r_2750_) == 0)
{
lean_object* v_size_2777_; 
v_size_2777_ = lean_ctor_get(v_r_2750_, 0);
lean_inc(v_size_2777_);
v___y_2761_ = v___x_2775_;
v___y_2762_ = v___x_2776_;
v___y_2763_ = v_size_2777_;
goto v___jp_2760_;
}
else
{
lean_object* v___x_2778_; 
v___x_2778_ = lean_unsigned_to_nat(0u);
v___y_2761_ = v___x_2775_;
v___y_2762_ = v___x_2776_;
v___y_2763_ = v___x_2778_;
goto v___jp_2760_;
}
}
}
}
}
else
{
lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2792_; 
lean_del_object(v___x_2583_);
v___x_2788_ = lean_nat_add(v___x_2728_, v_size_2729_);
v___x_2789_ = lean_nat_add(v___x_2788_, v_size_2730_);
lean_dec(v_size_2730_);
v___x_2790_ = lean_nat_add(v___x_2788_, v_size_2746_);
lean_dec(v___x_2788_);
lean_inc_ref(v_l_2580_);
if (v_isShared_2745_ == 0)
{
lean_ctor_set(v___x_2744_, 4, v_l_2733_);
lean_ctor_set(v___x_2744_, 3, v_l_2580_);
lean_ctor_set(v___x_2744_, 2, v_v_2579_);
lean_ctor_set(v___x_2744_, 1, v_k_2578_);
lean_ctor_set(v___x_2744_, 0, v___x_2790_);
v___x_2792_ = v___x_2744_;
goto v_reusejp_2791_;
}
else
{
lean_object* v_reuseFailAlloc_2805_; 
v_reuseFailAlloc_2805_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2805_, 0, v___x_2790_);
lean_ctor_set(v_reuseFailAlloc_2805_, 1, v_k_2578_);
lean_ctor_set(v_reuseFailAlloc_2805_, 2, v_v_2579_);
lean_ctor_set(v_reuseFailAlloc_2805_, 3, v_l_2580_);
lean_ctor_set(v_reuseFailAlloc_2805_, 4, v_l_2733_);
v___x_2792_ = v_reuseFailAlloc_2805_;
goto v_reusejp_2791_;
}
v_reusejp_2791_:
{
lean_object* v___x_2794_; uint8_t v_isShared_2795_; uint8_t v_isSharedCheck_2799_; 
v_isSharedCheck_2799_ = !lean_is_exclusive(v_l_2580_);
if (v_isSharedCheck_2799_ == 0)
{
lean_object* v_unused_2800_; lean_object* v_unused_2801_; lean_object* v_unused_2802_; lean_object* v_unused_2803_; lean_object* v_unused_2804_; 
v_unused_2800_ = lean_ctor_get(v_l_2580_, 4);
lean_dec(v_unused_2800_);
v_unused_2801_ = lean_ctor_get(v_l_2580_, 3);
lean_dec(v_unused_2801_);
v_unused_2802_ = lean_ctor_get(v_l_2580_, 2);
lean_dec(v_unused_2802_);
v_unused_2803_ = lean_ctor_get(v_l_2580_, 1);
lean_dec(v_unused_2803_);
v_unused_2804_ = lean_ctor_get(v_l_2580_, 0);
lean_dec(v_unused_2804_);
v___x_2794_ = v_l_2580_;
v_isShared_2795_ = v_isSharedCheck_2799_;
goto v_resetjp_2793_;
}
else
{
lean_dec(v_l_2580_);
v___x_2794_ = lean_box(0);
v_isShared_2795_ = v_isSharedCheck_2799_;
goto v_resetjp_2793_;
}
v_resetjp_2793_:
{
lean_object* v___x_2797_; 
if (v_isShared_2795_ == 0)
{
lean_ctor_set(v___x_2794_, 4, v_r_2734_);
lean_ctor_set(v___x_2794_, 3, v___x_2792_);
lean_ctor_set(v___x_2794_, 2, v_v_2732_);
lean_ctor_set(v___x_2794_, 1, v_k_2731_);
lean_ctor_set(v___x_2794_, 0, v___x_2789_);
v___x_2797_ = v___x_2794_;
goto v_reusejp_2796_;
}
else
{
lean_object* v_reuseFailAlloc_2798_; 
v_reuseFailAlloc_2798_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2798_, 0, v___x_2789_);
lean_ctor_set(v_reuseFailAlloc_2798_, 1, v_k_2731_);
lean_ctor_set(v_reuseFailAlloc_2798_, 2, v_v_2732_);
lean_ctor_set(v_reuseFailAlloc_2798_, 3, v___x_2792_);
lean_ctor_set(v_reuseFailAlloc_2798_, 4, v_r_2734_);
v___x_2797_ = v_reuseFailAlloc_2798_;
goto v_reusejp_2796_;
}
v_reusejp_2796_:
{
return v___x_2797_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2812_; 
v_l_2812_ = lean_ctor_get(v_impl_2727_, 3);
lean_inc(v_l_2812_);
if (lean_obj_tag(v_l_2812_) == 0)
{
lean_object* v_r_2813_; lean_object* v_k_2814_; lean_object* v_v_2815_; lean_object* v___x_2817_; uint8_t v_isShared_2818_; uint8_t v_isSharedCheck_2838_; 
v_r_2813_ = lean_ctor_get(v_impl_2727_, 4);
v_k_2814_ = lean_ctor_get(v_impl_2727_, 1);
v_v_2815_ = lean_ctor_get(v_impl_2727_, 2);
v_isSharedCheck_2838_ = !lean_is_exclusive(v_impl_2727_);
if (v_isSharedCheck_2838_ == 0)
{
lean_object* v_unused_2839_; lean_object* v_unused_2840_; 
v_unused_2839_ = lean_ctor_get(v_impl_2727_, 3);
lean_dec(v_unused_2839_);
v_unused_2840_ = lean_ctor_get(v_impl_2727_, 0);
lean_dec(v_unused_2840_);
v___x_2817_ = v_impl_2727_;
v_isShared_2818_ = v_isSharedCheck_2838_;
goto v_resetjp_2816_;
}
else
{
lean_inc(v_r_2813_);
lean_inc(v_v_2815_);
lean_inc(v_k_2814_);
lean_dec(v_impl_2727_);
v___x_2817_ = lean_box(0);
v_isShared_2818_ = v_isSharedCheck_2838_;
goto v_resetjp_2816_;
}
v_resetjp_2816_:
{
lean_object* v_k_2819_; lean_object* v_v_2820_; lean_object* v___x_2822_; uint8_t v_isShared_2823_; uint8_t v_isSharedCheck_2834_; 
v_k_2819_ = lean_ctor_get(v_l_2812_, 1);
v_v_2820_ = lean_ctor_get(v_l_2812_, 2);
v_isSharedCheck_2834_ = !lean_is_exclusive(v_l_2812_);
if (v_isSharedCheck_2834_ == 0)
{
lean_object* v_unused_2835_; lean_object* v_unused_2836_; lean_object* v_unused_2837_; 
v_unused_2835_ = lean_ctor_get(v_l_2812_, 4);
lean_dec(v_unused_2835_);
v_unused_2836_ = lean_ctor_get(v_l_2812_, 3);
lean_dec(v_unused_2836_);
v_unused_2837_ = lean_ctor_get(v_l_2812_, 0);
lean_dec(v_unused_2837_);
v___x_2822_ = v_l_2812_;
v_isShared_2823_ = v_isSharedCheck_2834_;
goto v_resetjp_2821_;
}
else
{
lean_inc(v_v_2820_);
lean_inc(v_k_2819_);
lean_dec(v_l_2812_);
v___x_2822_ = lean_box(0);
v_isShared_2823_ = v_isSharedCheck_2834_;
goto v_resetjp_2821_;
}
v_resetjp_2821_:
{
lean_object* v___x_2824_; lean_object* v___x_2826_; 
v___x_2824_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_2813_, 2);
if (v_isShared_2823_ == 0)
{
lean_ctor_set(v___x_2822_, 4, v_r_2813_);
lean_ctor_set(v___x_2822_, 3, v_r_2813_);
lean_ctor_set(v___x_2822_, 2, v_v_2579_);
lean_ctor_set(v___x_2822_, 1, v_k_2578_);
lean_ctor_set(v___x_2822_, 0, v___x_2728_);
v___x_2826_ = v___x_2822_;
goto v_reusejp_2825_;
}
else
{
lean_object* v_reuseFailAlloc_2833_; 
v_reuseFailAlloc_2833_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2833_, 0, v___x_2728_);
lean_ctor_set(v_reuseFailAlloc_2833_, 1, v_k_2578_);
lean_ctor_set(v_reuseFailAlloc_2833_, 2, v_v_2579_);
lean_ctor_set(v_reuseFailAlloc_2833_, 3, v_r_2813_);
lean_ctor_set(v_reuseFailAlloc_2833_, 4, v_r_2813_);
v___x_2826_ = v_reuseFailAlloc_2833_;
goto v_reusejp_2825_;
}
v_reusejp_2825_:
{
lean_object* v___x_2828_; 
lean_inc(v_r_2813_);
if (v_isShared_2818_ == 0)
{
lean_ctor_set(v___x_2817_, 3, v_r_2813_);
lean_ctor_set(v___x_2817_, 0, v___x_2728_);
v___x_2828_ = v___x_2817_;
goto v_reusejp_2827_;
}
else
{
lean_object* v_reuseFailAlloc_2832_; 
v_reuseFailAlloc_2832_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2832_, 0, v___x_2728_);
lean_ctor_set(v_reuseFailAlloc_2832_, 1, v_k_2814_);
lean_ctor_set(v_reuseFailAlloc_2832_, 2, v_v_2815_);
lean_ctor_set(v_reuseFailAlloc_2832_, 3, v_r_2813_);
lean_ctor_set(v_reuseFailAlloc_2832_, 4, v_r_2813_);
v___x_2828_ = v_reuseFailAlloc_2832_;
goto v_reusejp_2827_;
}
v_reusejp_2827_:
{
lean_object* v___x_2830_; 
if (v_isShared_2584_ == 0)
{
lean_ctor_set(v___x_2583_, 4, v___x_2828_);
lean_ctor_set(v___x_2583_, 3, v___x_2826_);
lean_ctor_set(v___x_2583_, 2, v_v_2820_);
lean_ctor_set(v___x_2583_, 1, v_k_2819_);
lean_ctor_set(v___x_2583_, 0, v___x_2824_);
v___x_2830_ = v___x_2583_;
goto v_reusejp_2829_;
}
else
{
lean_object* v_reuseFailAlloc_2831_; 
v_reuseFailAlloc_2831_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2831_, 0, v___x_2824_);
lean_ctor_set(v_reuseFailAlloc_2831_, 1, v_k_2819_);
lean_ctor_set(v_reuseFailAlloc_2831_, 2, v_v_2820_);
lean_ctor_set(v_reuseFailAlloc_2831_, 3, v___x_2826_);
lean_ctor_set(v_reuseFailAlloc_2831_, 4, v___x_2828_);
v___x_2830_ = v_reuseFailAlloc_2831_;
goto v_reusejp_2829_;
}
v_reusejp_2829_:
{
return v___x_2830_;
}
}
}
}
}
}
else
{
lean_object* v_r_2841_; 
v_r_2841_ = lean_ctor_get(v_impl_2727_, 4);
lean_inc(v_r_2841_);
if (lean_obj_tag(v_r_2841_) == 0)
{
lean_object* v_k_2842_; lean_object* v_v_2843_; lean_object* v___x_2845_; uint8_t v_isShared_2846_; uint8_t v_isSharedCheck_2854_; 
v_k_2842_ = lean_ctor_get(v_impl_2727_, 1);
v_v_2843_ = lean_ctor_get(v_impl_2727_, 2);
v_isSharedCheck_2854_ = !lean_is_exclusive(v_impl_2727_);
if (v_isSharedCheck_2854_ == 0)
{
lean_object* v_unused_2855_; lean_object* v_unused_2856_; lean_object* v_unused_2857_; 
v_unused_2855_ = lean_ctor_get(v_impl_2727_, 4);
lean_dec(v_unused_2855_);
v_unused_2856_ = lean_ctor_get(v_impl_2727_, 3);
lean_dec(v_unused_2856_);
v_unused_2857_ = lean_ctor_get(v_impl_2727_, 0);
lean_dec(v_unused_2857_);
v___x_2845_ = v_impl_2727_;
v_isShared_2846_ = v_isSharedCheck_2854_;
goto v_resetjp_2844_;
}
else
{
lean_inc(v_v_2843_);
lean_inc(v_k_2842_);
lean_dec(v_impl_2727_);
v___x_2845_ = lean_box(0);
v_isShared_2846_ = v_isSharedCheck_2854_;
goto v_resetjp_2844_;
}
v_resetjp_2844_:
{
lean_object* v___x_2847_; lean_object* v___x_2849_; 
v___x_2847_ = lean_unsigned_to_nat(3u);
if (v_isShared_2846_ == 0)
{
lean_ctor_set(v___x_2845_, 4, v_l_2812_);
lean_ctor_set(v___x_2845_, 2, v_v_2579_);
lean_ctor_set(v___x_2845_, 1, v_k_2578_);
lean_ctor_set(v___x_2845_, 0, v___x_2728_);
v___x_2849_ = v___x_2845_;
goto v_reusejp_2848_;
}
else
{
lean_object* v_reuseFailAlloc_2853_; 
v_reuseFailAlloc_2853_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2853_, 0, v___x_2728_);
lean_ctor_set(v_reuseFailAlloc_2853_, 1, v_k_2578_);
lean_ctor_set(v_reuseFailAlloc_2853_, 2, v_v_2579_);
lean_ctor_set(v_reuseFailAlloc_2853_, 3, v_l_2812_);
lean_ctor_set(v_reuseFailAlloc_2853_, 4, v_l_2812_);
v___x_2849_ = v_reuseFailAlloc_2853_;
goto v_reusejp_2848_;
}
v_reusejp_2848_:
{
lean_object* v___x_2851_; 
if (v_isShared_2584_ == 0)
{
lean_ctor_set(v___x_2583_, 4, v_r_2841_);
lean_ctor_set(v___x_2583_, 3, v___x_2849_);
lean_ctor_set(v___x_2583_, 2, v_v_2843_);
lean_ctor_set(v___x_2583_, 1, v_k_2842_);
lean_ctor_set(v___x_2583_, 0, v___x_2847_);
v___x_2851_ = v___x_2583_;
goto v_reusejp_2850_;
}
else
{
lean_object* v_reuseFailAlloc_2852_; 
v_reuseFailAlloc_2852_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2852_, 0, v___x_2847_);
lean_ctor_set(v_reuseFailAlloc_2852_, 1, v_k_2842_);
lean_ctor_set(v_reuseFailAlloc_2852_, 2, v_v_2843_);
lean_ctor_set(v_reuseFailAlloc_2852_, 3, v___x_2849_);
lean_ctor_set(v_reuseFailAlloc_2852_, 4, v_r_2841_);
v___x_2851_ = v_reuseFailAlloc_2852_;
goto v_reusejp_2850_;
}
v_reusejp_2850_:
{
return v___x_2851_;
}
}
}
}
else
{
lean_object* v___x_2858_; lean_object* v___x_2860_; 
v___x_2858_ = lean_unsigned_to_nat(2u);
if (v_isShared_2584_ == 0)
{
lean_ctor_set(v___x_2583_, 4, v_impl_2727_);
lean_ctor_set(v___x_2583_, 3, v_r_2841_);
lean_ctor_set(v___x_2583_, 0, v___x_2858_);
v___x_2860_ = v___x_2583_;
goto v_reusejp_2859_;
}
else
{
lean_object* v_reuseFailAlloc_2861_; 
v_reuseFailAlloc_2861_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2861_, 0, v___x_2858_);
lean_ctor_set(v_reuseFailAlloc_2861_, 1, v_k_2578_);
lean_ctor_set(v_reuseFailAlloc_2861_, 2, v_v_2579_);
lean_ctor_set(v_reuseFailAlloc_2861_, 3, v_r_2841_);
lean_ctor_set(v_reuseFailAlloc_2861_, 4, v_impl_2727_);
v___x_2860_ = v_reuseFailAlloc_2861_;
goto v_reusejp_2859_;
}
v_reusejp_2859_:
{
return v___x_2860_;
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
lean_object* v___x_2863_; lean_object* v___x_2864_; 
lean_dec_ref(v_cmp_2573_);
v___x_2863_ = lean_unsigned_to_nat(1u);
v___x_2864_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2864_, 0, v___x_2863_);
lean_ctor_set(v___x_2864_, 1, v_k_2574_);
lean_ctor_set(v___x_2864_, 2, v_v_2575_);
lean_ctor_set(v___x_2864_, 3, v_t_2576_);
lean_ctor_set(v___x_2864_, 4, v_t_2576_);
return v___x_2864_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__2_spec__4_spec__7_spec__11(lean_object* v_cmp_2865_, lean_object* v_init_2866_, lean_object* v_x_2867_){
_start:
{
if (lean_obj_tag(v_x_2867_) == 0)
{
lean_object* v_k_2868_; lean_object* v_v_2869_; lean_object* v_l_2870_; lean_object* v_r_2871_; lean_object* v___x_2872_; 
v_k_2868_ = lean_ctor_get(v_x_2867_, 1);
lean_inc(v_k_2868_);
v_v_2869_ = lean_ctor_get(v_x_2867_, 2);
lean_inc(v_v_2869_);
v_l_2870_ = lean_ctor_get(v_x_2867_, 3);
lean_inc(v_l_2870_);
v_r_2871_ = lean_ctor_get(v_x_2867_, 4);
lean_inc(v_r_2871_);
lean_dec_ref(v_x_2867_);
lean_inc_ref(v_cmp_2865_);
v___x_2872_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__2_spec__4_spec__7_spec__11(v_cmp_2865_, v_init_2866_, v_l_2870_);
if (lean_obj_tag(v___x_2872_) == 0)
{
lean_dec(v_r_2871_);
lean_dec(v_v_2869_);
lean_dec(v_k_2868_);
lean_dec_ref(v_cmp_2865_);
return v___x_2872_;
}
else
{
lean_object* v_a_2873_; lean_object* v___x_2874_; 
v_a_2873_ = lean_ctor_get(v___x_2872_, 0);
lean_inc(v_a_2873_);
lean_dec_ref(v___x_2872_);
v___x_2874_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentEdit_fromJson_spec__1_spec__1(v_v_2869_);
if (lean_obj_tag(v___x_2874_) == 0)
{
lean_object* v_a_2875_; lean_object* v___x_2877_; uint8_t v_isShared_2878_; uint8_t v_isSharedCheck_2882_; 
lean_dec(v_a_2873_);
lean_dec(v_r_2871_);
lean_dec(v_k_2868_);
lean_dec_ref(v_cmp_2865_);
v_a_2875_ = lean_ctor_get(v___x_2874_, 0);
v_isSharedCheck_2882_ = !lean_is_exclusive(v___x_2874_);
if (v_isSharedCheck_2882_ == 0)
{
v___x_2877_ = v___x_2874_;
v_isShared_2878_ = v_isSharedCheck_2882_;
goto v_resetjp_2876_;
}
else
{
lean_inc(v_a_2875_);
lean_dec(v___x_2874_);
v___x_2877_ = lean_box(0);
v_isShared_2878_ = v_isSharedCheck_2882_;
goto v_resetjp_2876_;
}
v_resetjp_2876_:
{
lean_object* v___x_2880_; 
if (v_isShared_2878_ == 0)
{
v___x_2880_ = v___x_2877_;
goto v_reusejp_2879_;
}
else
{
lean_object* v_reuseFailAlloc_2881_; 
v_reuseFailAlloc_2881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2881_, 0, v_a_2875_);
v___x_2880_ = v_reuseFailAlloc_2881_;
goto v_reusejp_2879_;
}
v_reusejp_2879_:
{
return v___x_2880_;
}
}
}
else
{
lean_object* v_a_2883_; lean_object* v___x_2884_; 
v_a_2883_ = lean_ctor_get(v___x_2874_, 0);
lean_inc(v_a_2883_);
lean_dec_ref(v___x_2874_);
lean_inc_ref(v_cmp_2865_);
v___x_2884_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__1_spec__2_spec__4_spec__7___redArg(v_cmp_2865_, v_k_2868_, v_a_2883_, v_a_2873_);
v_init_2866_ = v___x_2884_;
v_x_2867_ = v_r_2871_;
goto _start;
}
}
}
else
{
lean_object* v___x_2886_; 
lean_dec_ref(v_cmp_2865_);
v___x_2886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2886_, 0, v_init_2866_);
return v___x_2886_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__2_spec__4_spec__7(lean_object* v_cmp_2887_, lean_object* v_j_2888_){
_start:
{
lean_object* v___x_2889_; 
v___x_2889_ = l_Lean_Json_getObj_x3f(v_j_2888_);
if (lean_obj_tag(v___x_2889_) == 0)
{
lean_object* v_a_2890_; lean_object* v___x_2892_; uint8_t v_isShared_2893_; uint8_t v_isSharedCheck_2897_; 
lean_dec_ref(v_cmp_2887_);
v_a_2890_ = lean_ctor_get(v___x_2889_, 0);
v_isSharedCheck_2897_ = !lean_is_exclusive(v___x_2889_);
if (v_isSharedCheck_2897_ == 0)
{
v___x_2892_ = v___x_2889_;
v_isShared_2893_ = v_isSharedCheck_2897_;
goto v_resetjp_2891_;
}
else
{
lean_inc(v_a_2890_);
lean_dec(v___x_2889_);
v___x_2892_ = lean_box(0);
v_isShared_2893_ = v_isSharedCheck_2897_;
goto v_resetjp_2891_;
}
v_resetjp_2891_:
{
lean_object* v___x_2895_; 
if (v_isShared_2893_ == 0)
{
v___x_2895_ = v___x_2892_;
goto v_reusejp_2894_;
}
else
{
lean_object* v_reuseFailAlloc_2896_; 
v_reuseFailAlloc_2896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2896_, 0, v_a_2890_);
v___x_2895_ = v_reuseFailAlloc_2896_;
goto v_reusejp_2894_;
}
v_reusejp_2894_:
{
return v___x_2895_;
}
}
}
else
{
lean_object* v_a_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; 
v_a_2898_ = lean_ctor_get(v___x_2889_, 0);
lean_inc(v_a_2898_);
lean_dec_ref(v___x_2889_);
v___x_2899_ = lean_box(1);
v___x_2900_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__2_spec__4_spec__7_spec__11(v_cmp_2887_, v___x_2899_, v_a_2898_);
return v___x_2900_;
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__2_spec__4(lean_object* v_x_2904_){
_start:
{
if (lean_obj_tag(v_x_2904_) == 0)
{
lean_object* v___x_2905_; 
v___x_2905_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__2_spec__4___closed__0));
return v___x_2905_;
}
else
{
lean_object* v___f_2906_; lean_object* v___x_2907_; 
v___f_2906_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__2_spec__4___closed__1));
v___x_2907_ = l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__2_spec__4_spec__7(v___f_2906_, v_x_2904_);
if (lean_obj_tag(v___x_2907_) == 0)
{
lean_object* v_a_2908_; lean_object* v___x_2910_; uint8_t v_isShared_2911_; uint8_t v_isSharedCheck_2915_; 
v_a_2908_ = lean_ctor_get(v___x_2907_, 0);
v_isSharedCheck_2915_ = !lean_is_exclusive(v___x_2907_);
if (v_isSharedCheck_2915_ == 0)
{
v___x_2910_ = v___x_2907_;
v_isShared_2911_ = v_isSharedCheck_2915_;
goto v_resetjp_2909_;
}
else
{
lean_inc(v_a_2908_);
lean_dec(v___x_2907_);
v___x_2910_ = lean_box(0);
v_isShared_2911_ = v_isSharedCheck_2915_;
goto v_resetjp_2909_;
}
v_resetjp_2909_:
{
lean_object* v___x_2913_; 
if (v_isShared_2911_ == 0)
{
v___x_2913_ = v___x_2910_;
goto v_reusejp_2912_;
}
else
{
lean_object* v_reuseFailAlloc_2914_; 
v_reuseFailAlloc_2914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2914_, 0, v_a_2908_);
v___x_2913_ = v_reuseFailAlloc_2914_;
goto v_reusejp_2912_;
}
v_reusejp_2912_:
{
return v___x_2913_;
}
}
}
else
{
lean_object* v_a_2916_; lean_object* v___x_2918_; uint8_t v_isShared_2919_; uint8_t v_isSharedCheck_2924_; 
v_a_2916_ = lean_ctor_get(v___x_2907_, 0);
v_isSharedCheck_2924_ = !lean_is_exclusive(v___x_2907_);
if (v_isSharedCheck_2924_ == 0)
{
v___x_2918_ = v___x_2907_;
v_isShared_2919_ = v_isSharedCheck_2924_;
goto v_resetjp_2917_;
}
else
{
lean_inc(v_a_2916_);
lean_dec(v___x_2907_);
v___x_2918_ = lean_box(0);
v_isShared_2919_ = v_isSharedCheck_2924_;
goto v_resetjp_2917_;
}
v_resetjp_2917_:
{
lean_object* v___x_2920_; lean_object* v___x_2922_; 
v___x_2920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2920_, 0, v_a_2916_);
if (v_isShared_2919_ == 0)
{
lean_ctor_set(v___x_2918_, 0, v___x_2920_);
v___x_2922_ = v___x_2918_;
goto v_reusejp_2921_;
}
else
{
lean_object* v_reuseFailAlloc_2923_; 
v_reuseFailAlloc_2923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2923_, 0, v___x_2920_);
v___x_2922_ = v_reuseFailAlloc_2923_;
goto v_reusejp_2921_;
}
v_reusejp_2921_:
{
return v___x_2922_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__2(lean_object* v_j_2925_, lean_object* v_k_2926_){
_start:
{
lean_object* v___x_2927_; lean_object* v___x_2928_; 
v___x_2927_ = l_Lean_Json_getObjValD(v_j_2925_, v_k_2926_);
v___x_2928_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__2_spec__4(v___x_2927_);
return v___x_2928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__2___boxed(lean_object* v_j_2929_, lean_object* v_k_2930_){
_start:
{
lean_object* v_res_2931_; 
v_res_2931_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__2(v_j_2929_, v_k_2930_);
lean_dec_ref(v_k_2930_);
return v_res_2931_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__1_spec__2_spec__4_spec__8(lean_object* v_cmp_2932_, lean_object* v_init_2933_, lean_object* v_x_2934_){
_start:
{
if (lean_obj_tag(v_x_2934_) == 0)
{
lean_object* v_k_2935_; lean_object* v_v_2936_; lean_object* v_l_2937_; lean_object* v_r_2938_; lean_object* v___x_2939_; 
v_k_2935_ = lean_ctor_get(v_x_2934_, 1);
lean_inc(v_k_2935_);
v_v_2936_ = lean_ctor_get(v_x_2934_, 2);
lean_inc(v_v_2936_);
v_l_2937_ = lean_ctor_get(v_x_2934_, 3);
lean_inc(v_l_2937_);
v_r_2938_ = lean_ctor_get(v_x_2934_, 4);
lean_inc(v_r_2938_);
lean_dec_ref(v_x_2934_);
lean_inc_ref(v_cmp_2932_);
v___x_2939_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__1_spec__2_spec__4_spec__8(v_cmp_2932_, v_init_2933_, v_l_2937_);
if (lean_obj_tag(v___x_2939_) == 0)
{
lean_dec(v_r_2938_);
lean_dec(v_v_2936_);
lean_dec(v_k_2935_);
lean_dec_ref(v_cmp_2932_);
return v___x_2939_;
}
else
{
lean_object* v_a_2940_; lean_object* v___x_2941_; 
v_a_2940_ = lean_ctor_get(v___x_2939_, 0);
lean_inc(v_a_2940_);
lean_dec_ref(v___x_2939_);
v___x_2941_ = l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson(v_v_2936_);
if (lean_obj_tag(v___x_2941_) == 0)
{
lean_object* v_a_2942_; lean_object* v___x_2944_; uint8_t v_isShared_2945_; uint8_t v_isSharedCheck_2949_; 
lean_dec(v_a_2940_);
lean_dec(v_r_2938_);
lean_dec(v_k_2935_);
lean_dec_ref(v_cmp_2932_);
v_a_2942_ = lean_ctor_get(v___x_2941_, 0);
v_isSharedCheck_2949_ = !lean_is_exclusive(v___x_2941_);
if (v_isSharedCheck_2949_ == 0)
{
v___x_2944_ = v___x_2941_;
v_isShared_2945_ = v_isSharedCheck_2949_;
goto v_resetjp_2943_;
}
else
{
lean_inc(v_a_2942_);
lean_dec(v___x_2941_);
v___x_2944_ = lean_box(0);
v_isShared_2945_ = v_isSharedCheck_2949_;
goto v_resetjp_2943_;
}
v_resetjp_2943_:
{
lean_object* v___x_2947_; 
if (v_isShared_2945_ == 0)
{
v___x_2947_ = v___x_2944_;
goto v_reusejp_2946_;
}
else
{
lean_object* v_reuseFailAlloc_2948_; 
v_reuseFailAlloc_2948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2948_, 0, v_a_2942_);
v___x_2947_ = v_reuseFailAlloc_2948_;
goto v_reusejp_2946_;
}
v_reusejp_2946_:
{
return v___x_2947_;
}
}
}
else
{
lean_object* v_a_2950_; lean_object* v___x_2951_; 
v_a_2950_ = lean_ctor_get(v___x_2941_, 0);
lean_inc(v_a_2950_);
lean_dec_ref(v___x_2941_);
lean_inc_ref(v_cmp_2932_);
v___x_2951_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__1_spec__2_spec__4_spec__7___redArg(v_cmp_2932_, v_k_2935_, v_a_2950_, v_a_2940_);
v_init_2933_ = v___x_2951_;
v_x_2934_ = v_r_2938_;
goto _start;
}
}
}
else
{
lean_object* v___x_2953_; 
lean_dec_ref(v_cmp_2932_);
v___x_2953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2953_, 0, v_init_2933_);
return v___x_2953_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__1_spec__2_spec__4(lean_object* v_cmp_2954_, lean_object* v_j_2955_){
_start:
{
lean_object* v___x_2956_; 
v___x_2956_ = l_Lean_Json_getObj_x3f(v_j_2955_);
if (lean_obj_tag(v___x_2956_) == 0)
{
lean_object* v_a_2957_; lean_object* v___x_2959_; uint8_t v_isShared_2960_; uint8_t v_isSharedCheck_2964_; 
lean_dec_ref(v_cmp_2954_);
v_a_2957_ = lean_ctor_get(v___x_2956_, 0);
v_isSharedCheck_2964_ = !lean_is_exclusive(v___x_2956_);
if (v_isSharedCheck_2964_ == 0)
{
v___x_2959_ = v___x_2956_;
v_isShared_2960_ = v_isSharedCheck_2964_;
goto v_resetjp_2958_;
}
else
{
lean_inc(v_a_2957_);
lean_dec(v___x_2956_);
v___x_2959_ = lean_box(0);
v_isShared_2960_ = v_isSharedCheck_2964_;
goto v_resetjp_2958_;
}
v_resetjp_2958_:
{
lean_object* v___x_2962_; 
if (v_isShared_2960_ == 0)
{
v___x_2962_ = v___x_2959_;
goto v_reusejp_2961_;
}
else
{
lean_object* v_reuseFailAlloc_2963_; 
v_reuseFailAlloc_2963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2963_, 0, v_a_2957_);
v___x_2962_ = v_reuseFailAlloc_2963_;
goto v_reusejp_2961_;
}
v_reusejp_2961_:
{
return v___x_2962_;
}
}
}
else
{
lean_object* v_a_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; 
v_a_2965_ = lean_ctor_get(v___x_2956_, 0);
lean_inc(v_a_2965_);
lean_dec_ref(v___x_2956_);
v___x_2966_ = lean_box(1);
v___x_2967_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__1_spec__2_spec__4_spec__8(v_cmp_2954_, v___x_2966_, v_a_2965_);
return v___x_2967_;
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__1_spec__2(lean_object* v_x_2968_){
_start:
{
if (lean_obj_tag(v_x_2968_) == 0)
{
lean_object* v___x_2969_; 
v___x_2969_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__2_spec__4___closed__0));
return v___x_2969_;
}
else
{
lean_object* v___f_2970_; lean_object* v___x_2971_; 
v___f_2970_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__2_spec__4___closed__1));
v___x_2971_ = l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__1_spec__2_spec__4(v___f_2970_, v_x_2968_);
if (lean_obj_tag(v___x_2971_) == 0)
{
lean_object* v_a_2972_; lean_object* v___x_2974_; uint8_t v_isShared_2975_; uint8_t v_isSharedCheck_2979_; 
v_a_2972_ = lean_ctor_get(v___x_2971_, 0);
v_isSharedCheck_2979_ = !lean_is_exclusive(v___x_2971_);
if (v_isSharedCheck_2979_ == 0)
{
v___x_2974_ = v___x_2971_;
v_isShared_2975_ = v_isSharedCheck_2979_;
goto v_resetjp_2973_;
}
else
{
lean_inc(v_a_2972_);
lean_dec(v___x_2971_);
v___x_2974_ = lean_box(0);
v_isShared_2975_ = v_isSharedCheck_2979_;
goto v_resetjp_2973_;
}
v_resetjp_2973_:
{
lean_object* v___x_2977_; 
if (v_isShared_2975_ == 0)
{
v___x_2977_ = v___x_2974_;
goto v_reusejp_2976_;
}
else
{
lean_object* v_reuseFailAlloc_2978_; 
v_reuseFailAlloc_2978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2978_, 0, v_a_2972_);
v___x_2977_ = v_reuseFailAlloc_2978_;
goto v_reusejp_2976_;
}
v_reusejp_2976_:
{
return v___x_2977_;
}
}
}
else
{
lean_object* v_a_2980_; lean_object* v___x_2982_; uint8_t v_isShared_2983_; uint8_t v_isSharedCheck_2988_; 
v_a_2980_ = lean_ctor_get(v___x_2971_, 0);
v_isSharedCheck_2988_ = !lean_is_exclusive(v___x_2971_);
if (v_isSharedCheck_2988_ == 0)
{
v___x_2982_ = v___x_2971_;
v_isShared_2983_ = v_isSharedCheck_2988_;
goto v_resetjp_2981_;
}
else
{
lean_inc(v_a_2980_);
lean_dec(v___x_2971_);
v___x_2982_ = lean_box(0);
v_isShared_2983_ = v_isSharedCheck_2988_;
goto v_resetjp_2981_;
}
v_resetjp_2981_:
{
lean_object* v___x_2984_; lean_object* v___x_2986_; 
v___x_2984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2984_, 0, v_a_2980_);
if (v_isShared_2983_ == 0)
{
lean_ctor_set(v___x_2982_, 0, v___x_2984_);
v___x_2986_ = v___x_2982_;
goto v_reusejp_2985_;
}
else
{
lean_object* v_reuseFailAlloc_2987_; 
v_reuseFailAlloc_2987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2987_, 0, v___x_2984_);
v___x_2986_ = v_reuseFailAlloc_2987_;
goto v_reusejp_2985_;
}
v_reusejp_2985_:
{
return v___x_2986_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__1(lean_object* v_j_2989_, lean_object* v_k_2990_){
_start:
{
lean_object* v___x_2991_; lean_object* v___x_2992_; 
v___x_2991_ = l_Lean_Json_getObjValD(v_j_2989_, v_k_2990_);
v___x_2992_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__1_spec__2(v___x_2991_);
return v___x_2992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__1___boxed(lean_object* v_j_2993_, lean_object* v_k_2994_){
_start:
{
lean_object* v_res_2995_; 
v_res_2995_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__1(v_j_2993_, v_k_2994_);
lean_dec_ref(v_k_2994_);
return v_res_2995_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__0_spec__0_spec__1_spec__4___lam__0(lean_object* v_kind_2996_){
_start:
{
lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; 
v___x_2997_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDocumentChange___lam__0___closed__0));
v___x_2998_ = lean_unsigned_to_nat(80u);
v___x_2999_ = l_Lean_Json_pretty(v_kind_2996_, v___x_2998_);
v___x_3000_ = lean_string_append(v___x_2997_, v___x_2999_);
lean_dec_ref(v___x_2999_);
v___x_3001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3001_, 0, v___x_3000_);
return v___x_3001_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__0_spec__0_spec__1_spec__4(size_t v_sz_3002_, size_t v_i_3003_, lean_object* v_bs_3004_){
_start:
{
uint8_t v___x_3005_; 
v___x_3005_ = lean_usize_dec_lt(v_i_3003_, v_sz_3002_);
if (v___x_3005_ == 0)
{
lean_object* v___x_3006_; 
v___x_3006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3006_, 0, v_bs_3004_);
return v___x_3006_;
}
else
{
lean_object* v_v_3007_; lean_object* v___x_3008_; lean_object* v_bs_x27_3009_; lean_object* v_a_3011_; lean_object* v___y_3029_; lean_object* v___x_3031_; lean_object* v___x_3032_; 
v_v_3007_ = lean_array_uget(v_bs_3004_, v_i_3003_);
v___x_3008_ = lean_unsigned_to_nat(0u);
v_bs_x27_3009_ = lean_array_uset(v_bs_3004_, v_i_3003_, v___x_3008_);
v___x_3031_ = ((lean_object*)(l_Lean_Lsp_instToJsonDocumentChange___lam__0___closed__0));
lean_inc(v_v_3007_);
v___x_3032_ = l_Lean_Json_getObjVal_x3f(v_v_3007_, v___x_3031_);
if (lean_obj_tag(v___x_3032_) == 0)
{
lean_dec_ref(v___x_3032_);
goto v___jp_3016_;
}
else
{
lean_object* v_a_3033_; 
v_a_3033_ = lean_ctor_get(v___x_3032_, 0);
lean_inc(v_a_3033_);
lean_dec_ref(v___x_3032_);
if (lean_obj_tag(v_a_3033_) == 3)
{
lean_object* v_s_3034_; lean_object* v___x_3035_; uint8_t v___x_3036_; 
v_s_3034_ = lean_ctor_get(v_a_3033_, 0);
v___x_3035_ = ((lean_object*)(l_Lean_Lsp_instToJsonDocumentChange___lam__0___closed__1));
v___x_3036_ = lean_string_dec_eq(v_s_3034_, v___x_3035_);
if (v___x_3036_ == 0)
{
lean_object* v___x_3037_; uint8_t v___x_3038_; 
v___x_3037_ = ((lean_object*)(l_Lean_Lsp_instToJsonDocumentChange___lam__0___closed__3));
v___x_3038_ = lean_string_dec_eq(v_s_3034_, v___x_3037_);
if (v___x_3038_ == 0)
{
lean_object* v___x_3039_; uint8_t v___x_3040_; 
v___x_3039_ = ((lean_object*)(l_Lean_Lsp_instToJsonDocumentChange___lam__0___closed__5));
v___x_3040_ = lean_string_dec_eq(v_s_3034_, v___x_3039_);
if (v___x_3040_ == 0)
{
lean_object* v___x_3041_; 
v___x_3041_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__0_spec__0_spec__1_spec__4___lam__0(v_a_3033_);
v___y_3029_ = v___x_3041_;
goto v___jp_3028_;
}
else
{
lean_object* v___x_3042_; 
lean_dec_ref(v_a_3033_);
lean_inc(v_v_3007_);
v___x_3042_ = l_Lean_Lsp_instFromJsonDeleteFile_fromJson(v_v_3007_);
if (lean_obj_tag(v___x_3042_) == 0)
{
lean_dec_ref(v___x_3042_);
goto v___jp_3016_;
}
else
{
lean_object* v_a_3043_; lean_object* v___x_3045_; uint8_t v_isShared_3046_; uint8_t v_isSharedCheck_3050_; 
lean_dec(v_v_3007_);
v_a_3043_ = lean_ctor_get(v___x_3042_, 0);
v_isSharedCheck_3050_ = !lean_is_exclusive(v___x_3042_);
if (v_isSharedCheck_3050_ == 0)
{
v___x_3045_ = v___x_3042_;
v_isShared_3046_ = v_isSharedCheck_3050_;
goto v_resetjp_3044_;
}
else
{
lean_inc(v_a_3043_);
lean_dec(v___x_3042_);
v___x_3045_ = lean_box(0);
v_isShared_3046_ = v_isSharedCheck_3050_;
goto v_resetjp_3044_;
}
v_resetjp_3044_:
{
lean_object* v___x_3048_; 
if (v_isShared_3046_ == 0)
{
lean_ctor_set_tag(v___x_3045_, 2);
v___x_3048_ = v___x_3045_;
goto v_reusejp_3047_;
}
else
{
lean_object* v_reuseFailAlloc_3049_; 
v_reuseFailAlloc_3049_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3049_, 0, v_a_3043_);
v___x_3048_ = v_reuseFailAlloc_3049_;
goto v_reusejp_3047_;
}
v_reusejp_3047_:
{
v_a_3011_ = v___x_3048_;
goto v___jp_3010_;
}
}
}
}
}
else
{
lean_object* v___x_3051_; 
lean_dec_ref(v_a_3033_);
lean_inc(v_v_3007_);
v___x_3051_ = l_Lean_Lsp_instFromJsonRenameFile_fromJson(v_v_3007_);
if (lean_obj_tag(v___x_3051_) == 0)
{
lean_dec_ref(v___x_3051_);
goto v___jp_3016_;
}
else
{
lean_object* v_a_3052_; lean_object* v___x_3054_; uint8_t v_isShared_3055_; uint8_t v_isSharedCheck_3059_; 
lean_dec(v_v_3007_);
v_a_3052_ = lean_ctor_get(v___x_3051_, 0);
v_isSharedCheck_3059_ = !lean_is_exclusive(v___x_3051_);
if (v_isSharedCheck_3059_ == 0)
{
v___x_3054_ = v___x_3051_;
v_isShared_3055_ = v_isSharedCheck_3059_;
goto v_resetjp_3053_;
}
else
{
lean_inc(v_a_3052_);
lean_dec(v___x_3051_);
v___x_3054_ = lean_box(0);
v_isShared_3055_ = v_isSharedCheck_3059_;
goto v_resetjp_3053_;
}
v_resetjp_3053_:
{
lean_object* v___x_3057_; 
if (v_isShared_3055_ == 0)
{
v___x_3057_ = v___x_3054_;
goto v_reusejp_3056_;
}
else
{
lean_object* v_reuseFailAlloc_3058_; 
v_reuseFailAlloc_3058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3058_, 0, v_a_3052_);
v___x_3057_ = v_reuseFailAlloc_3058_;
goto v_reusejp_3056_;
}
v_reusejp_3056_:
{
v_a_3011_ = v___x_3057_;
goto v___jp_3010_;
}
}
}
}
}
else
{
lean_object* v___x_3060_; 
lean_dec_ref(v_a_3033_);
lean_inc(v_v_3007_);
v___x_3060_ = l_Lean_Lsp_instFromJsonCreateFile_fromJson(v_v_3007_);
if (lean_obj_tag(v___x_3060_) == 0)
{
lean_dec_ref(v___x_3060_);
goto v___jp_3016_;
}
else
{
lean_object* v_a_3061_; lean_object* v___x_3063_; uint8_t v_isShared_3064_; uint8_t v_isSharedCheck_3068_; 
lean_dec(v_v_3007_);
v_a_3061_ = lean_ctor_get(v___x_3060_, 0);
v_isSharedCheck_3068_ = !lean_is_exclusive(v___x_3060_);
if (v_isSharedCheck_3068_ == 0)
{
v___x_3063_ = v___x_3060_;
v_isShared_3064_ = v_isSharedCheck_3068_;
goto v_resetjp_3062_;
}
else
{
lean_inc(v_a_3061_);
lean_dec(v___x_3060_);
v___x_3063_ = lean_box(0);
v_isShared_3064_ = v_isSharedCheck_3068_;
goto v_resetjp_3062_;
}
v_resetjp_3062_:
{
lean_object* v___x_3066_; 
if (v_isShared_3064_ == 0)
{
lean_ctor_set_tag(v___x_3063_, 0);
v___x_3066_ = v___x_3063_;
goto v_reusejp_3065_;
}
else
{
lean_object* v_reuseFailAlloc_3067_; 
v_reuseFailAlloc_3067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3067_, 0, v_a_3061_);
v___x_3066_ = v_reuseFailAlloc_3067_;
goto v_reusejp_3065_;
}
v_reusejp_3065_:
{
v_a_3011_ = v___x_3066_;
goto v___jp_3010_;
}
}
}
}
}
else
{
lean_object* v___x_3069_; 
v___x_3069_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__0_spec__0_spec__1_spec__4___lam__0(v_a_3033_);
v___y_3029_ = v___x_3069_;
goto v___jp_3028_;
}
}
v___jp_3010_:
{
size_t v___x_3012_; size_t v___x_3013_; lean_object* v___x_3014_; 
v___x_3012_ = ((size_t)1ULL);
v___x_3013_ = lean_usize_add(v_i_3003_, v___x_3012_);
v___x_3014_ = lean_array_uset(v_bs_x27_3009_, v_i_3003_, v_a_3011_);
v_i_3003_ = v___x_3013_;
v_bs_3004_ = v___x_3014_;
goto _start;
}
v___jp_3016_:
{
lean_object* v___x_3017_; 
v___x_3017_ = l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson(v_v_3007_);
if (lean_obj_tag(v___x_3017_) == 0)
{
lean_object* v_a_3018_; lean_object* v___x_3020_; uint8_t v_isShared_3021_; uint8_t v_isSharedCheck_3025_; 
lean_dec_ref(v_bs_x27_3009_);
v_a_3018_ = lean_ctor_get(v___x_3017_, 0);
v_isSharedCheck_3025_ = !lean_is_exclusive(v___x_3017_);
if (v_isSharedCheck_3025_ == 0)
{
v___x_3020_ = v___x_3017_;
v_isShared_3021_ = v_isSharedCheck_3025_;
goto v_resetjp_3019_;
}
else
{
lean_inc(v_a_3018_);
lean_dec(v___x_3017_);
v___x_3020_ = lean_box(0);
v_isShared_3021_ = v_isSharedCheck_3025_;
goto v_resetjp_3019_;
}
v_resetjp_3019_:
{
lean_object* v___x_3023_; 
if (v_isShared_3021_ == 0)
{
v___x_3023_ = v___x_3020_;
goto v_reusejp_3022_;
}
else
{
lean_object* v_reuseFailAlloc_3024_; 
v_reuseFailAlloc_3024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3024_, 0, v_a_3018_);
v___x_3023_ = v_reuseFailAlloc_3024_;
goto v_reusejp_3022_;
}
v_reusejp_3022_:
{
return v___x_3023_;
}
}
}
else
{
lean_object* v_a_3026_; lean_object* v___x_3027_; 
v_a_3026_ = lean_ctor_get(v___x_3017_, 0);
lean_inc(v_a_3026_);
lean_dec_ref(v___x_3017_);
v___x_3027_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3027_, 0, v_a_3026_);
v_a_3011_ = v___x_3027_;
goto v___jp_3010_;
}
}
v___jp_3028_:
{
if (lean_obj_tag(v___y_3029_) == 0)
{
lean_dec_ref(v___y_3029_);
goto v___jp_3016_;
}
else
{
lean_object* v_a_3030_; 
lean_dec(v_v_3007_);
v_a_3030_ = lean_ctor_get(v___y_3029_, 0);
lean_inc(v_a_3030_);
lean_dec_ref(v___y_3029_);
v_a_3011_ = v_a_3030_;
goto v___jp_3010_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_sz_3070_, lean_object* v_i_3071_, lean_object* v_bs_3072_){
_start:
{
size_t v_sz_boxed_3073_; size_t v_i_boxed_3074_; lean_object* v_res_3075_; 
v_sz_boxed_3073_ = lean_unbox_usize(v_sz_3070_);
lean_dec(v_sz_3070_);
v_i_boxed_3074_ = lean_unbox_usize(v_i_3071_);
lean_dec(v_i_3071_);
v_res_3075_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__0_spec__0_spec__1_spec__4(v_sz_boxed_3073_, v_i_boxed_3074_, v_bs_3072_);
return v_res_3075_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__0_spec__0_spec__1(lean_object* v_x_3076_){
_start:
{
if (lean_obj_tag(v_x_3076_) == 4)
{
lean_object* v_elems_3077_; size_t v_sz_3078_; size_t v___x_3079_; lean_object* v___x_3080_; 
v_elems_3077_ = lean_ctor_get(v_x_3076_, 0);
lean_inc_ref(v_elems_3077_);
lean_dec_ref(v_x_3076_);
v_sz_3078_ = lean_array_size(v_elems_3077_);
v___x_3079_ = ((size_t)0ULL);
v___x_3080_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__0_spec__0_spec__1_spec__4(v_sz_3078_, v___x_3079_, v_elems_3077_);
return v___x_3080_;
}
else
{
lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; 
v___x_3081_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCommand_fromJson_spec__0_spec__0_spec__1___closed__0));
v___x_3082_ = lean_unsigned_to_nat(80u);
v___x_3083_ = l_Lean_Json_pretty(v_x_3076_, v___x_3082_);
v___x_3084_ = lean_string_append(v___x_3081_, v___x_3083_);
lean_dec_ref(v___x_3083_);
v___x_3085_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCommand_fromJson_spec__0_spec__0_spec__1___closed__1));
v___x_3086_ = lean_string_append(v___x_3084_, v___x_3085_);
v___x_3087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3087_, 0, v___x_3086_);
return v___x_3087_;
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__0_spec__0(lean_object* v_x_3090_){
_start:
{
if (lean_obj_tag(v_x_3090_) == 0)
{
lean_object* v___x_3091_; 
v___x_3091_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__0_spec__0___closed__0));
return v___x_3091_;
}
else
{
lean_object* v___x_3092_; 
v___x_3092_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__0_spec__0_spec__1(v_x_3090_);
if (lean_obj_tag(v___x_3092_) == 0)
{
lean_object* v_a_3093_; lean_object* v___x_3095_; uint8_t v_isShared_3096_; uint8_t v_isSharedCheck_3100_; 
v_a_3093_ = lean_ctor_get(v___x_3092_, 0);
v_isSharedCheck_3100_ = !lean_is_exclusive(v___x_3092_);
if (v_isSharedCheck_3100_ == 0)
{
v___x_3095_ = v___x_3092_;
v_isShared_3096_ = v_isSharedCheck_3100_;
goto v_resetjp_3094_;
}
else
{
lean_inc(v_a_3093_);
lean_dec(v___x_3092_);
v___x_3095_ = lean_box(0);
v_isShared_3096_ = v_isSharedCheck_3100_;
goto v_resetjp_3094_;
}
v_resetjp_3094_:
{
lean_object* v___x_3098_; 
if (v_isShared_3096_ == 0)
{
v___x_3098_ = v___x_3095_;
goto v_reusejp_3097_;
}
else
{
lean_object* v_reuseFailAlloc_3099_; 
v_reuseFailAlloc_3099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3099_, 0, v_a_3093_);
v___x_3098_ = v_reuseFailAlloc_3099_;
goto v_reusejp_3097_;
}
v_reusejp_3097_:
{
return v___x_3098_;
}
}
}
else
{
lean_object* v_a_3101_; lean_object* v___x_3103_; uint8_t v_isShared_3104_; uint8_t v_isSharedCheck_3109_; 
v_a_3101_ = lean_ctor_get(v___x_3092_, 0);
v_isSharedCheck_3109_ = !lean_is_exclusive(v___x_3092_);
if (v_isSharedCheck_3109_ == 0)
{
v___x_3103_ = v___x_3092_;
v_isShared_3104_ = v_isSharedCheck_3109_;
goto v_resetjp_3102_;
}
else
{
lean_inc(v_a_3101_);
lean_dec(v___x_3092_);
v___x_3103_ = lean_box(0);
v_isShared_3104_ = v_isSharedCheck_3109_;
goto v_resetjp_3102_;
}
v_resetjp_3102_:
{
lean_object* v___x_3105_; lean_object* v___x_3107_; 
v___x_3105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3105_, 0, v_a_3101_);
if (v_isShared_3104_ == 0)
{
lean_ctor_set(v___x_3103_, 0, v___x_3105_);
v___x_3107_ = v___x_3103_;
goto v_reusejp_3106_;
}
else
{
lean_object* v_reuseFailAlloc_3108_; 
v_reuseFailAlloc_3108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3108_, 0, v___x_3105_);
v___x_3107_ = v_reuseFailAlloc_3108_;
goto v_reusejp_3106_;
}
v_reusejp_3106_:
{
return v___x_3107_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__0(lean_object* v_j_3110_, lean_object* v_k_3111_){
_start:
{
lean_object* v___x_3112_; lean_object* v___x_3113_; 
v___x_3112_ = l_Lean_Json_getObjValD(v_j_3110_, v_k_3111_);
v___x_3113_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__0_spec__0(v___x_3112_);
return v___x_3113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__0___boxed(lean_object* v_j_3114_, lean_object* v_k_3115_){
_start:
{
lean_object* v_res_3116_; 
v_res_3116_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__0(v_j_3114_, v_k_3115_);
lean_dec_ref(v_k_3115_);
return v_res_3116_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__2(void){
_start:
{
uint8_t v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; 
v___x_3122_ = 1;
v___x_3123_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__1));
v___x_3124_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3123_, v___x_3122_);
return v___x_3124_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__3(void){
_start:
{
lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; 
v___x_3125_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__5));
v___x_3126_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__2, &l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__2);
v___x_3127_ = lean_string_append(v___x_3126_, v___x_3125_);
return v___x_3127_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__6(void){
_start:
{
uint8_t v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; 
v___x_3131_ = 1;
v___x_3132_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__5));
v___x_3133_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3132_, v___x_3131_);
return v___x_3133_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__7(void){
_start:
{
lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; 
v___x_3134_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__6, &l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__6);
v___x_3135_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__3, &l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__3);
v___x_3136_ = lean_string_append(v___x_3135_, v___x_3134_);
return v___x_3136_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__8(void){
_start:
{
lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; 
v___x_3137_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_3138_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__7, &l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__7);
v___x_3139_ = lean_string_append(v___x_3138_, v___x_3137_);
return v___x_3139_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__11(void){
_start:
{
uint8_t v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; 
v___x_3143_ = 1;
v___x_3144_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__10));
v___x_3145_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3144_, v___x_3143_);
return v___x_3145_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__12(void){
_start:
{
lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; 
v___x_3146_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__11, &l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__11);
v___x_3147_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__3, &l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__3);
v___x_3148_ = lean_string_append(v___x_3147_, v___x_3146_);
return v___x_3148_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__13(void){
_start:
{
lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; 
v___x_3149_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_3150_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__12, &l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__12);
v___x_3151_ = lean_string_append(v___x_3150_, v___x_3149_);
return v___x_3151_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__16(void){
_start:
{
uint8_t v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; 
v___x_3155_ = 1;
v___x_3156_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__15));
v___x_3157_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3156_, v___x_3155_);
return v___x_3157_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__17(void){
_start:
{
lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; 
v___x_3158_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__16, &l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__16_once, _init_l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__16);
v___x_3159_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__3, &l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__3);
v___x_3160_ = lean_string_append(v___x_3159_, v___x_3158_);
return v___x_3160_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__18(void){
_start:
{
lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; 
v___x_3161_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_3162_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__17, &l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__17_once, _init_l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__17);
v___x_3163_ = lean_string_append(v___x_3162_, v___x_3161_);
return v___x_3163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson(lean_object* v_json_3164_){
_start:
{
lean_object* v___x_3165_; lean_object* v___x_3166_; 
v___x_3165_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkspaceEdit_toJson___closed__0));
lean_inc(v_json_3164_);
v___x_3166_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__2(v_json_3164_, v___x_3165_);
if (lean_obj_tag(v___x_3166_) == 0)
{
lean_object* v_a_3167_; lean_object* v___x_3169_; uint8_t v_isShared_3170_; uint8_t v_isSharedCheck_3176_; 
lean_dec(v_json_3164_);
v_a_3167_ = lean_ctor_get(v___x_3166_, 0);
v_isSharedCheck_3176_ = !lean_is_exclusive(v___x_3166_);
if (v_isSharedCheck_3176_ == 0)
{
v___x_3169_ = v___x_3166_;
v_isShared_3170_ = v_isSharedCheck_3176_;
goto v_resetjp_3168_;
}
else
{
lean_inc(v_a_3167_);
lean_dec(v___x_3166_);
v___x_3169_ = lean_box(0);
v_isShared_3170_ = v_isSharedCheck_3176_;
goto v_resetjp_3168_;
}
v_resetjp_3168_:
{
lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3174_; 
v___x_3171_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__8, &l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__8);
v___x_3172_ = lean_string_append(v___x_3171_, v_a_3167_);
lean_dec(v_a_3167_);
if (v_isShared_3170_ == 0)
{
lean_ctor_set(v___x_3169_, 0, v___x_3172_);
v___x_3174_ = v___x_3169_;
goto v_reusejp_3173_;
}
else
{
lean_object* v_reuseFailAlloc_3175_; 
v_reuseFailAlloc_3175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3175_, 0, v___x_3172_);
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
if (lean_obj_tag(v___x_3166_) == 0)
{
lean_object* v_a_3177_; lean_object* v___x_3179_; uint8_t v_isShared_3180_; uint8_t v_isSharedCheck_3184_; 
lean_dec(v_json_3164_);
v_a_3177_ = lean_ctor_get(v___x_3166_, 0);
v_isSharedCheck_3184_ = !lean_is_exclusive(v___x_3166_);
if (v_isSharedCheck_3184_ == 0)
{
v___x_3179_ = v___x_3166_;
v_isShared_3180_ = v_isSharedCheck_3184_;
goto v_resetjp_3178_;
}
else
{
lean_inc(v_a_3177_);
lean_dec(v___x_3166_);
v___x_3179_ = lean_box(0);
v_isShared_3180_ = v_isSharedCheck_3184_;
goto v_resetjp_3178_;
}
v_resetjp_3178_:
{
lean_object* v___x_3182_; 
if (v_isShared_3180_ == 0)
{
lean_ctor_set_tag(v___x_3179_, 0);
v___x_3182_ = v___x_3179_;
goto v_reusejp_3181_;
}
else
{
lean_object* v_reuseFailAlloc_3183_; 
v_reuseFailAlloc_3183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3183_, 0, v_a_3177_);
v___x_3182_ = v_reuseFailAlloc_3183_;
goto v_reusejp_3181_;
}
v_reusejp_3181_:
{
return v___x_3182_;
}
}
}
else
{
lean_object* v_a_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; 
v_a_3185_ = lean_ctor_get(v___x_3166_, 0);
lean_inc(v_a_3185_);
lean_dec_ref(v___x_3166_);
v___x_3186_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkspaceEdit_toJson___closed__1));
lean_inc(v_json_3164_);
v___x_3187_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__0(v_json_3164_, v___x_3186_);
if (lean_obj_tag(v___x_3187_) == 0)
{
lean_object* v_a_3188_; lean_object* v___x_3190_; uint8_t v_isShared_3191_; uint8_t v_isSharedCheck_3197_; 
lean_dec(v_a_3185_);
lean_dec(v_json_3164_);
v_a_3188_ = lean_ctor_get(v___x_3187_, 0);
v_isSharedCheck_3197_ = !lean_is_exclusive(v___x_3187_);
if (v_isSharedCheck_3197_ == 0)
{
v___x_3190_ = v___x_3187_;
v_isShared_3191_ = v_isSharedCheck_3197_;
goto v_resetjp_3189_;
}
else
{
lean_inc(v_a_3188_);
lean_dec(v___x_3187_);
v___x_3190_ = lean_box(0);
v_isShared_3191_ = v_isSharedCheck_3197_;
goto v_resetjp_3189_;
}
v_resetjp_3189_:
{
lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3195_; 
v___x_3192_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__13, &l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__13);
v___x_3193_ = lean_string_append(v___x_3192_, v_a_3188_);
lean_dec(v_a_3188_);
if (v_isShared_3191_ == 0)
{
lean_ctor_set(v___x_3190_, 0, v___x_3193_);
v___x_3195_ = v___x_3190_;
goto v_reusejp_3194_;
}
else
{
lean_object* v_reuseFailAlloc_3196_; 
v_reuseFailAlloc_3196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3196_, 0, v___x_3193_);
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
if (lean_obj_tag(v___x_3187_) == 0)
{
lean_object* v_a_3198_; lean_object* v___x_3200_; uint8_t v_isShared_3201_; uint8_t v_isSharedCheck_3205_; 
lean_dec(v_a_3185_);
lean_dec(v_json_3164_);
v_a_3198_ = lean_ctor_get(v___x_3187_, 0);
v_isSharedCheck_3205_ = !lean_is_exclusive(v___x_3187_);
if (v_isSharedCheck_3205_ == 0)
{
v___x_3200_ = v___x_3187_;
v_isShared_3201_ = v_isSharedCheck_3205_;
goto v_resetjp_3199_;
}
else
{
lean_inc(v_a_3198_);
lean_dec(v___x_3187_);
v___x_3200_ = lean_box(0);
v_isShared_3201_ = v_isSharedCheck_3205_;
goto v_resetjp_3199_;
}
v_resetjp_3199_:
{
lean_object* v___x_3203_; 
if (v_isShared_3201_ == 0)
{
lean_ctor_set_tag(v___x_3200_, 0);
v___x_3203_ = v___x_3200_;
goto v_reusejp_3202_;
}
else
{
lean_object* v_reuseFailAlloc_3204_; 
v_reuseFailAlloc_3204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3204_, 0, v_a_3198_);
v___x_3203_ = v_reuseFailAlloc_3204_;
goto v_reusejp_3202_;
}
v_reusejp_3202_:
{
return v___x_3203_;
}
}
}
else
{
lean_object* v_a_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; 
v_a_3206_ = lean_ctor_get(v___x_3187_, 0);
lean_inc(v_a_3206_);
lean_dec_ref(v___x_3187_);
v___x_3207_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkspaceEdit_toJson___closed__2));
v___x_3208_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__1(v_json_3164_, v___x_3207_);
if (lean_obj_tag(v___x_3208_) == 0)
{
lean_object* v_a_3209_; lean_object* v___x_3211_; uint8_t v_isShared_3212_; uint8_t v_isSharedCheck_3218_; 
lean_dec(v_a_3206_);
lean_dec(v_a_3185_);
v_a_3209_ = lean_ctor_get(v___x_3208_, 0);
v_isSharedCheck_3218_ = !lean_is_exclusive(v___x_3208_);
if (v_isSharedCheck_3218_ == 0)
{
v___x_3211_ = v___x_3208_;
v_isShared_3212_ = v_isSharedCheck_3218_;
goto v_resetjp_3210_;
}
else
{
lean_inc(v_a_3209_);
lean_dec(v___x_3208_);
v___x_3211_ = lean_box(0);
v_isShared_3212_ = v_isSharedCheck_3218_;
goto v_resetjp_3210_;
}
v_resetjp_3210_:
{
lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3216_; 
v___x_3213_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__18, &l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__18_once, _init_l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__18);
v___x_3214_ = lean_string_append(v___x_3213_, v_a_3209_);
lean_dec(v_a_3209_);
if (v_isShared_3212_ == 0)
{
lean_ctor_set(v___x_3211_, 0, v___x_3214_);
v___x_3216_ = v___x_3211_;
goto v_reusejp_3215_;
}
else
{
lean_object* v_reuseFailAlloc_3217_; 
v_reuseFailAlloc_3217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3217_, 0, v___x_3214_);
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
if (lean_obj_tag(v___x_3208_) == 0)
{
lean_object* v_a_3219_; lean_object* v___x_3221_; uint8_t v_isShared_3222_; uint8_t v_isSharedCheck_3226_; 
lean_dec(v_a_3206_);
lean_dec(v_a_3185_);
v_a_3219_ = lean_ctor_get(v___x_3208_, 0);
v_isSharedCheck_3226_ = !lean_is_exclusive(v___x_3208_);
if (v_isSharedCheck_3226_ == 0)
{
v___x_3221_ = v___x_3208_;
v_isShared_3222_ = v_isSharedCheck_3226_;
goto v_resetjp_3220_;
}
else
{
lean_inc(v_a_3219_);
lean_dec(v___x_3208_);
v___x_3221_ = lean_box(0);
v_isShared_3222_ = v_isSharedCheck_3226_;
goto v_resetjp_3220_;
}
v_resetjp_3220_:
{
lean_object* v___x_3224_; 
if (v_isShared_3222_ == 0)
{
lean_ctor_set_tag(v___x_3221_, 0);
v___x_3224_ = v___x_3221_;
goto v_reusejp_3223_;
}
else
{
lean_object* v_reuseFailAlloc_3225_; 
v_reuseFailAlloc_3225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3225_, 0, v_a_3219_);
v___x_3224_ = v_reuseFailAlloc_3225_;
goto v_reusejp_3223_;
}
v_reusejp_3223_:
{
return v___x_3224_;
}
}
}
else
{
lean_object* v_a_3227_; lean_object* v___x_3229_; uint8_t v_isShared_3230_; uint8_t v_isSharedCheck_3235_; 
v_a_3227_ = lean_ctor_get(v___x_3208_, 0);
v_isSharedCheck_3235_ = !lean_is_exclusive(v___x_3208_);
if (v_isSharedCheck_3235_ == 0)
{
v___x_3229_ = v___x_3208_;
v_isShared_3230_ = v_isSharedCheck_3235_;
goto v_resetjp_3228_;
}
else
{
lean_inc(v_a_3227_);
lean_dec(v___x_3208_);
v___x_3229_ = lean_box(0);
v_isShared_3230_ = v_isSharedCheck_3235_;
goto v_resetjp_3228_;
}
v_resetjp_3228_:
{
lean_object* v___x_3231_; lean_object* v___x_3233_; 
v___x_3231_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3231_, 0, v_a_3185_);
lean_ctor_set(v___x_3231_, 1, v_a_3206_);
lean_ctor_set(v___x_3231_, 2, v_a_3227_);
if (v_isShared_3230_ == 0)
{
lean_ctor_set(v___x_3229_, 0, v___x_3231_);
v___x_3233_ = v___x_3229_;
goto v_reusejp_3232_;
}
else
{
lean_object* v_reuseFailAlloc_3234_; 
v_reuseFailAlloc_3234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3234_, 0, v___x_3231_);
v___x_3233_ = v_reuseFailAlloc_3234_;
goto v_reusejp_3232_;
}
v_reusejp_3232_:
{
return v___x_3233_;
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__1_spec__2_spec__4_spec__7(lean_object* v_cmp_3236_, lean_object* v_00_u03b2_3237_, lean_object* v_k_3238_, lean_object* v_v_3239_, lean_object* v_t_3240_, lean_object* v_hl_3241_){
_start:
{
lean_object* v___x_3242_; 
v___x_3242_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__1_spec__2_spec__4_spec__7___redArg(v_cmp_3236_, v_k_3238_, v_v_3239_, v_t_3240_);
return v___x_3242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_WorkspaceEdit_instAppend___lam__2(lean_object* v_b_u2082_3248_, lean_object* v_x_3249_){
_start:
{
if (lean_obj_tag(v_x_3249_) == 0)
{
lean_object* v___x_3250_; 
v___x_3250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3250_, 0, v_b_u2082_3248_);
return v___x_3250_;
}
else
{
lean_object* v_val_3251_; lean_object* v___x_3253_; uint8_t v_isShared_3254_; uint8_t v_isSharedCheck_3259_; 
v_val_3251_ = lean_ctor_get(v_x_3249_, 0);
v_isSharedCheck_3259_ = !lean_is_exclusive(v_x_3249_);
if (v_isSharedCheck_3259_ == 0)
{
v___x_3253_ = v_x_3249_;
v_isShared_3254_ = v_isSharedCheck_3259_;
goto v_resetjp_3252_;
}
else
{
lean_inc(v_val_3251_);
lean_dec(v_x_3249_);
v___x_3253_ = lean_box(0);
v_isShared_3254_ = v_isSharedCheck_3259_;
goto v_resetjp_3252_;
}
v_resetjp_3252_:
{
lean_object* v___x_3255_; lean_object* v___x_3257_; 
v___x_3255_ = l_Array_append___redArg(v_val_3251_, v_b_u2082_3248_);
lean_dec_ref(v_b_u2082_3248_);
if (v_isShared_3254_ == 0)
{
lean_ctor_set(v___x_3253_, 0, v___x_3255_);
v___x_3257_ = v___x_3253_;
goto v_reusejp_3256_;
}
else
{
lean_object* v_reuseFailAlloc_3258_; 
v_reuseFailAlloc_3258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3258_, 0, v___x_3255_);
v___x_3257_ = v_reuseFailAlloc_3258_;
goto v_reusejp_3256_;
}
v_reusejp_3256_:
{
return v___x_3257_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_WorkspaceEdit_instAppend___lam__0(lean_object* v___f_3260_, lean_object* v_t_3261_, lean_object* v_a_3262_, lean_object* v_b_u2082_3263_){
_start:
{
lean_object* v___f_3264_; lean_object* v___x_3265_; 
v___f_3264_ = lean_alloc_closure((void*)(l_Lean_Lsp_WorkspaceEdit_instAppend___lam__2), 2, 1);
lean_closure_set(v___f_3264_, 0, v_b_u2082_3263_);
v___x_3265_ = l_Std_DTreeMap_Internal_Impl_Const_alter___redArg(v___f_3260_, v_a_3262_, v___f_3264_, v_t_3261_);
return v___x_3265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_WorkspaceEdit_instAppend___lam__1(lean_object* v_b_u2082_3266_, lean_object* v_x_3267_){
_start:
{
lean_object* v___x_3268_; 
v___x_3268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3268_, 0, v_b_u2082_3266_);
return v___x_3268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_WorkspaceEdit_instAppend___lam__1___boxed(lean_object* v_b_u2082_3269_, lean_object* v_x_3270_){
_start:
{
lean_object* v_res_3271_; 
v_res_3271_ = l_Lean_Lsp_WorkspaceEdit_instAppend___lam__1(v_b_u2082_3269_, v_x_3270_);
lean_dec(v_x_3270_);
return v_res_3271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_WorkspaceEdit_instAppend___lam__3(lean_object* v___f_3272_, lean_object* v_t_3273_, lean_object* v_a_3274_, lean_object* v_b_u2082_3275_){
_start:
{
lean_object* v___f_3276_; lean_object* v___x_3277_; 
v___f_3276_ = lean_alloc_closure((void*)(l_Lean_Lsp_WorkspaceEdit_instAppend___lam__1___boxed), 2, 1);
lean_closure_set(v___f_3276_, 0, v_b_u2082_3275_);
v___x_3277_ = l_Std_DTreeMap_Internal_Impl_Const_alter___redArg(v___f_3272_, v_a_3274_, v___f_3276_, v_t_3273_);
return v___x_3277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_WorkspaceEdit_instAppend___lam__4(lean_object* v___f_3278_, lean_object* v___f_3279_, lean_object* v_x_3280_, lean_object* v_y_3281_){
_start:
{
lean_object* v_changes_x3f_3282_; lean_object* v_documentChanges_x3f_3283_; lean_object* v_changeAnnotations_x3f_3284_; lean_object* v___y_3286_; lean_object* v___y_3287_; lean_object* v___y_3322_; 
v_changes_x3f_3282_ = lean_ctor_get(v_y_3281_, 0);
lean_inc(v_changes_x3f_3282_);
v_documentChanges_x3f_3283_ = lean_ctor_get(v_y_3281_, 1);
lean_inc(v_documentChanges_x3f_3283_);
v_changeAnnotations_x3f_3284_ = lean_ctor_get(v_y_3281_, 2);
lean_inc(v_changeAnnotations_x3f_3284_);
lean_dec_ref(v_y_3281_);
if (lean_obj_tag(v_changes_x3f_3282_) == 0)
{
lean_object* v_changes_x3f_3335_; 
lean_dec_ref(v___f_3279_);
v_changes_x3f_3335_ = lean_ctor_get(v_x_3280_, 0);
lean_inc(v_changes_x3f_3335_);
v___y_3322_ = v_changes_x3f_3335_;
goto v___jp_3321_;
}
else
{
lean_object* v_changes_x3f_3336_; 
v_changes_x3f_3336_ = lean_ctor_get(v_x_3280_, 0);
lean_inc(v_changes_x3f_3336_);
if (lean_obj_tag(v_changes_x3f_3336_) == 0)
{
lean_dec_ref(v___f_3279_);
v___y_3322_ = v_changes_x3f_3282_;
goto v___jp_3321_;
}
else
{
lean_object* v_val_3337_; lean_object* v_val_3338_; lean_object* v___x_3340_; uint8_t v_isShared_3341_; uint8_t v_isSharedCheck_3346_; 
v_val_3337_ = lean_ctor_get(v_changes_x3f_3282_, 0);
lean_inc(v_val_3337_);
lean_dec_ref(v_changes_x3f_3282_);
v_val_3338_ = lean_ctor_get(v_changes_x3f_3336_, 0);
v_isSharedCheck_3346_ = !lean_is_exclusive(v_changes_x3f_3336_);
if (v_isSharedCheck_3346_ == 0)
{
v___x_3340_ = v_changes_x3f_3336_;
v_isShared_3341_ = v_isSharedCheck_3346_;
goto v_resetjp_3339_;
}
else
{
lean_inc(v_val_3338_);
lean_dec(v_changes_x3f_3336_);
v___x_3340_ = lean_box(0);
v_isShared_3341_ = v_isSharedCheck_3346_;
goto v_resetjp_3339_;
}
v_resetjp_3339_:
{
lean_object* v___x_3342_; lean_object* v___x_3344_; 
v___x_3342_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3279_, v_val_3338_, v_val_3337_);
if (v_isShared_3341_ == 0)
{
lean_ctor_set(v___x_3340_, 0, v___x_3342_);
v___x_3344_ = v___x_3340_;
goto v_reusejp_3343_;
}
else
{
lean_object* v_reuseFailAlloc_3345_; 
v_reuseFailAlloc_3345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3345_, 0, v___x_3342_);
v___x_3344_ = v_reuseFailAlloc_3345_;
goto v_reusejp_3343_;
}
v_reusejp_3343_:
{
v___y_3322_ = v___x_3344_;
goto v___jp_3321_;
}
}
}
}
v___jp_3285_:
{
if (lean_obj_tag(v_changeAnnotations_x3f_3284_) == 0)
{
lean_object* v_changeAnnotations_x3f_3288_; lean_object* v___x_3290_; uint8_t v_isShared_3291_; uint8_t v_isSharedCheck_3295_; 
lean_dec_ref(v___f_3278_);
v_changeAnnotations_x3f_3288_ = lean_ctor_get(v_x_3280_, 2);
v_isSharedCheck_3295_ = !lean_is_exclusive(v_x_3280_);
if (v_isSharedCheck_3295_ == 0)
{
lean_object* v_unused_3296_; lean_object* v_unused_3297_; 
v_unused_3296_ = lean_ctor_get(v_x_3280_, 1);
lean_dec(v_unused_3296_);
v_unused_3297_ = lean_ctor_get(v_x_3280_, 0);
lean_dec(v_unused_3297_);
v___x_3290_ = v_x_3280_;
v_isShared_3291_ = v_isSharedCheck_3295_;
goto v_resetjp_3289_;
}
else
{
lean_inc(v_changeAnnotations_x3f_3288_);
lean_dec(v_x_3280_);
v___x_3290_ = lean_box(0);
v_isShared_3291_ = v_isSharedCheck_3295_;
goto v_resetjp_3289_;
}
v_resetjp_3289_:
{
lean_object* v___x_3293_; 
if (v_isShared_3291_ == 0)
{
lean_ctor_set(v___x_3290_, 1, v___y_3287_);
lean_ctor_set(v___x_3290_, 0, v___y_3286_);
v___x_3293_ = v___x_3290_;
goto v_reusejp_3292_;
}
else
{
lean_object* v_reuseFailAlloc_3294_; 
v_reuseFailAlloc_3294_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3294_, 0, v___y_3286_);
lean_ctor_set(v_reuseFailAlloc_3294_, 1, v___y_3287_);
lean_ctor_set(v_reuseFailAlloc_3294_, 2, v_changeAnnotations_x3f_3288_);
v___x_3293_ = v_reuseFailAlloc_3294_;
goto v_reusejp_3292_;
}
v_reusejp_3292_:
{
return v___x_3293_;
}
}
}
else
{
lean_object* v_changeAnnotations_x3f_3298_; lean_object* v___x_3300_; uint8_t v_isShared_3301_; uint8_t v_isSharedCheck_3318_; 
v_changeAnnotations_x3f_3298_ = lean_ctor_get(v_x_3280_, 2);
v_isSharedCheck_3318_ = !lean_is_exclusive(v_x_3280_);
if (v_isSharedCheck_3318_ == 0)
{
lean_object* v_unused_3319_; lean_object* v_unused_3320_; 
v_unused_3319_ = lean_ctor_get(v_x_3280_, 1);
lean_dec(v_unused_3319_);
v_unused_3320_ = lean_ctor_get(v_x_3280_, 0);
lean_dec(v_unused_3320_);
v___x_3300_ = v_x_3280_;
v_isShared_3301_ = v_isSharedCheck_3318_;
goto v_resetjp_3299_;
}
else
{
lean_inc(v_changeAnnotations_x3f_3298_);
lean_dec(v_x_3280_);
v___x_3300_ = lean_box(0);
v_isShared_3301_ = v_isSharedCheck_3318_;
goto v_resetjp_3299_;
}
v_resetjp_3299_:
{
if (lean_obj_tag(v_changeAnnotations_x3f_3298_) == 0)
{
lean_object* v___x_3303_; 
lean_dec_ref(v___f_3278_);
if (v_isShared_3301_ == 0)
{
lean_ctor_set(v___x_3300_, 2, v_changeAnnotations_x3f_3284_);
lean_ctor_set(v___x_3300_, 1, v___y_3287_);
lean_ctor_set(v___x_3300_, 0, v___y_3286_);
v___x_3303_ = v___x_3300_;
goto v_reusejp_3302_;
}
else
{
lean_object* v_reuseFailAlloc_3304_; 
v_reuseFailAlloc_3304_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3304_, 0, v___y_3286_);
lean_ctor_set(v_reuseFailAlloc_3304_, 1, v___y_3287_);
lean_ctor_set(v_reuseFailAlloc_3304_, 2, v_changeAnnotations_x3f_3284_);
v___x_3303_ = v_reuseFailAlloc_3304_;
goto v_reusejp_3302_;
}
v_reusejp_3302_:
{
return v___x_3303_;
}
}
else
{
lean_object* v_val_3305_; lean_object* v_val_3306_; lean_object* v___x_3308_; uint8_t v_isShared_3309_; uint8_t v_isSharedCheck_3317_; 
v_val_3305_ = lean_ctor_get(v_changeAnnotations_x3f_3284_, 0);
lean_inc(v_val_3305_);
lean_dec_ref(v_changeAnnotations_x3f_3284_);
v_val_3306_ = lean_ctor_get(v_changeAnnotations_x3f_3298_, 0);
v_isSharedCheck_3317_ = !lean_is_exclusive(v_changeAnnotations_x3f_3298_);
if (v_isSharedCheck_3317_ == 0)
{
v___x_3308_ = v_changeAnnotations_x3f_3298_;
v_isShared_3309_ = v_isSharedCheck_3317_;
goto v_resetjp_3307_;
}
else
{
lean_inc(v_val_3306_);
lean_dec(v_changeAnnotations_x3f_3298_);
v___x_3308_ = lean_box(0);
v_isShared_3309_ = v_isSharedCheck_3317_;
goto v_resetjp_3307_;
}
v_resetjp_3307_:
{
lean_object* v___x_3310_; lean_object* v___x_3312_; 
v___x_3310_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3278_, v_val_3306_, v_val_3305_);
if (v_isShared_3309_ == 0)
{
lean_ctor_set(v___x_3308_, 0, v___x_3310_);
v___x_3312_ = v___x_3308_;
goto v_reusejp_3311_;
}
else
{
lean_object* v_reuseFailAlloc_3316_; 
v_reuseFailAlloc_3316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3316_, 0, v___x_3310_);
v___x_3312_ = v_reuseFailAlloc_3316_;
goto v_reusejp_3311_;
}
v_reusejp_3311_:
{
lean_object* v___x_3314_; 
if (v_isShared_3301_ == 0)
{
lean_ctor_set(v___x_3300_, 2, v___x_3312_);
lean_ctor_set(v___x_3300_, 1, v___y_3287_);
lean_ctor_set(v___x_3300_, 0, v___y_3286_);
v___x_3314_ = v___x_3300_;
goto v_reusejp_3313_;
}
else
{
lean_object* v_reuseFailAlloc_3315_; 
v_reuseFailAlloc_3315_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3315_, 0, v___y_3286_);
lean_ctor_set(v_reuseFailAlloc_3315_, 1, v___y_3287_);
lean_ctor_set(v_reuseFailAlloc_3315_, 2, v___x_3312_);
v___x_3314_ = v_reuseFailAlloc_3315_;
goto v_reusejp_3313_;
}
v_reusejp_3313_:
{
return v___x_3314_;
}
}
}
}
}
}
}
v___jp_3321_:
{
if (lean_obj_tag(v_documentChanges_x3f_3283_) == 0)
{
lean_object* v_documentChanges_x3f_3323_; 
v_documentChanges_x3f_3323_ = lean_ctor_get(v_x_3280_, 1);
lean_inc(v_documentChanges_x3f_3323_);
v___y_3286_ = v___y_3322_;
v___y_3287_ = v_documentChanges_x3f_3323_;
goto v___jp_3285_;
}
else
{
lean_object* v_documentChanges_x3f_3324_; 
v_documentChanges_x3f_3324_ = lean_ctor_get(v_x_3280_, 1);
lean_inc(v_documentChanges_x3f_3324_);
if (lean_obj_tag(v_documentChanges_x3f_3324_) == 0)
{
v___y_3286_ = v___y_3322_;
v___y_3287_ = v_documentChanges_x3f_3283_;
goto v___jp_3285_;
}
else
{
lean_object* v_val_3325_; lean_object* v_val_3326_; lean_object* v___x_3328_; uint8_t v_isShared_3329_; uint8_t v_isSharedCheck_3334_; 
v_val_3325_ = lean_ctor_get(v_documentChanges_x3f_3283_, 0);
lean_inc(v_val_3325_);
lean_dec_ref(v_documentChanges_x3f_3283_);
v_val_3326_ = lean_ctor_get(v_documentChanges_x3f_3324_, 0);
v_isSharedCheck_3334_ = !lean_is_exclusive(v_documentChanges_x3f_3324_);
if (v_isSharedCheck_3334_ == 0)
{
v___x_3328_ = v_documentChanges_x3f_3324_;
v_isShared_3329_ = v_isSharedCheck_3334_;
goto v_resetjp_3327_;
}
else
{
lean_inc(v_val_3326_);
lean_dec(v_documentChanges_x3f_3324_);
v___x_3328_ = lean_box(0);
v_isShared_3329_ = v_isSharedCheck_3334_;
goto v_resetjp_3327_;
}
v_resetjp_3327_:
{
lean_object* v___x_3330_; lean_object* v___x_3332_; 
v___x_3330_ = l_Array_append___redArg(v_val_3326_, v_val_3325_);
lean_dec(v_val_3325_);
if (v_isShared_3329_ == 0)
{
lean_ctor_set(v___x_3328_, 0, v___x_3330_);
v___x_3332_ = v___x_3328_;
goto v_reusejp_3331_;
}
else
{
lean_object* v_reuseFailAlloc_3333_; 
v_reuseFailAlloc_3333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3333_, 0, v___x_3330_);
v___x_3332_ = v_reuseFailAlloc_3333_;
goto v_reusejp_3331_;
}
v_reusejp_3331_:
{
v___y_3286_ = v___y_3322_;
v___y_3287_ = v___x_3332_;
goto v___jp_3285_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_WorkspaceEdit_ofTextDocumentEdit(lean_object* v_e_3355_){
_start:
{
lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; 
v___x_3356_ = lean_box(0);
v___x_3357_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3357_, 0, v_e_3355_);
v___x_3358_ = lean_unsigned_to_nat(1u);
v___x_3359_ = lean_mk_empty_array_with_capacity(v___x_3358_);
v___x_3360_ = lean_array_push(v___x_3359_, v___x_3357_);
v___x_3361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3361_, 0, v___x_3360_);
v___x_3362_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3362_, 0, v___x_3356_);
lean_ctor_set(v___x_3362_, 1, v___x_3361_);
lean_ctor_set(v___x_3362_, 2, v___x_3356_);
return v___x_3362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_WorkspaceEdit_ofTextEdit(lean_object* v_doc_3363_, lean_object* v_te_3364_){
_start:
{
lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; 
v___x_3365_ = lean_unsigned_to_nat(1u);
v___x_3366_ = lean_mk_empty_array_with_capacity(v___x_3365_);
v___x_3367_ = lean_array_push(v___x_3366_, v_te_3364_);
v___x_3368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3368_, 0, v_doc_3363_);
lean_ctor_set(v___x_3368_, 1, v___x_3367_);
v___x_3369_ = l_Lean_Lsp_WorkspaceEdit_ofTextDocumentEdit(v___x_3368_);
return v___x_3369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonApplyWorkspaceEditParams_toJson(lean_object* v_x_3371_){
_start:
{
lean_object* v_label_x3f_3372_; lean_object* v_edit_3373_; lean_object* v___x_3375_; uint8_t v_isShared_3376_; uint8_t v_isSharedCheck_3391_; 
v_label_x3f_3372_ = lean_ctor_get(v_x_3371_, 0);
v_edit_3373_ = lean_ctor_get(v_x_3371_, 1);
v_isSharedCheck_3391_ = !lean_is_exclusive(v_x_3371_);
if (v_isSharedCheck_3391_ == 0)
{
v___x_3375_ = v_x_3371_;
v_isShared_3376_ = v_isSharedCheck_3391_;
goto v_resetjp_3374_;
}
else
{
lean_inc(v_edit_3373_);
lean_inc(v_label_x3f_3372_);
lean_dec(v_x_3371_);
v___x_3375_ = lean_box(0);
v_isShared_3376_ = v_isSharedCheck_3391_;
goto v_resetjp_3374_;
}
v_resetjp_3374_:
{
lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3382_; 
v___x_3377_ = ((lean_object*)(l_Lean_Lsp_instToJsonChangeAnnotation_toJson___closed__0));
v___x_3378_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextEdit_toJson_spec__1(v___x_3377_, v_label_x3f_3372_);
v___x_3379_ = ((lean_object*)(l_Lean_Lsp_instToJsonApplyWorkspaceEditParams_toJson___closed__0));
v___x_3380_ = l_Lean_Lsp_instToJsonWorkspaceEdit_toJson(v_edit_3373_);
if (v_isShared_3376_ == 0)
{
lean_ctor_set(v___x_3375_, 1, v___x_3380_);
lean_ctor_set(v___x_3375_, 0, v___x_3379_);
v___x_3382_ = v___x_3375_;
goto v_reusejp_3381_;
}
else
{
lean_object* v_reuseFailAlloc_3390_; 
v_reuseFailAlloc_3390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3390_, 0, v___x_3379_);
lean_ctor_set(v_reuseFailAlloc_3390_, 1, v___x_3380_);
v___x_3382_ = v_reuseFailAlloc_3390_;
goto v_reusejp_3381_;
}
v_reusejp_3381_:
{
lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; 
v___x_3383_ = lean_box(0);
v___x_3384_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3384_, 0, v___x_3382_);
lean_ctor_set(v___x_3384_, 1, v___x_3383_);
v___x_3385_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3385_, 0, v___x_3384_);
lean_ctor_set(v___x_3385_, 1, v___x_3383_);
v___x_3386_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3386_, 0, v___x_3378_);
lean_ctor_set(v___x_3386_, 1, v___x_3385_);
v___x_3387_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__2));
v___x_3388_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLocation_toJson_spec__0(v___x_3386_, v___x_3387_);
v___x_3389_ = l_Lean_Json_mkObj(v___x_3388_);
return v___x_3389_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson_spec__0(lean_object* v_j_3394_, lean_object* v_k_3395_){
_start:
{
lean_object* v___x_3396_; lean_object* v___x_3397_; 
v___x_3396_ = l_Lean_Json_getObjValD(v_j_3394_, v_k_3395_);
v___x_3397_ = l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson(v___x_3396_);
return v___x_3397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson_spec__0___boxed(lean_object* v_j_3398_, lean_object* v_k_3399_){
_start:
{
lean_object* v_res_3400_; 
v_res_3400_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson_spec__0(v_j_3398_, v_k_3399_);
lean_dec_ref(v_k_3399_);
return v_res_3400_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__2(void){
_start:
{
uint8_t v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; 
v___x_3406_ = 1;
v___x_3407_ = ((lean_object*)(l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__1));
v___x_3408_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3407_, v___x_3406_);
return v___x_3408_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__3(void){
_start:
{
lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; 
v___x_3409_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__5));
v___x_3410_ = lean_obj_once(&l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__2, &l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__2);
v___x_3411_ = lean_string_append(v___x_3410_, v___x_3409_);
return v___x_3411_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__6(void){
_start:
{
uint8_t v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; 
v___x_3415_ = 1;
v___x_3416_ = ((lean_object*)(l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__5));
v___x_3417_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3416_, v___x_3415_);
return v___x_3417_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__7(void){
_start:
{
lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; 
v___x_3418_ = lean_obj_once(&l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__6, &l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__6);
v___x_3419_ = lean_obj_once(&l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__3);
v___x_3420_ = lean_string_append(v___x_3419_, v___x_3418_);
return v___x_3420_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__8(void){
_start:
{
lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; 
v___x_3421_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_3422_ = lean_obj_once(&l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__7);
v___x_3423_ = lean_string_append(v___x_3422_, v___x_3421_);
return v___x_3423_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__10(void){
_start:
{
uint8_t v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; 
v___x_3426_ = 1;
v___x_3427_ = ((lean_object*)(l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__9));
v___x_3428_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3427_, v___x_3426_);
return v___x_3428_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__11(void){
_start:
{
lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; 
v___x_3429_ = lean_obj_once(&l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__10, &l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__10);
v___x_3430_ = lean_obj_once(&l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__3);
v___x_3431_ = lean_string_append(v___x_3430_, v___x_3429_);
return v___x_3431_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__12(void){
_start:
{
lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; 
v___x_3432_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_3433_ = lean_obj_once(&l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__11, &l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__11);
v___x_3434_ = lean_string_append(v___x_3433_, v___x_3432_);
return v___x_3434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson(lean_object* v_json_3435_){
_start:
{
lean_object* v___x_3436_; lean_object* v___x_3437_; 
v___x_3436_ = ((lean_object*)(l_Lean_Lsp_instToJsonChangeAnnotation_toJson___closed__0));
lean_inc(v_json_3435_);
v___x_3437_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextEdit_fromJson_spec__1(v_json_3435_, v___x_3436_);
if (lean_obj_tag(v___x_3437_) == 0)
{
lean_object* v_a_3438_; lean_object* v___x_3440_; uint8_t v_isShared_3441_; uint8_t v_isSharedCheck_3447_; 
lean_dec(v_json_3435_);
v_a_3438_ = lean_ctor_get(v___x_3437_, 0);
v_isSharedCheck_3447_ = !lean_is_exclusive(v___x_3437_);
if (v_isSharedCheck_3447_ == 0)
{
v___x_3440_ = v___x_3437_;
v_isShared_3441_ = v_isSharedCheck_3447_;
goto v_resetjp_3439_;
}
else
{
lean_inc(v_a_3438_);
lean_dec(v___x_3437_);
v___x_3440_ = lean_box(0);
v_isShared_3441_ = v_isSharedCheck_3447_;
goto v_resetjp_3439_;
}
v_resetjp_3439_:
{
lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3445_; 
v___x_3442_ = lean_obj_once(&l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__8);
v___x_3443_ = lean_string_append(v___x_3442_, v_a_3438_);
lean_dec(v_a_3438_);
if (v_isShared_3441_ == 0)
{
lean_ctor_set(v___x_3440_, 0, v___x_3443_);
v___x_3445_ = v___x_3440_;
goto v_reusejp_3444_;
}
else
{
lean_object* v_reuseFailAlloc_3446_; 
v_reuseFailAlloc_3446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3446_, 0, v___x_3443_);
v___x_3445_ = v_reuseFailAlloc_3446_;
goto v_reusejp_3444_;
}
v_reusejp_3444_:
{
return v___x_3445_;
}
}
}
else
{
if (lean_obj_tag(v___x_3437_) == 0)
{
lean_object* v_a_3448_; lean_object* v___x_3450_; uint8_t v_isShared_3451_; uint8_t v_isSharedCheck_3455_; 
lean_dec(v_json_3435_);
v_a_3448_ = lean_ctor_get(v___x_3437_, 0);
v_isSharedCheck_3455_ = !lean_is_exclusive(v___x_3437_);
if (v_isSharedCheck_3455_ == 0)
{
v___x_3450_ = v___x_3437_;
v_isShared_3451_ = v_isSharedCheck_3455_;
goto v_resetjp_3449_;
}
else
{
lean_inc(v_a_3448_);
lean_dec(v___x_3437_);
v___x_3450_ = lean_box(0);
v_isShared_3451_ = v_isSharedCheck_3455_;
goto v_resetjp_3449_;
}
v_resetjp_3449_:
{
lean_object* v___x_3453_; 
if (v_isShared_3451_ == 0)
{
lean_ctor_set_tag(v___x_3450_, 0);
v___x_3453_ = v___x_3450_;
goto v_reusejp_3452_;
}
else
{
lean_object* v_reuseFailAlloc_3454_; 
v_reuseFailAlloc_3454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3454_, 0, v_a_3448_);
v___x_3453_ = v_reuseFailAlloc_3454_;
goto v_reusejp_3452_;
}
v_reusejp_3452_:
{
return v___x_3453_;
}
}
}
else
{
lean_object* v_a_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; 
v_a_3456_ = lean_ctor_get(v___x_3437_, 0);
lean_inc(v_a_3456_);
lean_dec_ref(v___x_3437_);
v___x_3457_ = ((lean_object*)(l_Lean_Lsp_instToJsonApplyWorkspaceEditParams_toJson___closed__0));
v___x_3458_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson_spec__0(v_json_3435_, v___x_3457_);
if (lean_obj_tag(v___x_3458_) == 0)
{
lean_object* v_a_3459_; lean_object* v___x_3461_; uint8_t v_isShared_3462_; uint8_t v_isSharedCheck_3468_; 
lean_dec(v_a_3456_);
v_a_3459_ = lean_ctor_get(v___x_3458_, 0);
v_isSharedCheck_3468_ = !lean_is_exclusive(v___x_3458_);
if (v_isSharedCheck_3468_ == 0)
{
v___x_3461_ = v___x_3458_;
v_isShared_3462_ = v_isSharedCheck_3468_;
goto v_resetjp_3460_;
}
else
{
lean_inc(v_a_3459_);
lean_dec(v___x_3458_);
v___x_3461_ = lean_box(0);
v_isShared_3462_ = v_isSharedCheck_3468_;
goto v_resetjp_3460_;
}
v_resetjp_3460_:
{
lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3466_; 
v___x_3463_ = lean_obj_once(&l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__12, &l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__12);
v___x_3464_ = lean_string_append(v___x_3463_, v_a_3459_);
lean_dec(v_a_3459_);
if (v_isShared_3462_ == 0)
{
lean_ctor_set(v___x_3461_, 0, v___x_3464_);
v___x_3466_ = v___x_3461_;
goto v_reusejp_3465_;
}
else
{
lean_object* v_reuseFailAlloc_3467_; 
v_reuseFailAlloc_3467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3467_, 0, v___x_3464_);
v___x_3466_ = v_reuseFailAlloc_3467_;
goto v_reusejp_3465_;
}
v_reusejp_3465_:
{
return v___x_3466_;
}
}
}
else
{
if (lean_obj_tag(v___x_3458_) == 0)
{
lean_object* v_a_3469_; lean_object* v___x_3471_; uint8_t v_isShared_3472_; uint8_t v_isSharedCheck_3476_; 
lean_dec(v_a_3456_);
v_a_3469_ = lean_ctor_get(v___x_3458_, 0);
v_isSharedCheck_3476_ = !lean_is_exclusive(v___x_3458_);
if (v_isSharedCheck_3476_ == 0)
{
v___x_3471_ = v___x_3458_;
v_isShared_3472_ = v_isSharedCheck_3476_;
goto v_resetjp_3470_;
}
else
{
lean_inc(v_a_3469_);
lean_dec(v___x_3458_);
v___x_3471_ = lean_box(0);
v_isShared_3472_ = v_isSharedCheck_3476_;
goto v_resetjp_3470_;
}
v_resetjp_3470_:
{
lean_object* v___x_3474_; 
if (v_isShared_3472_ == 0)
{
lean_ctor_set_tag(v___x_3471_, 0);
v___x_3474_ = v___x_3471_;
goto v_reusejp_3473_;
}
else
{
lean_object* v_reuseFailAlloc_3475_; 
v_reuseFailAlloc_3475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3475_, 0, v_a_3469_);
v___x_3474_ = v_reuseFailAlloc_3475_;
goto v_reusejp_3473_;
}
v_reusejp_3473_:
{
return v___x_3474_;
}
}
}
else
{
lean_object* v_a_3477_; lean_object* v___x_3479_; uint8_t v_isShared_3480_; uint8_t v_isSharedCheck_3485_; 
v_a_3477_ = lean_ctor_get(v___x_3458_, 0);
v_isSharedCheck_3485_ = !lean_is_exclusive(v___x_3458_);
if (v_isSharedCheck_3485_ == 0)
{
v___x_3479_ = v___x_3458_;
v_isShared_3480_ = v_isSharedCheck_3485_;
goto v_resetjp_3478_;
}
else
{
lean_inc(v_a_3477_);
lean_dec(v___x_3458_);
v___x_3479_ = lean_box(0);
v_isShared_3480_ = v_isSharedCheck_3485_;
goto v_resetjp_3478_;
}
v_resetjp_3478_:
{
lean_object* v___x_3481_; lean_object* v___x_3483_; 
v___x_3481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3481_, 0, v_a_3456_);
lean_ctor_set(v___x_3481_, 1, v_a_3477_);
if (v_isShared_3480_ == 0)
{
lean_ctor_set(v___x_3479_, 0, v___x_3481_);
v___x_3483_ = v___x_3479_;
goto v_reusejp_3482_;
}
else
{
lean_object* v_reuseFailAlloc_3484_; 
v_reuseFailAlloc_3484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3484_, 0, v___x_3481_);
v___x_3483_ = v_reuseFailAlloc_3484_;
goto v_reusejp_3482_;
}
v_reusejp_3482_:
{
return v___x_3483_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonTextDocumentItem_toJson(lean_object* v_x_3490_){
_start:
{
lean_object* v_uri_3491_; lean_object* v_languageId_3492_; lean_object* v_version_3493_; lean_object* v_text_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; 
v_uri_3491_ = lean_ctor_get(v_x_3490_, 0);
lean_inc_ref(v_uri_3491_);
v_languageId_3492_ = lean_ctor_get(v_x_3490_, 1);
lean_inc_ref(v_languageId_3492_);
v_version_3493_ = lean_ctor_get(v_x_3490_, 2);
lean_inc(v_version_3493_);
v_text_3494_ = lean_ctor_get(v_x_3490_, 3);
lean_inc_ref(v_text_3494_);
lean_dec_ref(v_x_3490_);
v___x_3495_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__0));
v___x_3496_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3496_, 0, v_uri_3491_);
v___x_3497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3497_, 0, v___x_3495_);
lean_ctor_set(v___x_3497_, 1, v___x_3496_);
v___x_3498_ = lean_box(0);
v___x_3499_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3499_, 0, v___x_3497_);
lean_ctor_set(v___x_3499_, 1, v___x_3498_);
v___x_3500_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextDocumentItem_toJson___closed__0));
v___x_3501_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3501_, 0, v_languageId_3492_);
v___x_3502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3502_, 0, v___x_3500_);
lean_ctor_set(v___x_3502_, 1, v___x_3501_);
v___x_3503_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3503_, 0, v___x_3502_);
lean_ctor_set(v___x_3503_, 1, v___x_3498_);
v___x_3504_ = ((lean_object*)(l_Lean_Lsp_instToJsonVersionedTextDocumentIdentifier_toJson___closed__0));
v___x_3505_ = l_Lean_JsonNumber_fromNat(v_version_3493_);
v___x_3506_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3506_, 0, v___x_3505_);
v___x_3507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3507_, 0, v___x_3504_);
lean_ctor_set(v___x_3507_, 1, v___x_3506_);
v___x_3508_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3508_, 0, v___x_3507_);
lean_ctor_set(v___x_3508_, 1, v___x_3498_);
v___x_3509_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextDocumentItem_toJson___closed__1));
v___x_3510_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3510_, 0, v_text_3494_);
v___x_3511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3511_, 0, v___x_3509_);
lean_ctor_set(v___x_3511_, 1, v___x_3510_);
v___x_3512_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3512_, 0, v___x_3511_);
lean_ctor_set(v___x_3512_, 1, v___x_3498_);
v___x_3513_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3513_, 0, v___x_3512_);
lean_ctor_set(v___x_3513_, 1, v___x_3498_);
v___x_3514_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3514_, 0, v___x_3508_);
lean_ctor_set(v___x_3514_, 1, v___x_3513_);
v___x_3515_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3515_, 0, v___x_3503_);
lean_ctor_set(v___x_3515_, 1, v___x_3514_);
v___x_3516_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3516_, 0, v___x_3499_);
lean_ctor_set(v___x_3516_, 1, v___x_3515_);
v___x_3517_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__2));
v___x_3518_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLocation_toJson_spec__0(v___x_3516_, v___x_3517_);
v___x_3519_ = l_Lean_Json_mkObj(v___x_3518_);
return v___x_3519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentItem_fromJson_spec__0(lean_object* v_j_3522_, lean_object* v_k_3523_){
_start:
{
lean_object* v___x_3524_; lean_object* v___x_3525_; 
v___x_3524_ = l_Lean_Json_getObjValD(v_j_3522_, v_k_3523_);
v___x_3525_ = l_Lean_Json_getNat_x3f(v___x_3524_);
return v___x_3525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentItem_fromJson_spec__0___boxed(lean_object* v_j_3526_, lean_object* v_k_3527_){
_start:
{
lean_object* v_res_3528_; 
v_res_3528_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentItem_fromJson_spec__0(v_j_3526_, v_k_3527_);
lean_dec_ref(v_k_3527_);
return v_res_3528_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__2(void){
_start:
{
uint8_t v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; 
v___x_3534_ = 1;
v___x_3535_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__1));
v___x_3536_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3535_, v___x_3534_);
return v___x_3536_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__3(void){
_start:
{
lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; 
v___x_3537_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__5));
v___x_3538_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__2, &l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__2);
v___x_3539_ = lean_string_append(v___x_3538_, v___x_3537_);
return v___x_3539_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__4(void){
_start:
{
lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; 
v___x_3540_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLocation_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLocation_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLocation_fromJson___closed__8);
v___x_3541_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__3, &l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__3);
v___x_3542_ = lean_string_append(v___x_3541_, v___x_3540_);
return v___x_3542_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__5(void){
_start:
{
lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; 
v___x_3543_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_3544_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__4, &l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__4);
v___x_3545_ = lean_string_append(v___x_3544_, v___x_3543_);
return v___x_3545_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__7(void){
_start:
{
uint8_t v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; 
v___x_3548_ = 1;
v___x_3549_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__6));
v___x_3550_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3549_, v___x_3548_);
return v___x_3550_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__8(void){
_start:
{
lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; 
v___x_3551_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__7, &l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__7);
v___x_3552_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__3, &l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__3);
v___x_3553_ = lean_string_append(v___x_3552_, v___x_3551_);
return v___x_3553_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__9(void){
_start:
{
lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; 
v___x_3554_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_3555_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__8, &l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__8);
v___x_3556_ = lean_string_append(v___x_3555_, v___x_3554_);
return v___x_3556_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__11(void){
_start:
{
uint8_t v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; 
v___x_3559_ = 1;
v___x_3560_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__10));
v___x_3561_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3560_, v___x_3559_);
return v___x_3561_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__12(void){
_start:
{
lean_object* v___x_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; 
v___x_3562_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__11, &l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__11);
v___x_3563_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__3, &l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__3);
v___x_3564_ = lean_string_append(v___x_3563_, v___x_3562_);
return v___x_3564_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__13(void){
_start:
{
lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; 
v___x_3565_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_3566_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__12, &l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__12);
v___x_3567_ = lean_string_append(v___x_3566_, v___x_3565_);
return v___x_3567_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__15(void){
_start:
{
uint8_t v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; 
v___x_3570_ = 1;
v___x_3571_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__14));
v___x_3572_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3571_, v___x_3570_);
return v___x_3572_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__16(void){
_start:
{
lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; 
v___x_3573_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__15, &l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__15_once, _init_l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__15);
v___x_3574_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__3, &l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__3);
v___x_3575_ = lean_string_append(v___x_3574_, v___x_3573_);
return v___x_3575_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__17(void){
_start:
{
lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; 
v___x_3576_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_3577_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__16, &l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__16_once, _init_l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__16);
v___x_3578_ = lean_string_append(v___x_3577_, v___x_3576_);
return v___x_3578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson(lean_object* v_json_3579_){
_start:
{
lean_object* v___x_3580_; lean_object* v___x_3581_; 
v___x_3580_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__0));
lean_inc(v_json_3579_);
v___x_3581_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocation_fromJson_spec__0(v_json_3579_, v___x_3580_);
if (lean_obj_tag(v___x_3581_) == 0)
{
lean_object* v_a_3582_; lean_object* v___x_3584_; uint8_t v_isShared_3585_; uint8_t v_isSharedCheck_3591_; 
lean_dec(v_json_3579_);
v_a_3582_ = lean_ctor_get(v___x_3581_, 0);
v_isSharedCheck_3591_ = !lean_is_exclusive(v___x_3581_);
if (v_isSharedCheck_3591_ == 0)
{
v___x_3584_ = v___x_3581_;
v_isShared_3585_ = v_isSharedCheck_3591_;
goto v_resetjp_3583_;
}
else
{
lean_inc(v_a_3582_);
lean_dec(v___x_3581_);
v___x_3584_ = lean_box(0);
v_isShared_3585_ = v_isSharedCheck_3591_;
goto v_resetjp_3583_;
}
v_resetjp_3583_:
{
lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3589_; 
v___x_3586_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__5, &l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__5);
v___x_3587_ = lean_string_append(v___x_3586_, v_a_3582_);
lean_dec(v_a_3582_);
if (v_isShared_3585_ == 0)
{
lean_ctor_set(v___x_3584_, 0, v___x_3587_);
v___x_3589_ = v___x_3584_;
goto v_reusejp_3588_;
}
else
{
lean_object* v_reuseFailAlloc_3590_; 
v_reuseFailAlloc_3590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3590_, 0, v___x_3587_);
v___x_3589_ = v_reuseFailAlloc_3590_;
goto v_reusejp_3588_;
}
v_reusejp_3588_:
{
return v___x_3589_;
}
}
}
else
{
if (lean_obj_tag(v___x_3581_) == 0)
{
lean_object* v_a_3592_; lean_object* v___x_3594_; uint8_t v_isShared_3595_; uint8_t v_isSharedCheck_3599_; 
lean_dec(v_json_3579_);
v_a_3592_ = lean_ctor_get(v___x_3581_, 0);
v_isSharedCheck_3599_ = !lean_is_exclusive(v___x_3581_);
if (v_isSharedCheck_3599_ == 0)
{
v___x_3594_ = v___x_3581_;
v_isShared_3595_ = v_isSharedCheck_3599_;
goto v_resetjp_3593_;
}
else
{
lean_inc(v_a_3592_);
lean_dec(v___x_3581_);
v___x_3594_ = lean_box(0);
v_isShared_3595_ = v_isSharedCheck_3599_;
goto v_resetjp_3593_;
}
v_resetjp_3593_:
{
lean_object* v___x_3597_; 
if (v_isShared_3595_ == 0)
{
lean_ctor_set_tag(v___x_3594_, 0);
v___x_3597_ = v___x_3594_;
goto v_reusejp_3596_;
}
else
{
lean_object* v_reuseFailAlloc_3598_; 
v_reuseFailAlloc_3598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3598_, 0, v_a_3592_);
v___x_3597_ = v_reuseFailAlloc_3598_;
goto v_reusejp_3596_;
}
v_reusejp_3596_:
{
return v___x_3597_;
}
}
}
else
{
lean_object* v_a_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; 
v_a_3600_ = lean_ctor_get(v___x_3581_, 0);
lean_inc(v_a_3600_);
lean_dec_ref(v___x_3581_);
v___x_3601_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextDocumentItem_toJson___closed__0));
lean_inc(v_json_3579_);
v___x_3602_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocation_fromJson_spec__0(v_json_3579_, v___x_3601_);
if (lean_obj_tag(v___x_3602_) == 0)
{
lean_object* v_a_3603_; lean_object* v___x_3605_; uint8_t v_isShared_3606_; uint8_t v_isSharedCheck_3612_; 
lean_dec(v_a_3600_);
lean_dec(v_json_3579_);
v_a_3603_ = lean_ctor_get(v___x_3602_, 0);
v_isSharedCheck_3612_ = !lean_is_exclusive(v___x_3602_);
if (v_isSharedCheck_3612_ == 0)
{
v___x_3605_ = v___x_3602_;
v_isShared_3606_ = v_isSharedCheck_3612_;
goto v_resetjp_3604_;
}
else
{
lean_inc(v_a_3603_);
lean_dec(v___x_3602_);
v___x_3605_ = lean_box(0);
v_isShared_3606_ = v_isSharedCheck_3612_;
goto v_resetjp_3604_;
}
v_resetjp_3604_:
{
lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3610_; 
v___x_3607_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__9, &l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__9);
v___x_3608_ = lean_string_append(v___x_3607_, v_a_3603_);
lean_dec(v_a_3603_);
if (v_isShared_3606_ == 0)
{
lean_ctor_set(v___x_3605_, 0, v___x_3608_);
v___x_3610_ = v___x_3605_;
goto v_reusejp_3609_;
}
else
{
lean_object* v_reuseFailAlloc_3611_; 
v_reuseFailAlloc_3611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3611_, 0, v___x_3608_);
v___x_3610_ = v_reuseFailAlloc_3611_;
goto v_reusejp_3609_;
}
v_reusejp_3609_:
{
return v___x_3610_;
}
}
}
else
{
if (lean_obj_tag(v___x_3602_) == 0)
{
lean_object* v_a_3613_; lean_object* v___x_3615_; uint8_t v_isShared_3616_; uint8_t v_isSharedCheck_3620_; 
lean_dec(v_a_3600_);
lean_dec(v_json_3579_);
v_a_3613_ = lean_ctor_get(v___x_3602_, 0);
v_isSharedCheck_3620_ = !lean_is_exclusive(v___x_3602_);
if (v_isSharedCheck_3620_ == 0)
{
v___x_3615_ = v___x_3602_;
v_isShared_3616_ = v_isSharedCheck_3620_;
goto v_resetjp_3614_;
}
else
{
lean_inc(v_a_3613_);
lean_dec(v___x_3602_);
v___x_3615_ = lean_box(0);
v_isShared_3616_ = v_isSharedCheck_3620_;
goto v_resetjp_3614_;
}
v_resetjp_3614_:
{
lean_object* v___x_3618_; 
if (v_isShared_3616_ == 0)
{
lean_ctor_set_tag(v___x_3615_, 0);
v___x_3618_ = v___x_3615_;
goto v_reusejp_3617_;
}
else
{
lean_object* v_reuseFailAlloc_3619_; 
v_reuseFailAlloc_3619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3619_, 0, v_a_3613_);
v___x_3618_ = v_reuseFailAlloc_3619_;
goto v_reusejp_3617_;
}
v_reusejp_3617_:
{
return v___x_3618_;
}
}
}
else
{
lean_object* v_a_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; 
v_a_3621_ = lean_ctor_get(v___x_3602_, 0);
lean_inc(v_a_3621_);
lean_dec_ref(v___x_3602_);
v___x_3622_ = ((lean_object*)(l_Lean_Lsp_instToJsonVersionedTextDocumentIdentifier_toJson___closed__0));
lean_inc(v_json_3579_);
v___x_3623_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentItem_fromJson_spec__0(v_json_3579_, v___x_3622_);
if (lean_obj_tag(v___x_3623_) == 0)
{
lean_object* v_a_3624_; lean_object* v___x_3626_; uint8_t v_isShared_3627_; uint8_t v_isSharedCheck_3633_; 
lean_dec(v_a_3621_);
lean_dec(v_a_3600_);
lean_dec(v_json_3579_);
v_a_3624_ = lean_ctor_get(v___x_3623_, 0);
v_isSharedCheck_3633_ = !lean_is_exclusive(v___x_3623_);
if (v_isSharedCheck_3633_ == 0)
{
v___x_3626_ = v___x_3623_;
v_isShared_3627_ = v_isSharedCheck_3633_;
goto v_resetjp_3625_;
}
else
{
lean_inc(v_a_3624_);
lean_dec(v___x_3623_);
v___x_3626_ = lean_box(0);
v_isShared_3627_ = v_isSharedCheck_3633_;
goto v_resetjp_3625_;
}
v_resetjp_3625_:
{
lean_object* v___x_3628_; lean_object* v___x_3629_; lean_object* v___x_3631_; 
v___x_3628_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__13, &l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__13);
v___x_3629_ = lean_string_append(v___x_3628_, v_a_3624_);
lean_dec(v_a_3624_);
if (v_isShared_3627_ == 0)
{
lean_ctor_set(v___x_3626_, 0, v___x_3629_);
v___x_3631_ = v___x_3626_;
goto v_reusejp_3630_;
}
else
{
lean_object* v_reuseFailAlloc_3632_; 
v_reuseFailAlloc_3632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3632_, 0, v___x_3629_);
v___x_3631_ = v_reuseFailAlloc_3632_;
goto v_reusejp_3630_;
}
v_reusejp_3630_:
{
return v___x_3631_;
}
}
}
else
{
if (lean_obj_tag(v___x_3623_) == 0)
{
lean_object* v_a_3634_; lean_object* v___x_3636_; uint8_t v_isShared_3637_; uint8_t v_isSharedCheck_3641_; 
lean_dec(v_a_3621_);
lean_dec(v_a_3600_);
lean_dec(v_json_3579_);
v_a_3634_ = lean_ctor_get(v___x_3623_, 0);
v_isSharedCheck_3641_ = !lean_is_exclusive(v___x_3623_);
if (v_isSharedCheck_3641_ == 0)
{
v___x_3636_ = v___x_3623_;
v_isShared_3637_ = v_isSharedCheck_3641_;
goto v_resetjp_3635_;
}
else
{
lean_inc(v_a_3634_);
lean_dec(v___x_3623_);
v___x_3636_ = lean_box(0);
v_isShared_3637_ = v_isSharedCheck_3641_;
goto v_resetjp_3635_;
}
v_resetjp_3635_:
{
lean_object* v___x_3639_; 
if (v_isShared_3637_ == 0)
{
lean_ctor_set_tag(v___x_3636_, 0);
v___x_3639_ = v___x_3636_;
goto v_reusejp_3638_;
}
else
{
lean_object* v_reuseFailAlloc_3640_; 
v_reuseFailAlloc_3640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3640_, 0, v_a_3634_);
v___x_3639_ = v_reuseFailAlloc_3640_;
goto v_reusejp_3638_;
}
v_reusejp_3638_:
{
return v___x_3639_;
}
}
}
else
{
lean_object* v_a_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; 
v_a_3642_ = lean_ctor_get(v___x_3623_, 0);
lean_inc(v_a_3642_);
lean_dec_ref(v___x_3623_);
v___x_3643_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextDocumentItem_toJson___closed__1));
v___x_3644_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocation_fromJson_spec__0(v_json_3579_, v___x_3643_);
if (lean_obj_tag(v___x_3644_) == 0)
{
lean_object* v_a_3645_; lean_object* v___x_3647_; uint8_t v_isShared_3648_; uint8_t v_isSharedCheck_3654_; 
lean_dec(v_a_3642_);
lean_dec(v_a_3621_);
lean_dec(v_a_3600_);
v_a_3645_ = lean_ctor_get(v___x_3644_, 0);
v_isSharedCheck_3654_ = !lean_is_exclusive(v___x_3644_);
if (v_isSharedCheck_3654_ == 0)
{
v___x_3647_ = v___x_3644_;
v_isShared_3648_ = v_isSharedCheck_3654_;
goto v_resetjp_3646_;
}
else
{
lean_inc(v_a_3645_);
lean_dec(v___x_3644_);
v___x_3647_ = lean_box(0);
v_isShared_3648_ = v_isSharedCheck_3654_;
goto v_resetjp_3646_;
}
v_resetjp_3646_:
{
lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3652_; 
v___x_3649_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__17, &l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__17_once, _init_l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__17);
v___x_3650_ = lean_string_append(v___x_3649_, v_a_3645_);
lean_dec(v_a_3645_);
if (v_isShared_3648_ == 0)
{
lean_ctor_set(v___x_3647_, 0, v___x_3650_);
v___x_3652_ = v___x_3647_;
goto v_reusejp_3651_;
}
else
{
lean_object* v_reuseFailAlloc_3653_; 
v_reuseFailAlloc_3653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3653_, 0, v___x_3650_);
v___x_3652_ = v_reuseFailAlloc_3653_;
goto v_reusejp_3651_;
}
v_reusejp_3651_:
{
return v___x_3652_;
}
}
}
else
{
if (lean_obj_tag(v___x_3644_) == 0)
{
lean_object* v_a_3655_; lean_object* v___x_3657_; uint8_t v_isShared_3658_; uint8_t v_isSharedCheck_3662_; 
lean_dec(v_a_3642_);
lean_dec(v_a_3621_);
lean_dec(v_a_3600_);
v_a_3655_ = lean_ctor_get(v___x_3644_, 0);
v_isSharedCheck_3662_ = !lean_is_exclusive(v___x_3644_);
if (v_isSharedCheck_3662_ == 0)
{
v___x_3657_ = v___x_3644_;
v_isShared_3658_ = v_isSharedCheck_3662_;
goto v_resetjp_3656_;
}
else
{
lean_inc(v_a_3655_);
lean_dec(v___x_3644_);
v___x_3657_ = lean_box(0);
v_isShared_3658_ = v_isSharedCheck_3662_;
goto v_resetjp_3656_;
}
v_resetjp_3656_:
{
lean_object* v___x_3660_; 
if (v_isShared_3658_ == 0)
{
lean_ctor_set_tag(v___x_3657_, 0);
v___x_3660_ = v___x_3657_;
goto v_reusejp_3659_;
}
else
{
lean_object* v_reuseFailAlloc_3661_; 
v_reuseFailAlloc_3661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3661_, 0, v_a_3655_);
v___x_3660_ = v_reuseFailAlloc_3661_;
goto v_reusejp_3659_;
}
v_reusejp_3659_:
{
return v___x_3660_;
}
}
}
else
{
lean_object* v_a_3663_; lean_object* v___x_3665_; uint8_t v_isShared_3666_; uint8_t v_isSharedCheck_3671_; 
v_a_3663_ = lean_ctor_get(v___x_3644_, 0);
v_isSharedCheck_3671_ = !lean_is_exclusive(v___x_3644_);
if (v_isSharedCheck_3671_ == 0)
{
v___x_3665_ = v___x_3644_;
v_isShared_3666_ = v_isSharedCheck_3671_;
goto v_resetjp_3664_;
}
else
{
lean_inc(v_a_3663_);
lean_dec(v___x_3644_);
v___x_3665_ = lean_box(0);
v_isShared_3666_ = v_isSharedCheck_3671_;
goto v_resetjp_3664_;
}
v_resetjp_3664_:
{
lean_object* v___x_3667_; lean_object* v___x_3669_; 
v___x_3667_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3667_, 0, v_a_3600_);
lean_ctor_set(v___x_3667_, 1, v_a_3621_);
lean_ctor_set(v___x_3667_, 2, v_a_3642_);
lean_ctor_set(v___x_3667_, 3, v_a_3663_);
if (v_isShared_3666_ == 0)
{
lean_ctor_set(v___x_3665_, 0, v___x_3667_);
v___x_3669_ = v___x_3665_;
goto v_reusejp_3668_;
}
else
{
lean_object* v_reuseFailAlloc_3670_; 
v_reuseFailAlloc_3670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3670_, 0, v___x_3667_);
v___x_3669_ = v_reuseFailAlloc_3670_;
goto v_reusejp_3668_;
}
v_reusejp_3668_:
{
return v___x_3669_;
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
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonTextDocumentPositionParams_toJson(lean_object* v_x_3675_){
_start:
{
lean_object* v_textDocument_3676_; lean_object* v_position_3677_; lean_object* v___x_3679_; uint8_t v_isShared_3680_; uint8_t v_isSharedCheck_3697_; 
v_textDocument_3676_ = lean_ctor_get(v_x_3675_, 0);
v_position_3677_ = lean_ctor_get(v_x_3675_, 1);
v_isSharedCheck_3697_ = !lean_is_exclusive(v_x_3675_);
if (v_isSharedCheck_3697_ == 0)
{
v___x_3679_ = v_x_3675_;
v_isShared_3680_ = v_isSharedCheck_3697_;
goto v_resetjp_3678_;
}
else
{
lean_inc(v_position_3677_);
lean_inc(v_textDocument_3676_);
lean_dec(v_x_3675_);
v___x_3679_ = lean_box(0);
v_isShared_3680_ = v_isSharedCheck_3697_;
goto v_resetjp_3678_;
}
v_resetjp_3678_:
{
lean_object* v___x_3681_; lean_object* v___x_3682_; lean_object* v___x_3684_; 
v___x_3681_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextDocumentEdit_toJson___closed__0));
v___x_3682_ = l_Lean_Lsp_instToJsonTextDocumentIdentifier_toJson(v_textDocument_3676_);
if (v_isShared_3680_ == 0)
{
lean_ctor_set(v___x_3679_, 1, v___x_3682_);
lean_ctor_set(v___x_3679_, 0, v___x_3681_);
v___x_3684_ = v___x_3679_;
goto v_reusejp_3683_;
}
else
{
lean_object* v_reuseFailAlloc_3696_; 
v_reuseFailAlloc_3696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3696_, 0, v___x_3681_);
lean_ctor_set(v_reuseFailAlloc_3696_, 1, v___x_3682_);
v___x_3684_ = v_reuseFailAlloc_3696_;
goto v_reusejp_3683_;
}
v_reusejp_3683_:
{
lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; 
v___x_3685_ = lean_box(0);
v___x_3686_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3686_, 0, v___x_3684_);
lean_ctor_set(v___x_3686_, 1, v___x_3685_);
v___x_3687_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextDocumentPositionParams_toJson___closed__0));
v___x_3688_ = l_Lean_Lsp_instToJsonPosition_toJson(v_position_3677_);
v___x_3689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3689_, 0, v___x_3687_);
lean_ctor_set(v___x_3689_, 1, v___x_3688_);
v___x_3690_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3690_, 0, v___x_3689_);
lean_ctor_set(v___x_3690_, 1, v___x_3685_);
v___x_3691_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3691_, 0, v___x_3690_);
lean_ctor_set(v___x_3691_, 1, v___x_3685_);
v___x_3692_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3692_, 0, v___x_3686_);
lean_ctor_set(v___x_3692_, 1, v___x_3691_);
v___x_3693_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__2));
v___x_3694_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLocation_toJson_spec__0(v___x_3692_, v___x_3693_);
v___x_3695_ = l_Lean_Json_mkObj(v___x_3694_);
return v___x_3695_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson_spec__0(lean_object* v_j_3700_, lean_object* v_k_3701_){
_start:
{
lean_object* v___x_3702_; lean_object* v___x_3703_; 
v___x_3702_ = l_Lean_Json_getObjValD(v_j_3700_, v_k_3701_);
v___x_3703_ = l_Lean_Lsp_instFromJsonTextDocumentIdentifier_fromJson(v___x_3702_);
return v___x_3703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson_spec__0___boxed(lean_object* v_j_3704_, lean_object* v_k_3705_){
_start:
{
lean_object* v_res_3706_; 
v_res_3706_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson_spec__0(v_j_3704_, v_k_3705_);
lean_dec_ref(v_k_3705_);
return v_res_3706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson_spec__1(lean_object* v_j_3707_, lean_object* v_k_3708_){
_start:
{
lean_object* v___x_3709_; lean_object* v___x_3710_; 
v___x_3709_ = l_Lean_Json_getObjValD(v_j_3707_, v_k_3708_);
v___x_3710_ = l_Lean_Lsp_instFromJsonPosition_fromJson(v___x_3709_);
return v___x_3710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson_spec__1___boxed(lean_object* v_j_3711_, lean_object* v_k_3712_){
_start:
{
lean_object* v_res_3713_; 
v_res_3713_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson_spec__1(v_j_3711_, v_k_3712_);
lean_dec_ref(v_k_3712_);
return v_res_3713_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__2(void){
_start:
{
uint8_t v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; 
v___x_3719_ = 1;
v___x_3720_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__1));
v___x_3721_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3720_, v___x_3719_);
return v___x_3721_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__3(void){
_start:
{
lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; 
v___x_3722_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__5));
v___x_3723_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__2, &l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__2);
v___x_3724_ = lean_string_append(v___x_3723_, v___x_3722_);
return v___x_3724_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; 
v___x_3725_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__5, &l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__5);
v___x_3726_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__3);
v___x_3727_ = lean_string_append(v___x_3726_, v___x_3725_);
return v___x_3727_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__5(void){
_start:
{
lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; 
v___x_3728_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_3729_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__4);
v___x_3730_ = lean_string_append(v___x_3729_, v___x_3728_);
return v___x_3730_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__7(void){
_start:
{
uint8_t v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; 
v___x_3733_ = 1;
v___x_3734_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__6));
v___x_3735_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3734_, v___x_3733_);
return v___x_3735_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__8(void){
_start:
{
lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; 
v___x_3736_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__7);
v___x_3737_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__3);
v___x_3738_ = lean_string_append(v___x_3737_, v___x_3736_);
return v___x_3738_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__9(void){
_start:
{
lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; 
v___x_3739_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_3740_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__8);
v___x_3741_ = lean_string_append(v___x_3740_, v___x_3739_);
return v___x_3741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson(lean_object* v_json_3742_){
_start:
{
lean_object* v___x_3743_; lean_object* v___x_3744_; 
v___x_3743_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextDocumentEdit_toJson___closed__0));
lean_inc(v_json_3742_);
v___x_3744_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson_spec__0(v_json_3742_, v___x_3743_);
if (lean_obj_tag(v___x_3744_) == 0)
{
lean_object* v_a_3745_; lean_object* v___x_3747_; uint8_t v_isShared_3748_; uint8_t v_isSharedCheck_3754_; 
lean_dec(v_json_3742_);
v_a_3745_ = lean_ctor_get(v___x_3744_, 0);
v_isSharedCheck_3754_ = !lean_is_exclusive(v___x_3744_);
if (v_isSharedCheck_3754_ == 0)
{
v___x_3747_ = v___x_3744_;
v_isShared_3748_ = v_isSharedCheck_3754_;
goto v_resetjp_3746_;
}
else
{
lean_inc(v_a_3745_);
lean_dec(v___x_3744_);
v___x_3747_ = lean_box(0);
v_isShared_3748_ = v_isSharedCheck_3754_;
goto v_resetjp_3746_;
}
v_resetjp_3746_:
{
lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3752_; 
v___x_3749_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__5, &l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__5);
v___x_3750_ = lean_string_append(v___x_3749_, v_a_3745_);
lean_dec(v_a_3745_);
if (v_isShared_3748_ == 0)
{
lean_ctor_set(v___x_3747_, 0, v___x_3750_);
v___x_3752_ = v___x_3747_;
goto v_reusejp_3751_;
}
else
{
lean_object* v_reuseFailAlloc_3753_; 
v_reuseFailAlloc_3753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3753_, 0, v___x_3750_);
v___x_3752_ = v_reuseFailAlloc_3753_;
goto v_reusejp_3751_;
}
v_reusejp_3751_:
{
return v___x_3752_;
}
}
}
else
{
if (lean_obj_tag(v___x_3744_) == 0)
{
lean_object* v_a_3755_; lean_object* v___x_3757_; uint8_t v_isShared_3758_; uint8_t v_isSharedCheck_3762_; 
lean_dec(v_json_3742_);
v_a_3755_ = lean_ctor_get(v___x_3744_, 0);
v_isSharedCheck_3762_ = !lean_is_exclusive(v___x_3744_);
if (v_isSharedCheck_3762_ == 0)
{
v___x_3757_ = v___x_3744_;
v_isShared_3758_ = v_isSharedCheck_3762_;
goto v_resetjp_3756_;
}
else
{
lean_inc(v_a_3755_);
lean_dec(v___x_3744_);
v___x_3757_ = lean_box(0);
v_isShared_3758_ = v_isSharedCheck_3762_;
goto v_resetjp_3756_;
}
v_resetjp_3756_:
{
lean_object* v___x_3760_; 
if (v_isShared_3758_ == 0)
{
lean_ctor_set_tag(v___x_3757_, 0);
v___x_3760_ = v___x_3757_;
goto v_reusejp_3759_;
}
else
{
lean_object* v_reuseFailAlloc_3761_; 
v_reuseFailAlloc_3761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3761_, 0, v_a_3755_);
v___x_3760_ = v_reuseFailAlloc_3761_;
goto v_reusejp_3759_;
}
v_reusejp_3759_:
{
return v___x_3760_;
}
}
}
else
{
lean_object* v_a_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; 
v_a_3763_ = lean_ctor_get(v___x_3744_, 0);
lean_inc(v_a_3763_);
lean_dec_ref(v___x_3744_);
v___x_3764_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextDocumentPositionParams_toJson___closed__0));
v___x_3765_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson_spec__1(v_json_3742_, v___x_3764_);
if (lean_obj_tag(v___x_3765_) == 0)
{
lean_object* v_a_3766_; lean_object* v___x_3768_; uint8_t v_isShared_3769_; uint8_t v_isSharedCheck_3775_; 
lean_dec(v_a_3763_);
v_a_3766_ = lean_ctor_get(v___x_3765_, 0);
v_isSharedCheck_3775_ = !lean_is_exclusive(v___x_3765_);
if (v_isSharedCheck_3775_ == 0)
{
v___x_3768_ = v___x_3765_;
v_isShared_3769_ = v_isSharedCheck_3775_;
goto v_resetjp_3767_;
}
else
{
lean_inc(v_a_3766_);
lean_dec(v___x_3765_);
v___x_3768_ = lean_box(0);
v_isShared_3769_ = v_isSharedCheck_3775_;
goto v_resetjp_3767_;
}
v_resetjp_3767_:
{
lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3773_; 
v___x_3770_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__9, &l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__9);
v___x_3771_ = lean_string_append(v___x_3770_, v_a_3766_);
lean_dec(v_a_3766_);
if (v_isShared_3769_ == 0)
{
lean_ctor_set(v___x_3768_, 0, v___x_3771_);
v___x_3773_ = v___x_3768_;
goto v_reusejp_3772_;
}
else
{
lean_object* v_reuseFailAlloc_3774_; 
v_reuseFailAlloc_3774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3774_, 0, v___x_3771_);
v___x_3773_ = v_reuseFailAlloc_3774_;
goto v_reusejp_3772_;
}
v_reusejp_3772_:
{
return v___x_3773_;
}
}
}
else
{
if (lean_obj_tag(v___x_3765_) == 0)
{
lean_object* v_a_3776_; lean_object* v___x_3778_; uint8_t v_isShared_3779_; uint8_t v_isSharedCheck_3783_; 
lean_dec(v_a_3763_);
v_a_3776_ = lean_ctor_get(v___x_3765_, 0);
v_isSharedCheck_3783_ = !lean_is_exclusive(v___x_3765_);
if (v_isSharedCheck_3783_ == 0)
{
v___x_3778_ = v___x_3765_;
v_isShared_3779_ = v_isSharedCheck_3783_;
goto v_resetjp_3777_;
}
else
{
lean_inc(v_a_3776_);
lean_dec(v___x_3765_);
v___x_3778_ = lean_box(0);
v_isShared_3779_ = v_isSharedCheck_3783_;
goto v_resetjp_3777_;
}
v_resetjp_3777_:
{
lean_object* v___x_3781_; 
if (v_isShared_3779_ == 0)
{
lean_ctor_set_tag(v___x_3778_, 0);
v___x_3781_ = v___x_3778_;
goto v_reusejp_3780_;
}
else
{
lean_object* v_reuseFailAlloc_3782_; 
v_reuseFailAlloc_3782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3782_, 0, v_a_3776_);
v___x_3781_ = v_reuseFailAlloc_3782_;
goto v_reusejp_3780_;
}
v_reusejp_3780_:
{
return v___x_3781_;
}
}
}
else
{
lean_object* v_a_3784_; lean_object* v___x_3786_; uint8_t v_isShared_3787_; uint8_t v_isSharedCheck_3792_; 
v_a_3784_ = lean_ctor_get(v___x_3765_, 0);
v_isSharedCheck_3792_ = !lean_is_exclusive(v___x_3765_);
if (v_isSharedCheck_3792_ == 0)
{
v___x_3786_ = v___x_3765_;
v_isShared_3787_ = v_isSharedCheck_3792_;
goto v_resetjp_3785_;
}
else
{
lean_inc(v_a_3784_);
lean_dec(v___x_3765_);
v___x_3786_ = lean_box(0);
v_isShared_3787_ = v_isSharedCheck_3792_;
goto v_resetjp_3785_;
}
v_resetjp_3785_:
{
lean_object* v___x_3788_; lean_object* v___x_3790_; 
v___x_3788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3788_, 0, v_a_3763_);
lean_ctor_set(v___x_3788_, 1, v_a_3784_);
if (v_isShared_3787_ == 0)
{
lean_ctor_set(v___x_3786_, 0, v___x_3788_);
v___x_3790_ = v___x_3786_;
goto v_reusejp_3789_;
}
else
{
lean_object* v_reuseFailAlloc_3791_; 
v_reuseFailAlloc_3791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3791_, 0, v___x_3788_);
v___x_3790_ = v_reuseFailAlloc_3791_;
goto v_reusejp_3789_;
}
v_reusejp_3789_:
{
return v___x_3790_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToStringTextDocumentPositionParams___lam__0(lean_object* v_p_3796_){
_start:
{
lean_object* v_position_3797_; lean_object* v_textDocument_3798_; lean_object* v_line_3799_; lean_object* v_character_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; 
v_position_3797_ = lean_ctor_get(v_p_3796_, 1);
lean_inc_ref(v_position_3797_);
v_textDocument_3798_ = lean_ctor_get(v_p_3796_, 0);
lean_inc_ref(v_textDocument_3798_);
lean_dec_ref(v_p_3796_);
v_line_3799_ = lean_ctor_get(v_position_3797_, 0);
lean_inc(v_line_3799_);
v_character_3800_ = lean_ctor_get(v_position_3797_, 1);
lean_inc(v_character_3800_);
lean_dec_ref(v_position_3797_);
v___x_3801_ = ((lean_object*)(l_Lean_Lsp_instToStringTextDocumentPositionParams___lam__0___closed__0));
v___x_3802_ = lean_string_append(v_textDocument_3798_, v___x_3801_);
v___x_3803_ = l_Nat_reprFast(v_line_3799_);
v___x_3804_ = lean_string_append(v___x_3802_, v___x_3803_);
lean_dec_ref(v___x_3803_);
v___x_3805_ = lean_string_append(v___x_3804_, v___x_3801_);
v___x_3806_ = l_Nat_reprFast(v_character_3800_);
v___x_3807_ = lean_string_append(v___x_3805_, v___x_3806_);
lean_dec_ref(v___x_3806_);
return v___x_3807_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDocumentFilter_toJson(lean_object* v_x_3813_){
_start:
{
lean_object* v_language_x3f_3814_; lean_object* v_scheme_x3f_3815_; lean_object* v_pattern_x3f_3816_; lean_object* v___x_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; 
v_language_x3f_3814_ = lean_ctor_get(v_x_3813_, 0);
lean_inc(v_language_x3f_3814_);
v_scheme_x3f_3815_ = lean_ctor_get(v_x_3813_, 1);
lean_inc(v_scheme_x3f_3815_);
v_pattern_x3f_3816_ = lean_ctor_get(v_x_3813_, 2);
lean_inc(v_pattern_x3f_3816_);
lean_dec_ref(v_x_3813_);
v___x_3817_ = ((lean_object*)(l_Lean_Lsp_instToJsonDocumentFilter_toJson___closed__0));
v___x_3818_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextEdit_toJson_spec__1(v___x_3817_, v_language_x3f_3814_);
v___x_3819_ = ((lean_object*)(l_Lean_Lsp_instToJsonDocumentFilter_toJson___closed__1));
v___x_3820_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextEdit_toJson_spec__1(v___x_3819_, v_scheme_x3f_3815_);
v___x_3821_ = ((lean_object*)(l_Lean_Lsp_instToJsonDocumentFilter_toJson___closed__2));
v___x_3822_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextEdit_toJson_spec__1(v___x_3821_, v_pattern_x3f_3816_);
v___x_3823_ = lean_box(0);
v___x_3824_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3824_, 0, v___x_3822_);
lean_ctor_set(v___x_3824_, 1, v___x_3823_);
v___x_3825_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3825_, 0, v___x_3820_);
lean_ctor_set(v___x_3825_, 1, v___x_3824_);
v___x_3826_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3826_, 0, v___x_3818_);
lean_ctor_set(v___x_3826_, 1, v___x_3825_);
v___x_3827_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__2));
v___x_3828_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLocation_toJson_spec__0(v___x_3826_, v___x_3827_);
v___x_3829_ = l_Lean_Json_mkObj(v___x_3828_);
return v___x_3829_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__2(void){
_start:
{
uint8_t v___x_3837_; lean_object* v___x_3838_; lean_object* v___x_3839_; 
v___x_3837_ = 1;
v___x_3838_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__1));
v___x_3839_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3838_, v___x_3837_);
return v___x_3839_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__3(void){
_start:
{
lean_object* v___x_3840_; lean_object* v___x_3841_; lean_object* v___x_3842_; 
v___x_3840_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__5));
v___x_3841_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__2, &l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__2);
v___x_3842_ = lean_string_append(v___x_3841_, v___x_3840_);
return v___x_3842_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__6(void){
_start:
{
uint8_t v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; 
v___x_3846_ = 1;
v___x_3847_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__5));
v___x_3848_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3847_, v___x_3846_);
return v___x_3848_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__7(void){
_start:
{
lean_object* v___x_3849_; lean_object* v___x_3850_; lean_object* v___x_3851_; 
v___x_3849_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__6, &l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__6);
v___x_3850_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__3, &l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__3);
v___x_3851_ = lean_string_append(v___x_3850_, v___x_3849_);
return v___x_3851_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__8(void){
_start:
{
lean_object* v___x_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; 
v___x_3852_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_3853_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__7, &l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__7);
v___x_3854_ = lean_string_append(v___x_3853_, v___x_3852_);
return v___x_3854_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__11(void){
_start:
{
uint8_t v___x_3858_; lean_object* v___x_3859_; lean_object* v___x_3860_; 
v___x_3858_ = 1;
v___x_3859_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__10));
v___x_3860_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3859_, v___x_3858_);
return v___x_3860_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__12(void){
_start:
{
lean_object* v___x_3861_; lean_object* v___x_3862_; lean_object* v___x_3863_; 
v___x_3861_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__11, &l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__11);
v___x_3862_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__3, &l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__3);
v___x_3863_ = lean_string_append(v___x_3862_, v___x_3861_);
return v___x_3863_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__13(void){
_start:
{
lean_object* v___x_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; 
v___x_3864_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_3865_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__12, &l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__12);
v___x_3866_ = lean_string_append(v___x_3865_, v___x_3864_);
return v___x_3866_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__16(void){
_start:
{
uint8_t v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; 
v___x_3870_ = 1;
v___x_3871_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__15));
v___x_3872_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3871_, v___x_3870_);
return v___x_3872_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__17(void){
_start:
{
lean_object* v___x_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; 
v___x_3873_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__16, &l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__16_once, _init_l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__16);
v___x_3874_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__3, &l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__3);
v___x_3875_ = lean_string_append(v___x_3874_, v___x_3873_);
return v___x_3875_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__18(void){
_start:
{
lean_object* v___x_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; 
v___x_3876_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_3877_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__17, &l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__17_once, _init_l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__17);
v___x_3878_ = lean_string_append(v___x_3877_, v___x_3876_);
return v___x_3878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDocumentFilter_fromJson(lean_object* v_json_3879_){
_start:
{
lean_object* v___x_3880_; lean_object* v___x_3881_; 
v___x_3880_ = ((lean_object*)(l_Lean_Lsp_instToJsonDocumentFilter_toJson___closed__0));
lean_inc(v_json_3879_);
v___x_3881_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextEdit_fromJson_spec__1(v_json_3879_, v___x_3880_);
if (lean_obj_tag(v___x_3881_) == 0)
{
lean_object* v_a_3882_; lean_object* v___x_3884_; uint8_t v_isShared_3885_; uint8_t v_isSharedCheck_3891_; 
lean_dec(v_json_3879_);
v_a_3882_ = lean_ctor_get(v___x_3881_, 0);
v_isSharedCheck_3891_ = !lean_is_exclusive(v___x_3881_);
if (v_isSharedCheck_3891_ == 0)
{
v___x_3884_ = v___x_3881_;
v_isShared_3885_ = v_isSharedCheck_3891_;
goto v_resetjp_3883_;
}
else
{
lean_inc(v_a_3882_);
lean_dec(v___x_3881_);
v___x_3884_ = lean_box(0);
v_isShared_3885_ = v_isSharedCheck_3891_;
goto v_resetjp_3883_;
}
v_resetjp_3883_:
{
lean_object* v___x_3886_; lean_object* v___x_3887_; lean_object* v___x_3889_; 
v___x_3886_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__8, &l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__8);
v___x_3887_ = lean_string_append(v___x_3886_, v_a_3882_);
lean_dec(v_a_3882_);
if (v_isShared_3885_ == 0)
{
lean_ctor_set(v___x_3884_, 0, v___x_3887_);
v___x_3889_ = v___x_3884_;
goto v_reusejp_3888_;
}
else
{
lean_object* v_reuseFailAlloc_3890_; 
v_reuseFailAlloc_3890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3890_, 0, v___x_3887_);
v___x_3889_ = v_reuseFailAlloc_3890_;
goto v_reusejp_3888_;
}
v_reusejp_3888_:
{
return v___x_3889_;
}
}
}
else
{
if (lean_obj_tag(v___x_3881_) == 0)
{
lean_object* v_a_3892_; lean_object* v___x_3894_; uint8_t v_isShared_3895_; uint8_t v_isSharedCheck_3899_; 
lean_dec(v_json_3879_);
v_a_3892_ = lean_ctor_get(v___x_3881_, 0);
v_isSharedCheck_3899_ = !lean_is_exclusive(v___x_3881_);
if (v_isSharedCheck_3899_ == 0)
{
v___x_3894_ = v___x_3881_;
v_isShared_3895_ = v_isSharedCheck_3899_;
goto v_resetjp_3893_;
}
else
{
lean_inc(v_a_3892_);
lean_dec(v___x_3881_);
v___x_3894_ = lean_box(0);
v_isShared_3895_ = v_isSharedCheck_3899_;
goto v_resetjp_3893_;
}
v_resetjp_3893_:
{
lean_object* v___x_3897_; 
if (v_isShared_3895_ == 0)
{
lean_ctor_set_tag(v___x_3894_, 0);
v___x_3897_ = v___x_3894_;
goto v_reusejp_3896_;
}
else
{
lean_object* v_reuseFailAlloc_3898_; 
v_reuseFailAlloc_3898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3898_, 0, v_a_3892_);
v___x_3897_ = v_reuseFailAlloc_3898_;
goto v_reusejp_3896_;
}
v_reusejp_3896_:
{
return v___x_3897_;
}
}
}
else
{
lean_object* v_a_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; 
v_a_3900_ = lean_ctor_get(v___x_3881_, 0);
lean_inc(v_a_3900_);
lean_dec_ref(v___x_3881_);
v___x_3901_ = ((lean_object*)(l_Lean_Lsp_instToJsonDocumentFilter_toJson___closed__1));
lean_inc(v_json_3879_);
v___x_3902_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextEdit_fromJson_spec__1(v_json_3879_, v___x_3901_);
if (lean_obj_tag(v___x_3902_) == 0)
{
lean_object* v_a_3903_; lean_object* v___x_3905_; uint8_t v_isShared_3906_; uint8_t v_isSharedCheck_3912_; 
lean_dec(v_a_3900_);
lean_dec(v_json_3879_);
v_a_3903_ = lean_ctor_get(v___x_3902_, 0);
v_isSharedCheck_3912_ = !lean_is_exclusive(v___x_3902_);
if (v_isSharedCheck_3912_ == 0)
{
v___x_3905_ = v___x_3902_;
v_isShared_3906_ = v_isSharedCheck_3912_;
goto v_resetjp_3904_;
}
else
{
lean_inc(v_a_3903_);
lean_dec(v___x_3902_);
v___x_3905_ = lean_box(0);
v_isShared_3906_ = v_isSharedCheck_3912_;
goto v_resetjp_3904_;
}
v_resetjp_3904_:
{
lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3910_; 
v___x_3907_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__13, &l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__13);
v___x_3908_ = lean_string_append(v___x_3907_, v_a_3903_);
lean_dec(v_a_3903_);
if (v_isShared_3906_ == 0)
{
lean_ctor_set(v___x_3905_, 0, v___x_3908_);
v___x_3910_ = v___x_3905_;
goto v_reusejp_3909_;
}
else
{
lean_object* v_reuseFailAlloc_3911_; 
v_reuseFailAlloc_3911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3911_, 0, v___x_3908_);
v___x_3910_ = v_reuseFailAlloc_3911_;
goto v_reusejp_3909_;
}
v_reusejp_3909_:
{
return v___x_3910_;
}
}
}
else
{
if (lean_obj_tag(v___x_3902_) == 0)
{
lean_object* v_a_3913_; lean_object* v___x_3915_; uint8_t v_isShared_3916_; uint8_t v_isSharedCheck_3920_; 
lean_dec(v_a_3900_);
lean_dec(v_json_3879_);
v_a_3913_ = lean_ctor_get(v___x_3902_, 0);
v_isSharedCheck_3920_ = !lean_is_exclusive(v___x_3902_);
if (v_isSharedCheck_3920_ == 0)
{
v___x_3915_ = v___x_3902_;
v_isShared_3916_ = v_isSharedCheck_3920_;
goto v_resetjp_3914_;
}
else
{
lean_inc(v_a_3913_);
lean_dec(v___x_3902_);
v___x_3915_ = lean_box(0);
v_isShared_3916_ = v_isSharedCheck_3920_;
goto v_resetjp_3914_;
}
v_resetjp_3914_:
{
lean_object* v___x_3918_; 
if (v_isShared_3916_ == 0)
{
lean_ctor_set_tag(v___x_3915_, 0);
v___x_3918_ = v___x_3915_;
goto v_reusejp_3917_;
}
else
{
lean_object* v_reuseFailAlloc_3919_; 
v_reuseFailAlloc_3919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3919_, 0, v_a_3913_);
v___x_3918_ = v_reuseFailAlloc_3919_;
goto v_reusejp_3917_;
}
v_reusejp_3917_:
{
return v___x_3918_;
}
}
}
else
{
lean_object* v_a_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; 
v_a_3921_ = lean_ctor_get(v___x_3902_, 0);
lean_inc(v_a_3921_);
lean_dec_ref(v___x_3902_);
v___x_3922_ = ((lean_object*)(l_Lean_Lsp_instToJsonDocumentFilter_toJson___closed__2));
v___x_3923_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextEdit_fromJson_spec__1(v_json_3879_, v___x_3922_);
if (lean_obj_tag(v___x_3923_) == 0)
{
lean_object* v_a_3924_; lean_object* v___x_3926_; uint8_t v_isShared_3927_; uint8_t v_isSharedCheck_3933_; 
lean_dec(v_a_3921_);
lean_dec(v_a_3900_);
v_a_3924_ = lean_ctor_get(v___x_3923_, 0);
v_isSharedCheck_3933_ = !lean_is_exclusive(v___x_3923_);
if (v_isSharedCheck_3933_ == 0)
{
v___x_3926_ = v___x_3923_;
v_isShared_3927_ = v_isSharedCheck_3933_;
goto v_resetjp_3925_;
}
else
{
lean_inc(v_a_3924_);
lean_dec(v___x_3923_);
v___x_3926_ = lean_box(0);
v_isShared_3927_ = v_isSharedCheck_3933_;
goto v_resetjp_3925_;
}
v_resetjp_3925_:
{
lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3931_; 
v___x_3928_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__18, &l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__18_once, _init_l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__18);
v___x_3929_ = lean_string_append(v___x_3928_, v_a_3924_);
lean_dec(v_a_3924_);
if (v_isShared_3927_ == 0)
{
lean_ctor_set(v___x_3926_, 0, v___x_3929_);
v___x_3931_ = v___x_3926_;
goto v_reusejp_3930_;
}
else
{
lean_object* v_reuseFailAlloc_3932_; 
v_reuseFailAlloc_3932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3932_, 0, v___x_3929_);
v___x_3931_ = v_reuseFailAlloc_3932_;
goto v_reusejp_3930_;
}
v_reusejp_3930_:
{
return v___x_3931_;
}
}
}
else
{
if (lean_obj_tag(v___x_3923_) == 0)
{
lean_object* v_a_3934_; lean_object* v___x_3936_; uint8_t v_isShared_3937_; uint8_t v_isSharedCheck_3941_; 
lean_dec(v_a_3921_);
lean_dec(v_a_3900_);
v_a_3934_ = lean_ctor_get(v___x_3923_, 0);
v_isSharedCheck_3941_ = !lean_is_exclusive(v___x_3923_);
if (v_isSharedCheck_3941_ == 0)
{
v___x_3936_ = v___x_3923_;
v_isShared_3937_ = v_isSharedCheck_3941_;
goto v_resetjp_3935_;
}
else
{
lean_inc(v_a_3934_);
lean_dec(v___x_3923_);
v___x_3936_ = lean_box(0);
v_isShared_3937_ = v_isSharedCheck_3941_;
goto v_resetjp_3935_;
}
v_resetjp_3935_:
{
lean_object* v___x_3939_; 
if (v_isShared_3937_ == 0)
{
lean_ctor_set_tag(v___x_3936_, 0);
v___x_3939_ = v___x_3936_;
goto v_reusejp_3938_;
}
else
{
lean_object* v_reuseFailAlloc_3940_; 
v_reuseFailAlloc_3940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3940_, 0, v_a_3934_);
v___x_3939_ = v_reuseFailAlloc_3940_;
goto v_reusejp_3938_;
}
v_reusejp_3938_:
{
return v___x_3939_;
}
}
}
else
{
lean_object* v_a_3942_; lean_object* v___x_3944_; uint8_t v_isShared_3945_; uint8_t v_isSharedCheck_3950_; 
v_a_3942_ = lean_ctor_get(v___x_3923_, 0);
v_isSharedCheck_3950_ = !lean_is_exclusive(v___x_3923_);
if (v_isSharedCheck_3950_ == 0)
{
v___x_3944_ = v___x_3923_;
v_isShared_3945_ = v_isSharedCheck_3950_;
goto v_resetjp_3943_;
}
else
{
lean_inc(v_a_3942_);
lean_dec(v___x_3923_);
v___x_3944_ = lean_box(0);
v_isShared_3945_ = v_isSharedCheck_3950_;
goto v_resetjp_3943_;
}
v_resetjp_3943_:
{
lean_object* v___x_3946_; lean_object* v___x_3948_; 
v___x_3946_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3946_, 0, v_a_3900_);
lean_ctor_set(v___x_3946_, 1, v_a_3921_);
lean_ctor_set(v___x_3946_, 2, v_a_3942_);
if (v_isShared_3945_ == 0)
{
lean_ctor_set(v___x_3944_, 0, v___x_3946_);
v___x_3948_ = v___x_3944_;
goto v_reusejp_3947_;
}
else
{
lean_object* v_reuseFailAlloc_3949_; 
v_reuseFailAlloc_3949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3949_, 0, v___x_3946_);
v___x_3948_ = v_reuseFailAlloc_3949_;
goto v_reusejp_3947_;
}
v_reusejp_3947_:
{
return v___x_3948_;
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
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonStaticRegistrationOptions_toJson(lean_object* v_x_3960_){
_start:
{
lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; 
v___x_3961_ = ((lean_object*)(l_Lean_Lsp_instToJsonStaticRegistrationOptions_toJson___closed__0));
v___x_3962_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextEdit_toJson_spec__1(v___x_3961_, v_x_3960_);
v___x_3963_ = lean_box(0);
v___x_3964_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3964_, 0, v___x_3962_);
lean_ctor_set(v___x_3964_, 1, v___x_3963_);
v___x_3965_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__2));
v___x_3966_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLocation_toJson_spec__0(v___x_3964_, v___x_3965_);
v___x_3967_ = l_Lean_Json_mkObj(v___x_3966_);
return v___x_3967_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonStaticRegistrationOptions_fromJson___closed__2(void){
_start:
{
uint8_t v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; 
v___x_3975_ = 1;
v___x_3976_ = ((lean_object*)(l_Lean_Lsp_instFromJsonStaticRegistrationOptions_fromJson___closed__1));
v___x_3977_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3976_, v___x_3975_);
return v___x_3977_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonStaticRegistrationOptions_fromJson___closed__3(void){
_start:
{
lean_object* v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; 
v___x_3978_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__5));
v___x_3979_ = lean_obj_once(&l_Lean_Lsp_instFromJsonStaticRegistrationOptions_fromJson___closed__2, &l_Lean_Lsp_instFromJsonStaticRegistrationOptions_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonStaticRegistrationOptions_fromJson___closed__2);
v___x_3980_ = lean_string_append(v___x_3979_, v___x_3978_);
return v___x_3980_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonStaticRegistrationOptions_fromJson___closed__6(void){
_start:
{
uint8_t v___x_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; 
v___x_3984_ = 1;
v___x_3985_ = ((lean_object*)(l_Lean_Lsp_instFromJsonStaticRegistrationOptions_fromJson___closed__5));
v___x_3986_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3985_, v___x_3984_);
return v___x_3986_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonStaticRegistrationOptions_fromJson___closed__7(void){
_start:
{
lean_object* v___x_3987_; lean_object* v___x_3988_; lean_object* v___x_3989_; 
v___x_3987_ = lean_obj_once(&l_Lean_Lsp_instFromJsonStaticRegistrationOptions_fromJson___closed__6, &l_Lean_Lsp_instFromJsonStaticRegistrationOptions_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonStaticRegistrationOptions_fromJson___closed__6);
v___x_3988_ = lean_obj_once(&l_Lean_Lsp_instFromJsonStaticRegistrationOptions_fromJson___closed__3, &l_Lean_Lsp_instFromJsonStaticRegistrationOptions_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonStaticRegistrationOptions_fromJson___closed__3);
v___x_3989_ = lean_string_append(v___x_3988_, v___x_3987_);
return v___x_3989_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonStaticRegistrationOptions_fromJson___closed__8(void){
_start:
{
lean_object* v___x_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; 
v___x_3990_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_3991_ = lean_obj_once(&l_Lean_Lsp_instFromJsonStaticRegistrationOptions_fromJson___closed__7, &l_Lean_Lsp_instFromJsonStaticRegistrationOptions_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonStaticRegistrationOptions_fromJson___closed__7);
v___x_3992_ = lean_string_append(v___x_3991_, v___x_3990_);
return v___x_3992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonStaticRegistrationOptions_fromJson(lean_object* v_json_3993_){
_start:
{
lean_object* v___x_3994_; lean_object* v___x_3995_; 
v___x_3994_ = ((lean_object*)(l_Lean_Lsp_instToJsonStaticRegistrationOptions_toJson___closed__0));
v___x_3995_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextEdit_fromJson_spec__1(v_json_3993_, v___x_3994_);
if (lean_obj_tag(v___x_3995_) == 0)
{
lean_object* v_a_3996_; lean_object* v___x_3998_; uint8_t v_isShared_3999_; uint8_t v_isSharedCheck_4005_; 
v_a_3996_ = lean_ctor_get(v___x_3995_, 0);
v_isSharedCheck_4005_ = !lean_is_exclusive(v___x_3995_);
if (v_isSharedCheck_4005_ == 0)
{
v___x_3998_ = v___x_3995_;
v_isShared_3999_ = v_isSharedCheck_4005_;
goto v_resetjp_3997_;
}
else
{
lean_inc(v_a_3996_);
lean_dec(v___x_3995_);
v___x_3998_ = lean_box(0);
v_isShared_3999_ = v_isSharedCheck_4005_;
goto v_resetjp_3997_;
}
v_resetjp_3997_:
{
lean_object* v___x_4000_; lean_object* v___x_4001_; lean_object* v___x_4003_; 
v___x_4000_ = lean_obj_once(&l_Lean_Lsp_instFromJsonStaticRegistrationOptions_fromJson___closed__8, &l_Lean_Lsp_instFromJsonStaticRegistrationOptions_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonStaticRegistrationOptions_fromJson___closed__8);
v___x_4001_ = lean_string_append(v___x_4000_, v_a_3996_);
lean_dec(v_a_3996_);
if (v_isShared_3999_ == 0)
{
lean_ctor_set(v___x_3998_, 0, v___x_4001_);
v___x_4003_ = v___x_3998_;
goto v_reusejp_4002_;
}
else
{
lean_object* v_reuseFailAlloc_4004_; 
v_reuseFailAlloc_4004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4004_, 0, v___x_4001_);
v___x_4003_ = v_reuseFailAlloc_4004_;
goto v_reusejp_4002_;
}
v_reusejp_4002_:
{
return v___x_4003_;
}
}
}
else
{
if (lean_obj_tag(v___x_3995_) == 0)
{
lean_object* v_a_4006_; lean_object* v___x_4008_; uint8_t v_isShared_4009_; uint8_t v_isSharedCheck_4013_; 
v_a_4006_ = lean_ctor_get(v___x_3995_, 0);
v_isSharedCheck_4013_ = !lean_is_exclusive(v___x_3995_);
if (v_isSharedCheck_4013_ == 0)
{
v___x_4008_ = v___x_3995_;
v_isShared_4009_ = v_isSharedCheck_4013_;
goto v_resetjp_4007_;
}
else
{
lean_inc(v_a_4006_);
lean_dec(v___x_3995_);
v___x_4008_ = lean_box(0);
v_isShared_4009_ = v_isSharedCheck_4013_;
goto v_resetjp_4007_;
}
v_resetjp_4007_:
{
lean_object* v___x_4011_; 
if (v_isShared_4009_ == 0)
{
lean_ctor_set_tag(v___x_4008_, 0);
v___x_4011_ = v___x_4008_;
goto v_reusejp_4010_;
}
else
{
lean_object* v_reuseFailAlloc_4012_; 
v_reuseFailAlloc_4012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4012_, 0, v_a_4006_);
v___x_4011_ = v_reuseFailAlloc_4012_;
goto v_reusejp_4010_;
}
v_reusejp_4010_:
{
return v___x_4011_;
}
}
}
else
{
lean_object* v_a_4014_; lean_object* v___x_4016_; uint8_t v_isShared_4017_; uint8_t v_isSharedCheck_4021_; 
v_a_4014_ = lean_ctor_get(v___x_3995_, 0);
v_isSharedCheck_4021_ = !lean_is_exclusive(v___x_3995_);
if (v_isSharedCheck_4021_ == 0)
{
v___x_4016_ = v___x_3995_;
v_isShared_4017_ = v_isSharedCheck_4021_;
goto v_resetjp_4015_;
}
else
{
lean_inc(v_a_4014_);
lean_dec(v___x_3995_);
v___x_4016_ = lean_box(0);
v_isShared_4017_ = v_isSharedCheck_4021_;
goto v_resetjp_4015_;
}
v_resetjp_4015_:
{
lean_object* v___x_4019_; 
if (v_isShared_4017_ == 0)
{
v___x_4019_ = v___x_4016_;
goto v_reusejp_4018_;
}
else
{
lean_object* v_reuseFailAlloc_4020_; 
v_reuseFailAlloc_4020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4020_, 0, v_a_4014_);
v___x_4019_ = v_reuseFailAlloc_4020_;
goto v_reusejp_4018_;
}
v_reusejp_4018_:
{
return v___x_4019_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonTextDocumentRegistrationOptions_toJson_spec__0_spec__0_spec__1(size_t v_sz_4024_, size_t v_i_4025_, lean_object* v_bs_4026_){
_start:
{
uint8_t v___x_4027_; 
v___x_4027_ = lean_usize_dec_lt(v_i_4025_, v_sz_4024_);
if (v___x_4027_ == 0)
{
return v_bs_4026_;
}
else
{
lean_object* v_v_4028_; lean_object* v___x_4029_; lean_object* v_bs_x27_4030_; lean_object* v___x_4031_; size_t v___x_4032_; size_t v___x_4033_; lean_object* v___x_4034_; 
v_v_4028_ = lean_array_uget(v_bs_4026_, v_i_4025_);
v___x_4029_ = lean_unsigned_to_nat(0u);
v_bs_x27_4030_ = lean_array_uset(v_bs_4026_, v_i_4025_, v___x_4029_);
v___x_4031_ = l_Lean_Lsp_instToJsonDocumentFilter_toJson(v_v_4028_);
v___x_4032_ = ((size_t)1ULL);
v___x_4033_ = lean_usize_add(v_i_4025_, v___x_4032_);
v___x_4034_ = lean_array_uset(v_bs_x27_4030_, v_i_4025_, v___x_4031_);
v_i_4025_ = v___x_4033_;
v_bs_4026_ = v___x_4034_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonTextDocumentRegistrationOptions_toJson_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_4036_, lean_object* v_i_4037_, lean_object* v_bs_4038_){
_start:
{
size_t v_sz_boxed_4039_; size_t v_i_boxed_4040_; lean_object* v_res_4041_; 
v_sz_boxed_4039_ = lean_unbox_usize(v_sz_4036_);
lean_dec(v_sz_4036_);
v_i_boxed_4040_ = lean_unbox_usize(v_i_4037_);
lean_dec(v_i_4037_);
v_res_4041_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonTextDocumentRegistrationOptions_toJson_spec__0_spec__0_spec__1(v_sz_boxed_4039_, v_i_boxed_4040_, v_bs_4038_);
return v_res_4041_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonTextDocumentRegistrationOptions_toJson_spec__0_spec__0(lean_object* v_a_4042_){
_start:
{
size_t v_sz_4043_; size_t v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; 
v_sz_4043_ = lean_array_size(v_a_4042_);
v___x_4044_ = ((size_t)0ULL);
v___x_4045_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonTextDocumentRegistrationOptions_toJson_spec__0_spec__0_spec__1(v_sz_4043_, v___x_4044_, v_a_4042_);
v___x_4046_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_4046_, 0, v___x_4045_);
return v___x_4046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextDocumentRegistrationOptions_toJson_spec__0(lean_object* v_k_4047_, lean_object* v_x_4048_){
_start:
{
if (lean_obj_tag(v_x_4048_) == 0)
{
lean_object* v___x_4049_; 
lean_dec_ref(v_k_4047_);
v___x_4049_ = lean_box(0);
return v___x_4049_;
}
else
{
lean_object* v_val_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; 
v_val_4050_ = lean_ctor_get(v_x_4048_, 0);
lean_inc(v_val_4050_);
lean_dec_ref(v_x_4048_);
v___x_4051_ = l_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonTextDocumentRegistrationOptions_toJson_spec__0_spec__0(v_val_4050_);
v___x_4052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4052_, 0, v_k_4047_);
lean_ctor_set(v___x_4052_, 1, v___x_4051_);
v___x_4053_ = lean_box(0);
v___x_4054_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4054_, 0, v___x_4052_);
lean_ctor_set(v___x_4054_, 1, v___x_4053_);
return v___x_4054_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonTextDocumentRegistrationOptions_toJson(lean_object* v_x_4056_){
_start:
{
lean_object* v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; 
v___x_4057_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextDocumentRegistrationOptions_toJson___closed__0));
v___x_4058_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextDocumentRegistrationOptions_toJson_spec__0(v___x_4057_, v_x_4056_);
v___x_4059_ = lean_box(0);
v___x_4060_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4060_, 0, v___x_4058_);
lean_ctor_set(v___x_4060_, 1, v___x_4059_);
v___x_4061_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__2));
v___x_4062_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLocation_toJson_spec__0(v___x_4060_, v___x_4061_);
v___x_4063_ = l_Lean_Json_mkObj(v___x_4062_);
return v___x_4063_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson_spec__0_spec__0_spec__1_spec__2(size_t v_sz_4066_, size_t v_i_4067_, lean_object* v_bs_4068_){
_start:
{
uint8_t v___x_4069_; 
v___x_4069_ = lean_usize_dec_lt(v_i_4067_, v_sz_4066_);
if (v___x_4069_ == 0)
{
lean_object* v___x_4070_; 
v___x_4070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4070_, 0, v_bs_4068_);
return v___x_4070_;
}
else
{
lean_object* v_v_4071_; lean_object* v___x_4072_; 
v_v_4071_ = lean_array_uget_borrowed(v_bs_4068_, v_i_4067_);
lean_inc(v_v_4071_);
v___x_4072_ = l_Lean_Lsp_instFromJsonDocumentFilter_fromJson(v_v_4071_);
if (lean_obj_tag(v___x_4072_) == 0)
{
lean_object* v_a_4073_; lean_object* v___x_4075_; uint8_t v_isShared_4076_; uint8_t v_isSharedCheck_4080_; 
lean_dec_ref(v_bs_4068_);
v_a_4073_ = lean_ctor_get(v___x_4072_, 0);
v_isSharedCheck_4080_ = !lean_is_exclusive(v___x_4072_);
if (v_isSharedCheck_4080_ == 0)
{
v___x_4075_ = v___x_4072_;
v_isShared_4076_ = v_isSharedCheck_4080_;
goto v_resetjp_4074_;
}
else
{
lean_inc(v_a_4073_);
lean_dec(v___x_4072_);
v___x_4075_ = lean_box(0);
v_isShared_4076_ = v_isSharedCheck_4080_;
goto v_resetjp_4074_;
}
v_resetjp_4074_:
{
lean_object* v___x_4078_; 
if (v_isShared_4076_ == 0)
{
v___x_4078_ = v___x_4075_;
goto v_reusejp_4077_;
}
else
{
lean_object* v_reuseFailAlloc_4079_; 
v_reuseFailAlloc_4079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4079_, 0, v_a_4073_);
v___x_4078_ = v_reuseFailAlloc_4079_;
goto v_reusejp_4077_;
}
v_reusejp_4077_:
{
return v___x_4078_;
}
}
}
else
{
lean_object* v_a_4081_; lean_object* v___x_4082_; lean_object* v_bs_x27_4083_; size_t v___x_4084_; size_t v___x_4085_; lean_object* v___x_4086_; 
v_a_4081_ = lean_ctor_get(v___x_4072_, 0);
lean_inc(v_a_4081_);
lean_dec_ref(v___x_4072_);
v___x_4082_ = lean_unsigned_to_nat(0u);
v_bs_x27_4083_ = lean_array_uset(v_bs_4068_, v_i_4067_, v___x_4082_);
v___x_4084_ = ((size_t)1ULL);
v___x_4085_ = lean_usize_add(v_i_4067_, v___x_4084_);
v___x_4086_ = lean_array_uset(v_bs_x27_4083_, v_i_4067_, v_a_4081_);
v_i_4067_ = v___x_4085_;
v_bs_4068_ = v___x_4086_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_sz_4088_, lean_object* v_i_4089_, lean_object* v_bs_4090_){
_start:
{
size_t v_sz_boxed_4091_; size_t v_i_boxed_4092_; lean_object* v_res_4093_; 
v_sz_boxed_4091_ = lean_unbox_usize(v_sz_4088_);
lean_dec(v_sz_4088_);
v_i_boxed_4092_ = lean_unbox_usize(v_i_4089_);
lean_dec(v_i_4089_);
v_res_4093_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson_spec__0_spec__0_spec__1_spec__2(v_sz_boxed_4091_, v_i_boxed_4092_, v_bs_4090_);
return v_res_4093_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson_spec__0_spec__0_spec__1(lean_object* v_x_4094_){
_start:
{
if (lean_obj_tag(v_x_4094_) == 4)
{
lean_object* v_elems_4095_; size_t v_sz_4096_; size_t v___x_4097_; lean_object* v___x_4098_; 
v_elems_4095_ = lean_ctor_get(v_x_4094_, 0);
lean_inc_ref(v_elems_4095_);
lean_dec_ref(v_x_4094_);
v_sz_4096_ = lean_array_size(v_elems_4095_);
v___x_4097_ = ((size_t)0ULL);
v___x_4098_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson_spec__0_spec__0_spec__1_spec__2(v_sz_4096_, v___x_4097_, v_elems_4095_);
return v___x_4098_;
}
else
{
lean_object* v___x_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; 
v___x_4099_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCommand_fromJson_spec__0_spec__0_spec__1___closed__0));
v___x_4100_ = lean_unsigned_to_nat(80u);
v___x_4101_ = l_Lean_Json_pretty(v_x_4094_, v___x_4100_);
v___x_4102_ = lean_string_append(v___x_4099_, v___x_4101_);
lean_dec_ref(v___x_4101_);
v___x_4103_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCommand_fromJson_spec__0_spec__0_spec__1___closed__1));
v___x_4104_ = lean_string_append(v___x_4102_, v___x_4103_);
v___x_4105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4105_, 0, v___x_4104_);
return v___x_4105_;
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson_spec__0_spec__0(lean_object* v_x_4108_){
_start:
{
if (lean_obj_tag(v_x_4108_) == 0)
{
lean_object* v___x_4109_; 
v___x_4109_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson_spec__0_spec__0___closed__0));
return v___x_4109_;
}
else
{
lean_object* v___x_4110_; 
v___x_4110_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson_spec__0_spec__0_spec__1(v_x_4108_);
if (lean_obj_tag(v___x_4110_) == 0)
{
lean_object* v_a_4111_; lean_object* v___x_4113_; uint8_t v_isShared_4114_; uint8_t v_isSharedCheck_4118_; 
v_a_4111_ = lean_ctor_get(v___x_4110_, 0);
v_isSharedCheck_4118_ = !lean_is_exclusive(v___x_4110_);
if (v_isSharedCheck_4118_ == 0)
{
v___x_4113_ = v___x_4110_;
v_isShared_4114_ = v_isSharedCheck_4118_;
goto v_resetjp_4112_;
}
else
{
lean_inc(v_a_4111_);
lean_dec(v___x_4110_);
v___x_4113_ = lean_box(0);
v_isShared_4114_ = v_isSharedCheck_4118_;
goto v_resetjp_4112_;
}
v_resetjp_4112_:
{
lean_object* v___x_4116_; 
if (v_isShared_4114_ == 0)
{
v___x_4116_ = v___x_4113_;
goto v_reusejp_4115_;
}
else
{
lean_object* v_reuseFailAlloc_4117_; 
v_reuseFailAlloc_4117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4117_, 0, v_a_4111_);
v___x_4116_ = v_reuseFailAlloc_4117_;
goto v_reusejp_4115_;
}
v_reusejp_4115_:
{
return v___x_4116_;
}
}
}
else
{
lean_object* v_a_4119_; lean_object* v___x_4121_; uint8_t v_isShared_4122_; uint8_t v_isSharedCheck_4127_; 
v_a_4119_ = lean_ctor_get(v___x_4110_, 0);
v_isSharedCheck_4127_ = !lean_is_exclusive(v___x_4110_);
if (v_isSharedCheck_4127_ == 0)
{
v___x_4121_ = v___x_4110_;
v_isShared_4122_ = v_isSharedCheck_4127_;
goto v_resetjp_4120_;
}
else
{
lean_inc(v_a_4119_);
lean_dec(v___x_4110_);
v___x_4121_ = lean_box(0);
v_isShared_4122_ = v_isSharedCheck_4127_;
goto v_resetjp_4120_;
}
v_resetjp_4120_:
{
lean_object* v___x_4123_; lean_object* v___x_4125_; 
v___x_4123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4123_, 0, v_a_4119_);
if (v_isShared_4122_ == 0)
{
lean_ctor_set(v___x_4121_, 0, v___x_4123_);
v___x_4125_ = v___x_4121_;
goto v_reusejp_4124_;
}
else
{
lean_object* v_reuseFailAlloc_4126_; 
v_reuseFailAlloc_4126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4126_, 0, v___x_4123_);
v___x_4125_ = v_reuseFailAlloc_4126_;
goto v_reusejp_4124_;
}
v_reusejp_4124_:
{
return v___x_4125_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson_spec__0(lean_object* v_j_4128_, lean_object* v_k_4129_){
_start:
{
lean_object* v___x_4130_; lean_object* v___x_4131_; 
v___x_4130_ = l_Lean_Json_getObjValD(v_j_4128_, v_k_4129_);
v___x_4131_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson_spec__0_spec__0(v___x_4130_);
return v___x_4131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson_spec__0___boxed(lean_object* v_j_4132_, lean_object* v_k_4133_){
_start:
{
lean_object* v_res_4134_; 
v_res_4134_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson_spec__0(v_j_4132_, v_k_4133_);
lean_dec_ref(v_k_4133_);
return v_res_4134_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson___closed__2(void){
_start:
{
uint8_t v___x_4140_; lean_object* v___x_4141_; lean_object* v___x_4142_; 
v___x_4140_ = 1;
v___x_4141_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson___closed__1));
v___x_4142_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4141_, v___x_4140_);
return v___x_4142_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson___closed__3(void){
_start:
{
lean_object* v___x_4143_; lean_object* v___x_4144_; lean_object* v___x_4145_; 
v___x_4143_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__5));
v___x_4144_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson___closed__2, &l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson___closed__2);
v___x_4145_ = lean_string_append(v___x_4144_, v___x_4143_);
return v___x_4145_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson___closed__6(void){
_start:
{
uint8_t v___x_4149_; lean_object* v___x_4150_; lean_object* v___x_4151_; 
v___x_4149_ = 1;
v___x_4150_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson___closed__5));
v___x_4151_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4150_, v___x_4149_);
return v___x_4151_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson___closed__7(void){
_start:
{
lean_object* v___x_4152_; lean_object* v___x_4153_; lean_object* v___x_4154_; 
v___x_4152_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson___closed__6, &l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson___closed__6);
v___x_4153_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson___closed__3, &l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson___closed__3);
v___x_4154_ = lean_string_append(v___x_4153_, v___x_4152_);
return v___x_4154_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson___closed__8(void){
_start:
{
lean_object* v___x_4155_; lean_object* v___x_4156_; lean_object* v___x_4157_; 
v___x_4155_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_4156_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson___closed__7, &l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson___closed__7);
v___x_4157_ = lean_string_append(v___x_4156_, v___x_4155_);
return v___x_4157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson(lean_object* v_json_4158_){
_start:
{
lean_object* v___x_4159_; lean_object* v___x_4160_; 
v___x_4159_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextDocumentRegistrationOptions_toJson___closed__0));
v___x_4160_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson_spec__0(v_json_4158_, v___x_4159_);
if (lean_obj_tag(v___x_4160_) == 0)
{
lean_object* v_a_4161_; lean_object* v___x_4163_; uint8_t v_isShared_4164_; uint8_t v_isSharedCheck_4170_; 
v_a_4161_ = lean_ctor_get(v___x_4160_, 0);
v_isSharedCheck_4170_ = !lean_is_exclusive(v___x_4160_);
if (v_isSharedCheck_4170_ == 0)
{
v___x_4163_ = v___x_4160_;
v_isShared_4164_ = v_isSharedCheck_4170_;
goto v_resetjp_4162_;
}
else
{
lean_inc(v_a_4161_);
lean_dec(v___x_4160_);
v___x_4163_ = lean_box(0);
v_isShared_4164_ = v_isSharedCheck_4170_;
goto v_resetjp_4162_;
}
v_resetjp_4162_:
{
lean_object* v___x_4165_; lean_object* v___x_4166_; lean_object* v___x_4168_; 
v___x_4165_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson___closed__8, &l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson___closed__8);
v___x_4166_ = lean_string_append(v___x_4165_, v_a_4161_);
lean_dec(v_a_4161_);
if (v_isShared_4164_ == 0)
{
lean_ctor_set(v___x_4163_, 0, v___x_4166_);
v___x_4168_ = v___x_4163_;
goto v_reusejp_4167_;
}
else
{
lean_object* v_reuseFailAlloc_4169_; 
v_reuseFailAlloc_4169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4169_, 0, v___x_4166_);
v___x_4168_ = v_reuseFailAlloc_4169_;
goto v_reusejp_4167_;
}
v_reusejp_4167_:
{
return v___x_4168_;
}
}
}
else
{
if (lean_obj_tag(v___x_4160_) == 0)
{
lean_object* v_a_4171_; lean_object* v___x_4173_; uint8_t v_isShared_4174_; uint8_t v_isSharedCheck_4178_; 
v_a_4171_ = lean_ctor_get(v___x_4160_, 0);
v_isSharedCheck_4178_ = !lean_is_exclusive(v___x_4160_);
if (v_isSharedCheck_4178_ == 0)
{
v___x_4173_ = v___x_4160_;
v_isShared_4174_ = v_isSharedCheck_4178_;
goto v_resetjp_4172_;
}
else
{
lean_inc(v_a_4171_);
lean_dec(v___x_4160_);
v___x_4173_ = lean_box(0);
v_isShared_4174_ = v_isSharedCheck_4178_;
goto v_resetjp_4172_;
}
v_resetjp_4172_:
{
lean_object* v___x_4176_; 
if (v_isShared_4174_ == 0)
{
lean_ctor_set_tag(v___x_4173_, 0);
v___x_4176_ = v___x_4173_;
goto v_reusejp_4175_;
}
else
{
lean_object* v_reuseFailAlloc_4177_; 
v_reuseFailAlloc_4177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4177_, 0, v_a_4171_);
v___x_4176_ = v_reuseFailAlloc_4177_;
goto v_reusejp_4175_;
}
v_reusejp_4175_:
{
return v___x_4176_;
}
}
}
else
{
lean_object* v_a_4179_; lean_object* v___x_4181_; uint8_t v_isShared_4182_; uint8_t v_isSharedCheck_4186_; 
v_a_4179_ = lean_ctor_get(v___x_4160_, 0);
v_isSharedCheck_4186_ = !lean_is_exclusive(v___x_4160_);
if (v_isSharedCheck_4186_ == 0)
{
v___x_4181_ = v___x_4160_;
v_isShared_4182_ = v_isSharedCheck_4186_;
goto v_resetjp_4180_;
}
else
{
lean_inc(v_a_4179_);
lean_dec(v___x_4160_);
v___x_4181_ = lean_box(0);
v_isShared_4182_ = v_isSharedCheck_4186_;
goto v_resetjp_4180_;
}
v_resetjp_4180_:
{
lean_object* v___x_4184_; 
if (v_isShared_4182_ == 0)
{
v___x_4184_ = v___x_4181_;
goto v_reusejp_4183_;
}
else
{
lean_object* v_reuseFailAlloc_4185_; 
v_reuseFailAlloc_4185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4185_, 0, v_a_4179_);
v___x_4184_ = v_reuseFailAlloc_4185_;
goto v_reusejp_4183_;
}
v_reusejp_4183_:
{
return v___x_4184_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MarkupKind_ctorIdx(uint8_t v_x_4189_){
_start:
{
if (v_x_4189_ == 0)
{
lean_object* v___x_4190_; 
v___x_4190_ = lean_unsigned_to_nat(0u);
return v___x_4190_;
}
else
{
lean_object* v___x_4191_; 
v___x_4191_ = lean_unsigned_to_nat(1u);
return v___x_4191_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MarkupKind_ctorIdx___boxed(lean_object* v_x_4192_){
_start:
{
uint8_t v_x_boxed_4193_; lean_object* v_res_4194_; 
v_x_boxed_4193_ = lean_unbox(v_x_4192_);
v_res_4194_ = l_Lean_Lsp_MarkupKind_ctorIdx(v_x_boxed_4193_);
return v_res_4194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MarkupKind_toCtorIdx(uint8_t v_x_4195_){
_start:
{
lean_object* v___x_4196_; 
v___x_4196_ = l_Lean_Lsp_MarkupKind_ctorIdx(v_x_4195_);
return v___x_4196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MarkupKind_toCtorIdx___boxed(lean_object* v_x_4197_){
_start:
{
uint8_t v_x_4__boxed_4198_; lean_object* v_res_4199_; 
v_x_4__boxed_4198_ = lean_unbox(v_x_4197_);
v_res_4199_ = l_Lean_Lsp_MarkupKind_toCtorIdx(v_x_4__boxed_4198_);
return v_res_4199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MarkupKind_ctorElim___redArg(lean_object* v_k_4200_){
_start:
{
lean_inc(v_k_4200_);
return v_k_4200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MarkupKind_ctorElim___redArg___boxed(lean_object* v_k_4201_){
_start:
{
lean_object* v_res_4202_; 
v_res_4202_ = l_Lean_Lsp_MarkupKind_ctorElim___redArg(v_k_4201_);
lean_dec(v_k_4201_);
return v_res_4202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MarkupKind_ctorElim(lean_object* v_motive_4203_, lean_object* v_ctorIdx_4204_, uint8_t v_t_4205_, lean_object* v_h_4206_, lean_object* v_k_4207_){
_start:
{
lean_inc(v_k_4207_);
return v_k_4207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MarkupKind_ctorElim___boxed(lean_object* v_motive_4208_, lean_object* v_ctorIdx_4209_, lean_object* v_t_4210_, lean_object* v_h_4211_, lean_object* v_k_4212_){
_start:
{
uint8_t v_t_boxed_4213_; lean_object* v_res_4214_; 
v_t_boxed_4213_ = lean_unbox(v_t_4210_);
v_res_4214_ = l_Lean_Lsp_MarkupKind_ctorElim(v_motive_4208_, v_ctorIdx_4209_, v_t_boxed_4213_, v_h_4211_, v_k_4212_);
lean_dec(v_k_4212_);
lean_dec(v_ctorIdx_4209_);
return v_res_4214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MarkupKind_plaintext_elim___redArg(lean_object* v_plaintext_4215_){
_start:
{
lean_inc(v_plaintext_4215_);
return v_plaintext_4215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MarkupKind_plaintext_elim___redArg___boxed(lean_object* v_plaintext_4216_){
_start:
{
lean_object* v_res_4217_; 
v_res_4217_ = l_Lean_Lsp_MarkupKind_plaintext_elim___redArg(v_plaintext_4216_);
lean_dec(v_plaintext_4216_);
return v_res_4217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MarkupKind_plaintext_elim(lean_object* v_motive_4218_, uint8_t v_t_4219_, lean_object* v_h_4220_, lean_object* v_plaintext_4221_){
_start:
{
lean_inc(v_plaintext_4221_);
return v_plaintext_4221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MarkupKind_plaintext_elim___boxed(lean_object* v_motive_4222_, lean_object* v_t_4223_, lean_object* v_h_4224_, lean_object* v_plaintext_4225_){
_start:
{
uint8_t v_t_boxed_4226_; lean_object* v_res_4227_; 
v_t_boxed_4226_ = lean_unbox(v_t_4223_);
v_res_4227_ = l_Lean_Lsp_MarkupKind_plaintext_elim(v_motive_4222_, v_t_boxed_4226_, v_h_4224_, v_plaintext_4225_);
lean_dec(v_plaintext_4225_);
return v_res_4227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MarkupKind_markdown_elim___redArg(lean_object* v_markdown_4228_){
_start:
{
lean_inc(v_markdown_4228_);
return v_markdown_4228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MarkupKind_markdown_elim___redArg___boxed(lean_object* v_markdown_4229_){
_start:
{
lean_object* v_res_4230_; 
v_res_4230_ = l_Lean_Lsp_MarkupKind_markdown_elim___redArg(v_markdown_4229_);
lean_dec(v_markdown_4229_);
return v_res_4230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MarkupKind_markdown_elim(lean_object* v_motive_4231_, uint8_t v_t_4232_, lean_object* v_h_4233_, lean_object* v_markdown_4234_){
_start:
{
lean_inc(v_markdown_4234_);
return v_markdown_4234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MarkupKind_markdown_elim___boxed(lean_object* v_motive_4235_, lean_object* v_t_4236_, lean_object* v_h_4237_, lean_object* v_markdown_4238_){
_start:
{
uint8_t v_t_boxed_4239_; lean_object* v_res_4240_; 
v_t_boxed_4239_ = lean_unbox(v_t_4236_);
v_res_4240_ = l_Lean_Lsp_MarkupKind_markdown_elim(v_motive_4235_, v_t_boxed_4239_, v_h_4237_, v_markdown_4238_);
lean_dec(v_markdown_4238_);
return v_res_4240_;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_MarkupKind_ofNat(lean_object* v_n_4241_){
_start:
{
lean_object* v___x_4242_; uint8_t v___x_4243_; 
v___x_4242_ = lean_unsigned_to_nat(0u);
v___x_4243_ = lean_nat_dec_le(v_n_4241_, v___x_4242_);
if (v___x_4243_ == 0)
{
uint8_t v___x_4244_; 
v___x_4244_ = 1;
return v___x_4244_;
}
else
{
uint8_t v___x_4245_; 
v___x_4245_ = 0;
return v___x_4245_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MarkupKind_ofNat___boxed(lean_object* v_n_4246_){
_start:
{
uint8_t v_res_4247_; lean_object* v_r_4248_; 
v_res_4247_ = l_Lean_Lsp_MarkupKind_ofNat(v_n_4246_);
lean_dec(v_n_4246_);
v_r_4248_ = lean_box(v_res_4247_);
return v_r_4248_;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_instDecidableEqMarkupKind(uint8_t v_x_4249_, uint8_t v_y_4250_){
_start:
{
lean_object* v___x_4251_; lean_object* v___x_4252_; uint8_t v___x_4253_; 
v___x_4251_ = l_Lean_Lsp_MarkupKind_ctorIdx(v_x_4249_);
v___x_4252_ = l_Lean_Lsp_MarkupKind_ctorIdx(v_y_4250_);
v___x_4253_ = lean_nat_dec_eq(v___x_4251_, v___x_4252_);
lean_dec(v___x_4252_);
lean_dec(v___x_4251_);
return v___x_4253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instDecidableEqMarkupKind___boxed(lean_object* v_x_4254_, lean_object* v_y_4255_){
_start:
{
uint8_t v_x_13__boxed_4256_; uint8_t v_y_14__boxed_4257_; uint8_t v_res_4258_; lean_object* v_r_4259_; 
v_x_13__boxed_4256_ = lean_unbox(v_x_4254_);
v_y_14__boxed_4257_ = lean_unbox(v_y_4255_);
v_res_4258_ = l_Lean_Lsp_instDecidableEqMarkupKind(v_x_13__boxed_4256_, v_y_14__boxed_4257_);
v_r_4259_ = lean_box(v_res_4258_);
return v_r_4259_;
}
}
LEAN_EXPORT uint64_t l_Lean_Lsp_instHashableMarkupKind_hash(uint8_t v_x_4260_){
_start:
{
if (v_x_4260_ == 0)
{
uint64_t v___x_4261_; 
v___x_4261_ = 0ULL;
return v___x_4261_;
}
else
{
uint64_t v___x_4262_; 
v___x_4262_ = 1ULL;
return v___x_4262_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instHashableMarkupKind_hash___boxed(lean_object* v_x_4263_){
_start:
{
uint8_t v_x_28__boxed_4264_; uint64_t v_res_4265_; lean_object* v_r_4266_; 
v_x_28__boxed_4264_ = lean_unbox(v_x_4263_);
v_res_4265_ = l_Lean_Lsp_instHashableMarkupKind_hash(v_x_28__boxed_4264_);
v_r_4266_ = lean_box_uint64(v_res_4265_);
return v_r_4266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonMarkupKind___lam__0(lean_object* v_x_4280_){
_start:
{
if (lean_obj_tag(v_x_4280_) == 3)
{
lean_object* v_s_4283_; lean_object* v___x_4284_; uint8_t v___x_4285_; 
v_s_4283_ = lean_ctor_get(v_x_4280_, 0);
v___x_4284_ = ((lean_object*)(l_Lean_Lsp_instFromJsonMarkupKind___lam__0___closed__2));
v___x_4285_ = lean_string_dec_eq(v_s_4283_, v___x_4284_);
if (v___x_4285_ == 0)
{
lean_object* v___x_4286_; uint8_t v___x_4287_; 
v___x_4286_ = ((lean_object*)(l_Lean_Lsp_instFromJsonMarkupKind___lam__0___closed__3));
v___x_4287_ = lean_string_dec_eq(v_s_4283_, v___x_4286_);
if (v___x_4287_ == 0)
{
goto v___jp_4281_;
}
else
{
lean_object* v___x_4288_; 
v___x_4288_ = ((lean_object*)(l_Lean_Lsp_instFromJsonMarkupKind___lam__0___closed__4));
return v___x_4288_;
}
}
else
{
lean_object* v___x_4289_; 
v___x_4289_ = ((lean_object*)(l_Lean_Lsp_instFromJsonMarkupKind___lam__0___closed__5));
return v___x_4289_;
}
}
else
{
goto v___jp_4281_;
}
v___jp_4281_:
{
lean_object* v___x_4282_; 
v___x_4282_ = ((lean_object*)(l_Lean_Lsp_instFromJsonMarkupKind___lam__0___closed__1));
return v___x_4282_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonMarkupKind___lam__0___boxed(lean_object* v_x_4290_){
_start:
{
lean_object* v_res_4291_; 
v_res_4291_ = l_Lean_Lsp_instFromJsonMarkupKind___lam__0(v_x_4290_);
lean_dec(v_x_4290_);
return v_res_4291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonMarkupKind___lam__0(uint8_t v_x_4298_){
_start:
{
if (v_x_4298_ == 0)
{
lean_object* v___x_4299_; 
v___x_4299_ = ((lean_object*)(l_Lean_Lsp_instToJsonMarkupKind___lam__0___closed__0));
return v___x_4299_;
}
else
{
lean_object* v___x_4300_; 
v___x_4300_ = ((lean_object*)(l_Lean_Lsp_instToJsonMarkupKind___lam__0___closed__1));
return v___x_4300_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonMarkupKind___lam__0___boxed(lean_object* v_x_4301_){
_start:
{
uint8_t v_x_38__boxed_4302_; lean_object* v_res_4303_; 
v_x_38__boxed_4302_ = lean_unbox(v_x_4301_);
v_res_4303_ = l_Lean_Lsp_instToJsonMarkupKind___lam__0(v_x_38__boxed_4302_);
return v_res_4303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonMarkupContent_toJson(lean_object* v_x_4306_){
_start:
{
uint8_t v_kind_4307_; lean_object* v_value_4308_; lean_object* v___x_4309_; lean_object* v___y_4311_; 
v_kind_4307_ = lean_ctor_get_uint8(v_x_4306_, sizeof(void*)*1);
v_value_4308_ = lean_ctor_get(v_x_4306_, 0);
v___x_4309_ = ((lean_object*)(l_Lean_Lsp_instToJsonDocumentChange___lam__0___closed__0));
if (v_kind_4307_ == 0)
{
lean_object* v___x_4324_; 
v___x_4324_ = ((lean_object*)(l_Lean_Lsp_instToJsonMarkupKind___lam__0___closed__0));
v___y_4311_ = v___x_4324_;
goto v___jp_4310_;
}
else
{
lean_object* v___x_4325_; 
v___x_4325_ = ((lean_object*)(l_Lean_Lsp_instToJsonMarkupKind___lam__0___closed__1));
v___y_4311_ = v___x_4325_;
goto v___jp_4310_;
}
v___jp_4310_:
{
lean_object* v___x_4312_; lean_object* v___x_4313_; lean_object* v___x_4314_; lean_object* v___x_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; lean_object* v___x_4318_; lean_object* v___x_4319_; lean_object* v___x_4320_; lean_object* v___x_4321_; lean_object* v___x_4322_; lean_object* v___x_4323_; 
v___x_4312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4312_, 0, v___x_4309_);
lean_ctor_set(v___x_4312_, 1, v___y_4311_);
v___x_4313_ = lean_box(0);
v___x_4314_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4314_, 0, v___x_4312_);
lean_ctor_set(v___x_4314_, 1, v___x_4313_);
v___x_4315_ = ((lean_object*)(l_Lean_Lsp_instToJsonSnippetString_toJson___closed__0));
lean_inc_ref(v_value_4308_);
v___x_4316_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4316_, 0, v_value_4308_);
v___x_4317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4317_, 0, v___x_4315_);
lean_ctor_set(v___x_4317_, 1, v___x_4316_);
v___x_4318_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4318_, 0, v___x_4317_);
lean_ctor_set(v___x_4318_, 1, v___x_4313_);
v___x_4319_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4319_, 0, v___x_4318_);
lean_ctor_set(v___x_4319_, 1, v___x_4313_);
v___x_4320_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4320_, 0, v___x_4314_);
lean_ctor_set(v___x_4320_, 1, v___x_4319_);
v___x_4321_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__2));
v___x_4322_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLocation_toJson_spec__0(v___x_4320_, v___x_4321_);
v___x_4323_ = l_Lean_Json_mkObj(v___x_4322_);
return v___x_4323_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonMarkupContent_toJson___boxed(lean_object* v_x_4326_){
_start:
{
lean_object* v_res_4327_; 
v_res_4327_ = l_Lean_Lsp_instToJsonMarkupContent_toJson(v_x_4326_);
lean_dec_ref(v_x_4326_);
return v_res_4327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonMarkupContent_fromJson_spec__0(lean_object* v_j_4330_, lean_object* v_k_4331_){
_start:
{
lean_object* v___x_4334_; 
v___x_4334_ = l_Lean_Json_getObjValD(v_j_4330_, v_k_4331_);
if (lean_obj_tag(v___x_4334_) == 3)
{
lean_object* v_s_4335_; lean_object* v___x_4336_; uint8_t v___x_4337_; 
v_s_4335_ = lean_ctor_get(v___x_4334_, 0);
lean_inc_ref(v_s_4335_);
lean_dec_ref(v___x_4334_);
v___x_4336_ = ((lean_object*)(l_Lean_Lsp_instFromJsonMarkupKind___lam__0___closed__2));
v___x_4337_ = lean_string_dec_eq(v_s_4335_, v___x_4336_);
if (v___x_4337_ == 0)
{
lean_object* v___x_4338_; uint8_t v___x_4339_; 
v___x_4338_ = ((lean_object*)(l_Lean_Lsp_instFromJsonMarkupKind___lam__0___closed__3));
v___x_4339_ = lean_string_dec_eq(v_s_4335_, v___x_4338_);
lean_dec_ref(v_s_4335_);
if (v___x_4339_ == 0)
{
goto v___jp_4332_;
}
else
{
lean_object* v___x_4340_; 
v___x_4340_ = ((lean_object*)(l_Lean_Lsp_instFromJsonMarkupKind___lam__0___closed__4));
return v___x_4340_;
}
}
else
{
lean_object* v___x_4341_; 
lean_dec_ref(v_s_4335_);
v___x_4341_ = ((lean_object*)(l_Lean_Lsp_instFromJsonMarkupKind___lam__0___closed__5));
return v___x_4341_;
}
}
else
{
lean_dec(v___x_4334_);
goto v___jp_4332_;
}
v___jp_4332_:
{
lean_object* v___x_4333_; 
v___x_4333_ = ((lean_object*)(l_Lean_Lsp_instFromJsonMarkupKind___lam__0___closed__1));
return v___x_4333_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonMarkupContent_fromJson_spec__0___boxed(lean_object* v_j_4342_, lean_object* v_k_4343_){
_start:
{
lean_object* v_res_4344_; 
v_res_4344_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonMarkupContent_fromJson_spec__0(v_j_4342_, v_k_4343_);
lean_dec_ref(v_k_4343_);
return v_res_4344_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__2(void){
_start:
{
uint8_t v___x_4350_; lean_object* v___x_4351_; lean_object* v___x_4352_; 
v___x_4350_ = 1;
v___x_4351_ = ((lean_object*)(l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__1));
v___x_4352_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4351_, v___x_4350_);
return v___x_4352_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__3(void){
_start:
{
lean_object* v___x_4353_; lean_object* v___x_4354_; lean_object* v___x_4355_; 
v___x_4353_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__5));
v___x_4354_ = lean_obj_once(&l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__2, &l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__2);
v___x_4355_ = lean_string_append(v___x_4354_, v___x_4353_);
return v___x_4355_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__5(void){
_start:
{
uint8_t v___x_4358_; lean_object* v___x_4359_; lean_object* v___x_4360_; 
v___x_4358_ = 1;
v___x_4359_ = ((lean_object*)(l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__4));
v___x_4360_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4359_, v___x_4358_);
return v___x_4360_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__6(void){
_start:
{
lean_object* v___x_4361_; lean_object* v___x_4362_; lean_object* v___x_4363_; 
v___x_4361_ = lean_obj_once(&l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__5, &l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__5);
v___x_4362_ = lean_obj_once(&l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__3, &l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__3);
v___x_4363_ = lean_string_append(v___x_4362_, v___x_4361_);
return v___x_4363_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__7(void){
_start:
{
lean_object* v___x_4364_; lean_object* v___x_4365_; lean_object* v___x_4366_; 
v___x_4364_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_4365_ = lean_obj_once(&l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__6, &l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__6);
v___x_4366_ = lean_string_append(v___x_4365_, v___x_4364_);
return v___x_4366_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__8(void){
_start:
{
lean_object* v___x_4367_; lean_object* v___x_4368_; lean_object* v___x_4369_; 
v___x_4367_ = lean_obj_once(&l_Lean_Lsp_instFromJsonSnippetString_fromJson___closed__5, &l_Lean_Lsp_instFromJsonSnippetString_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonSnippetString_fromJson___closed__5);
v___x_4368_ = lean_obj_once(&l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__3, &l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__3);
v___x_4369_ = lean_string_append(v___x_4368_, v___x_4367_);
return v___x_4369_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__9(void){
_start:
{
lean_object* v___x_4370_; lean_object* v___x_4371_; lean_object* v___x_4372_; 
v___x_4370_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_4371_ = lean_obj_once(&l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__8, &l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__8);
v___x_4372_ = lean_string_append(v___x_4371_, v___x_4370_);
return v___x_4372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonMarkupContent_fromJson(lean_object* v_json_4373_){
_start:
{
lean_object* v___x_4374_; lean_object* v___x_4375_; 
v___x_4374_ = ((lean_object*)(l_Lean_Lsp_instToJsonDocumentChange___lam__0___closed__0));
lean_inc(v_json_4373_);
v___x_4375_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonMarkupContent_fromJson_spec__0(v_json_4373_, v___x_4374_);
if (lean_obj_tag(v___x_4375_) == 0)
{
lean_object* v_a_4376_; lean_object* v___x_4378_; uint8_t v_isShared_4379_; uint8_t v_isSharedCheck_4385_; 
lean_dec(v_json_4373_);
v_a_4376_ = lean_ctor_get(v___x_4375_, 0);
v_isSharedCheck_4385_ = !lean_is_exclusive(v___x_4375_);
if (v_isSharedCheck_4385_ == 0)
{
v___x_4378_ = v___x_4375_;
v_isShared_4379_ = v_isSharedCheck_4385_;
goto v_resetjp_4377_;
}
else
{
lean_inc(v_a_4376_);
lean_dec(v___x_4375_);
v___x_4378_ = lean_box(0);
v_isShared_4379_ = v_isSharedCheck_4385_;
goto v_resetjp_4377_;
}
v_resetjp_4377_:
{
lean_object* v___x_4380_; lean_object* v___x_4381_; lean_object* v___x_4383_; 
v___x_4380_ = lean_obj_once(&l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__7, &l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__7);
v___x_4381_ = lean_string_append(v___x_4380_, v_a_4376_);
lean_dec(v_a_4376_);
if (v_isShared_4379_ == 0)
{
lean_ctor_set(v___x_4378_, 0, v___x_4381_);
v___x_4383_ = v___x_4378_;
goto v_reusejp_4382_;
}
else
{
lean_object* v_reuseFailAlloc_4384_; 
v_reuseFailAlloc_4384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4384_, 0, v___x_4381_);
v___x_4383_ = v_reuseFailAlloc_4384_;
goto v_reusejp_4382_;
}
v_reusejp_4382_:
{
return v___x_4383_;
}
}
}
else
{
if (lean_obj_tag(v___x_4375_) == 0)
{
lean_object* v_a_4386_; lean_object* v___x_4388_; uint8_t v_isShared_4389_; uint8_t v_isSharedCheck_4393_; 
lean_dec(v_json_4373_);
v_a_4386_ = lean_ctor_get(v___x_4375_, 0);
v_isSharedCheck_4393_ = !lean_is_exclusive(v___x_4375_);
if (v_isSharedCheck_4393_ == 0)
{
v___x_4388_ = v___x_4375_;
v_isShared_4389_ = v_isSharedCheck_4393_;
goto v_resetjp_4387_;
}
else
{
lean_inc(v_a_4386_);
lean_dec(v___x_4375_);
v___x_4388_ = lean_box(0);
v_isShared_4389_ = v_isSharedCheck_4393_;
goto v_resetjp_4387_;
}
v_resetjp_4387_:
{
lean_object* v___x_4391_; 
if (v_isShared_4389_ == 0)
{
lean_ctor_set_tag(v___x_4388_, 0);
v___x_4391_ = v___x_4388_;
goto v_reusejp_4390_;
}
else
{
lean_object* v_reuseFailAlloc_4392_; 
v_reuseFailAlloc_4392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4392_, 0, v_a_4386_);
v___x_4391_ = v_reuseFailAlloc_4392_;
goto v_reusejp_4390_;
}
v_reusejp_4390_:
{
return v___x_4391_;
}
}
}
else
{
lean_object* v_a_4394_; lean_object* v___x_4395_; lean_object* v___x_4396_; 
v_a_4394_ = lean_ctor_get(v___x_4375_, 0);
lean_inc(v_a_4394_);
lean_dec_ref(v___x_4375_);
v___x_4395_ = ((lean_object*)(l_Lean_Lsp_instToJsonSnippetString_toJson___closed__0));
v___x_4396_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocation_fromJson_spec__0(v_json_4373_, v___x_4395_);
if (lean_obj_tag(v___x_4396_) == 0)
{
lean_object* v_a_4397_; lean_object* v___x_4399_; uint8_t v_isShared_4400_; uint8_t v_isSharedCheck_4406_; 
lean_dec(v_a_4394_);
v_a_4397_ = lean_ctor_get(v___x_4396_, 0);
v_isSharedCheck_4406_ = !lean_is_exclusive(v___x_4396_);
if (v_isSharedCheck_4406_ == 0)
{
v___x_4399_ = v___x_4396_;
v_isShared_4400_ = v_isSharedCheck_4406_;
goto v_resetjp_4398_;
}
else
{
lean_inc(v_a_4397_);
lean_dec(v___x_4396_);
v___x_4399_ = lean_box(0);
v_isShared_4400_ = v_isSharedCheck_4406_;
goto v_resetjp_4398_;
}
v_resetjp_4398_:
{
lean_object* v___x_4401_; lean_object* v___x_4402_; lean_object* v___x_4404_; 
v___x_4401_ = lean_obj_once(&l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__9, &l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__9);
v___x_4402_ = lean_string_append(v___x_4401_, v_a_4397_);
lean_dec(v_a_4397_);
if (v_isShared_4400_ == 0)
{
lean_ctor_set(v___x_4399_, 0, v___x_4402_);
v___x_4404_ = v___x_4399_;
goto v_reusejp_4403_;
}
else
{
lean_object* v_reuseFailAlloc_4405_; 
v_reuseFailAlloc_4405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4405_, 0, v___x_4402_);
v___x_4404_ = v_reuseFailAlloc_4405_;
goto v_reusejp_4403_;
}
v_reusejp_4403_:
{
return v___x_4404_;
}
}
}
else
{
if (lean_obj_tag(v___x_4396_) == 0)
{
lean_object* v_a_4407_; lean_object* v___x_4409_; uint8_t v_isShared_4410_; uint8_t v_isSharedCheck_4414_; 
lean_dec(v_a_4394_);
v_a_4407_ = lean_ctor_get(v___x_4396_, 0);
v_isSharedCheck_4414_ = !lean_is_exclusive(v___x_4396_);
if (v_isSharedCheck_4414_ == 0)
{
v___x_4409_ = v___x_4396_;
v_isShared_4410_ = v_isSharedCheck_4414_;
goto v_resetjp_4408_;
}
else
{
lean_inc(v_a_4407_);
lean_dec(v___x_4396_);
v___x_4409_ = lean_box(0);
v_isShared_4410_ = v_isSharedCheck_4414_;
goto v_resetjp_4408_;
}
v_resetjp_4408_:
{
lean_object* v___x_4412_; 
if (v_isShared_4410_ == 0)
{
lean_ctor_set_tag(v___x_4409_, 0);
v___x_4412_ = v___x_4409_;
goto v_reusejp_4411_;
}
else
{
lean_object* v_reuseFailAlloc_4413_; 
v_reuseFailAlloc_4413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4413_, 0, v_a_4407_);
v___x_4412_ = v_reuseFailAlloc_4413_;
goto v_reusejp_4411_;
}
v_reusejp_4411_:
{
return v___x_4412_;
}
}
}
else
{
lean_object* v_a_4415_; lean_object* v___x_4417_; uint8_t v_isShared_4418_; uint8_t v_isSharedCheck_4424_; 
v_a_4415_ = lean_ctor_get(v___x_4396_, 0);
v_isSharedCheck_4424_ = !lean_is_exclusive(v___x_4396_);
if (v_isSharedCheck_4424_ == 0)
{
v___x_4417_ = v___x_4396_;
v_isShared_4418_ = v_isSharedCheck_4424_;
goto v_resetjp_4416_;
}
else
{
lean_inc(v_a_4415_);
lean_dec(v___x_4396_);
v___x_4417_ = lean_box(0);
v_isShared_4418_ = v_isSharedCheck_4424_;
goto v_resetjp_4416_;
}
v_resetjp_4416_:
{
lean_object* v___x_4419_; uint8_t v___x_4420_; lean_object* v___x_4422_; 
v___x_4419_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4419_, 0, v_a_4415_);
v___x_4420_ = lean_unbox(v_a_4394_);
lean_dec(v_a_4394_);
lean_ctor_set_uint8(v___x_4419_, sizeof(void*)*1, v___x_4420_);
if (v_isShared_4418_ == 0)
{
lean_ctor_set(v___x_4417_, 0, v___x_4419_);
v___x_4422_ = v___x_4417_;
goto v_reusejp_4421_;
}
else
{
lean_object* v_reuseFailAlloc_4423_; 
v_reuseFailAlloc_4423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4423_, 0, v___x_4419_);
v___x_4422_ = v_reuseFailAlloc_4423_;
goto v_reusejp_4421_;
}
v_reusejp_4421_:
{
return v___x_4422_;
}
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_instDecidableEqMarkupContent_decEq(lean_object* v_x_4427_, lean_object* v_x_4428_){
_start:
{
uint8_t v_kind_4429_; lean_object* v_value_4430_; uint8_t v_kind_4431_; lean_object* v_value_4432_; uint8_t v___x_4433_; 
v_kind_4429_ = lean_ctor_get_uint8(v_x_4427_, sizeof(void*)*1);
v_value_4430_ = lean_ctor_get(v_x_4427_, 0);
v_kind_4431_ = lean_ctor_get_uint8(v_x_4428_, sizeof(void*)*1);
v_value_4432_ = lean_ctor_get(v_x_4428_, 0);
v___x_4433_ = l_Lean_Lsp_instDecidableEqMarkupKind(v_kind_4429_, v_kind_4431_);
if (v___x_4433_ == 0)
{
return v___x_4433_;
}
else
{
uint8_t v___x_4434_; 
v___x_4434_ = lean_string_dec_eq(v_value_4430_, v_value_4432_);
return v___x_4434_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instDecidableEqMarkupContent_decEq___boxed(lean_object* v_x_4435_, lean_object* v_x_4436_){
_start:
{
uint8_t v_res_4437_; lean_object* v_r_4438_; 
v_res_4437_ = l_Lean_Lsp_instDecidableEqMarkupContent_decEq(v_x_4435_, v_x_4436_);
lean_dec_ref(v_x_4436_);
lean_dec_ref(v_x_4435_);
v_r_4438_ = lean_box(v_res_4437_);
return v_r_4438_;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_instDecidableEqMarkupContent(lean_object* v_x_4439_, lean_object* v_x_4440_){
_start:
{
uint8_t v___x_4441_; 
v___x_4441_ = l_Lean_Lsp_instDecidableEqMarkupContent_decEq(v_x_4439_, v_x_4440_);
return v___x_4441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instDecidableEqMarkupContent___boxed(lean_object* v_x_4442_, lean_object* v_x_4443_){
_start:
{
uint8_t v_res_4444_; lean_object* v_r_4445_; 
v_res_4444_ = l_Lean_Lsp_instDecidableEqMarkupContent(v_x_4442_, v_x_4443_);
lean_dec_ref(v_x_4443_);
lean_dec_ref(v_x_4442_);
v_r_4445_ = lean_box(v_res_4444_);
return v_r_4445_;
}
}
LEAN_EXPORT uint64_t l_Lean_Lsp_instHashableMarkupContent_hash(lean_object* v_x_4446_){
_start:
{
uint8_t v_kind_4447_; lean_object* v_value_4448_; uint64_t v___x_4449_; uint64_t v___x_4450_; uint64_t v___x_4451_; uint64_t v___x_4452_; uint64_t v___x_4453_; 
v_kind_4447_ = lean_ctor_get_uint8(v_x_4446_, sizeof(void*)*1);
v_value_4448_ = lean_ctor_get(v_x_4446_, 0);
v___x_4449_ = 0ULL;
v___x_4450_ = l_Lean_Lsp_instHashableMarkupKind_hash(v_kind_4447_);
v___x_4451_ = lean_uint64_mix_hash(v___x_4449_, v___x_4450_);
v___x_4452_ = lean_string_hash(v_value_4448_);
v___x_4453_ = lean_uint64_mix_hash(v___x_4451_, v___x_4452_);
return v___x_4453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instHashableMarkupContent_hash___boxed(lean_object* v_x_4454_){
_start:
{
uint64_t v_res_4455_; lean_object* v_r_4456_; 
v_res_4455_ = l_Lean_Lsp_instHashableMarkupContent_hash(v_x_4454_);
lean_dec_ref(v_x_4454_);
v_r_4456_ = lean_box_uint64(v_res_4455_);
return v_r_4456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonProgressParams_toJson___redArg(lean_object* v_inst_4461_, lean_object* v_x_4462_){
_start:
{
lean_object* v_token_4463_; lean_object* v_value_4464_; lean_object* v___x_4466_; uint8_t v_isShared_4467_; uint8_t v_isSharedCheck_4485_; 
v_token_4463_ = lean_ctor_get(v_x_4462_, 0);
v_value_4464_ = lean_ctor_get(v_x_4462_, 1);
v_isSharedCheck_4485_ = !lean_is_exclusive(v_x_4462_);
if (v_isSharedCheck_4485_ == 0)
{
v___x_4466_ = v_x_4462_;
v_isShared_4467_ = v_isSharedCheck_4485_;
goto v_resetjp_4465_;
}
else
{
lean_inc(v_value_4464_);
lean_inc(v_token_4463_);
lean_dec(v_x_4462_);
v___x_4466_ = lean_box(0);
v_isShared_4467_ = v_isSharedCheck_4485_;
goto v_resetjp_4465_;
}
v_resetjp_4465_:
{
lean_object* v___x_4468_; lean_object* v___x_4469_; lean_object* v___x_4471_; 
v___x_4468_ = ((lean_object*)(l_Lean_Lsp_instToJsonProgressParams_toJson___redArg___closed__0));
v___x_4469_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4469_, 0, v_token_4463_);
if (v_isShared_4467_ == 0)
{
lean_ctor_set(v___x_4466_, 1, v___x_4469_);
lean_ctor_set(v___x_4466_, 0, v___x_4468_);
v___x_4471_ = v___x_4466_;
goto v_reusejp_4470_;
}
else
{
lean_object* v_reuseFailAlloc_4484_; 
v_reuseFailAlloc_4484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4484_, 0, v___x_4468_);
lean_ctor_set(v_reuseFailAlloc_4484_, 1, v___x_4469_);
v___x_4471_ = v_reuseFailAlloc_4484_;
goto v_reusejp_4470_;
}
v_reusejp_4470_:
{
lean_object* v___x_4472_; lean_object* v___x_4473_; lean_object* v___x_4474_; lean_object* v___x_4475_; lean_object* v___x_4476_; lean_object* v___x_4477_; lean_object* v___x_4478_; lean_object* v___x_4479_; lean_object* v___x_4480_; lean_object* v___x_4481_; lean_object* v___x_4482_; lean_object* v___x_4483_; 
v___x_4472_ = lean_box(0);
v___x_4473_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4473_, 0, v___x_4471_);
lean_ctor_set(v___x_4473_, 1, v___x_4472_);
v___x_4474_ = ((lean_object*)(l_Lean_Lsp_instToJsonSnippetString_toJson___closed__0));
v___x_4475_ = lean_apply_1(v_inst_4461_, v_value_4464_);
v___x_4476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4476_, 0, v___x_4474_);
lean_ctor_set(v___x_4476_, 1, v___x_4475_);
v___x_4477_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4477_, 0, v___x_4476_);
lean_ctor_set(v___x_4477_, 1, v___x_4472_);
v___x_4478_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4478_, 0, v___x_4477_);
lean_ctor_set(v___x_4478_, 1, v___x_4472_);
v___x_4479_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4479_, 0, v___x_4473_);
lean_ctor_set(v___x_4479_, 1, v___x_4478_);
v___x_4480_ = ((lean_object*)(l_Lean_Lsp_instToJsonProgressParams_toJson___redArg___closed__1));
v___x_4481_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__2));
v___x_4482_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go(lean_box(0), lean_box(0), v___x_4480_, v___x_4479_, v___x_4481_);
v___x_4483_ = l_Lean_Json_mkObj(v___x_4482_);
return v___x_4483_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonProgressParams_toJson(lean_object* v_00_u03b1_4486_, lean_object* v_inst_4487_, lean_object* v_x_4488_){
_start:
{
lean_object* v___x_4489_; 
v___x_4489_ = l_Lean_Lsp_instToJsonProgressParams_toJson___redArg(v_inst_4487_, v_x_4488_);
return v___x_4489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonProgressParams___redArg(lean_object* v_inst_4490_){
_start:
{
lean_object* v___x_4491_; 
v___x_4491_ = lean_alloc_closure((void*)(l_Lean_Lsp_instToJsonProgressParams_toJson), 3, 2);
lean_closure_set(v___x_4491_, 0, lean_box(0));
lean_closure_set(v___x_4491_, 1, v_inst_4490_);
return v___x_4491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonProgressParams(lean_object* v_00_u03b1_4492_, lean_object* v_inst_4493_){
_start:
{
lean_object* v___x_4494_; 
v___x_4494_ = lean_alloc_closure((void*)(l_Lean_Lsp_instToJsonProgressParams_toJson), 3, 2);
lean_closure_set(v___x_4494_, 0, lean_box(0));
lean_closure_set(v___x_4494_, 1, v_inst_4493_);
return v___x_4494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonWorkDoneProgressReport_toJson(lean_object* v_x_4498_){
_start:
{
lean_object* v_kind_4499_; lean_object* v_message_x3f_4500_; uint8_t v_cancellable_4501_; lean_object* v_percentage_x3f_4502_; lean_object* v___x_4503_; lean_object* v___x_4504_; lean_object* v___x_4505_; lean_object* v___x_4506_; lean_object* v___x_4507_; lean_object* v___x_4508_; lean_object* v___x_4509_; lean_object* v___x_4510_; lean_object* v___x_4511_; lean_object* v___x_4512_; lean_object* v___x_4513_; lean_object* v___x_4514_; lean_object* v___x_4515_; lean_object* v___x_4516_; lean_object* v___x_4517_; lean_object* v___x_4518_; lean_object* v___x_4519_; lean_object* v___x_4520_; lean_object* v___x_4521_; lean_object* v___x_4522_; 
v_kind_4499_ = lean_ctor_get(v_x_4498_, 0);
lean_inc_ref(v_kind_4499_);
v_message_x3f_4500_ = lean_ctor_get(v_x_4498_, 1);
lean_inc(v_message_x3f_4500_);
v_cancellable_4501_ = lean_ctor_get_uint8(v_x_4498_, sizeof(void*)*3);
v_percentage_x3f_4502_ = lean_ctor_get(v_x_4498_, 2);
lean_inc(v_percentage_x3f_4502_);
lean_dec_ref(v_x_4498_);
v___x_4503_ = ((lean_object*)(l_Lean_Lsp_instToJsonDocumentChange___lam__0___closed__0));
v___x_4504_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4504_, 0, v_kind_4499_);
v___x_4505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4505_, 0, v___x_4503_);
lean_ctor_set(v___x_4505_, 1, v___x_4504_);
v___x_4506_ = lean_box(0);
v___x_4507_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4507_, 0, v___x_4505_);
lean_ctor_set(v___x_4507_, 1, v___x_4506_);
v___x_4508_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkDoneProgressReport_toJson___closed__0));
v___x_4509_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextEdit_toJson_spec__1(v___x_4508_, v_message_x3f_4500_);
v___x_4510_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkDoneProgressReport_toJson___closed__1));
v___x_4511_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_4511_, 0, v_cancellable_4501_);
v___x_4512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4512_, 0, v___x_4510_);
lean_ctor_set(v___x_4512_, 1, v___x_4511_);
v___x_4513_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4513_, 0, v___x_4512_);
lean_ctor_set(v___x_4513_, 1, v___x_4506_);
v___x_4514_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkDoneProgressReport_toJson___closed__2));
v___x_4515_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonVersionedTextDocumentIdentifier_toJson_spec__0(v___x_4514_, v_percentage_x3f_4502_);
v___x_4516_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4516_, 0, v___x_4515_);
lean_ctor_set(v___x_4516_, 1, v___x_4506_);
v___x_4517_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4517_, 0, v___x_4513_);
lean_ctor_set(v___x_4517_, 1, v___x_4516_);
v___x_4518_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4518_, 0, v___x_4509_);
lean_ctor_set(v___x_4518_, 1, v___x_4517_);
v___x_4519_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4519_, 0, v___x_4507_);
lean_ctor_set(v___x_4519_, 1, v___x_4518_);
v___x_4520_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__2));
v___x_4521_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLocation_toJson_spec__0(v___x_4519_, v___x_4520_);
v___x_4522_ = l_Lean_Json_mkObj(v___x_4521_);
return v___x_4522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonWorkDoneProgressBegin_toJson(lean_object* v_x_4525_){
_start:
{
lean_object* v_toWorkDoneProgressReport_4526_; lean_object* v_title_4527_; lean_object* v___x_4529_; uint8_t v_isShared_4530_; uint8_t v_isSharedCheck_4562_; 
v_toWorkDoneProgressReport_4526_ = lean_ctor_get(v_x_4525_, 0);
v_title_4527_ = lean_ctor_get(v_x_4525_, 1);
v_isSharedCheck_4562_ = !lean_is_exclusive(v_x_4525_);
if (v_isSharedCheck_4562_ == 0)
{
v___x_4529_ = v_x_4525_;
v_isShared_4530_ = v_isSharedCheck_4562_;
goto v_resetjp_4528_;
}
else
{
lean_inc(v_title_4527_);
lean_inc(v_toWorkDoneProgressReport_4526_);
lean_dec(v_x_4525_);
v___x_4529_ = lean_box(0);
v_isShared_4530_ = v_isSharedCheck_4562_;
goto v_resetjp_4528_;
}
v_resetjp_4528_:
{
lean_object* v_kind_4531_; lean_object* v_message_x3f_4532_; uint8_t v_cancellable_4533_; lean_object* v_percentage_x3f_4534_; lean_object* v___x_4535_; lean_object* v___x_4536_; lean_object* v___x_4538_; 
v_kind_4531_ = lean_ctor_get(v_toWorkDoneProgressReport_4526_, 0);
lean_inc_ref(v_kind_4531_);
v_message_x3f_4532_ = lean_ctor_get(v_toWorkDoneProgressReport_4526_, 1);
lean_inc(v_message_x3f_4532_);
v_cancellable_4533_ = lean_ctor_get_uint8(v_toWorkDoneProgressReport_4526_, sizeof(void*)*3);
v_percentage_x3f_4534_ = lean_ctor_get(v_toWorkDoneProgressReport_4526_, 2);
lean_inc(v_percentage_x3f_4534_);
lean_dec_ref(v_toWorkDoneProgressReport_4526_);
v___x_4535_ = ((lean_object*)(l_Lean_Lsp_instToJsonDocumentChange___lam__0___closed__0));
v___x_4536_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4536_, 0, v_kind_4531_);
if (v_isShared_4530_ == 0)
{
lean_ctor_set(v___x_4529_, 1, v___x_4536_);
lean_ctor_set(v___x_4529_, 0, v___x_4535_);
v___x_4538_ = v___x_4529_;
goto v_reusejp_4537_;
}
else
{
lean_object* v_reuseFailAlloc_4561_; 
v_reuseFailAlloc_4561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4561_, 0, v___x_4535_);
lean_ctor_set(v_reuseFailAlloc_4561_, 1, v___x_4536_);
v___x_4538_ = v_reuseFailAlloc_4561_;
goto v_reusejp_4537_;
}
v_reusejp_4537_:
{
lean_object* v___x_4539_; lean_object* v___x_4540_; lean_object* v___x_4541_; lean_object* v___x_4542_; lean_object* v___x_4543_; lean_object* v___x_4544_; lean_object* v___x_4545_; lean_object* v___x_4546_; lean_object* v___x_4547_; lean_object* v___x_4548_; lean_object* v___x_4549_; lean_object* v___x_4550_; lean_object* v___x_4551_; lean_object* v___x_4552_; lean_object* v___x_4553_; lean_object* v___x_4554_; lean_object* v___x_4555_; lean_object* v___x_4556_; lean_object* v___x_4557_; lean_object* v___x_4558_; lean_object* v___x_4559_; lean_object* v___x_4560_; 
v___x_4539_ = lean_box(0);
v___x_4540_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4540_, 0, v___x_4538_);
lean_ctor_set(v___x_4540_, 1, v___x_4539_);
v___x_4541_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkDoneProgressReport_toJson___closed__0));
v___x_4542_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextEdit_toJson_spec__1(v___x_4541_, v_message_x3f_4532_);
v___x_4543_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkDoneProgressReport_toJson___closed__1));
v___x_4544_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_4544_, 0, v_cancellable_4533_);
v___x_4545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4545_, 0, v___x_4543_);
lean_ctor_set(v___x_4545_, 1, v___x_4544_);
v___x_4546_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4546_, 0, v___x_4545_);
lean_ctor_set(v___x_4546_, 1, v___x_4539_);
v___x_4547_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkDoneProgressReport_toJson___closed__2));
v___x_4548_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonVersionedTextDocumentIdentifier_toJson_spec__0(v___x_4547_, v_percentage_x3f_4534_);
v___x_4549_ = ((lean_object*)(l_Lean_Lsp_instToJsonCommand_toJson___closed__0));
v___x_4550_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4550_, 0, v_title_4527_);
v___x_4551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4551_, 0, v___x_4549_);
lean_ctor_set(v___x_4551_, 1, v___x_4550_);
v___x_4552_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4552_, 0, v___x_4551_);
lean_ctor_set(v___x_4552_, 1, v___x_4539_);
v___x_4553_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4553_, 0, v___x_4552_);
lean_ctor_set(v___x_4553_, 1, v___x_4539_);
v___x_4554_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4554_, 0, v___x_4548_);
lean_ctor_set(v___x_4554_, 1, v___x_4553_);
v___x_4555_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4555_, 0, v___x_4546_);
lean_ctor_set(v___x_4555_, 1, v___x_4554_);
v___x_4556_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4556_, 0, v___x_4542_);
lean_ctor_set(v___x_4556_, 1, v___x_4555_);
v___x_4557_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4557_, 0, v___x_4540_);
lean_ctor_set(v___x_4557_, 1, v___x_4556_);
v___x_4558_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__2));
v___x_4559_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLocation_toJson_spec__0(v___x_4557_, v___x_4558_);
v___x_4560_ = l_Lean_Json_mkObj(v___x_4559_);
return v___x_4560_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonWorkDoneProgressEnd_toJson(lean_object* v_x_4565_){
_start:
{
lean_object* v_kind_4566_; lean_object* v_message_x3f_4567_; lean_object* v___x_4569_; uint8_t v_isShared_4570_; uint8_t v_isSharedCheck_4585_; 
v_kind_4566_ = lean_ctor_get(v_x_4565_, 0);
v_message_x3f_4567_ = lean_ctor_get(v_x_4565_, 1);
v_isSharedCheck_4585_ = !lean_is_exclusive(v_x_4565_);
if (v_isSharedCheck_4585_ == 0)
{
v___x_4569_ = v_x_4565_;
v_isShared_4570_ = v_isSharedCheck_4585_;
goto v_resetjp_4568_;
}
else
{
lean_inc(v_message_x3f_4567_);
lean_inc(v_kind_4566_);
lean_dec(v_x_4565_);
v___x_4569_ = lean_box(0);
v_isShared_4570_ = v_isSharedCheck_4585_;
goto v_resetjp_4568_;
}
v_resetjp_4568_:
{
lean_object* v___x_4571_; lean_object* v___x_4572_; lean_object* v___x_4574_; 
v___x_4571_ = ((lean_object*)(l_Lean_Lsp_instToJsonDocumentChange___lam__0___closed__0));
v___x_4572_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4572_, 0, v_kind_4566_);
if (v_isShared_4570_ == 0)
{
lean_ctor_set(v___x_4569_, 1, v___x_4572_);
lean_ctor_set(v___x_4569_, 0, v___x_4571_);
v___x_4574_ = v___x_4569_;
goto v_reusejp_4573_;
}
else
{
lean_object* v_reuseFailAlloc_4584_; 
v_reuseFailAlloc_4584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4584_, 0, v___x_4571_);
lean_ctor_set(v_reuseFailAlloc_4584_, 1, v___x_4572_);
v___x_4574_ = v_reuseFailAlloc_4584_;
goto v_reusejp_4573_;
}
v_reusejp_4573_:
{
lean_object* v___x_4575_; lean_object* v___x_4576_; lean_object* v___x_4577_; lean_object* v___x_4578_; lean_object* v___x_4579_; lean_object* v___x_4580_; lean_object* v___x_4581_; lean_object* v___x_4582_; lean_object* v___x_4583_; 
v___x_4575_ = lean_box(0);
v___x_4576_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4576_, 0, v___x_4574_);
lean_ctor_set(v___x_4576_, 1, v___x_4575_);
v___x_4577_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkDoneProgressReport_toJson___closed__0));
v___x_4578_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextEdit_toJson_spec__1(v___x_4577_, v_message_x3f_4567_);
v___x_4579_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4579_, 0, v___x_4578_);
lean_ctor_set(v___x_4579_, 1, v___x_4575_);
v___x_4580_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4580_, 0, v___x_4576_);
lean_ctor_set(v___x_4580_, 1, v___x_4579_);
v___x_4581_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__2));
v___x_4582_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLocation_toJson_spec__0(v___x_4580_, v___x_4581_);
v___x_4583_ = l_Lean_Json_mkObj(v___x_4582_);
return v___x_4583_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonWorkDoneProgressParams_toJson(lean_object* v_x_4589_){
_start:
{
lean_object* v___x_4590_; lean_object* v___x_4591_; lean_object* v___x_4592_; lean_object* v___x_4593_; lean_object* v___x_4594_; lean_object* v___x_4595_; lean_object* v___x_4596_; 
v___x_4590_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkDoneProgressParams_toJson___closed__0));
v___x_4591_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextEdit_toJson_spec__1(v___x_4590_, v_x_4589_);
v___x_4592_ = lean_box(0);
v___x_4593_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4593_, 0, v___x_4591_);
lean_ctor_set(v___x_4593_, 1, v___x_4592_);
v___x_4594_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__2));
v___x_4595_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLocation_toJson_spec__0(v___x_4593_, v___x_4594_);
v___x_4596_ = l_Lean_Json_mkObj(v___x_4595_);
return v___x_4596_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkDoneProgressParams_fromJson___closed__2(void){
_start:
{
uint8_t v___x_4604_; lean_object* v___x_4605_; lean_object* v___x_4606_; 
v___x_4604_ = 1;
v___x_4605_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWorkDoneProgressParams_fromJson___closed__1));
v___x_4606_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4605_, v___x_4604_);
return v___x_4606_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkDoneProgressParams_fromJson___closed__3(void){
_start:
{
lean_object* v___x_4607_; lean_object* v___x_4608_; lean_object* v___x_4609_; 
v___x_4607_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__5));
v___x_4608_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkDoneProgressParams_fromJson___closed__2, &l_Lean_Lsp_instFromJsonWorkDoneProgressParams_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonWorkDoneProgressParams_fromJson___closed__2);
v___x_4609_ = lean_string_append(v___x_4608_, v___x_4607_);
return v___x_4609_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkDoneProgressParams_fromJson___closed__6(void){
_start:
{
uint8_t v___x_4613_; lean_object* v___x_4614_; lean_object* v___x_4615_; 
v___x_4613_ = 1;
v___x_4614_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWorkDoneProgressParams_fromJson___closed__5));
v___x_4615_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4614_, v___x_4613_);
return v___x_4615_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkDoneProgressParams_fromJson___closed__7(void){
_start:
{
lean_object* v___x_4616_; lean_object* v___x_4617_; lean_object* v___x_4618_; 
v___x_4616_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkDoneProgressParams_fromJson___closed__6, &l_Lean_Lsp_instFromJsonWorkDoneProgressParams_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonWorkDoneProgressParams_fromJson___closed__6);
v___x_4617_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkDoneProgressParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonWorkDoneProgressParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonWorkDoneProgressParams_fromJson___closed__3);
v___x_4618_ = lean_string_append(v___x_4617_, v___x_4616_);
return v___x_4618_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkDoneProgressParams_fromJson___closed__8(void){
_start:
{
lean_object* v___x_4619_; lean_object* v___x_4620_; lean_object* v___x_4621_; 
v___x_4619_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_4620_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkDoneProgressParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonWorkDoneProgressParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonWorkDoneProgressParams_fromJson___closed__7);
v___x_4621_ = lean_string_append(v___x_4620_, v___x_4619_);
return v___x_4621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonWorkDoneProgressParams_fromJson(lean_object* v_json_4622_){
_start:
{
lean_object* v___x_4623_; lean_object* v___x_4624_; 
v___x_4623_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkDoneProgressParams_toJson___closed__0));
v___x_4624_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextEdit_fromJson_spec__1(v_json_4622_, v___x_4623_);
if (lean_obj_tag(v___x_4624_) == 0)
{
lean_object* v_a_4625_; lean_object* v___x_4627_; uint8_t v_isShared_4628_; uint8_t v_isSharedCheck_4634_; 
v_a_4625_ = lean_ctor_get(v___x_4624_, 0);
v_isSharedCheck_4634_ = !lean_is_exclusive(v___x_4624_);
if (v_isSharedCheck_4634_ == 0)
{
v___x_4627_ = v___x_4624_;
v_isShared_4628_ = v_isSharedCheck_4634_;
goto v_resetjp_4626_;
}
else
{
lean_inc(v_a_4625_);
lean_dec(v___x_4624_);
v___x_4627_ = lean_box(0);
v_isShared_4628_ = v_isSharedCheck_4634_;
goto v_resetjp_4626_;
}
v_resetjp_4626_:
{
lean_object* v___x_4629_; lean_object* v___x_4630_; lean_object* v___x_4632_; 
v___x_4629_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkDoneProgressParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonWorkDoneProgressParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonWorkDoneProgressParams_fromJson___closed__8);
v___x_4630_ = lean_string_append(v___x_4629_, v_a_4625_);
lean_dec(v_a_4625_);
if (v_isShared_4628_ == 0)
{
lean_ctor_set(v___x_4627_, 0, v___x_4630_);
v___x_4632_ = v___x_4627_;
goto v_reusejp_4631_;
}
else
{
lean_object* v_reuseFailAlloc_4633_; 
v_reuseFailAlloc_4633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4633_, 0, v___x_4630_);
v___x_4632_ = v_reuseFailAlloc_4633_;
goto v_reusejp_4631_;
}
v_reusejp_4631_:
{
return v___x_4632_;
}
}
}
else
{
if (lean_obj_tag(v___x_4624_) == 0)
{
lean_object* v_a_4635_; lean_object* v___x_4637_; uint8_t v_isShared_4638_; uint8_t v_isSharedCheck_4642_; 
v_a_4635_ = lean_ctor_get(v___x_4624_, 0);
v_isSharedCheck_4642_ = !lean_is_exclusive(v___x_4624_);
if (v_isSharedCheck_4642_ == 0)
{
v___x_4637_ = v___x_4624_;
v_isShared_4638_ = v_isSharedCheck_4642_;
goto v_resetjp_4636_;
}
else
{
lean_inc(v_a_4635_);
lean_dec(v___x_4624_);
v___x_4637_ = lean_box(0);
v_isShared_4638_ = v_isSharedCheck_4642_;
goto v_resetjp_4636_;
}
v_resetjp_4636_:
{
lean_object* v___x_4640_; 
if (v_isShared_4638_ == 0)
{
lean_ctor_set_tag(v___x_4637_, 0);
v___x_4640_ = v___x_4637_;
goto v_reusejp_4639_;
}
else
{
lean_object* v_reuseFailAlloc_4641_; 
v_reuseFailAlloc_4641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4641_, 0, v_a_4635_);
v___x_4640_ = v_reuseFailAlloc_4641_;
goto v_reusejp_4639_;
}
v_reusejp_4639_:
{
return v___x_4640_;
}
}
}
else
{
lean_object* v_a_4643_; lean_object* v___x_4645_; uint8_t v_isShared_4646_; uint8_t v_isSharedCheck_4650_; 
v_a_4643_ = lean_ctor_get(v___x_4624_, 0);
v_isSharedCheck_4650_ = !lean_is_exclusive(v___x_4624_);
if (v_isSharedCheck_4650_ == 0)
{
v___x_4645_ = v___x_4624_;
v_isShared_4646_ = v_isSharedCheck_4650_;
goto v_resetjp_4644_;
}
else
{
lean_inc(v_a_4643_);
lean_dec(v___x_4624_);
v___x_4645_ = lean_box(0);
v_isShared_4646_ = v_isSharedCheck_4650_;
goto v_resetjp_4644_;
}
v_resetjp_4644_:
{
lean_object* v___x_4648_; 
if (v_isShared_4646_ == 0)
{
v___x_4648_ = v___x_4645_;
goto v_reusejp_4647_;
}
else
{
lean_object* v_reuseFailAlloc_4649_; 
v_reuseFailAlloc_4649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4649_, 0, v_a_4643_);
v___x_4648_ = v_reuseFailAlloc_4649_;
goto v_reusejp_4647_;
}
v_reusejp_4647_:
{
return v___x_4648_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonPartialResultParams_toJson(lean_object* v_x_4654_){
_start:
{
lean_object* v___x_4655_; lean_object* v___x_4656_; lean_object* v___x_4657_; lean_object* v___x_4658_; lean_object* v___x_4659_; lean_object* v___x_4660_; lean_object* v___x_4661_; 
v___x_4655_ = ((lean_object*)(l_Lean_Lsp_instToJsonPartialResultParams_toJson___closed__0));
v___x_4656_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextEdit_toJson_spec__1(v___x_4655_, v_x_4654_);
v___x_4657_ = lean_box(0);
v___x_4658_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4658_, 0, v___x_4656_);
lean_ctor_set(v___x_4658_, 1, v___x_4657_);
v___x_4659_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__2));
v___x_4660_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLocation_toJson_spec__0(v___x_4658_, v___x_4659_);
v___x_4661_ = l_Lean_Json_mkObj(v___x_4660_);
return v___x_4661_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPartialResultParams_fromJson___closed__2(void){
_start:
{
uint8_t v___x_4669_; lean_object* v___x_4670_; lean_object* v___x_4671_; 
v___x_4669_ = 1;
v___x_4670_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPartialResultParams_fromJson___closed__1));
v___x_4671_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4670_, v___x_4669_);
return v___x_4671_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPartialResultParams_fromJson___closed__3(void){
_start:
{
lean_object* v___x_4672_; lean_object* v___x_4673_; lean_object* v___x_4674_; 
v___x_4672_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__5));
v___x_4673_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPartialResultParams_fromJson___closed__2, &l_Lean_Lsp_instFromJsonPartialResultParams_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonPartialResultParams_fromJson___closed__2);
v___x_4674_ = lean_string_append(v___x_4673_, v___x_4672_);
return v___x_4674_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPartialResultParams_fromJson___closed__6(void){
_start:
{
uint8_t v___x_4678_; lean_object* v___x_4679_; lean_object* v___x_4680_; 
v___x_4678_ = 1;
v___x_4679_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPartialResultParams_fromJson___closed__5));
v___x_4680_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4679_, v___x_4678_);
return v___x_4680_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPartialResultParams_fromJson___closed__7(void){
_start:
{
lean_object* v___x_4681_; lean_object* v___x_4682_; lean_object* v___x_4683_; 
v___x_4681_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPartialResultParams_fromJson___closed__6, &l_Lean_Lsp_instFromJsonPartialResultParams_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonPartialResultParams_fromJson___closed__6);
v___x_4682_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPartialResultParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonPartialResultParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonPartialResultParams_fromJson___closed__3);
v___x_4683_ = lean_string_append(v___x_4682_, v___x_4681_);
return v___x_4683_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPartialResultParams_fromJson___closed__8(void){
_start:
{
lean_object* v___x_4684_; lean_object* v___x_4685_; lean_object* v___x_4686_; 
v___x_4684_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_4685_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPartialResultParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonPartialResultParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonPartialResultParams_fromJson___closed__7);
v___x_4686_ = lean_string_append(v___x_4685_, v___x_4684_);
return v___x_4686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonPartialResultParams_fromJson(lean_object* v_json_4687_){
_start:
{
lean_object* v___x_4688_; lean_object* v___x_4689_; 
v___x_4688_ = ((lean_object*)(l_Lean_Lsp_instToJsonPartialResultParams_toJson___closed__0));
v___x_4689_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextEdit_fromJson_spec__1(v_json_4687_, v___x_4688_);
if (lean_obj_tag(v___x_4689_) == 0)
{
lean_object* v_a_4690_; lean_object* v___x_4692_; uint8_t v_isShared_4693_; uint8_t v_isSharedCheck_4699_; 
v_a_4690_ = lean_ctor_get(v___x_4689_, 0);
v_isSharedCheck_4699_ = !lean_is_exclusive(v___x_4689_);
if (v_isSharedCheck_4699_ == 0)
{
v___x_4692_ = v___x_4689_;
v_isShared_4693_ = v_isSharedCheck_4699_;
goto v_resetjp_4691_;
}
else
{
lean_inc(v_a_4690_);
lean_dec(v___x_4689_);
v___x_4692_ = lean_box(0);
v_isShared_4693_ = v_isSharedCheck_4699_;
goto v_resetjp_4691_;
}
v_resetjp_4691_:
{
lean_object* v___x_4694_; lean_object* v___x_4695_; lean_object* v___x_4697_; 
v___x_4694_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPartialResultParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonPartialResultParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonPartialResultParams_fromJson___closed__8);
v___x_4695_ = lean_string_append(v___x_4694_, v_a_4690_);
lean_dec(v_a_4690_);
if (v_isShared_4693_ == 0)
{
lean_ctor_set(v___x_4692_, 0, v___x_4695_);
v___x_4697_ = v___x_4692_;
goto v_reusejp_4696_;
}
else
{
lean_object* v_reuseFailAlloc_4698_; 
v_reuseFailAlloc_4698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4698_, 0, v___x_4695_);
v___x_4697_ = v_reuseFailAlloc_4698_;
goto v_reusejp_4696_;
}
v_reusejp_4696_:
{
return v___x_4697_;
}
}
}
else
{
if (lean_obj_tag(v___x_4689_) == 0)
{
lean_object* v_a_4700_; lean_object* v___x_4702_; uint8_t v_isShared_4703_; uint8_t v_isSharedCheck_4707_; 
v_a_4700_ = lean_ctor_get(v___x_4689_, 0);
v_isSharedCheck_4707_ = !lean_is_exclusive(v___x_4689_);
if (v_isSharedCheck_4707_ == 0)
{
v___x_4702_ = v___x_4689_;
v_isShared_4703_ = v_isSharedCheck_4707_;
goto v_resetjp_4701_;
}
else
{
lean_inc(v_a_4700_);
lean_dec(v___x_4689_);
v___x_4702_ = lean_box(0);
v_isShared_4703_ = v_isSharedCheck_4707_;
goto v_resetjp_4701_;
}
v_resetjp_4701_:
{
lean_object* v___x_4705_; 
if (v_isShared_4703_ == 0)
{
lean_ctor_set_tag(v___x_4702_, 0);
v___x_4705_ = v___x_4702_;
goto v_reusejp_4704_;
}
else
{
lean_object* v_reuseFailAlloc_4706_; 
v_reuseFailAlloc_4706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4706_, 0, v_a_4700_);
v___x_4705_ = v_reuseFailAlloc_4706_;
goto v_reusejp_4704_;
}
v_reusejp_4704_:
{
return v___x_4705_;
}
}
}
else
{
lean_object* v_a_4708_; lean_object* v___x_4710_; uint8_t v_isShared_4711_; uint8_t v_isSharedCheck_4715_; 
v_a_4708_ = lean_ctor_get(v___x_4689_, 0);
v_isSharedCheck_4715_ = !lean_is_exclusive(v___x_4689_);
if (v_isSharedCheck_4715_ == 0)
{
v___x_4710_ = v___x_4689_;
v_isShared_4711_ = v_isSharedCheck_4715_;
goto v_resetjp_4709_;
}
else
{
lean_inc(v_a_4708_);
lean_dec(v___x_4689_);
v___x_4710_ = lean_box(0);
v_isShared_4711_ = v_isSharedCheck_4715_;
goto v_resetjp_4709_;
}
v_resetjp_4709_:
{
lean_object* v___x_4713_; 
if (v_isShared_4711_ == 0)
{
v___x_4713_ = v___x_4710_;
goto v_reusejp_4712_;
}
else
{
lean_object* v_reuseFailAlloc_4714_; 
v_reuseFailAlloc_4714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4714_, 0, v_a_4708_);
v___x_4713_ = v_reuseFailAlloc_4714_;
goto v_reusejp_4712_;
}
v_reusejp_4712_:
{
return v___x_4713_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonWorkDoneProgressOptions_toJson(uint8_t v_x_4719_){
_start:
{
lean_object* v___x_4720_; lean_object* v___x_4721_; lean_object* v___x_4722_; lean_object* v___x_4723_; lean_object* v___x_4724_; lean_object* v___x_4725_; lean_object* v___x_4726_; lean_object* v___x_4727_; lean_object* v___x_4728_; 
v___x_4720_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkDoneProgressOptions_toJson___closed__0));
v___x_4721_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_4721_, 0, v_x_4719_);
v___x_4722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4722_, 0, v___x_4720_);
lean_ctor_set(v___x_4722_, 1, v___x_4721_);
v___x_4723_ = lean_box(0);
v___x_4724_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4724_, 0, v___x_4722_);
lean_ctor_set(v___x_4724_, 1, v___x_4723_);
v___x_4725_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4725_, 0, v___x_4724_);
lean_ctor_set(v___x_4725_, 1, v___x_4723_);
v___x_4726_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__2));
v___x_4727_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLocation_toJson_spec__0(v___x_4725_, v___x_4726_);
v___x_4728_ = l_Lean_Json_mkObj(v___x_4727_);
return v___x_4728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonWorkDoneProgressOptions_toJson___boxed(lean_object* v_x_4729_){
_start:
{
uint8_t v_x_29__boxed_4730_; lean_object* v_res_4731_; 
v_x_29__boxed_4730_ = lean_unbox(v_x_4729_);
v_res_4731_ = l_Lean_Lsp_instToJsonWorkDoneProgressOptions_toJson(v_x_29__boxed_4730_);
return v_res_4731_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkDoneProgressOptions_fromJson___closed__2(void){
_start:
{
uint8_t v___x_4739_; lean_object* v___x_4740_; lean_object* v___x_4741_; 
v___x_4739_ = 1;
v___x_4740_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWorkDoneProgressOptions_fromJson___closed__1));
v___x_4741_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4740_, v___x_4739_);
return v___x_4741_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkDoneProgressOptions_fromJson___closed__3(void){
_start:
{
lean_object* v___x_4742_; lean_object* v___x_4743_; lean_object* v___x_4744_; 
v___x_4742_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__5));
v___x_4743_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkDoneProgressOptions_fromJson___closed__2, &l_Lean_Lsp_instFromJsonWorkDoneProgressOptions_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonWorkDoneProgressOptions_fromJson___closed__2);
v___x_4744_ = lean_string_append(v___x_4743_, v___x_4742_);
return v___x_4744_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkDoneProgressOptions_fromJson___closed__5(void){
_start:
{
uint8_t v___x_4747_; lean_object* v___x_4748_; lean_object* v___x_4749_; 
v___x_4747_ = 1;
v___x_4748_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWorkDoneProgressOptions_fromJson___closed__4));
v___x_4749_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4748_, v___x_4747_);
return v___x_4749_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkDoneProgressOptions_fromJson___closed__6(void){
_start:
{
lean_object* v___x_4750_; lean_object* v___x_4751_; lean_object* v___x_4752_; 
v___x_4750_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkDoneProgressOptions_fromJson___closed__5, &l_Lean_Lsp_instFromJsonWorkDoneProgressOptions_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonWorkDoneProgressOptions_fromJson___closed__5);
v___x_4751_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkDoneProgressOptions_fromJson___closed__3, &l_Lean_Lsp_instFromJsonWorkDoneProgressOptions_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonWorkDoneProgressOptions_fromJson___closed__3);
v___x_4752_ = lean_string_append(v___x_4751_, v___x_4750_);
return v___x_4752_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkDoneProgressOptions_fromJson___closed__7(void){
_start:
{
lean_object* v___x_4753_; lean_object* v___x_4754_; lean_object* v___x_4755_; 
v___x_4753_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_4754_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkDoneProgressOptions_fromJson___closed__6, &l_Lean_Lsp_instFromJsonWorkDoneProgressOptions_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonWorkDoneProgressOptions_fromJson___closed__6);
v___x_4755_ = lean_string_append(v___x_4754_, v___x_4753_);
return v___x_4755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonWorkDoneProgressOptions_fromJson(lean_object* v_json_4756_){
_start:
{
lean_object* v___x_4757_; lean_object* v___x_4758_; 
v___x_4757_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkDoneProgressOptions_toJson___closed__0));
v___x_4758_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonChangeAnnotation_fromJson_spec__0(v_json_4756_, v___x_4757_);
if (lean_obj_tag(v___x_4758_) == 0)
{
lean_object* v_a_4759_; lean_object* v___x_4761_; uint8_t v_isShared_4762_; uint8_t v_isSharedCheck_4768_; 
v_a_4759_ = lean_ctor_get(v___x_4758_, 0);
v_isSharedCheck_4768_ = !lean_is_exclusive(v___x_4758_);
if (v_isSharedCheck_4768_ == 0)
{
v___x_4761_ = v___x_4758_;
v_isShared_4762_ = v_isSharedCheck_4768_;
goto v_resetjp_4760_;
}
else
{
lean_inc(v_a_4759_);
lean_dec(v___x_4758_);
v___x_4761_ = lean_box(0);
v_isShared_4762_ = v_isSharedCheck_4768_;
goto v_resetjp_4760_;
}
v_resetjp_4760_:
{
lean_object* v___x_4763_; lean_object* v___x_4764_; lean_object* v___x_4766_; 
v___x_4763_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkDoneProgressOptions_fromJson___closed__7, &l_Lean_Lsp_instFromJsonWorkDoneProgressOptions_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonWorkDoneProgressOptions_fromJson___closed__7);
v___x_4764_ = lean_string_append(v___x_4763_, v_a_4759_);
lean_dec(v_a_4759_);
if (v_isShared_4762_ == 0)
{
lean_ctor_set(v___x_4761_, 0, v___x_4764_);
v___x_4766_ = v___x_4761_;
goto v_reusejp_4765_;
}
else
{
lean_object* v_reuseFailAlloc_4767_; 
v_reuseFailAlloc_4767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4767_, 0, v___x_4764_);
v___x_4766_ = v_reuseFailAlloc_4767_;
goto v_reusejp_4765_;
}
v_reusejp_4765_:
{
return v___x_4766_;
}
}
}
else
{
if (lean_obj_tag(v___x_4758_) == 0)
{
lean_object* v_a_4769_; lean_object* v___x_4771_; uint8_t v_isShared_4772_; uint8_t v_isSharedCheck_4776_; 
v_a_4769_ = lean_ctor_get(v___x_4758_, 0);
v_isSharedCheck_4776_ = !lean_is_exclusive(v___x_4758_);
if (v_isSharedCheck_4776_ == 0)
{
v___x_4771_ = v___x_4758_;
v_isShared_4772_ = v_isSharedCheck_4776_;
goto v_resetjp_4770_;
}
else
{
lean_inc(v_a_4769_);
lean_dec(v___x_4758_);
v___x_4771_ = lean_box(0);
v_isShared_4772_ = v_isSharedCheck_4776_;
goto v_resetjp_4770_;
}
v_resetjp_4770_:
{
lean_object* v___x_4774_; 
if (v_isShared_4772_ == 0)
{
lean_ctor_set_tag(v___x_4771_, 0);
v___x_4774_ = v___x_4771_;
goto v_reusejp_4773_;
}
else
{
lean_object* v_reuseFailAlloc_4775_; 
v_reuseFailAlloc_4775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4775_, 0, v_a_4769_);
v___x_4774_ = v_reuseFailAlloc_4775_;
goto v_reusejp_4773_;
}
v_reusejp_4773_:
{
return v___x_4774_;
}
}
}
else
{
lean_object* v_a_4777_; lean_object* v___x_4779_; uint8_t v_isShared_4780_; uint8_t v_isSharedCheck_4784_; 
v_a_4777_ = lean_ctor_get(v___x_4758_, 0);
v_isSharedCheck_4784_ = !lean_is_exclusive(v___x_4758_);
if (v_isSharedCheck_4784_ == 0)
{
v___x_4779_ = v___x_4758_;
v_isShared_4780_ = v_isSharedCheck_4784_;
goto v_resetjp_4778_;
}
else
{
lean_inc(v_a_4777_);
lean_dec(v___x_4758_);
v___x_4779_ = lean_box(0);
v_isShared_4780_ = v_isSharedCheck_4784_;
goto v_resetjp_4778_;
}
v_resetjp_4778_:
{
lean_object* v___x_4782_; 
if (v_isShared_4780_ == 0)
{
v___x_4782_ = v___x_4779_;
goto v_reusejp_4781_;
}
else
{
lean_object* v_reuseFailAlloc_4783_; 
v_reuseFailAlloc_4783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4783_, 0, v_a_4777_);
v___x_4782_ = v_reuseFailAlloc_4783_;
goto v_reusejp_4781_;
}
v_reusejp_4781_:
{
return v___x_4782_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonResolveSupport_fromJson_spec__0_spec__0_spec__1(size_t v_sz_4787_, size_t v_i_4788_, lean_object* v_bs_4789_){
_start:
{
uint8_t v___x_4790_; 
v___x_4790_ = lean_usize_dec_lt(v_i_4788_, v_sz_4787_);
if (v___x_4790_ == 0)
{
lean_object* v___x_4791_; 
v___x_4791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4791_, 0, v_bs_4789_);
return v___x_4791_;
}
else
{
lean_object* v_v_4792_; lean_object* v___x_4793_; 
v_v_4792_ = lean_array_uget_borrowed(v_bs_4789_, v_i_4788_);
lean_inc(v_v_4792_);
v___x_4793_ = l_Lean_Json_getStr_x3f(v_v_4792_);
if (lean_obj_tag(v___x_4793_) == 0)
{
lean_object* v_a_4794_; lean_object* v___x_4796_; uint8_t v_isShared_4797_; uint8_t v_isSharedCheck_4801_; 
lean_dec_ref(v_bs_4789_);
v_a_4794_ = lean_ctor_get(v___x_4793_, 0);
v_isSharedCheck_4801_ = !lean_is_exclusive(v___x_4793_);
if (v_isSharedCheck_4801_ == 0)
{
v___x_4796_ = v___x_4793_;
v_isShared_4797_ = v_isSharedCheck_4801_;
goto v_resetjp_4795_;
}
else
{
lean_inc(v_a_4794_);
lean_dec(v___x_4793_);
v___x_4796_ = lean_box(0);
v_isShared_4797_ = v_isSharedCheck_4801_;
goto v_resetjp_4795_;
}
v_resetjp_4795_:
{
lean_object* v___x_4799_; 
if (v_isShared_4797_ == 0)
{
v___x_4799_ = v___x_4796_;
goto v_reusejp_4798_;
}
else
{
lean_object* v_reuseFailAlloc_4800_; 
v_reuseFailAlloc_4800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4800_, 0, v_a_4794_);
v___x_4799_ = v_reuseFailAlloc_4800_;
goto v_reusejp_4798_;
}
v_reusejp_4798_:
{
return v___x_4799_;
}
}
}
else
{
lean_object* v_a_4802_; lean_object* v___x_4803_; lean_object* v_bs_x27_4804_; size_t v___x_4805_; size_t v___x_4806_; lean_object* v___x_4807_; 
v_a_4802_ = lean_ctor_get(v___x_4793_, 0);
lean_inc(v_a_4802_);
lean_dec_ref(v___x_4793_);
v___x_4803_ = lean_unsigned_to_nat(0u);
v_bs_x27_4804_ = lean_array_uset(v_bs_4789_, v_i_4788_, v___x_4803_);
v___x_4805_ = ((size_t)1ULL);
v___x_4806_ = lean_usize_add(v_i_4788_, v___x_4805_);
v___x_4807_ = lean_array_uset(v_bs_x27_4804_, v_i_4788_, v_a_4802_);
v_i_4788_ = v___x_4806_;
v_bs_4789_ = v___x_4807_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonResolveSupport_fromJson_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_4809_, lean_object* v_i_4810_, lean_object* v_bs_4811_){
_start:
{
size_t v_sz_boxed_4812_; size_t v_i_boxed_4813_; lean_object* v_res_4814_; 
v_sz_boxed_4812_ = lean_unbox_usize(v_sz_4809_);
lean_dec(v_sz_4809_);
v_i_boxed_4813_ = lean_unbox_usize(v_i_4810_);
lean_dec(v_i_4810_);
v_res_4814_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonResolveSupport_fromJson_spec__0_spec__0_spec__1(v_sz_boxed_4812_, v_i_boxed_4813_, v_bs_4811_);
return v_res_4814_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonResolveSupport_fromJson_spec__0_spec__0(lean_object* v_x_4815_){
_start:
{
if (lean_obj_tag(v_x_4815_) == 4)
{
lean_object* v_elems_4816_; size_t v_sz_4817_; size_t v___x_4818_; lean_object* v___x_4819_; 
v_elems_4816_ = lean_ctor_get(v_x_4815_, 0);
lean_inc_ref(v_elems_4816_);
lean_dec_ref(v_x_4815_);
v_sz_4817_ = lean_array_size(v_elems_4816_);
v___x_4818_ = ((size_t)0ULL);
v___x_4819_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonResolveSupport_fromJson_spec__0_spec__0_spec__1(v_sz_4817_, v___x_4818_, v_elems_4816_);
return v___x_4819_;
}
else
{
lean_object* v___x_4820_; lean_object* v___x_4821_; lean_object* v___x_4822_; lean_object* v___x_4823_; lean_object* v___x_4824_; lean_object* v___x_4825_; lean_object* v___x_4826_; 
v___x_4820_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCommand_fromJson_spec__0_spec__0_spec__1___closed__0));
v___x_4821_ = lean_unsigned_to_nat(80u);
v___x_4822_ = l_Lean_Json_pretty(v_x_4815_, v___x_4821_);
v___x_4823_ = lean_string_append(v___x_4820_, v___x_4822_);
lean_dec_ref(v___x_4822_);
v___x_4824_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCommand_fromJson_spec__0_spec__0_spec__1___closed__1));
v___x_4825_ = lean_string_append(v___x_4823_, v___x_4824_);
v___x_4826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4826_, 0, v___x_4825_);
return v___x_4826_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonResolveSupport_fromJson_spec__0(lean_object* v_j_4827_, lean_object* v_k_4828_){
_start:
{
lean_object* v___x_4829_; lean_object* v___x_4830_; 
v___x_4829_ = l_Lean_Json_getObjValD(v_j_4827_, v_k_4828_);
v___x_4830_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonResolveSupport_fromJson_spec__0_spec__0(v___x_4829_);
return v___x_4830_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonResolveSupport_fromJson_spec__0___boxed(lean_object* v_j_4831_, lean_object* v_k_4832_){
_start:
{
lean_object* v_res_4833_; 
v_res_4833_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonResolveSupport_fromJson_spec__0(v_j_4831_, v_k_4832_);
lean_dec_ref(v_k_4832_);
return v_res_4833_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonResolveSupport_fromJson___closed__3(void){
_start:
{
uint8_t v___x_4840_; lean_object* v___x_4841_; lean_object* v___x_4842_; 
v___x_4840_ = 1;
v___x_4841_ = ((lean_object*)(l_Lean_Lsp_instFromJsonResolveSupport_fromJson___closed__2));
v___x_4842_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4841_, v___x_4840_);
return v___x_4842_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonResolveSupport_fromJson___closed__4(void){
_start:
{
lean_object* v___x_4843_; lean_object* v___x_4844_; lean_object* v___x_4845_; 
v___x_4843_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__5));
v___x_4844_ = lean_obj_once(&l_Lean_Lsp_instFromJsonResolveSupport_fromJson___closed__3, &l_Lean_Lsp_instFromJsonResolveSupport_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonResolveSupport_fromJson___closed__3);
v___x_4845_ = lean_string_append(v___x_4844_, v___x_4843_);
return v___x_4845_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonResolveSupport_fromJson___closed__6(void){
_start:
{
uint8_t v___x_4848_; lean_object* v___x_4849_; lean_object* v___x_4850_; 
v___x_4848_ = 1;
v___x_4849_ = ((lean_object*)(l_Lean_Lsp_instFromJsonResolveSupport_fromJson___closed__5));
v___x_4850_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4849_, v___x_4848_);
return v___x_4850_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonResolveSupport_fromJson___closed__7(void){
_start:
{
lean_object* v___x_4851_; lean_object* v___x_4852_; lean_object* v___x_4853_; 
v___x_4851_ = lean_obj_once(&l_Lean_Lsp_instFromJsonResolveSupport_fromJson___closed__6, &l_Lean_Lsp_instFromJsonResolveSupport_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonResolveSupport_fromJson___closed__6);
v___x_4852_ = lean_obj_once(&l_Lean_Lsp_instFromJsonResolveSupport_fromJson___closed__4, &l_Lean_Lsp_instFromJsonResolveSupport_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonResolveSupport_fromJson___closed__4);
v___x_4853_ = lean_string_append(v___x_4852_, v___x_4851_);
return v___x_4853_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonResolveSupport_fromJson___closed__8(void){
_start:
{
lean_object* v___x_4854_; lean_object* v___x_4855_; lean_object* v___x_4856_; 
v___x_4854_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_4855_ = lean_obj_once(&l_Lean_Lsp_instFromJsonResolveSupport_fromJson___closed__7, &l_Lean_Lsp_instFromJsonResolveSupport_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonResolveSupport_fromJson___closed__7);
v___x_4856_ = lean_string_append(v___x_4855_, v___x_4854_);
return v___x_4856_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonResolveSupport_fromJson(lean_object* v_json_4857_){
_start:
{
lean_object* v___x_4858_; lean_object* v___x_4859_; 
v___x_4858_ = ((lean_object*)(l_Lean_Lsp_instFromJsonResolveSupport_fromJson___closed__0));
v___x_4859_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonResolveSupport_fromJson_spec__0(v_json_4857_, v___x_4858_);
if (lean_obj_tag(v___x_4859_) == 0)
{
lean_object* v_a_4860_; lean_object* v___x_4862_; uint8_t v_isShared_4863_; uint8_t v_isSharedCheck_4869_; 
v_a_4860_ = lean_ctor_get(v___x_4859_, 0);
v_isSharedCheck_4869_ = !lean_is_exclusive(v___x_4859_);
if (v_isSharedCheck_4869_ == 0)
{
v___x_4862_ = v___x_4859_;
v_isShared_4863_ = v_isSharedCheck_4869_;
goto v_resetjp_4861_;
}
else
{
lean_inc(v_a_4860_);
lean_dec(v___x_4859_);
v___x_4862_ = lean_box(0);
v_isShared_4863_ = v_isSharedCheck_4869_;
goto v_resetjp_4861_;
}
v_resetjp_4861_:
{
lean_object* v___x_4864_; lean_object* v___x_4865_; lean_object* v___x_4867_; 
v___x_4864_ = lean_obj_once(&l_Lean_Lsp_instFromJsonResolveSupport_fromJson___closed__8, &l_Lean_Lsp_instFromJsonResolveSupport_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonResolveSupport_fromJson___closed__8);
v___x_4865_ = lean_string_append(v___x_4864_, v_a_4860_);
lean_dec(v_a_4860_);
if (v_isShared_4863_ == 0)
{
lean_ctor_set(v___x_4862_, 0, v___x_4865_);
v___x_4867_ = v___x_4862_;
goto v_reusejp_4866_;
}
else
{
lean_object* v_reuseFailAlloc_4868_; 
v_reuseFailAlloc_4868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4868_, 0, v___x_4865_);
v___x_4867_ = v_reuseFailAlloc_4868_;
goto v_reusejp_4866_;
}
v_reusejp_4866_:
{
return v___x_4867_;
}
}
}
else
{
if (lean_obj_tag(v___x_4859_) == 0)
{
lean_object* v_a_4870_; lean_object* v___x_4872_; uint8_t v_isShared_4873_; uint8_t v_isSharedCheck_4877_; 
v_a_4870_ = lean_ctor_get(v___x_4859_, 0);
v_isSharedCheck_4877_ = !lean_is_exclusive(v___x_4859_);
if (v_isSharedCheck_4877_ == 0)
{
v___x_4872_ = v___x_4859_;
v_isShared_4873_ = v_isSharedCheck_4877_;
goto v_resetjp_4871_;
}
else
{
lean_inc(v_a_4870_);
lean_dec(v___x_4859_);
v___x_4872_ = lean_box(0);
v_isShared_4873_ = v_isSharedCheck_4877_;
goto v_resetjp_4871_;
}
v_resetjp_4871_:
{
lean_object* v___x_4875_; 
if (v_isShared_4873_ == 0)
{
lean_ctor_set_tag(v___x_4872_, 0);
v___x_4875_ = v___x_4872_;
goto v_reusejp_4874_;
}
else
{
lean_object* v_reuseFailAlloc_4876_; 
v_reuseFailAlloc_4876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4876_, 0, v_a_4870_);
v___x_4875_ = v_reuseFailAlloc_4876_;
goto v_reusejp_4874_;
}
v_reusejp_4874_:
{
return v___x_4875_;
}
}
}
else
{
lean_object* v_a_4878_; lean_object* v___x_4880_; uint8_t v_isShared_4881_; uint8_t v_isSharedCheck_4885_; 
v_a_4878_ = lean_ctor_get(v___x_4859_, 0);
v_isSharedCheck_4885_ = !lean_is_exclusive(v___x_4859_);
if (v_isSharedCheck_4885_ == 0)
{
v___x_4880_ = v___x_4859_;
v_isShared_4881_ = v_isSharedCheck_4885_;
goto v_resetjp_4879_;
}
else
{
lean_inc(v_a_4878_);
lean_dec(v___x_4859_);
v___x_4880_ = lean_box(0);
v_isShared_4881_ = v_isSharedCheck_4885_;
goto v_resetjp_4879_;
}
v_resetjp_4879_:
{
lean_object* v___x_4883_; 
if (v_isShared_4881_ == 0)
{
v___x_4883_ = v___x_4880_;
goto v_reusejp_4882_;
}
else
{
lean_object* v_reuseFailAlloc_4884_; 
v_reuseFailAlloc_4884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4884_, 0, v_a_4878_);
v___x_4883_ = v_reuseFailAlloc_4884_;
goto v_reusejp_4882_;
}
v_reusejp_4882_:
{
return v___x_4883_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonResolveSupport_toJson_spec__0_spec__0(size_t v_sz_4888_, size_t v_i_4889_, lean_object* v_bs_4890_){
_start:
{
uint8_t v___x_4891_; 
v___x_4891_ = lean_usize_dec_lt(v_i_4889_, v_sz_4888_);
if (v___x_4891_ == 0)
{
return v_bs_4890_;
}
else
{
lean_object* v_v_4892_; lean_object* v___x_4893_; lean_object* v_bs_x27_4894_; lean_object* v___x_4895_; size_t v___x_4896_; size_t v___x_4897_; lean_object* v___x_4898_; 
v_v_4892_ = lean_array_uget(v_bs_4890_, v_i_4889_);
v___x_4893_ = lean_unsigned_to_nat(0u);
v_bs_x27_4894_ = lean_array_uset(v_bs_4890_, v_i_4889_, v___x_4893_);
v___x_4895_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4895_, 0, v_v_4892_);
v___x_4896_ = ((size_t)1ULL);
v___x_4897_ = lean_usize_add(v_i_4889_, v___x_4896_);
v___x_4898_ = lean_array_uset(v_bs_x27_4894_, v_i_4889_, v___x_4895_);
v_i_4889_ = v___x_4897_;
v_bs_4890_ = v___x_4898_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonResolveSupport_toJson_spec__0_spec__0___boxed(lean_object* v_sz_4900_, lean_object* v_i_4901_, lean_object* v_bs_4902_){
_start:
{
size_t v_sz_boxed_4903_; size_t v_i_boxed_4904_; lean_object* v_res_4905_; 
v_sz_boxed_4903_ = lean_unbox_usize(v_sz_4900_);
lean_dec(v_sz_4900_);
v_i_boxed_4904_ = lean_unbox_usize(v_i_4901_);
lean_dec(v_i_4901_);
v_res_4905_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonResolveSupport_toJson_spec__0_spec__0(v_sz_boxed_4903_, v_i_boxed_4904_, v_bs_4902_);
return v_res_4905_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Lsp_instToJsonResolveSupport_toJson_spec__0(lean_object* v_a_4906_){
_start:
{
size_t v_sz_4907_; size_t v___x_4908_; lean_object* v___x_4909_; lean_object* v___x_4910_; 
v_sz_4907_ = lean_array_size(v_a_4906_);
v___x_4908_ = ((size_t)0ULL);
v___x_4909_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonResolveSupport_toJson_spec__0_spec__0(v_sz_4907_, v___x_4908_, v_a_4906_);
v___x_4910_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_4910_, 0, v___x_4909_);
return v___x_4910_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonResolveSupport_toJson(lean_object* v_x_4911_){
_start:
{
lean_object* v___x_4912_; lean_object* v___x_4913_; lean_object* v___x_4914_; lean_object* v___x_4915_; lean_object* v___x_4916_; lean_object* v___x_4917_; lean_object* v___x_4918_; lean_object* v___x_4919_; lean_object* v___x_4920_; 
v___x_4912_ = ((lean_object*)(l_Lean_Lsp_instFromJsonResolveSupport_fromJson___closed__0));
v___x_4913_ = l_Array_toJson___at___00Lean_Lsp_instToJsonResolveSupport_toJson_spec__0(v_x_4911_);
v___x_4914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4914_, 0, v___x_4912_);
lean_ctor_set(v___x_4914_, 1, v___x_4913_);
v___x_4915_ = lean_box(0);
v___x_4916_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4916_, 0, v___x_4914_);
lean_ctor_set(v___x_4916_, 1, v___x_4915_);
v___x_4917_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4917_, 0, v___x_4916_);
lean_ctor_set(v___x_4917_, 1, v___x_4915_);
v___x_4918_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__2));
v___x_4919_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLocation_toJson_spec__0(v___x_4917_, v___x_4918_);
v___x_4920_ = l_Lean_Json_mkObj(v___x_4919_);
return v___x_4920_;
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

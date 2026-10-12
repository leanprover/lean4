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
lean_object* l_String_compare___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Json_getObj_x3f(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint64_t lean_string_hash(lean_object*);
lean_object* l_Lean_Lsp_instToJsonPosition_toJson(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Lsp_instFromJsonPosition_fromJson(lean_object*);
lean_object* l_Lean_Array_fromJson_x3f(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_Lsp_instInhabitedRange_default;
uint8_t lean_string_compare(lean_object*, lean_object*);
uint8_t l_Lean_Lsp_instOrdRange_ord(lean_object*, lean_object*);
lean_object* l_Lean_Array_toJson(lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocationLink_fromJson_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocationLink_fromJson_spec__0_spec__0___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocationLink_fromJson_spec__0_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocationLink_fromJson_spec__0_spec__0(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonCommand_toJson_spec__0_spec__0_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonCommand_toJson_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonCommand_toJson_spec__0_spec__0(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCommand_fromJson_spec__0_spec__0_spec__1_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCommand_fromJson_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCommand_fromJson_spec__0_spec__0_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "expected JSON array, got '"};
static const lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCommand_fromJson_spec__0_spec__0_spec__1___closed__0 = (const lean_object*)&l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCommand_fromJson_spec__0_spec__0_spec__1___closed__0_value;
static const lean_string_object l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCommand_fromJson_spec__0_spec__0_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCommand_fromJson_spec__0_spec__0_spec__1___closed__1 = (const lean_object*)&l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCommand_fromJson_spec__0_spec__0_spec__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCommand_fromJson_spec__0_spec__0_spec__1(lean_object*);
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCommand_fromJson_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCommand_fromJson_spec__0_spec__0___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCommand_fromJson_spec__0_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCommand_fromJson_spec__0_spec__0(lean_object*);
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
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextEdit_fromJson_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextEdit_fromJson_spec__0_spec__0___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextEdit_fromJson_spec__0_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextEdit_fromJson_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextEdit_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextEdit_fromJson_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextEdit_fromJson_spec__1_spec__2(lean_object*);
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
static const lean_closure_object l_Lean_Lsp_instFromJsonTextEditBatch___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Array_fromJson_x3f, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonTextEdit___closed__0_value)} };
static const lean_object* l_Lean_Lsp_instFromJsonTextEditBatch___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonTextEditBatch___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonTextEditBatch = (const lean_object*)&l_Lean_Lsp_instFromJsonTextEditBatch___closed__0_value;
static const lean_closure_object l_Lean_Lsp_instToJsonTextEditBatch___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Array_toJson, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instToJsonTextEdit___closed__0_value)} };
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
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson_spec__0_spec__0___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson_spec__0_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson_spec__0_spec__0(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonTextDocumentEdit_toJson_spec__0_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonTextDocumentEdit_toJson_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonTextDocumentEdit_toJson_spec__0(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentEdit_fromJson_spec__1_spec__1_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentEdit_fromJson_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentEdit_fromJson_spec__1_spec__1(lean_object*);
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
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCreateFile_fromJson_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCreateFile_fromJson_spec__0_spec__0___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCreateFile_fromJson_spec__0_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCreateFile_fromJson_spec__0_spec__0(lean_object*);
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
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDeleteFile_fromJson_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDeleteFile_fromJson_spec__0_spec__0___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDeleteFile_fromJson_spec__0_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDeleteFile_fromJson_spec__0_spec__0(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Lsp_DocumentChange_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DocumentChange_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEdit_toJson_spec__1_spec__2_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEdit_toJson_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEdit_toJson_spec__1_spec__2(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__1_spec__2_spec__4_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__2_spec__4_spec__7_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__2_spec__4_spec__7(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__2_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__2_spec__4___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__2_spec__4___closed__0_value;
static const lean_closure_object l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__2_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_compare___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__2_spec__4___closed__1 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__2_spec__4___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__2_spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__1_spec__2_spec__4_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__1_spec__2_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__1_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__0_spec__0_spec__1_spec__4___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__0_spec__0_spec__1_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__0_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__0_spec__0_spec__1(lean_object*);
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__0_spec__0___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__0_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__0_spec__0(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__1_spec__2_spec__4_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l_Lean_Lsp_WorkspaceEdit_instAppend___lam__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_WorkspaceEdit_instAppend___lam__1, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__2_spec__4___closed__1_value)} };
static const lean_object* l_Lean_Lsp_WorkspaceEdit_instAppend___lam__4___closed__0 = (const lean_object*)&l_Lean_Lsp_WorkspaceEdit_instAppend___lam__4___closed__0_value;
static const lean_closure_object l_Lean_Lsp_WorkspaceEdit_instAppend___lam__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_WorkspaceEdit_instAppend___lam__3, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__2_spec__4___closed__1_value)} };
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
static const lean_closure_object l_Lean_Lsp_instFromJsonDocumentSelector___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Array_fromJson_x3f, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonDocumentFilter___closed__0_value)} };
static const lean_object* l_Lean_Lsp_instFromJsonDocumentSelector___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonDocumentSelector___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonDocumentSelector = (const lean_object*)&l_Lean_Lsp_instFromJsonDocumentSelector___closed__0_value;
static const lean_closure_object l_Lean_Lsp_instToJsonDocumentSelector___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Array_toJson, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instToJsonDocumentFilter___closed__0_value)} };
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonTextDocumentRegistrationOptions_toJson_spec__0_spec__0_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonTextDocumentRegistrationOptions_toJson_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonTextDocumentRegistrationOptions_toJson_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextDocumentRegistrationOptions_toJson_spec__0(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instToJsonTextDocumentRegistrationOptions_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "documentSelector"};
static const lean_object* l_Lean_Lsp_instToJsonTextDocumentRegistrationOptions_toJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonTextDocumentRegistrationOptions_toJson___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonTextDocumentRegistrationOptions_toJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonTextDocumentRegistrationOptions___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonTextDocumentRegistrationOptions_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonTextDocumentRegistrationOptions___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonTextDocumentRegistrationOptions___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonTextDocumentRegistrationOptions = (const lean_object*)&l_Lean_Lsp_instToJsonTextDocumentRegistrationOptions___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson_spec__0_spec__0_spec__1_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson_spec__0_spec__0_spec__1(lean_object*);
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson_spec__0_spec__0___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson_spec__0_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson_spec__0_spec__0(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Lsp_MarkupKind_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Lsp_MarkupKind_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonResolveSupport_fromJson_spec__0_spec__0_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonResolveSupport_fromJson_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonResolveSupport_fromJson_spec__0_spec__0(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonResolveSupport_toJson_spec__0_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonResolveSupport_toJson_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonResolveSupport_toJson_spec__0(lean_object*);
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
uint8_t l_Lean_Lsp_instBEqLocation_beq(lean_object* v_x_7_, lean_object* v_x_8_){
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
LEAN_EXPORT void l_Lean_Lsp_instBEqLocation_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_7_ = stack[0].m_obj;
lean_object* v_x_8_ = stack[1].m_obj;
uint8_t v_res_15_;
v_res_15_ = l_Lean_Lsp_instBEqLocation_beq(v_x_7_, v_x_8_);
stack->m_num = v_res_15_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqLocation_beq___boxed(lean_object* v_x_16_, lean_object* v_x_17_){
_start:
{
uint8_t v_res_18_; lean_object* v_r_19_; 
v_res_18_ = l_Lean_Lsp_instBEqLocation_beq(v_x_16_, v_x_17_);
lean_dec_ref(v_x_17_);
lean_dec_ref(v_x_16_);
v_r_19_ = lean_box(v_res_18_);
return v_r_19_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLocation_toJson_spec__0(lean_object* v_a_22_, lean_object* v_a_23_){
_start:
{
if (lean_obj_tag(v_a_22_) == 0)
{
lean_object* v___x_24_; 
v___x_24_ = lean_array_to_list(v_a_23_);
return v___x_24_;
}
else
{
lean_object* v_head_25_; lean_object* v_tail_26_; lean_object* v___x_27_; 
v_head_25_ = lean_ctor_get(v_a_22_, 0);
lean_inc(v_head_25_);
v_tail_26_ = lean_ctor_get(v_a_22_, 1);
lean_inc(v_tail_26_);
lean_dec_ref_known(v_a_22_, 2);
v___x_27_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_23_, v_head_25_);
v_a_22_ = v_tail_26_;
v_a_23_ = v___x_27_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLocation_toJson(lean_object* v_x_33_){
_start:
{
lean_object* v_uri_34_; lean_object* v_range_35_; lean_object* v___x_37_; uint8_t v_isShared_38_; uint8_t v_isSharedCheck_55_; 
v_uri_34_ = lean_ctor_get(v_x_33_, 0);
v_range_35_ = lean_ctor_get(v_x_33_, 1);
v_isSharedCheck_55_ = !lean_is_exclusive(v_x_33_);
if (v_isSharedCheck_55_ == 0)
{
v___x_37_ = v_x_33_;
v_isShared_38_ = v_isSharedCheck_55_;
goto v_resetjp_36_;
}
else
{
lean_inc(v_range_35_);
lean_inc(v_uri_34_);
lean_dec(v_x_33_);
v___x_37_ = lean_box(0);
v_isShared_38_ = v_isSharedCheck_55_;
goto v_resetjp_36_;
}
v_resetjp_36_:
{
lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_42_; 
v___x_39_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__0));
v___x_40_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_40_, 0, v_uri_34_);
if (v_isShared_38_ == 0)
{
lean_ctor_set(v___x_37_, 1, v___x_40_);
lean_ctor_set(v___x_37_, 0, v___x_39_);
v___x_42_ = v___x_37_;
goto v_reusejp_41_;
}
else
{
lean_object* v_reuseFailAlloc_54_; 
v_reuseFailAlloc_54_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_54_, 0, v___x_39_);
lean_ctor_set(v_reuseFailAlloc_54_, 1, v___x_40_);
v___x_42_ = v_reuseFailAlloc_54_;
goto v_reusejp_41_;
}
v_reusejp_41_:
{
lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_43_ = lean_box(0);
v___x_44_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_44_, 0, v___x_42_);
lean_ctor_set(v___x_44_, 1, v___x_43_);
v___x_45_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__1));
v___x_46_ = l_Lean_Lsp_instToJsonRange_toJson(v_range_35_);
v___x_47_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_47_, 0, v___x_45_);
lean_ctor_set(v___x_47_, 1, v___x_46_);
v___x_48_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_48_, 0, v___x_47_);
lean_ctor_set(v___x_48_, 1, v___x_43_);
v___x_49_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_49_, 0, v___x_48_);
lean_ctor_set(v___x_49_, 1, v___x_43_);
v___x_50_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_50_, 0, v___x_44_);
lean_ctor_set(v___x_50_, 1, v___x_49_);
v___x_51_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__2));
v___x_52_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLocation_toJson_spec__0(v___x_50_, v___x_51_);
v___x_53_ = l_Lean_Json_mkObj(v___x_52_);
lean_dec(v___x_52_);
return v___x_53_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocation_fromJson_spec__0(lean_object* v_j_58_, lean_object* v_k_59_){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_60_ = l_Lean_Json_getObjValD(v_j_58_, v_k_59_);
v___x_61_ = l_Lean_Json_getStr_x3f(v___x_60_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocation_fromJson_spec__0___boxed(lean_object* v_j_62_, lean_object* v_k_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocation_fromJson_spec__0(v_j_62_, v_k_63_);
lean_dec_ref(v_k_63_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocation_fromJson_spec__1(lean_object* v_j_65_, lean_object* v_k_66_){
_start:
{
lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_67_ = l_Lean_Json_getObjValD(v_j_65_, v_k_66_);
v___x_68_ = l_Lean_Lsp_instFromJsonRange_fromJson(v___x_67_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocation_fromJson_spec__1___boxed(lean_object* v_j_69_, lean_object* v_k_70_){
_start:
{
lean_object* v_res_71_; 
v_res_71_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocation_fromJson_spec__1(v_j_69_, v_k_70_);
lean_dec_ref(v_k_70_);
return v_res_71_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLocation_fromJson___closed__4(void){
_start:
{
uint8_t v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_79_ = 1;
v___x_80_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__3));
v___x_81_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_80_, v___x_79_);
return v___x_81_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLocation_fromJson___closed__6(void){
_start:
{
lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; 
v___x_83_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__5));
v___x_84_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLocation_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLocation_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLocation_fromJson___closed__4);
v___x_85_ = lean_string_append(v___x_84_, v___x_83_);
return v___x_85_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLocation_fromJson___closed__8(void){
_start:
{
uint8_t v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_88_ = 1;
v___x_89_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__7));
v___x_90_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_89_, v___x_88_);
return v___x_90_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLocation_fromJson___closed__9(void){
_start:
{
lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_91_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLocation_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLocation_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLocation_fromJson___closed__8);
v___x_92_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLocation_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLocation_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLocation_fromJson___closed__6);
v___x_93_ = lean_string_append(v___x_92_, v___x_91_);
return v___x_93_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLocation_fromJson___closed__11(void){
_start:
{
lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_95_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_96_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLocation_fromJson___closed__9, &l_Lean_Lsp_instFromJsonLocation_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonLocation_fromJson___closed__9);
v___x_97_ = lean_string_append(v___x_96_, v___x_95_);
return v___x_97_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLocation_fromJson___closed__13(void){
_start:
{
uint8_t v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_100_ = 1;
v___x_101_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__12));
v___x_102_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_101_, v___x_100_);
return v___x_102_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLocation_fromJson___closed__14(void){
_start:
{
lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_103_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLocation_fromJson___closed__13, &l_Lean_Lsp_instFromJsonLocation_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonLocation_fromJson___closed__13);
v___x_104_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLocation_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLocation_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLocation_fromJson___closed__6);
v___x_105_ = lean_string_append(v___x_104_, v___x_103_);
return v___x_105_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLocation_fromJson___closed__15(void){
_start:
{
lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_106_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_107_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLocation_fromJson___closed__14, &l_Lean_Lsp_instFromJsonLocation_fromJson___closed__14_once, _init_l_Lean_Lsp_instFromJsonLocation_fromJson___closed__14);
v___x_108_ = lean_string_append(v___x_107_, v___x_106_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLocation_fromJson(lean_object* v_json_109_){
_start:
{
lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_110_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__0));
lean_inc(v_json_109_);
v___x_111_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocation_fromJson_spec__0(v_json_109_, v___x_110_);
if (lean_obj_tag(v___x_111_) == 0)
{
lean_object* v_a_112_; lean_object* v___x_114_; uint8_t v_isShared_115_; uint8_t v_isSharedCheck_121_; 
lean_dec(v_json_109_);
v_a_112_ = lean_ctor_get(v___x_111_, 0);
v_isSharedCheck_121_ = !lean_is_exclusive(v___x_111_);
if (v_isSharedCheck_121_ == 0)
{
v___x_114_ = v___x_111_;
v_isShared_115_ = v_isSharedCheck_121_;
goto v_resetjp_113_;
}
else
{
lean_inc(v_a_112_);
lean_dec(v___x_111_);
v___x_114_ = lean_box(0);
v_isShared_115_ = v_isSharedCheck_121_;
goto v_resetjp_113_;
}
v_resetjp_113_:
{
lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_119_; 
v___x_116_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLocation_fromJson___closed__11, &l_Lean_Lsp_instFromJsonLocation_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonLocation_fromJson___closed__11);
v___x_117_ = lean_string_append(v___x_116_, v_a_112_);
lean_dec(v_a_112_);
if (v_isShared_115_ == 0)
{
lean_ctor_set(v___x_114_, 0, v___x_117_);
v___x_119_ = v___x_114_;
goto v_reusejp_118_;
}
else
{
lean_object* v_reuseFailAlloc_120_; 
v_reuseFailAlloc_120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_120_, 0, v___x_117_);
v___x_119_ = v_reuseFailAlloc_120_;
goto v_reusejp_118_;
}
v_reusejp_118_:
{
return v___x_119_;
}
}
}
else
{
if (lean_obj_tag(v___x_111_) == 0)
{
lean_object* v_a_122_; lean_object* v___x_124_; uint8_t v_isShared_125_; uint8_t v_isSharedCheck_129_; 
lean_dec(v_json_109_);
v_a_122_ = lean_ctor_get(v___x_111_, 0);
v_isSharedCheck_129_ = !lean_is_exclusive(v___x_111_);
if (v_isSharedCheck_129_ == 0)
{
v___x_124_ = v___x_111_;
v_isShared_125_ = v_isSharedCheck_129_;
goto v_resetjp_123_;
}
else
{
lean_inc(v_a_122_);
lean_dec(v___x_111_);
v___x_124_ = lean_box(0);
v_isShared_125_ = v_isSharedCheck_129_;
goto v_resetjp_123_;
}
v_resetjp_123_:
{
lean_object* v___x_127_; 
if (v_isShared_125_ == 0)
{
lean_ctor_set_tag(v___x_124_, 0);
v___x_127_ = v___x_124_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_128_; 
v_reuseFailAlloc_128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_128_, 0, v_a_122_);
v___x_127_ = v_reuseFailAlloc_128_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
return v___x_127_;
}
}
}
else
{
lean_object* v_a_130_; lean_object* v___x_131_; lean_object* v___x_132_; 
v_a_130_ = lean_ctor_get(v___x_111_, 0);
lean_inc(v_a_130_);
lean_dec_ref_known(v___x_111_, 1);
v___x_131_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__1));
v___x_132_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocation_fromJson_spec__1(v_json_109_, v___x_131_);
if (lean_obj_tag(v___x_132_) == 0)
{
lean_object* v_a_133_; lean_object* v___x_135_; uint8_t v_isShared_136_; uint8_t v_isSharedCheck_142_; 
lean_dec(v_a_130_);
v_a_133_ = lean_ctor_get(v___x_132_, 0);
v_isSharedCheck_142_ = !lean_is_exclusive(v___x_132_);
if (v_isSharedCheck_142_ == 0)
{
v___x_135_ = v___x_132_;
v_isShared_136_ = v_isSharedCheck_142_;
goto v_resetjp_134_;
}
else
{
lean_inc(v_a_133_);
lean_dec(v___x_132_);
v___x_135_ = lean_box(0);
v_isShared_136_ = v_isSharedCheck_142_;
goto v_resetjp_134_;
}
v_resetjp_134_:
{
lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_140_; 
v___x_137_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLocation_fromJson___closed__15, &l_Lean_Lsp_instFromJsonLocation_fromJson___closed__15_once, _init_l_Lean_Lsp_instFromJsonLocation_fromJson___closed__15);
v___x_138_ = lean_string_append(v___x_137_, v_a_133_);
lean_dec(v_a_133_);
if (v_isShared_136_ == 0)
{
lean_ctor_set(v___x_135_, 0, v___x_138_);
v___x_140_ = v___x_135_;
goto v_reusejp_139_;
}
else
{
lean_object* v_reuseFailAlloc_141_; 
v_reuseFailAlloc_141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_141_, 0, v___x_138_);
v___x_140_ = v_reuseFailAlloc_141_;
goto v_reusejp_139_;
}
v_reusejp_139_:
{
return v___x_140_;
}
}
}
else
{
if (lean_obj_tag(v___x_132_) == 0)
{
lean_object* v_a_143_; lean_object* v___x_145_; uint8_t v_isShared_146_; uint8_t v_isSharedCheck_150_; 
lean_dec(v_a_130_);
v_a_143_ = lean_ctor_get(v___x_132_, 0);
v_isSharedCheck_150_ = !lean_is_exclusive(v___x_132_);
if (v_isSharedCheck_150_ == 0)
{
v___x_145_ = v___x_132_;
v_isShared_146_ = v_isSharedCheck_150_;
goto v_resetjp_144_;
}
else
{
lean_inc(v_a_143_);
lean_dec(v___x_132_);
v___x_145_ = lean_box(0);
v_isShared_146_ = v_isSharedCheck_150_;
goto v_resetjp_144_;
}
v_resetjp_144_:
{
lean_object* v___x_148_; 
if (v_isShared_146_ == 0)
{
lean_ctor_set_tag(v___x_145_, 0);
v___x_148_ = v___x_145_;
goto v_reusejp_147_;
}
else
{
lean_object* v_reuseFailAlloc_149_; 
v_reuseFailAlloc_149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_149_, 0, v_a_143_);
v___x_148_ = v_reuseFailAlloc_149_;
goto v_reusejp_147_;
}
v_reusejp_147_:
{
return v___x_148_;
}
}
}
else
{
lean_object* v_a_151_; lean_object* v___x_153_; uint8_t v_isShared_154_; uint8_t v_isSharedCheck_159_; 
v_a_151_ = lean_ctor_get(v___x_132_, 0);
v_isSharedCheck_159_ = !lean_is_exclusive(v___x_132_);
if (v_isSharedCheck_159_ == 0)
{
v___x_153_ = v___x_132_;
v_isShared_154_ = v_isSharedCheck_159_;
goto v_resetjp_152_;
}
else
{
lean_inc(v_a_151_);
lean_dec(v___x_132_);
v___x_153_ = lean_box(0);
v_isShared_154_ = v_isSharedCheck_159_;
goto v_resetjp_152_;
}
v_resetjp_152_:
{
lean_object* v___x_155_; lean_object* v___x_157_; 
v___x_155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_155_, 0, v_a_130_);
lean_ctor_set(v___x_155_, 1, v_a_151_);
if (v_isShared_154_ == 0)
{
lean_ctor_set(v___x_153_, 0, v___x_155_);
v___x_157_ = v___x_153_;
goto v_reusejp_156_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(1, 1, 0);
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
}
}
}
}
}
uint8_t l_Lean_Lsp_instOrdLocation_ord(lean_object* v_x_162_, lean_object* v_x_163_){
_start:
{
lean_object* v_uri_164_; lean_object* v_range_165_; lean_object* v_uri_166_; lean_object* v_range_167_; uint8_t v___x_168_; 
v_uri_164_ = lean_ctor_get(v_x_162_, 0);
v_range_165_ = lean_ctor_get(v_x_162_, 1);
v_uri_166_ = lean_ctor_get(v_x_163_, 0);
v_range_167_ = lean_ctor_get(v_x_163_, 1);
v___x_168_ = lean_string_compare(v_uri_164_, v_uri_166_);
if (v___x_168_ == 1)
{
uint8_t v___x_169_; 
v___x_169_ = l_Lean_Lsp_instOrdRange_ord(v_range_165_, v_range_167_);
return v___x_169_;
}
else
{
return v___x_168_;
}
}
}
LEAN_EXPORT void l_Lean_Lsp_instOrdLocation_ord_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_162_ = stack[0].m_obj;
lean_object* v_x_163_ = stack[1].m_obj;
uint8_t v_res_170_;
v_res_170_ = l_Lean_Lsp_instOrdLocation_ord(v_x_162_, v_x_163_);
stack->m_num = v_res_170_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instOrdLocation_ord___boxed(lean_object* v_x_171_, lean_object* v_x_172_){
_start:
{
uint8_t v_res_173_; lean_object* v_r_174_; 
v_res_173_ = l_Lean_Lsp_instOrdLocation_ord(v_x_171_, v_x_172_);
lean_dec_ref(v_x_172_);
lean_dec_ref(v_x_171_);
v_r_174_ = lean_box(v_res_173_);
return v_r_174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLocationLink_toJson_spec__0(lean_object* v_k_177_, lean_object* v_x_178_){
_start:
{
if (lean_obj_tag(v_x_178_) == 0)
{
lean_object* v___x_179_; 
lean_dec_ref(v_k_177_);
v___x_179_ = lean_box(0);
return v___x_179_;
}
else
{
lean_object* v_val_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
v_val_180_ = lean_ctor_get(v_x_178_, 0);
lean_inc(v_val_180_);
lean_dec_ref_known(v_x_178_, 1);
v___x_181_ = l_Lean_Lsp_instToJsonRange_toJson(v_val_180_);
v___x_182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_182_, 0, v_k_177_);
lean_ctor_set(v___x_182_, 1, v___x_181_);
v___x_183_ = lean_box(0);
v___x_184_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_184_, 0, v___x_182_);
lean_ctor_set(v___x_184_, 1, v___x_183_);
return v___x_184_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLocationLink_toJson(lean_object* v_x_189_){
_start:
{
lean_object* v_originSelectionRange_x3f_190_; lean_object* v_targetUri_191_; lean_object* v_targetRange_192_; lean_object* v_targetSelectionRange_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
v_originSelectionRange_x3f_190_ = lean_ctor_get(v_x_189_, 0);
lean_inc(v_originSelectionRange_x3f_190_);
v_targetUri_191_ = lean_ctor_get(v_x_189_, 1);
lean_inc_ref(v_targetUri_191_);
v_targetRange_192_ = lean_ctor_get(v_x_189_, 2);
lean_inc_ref(v_targetRange_192_);
v_targetSelectionRange_193_ = lean_ctor_get(v_x_189_, 3);
lean_inc_ref(v_targetSelectionRange_193_);
lean_dec_ref(v_x_189_);
v___x_194_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocationLink_toJson___closed__0));
v___x_195_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLocationLink_toJson_spec__0(v___x_194_, v_originSelectionRange_x3f_190_);
v___x_196_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocationLink_toJson___closed__1));
v___x_197_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_197_, 0, v_targetUri_191_);
v___x_198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_198_, 0, v___x_196_);
lean_ctor_set(v___x_198_, 1, v___x_197_);
v___x_199_ = lean_box(0);
v___x_200_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_200_, 0, v___x_198_);
lean_ctor_set(v___x_200_, 1, v___x_199_);
v___x_201_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocationLink_toJson___closed__2));
v___x_202_ = l_Lean_Lsp_instToJsonRange_toJson(v_targetRange_192_);
v___x_203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_203_, 0, v___x_201_);
lean_ctor_set(v___x_203_, 1, v___x_202_);
v___x_204_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_204_, 0, v___x_203_);
lean_ctor_set(v___x_204_, 1, v___x_199_);
v___x_205_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocationLink_toJson___closed__3));
v___x_206_ = l_Lean_Lsp_instToJsonRange_toJson(v_targetSelectionRange_193_);
v___x_207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_207_, 0, v___x_205_);
lean_ctor_set(v___x_207_, 1, v___x_206_);
v___x_208_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_208_, 0, v___x_207_);
lean_ctor_set(v___x_208_, 1, v___x_199_);
v___x_209_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_209_, 0, v___x_208_);
lean_ctor_set(v___x_209_, 1, v___x_199_);
v___x_210_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_210_, 0, v___x_204_);
lean_ctor_set(v___x_210_, 1, v___x_209_);
v___x_211_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_211_, 0, v___x_200_);
lean_ctor_set(v___x_211_, 1, v___x_210_);
v___x_212_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_212_, 0, v___x_195_);
lean_ctor_set(v___x_212_, 1, v___x_211_);
v___x_213_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__2));
v___x_214_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLocation_toJson_spec__0(v___x_212_, v___x_213_);
v___x_215_ = l_Lean_Json_mkObj(v___x_214_);
lean_dec(v___x_214_);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocationLink_fromJson_spec__0_spec__0(lean_object* v_x_220_){
_start:
{
if (lean_obj_tag(v_x_220_) == 0)
{
lean_object* v___x_221_; 
v___x_221_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocationLink_fromJson_spec__0_spec__0___closed__0));
return v___x_221_;
}
else
{
lean_object* v___x_222_; 
v___x_222_ = l_Lean_Lsp_instFromJsonRange_fromJson(v_x_220_);
if (lean_obj_tag(v___x_222_) == 0)
{
lean_object* v_a_223_; lean_object* v___x_225_; uint8_t v_isShared_226_; uint8_t v_isSharedCheck_230_; 
v_a_223_ = lean_ctor_get(v___x_222_, 0);
v_isSharedCheck_230_ = !lean_is_exclusive(v___x_222_);
if (v_isSharedCheck_230_ == 0)
{
v___x_225_ = v___x_222_;
v_isShared_226_ = v_isSharedCheck_230_;
goto v_resetjp_224_;
}
else
{
lean_inc(v_a_223_);
lean_dec(v___x_222_);
v___x_225_ = lean_box(0);
v_isShared_226_ = v_isSharedCheck_230_;
goto v_resetjp_224_;
}
v_resetjp_224_:
{
lean_object* v___x_228_; 
if (v_isShared_226_ == 0)
{
v___x_228_ = v___x_225_;
goto v_reusejp_227_;
}
else
{
lean_object* v_reuseFailAlloc_229_; 
v_reuseFailAlloc_229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_229_, 0, v_a_223_);
v___x_228_ = v_reuseFailAlloc_229_;
goto v_reusejp_227_;
}
v_reusejp_227_:
{
return v___x_228_;
}
}
}
else
{
lean_object* v_a_231_; lean_object* v___x_233_; uint8_t v_isShared_234_; uint8_t v_isSharedCheck_239_; 
v_a_231_ = lean_ctor_get(v___x_222_, 0);
v_isSharedCheck_239_ = !lean_is_exclusive(v___x_222_);
if (v_isSharedCheck_239_ == 0)
{
v___x_233_ = v___x_222_;
v_isShared_234_ = v_isSharedCheck_239_;
goto v_resetjp_232_;
}
else
{
lean_inc(v_a_231_);
lean_dec(v___x_222_);
v___x_233_ = lean_box(0);
v_isShared_234_ = v_isSharedCheck_239_;
goto v_resetjp_232_;
}
v_resetjp_232_:
{
lean_object* v___x_235_; lean_object* v___x_237_; 
v___x_235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_235_, 0, v_a_231_);
if (v_isShared_234_ == 0)
{
lean_ctor_set(v___x_233_, 0, v___x_235_);
v___x_237_ = v___x_233_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(1, 1, 0);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocationLink_fromJson_spec__0(lean_object* v_j_240_, lean_object* v_k_241_){
_start:
{
lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_242_ = l_Lean_Json_getObjValD(v_j_240_, v_k_241_);
v___x_243_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocationLink_fromJson_spec__0_spec__0(v___x_242_);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocationLink_fromJson_spec__0___boxed(lean_object* v_j_244_, lean_object* v_k_245_){
_start:
{
lean_object* v_res_246_; 
v_res_246_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocationLink_fromJson_spec__0(v_j_244_, v_k_245_);
lean_dec_ref(v_k_245_);
return v_res_246_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__2(void){
_start:
{
uint8_t v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_252_ = 1;
v___x_253_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__1));
v___x_254_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_253_, v___x_252_);
return v___x_254_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__3(void){
_start:
{
lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; 
v___x_255_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__5));
v___x_256_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__2, &l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__2);
v___x_257_ = lean_string_append(v___x_256_, v___x_255_);
return v___x_257_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__6(void){
_start:
{
uint8_t v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; 
v___x_261_ = 1;
v___x_262_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__5));
v___x_263_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_262_, v___x_261_);
return v___x_263_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__7(void){
_start:
{
lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_264_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__6);
v___x_265_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__3);
v___x_266_ = lean_string_append(v___x_265_, v___x_264_);
return v___x_266_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__8(void){
_start:
{
lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; 
v___x_267_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_268_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__7);
v___x_269_ = lean_string_append(v___x_268_, v___x_267_);
return v___x_269_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__10(void){
_start:
{
uint8_t v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_272_ = 1;
v___x_273_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__9));
v___x_274_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_273_, v___x_272_);
return v___x_274_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__11(void){
_start:
{
lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_275_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__10, &l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__10);
v___x_276_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__3);
v___x_277_ = lean_string_append(v___x_276_, v___x_275_);
return v___x_277_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__12(void){
_start:
{
lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_278_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_279_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__11, &l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__11);
v___x_280_ = lean_string_append(v___x_279_, v___x_278_);
return v___x_280_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__14(void){
_start:
{
uint8_t v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_283_ = 1;
v___x_284_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__13));
v___x_285_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_284_, v___x_283_);
return v___x_285_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__15(void){
_start:
{
lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; 
v___x_286_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__14, &l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__14_once, _init_l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__14);
v___x_287_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__3);
v___x_288_ = lean_string_append(v___x_287_, v___x_286_);
return v___x_288_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__16(void){
_start:
{
lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_289_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_290_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__15, &l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__15_once, _init_l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__15);
v___x_291_ = lean_string_append(v___x_290_, v___x_289_);
return v___x_291_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__18(void){
_start:
{
uint8_t v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_294_ = 1;
v___x_295_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__17));
v___x_296_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_295_, v___x_294_);
return v___x_296_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__19(void){
_start:
{
lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_297_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__18, &l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__18_once, _init_l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__18);
v___x_298_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__3);
v___x_299_ = lean_string_append(v___x_298_, v___x_297_);
return v___x_299_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__20(void){
_start:
{
lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_300_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_301_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__19, &l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__19_once, _init_l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__19);
v___x_302_ = lean_string_append(v___x_301_, v___x_300_);
return v___x_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLocationLink_fromJson(lean_object* v_json_303_){
_start:
{
lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_304_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocationLink_toJson___closed__0));
lean_inc(v_json_303_);
v___x_305_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocationLink_fromJson_spec__0(v_json_303_, v___x_304_);
if (lean_obj_tag(v___x_305_) == 0)
{
lean_object* v_a_306_; lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_315_; 
lean_dec(v_json_303_);
v_a_306_ = lean_ctor_get(v___x_305_, 0);
v_isSharedCheck_315_ = !lean_is_exclusive(v___x_305_);
if (v_isSharedCheck_315_ == 0)
{
v___x_308_ = v___x_305_;
v_isShared_309_ = v_isSharedCheck_315_;
goto v_resetjp_307_;
}
else
{
lean_inc(v_a_306_);
lean_dec(v___x_305_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_315_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_313_; 
v___x_310_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__8);
v___x_311_ = lean_string_append(v___x_310_, v_a_306_);
lean_dec(v_a_306_);
if (v_isShared_309_ == 0)
{
lean_ctor_set(v___x_308_, 0, v___x_311_);
v___x_313_ = v___x_308_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v___x_311_);
v___x_313_ = v_reuseFailAlloc_314_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
return v___x_313_;
}
}
}
else
{
if (lean_obj_tag(v___x_305_) == 0)
{
lean_object* v_a_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_323_; 
lean_dec(v_json_303_);
v_a_316_ = lean_ctor_get(v___x_305_, 0);
v_isSharedCheck_323_ = !lean_is_exclusive(v___x_305_);
if (v_isSharedCheck_323_ == 0)
{
v___x_318_ = v___x_305_;
v_isShared_319_ = v_isSharedCheck_323_;
goto v_resetjp_317_;
}
else
{
lean_inc(v_a_316_);
lean_dec(v___x_305_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_323_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
lean_object* v___x_321_; 
if (v_isShared_319_ == 0)
{
lean_ctor_set_tag(v___x_318_, 0);
v___x_321_ = v___x_318_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v_a_316_);
v___x_321_ = v_reuseFailAlloc_322_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
return v___x_321_;
}
}
}
else
{
lean_object* v_a_324_; lean_object* v___x_325_; lean_object* v___x_326_; 
v_a_324_ = lean_ctor_get(v___x_305_, 0);
lean_inc(v_a_324_);
lean_dec_ref_known(v___x_305_, 1);
v___x_325_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocationLink_toJson___closed__1));
lean_inc(v_json_303_);
v___x_326_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocation_fromJson_spec__0(v_json_303_, v___x_325_);
if (lean_obj_tag(v___x_326_) == 0)
{
lean_object* v_a_327_; lean_object* v___x_329_; uint8_t v_isShared_330_; uint8_t v_isSharedCheck_336_; 
lean_dec(v_a_324_);
lean_dec(v_json_303_);
v_a_327_ = lean_ctor_get(v___x_326_, 0);
v_isSharedCheck_336_ = !lean_is_exclusive(v___x_326_);
if (v_isSharedCheck_336_ == 0)
{
v___x_329_ = v___x_326_;
v_isShared_330_ = v_isSharedCheck_336_;
goto v_resetjp_328_;
}
else
{
lean_inc(v_a_327_);
lean_dec(v___x_326_);
v___x_329_ = lean_box(0);
v_isShared_330_ = v_isSharedCheck_336_;
goto v_resetjp_328_;
}
v_resetjp_328_:
{
lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_334_; 
v___x_331_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__12, &l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__12);
v___x_332_ = lean_string_append(v___x_331_, v_a_327_);
lean_dec(v_a_327_);
if (v_isShared_330_ == 0)
{
lean_ctor_set(v___x_329_, 0, v___x_332_);
v___x_334_ = v___x_329_;
goto v_reusejp_333_;
}
else
{
lean_object* v_reuseFailAlloc_335_; 
v_reuseFailAlloc_335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_335_, 0, v___x_332_);
v___x_334_ = v_reuseFailAlloc_335_;
goto v_reusejp_333_;
}
v_reusejp_333_:
{
return v___x_334_;
}
}
}
else
{
if (lean_obj_tag(v___x_326_) == 0)
{
lean_object* v_a_337_; lean_object* v___x_339_; uint8_t v_isShared_340_; uint8_t v_isSharedCheck_344_; 
lean_dec(v_a_324_);
lean_dec(v_json_303_);
v_a_337_ = lean_ctor_get(v___x_326_, 0);
v_isSharedCheck_344_ = !lean_is_exclusive(v___x_326_);
if (v_isSharedCheck_344_ == 0)
{
v___x_339_ = v___x_326_;
v_isShared_340_ = v_isSharedCheck_344_;
goto v_resetjp_338_;
}
else
{
lean_inc(v_a_337_);
lean_dec(v___x_326_);
v___x_339_ = lean_box(0);
v_isShared_340_ = v_isSharedCheck_344_;
goto v_resetjp_338_;
}
v_resetjp_338_:
{
lean_object* v___x_342_; 
if (v_isShared_340_ == 0)
{
lean_ctor_set_tag(v___x_339_, 0);
v___x_342_ = v___x_339_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v_a_337_);
v___x_342_ = v_reuseFailAlloc_343_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
return v___x_342_;
}
}
}
else
{
lean_object* v_a_345_; lean_object* v___x_346_; lean_object* v___x_347_; 
v_a_345_ = lean_ctor_get(v___x_326_, 0);
lean_inc(v_a_345_);
lean_dec_ref_known(v___x_326_, 1);
v___x_346_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocationLink_toJson___closed__2));
lean_inc(v_json_303_);
v___x_347_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocation_fromJson_spec__1(v_json_303_, v___x_346_);
if (lean_obj_tag(v___x_347_) == 0)
{
lean_object* v_a_348_; lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_357_; 
lean_dec(v_a_345_);
lean_dec(v_a_324_);
lean_dec(v_json_303_);
v_a_348_ = lean_ctor_get(v___x_347_, 0);
v_isSharedCheck_357_ = !lean_is_exclusive(v___x_347_);
if (v_isSharedCheck_357_ == 0)
{
v___x_350_ = v___x_347_;
v_isShared_351_ = v_isSharedCheck_357_;
goto v_resetjp_349_;
}
else
{
lean_inc(v_a_348_);
lean_dec(v___x_347_);
v___x_350_ = lean_box(0);
v_isShared_351_ = v_isSharedCheck_357_;
goto v_resetjp_349_;
}
v_resetjp_349_:
{
lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_355_; 
v___x_352_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__16, &l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__16_once, _init_l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__16);
v___x_353_ = lean_string_append(v___x_352_, v_a_348_);
lean_dec(v_a_348_);
if (v_isShared_351_ == 0)
{
lean_ctor_set(v___x_350_, 0, v___x_353_);
v___x_355_ = v___x_350_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v___x_353_);
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
if (lean_obj_tag(v___x_347_) == 0)
{
lean_object* v_a_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_365_; 
lean_dec(v_a_345_);
lean_dec(v_a_324_);
lean_dec(v_json_303_);
v_a_358_ = lean_ctor_get(v___x_347_, 0);
v_isSharedCheck_365_ = !lean_is_exclusive(v___x_347_);
if (v_isSharedCheck_365_ == 0)
{
v___x_360_ = v___x_347_;
v_isShared_361_ = v_isSharedCheck_365_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_a_358_);
lean_dec(v___x_347_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_365_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
lean_object* v___x_363_; 
if (v_isShared_361_ == 0)
{
lean_ctor_set_tag(v___x_360_, 0);
v___x_363_ = v___x_360_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_366_; lean_object* v___x_367_; lean_object* v___x_368_; 
v_a_366_ = lean_ctor_get(v___x_347_, 0);
lean_inc(v_a_366_);
lean_dec_ref_known(v___x_347_, 1);
v___x_367_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocationLink_toJson___closed__3));
v___x_368_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocation_fromJson_spec__1(v_json_303_, v___x_367_);
if (lean_obj_tag(v___x_368_) == 0)
{
lean_object* v_a_369_; lean_object* v___x_371_; uint8_t v_isShared_372_; uint8_t v_isSharedCheck_378_; 
lean_dec(v_a_366_);
lean_dec(v_a_345_);
lean_dec(v_a_324_);
v_a_369_ = lean_ctor_get(v___x_368_, 0);
v_isSharedCheck_378_ = !lean_is_exclusive(v___x_368_);
if (v_isSharedCheck_378_ == 0)
{
v___x_371_ = v___x_368_;
v_isShared_372_ = v_isSharedCheck_378_;
goto v_resetjp_370_;
}
else
{
lean_inc(v_a_369_);
lean_dec(v___x_368_);
v___x_371_ = lean_box(0);
v_isShared_372_ = v_isSharedCheck_378_;
goto v_resetjp_370_;
}
v_resetjp_370_:
{
lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_376_; 
v___x_373_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__20, &l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__20_once, _init_l_Lean_Lsp_instFromJsonLocationLink_fromJson___closed__20);
v___x_374_ = lean_string_append(v___x_373_, v_a_369_);
lean_dec(v_a_369_);
if (v_isShared_372_ == 0)
{
lean_ctor_set(v___x_371_, 0, v___x_374_);
v___x_376_ = v___x_371_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v___x_374_);
v___x_376_ = v_reuseFailAlloc_377_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
return v___x_376_;
}
}
}
else
{
if (lean_obj_tag(v___x_368_) == 0)
{
lean_object* v_a_379_; lean_object* v___x_381_; uint8_t v_isShared_382_; uint8_t v_isSharedCheck_386_; 
lean_dec(v_a_366_);
lean_dec(v_a_345_);
lean_dec(v_a_324_);
v_a_379_ = lean_ctor_get(v___x_368_, 0);
v_isSharedCheck_386_ = !lean_is_exclusive(v___x_368_);
if (v_isSharedCheck_386_ == 0)
{
v___x_381_ = v___x_368_;
v_isShared_382_ = v_isSharedCheck_386_;
goto v_resetjp_380_;
}
else
{
lean_inc(v_a_379_);
lean_dec(v___x_368_);
v___x_381_ = lean_box(0);
v_isShared_382_ = v_isSharedCheck_386_;
goto v_resetjp_380_;
}
v_resetjp_380_:
{
lean_object* v___x_384_; 
if (v_isShared_382_ == 0)
{
lean_ctor_set_tag(v___x_381_, 0);
v___x_384_ = v___x_381_;
goto v_reusejp_383_;
}
else
{
lean_object* v_reuseFailAlloc_385_; 
v_reuseFailAlloc_385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_385_, 0, v_a_379_);
v___x_384_ = v_reuseFailAlloc_385_;
goto v_reusejp_383_;
}
v_reusejp_383_:
{
return v___x_384_;
}
}
}
else
{
lean_object* v_a_387_; lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_395_; 
v_a_387_ = lean_ctor_get(v___x_368_, 0);
v_isSharedCheck_395_ = !lean_is_exclusive(v___x_368_);
if (v_isSharedCheck_395_ == 0)
{
v___x_389_ = v___x_368_;
v_isShared_390_ = v_isSharedCheck_395_;
goto v_resetjp_388_;
}
else
{
lean_inc(v_a_387_);
lean_dec(v___x_368_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_395_;
goto v_resetjp_388_;
}
v_resetjp_388_:
{
lean_object* v___x_391_; lean_object* v___x_393_; 
v___x_391_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_391_, 0, v_a_324_);
lean_ctor_set(v___x_391_, 1, v_a_345_);
lean_ctor_set(v___x_391_, 2, v_a_366_);
lean_ctor_set(v___x_391_, 3, v_a_387_);
if (v_isShared_390_ == 0)
{
lean_ctor_set(v___x_389_, 0, v___x_391_);
v___x_393_ = v___x_389_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v___x_391_);
v___x_393_ = v_reuseFailAlloc_394_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
return v___x_393_;
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
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonCommand_toJson_spec__0_spec__0_spec__1(size_t v_sz_398_, size_t v_i_399_, lean_object* v_bs_400_){
_start:
{
uint8_t v___x_401_; 
v___x_401_ = lean_usize_dec_lt(v_i_399_, v_sz_398_);
if (v___x_401_ == 0)
{
return v_bs_400_;
}
else
{
lean_object* v_v_402_; lean_object* v___x_403_; lean_object* v_bs_x27_404_; size_t v___x_405_; size_t v___x_406_; lean_object* v___x_407_; 
v_v_402_ = lean_array_uget(v_bs_400_, v_i_399_);
v___x_403_ = lean_unsigned_to_nat(0u);
v_bs_x27_404_ = lean_array_uset(v_bs_400_, v_i_399_, v___x_403_);
v___x_405_ = ((size_t)1ULL);
v___x_406_ = lean_usize_add(v_i_399_, v___x_405_);
v___x_407_ = lean_array_uset(v_bs_x27_404_, v_i_399_, v_v_402_);
v_i_399_ = v___x_406_;
v_bs_400_ = v___x_407_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonCommand_toJson_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
size_t v_sz_398_ = stack[0].m_num;
size_t v_i_399_ = stack[1].m_num;
lean_object* v_bs_400_ = stack[2].m_obj;
lean_object* v_res_409_;
v_res_409_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonCommand_toJson_spec__0_spec__0_spec__1(v_sz_398_, v_i_399_, v_bs_400_);
stack->m_obj
 = v_res_409_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonCommand_toJson_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_410_, lean_object* v_i_411_, lean_object* v_bs_412_){
_start:
{
size_t v_sz_boxed_413_; size_t v_i_boxed_414_; lean_object* v_res_415_; 
v_sz_boxed_413_ = lean_unbox_usize(v_sz_410_);
lean_dec(v_sz_410_);
v_i_boxed_414_ = lean_unbox_usize(v_i_411_);
lean_dec(v_i_411_);
v_res_415_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonCommand_toJson_spec__0_spec__0_spec__1(v_sz_boxed_413_, v_i_boxed_414_, v_bs_412_);
return v_res_415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonCommand_toJson_spec__0_spec__0(lean_object* v_a_416_){
_start:
{
size_t v_sz_417_; size_t v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; 
v_sz_417_ = lean_array_size(v_a_416_);
v___x_418_ = ((size_t)0ULL);
v___x_419_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonCommand_toJson_spec__0_spec__0_spec__1(v_sz_417_, v___x_418_, v_a_416_);
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
lean_dec_ref_known(v_x_422_, 1);
v___x_425_ = l_Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonCommand_toJson_spec__0_spec__0(v_val_424_);
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
lean_dec(v___x_451_);
return v___x_452_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCommand_fromJson_spec__0_spec__0_spec__1_spec__2(size_t v_sz_455_, size_t v_i_456_, lean_object* v_bs_457_){
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCommand_fromJson_spec__0_spec__0_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
size_t v_sz_455_ = stack[0].m_num;
size_t v_i_456_ = stack[1].m_num;
lean_object* v_bs_457_ = stack[2].m_obj;
lean_object* v_res_467_;
v_res_467_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCommand_fromJson_spec__0_spec__0_spec__1_spec__2(v_sz_455_, v_i_456_, v_bs_457_);
stack->m_obj
 = v_res_467_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCommand_fromJson_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_sz_468_, lean_object* v_i_469_, lean_object* v_bs_470_){
_start:
{
size_t v_sz_boxed_471_; size_t v_i_boxed_472_; lean_object* v_res_473_; 
v_sz_boxed_471_ = lean_unbox_usize(v_sz_468_);
lean_dec(v_sz_468_);
v_i_boxed_472_ = lean_unbox_usize(v_i_469_);
lean_dec(v_i_469_);
v_res_473_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCommand_fromJson_spec__0_spec__0_spec__1_spec__2(v_sz_boxed_471_, v_i_boxed_472_, v_bs_470_);
return v_res_473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCommand_fromJson_spec__0_spec__0_spec__1(lean_object* v_x_476_){
_start:
{
if (lean_obj_tag(v_x_476_) == 4)
{
lean_object* v_elems_477_; size_t v_sz_478_; size_t v___x_479_; lean_object* v___x_480_; 
v_elems_477_ = lean_ctor_get(v_x_476_, 0);
lean_inc_ref(v_elems_477_);
lean_dec_ref_known(v_x_476_, 1);
v_sz_478_ = lean_array_size(v_elems_477_);
v___x_479_ = ((size_t)0ULL);
v___x_480_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCommand_fromJson_spec__0_spec__0_spec__1_spec__2(v_sz_478_, v___x_479_, v_elems_477_);
return v___x_480_;
}
else
{
lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; 
v___x_481_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCommand_fromJson_spec__0_spec__0_spec__1___closed__0));
v___x_482_ = lean_unsigned_to_nat(80u);
v___x_483_ = l_Lean_Json_pretty(v_x_476_, v___x_482_);
v___x_484_ = lean_string_append(v___x_481_, v___x_483_);
lean_dec_ref(v___x_483_);
v___x_485_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCommand_fromJson_spec__0_spec__0_spec__1___closed__1));
v___x_486_ = lean_string_append(v___x_484_, v___x_485_);
v___x_487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_487_, 0, v___x_486_);
return v___x_487_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCommand_fromJson_spec__0_spec__0(lean_object* v_x_490_){
_start:
{
if (lean_obj_tag(v_x_490_) == 0)
{
lean_object* v___x_491_; 
v___x_491_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCommand_fromJson_spec__0_spec__0___closed__0));
return v___x_491_;
}
else
{
lean_object* v___x_492_; 
v___x_492_ = l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCommand_fromJson_spec__0_spec__0_spec__1(v_x_490_);
if (lean_obj_tag(v___x_492_) == 0)
{
lean_object* v_a_493_; lean_object* v___x_495_; uint8_t v_isShared_496_; uint8_t v_isSharedCheck_500_; 
v_a_493_ = lean_ctor_get(v___x_492_, 0);
v_isSharedCheck_500_ = !lean_is_exclusive(v___x_492_);
if (v_isSharedCheck_500_ == 0)
{
v___x_495_ = v___x_492_;
v_isShared_496_ = v_isSharedCheck_500_;
goto v_resetjp_494_;
}
else
{
lean_inc(v_a_493_);
lean_dec(v___x_492_);
v___x_495_ = lean_box(0);
v_isShared_496_ = v_isSharedCheck_500_;
goto v_resetjp_494_;
}
v_resetjp_494_:
{
lean_object* v___x_498_; 
if (v_isShared_496_ == 0)
{
v___x_498_ = v___x_495_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v_a_493_);
v___x_498_ = v_reuseFailAlloc_499_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
return v___x_498_;
}
}
}
else
{
lean_object* v_a_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_509_; 
v_a_501_ = lean_ctor_get(v___x_492_, 0);
v_isSharedCheck_509_ = !lean_is_exclusive(v___x_492_);
if (v_isSharedCheck_509_ == 0)
{
v___x_503_ = v___x_492_;
v_isShared_504_ = v_isSharedCheck_509_;
goto v_resetjp_502_;
}
else
{
lean_inc(v_a_501_);
lean_dec(v___x_492_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_509_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
lean_object* v___x_505_; lean_object* v___x_507_; 
v___x_505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_505_, 0, v_a_501_);
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 0, v___x_505_);
v___x_507_ = v___x_503_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v___x_505_);
v___x_507_ = v_reuseFailAlloc_508_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
return v___x_507_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCommand_fromJson_spec__0(lean_object* v_j_510_, lean_object* v_k_511_){
_start:
{
lean_object* v___x_512_; lean_object* v___x_513_; 
v___x_512_ = l_Lean_Json_getObjValD(v_j_510_, v_k_511_);
v___x_513_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCommand_fromJson_spec__0_spec__0(v___x_512_);
return v___x_513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCommand_fromJson_spec__0___boxed(lean_object* v_j_514_, lean_object* v_k_515_){
_start:
{
lean_object* v_res_516_; 
v_res_516_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCommand_fromJson_spec__0(v_j_514_, v_k_515_);
lean_dec_ref(v_k_515_);
return v_res_516_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonCommand_fromJson___closed__2(void){
_start:
{
uint8_t v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; 
v___x_522_ = 1;
v___x_523_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCommand_fromJson___closed__1));
v___x_524_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_523_, v___x_522_);
return v___x_524_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonCommand_fromJson___closed__3(void){
_start:
{
lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_525_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__5));
v___x_526_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCommand_fromJson___closed__2, &l_Lean_Lsp_instFromJsonCommand_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonCommand_fromJson___closed__2);
v___x_527_ = lean_string_append(v___x_526_, v___x_525_);
return v___x_527_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonCommand_fromJson___closed__5(void){
_start:
{
uint8_t v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_530_ = 1;
v___x_531_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCommand_fromJson___closed__4));
v___x_532_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_531_, v___x_530_);
return v___x_532_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonCommand_fromJson___closed__6(void){
_start:
{
lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_533_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCommand_fromJson___closed__5, &l_Lean_Lsp_instFromJsonCommand_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonCommand_fromJson___closed__5);
v___x_534_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCommand_fromJson___closed__3, &l_Lean_Lsp_instFromJsonCommand_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonCommand_fromJson___closed__3);
v___x_535_ = lean_string_append(v___x_534_, v___x_533_);
return v___x_535_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonCommand_fromJson___closed__7(void){
_start:
{
lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; 
v___x_536_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_537_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCommand_fromJson___closed__6, &l_Lean_Lsp_instFromJsonCommand_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonCommand_fromJson___closed__6);
v___x_538_ = lean_string_append(v___x_537_, v___x_536_);
return v___x_538_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonCommand_fromJson___closed__9(void){
_start:
{
uint8_t v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; 
v___x_541_ = 1;
v___x_542_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCommand_fromJson___closed__8));
v___x_543_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_542_, v___x_541_);
return v___x_543_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonCommand_fromJson___closed__10(void){
_start:
{
lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; 
v___x_544_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCommand_fromJson___closed__9, &l_Lean_Lsp_instFromJsonCommand_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonCommand_fromJson___closed__9);
v___x_545_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCommand_fromJson___closed__3, &l_Lean_Lsp_instFromJsonCommand_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonCommand_fromJson___closed__3);
v___x_546_ = lean_string_append(v___x_545_, v___x_544_);
return v___x_546_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonCommand_fromJson___closed__11(void){
_start:
{
lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; 
v___x_547_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_548_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCommand_fromJson___closed__10, &l_Lean_Lsp_instFromJsonCommand_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonCommand_fromJson___closed__10);
v___x_549_ = lean_string_append(v___x_548_, v___x_547_);
return v___x_549_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonCommand_fromJson___closed__14(void){
_start:
{
uint8_t v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; 
v___x_553_ = 1;
v___x_554_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCommand_fromJson___closed__13));
v___x_555_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_554_, v___x_553_);
return v___x_555_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonCommand_fromJson___closed__15(void){
_start:
{
lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_556_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCommand_fromJson___closed__14, &l_Lean_Lsp_instFromJsonCommand_fromJson___closed__14_once, _init_l_Lean_Lsp_instFromJsonCommand_fromJson___closed__14);
v___x_557_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCommand_fromJson___closed__3, &l_Lean_Lsp_instFromJsonCommand_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonCommand_fromJson___closed__3);
v___x_558_ = lean_string_append(v___x_557_, v___x_556_);
return v___x_558_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonCommand_fromJson___closed__16(void){
_start:
{
lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; 
v___x_559_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_560_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCommand_fromJson___closed__15, &l_Lean_Lsp_instFromJsonCommand_fromJson___closed__15_once, _init_l_Lean_Lsp_instFromJsonCommand_fromJson___closed__15);
v___x_561_ = lean_string_append(v___x_560_, v___x_559_);
return v___x_561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonCommand_fromJson(lean_object* v_json_562_){
_start:
{
lean_object* v___x_563_; lean_object* v___x_564_; 
v___x_563_ = ((lean_object*)(l_Lean_Lsp_instToJsonCommand_toJson___closed__0));
lean_inc(v_json_562_);
v___x_564_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocation_fromJson_spec__0(v_json_562_, v___x_563_);
if (lean_obj_tag(v___x_564_) == 0)
{
lean_object* v_a_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_574_; 
lean_dec(v_json_562_);
v_a_565_ = lean_ctor_get(v___x_564_, 0);
v_isSharedCheck_574_ = !lean_is_exclusive(v___x_564_);
if (v_isSharedCheck_574_ == 0)
{
v___x_567_ = v___x_564_;
v_isShared_568_ = v_isSharedCheck_574_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_a_565_);
lean_dec(v___x_564_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_574_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_572_; 
v___x_569_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCommand_fromJson___closed__7, &l_Lean_Lsp_instFromJsonCommand_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonCommand_fromJson___closed__7);
v___x_570_ = lean_string_append(v___x_569_, v_a_565_);
lean_dec(v_a_565_);
if (v_isShared_568_ == 0)
{
lean_ctor_set(v___x_567_, 0, v___x_570_);
v___x_572_ = v___x_567_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v___x_570_);
v___x_572_ = v_reuseFailAlloc_573_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
return v___x_572_;
}
}
}
else
{
if (lean_obj_tag(v___x_564_) == 0)
{
lean_object* v_a_575_; lean_object* v___x_577_; uint8_t v_isShared_578_; uint8_t v_isSharedCheck_582_; 
lean_dec(v_json_562_);
v_a_575_ = lean_ctor_get(v___x_564_, 0);
v_isSharedCheck_582_ = !lean_is_exclusive(v___x_564_);
if (v_isSharedCheck_582_ == 0)
{
v___x_577_ = v___x_564_;
v_isShared_578_ = v_isSharedCheck_582_;
goto v_resetjp_576_;
}
else
{
lean_inc(v_a_575_);
lean_dec(v___x_564_);
v___x_577_ = lean_box(0);
v_isShared_578_ = v_isSharedCheck_582_;
goto v_resetjp_576_;
}
v_resetjp_576_:
{
lean_object* v___x_580_; 
if (v_isShared_578_ == 0)
{
lean_ctor_set_tag(v___x_577_, 0);
v___x_580_ = v___x_577_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v_a_575_);
v___x_580_ = v_reuseFailAlloc_581_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
return v___x_580_;
}
}
}
else
{
lean_object* v_a_583_; lean_object* v___x_584_; lean_object* v___x_585_; 
v_a_583_ = lean_ctor_get(v___x_564_, 0);
lean_inc(v_a_583_);
lean_dec_ref_known(v___x_564_, 1);
v___x_584_ = ((lean_object*)(l_Lean_Lsp_instToJsonCommand_toJson___closed__1));
lean_inc(v_json_562_);
v___x_585_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocation_fromJson_spec__0(v_json_562_, v___x_584_);
if (lean_obj_tag(v___x_585_) == 0)
{
lean_object* v_a_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_595_; 
lean_dec(v_a_583_);
lean_dec(v_json_562_);
v_a_586_ = lean_ctor_get(v___x_585_, 0);
v_isSharedCheck_595_ = !lean_is_exclusive(v___x_585_);
if (v_isSharedCheck_595_ == 0)
{
v___x_588_ = v___x_585_;
v_isShared_589_ = v_isSharedCheck_595_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_a_586_);
lean_dec(v___x_585_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_595_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_593_; 
v___x_590_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCommand_fromJson___closed__11, &l_Lean_Lsp_instFromJsonCommand_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonCommand_fromJson___closed__11);
v___x_591_ = lean_string_append(v___x_590_, v_a_586_);
lean_dec(v_a_586_);
if (v_isShared_589_ == 0)
{
lean_ctor_set(v___x_588_, 0, v___x_591_);
v___x_593_ = v___x_588_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v___x_591_);
v___x_593_ = v_reuseFailAlloc_594_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
return v___x_593_;
}
}
}
else
{
if (lean_obj_tag(v___x_585_) == 0)
{
lean_object* v_a_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_603_; 
lean_dec(v_a_583_);
lean_dec(v_json_562_);
v_a_596_ = lean_ctor_get(v___x_585_, 0);
v_isSharedCheck_603_ = !lean_is_exclusive(v___x_585_);
if (v_isSharedCheck_603_ == 0)
{
v___x_598_ = v___x_585_;
v_isShared_599_ = v_isSharedCheck_603_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_a_596_);
lean_dec(v___x_585_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_603_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v___x_601_; 
if (v_isShared_599_ == 0)
{
lean_ctor_set_tag(v___x_598_, 0);
v___x_601_ = v___x_598_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v_a_596_);
v___x_601_ = v_reuseFailAlloc_602_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
return v___x_601_;
}
}
}
else
{
lean_object* v_a_604_; lean_object* v___x_605_; lean_object* v___x_606_; 
v_a_604_ = lean_ctor_get(v___x_585_, 0);
lean_inc(v_a_604_);
lean_dec_ref_known(v___x_585_, 1);
v___x_605_ = ((lean_object*)(l_Lean_Lsp_instToJsonCommand_toJson___closed__2));
v___x_606_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCommand_fromJson_spec__0(v_json_562_, v___x_605_);
if (lean_obj_tag(v___x_606_) == 0)
{
lean_object* v_a_607_; lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_616_; 
lean_dec(v_a_604_);
lean_dec(v_a_583_);
v_a_607_ = lean_ctor_get(v___x_606_, 0);
v_isSharedCheck_616_ = !lean_is_exclusive(v___x_606_);
if (v_isSharedCheck_616_ == 0)
{
v___x_609_ = v___x_606_;
v_isShared_610_ = v_isSharedCheck_616_;
goto v_resetjp_608_;
}
else
{
lean_inc(v_a_607_);
lean_dec(v___x_606_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_616_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_614_; 
v___x_611_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCommand_fromJson___closed__16, &l_Lean_Lsp_instFromJsonCommand_fromJson___closed__16_once, _init_l_Lean_Lsp_instFromJsonCommand_fromJson___closed__16);
v___x_612_ = lean_string_append(v___x_611_, v_a_607_);
lean_dec(v_a_607_);
if (v_isShared_610_ == 0)
{
lean_ctor_set(v___x_609_, 0, v___x_612_);
v___x_614_ = v___x_609_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v___x_612_);
v___x_614_ = v_reuseFailAlloc_615_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
return v___x_614_;
}
}
}
else
{
if (lean_obj_tag(v___x_606_) == 0)
{
lean_object* v_a_617_; lean_object* v___x_619_; uint8_t v_isShared_620_; uint8_t v_isSharedCheck_624_; 
lean_dec(v_a_604_);
lean_dec(v_a_583_);
v_a_617_ = lean_ctor_get(v___x_606_, 0);
v_isSharedCheck_624_ = !lean_is_exclusive(v___x_606_);
if (v_isSharedCheck_624_ == 0)
{
v___x_619_ = v___x_606_;
v_isShared_620_ = v_isSharedCheck_624_;
goto v_resetjp_618_;
}
else
{
lean_inc(v_a_617_);
lean_dec(v___x_606_);
v___x_619_ = lean_box(0);
v_isShared_620_ = v_isSharedCheck_624_;
goto v_resetjp_618_;
}
v_resetjp_618_:
{
lean_object* v___x_622_; 
if (v_isShared_620_ == 0)
{
lean_ctor_set_tag(v___x_619_, 0);
v___x_622_ = v___x_619_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_623_; 
v_reuseFailAlloc_623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_623_, 0, v_a_617_);
v___x_622_ = v_reuseFailAlloc_623_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
return v___x_622_;
}
}
}
else
{
lean_object* v_a_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_633_; 
v_a_625_ = lean_ctor_get(v___x_606_, 0);
v_isSharedCheck_633_ = !lean_is_exclusive(v___x_606_);
if (v_isSharedCheck_633_ == 0)
{
v___x_627_ = v___x_606_;
v_isShared_628_ = v_isSharedCheck_633_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_a_625_);
lean_dec(v___x_606_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_633_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v___x_629_; lean_object* v___x_631_; 
v___x_629_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_629_, 0, v_a_583_);
lean_ctor_set(v___x_629_, 1, v_a_604_);
lean_ctor_set(v___x_629_, 2, v_a_625_);
if (v_isShared_628_ == 0)
{
lean_ctor_set(v___x_627_, 0, v___x_629_);
v___x_631_ = v___x_627_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v___x_629_);
v___x_631_ = v_reuseFailAlloc_632_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
return v___x_631_;
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
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonSnippetString_toJson(lean_object* v_x_637_){
_start:
{
lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_638_ = ((lean_object*)(l_Lean_Lsp_instToJsonSnippetString_toJson___closed__0));
v___x_639_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_639_, 0, v_x_637_);
v___x_640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_640_, 0, v___x_638_);
lean_ctor_set(v___x_640_, 1, v___x_639_);
v___x_641_ = lean_box(0);
v___x_642_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_642_, 0, v___x_640_);
lean_ctor_set(v___x_642_, 1, v___x_641_);
v___x_643_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_643_, 0, v___x_642_);
lean_ctor_set(v___x_643_, 1, v___x_641_);
v___x_644_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__2));
v___x_645_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLocation_toJson_spec__0(v___x_643_, v___x_644_);
v___x_646_ = l_Lean_Json_mkObj(v___x_645_);
lean_dec(v___x_645_);
return v___x_646_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonSnippetString_fromJson___closed__2(void){
_start:
{
uint8_t v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; 
v___x_654_ = 1;
v___x_655_ = ((lean_object*)(l_Lean_Lsp_instFromJsonSnippetString_fromJson___closed__1));
v___x_656_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_655_, v___x_654_);
return v___x_656_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonSnippetString_fromJson___closed__3(void){
_start:
{
lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_657_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__5));
v___x_658_ = lean_obj_once(&l_Lean_Lsp_instFromJsonSnippetString_fromJson___closed__2, &l_Lean_Lsp_instFromJsonSnippetString_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonSnippetString_fromJson___closed__2);
v___x_659_ = lean_string_append(v___x_658_, v___x_657_);
return v___x_659_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonSnippetString_fromJson___closed__5(void){
_start:
{
uint8_t v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; 
v___x_662_ = 1;
v___x_663_ = ((lean_object*)(l_Lean_Lsp_instFromJsonSnippetString_fromJson___closed__4));
v___x_664_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_663_, v___x_662_);
return v___x_664_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonSnippetString_fromJson___closed__6(void){
_start:
{
lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; 
v___x_665_ = lean_obj_once(&l_Lean_Lsp_instFromJsonSnippetString_fromJson___closed__5, &l_Lean_Lsp_instFromJsonSnippetString_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonSnippetString_fromJson___closed__5);
v___x_666_ = lean_obj_once(&l_Lean_Lsp_instFromJsonSnippetString_fromJson___closed__3, &l_Lean_Lsp_instFromJsonSnippetString_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonSnippetString_fromJson___closed__3);
v___x_667_ = lean_string_append(v___x_666_, v___x_665_);
return v___x_667_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonSnippetString_fromJson___closed__7(void){
_start:
{
lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; 
v___x_668_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_669_ = lean_obj_once(&l_Lean_Lsp_instFromJsonSnippetString_fromJson___closed__6, &l_Lean_Lsp_instFromJsonSnippetString_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonSnippetString_fromJson___closed__6);
v___x_670_ = lean_string_append(v___x_669_, v___x_668_);
return v___x_670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonSnippetString_fromJson(lean_object* v_json_671_){
_start:
{
lean_object* v___x_672_; lean_object* v___x_673_; 
v___x_672_ = ((lean_object*)(l_Lean_Lsp_instToJsonSnippetString_toJson___closed__0));
v___x_673_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocation_fromJson_spec__0(v_json_671_, v___x_672_);
if (lean_obj_tag(v___x_673_) == 0)
{
lean_object* v_a_674_; lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_683_; 
v_a_674_ = lean_ctor_get(v___x_673_, 0);
v_isSharedCheck_683_ = !lean_is_exclusive(v___x_673_);
if (v_isSharedCheck_683_ == 0)
{
v___x_676_ = v___x_673_;
v_isShared_677_ = v_isSharedCheck_683_;
goto v_resetjp_675_;
}
else
{
lean_inc(v_a_674_);
lean_dec(v___x_673_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_683_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_681_; 
v___x_678_ = lean_obj_once(&l_Lean_Lsp_instFromJsonSnippetString_fromJson___closed__7, &l_Lean_Lsp_instFromJsonSnippetString_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonSnippetString_fromJson___closed__7);
v___x_679_ = lean_string_append(v___x_678_, v_a_674_);
lean_dec(v_a_674_);
if (v_isShared_677_ == 0)
{
lean_ctor_set(v___x_676_, 0, v___x_679_);
v___x_681_ = v___x_676_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v___x_679_);
v___x_681_ = v_reuseFailAlloc_682_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
return v___x_681_;
}
}
}
else
{
if (lean_obj_tag(v___x_673_) == 0)
{
lean_object* v_a_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_691_; 
v_a_684_ = lean_ctor_get(v___x_673_, 0);
v_isSharedCheck_691_ = !lean_is_exclusive(v___x_673_);
if (v_isSharedCheck_691_ == 0)
{
v___x_686_ = v___x_673_;
v_isShared_687_ = v_isSharedCheck_691_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_a_684_);
lean_dec(v___x_673_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_691_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v___x_689_; 
if (v_isShared_687_ == 0)
{
lean_ctor_set_tag(v___x_686_, 0);
v___x_689_ = v___x_686_;
goto v_reusejp_688_;
}
else
{
lean_object* v_reuseFailAlloc_690_; 
v_reuseFailAlloc_690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_690_, 0, v_a_684_);
v___x_689_ = v_reuseFailAlloc_690_;
goto v_reusejp_688_;
}
v_reusejp_688_:
{
return v___x_689_;
}
}
}
else
{
lean_object* v_a_692_; lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_699_; 
v_a_692_ = lean_ctor_get(v___x_673_, 0);
v_isSharedCheck_699_ = !lean_is_exclusive(v___x_673_);
if (v_isSharedCheck_699_ == 0)
{
v___x_694_ = v___x_673_;
v_isShared_695_ = v_isSharedCheck_699_;
goto v_resetjp_693_;
}
else
{
lean_inc(v_a_692_);
lean_dec(v___x_673_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_699_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
lean_object* v___x_697_; 
if (v_isShared_695_ == 0)
{
v___x_697_ = v___x_694_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v_a_692_);
v___x_697_ = v_reuseFailAlloc_698_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
return v___x_697_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextEdit_toJson_spec__0(lean_object* v_k_702_, lean_object* v_x_703_){
_start:
{
if (lean_obj_tag(v_x_703_) == 0)
{
lean_object* v___x_704_; 
lean_dec_ref(v_k_702_);
v___x_704_ = lean_box(0);
return v___x_704_;
}
else
{
lean_object* v_val_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; 
v_val_705_ = lean_ctor_get(v_x_703_, 0);
lean_inc(v_val_705_);
lean_dec_ref_known(v_x_703_, 1);
v___x_706_ = l_Lean_Lsp_instToJsonSnippetString_toJson(v_val_705_);
v___x_707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_707_, 0, v_k_702_);
lean_ctor_set(v___x_707_, 1, v___x_706_);
v___x_708_ = lean_box(0);
v___x_709_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_709_, 0, v___x_707_);
lean_ctor_set(v___x_709_, 1, v___x_708_);
return v___x_709_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextEdit_toJson_spec__1(lean_object* v_k_710_, lean_object* v_x_711_){
_start:
{
if (lean_obj_tag(v_x_711_) == 0)
{
lean_object* v___x_712_; 
lean_dec_ref(v_k_710_);
v___x_712_ = lean_box(0);
return v___x_712_;
}
else
{
lean_object* v_val_713_; lean_object* v___x_715_; uint8_t v_isShared_716_; uint8_t v_isSharedCheck_723_; 
v_val_713_ = lean_ctor_get(v_x_711_, 0);
v_isSharedCheck_723_ = !lean_is_exclusive(v_x_711_);
if (v_isSharedCheck_723_ == 0)
{
v___x_715_ = v_x_711_;
v_isShared_716_ = v_isSharedCheck_723_;
goto v_resetjp_714_;
}
else
{
lean_inc(v_val_713_);
lean_dec(v_x_711_);
v___x_715_ = lean_box(0);
v_isShared_716_ = v_isSharedCheck_723_;
goto v_resetjp_714_;
}
v_resetjp_714_:
{
lean_object* v___x_718_; 
if (v_isShared_716_ == 0)
{
lean_ctor_set_tag(v___x_715_, 3);
v___x_718_ = v___x_715_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v_val_713_);
v___x_718_ = v_reuseFailAlloc_722_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; 
v___x_719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_719_, 0, v_k_710_);
lean_ctor_set(v___x_719_, 1, v___x_718_);
v___x_720_ = lean_box(0);
v___x_721_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_721_, 0, v___x_719_);
lean_ctor_set(v___x_721_, 1, v___x_720_);
return v___x_721_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonTextEdit_toJson(lean_object* v_x_727_){
_start:
{
lean_object* v_range_728_; lean_object* v_newText_729_; lean_object* v_leanExtSnippet_x3f_730_; lean_object* v_annotationId_x3f_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; 
v_range_728_ = lean_ctor_get(v_x_727_, 0);
lean_inc_ref(v_range_728_);
v_newText_729_ = lean_ctor_get(v_x_727_, 1);
lean_inc_ref(v_newText_729_);
v_leanExtSnippet_x3f_730_ = lean_ctor_get(v_x_727_, 2);
lean_inc(v_leanExtSnippet_x3f_730_);
v_annotationId_x3f_731_ = lean_ctor_get(v_x_727_, 3);
lean_inc(v_annotationId_x3f_731_);
lean_dec_ref(v_x_727_);
v___x_732_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__1));
v___x_733_ = l_Lean_Lsp_instToJsonRange_toJson(v_range_728_);
v___x_734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_734_, 0, v___x_732_);
lean_ctor_set(v___x_734_, 1, v___x_733_);
v___x_735_ = lean_box(0);
v___x_736_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_736_, 0, v___x_734_);
lean_ctor_set(v___x_736_, 1, v___x_735_);
v___x_737_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextEdit_toJson___closed__0));
v___x_738_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_738_, 0, v_newText_729_);
v___x_739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_739_, 0, v___x_737_);
lean_ctor_set(v___x_739_, 1, v___x_738_);
v___x_740_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_740_, 0, v___x_739_);
lean_ctor_set(v___x_740_, 1, v___x_735_);
v___x_741_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextEdit_toJson___closed__1));
v___x_742_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextEdit_toJson_spec__0(v___x_741_, v_leanExtSnippet_x3f_730_);
v___x_743_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextEdit_toJson___closed__2));
v___x_744_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextEdit_toJson_spec__1(v___x_743_, v_annotationId_x3f_731_);
v___x_745_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_745_, 0, v___x_744_);
lean_ctor_set(v___x_745_, 1, v___x_735_);
v___x_746_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_746_, 0, v___x_742_);
lean_ctor_set(v___x_746_, 1, v___x_745_);
v___x_747_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_747_, 0, v___x_740_);
lean_ctor_set(v___x_747_, 1, v___x_746_);
v___x_748_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_748_, 0, v___x_736_);
lean_ctor_set(v___x_748_, 1, v___x_747_);
v___x_749_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__2));
v___x_750_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLocation_toJson_spec__0(v___x_748_, v___x_749_);
v___x_751_ = l_Lean_Json_mkObj(v___x_750_);
lean_dec(v___x_750_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextEdit_fromJson_spec__0_spec__0(lean_object* v_x_756_){
_start:
{
if (lean_obj_tag(v_x_756_) == 0)
{
lean_object* v___x_757_; 
v___x_757_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextEdit_fromJson_spec__0_spec__0___closed__0));
return v___x_757_;
}
else
{
lean_object* v___x_758_; 
v___x_758_ = l_Lean_Lsp_instFromJsonSnippetString_fromJson(v_x_756_);
if (lean_obj_tag(v___x_758_) == 0)
{
lean_object* v_a_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_766_; 
v_a_759_ = lean_ctor_get(v___x_758_, 0);
v_isSharedCheck_766_ = !lean_is_exclusive(v___x_758_);
if (v_isSharedCheck_766_ == 0)
{
v___x_761_ = v___x_758_;
v_isShared_762_ = v_isSharedCheck_766_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_a_759_);
lean_dec(v___x_758_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_766_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v___x_764_; 
if (v_isShared_762_ == 0)
{
v___x_764_ = v___x_761_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v_a_759_);
v___x_764_ = v_reuseFailAlloc_765_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
return v___x_764_;
}
}
}
else
{
lean_object* v_a_767_; lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_775_; 
v_a_767_ = lean_ctor_get(v___x_758_, 0);
v_isSharedCheck_775_ = !lean_is_exclusive(v___x_758_);
if (v_isSharedCheck_775_ == 0)
{
v___x_769_ = v___x_758_;
v_isShared_770_ = v_isSharedCheck_775_;
goto v_resetjp_768_;
}
else
{
lean_inc(v_a_767_);
lean_dec(v___x_758_);
v___x_769_ = lean_box(0);
v_isShared_770_ = v_isSharedCheck_775_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
lean_object* v___x_771_; lean_object* v___x_773_; 
v___x_771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_771_, 0, v_a_767_);
if (v_isShared_770_ == 0)
{
lean_ctor_set(v___x_769_, 0, v___x_771_);
v___x_773_ = v___x_769_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v___x_771_);
v___x_773_ = v_reuseFailAlloc_774_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
return v___x_773_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextEdit_fromJson_spec__0(lean_object* v_j_776_, lean_object* v_k_777_){
_start:
{
lean_object* v___x_778_; lean_object* v___x_779_; 
v___x_778_ = l_Lean_Json_getObjValD(v_j_776_, v_k_777_);
v___x_779_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextEdit_fromJson_spec__0_spec__0(v___x_778_);
return v___x_779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextEdit_fromJson_spec__0___boxed(lean_object* v_j_780_, lean_object* v_k_781_){
_start:
{
lean_object* v_res_782_; 
v_res_782_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextEdit_fromJson_spec__0(v_j_780_, v_k_781_);
lean_dec_ref(v_k_781_);
return v_res_782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextEdit_fromJson_spec__1_spec__2(lean_object* v_x_783_){
_start:
{
if (lean_obj_tag(v_x_783_) == 0)
{
lean_object* v___x_784_; 
v___x_784_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextEdit_fromJson_spec__0_spec__0___closed__0));
return v___x_784_;
}
else
{
lean_object* v___x_785_; 
v___x_785_ = l_Lean_Json_getStr_x3f(v_x_783_);
if (lean_obj_tag(v___x_785_) == 0)
{
lean_object* v_a_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_793_; 
v_a_786_ = lean_ctor_get(v___x_785_, 0);
v_isSharedCheck_793_ = !lean_is_exclusive(v___x_785_);
if (v_isSharedCheck_793_ == 0)
{
v___x_788_ = v___x_785_;
v_isShared_789_ = v_isSharedCheck_793_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_a_786_);
lean_dec(v___x_785_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_793_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v___x_791_; 
if (v_isShared_789_ == 0)
{
v___x_791_ = v___x_788_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v_a_786_);
v___x_791_ = v_reuseFailAlloc_792_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
return v___x_791_;
}
}
}
else
{
lean_object* v_a_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_802_; 
v_a_794_ = lean_ctor_get(v___x_785_, 0);
v_isSharedCheck_802_ = !lean_is_exclusive(v___x_785_);
if (v_isSharedCheck_802_ == 0)
{
v___x_796_ = v___x_785_;
v_isShared_797_ = v_isSharedCheck_802_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_a_794_);
lean_dec(v___x_785_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_802_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
lean_object* v___x_798_; lean_object* v___x_800_; 
v___x_798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_798_, 0, v_a_794_);
if (v_isShared_797_ == 0)
{
lean_ctor_set(v___x_796_, 0, v___x_798_);
v___x_800_ = v___x_796_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v___x_798_);
v___x_800_ = v_reuseFailAlloc_801_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
return v___x_800_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextEdit_fromJson_spec__1(lean_object* v_j_803_, lean_object* v_k_804_){
_start:
{
lean_object* v___x_805_; lean_object* v___x_806_; 
v___x_805_ = l_Lean_Json_getObjValD(v_j_803_, v_k_804_);
v___x_806_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextEdit_fromJson_spec__1_spec__2(v___x_805_);
return v___x_806_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextEdit_fromJson_spec__1___boxed(lean_object* v_j_807_, lean_object* v_k_808_){
_start:
{
lean_object* v_res_809_; 
v_res_809_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextEdit_fromJson_spec__1(v_j_807_, v_k_808_);
lean_dec_ref(v_k_808_);
return v_res_809_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__2(void){
_start:
{
uint8_t v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; 
v___x_815_ = 1;
v___x_816_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__1));
v___x_817_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_816_, v___x_815_);
return v___x_817_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__3(void){
_start:
{
lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; 
v___x_818_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__5));
v___x_819_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__2, &l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__2);
v___x_820_ = lean_string_append(v___x_819_, v___x_818_);
return v___x_820_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__4(void){
_start:
{
lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; 
v___x_821_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLocation_fromJson___closed__13, &l_Lean_Lsp_instFromJsonLocation_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonLocation_fromJson___closed__13);
v___x_822_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__3, &l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__3);
v___x_823_ = lean_string_append(v___x_822_, v___x_821_);
return v___x_823_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__5(void){
_start:
{
lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; 
v___x_824_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_825_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__4, &l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__4);
v___x_826_ = lean_string_append(v___x_825_, v___x_824_);
return v___x_826_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__7(void){
_start:
{
uint8_t v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; 
v___x_829_ = 1;
v___x_830_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__6));
v___x_831_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_830_, v___x_829_);
return v___x_831_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__8(void){
_start:
{
lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; 
v___x_832_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__7, &l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__7);
v___x_833_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__3, &l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__3);
v___x_834_ = lean_string_append(v___x_833_, v___x_832_);
return v___x_834_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__9(void){
_start:
{
lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; 
v___x_835_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_836_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__8, &l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__8);
v___x_837_ = lean_string_append(v___x_836_, v___x_835_);
return v___x_837_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__12(void){
_start:
{
uint8_t v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; 
v___x_841_ = 1;
v___x_842_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__11));
v___x_843_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_842_, v___x_841_);
return v___x_843_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__13(void){
_start:
{
lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; 
v___x_844_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__12, &l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__12);
v___x_845_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__3, &l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__3);
v___x_846_ = lean_string_append(v___x_845_, v___x_844_);
return v___x_846_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__14(void){
_start:
{
lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; 
v___x_847_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_848_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__13, &l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__13);
v___x_849_ = lean_string_append(v___x_848_, v___x_847_);
return v___x_849_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__17(void){
_start:
{
uint8_t v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; 
v___x_853_ = 1;
v___x_854_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__16));
v___x_855_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_854_, v___x_853_);
return v___x_855_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__18(void){
_start:
{
lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; 
v___x_856_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__17, &l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__17_once, _init_l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__17);
v___x_857_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__3, &l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__3);
v___x_858_ = lean_string_append(v___x_857_, v___x_856_);
return v___x_858_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__19(void){
_start:
{
lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; 
v___x_859_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_860_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__18, &l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__18_once, _init_l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__18);
v___x_861_ = lean_string_append(v___x_860_, v___x_859_);
return v___x_861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonTextEdit_fromJson(lean_object* v_json_862_){
_start:
{
lean_object* v___x_863_; lean_object* v___x_864_; 
v___x_863_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__1));
lean_inc(v_json_862_);
v___x_864_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocation_fromJson_spec__1(v_json_862_, v___x_863_);
if (lean_obj_tag(v___x_864_) == 0)
{
lean_object* v_a_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_874_; 
lean_dec(v_json_862_);
v_a_865_ = lean_ctor_get(v___x_864_, 0);
v_isSharedCheck_874_ = !lean_is_exclusive(v___x_864_);
if (v_isSharedCheck_874_ == 0)
{
v___x_867_ = v___x_864_;
v_isShared_868_ = v_isSharedCheck_874_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_a_865_);
lean_dec(v___x_864_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_874_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_872_; 
v___x_869_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__5, &l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__5);
v___x_870_ = lean_string_append(v___x_869_, v_a_865_);
lean_dec(v_a_865_);
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 0, v___x_870_);
v___x_872_ = v___x_867_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v___x_870_);
v___x_872_ = v_reuseFailAlloc_873_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
return v___x_872_;
}
}
}
else
{
if (lean_obj_tag(v___x_864_) == 0)
{
lean_object* v_a_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_882_; 
lean_dec(v_json_862_);
v_a_875_ = lean_ctor_get(v___x_864_, 0);
v_isSharedCheck_882_ = !lean_is_exclusive(v___x_864_);
if (v_isSharedCheck_882_ == 0)
{
v___x_877_ = v___x_864_;
v_isShared_878_ = v_isSharedCheck_882_;
goto v_resetjp_876_;
}
else
{
lean_inc(v_a_875_);
lean_dec(v___x_864_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_882_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
lean_object* v___x_880_; 
if (v_isShared_878_ == 0)
{
lean_ctor_set_tag(v___x_877_, 0);
v___x_880_ = v___x_877_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v_a_875_);
v___x_880_ = v_reuseFailAlloc_881_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
return v___x_880_;
}
}
}
else
{
lean_object* v_a_883_; lean_object* v___x_884_; lean_object* v___x_885_; 
v_a_883_ = lean_ctor_get(v___x_864_, 0);
lean_inc(v_a_883_);
lean_dec_ref_known(v___x_864_, 1);
v___x_884_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextEdit_toJson___closed__0));
lean_inc(v_json_862_);
v___x_885_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocation_fromJson_spec__0(v_json_862_, v___x_884_);
if (lean_obj_tag(v___x_885_) == 0)
{
lean_object* v_a_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_895_; 
lean_dec(v_a_883_);
lean_dec(v_json_862_);
v_a_886_ = lean_ctor_get(v___x_885_, 0);
v_isSharedCheck_895_ = !lean_is_exclusive(v___x_885_);
if (v_isSharedCheck_895_ == 0)
{
v___x_888_ = v___x_885_;
v_isShared_889_ = v_isSharedCheck_895_;
goto v_resetjp_887_;
}
else
{
lean_inc(v_a_886_);
lean_dec(v___x_885_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_895_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_893_; 
v___x_890_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__9, &l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__9);
v___x_891_ = lean_string_append(v___x_890_, v_a_886_);
lean_dec(v_a_886_);
if (v_isShared_889_ == 0)
{
lean_ctor_set(v___x_888_, 0, v___x_891_);
v___x_893_ = v___x_888_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v___x_891_);
v___x_893_ = v_reuseFailAlloc_894_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
return v___x_893_;
}
}
}
else
{
if (lean_obj_tag(v___x_885_) == 0)
{
lean_object* v_a_896_; lean_object* v___x_898_; uint8_t v_isShared_899_; uint8_t v_isSharedCheck_903_; 
lean_dec(v_a_883_);
lean_dec(v_json_862_);
v_a_896_ = lean_ctor_get(v___x_885_, 0);
v_isSharedCheck_903_ = !lean_is_exclusive(v___x_885_);
if (v_isSharedCheck_903_ == 0)
{
v___x_898_ = v___x_885_;
v_isShared_899_ = v_isSharedCheck_903_;
goto v_resetjp_897_;
}
else
{
lean_inc(v_a_896_);
lean_dec(v___x_885_);
v___x_898_ = lean_box(0);
v_isShared_899_ = v_isSharedCheck_903_;
goto v_resetjp_897_;
}
v_resetjp_897_:
{
lean_object* v___x_901_; 
if (v_isShared_899_ == 0)
{
lean_ctor_set_tag(v___x_898_, 0);
v___x_901_ = v___x_898_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v_a_896_);
v___x_901_ = v_reuseFailAlloc_902_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
return v___x_901_;
}
}
}
else
{
lean_object* v_a_904_; lean_object* v___x_905_; lean_object* v___x_906_; 
v_a_904_ = lean_ctor_get(v___x_885_, 0);
lean_inc(v_a_904_);
lean_dec_ref_known(v___x_885_, 1);
v___x_905_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextEdit_toJson___closed__1));
lean_inc(v_json_862_);
v___x_906_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextEdit_fromJson_spec__0(v_json_862_, v___x_905_);
if (lean_obj_tag(v___x_906_) == 0)
{
lean_object* v_a_907_; lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_916_; 
lean_dec(v_a_904_);
lean_dec(v_a_883_);
lean_dec(v_json_862_);
v_a_907_ = lean_ctor_get(v___x_906_, 0);
v_isSharedCheck_916_ = !lean_is_exclusive(v___x_906_);
if (v_isSharedCheck_916_ == 0)
{
v___x_909_ = v___x_906_;
v_isShared_910_ = v_isSharedCheck_916_;
goto v_resetjp_908_;
}
else
{
lean_inc(v_a_907_);
lean_dec(v___x_906_);
v___x_909_ = lean_box(0);
v_isShared_910_ = v_isSharedCheck_916_;
goto v_resetjp_908_;
}
v_resetjp_908_:
{
lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_914_; 
v___x_911_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__14, &l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__14_once, _init_l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__14);
v___x_912_ = lean_string_append(v___x_911_, v_a_907_);
lean_dec(v_a_907_);
if (v_isShared_910_ == 0)
{
lean_ctor_set(v___x_909_, 0, v___x_912_);
v___x_914_ = v___x_909_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v___x_912_);
v___x_914_ = v_reuseFailAlloc_915_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
return v___x_914_;
}
}
}
else
{
if (lean_obj_tag(v___x_906_) == 0)
{
lean_object* v_a_917_; lean_object* v___x_919_; uint8_t v_isShared_920_; uint8_t v_isSharedCheck_924_; 
lean_dec(v_a_904_);
lean_dec(v_a_883_);
lean_dec(v_json_862_);
v_a_917_ = lean_ctor_get(v___x_906_, 0);
v_isSharedCheck_924_ = !lean_is_exclusive(v___x_906_);
if (v_isSharedCheck_924_ == 0)
{
v___x_919_ = v___x_906_;
v_isShared_920_ = v_isSharedCheck_924_;
goto v_resetjp_918_;
}
else
{
lean_inc(v_a_917_);
lean_dec(v___x_906_);
v___x_919_ = lean_box(0);
v_isShared_920_ = v_isSharedCheck_924_;
goto v_resetjp_918_;
}
v_resetjp_918_:
{
lean_object* v___x_922_; 
if (v_isShared_920_ == 0)
{
lean_ctor_set_tag(v___x_919_, 0);
v___x_922_ = v___x_919_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v_a_917_);
v___x_922_ = v_reuseFailAlloc_923_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
return v___x_922_;
}
}
}
else
{
lean_object* v_a_925_; lean_object* v___x_926_; lean_object* v___x_927_; 
v_a_925_ = lean_ctor_get(v___x_906_, 0);
lean_inc(v_a_925_);
lean_dec_ref_known(v___x_906_, 1);
v___x_926_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextEdit_toJson___closed__2));
v___x_927_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextEdit_fromJson_spec__1(v_json_862_, v___x_926_);
if (lean_obj_tag(v___x_927_) == 0)
{
lean_object* v_a_928_; lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_937_; 
lean_dec(v_a_925_);
lean_dec(v_a_904_);
lean_dec(v_a_883_);
v_a_928_ = lean_ctor_get(v___x_927_, 0);
v_isSharedCheck_937_ = !lean_is_exclusive(v___x_927_);
if (v_isSharedCheck_937_ == 0)
{
v___x_930_ = v___x_927_;
v_isShared_931_ = v_isSharedCheck_937_;
goto v_resetjp_929_;
}
else
{
lean_inc(v_a_928_);
lean_dec(v___x_927_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_937_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_935_; 
v___x_932_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__19, &l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__19_once, _init_l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__19);
v___x_933_ = lean_string_append(v___x_932_, v_a_928_);
lean_dec(v_a_928_);
if (v_isShared_931_ == 0)
{
lean_ctor_set(v___x_930_, 0, v___x_933_);
v___x_935_ = v___x_930_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v___x_933_);
v___x_935_ = v_reuseFailAlloc_936_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
return v___x_935_;
}
}
}
else
{
if (lean_obj_tag(v___x_927_) == 0)
{
lean_object* v_a_938_; lean_object* v___x_940_; uint8_t v_isShared_941_; uint8_t v_isSharedCheck_945_; 
lean_dec(v_a_925_);
lean_dec(v_a_904_);
lean_dec(v_a_883_);
v_a_938_ = lean_ctor_get(v___x_927_, 0);
v_isSharedCheck_945_ = !lean_is_exclusive(v___x_927_);
if (v_isSharedCheck_945_ == 0)
{
v___x_940_ = v___x_927_;
v_isShared_941_ = v_isSharedCheck_945_;
goto v_resetjp_939_;
}
else
{
lean_inc(v_a_938_);
lean_dec(v___x_927_);
v___x_940_ = lean_box(0);
v_isShared_941_ = v_isSharedCheck_945_;
goto v_resetjp_939_;
}
v_resetjp_939_:
{
lean_object* v___x_943_; 
if (v_isShared_941_ == 0)
{
lean_ctor_set_tag(v___x_940_, 0);
v___x_943_ = v___x_940_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_944_; 
v_reuseFailAlloc_944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_944_, 0, v_a_938_);
v___x_943_ = v_reuseFailAlloc_944_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
return v___x_943_;
}
}
}
else
{
lean_object* v_a_946_; lean_object* v___x_948_; uint8_t v_isShared_949_; uint8_t v_isSharedCheck_954_; 
v_a_946_ = lean_ctor_get(v___x_927_, 0);
v_isSharedCheck_954_ = !lean_is_exclusive(v___x_927_);
if (v_isSharedCheck_954_ == 0)
{
v___x_948_ = v___x_927_;
v_isShared_949_ = v_isSharedCheck_954_;
goto v_resetjp_947_;
}
else
{
lean_inc(v_a_946_);
lean_dec(v___x_927_);
v___x_948_ = lean_box(0);
v_isShared_949_ = v_isSharedCheck_954_;
goto v_resetjp_947_;
}
v_resetjp_947_:
{
lean_object* v___x_950_; lean_object* v___x_952_; 
v___x_950_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_950_, 0, v_a_883_);
lean_ctor_set(v___x_950_, 1, v_a_904_);
lean_ctor_set(v___x_950_, 2, v_a_925_);
lean_ctor_set(v___x_950_, 3, v_a_946_);
if (v_isShared_949_ == 0)
{
lean_ctor_set(v___x_948_, 0, v___x_950_);
v___x_952_ = v___x_948_;
goto v_reusejp_951_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v___x_950_);
v___x_952_ = v_reuseFailAlloc_953_;
goto v_reusejp_951_;
}
v_reusejp_951_:
{
return v___x_952_;
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
LEAN_EXPORT lean_object* l_Lean_Lsp_instAppendTextEditBatch___aux__1(lean_object* v_as_966_, lean_object* v_bs_967_){
_start:
{
lean_object* v___x_968_; 
v___x_968_ = l_Array_append___redArg(v_as_966_, v_bs_967_);
return v___x_968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instAppendTextEditBatch___aux__1___boxed(lean_object* v_as_969_, lean_object* v_bs_970_){
_start:
{
lean_object* v_res_971_; 
v_res_971_ = l_Lean_Lsp_instAppendTextEditBatch___aux__1(v_as_969_, v_bs_970_);
lean_dec_ref(v_bs_970_);
return v_res_971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instCoeTextEditTextEditBatch___lam__0(lean_object* v_te_974_){
_start:
{
lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; 
v___x_975_ = lean_unsigned_to_nat(1u);
v___x_976_ = lean_mk_empty_array_with_capacity(v___x_975_);
v___x_977_ = lean_array_push(v___x_976_, v_te_974_);
return v___x_977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonTextDocumentIdentifier_toJson(lean_object* v_x_980_){
_start:
{
lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; 
v___x_981_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__0));
v___x_982_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_982_, 0, v_x_980_);
v___x_983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_983_, 0, v___x_981_);
lean_ctor_set(v___x_983_, 1, v___x_982_);
v___x_984_ = lean_box(0);
v___x_985_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_985_, 0, v___x_983_);
lean_ctor_set(v___x_985_, 1, v___x_984_);
v___x_986_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_986_, 0, v___x_985_);
lean_ctor_set(v___x_986_, 1, v___x_984_);
v___x_987_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__2));
v___x_988_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLocation_toJson_spec__0(v___x_986_, v___x_987_);
v___x_989_ = l_Lean_Json_mkObj(v___x_988_);
lean_dec(v___x_988_);
return v___x_989_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentIdentifier_fromJson___closed__2(void){
_start:
{
uint8_t v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; 
v___x_997_ = 1;
v___x_998_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentIdentifier_fromJson___closed__1));
v___x_999_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_998_, v___x_997_);
return v___x_999_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentIdentifier_fromJson___closed__3(void){
_start:
{
lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; 
v___x_1000_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__5));
v___x_1001_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentIdentifier_fromJson___closed__2, &l_Lean_Lsp_instFromJsonTextDocumentIdentifier_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonTextDocumentIdentifier_fromJson___closed__2);
v___x_1002_ = lean_string_append(v___x_1001_, v___x_1000_);
return v___x_1002_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentIdentifier_fromJson___closed__4(void){
_start:
{
lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; 
v___x_1003_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLocation_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLocation_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLocation_fromJson___closed__8);
v___x_1004_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentIdentifier_fromJson___closed__3, &l_Lean_Lsp_instFromJsonTextDocumentIdentifier_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonTextDocumentIdentifier_fromJson___closed__3);
v___x_1005_ = lean_string_append(v___x_1004_, v___x_1003_);
return v___x_1005_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentIdentifier_fromJson___closed__5(void){
_start:
{
lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; 
v___x_1006_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_1007_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentIdentifier_fromJson___closed__4, &l_Lean_Lsp_instFromJsonTextDocumentIdentifier_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonTextDocumentIdentifier_fromJson___closed__4);
v___x_1008_ = lean_string_append(v___x_1007_, v___x_1006_);
return v___x_1008_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonTextDocumentIdentifier_fromJson(lean_object* v_json_1009_){
_start:
{
lean_object* v___x_1010_; lean_object* v___x_1011_; 
v___x_1010_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__0));
v___x_1011_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocation_fromJson_spec__0(v_json_1009_, v___x_1010_);
if (lean_obj_tag(v___x_1011_) == 0)
{
lean_object* v_a_1012_; lean_object* v___x_1014_; uint8_t v_isShared_1015_; uint8_t v_isSharedCheck_1021_; 
v_a_1012_ = lean_ctor_get(v___x_1011_, 0);
v_isSharedCheck_1021_ = !lean_is_exclusive(v___x_1011_);
if (v_isSharedCheck_1021_ == 0)
{
v___x_1014_ = v___x_1011_;
v_isShared_1015_ = v_isSharedCheck_1021_;
goto v_resetjp_1013_;
}
else
{
lean_inc(v_a_1012_);
lean_dec(v___x_1011_);
v___x_1014_ = lean_box(0);
v_isShared_1015_ = v_isSharedCheck_1021_;
goto v_resetjp_1013_;
}
v_resetjp_1013_:
{
lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1019_; 
v___x_1016_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentIdentifier_fromJson___closed__5, &l_Lean_Lsp_instFromJsonTextDocumentIdentifier_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonTextDocumentIdentifier_fromJson___closed__5);
v___x_1017_ = lean_string_append(v___x_1016_, v_a_1012_);
lean_dec(v_a_1012_);
if (v_isShared_1015_ == 0)
{
lean_ctor_set(v___x_1014_, 0, v___x_1017_);
v___x_1019_ = v___x_1014_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v___x_1017_);
v___x_1019_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
return v___x_1019_;
}
}
}
else
{
if (lean_obj_tag(v___x_1011_) == 0)
{
lean_object* v_a_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1029_; 
v_a_1022_ = lean_ctor_get(v___x_1011_, 0);
v_isSharedCheck_1029_ = !lean_is_exclusive(v___x_1011_);
if (v_isSharedCheck_1029_ == 0)
{
v___x_1024_ = v___x_1011_;
v_isShared_1025_ = v_isSharedCheck_1029_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_a_1022_);
lean_dec(v___x_1011_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1029_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v___x_1027_; 
if (v_isShared_1025_ == 0)
{
lean_ctor_set_tag(v___x_1024_, 0);
v___x_1027_ = v___x_1024_;
goto v_reusejp_1026_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v_a_1022_);
v___x_1027_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1026_;
}
v_reusejp_1026_:
{
return v___x_1027_;
}
}
}
else
{
lean_object* v_a_1030_; lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1037_; 
v_a_1030_ = lean_ctor_get(v___x_1011_, 0);
v_isSharedCheck_1037_ = !lean_is_exclusive(v___x_1011_);
if (v_isSharedCheck_1037_ == 0)
{
v___x_1032_ = v___x_1011_;
v_isShared_1033_ = v_isSharedCheck_1037_;
goto v_resetjp_1031_;
}
else
{
lean_inc(v_a_1030_);
lean_dec(v___x_1011_);
v___x_1032_ = lean_box(0);
v_isShared_1033_ = v_isSharedCheck_1037_;
goto v_resetjp_1031_;
}
v_resetjp_1031_:
{
lean_object* v___x_1035_; 
if (v_isShared_1033_ == 0)
{
v___x_1035_ = v___x_1032_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v_a_1030_);
v___x_1035_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
return v___x_1035_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonVersionedTextDocumentIdentifier_toJson_spec__0(lean_object* v_k_1040_, lean_object* v_x_1041_){
_start:
{
if (lean_obj_tag(v_x_1041_) == 0)
{
lean_object* v___x_1042_; 
lean_dec_ref(v_k_1040_);
v___x_1042_ = lean_box(0);
return v___x_1042_;
}
else
{
lean_object* v_val_1043_; lean_object* v___x_1045_; uint8_t v_isShared_1046_; uint8_t v_isSharedCheck_1054_; 
v_val_1043_ = lean_ctor_get(v_x_1041_, 0);
v_isSharedCheck_1054_ = !lean_is_exclusive(v_x_1041_);
if (v_isSharedCheck_1054_ == 0)
{
v___x_1045_ = v_x_1041_;
v_isShared_1046_ = v_isSharedCheck_1054_;
goto v_resetjp_1044_;
}
else
{
lean_inc(v_val_1043_);
lean_dec(v_x_1041_);
v___x_1045_ = lean_box(0);
v_isShared_1046_ = v_isSharedCheck_1054_;
goto v_resetjp_1044_;
}
v_resetjp_1044_:
{
lean_object* v___x_1047_; lean_object* v___x_1049_; 
v___x_1047_ = l_Lean_JsonNumber_fromNat(v_val_1043_);
if (v_isShared_1046_ == 0)
{
lean_ctor_set_tag(v___x_1045_, 2);
lean_ctor_set(v___x_1045_, 0, v___x_1047_);
v___x_1049_ = v___x_1045_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v___x_1047_);
v___x_1049_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1048_;
}
v_reusejp_1048_:
{
lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; 
v___x_1050_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1050_, 0, v_k_1040_);
lean_ctor_set(v___x_1050_, 1, v___x_1049_);
v___x_1051_ = lean_box(0);
v___x_1052_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1052_, 0, v___x_1050_);
lean_ctor_set(v___x_1052_, 1, v___x_1051_);
return v___x_1052_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonVersionedTextDocumentIdentifier_toJson(lean_object* v_x_1056_){
_start:
{
lean_object* v_uri_1057_; lean_object* v_version_x3f_1058_; lean_object* v___x_1060_; uint8_t v_isShared_1061_; uint8_t v_isSharedCheck_1076_; 
v_uri_1057_ = lean_ctor_get(v_x_1056_, 0);
v_version_x3f_1058_ = lean_ctor_get(v_x_1056_, 1);
v_isSharedCheck_1076_ = !lean_is_exclusive(v_x_1056_);
if (v_isSharedCheck_1076_ == 0)
{
v___x_1060_ = v_x_1056_;
v_isShared_1061_ = v_isSharedCheck_1076_;
goto v_resetjp_1059_;
}
else
{
lean_inc(v_version_x3f_1058_);
lean_inc(v_uri_1057_);
lean_dec(v_x_1056_);
v___x_1060_ = lean_box(0);
v_isShared_1061_ = v_isSharedCheck_1076_;
goto v_resetjp_1059_;
}
v_resetjp_1059_:
{
lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1065_; 
v___x_1062_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__0));
v___x_1063_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1063_, 0, v_uri_1057_);
if (v_isShared_1061_ == 0)
{
lean_ctor_set(v___x_1060_, 1, v___x_1063_);
lean_ctor_set(v___x_1060_, 0, v___x_1062_);
v___x_1065_ = v___x_1060_;
goto v_reusejp_1064_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v___x_1062_);
lean_ctor_set(v_reuseFailAlloc_1075_, 1, v___x_1063_);
v___x_1065_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1064_;
}
v_reusejp_1064_:
{
lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; 
v___x_1066_ = lean_box(0);
v___x_1067_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1067_, 0, v___x_1065_);
lean_ctor_set(v___x_1067_, 1, v___x_1066_);
v___x_1068_ = ((lean_object*)(l_Lean_Lsp_instToJsonVersionedTextDocumentIdentifier_toJson___closed__0));
v___x_1069_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonVersionedTextDocumentIdentifier_toJson_spec__0(v___x_1068_, v_version_x3f_1058_);
v___x_1070_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1069_);
lean_ctor_set(v___x_1070_, 1, v___x_1066_);
v___x_1071_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1071_, 0, v___x_1067_);
lean_ctor_set(v___x_1071_, 1, v___x_1070_);
v___x_1072_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__2));
v___x_1073_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLocation_toJson_spec__0(v___x_1071_, v___x_1072_);
v___x_1074_ = l_Lean_Json_mkObj(v___x_1073_);
lean_dec(v___x_1073_);
return v___x_1074_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson_spec__0_spec__0(lean_object* v_x_1081_){
_start:
{
if (lean_obj_tag(v_x_1081_) == 0)
{
lean_object* v___x_1082_; 
v___x_1082_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson_spec__0_spec__0___closed__0));
return v___x_1082_;
}
else
{
lean_object* v___x_1083_; 
v___x_1083_ = l_Lean_Json_getNat_x3f(v_x_1081_);
if (lean_obj_tag(v___x_1083_) == 0)
{
lean_object* v_a_1084_; lean_object* v___x_1086_; uint8_t v_isShared_1087_; uint8_t v_isSharedCheck_1091_; 
v_a_1084_ = lean_ctor_get(v___x_1083_, 0);
v_isSharedCheck_1091_ = !lean_is_exclusive(v___x_1083_);
if (v_isSharedCheck_1091_ == 0)
{
v___x_1086_ = v___x_1083_;
v_isShared_1087_ = v_isSharedCheck_1091_;
goto v_resetjp_1085_;
}
else
{
lean_inc(v_a_1084_);
lean_dec(v___x_1083_);
v___x_1086_ = lean_box(0);
v_isShared_1087_ = v_isSharedCheck_1091_;
goto v_resetjp_1085_;
}
v_resetjp_1085_:
{
lean_object* v___x_1089_; 
if (v_isShared_1087_ == 0)
{
v___x_1089_ = v___x_1086_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v_a_1084_);
v___x_1089_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
return v___x_1089_;
}
}
}
else
{
lean_object* v_a_1092_; lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1100_; 
v_a_1092_ = lean_ctor_get(v___x_1083_, 0);
v_isSharedCheck_1100_ = !lean_is_exclusive(v___x_1083_);
if (v_isSharedCheck_1100_ == 0)
{
v___x_1094_ = v___x_1083_;
v_isShared_1095_ = v_isSharedCheck_1100_;
goto v_resetjp_1093_;
}
else
{
lean_inc(v_a_1092_);
lean_dec(v___x_1083_);
v___x_1094_ = lean_box(0);
v_isShared_1095_ = v_isSharedCheck_1100_;
goto v_resetjp_1093_;
}
v_resetjp_1093_:
{
lean_object* v___x_1096_; lean_object* v___x_1098_; 
v___x_1096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1096_, 0, v_a_1092_);
if (v_isShared_1095_ == 0)
{
lean_ctor_set(v___x_1094_, 0, v___x_1096_);
v___x_1098_ = v___x_1094_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v___x_1096_);
v___x_1098_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
return v___x_1098_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson_spec__0(lean_object* v_j_1101_, lean_object* v_k_1102_){
_start:
{
lean_object* v___x_1103_; lean_object* v___x_1104_; 
v___x_1103_ = l_Lean_Json_getObjValD(v_j_1101_, v_k_1102_);
v___x_1104_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson_spec__0_spec__0(v___x_1103_);
return v___x_1104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson_spec__0___boxed(lean_object* v_j_1105_, lean_object* v_k_1106_){
_start:
{
lean_object* v_res_1107_; 
v_res_1107_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson_spec__0(v_j_1105_, v_k_1106_);
lean_dec_ref(v_k_1106_);
return v_res_1107_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__2(void){
_start:
{
uint8_t v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; 
v___x_1113_ = 1;
v___x_1114_ = ((lean_object*)(l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__1));
v___x_1115_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1114_, v___x_1113_);
return v___x_1115_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__3(void){
_start:
{
lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; 
v___x_1116_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__5));
v___x_1117_ = lean_obj_once(&l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__2, &l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__2);
v___x_1118_ = lean_string_append(v___x_1117_, v___x_1116_);
return v___x_1118_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__4(void){
_start:
{
lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; 
v___x_1119_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLocation_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLocation_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLocation_fromJson___closed__8);
v___x_1120_ = lean_obj_once(&l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__3, &l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__3);
v___x_1121_ = lean_string_append(v___x_1120_, v___x_1119_);
return v___x_1121_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__5(void){
_start:
{
lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; 
v___x_1122_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_1123_ = lean_obj_once(&l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__4, &l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__4);
v___x_1124_ = lean_string_append(v___x_1123_, v___x_1122_);
return v___x_1124_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__8(void){
_start:
{
uint8_t v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; 
v___x_1128_ = 1;
v___x_1129_ = ((lean_object*)(l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__7));
v___x_1130_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1129_, v___x_1128_);
return v___x_1130_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__9(void){
_start:
{
lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; 
v___x_1131_ = lean_obj_once(&l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__8, &l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__8);
v___x_1132_ = lean_obj_once(&l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__3, &l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__3);
v___x_1133_ = lean_string_append(v___x_1132_, v___x_1131_);
return v___x_1133_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__10(void){
_start:
{
lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; 
v___x_1134_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_1135_ = lean_obj_once(&l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__9, &l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__9);
v___x_1136_ = lean_string_append(v___x_1135_, v___x_1134_);
return v___x_1136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson(lean_object* v_json_1137_){
_start:
{
lean_object* v___x_1138_; lean_object* v___x_1139_; 
v___x_1138_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__0));
lean_inc(v_json_1137_);
v___x_1139_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocation_fromJson_spec__0(v_json_1137_, v___x_1138_);
if (lean_obj_tag(v___x_1139_) == 0)
{
lean_object* v_a_1140_; lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1149_; 
lean_dec(v_json_1137_);
v_a_1140_ = lean_ctor_get(v___x_1139_, 0);
v_isSharedCheck_1149_ = !lean_is_exclusive(v___x_1139_);
if (v_isSharedCheck_1149_ == 0)
{
v___x_1142_ = v___x_1139_;
v_isShared_1143_ = v_isSharedCheck_1149_;
goto v_resetjp_1141_;
}
else
{
lean_inc(v_a_1140_);
lean_dec(v___x_1139_);
v___x_1142_ = lean_box(0);
v_isShared_1143_ = v_isSharedCheck_1149_;
goto v_resetjp_1141_;
}
v_resetjp_1141_:
{
lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1147_; 
v___x_1144_ = lean_obj_once(&l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__5, &l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__5);
v___x_1145_ = lean_string_append(v___x_1144_, v_a_1140_);
lean_dec(v_a_1140_);
if (v_isShared_1143_ == 0)
{
lean_ctor_set(v___x_1142_, 0, v___x_1145_);
v___x_1147_ = v___x_1142_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v___x_1145_);
v___x_1147_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
return v___x_1147_;
}
}
}
else
{
if (lean_obj_tag(v___x_1139_) == 0)
{
lean_object* v_a_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1157_; 
lean_dec(v_json_1137_);
v_a_1150_ = lean_ctor_get(v___x_1139_, 0);
v_isSharedCheck_1157_ = !lean_is_exclusive(v___x_1139_);
if (v_isSharedCheck_1157_ == 0)
{
v___x_1152_ = v___x_1139_;
v_isShared_1153_ = v_isSharedCheck_1157_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_a_1150_);
lean_dec(v___x_1139_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1157_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v___x_1155_; 
if (v_isShared_1153_ == 0)
{
lean_ctor_set_tag(v___x_1152_, 0);
v___x_1155_ = v___x_1152_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v_a_1150_);
v___x_1155_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
return v___x_1155_;
}
}
}
else
{
lean_object* v_a_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; 
v_a_1158_ = lean_ctor_get(v___x_1139_, 0);
lean_inc(v_a_1158_);
lean_dec_ref_known(v___x_1139_, 1);
v___x_1159_ = ((lean_object*)(l_Lean_Lsp_instToJsonVersionedTextDocumentIdentifier_toJson___closed__0));
v___x_1160_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson_spec__0(v_json_1137_, v___x_1159_);
if (lean_obj_tag(v___x_1160_) == 0)
{
lean_object* v_a_1161_; lean_object* v___x_1163_; uint8_t v_isShared_1164_; uint8_t v_isSharedCheck_1170_; 
lean_dec(v_a_1158_);
v_a_1161_ = lean_ctor_get(v___x_1160_, 0);
v_isSharedCheck_1170_ = !lean_is_exclusive(v___x_1160_);
if (v_isSharedCheck_1170_ == 0)
{
v___x_1163_ = v___x_1160_;
v_isShared_1164_ = v_isSharedCheck_1170_;
goto v_resetjp_1162_;
}
else
{
lean_inc(v_a_1161_);
lean_dec(v___x_1160_);
v___x_1163_ = lean_box(0);
v_isShared_1164_ = v_isSharedCheck_1170_;
goto v_resetjp_1162_;
}
v_resetjp_1162_:
{
lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1168_; 
v___x_1165_ = lean_obj_once(&l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__10, &l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson___closed__10);
v___x_1166_ = lean_string_append(v___x_1165_, v_a_1161_);
lean_dec(v_a_1161_);
if (v_isShared_1164_ == 0)
{
lean_ctor_set(v___x_1163_, 0, v___x_1166_);
v___x_1168_ = v___x_1163_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v___x_1166_);
v___x_1168_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
return v___x_1168_;
}
}
}
else
{
if (lean_obj_tag(v___x_1160_) == 0)
{
lean_object* v_a_1171_; lean_object* v___x_1173_; uint8_t v_isShared_1174_; uint8_t v_isSharedCheck_1178_; 
lean_dec(v_a_1158_);
v_a_1171_ = lean_ctor_get(v___x_1160_, 0);
v_isSharedCheck_1178_ = !lean_is_exclusive(v___x_1160_);
if (v_isSharedCheck_1178_ == 0)
{
v___x_1173_ = v___x_1160_;
v_isShared_1174_ = v_isSharedCheck_1178_;
goto v_resetjp_1172_;
}
else
{
lean_inc(v_a_1171_);
lean_dec(v___x_1160_);
v___x_1173_ = lean_box(0);
v_isShared_1174_ = v_isSharedCheck_1178_;
goto v_resetjp_1172_;
}
v_resetjp_1172_:
{
lean_object* v___x_1176_; 
if (v_isShared_1174_ == 0)
{
lean_ctor_set_tag(v___x_1173_, 0);
v___x_1176_ = v___x_1173_;
goto v_reusejp_1175_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v_a_1171_);
v___x_1176_ = v_reuseFailAlloc_1177_;
goto v_reusejp_1175_;
}
v_reusejp_1175_:
{
return v___x_1176_;
}
}
}
else
{
lean_object* v_a_1179_; lean_object* v___x_1181_; uint8_t v_isShared_1182_; uint8_t v_isSharedCheck_1187_; 
v_a_1179_ = lean_ctor_get(v___x_1160_, 0);
v_isSharedCheck_1187_ = !lean_is_exclusive(v___x_1160_);
if (v_isSharedCheck_1187_ == 0)
{
v___x_1181_ = v___x_1160_;
v_isShared_1182_ = v_isSharedCheck_1187_;
goto v_resetjp_1180_;
}
else
{
lean_inc(v_a_1179_);
lean_dec(v___x_1160_);
v___x_1181_ = lean_box(0);
v_isShared_1182_ = v_isSharedCheck_1187_;
goto v_resetjp_1180_;
}
v_resetjp_1180_:
{
lean_object* v___x_1183_; lean_object* v___x_1185_; 
v___x_1183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1183_, 0, v_a_1158_);
lean_ctor_set(v___x_1183_, 1, v_a_1179_);
if (v_isShared_1182_ == 0)
{
lean_ctor_set(v___x_1181_, 0, v___x_1183_);
v___x_1185_ = v___x_1181_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v___x_1183_);
v___x_1185_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
return v___x_1185_;
}
}
}
}
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonTextDocumentEdit_toJson_spec__0_spec__0(size_t v_sz_1190_, size_t v_i_1191_, lean_object* v_bs_1192_){
_start:
{
uint8_t v___x_1193_; 
v___x_1193_ = lean_usize_dec_lt(v_i_1191_, v_sz_1190_);
if (v___x_1193_ == 0)
{
return v_bs_1192_;
}
else
{
lean_object* v_v_1194_; lean_object* v___x_1195_; lean_object* v_bs_x27_1196_; lean_object* v___x_1197_; size_t v___x_1198_; size_t v___x_1199_; lean_object* v___x_1200_; 
v_v_1194_ = lean_array_uget(v_bs_1192_, v_i_1191_);
v___x_1195_ = lean_unsigned_to_nat(0u);
v_bs_x27_1196_ = lean_array_uset(v_bs_1192_, v_i_1191_, v___x_1195_);
v___x_1197_ = l_Lean_Lsp_instToJsonTextEdit_toJson(v_v_1194_);
v___x_1198_ = ((size_t)1ULL);
v___x_1199_ = lean_usize_add(v_i_1191_, v___x_1198_);
v___x_1200_ = lean_array_uset(v_bs_x27_1196_, v_i_1191_, v___x_1197_);
v_i_1191_ = v___x_1199_;
v_bs_1192_ = v___x_1200_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonTextDocumentEdit_toJson_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1190_ = stack[0].m_num;
size_t v_i_1191_ = stack[1].m_num;
lean_object* v_bs_1192_ = stack[2].m_obj;
lean_object* v_res_1202_;
v_res_1202_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonTextDocumentEdit_toJson_spec__0_spec__0(v_sz_1190_, v_i_1191_, v_bs_1192_);
stack->m_obj
 = v_res_1202_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonTextDocumentEdit_toJson_spec__0_spec__0___boxed(lean_object* v_sz_1203_, lean_object* v_i_1204_, lean_object* v_bs_1205_){
_start:
{
size_t v_sz_boxed_1206_; size_t v_i_boxed_1207_; lean_object* v_res_1208_; 
v_sz_boxed_1206_ = lean_unbox_usize(v_sz_1203_);
lean_dec(v_sz_1203_);
v_i_boxed_1207_ = lean_unbox_usize(v_i_1204_);
lean_dec(v_i_1204_);
v_res_1208_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonTextDocumentEdit_toJson_spec__0_spec__0(v_sz_boxed_1206_, v_i_boxed_1207_, v_bs_1205_);
return v_res_1208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonTextDocumentEdit_toJson_spec__0(lean_object* v_a_1209_){
_start:
{
size_t v_sz_1210_; size_t v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; 
v_sz_1210_ = lean_array_size(v_a_1209_);
v___x_1211_ = ((size_t)0ULL);
v___x_1212_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonTextDocumentEdit_toJson_spec__0_spec__0(v_sz_1210_, v___x_1211_, v_a_1209_);
v___x_1213_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1213_, 0, v___x_1212_);
return v___x_1213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonTextDocumentEdit_toJson(lean_object* v_x_1216_){
_start:
{
lean_object* v_textDocument_1217_; lean_object* v_edits_1218_; lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1238_; 
v_textDocument_1217_ = lean_ctor_get(v_x_1216_, 0);
v_edits_1218_ = lean_ctor_get(v_x_1216_, 1);
v_isSharedCheck_1238_ = !lean_is_exclusive(v_x_1216_);
if (v_isSharedCheck_1238_ == 0)
{
v___x_1220_ = v_x_1216_;
v_isShared_1221_ = v_isSharedCheck_1238_;
goto v_resetjp_1219_;
}
else
{
lean_inc(v_edits_1218_);
lean_inc(v_textDocument_1217_);
lean_dec(v_x_1216_);
v___x_1220_ = lean_box(0);
v_isShared_1221_ = v_isSharedCheck_1238_;
goto v_resetjp_1219_;
}
v_resetjp_1219_:
{
lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1225_; 
v___x_1222_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextDocumentEdit_toJson___closed__0));
v___x_1223_ = l_Lean_Lsp_instToJsonVersionedTextDocumentIdentifier_toJson(v_textDocument_1217_);
if (v_isShared_1221_ == 0)
{
lean_ctor_set(v___x_1220_, 1, v___x_1223_);
lean_ctor_set(v___x_1220_, 0, v___x_1222_);
v___x_1225_ = v___x_1220_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1237_; 
v_reuseFailAlloc_1237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1237_, 0, v___x_1222_);
lean_ctor_set(v_reuseFailAlloc_1237_, 1, v___x_1223_);
v___x_1225_ = v_reuseFailAlloc_1237_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; 
v___x_1226_ = lean_box(0);
v___x_1227_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1227_, 0, v___x_1225_);
lean_ctor_set(v___x_1227_, 1, v___x_1226_);
v___x_1228_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextDocumentEdit_toJson___closed__1));
v___x_1229_ = l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonTextDocumentEdit_toJson_spec__0(v_edits_1218_);
v___x_1230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1230_, 0, v___x_1228_);
lean_ctor_set(v___x_1230_, 1, v___x_1229_);
v___x_1231_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1231_, 0, v___x_1230_);
lean_ctor_set(v___x_1231_, 1, v___x_1226_);
v___x_1232_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1232_, 0, v___x_1231_);
lean_ctor_set(v___x_1232_, 1, v___x_1226_);
v___x_1233_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1233_, 0, v___x_1227_);
lean_ctor_set(v___x_1233_, 1, v___x_1232_);
v___x_1234_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__2));
v___x_1235_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLocation_toJson_spec__0(v___x_1233_, v___x_1234_);
v___x_1236_ = l_Lean_Json_mkObj(v___x_1235_);
lean_dec(v___x_1235_);
return v___x_1236_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentEdit_fromJson_spec__0(lean_object* v_j_1241_, lean_object* v_k_1242_){
_start:
{
lean_object* v___x_1243_; lean_object* v___x_1244_; 
v___x_1243_ = l_Lean_Json_getObjValD(v_j_1241_, v_k_1242_);
v___x_1244_ = l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson(v___x_1243_);
return v___x_1244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentEdit_fromJson_spec__0___boxed(lean_object* v_j_1245_, lean_object* v_k_1246_){
_start:
{
lean_object* v_res_1247_; 
v_res_1247_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentEdit_fromJson_spec__0(v_j_1245_, v_k_1246_);
lean_dec_ref(v_k_1246_);
return v_res_1247_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentEdit_fromJson_spec__1_spec__1_spec__2(size_t v_sz_1248_, size_t v_i_1249_, lean_object* v_bs_1250_){
_start:
{
uint8_t v___x_1251_; 
v___x_1251_ = lean_usize_dec_lt(v_i_1249_, v_sz_1248_);
if (v___x_1251_ == 0)
{
lean_object* v___x_1252_; 
v___x_1252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1252_, 0, v_bs_1250_);
return v___x_1252_;
}
else
{
lean_object* v_v_1253_; lean_object* v___x_1254_; 
v_v_1253_ = lean_array_uget_borrowed(v_bs_1250_, v_i_1249_);
lean_inc(v_v_1253_);
v___x_1254_ = l_Lean_Lsp_instFromJsonTextEdit_fromJson(v_v_1253_);
if (lean_obj_tag(v___x_1254_) == 0)
{
lean_object* v_a_1255_; lean_object* v___x_1257_; uint8_t v_isShared_1258_; uint8_t v_isSharedCheck_1262_; 
lean_dec_ref(v_bs_1250_);
v_a_1255_ = lean_ctor_get(v___x_1254_, 0);
v_isSharedCheck_1262_ = !lean_is_exclusive(v___x_1254_);
if (v_isSharedCheck_1262_ == 0)
{
v___x_1257_ = v___x_1254_;
v_isShared_1258_ = v_isSharedCheck_1262_;
goto v_resetjp_1256_;
}
else
{
lean_inc(v_a_1255_);
lean_dec(v___x_1254_);
v___x_1257_ = lean_box(0);
v_isShared_1258_ = v_isSharedCheck_1262_;
goto v_resetjp_1256_;
}
v_resetjp_1256_:
{
lean_object* v___x_1260_; 
if (v_isShared_1258_ == 0)
{
v___x_1260_ = v___x_1257_;
goto v_reusejp_1259_;
}
else
{
lean_object* v_reuseFailAlloc_1261_; 
v_reuseFailAlloc_1261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v_a_1255_);
v___x_1260_ = v_reuseFailAlloc_1261_;
goto v_reusejp_1259_;
}
v_reusejp_1259_:
{
return v___x_1260_;
}
}
}
else
{
lean_object* v_a_1263_; lean_object* v___x_1264_; lean_object* v_bs_x27_1265_; size_t v___x_1266_; size_t v___x_1267_; lean_object* v___x_1268_; 
v_a_1263_ = lean_ctor_get(v___x_1254_, 0);
lean_inc(v_a_1263_);
lean_dec_ref_known(v___x_1254_, 1);
v___x_1264_ = lean_unsigned_to_nat(0u);
v_bs_x27_1265_ = lean_array_uset(v_bs_1250_, v_i_1249_, v___x_1264_);
v___x_1266_ = ((size_t)1ULL);
v___x_1267_ = lean_usize_add(v_i_1249_, v___x_1266_);
v___x_1268_ = lean_array_uset(v_bs_x27_1265_, v_i_1249_, v_a_1263_);
v_i_1249_ = v___x_1267_;
v_bs_1250_ = v___x_1268_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentEdit_fromJson_spec__1_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1248_ = stack[0].m_num;
size_t v_i_1249_ = stack[1].m_num;
lean_object* v_bs_1250_ = stack[2].m_obj;
lean_object* v_res_1270_;
v_res_1270_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentEdit_fromJson_spec__1_spec__1_spec__2(v_sz_1248_, v_i_1249_, v_bs_1250_);
stack->m_obj
 = v_res_1270_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentEdit_fromJson_spec__1_spec__1_spec__2___boxed(lean_object* v_sz_1271_, lean_object* v_i_1272_, lean_object* v_bs_1273_){
_start:
{
size_t v_sz_boxed_1274_; size_t v_i_boxed_1275_; lean_object* v_res_1276_; 
v_sz_boxed_1274_ = lean_unbox_usize(v_sz_1271_);
lean_dec(v_sz_1271_);
v_i_boxed_1275_ = lean_unbox_usize(v_i_1272_);
lean_dec(v_i_1272_);
v_res_1276_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentEdit_fromJson_spec__1_spec__1_spec__2(v_sz_boxed_1274_, v_i_boxed_1275_, v_bs_1273_);
return v_res_1276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentEdit_fromJson_spec__1_spec__1(lean_object* v_x_1277_){
_start:
{
if (lean_obj_tag(v_x_1277_) == 4)
{
lean_object* v_elems_1278_; size_t v_sz_1279_; size_t v___x_1280_; lean_object* v___x_1281_; 
v_elems_1278_ = lean_ctor_get(v_x_1277_, 0);
lean_inc_ref(v_elems_1278_);
lean_dec_ref_known(v_x_1277_, 1);
v_sz_1279_ = lean_array_size(v_elems_1278_);
v___x_1280_ = ((size_t)0ULL);
v___x_1281_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentEdit_fromJson_spec__1_spec__1_spec__2(v_sz_1279_, v___x_1280_, v_elems_1278_);
return v___x_1281_;
}
else
{
lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; 
v___x_1282_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCommand_fromJson_spec__0_spec__0_spec__1___closed__0));
v___x_1283_ = lean_unsigned_to_nat(80u);
v___x_1284_ = l_Lean_Json_pretty(v_x_1277_, v___x_1283_);
v___x_1285_ = lean_string_append(v___x_1282_, v___x_1284_);
lean_dec_ref(v___x_1284_);
v___x_1286_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCommand_fromJson_spec__0_spec__0_spec__1___closed__1));
v___x_1287_ = lean_string_append(v___x_1285_, v___x_1286_);
v___x_1288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1288_, 0, v___x_1287_);
return v___x_1288_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentEdit_fromJson_spec__1(lean_object* v_j_1289_, lean_object* v_k_1290_){
_start:
{
lean_object* v___x_1291_; lean_object* v___x_1292_; 
v___x_1291_ = l_Lean_Json_getObjValD(v_j_1289_, v_k_1290_);
v___x_1292_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentEdit_fromJson_spec__1_spec__1(v___x_1291_);
return v___x_1292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentEdit_fromJson_spec__1___boxed(lean_object* v_j_1293_, lean_object* v_k_1294_){
_start:
{
lean_object* v_res_1295_; 
v_res_1295_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentEdit_fromJson_spec__1(v_j_1293_, v_k_1294_);
lean_dec_ref(v_k_1294_);
return v_res_1295_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__2(void){
_start:
{
uint8_t v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; 
v___x_1301_ = 1;
v___x_1302_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__1));
v___x_1303_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1302_, v___x_1301_);
return v___x_1303_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__3(void){
_start:
{
lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; 
v___x_1304_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__5));
v___x_1305_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__2, &l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__2);
v___x_1306_ = lean_string_append(v___x_1305_, v___x_1304_);
return v___x_1306_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__5(void){
_start:
{
uint8_t v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; 
v___x_1309_ = 1;
v___x_1310_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__4));
v___x_1311_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1310_, v___x_1309_);
return v___x_1311_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__6(void){
_start:
{
lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; 
v___x_1312_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__5, &l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__5);
v___x_1313_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__3, &l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__3);
v___x_1314_ = lean_string_append(v___x_1313_, v___x_1312_);
return v___x_1314_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__7(void){
_start:
{
lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; 
v___x_1315_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_1316_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__6, &l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__6);
v___x_1317_ = lean_string_append(v___x_1316_, v___x_1315_);
return v___x_1317_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__9(void){
_start:
{
uint8_t v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; 
v___x_1320_ = 1;
v___x_1321_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__8));
v___x_1322_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1321_, v___x_1320_);
return v___x_1322_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__10(void){
_start:
{
lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; 
v___x_1323_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__9, &l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__9);
v___x_1324_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__3, &l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__3);
v___x_1325_ = lean_string_append(v___x_1324_, v___x_1323_);
return v___x_1325_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__11(void){
_start:
{
lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; 
v___x_1326_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_1327_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__10, &l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__10);
v___x_1328_ = lean_string_append(v___x_1327_, v___x_1326_);
return v___x_1328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson(lean_object* v_json_1329_){
_start:
{
lean_object* v___x_1330_; lean_object* v___x_1331_; 
v___x_1330_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextDocumentEdit_toJson___closed__0));
lean_inc(v_json_1329_);
v___x_1331_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentEdit_fromJson_spec__0(v_json_1329_, v___x_1330_);
if (lean_obj_tag(v___x_1331_) == 0)
{
lean_object* v_a_1332_; lean_object* v___x_1334_; uint8_t v_isShared_1335_; uint8_t v_isSharedCheck_1341_; 
lean_dec(v_json_1329_);
v_a_1332_ = lean_ctor_get(v___x_1331_, 0);
v_isSharedCheck_1341_ = !lean_is_exclusive(v___x_1331_);
if (v_isSharedCheck_1341_ == 0)
{
v___x_1334_ = v___x_1331_;
v_isShared_1335_ = v_isSharedCheck_1341_;
goto v_resetjp_1333_;
}
else
{
lean_inc(v_a_1332_);
lean_dec(v___x_1331_);
v___x_1334_ = lean_box(0);
v_isShared_1335_ = v_isSharedCheck_1341_;
goto v_resetjp_1333_;
}
v_resetjp_1333_:
{
lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1339_; 
v___x_1336_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__7, &l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__7);
v___x_1337_ = lean_string_append(v___x_1336_, v_a_1332_);
lean_dec(v_a_1332_);
if (v_isShared_1335_ == 0)
{
lean_ctor_set(v___x_1334_, 0, v___x_1337_);
v___x_1339_ = v___x_1334_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v___x_1337_);
v___x_1339_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
return v___x_1339_;
}
}
}
else
{
if (lean_obj_tag(v___x_1331_) == 0)
{
lean_object* v_a_1342_; lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1349_; 
lean_dec(v_json_1329_);
v_a_1342_ = lean_ctor_get(v___x_1331_, 0);
v_isSharedCheck_1349_ = !lean_is_exclusive(v___x_1331_);
if (v_isSharedCheck_1349_ == 0)
{
v___x_1344_ = v___x_1331_;
v_isShared_1345_ = v_isSharedCheck_1349_;
goto v_resetjp_1343_;
}
else
{
lean_inc(v_a_1342_);
lean_dec(v___x_1331_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1349_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
lean_object* v___x_1347_; 
if (v_isShared_1345_ == 0)
{
lean_ctor_set_tag(v___x_1344_, 0);
v___x_1347_ = v___x_1344_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1348_; 
v_reuseFailAlloc_1348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1348_, 0, v_a_1342_);
v___x_1347_ = v_reuseFailAlloc_1348_;
goto v_reusejp_1346_;
}
v_reusejp_1346_:
{
return v___x_1347_;
}
}
}
else
{
lean_object* v_a_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; 
v_a_1350_ = lean_ctor_get(v___x_1331_, 0);
lean_inc(v_a_1350_);
lean_dec_ref_known(v___x_1331_, 1);
v___x_1351_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextDocumentEdit_toJson___closed__1));
v___x_1352_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentEdit_fromJson_spec__1(v_json_1329_, v___x_1351_);
if (lean_obj_tag(v___x_1352_) == 0)
{
lean_object* v_a_1353_; lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1362_; 
lean_dec(v_a_1350_);
v_a_1353_ = lean_ctor_get(v___x_1352_, 0);
v_isSharedCheck_1362_ = !lean_is_exclusive(v___x_1352_);
if (v_isSharedCheck_1362_ == 0)
{
v___x_1355_ = v___x_1352_;
v_isShared_1356_ = v_isSharedCheck_1362_;
goto v_resetjp_1354_;
}
else
{
lean_inc(v_a_1353_);
lean_dec(v___x_1352_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1362_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1360_; 
v___x_1357_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__11, &l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__11);
v___x_1358_ = lean_string_append(v___x_1357_, v_a_1353_);
lean_dec(v_a_1353_);
if (v_isShared_1356_ == 0)
{
lean_ctor_set(v___x_1355_, 0, v___x_1358_);
v___x_1360_ = v___x_1355_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v___x_1358_);
v___x_1360_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
return v___x_1360_;
}
}
}
else
{
if (lean_obj_tag(v___x_1352_) == 0)
{
lean_object* v_a_1363_; lean_object* v___x_1365_; uint8_t v_isShared_1366_; uint8_t v_isSharedCheck_1370_; 
lean_dec(v_a_1350_);
v_a_1363_ = lean_ctor_get(v___x_1352_, 0);
v_isSharedCheck_1370_ = !lean_is_exclusive(v___x_1352_);
if (v_isSharedCheck_1370_ == 0)
{
v___x_1365_ = v___x_1352_;
v_isShared_1366_ = v_isSharedCheck_1370_;
goto v_resetjp_1364_;
}
else
{
lean_inc(v_a_1363_);
lean_dec(v___x_1352_);
v___x_1365_ = lean_box(0);
v_isShared_1366_ = v_isSharedCheck_1370_;
goto v_resetjp_1364_;
}
v_resetjp_1364_:
{
lean_object* v___x_1368_; 
if (v_isShared_1366_ == 0)
{
lean_ctor_set_tag(v___x_1365_, 0);
v___x_1368_ = v___x_1365_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v_a_1363_);
v___x_1368_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
return v___x_1368_;
}
}
}
else
{
lean_object* v_a_1371_; lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1379_; 
v_a_1371_ = lean_ctor_get(v___x_1352_, 0);
v_isSharedCheck_1379_ = !lean_is_exclusive(v___x_1352_);
if (v_isSharedCheck_1379_ == 0)
{
v___x_1373_ = v___x_1352_;
v_isShared_1374_ = v_isSharedCheck_1379_;
goto v_resetjp_1372_;
}
else
{
lean_inc(v_a_1371_);
lean_dec(v___x_1352_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1379_;
goto v_resetjp_1372_;
}
v_resetjp_1372_:
{
lean_object* v___x_1375_; lean_object* v___x_1377_; 
v___x_1375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1375_, 0, v_a_1350_);
lean_ctor_set(v___x_1375_, 1, v_a_1371_);
if (v_isShared_1374_ == 0)
{
lean_ctor_set(v___x_1373_, 0, v___x_1375_);
v___x_1377_ = v___x_1373_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v___x_1375_);
v___x_1377_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
return v___x_1377_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonChangeAnnotation_toJson(lean_object* v_x_1385_){
_start:
{
lean_object* v_label_1386_; uint8_t v_needsConfirmation_1387_; lean_object* v_description_x3f_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; 
v_label_1386_ = lean_ctor_get(v_x_1385_, 0);
lean_inc_ref(v_label_1386_);
v_needsConfirmation_1387_ = lean_ctor_get_uint8(v_x_1385_, sizeof(void*)*2);
v_description_x3f_1388_ = lean_ctor_get(v_x_1385_, 1);
lean_inc(v_description_x3f_1388_);
lean_dec_ref(v_x_1385_);
v___x_1389_ = ((lean_object*)(l_Lean_Lsp_instToJsonChangeAnnotation_toJson___closed__0));
v___x_1390_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1390_, 0, v_label_1386_);
v___x_1391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1391_, 0, v___x_1389_);
lean_ctor_set(v___x_1391_, 1, v___x_1390_);
v___x_1392_ = lean_box(0);
v___x_1393_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1393_, 0, v___x_1391_);
lean_ctor_set(v___x_1393_, 1, v___x_1392_);
v___x_1394_ = ((lean_object*)(l_Lean_Lsp_instToJsonChangeAnnotation_toJson___closed__1));
v___x_1395_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1395_, 0, v_needsConfirmation_1387_);
v___x_1396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1396_, 0, v___x_1394_);
lean_ctor_set(v___x_1396_, 1, v___x_1395_);
v___x_1397_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1397_, 0, v___x_1396_);
lean_ctor_set(v___x_1397_, 1, v___x_1392_);
v___x_1398_ = ((lean_object*)(l_Lean_Lsp_instToJsonChangeAnnotation_toJson___closed__2));
v___x_1399_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextEdit_toJson_spec__1(v___x_1398_, v_description_x3f_1388_);
v___x_1400_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1400_, 0, v___x_1399_);
lean_ctor_set(v___x_1400_, 1, v___x_1392_);
v___x_1401_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1401_, 0, v___x_1397_);
lean_ctor_set(v___x_1401_, 1, v___x_1400_);
v___x_1402_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1402_, 0, v___x_1393_);
lean_ctor_set(v___x_1402_, 1, v___x_1401_);
v___x_1403_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__2));
v___x_1404_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLocation_toJson_spec__0(v___x_1402_, v___x_1403_);
v___x_1405_ = l_Lean_Json_mkObj(v___x_1404_);
lean_dec(v___x_1404_);
return v___x_1405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonChangeAnnotation_fromJson_spec__0(lean_object* v_j_1408_, lean_object* v_k_1409_){
_start:
{
lean_object* v___x_1410_; lean_object* v___x_1411_; 
v___x_1410_ = l_Lean_Json_getObjValD(v_j_1408_, v_k_1409_);
v___x_1411_ = l_Lean_Json_getBool_x3f(v___x_1410_);
lean_dec(v___x_1410_);
return v___x_1411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonChangeAnnotation_fromJson_spec__0___boxed(lean_object* v_j_1412_, lean_object* v_k_1413_){
_start:
{
lean_object* v_res_1414_; 
v_res_1414_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonChangeAnnotation_fromJson_spec__0(v_j_1412_, v_k_1413_);
lean_dec_ref(v_k_1413_);
return v_res_1414_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__2(void){
_start:
{
uint8_t v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; 
v___x_1420_ = 1;
v___x_1421_ = ((lean_object*)(l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__1));
v___x_1422_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1421_, v___x_1420_);
return v___x_1422_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__3(void){
_start:
{
lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; 
v___x_1423_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__5));
v___x_1424_ = lean_obj_once(&l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__2, &l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__2);
v___x_1425_ = lean_string_append(v___x_1424_, v___x_1423_);
return v___x_1425_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__5(void){
_start:
{
uint8_t v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; 
v___x_1428_ = 1;
v___x_1429_ = ((lean_object*)(l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__4));
v___x_1430_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1429_, v___x_1428_);
return v___x_1430_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__6(void){
_start:
{
lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; 
v___x_1431_ = lean_obj_once(&l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__5, &l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__5);
v___x_1432_ = lean_obj_once(&l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__3, &l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__3);
v___x_1433_ = lean_string_append(v___x_1432_, v___x_1431_);
return v___x_1433_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__7(void){
_start:
{
lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; 
v___x_1434_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_1435_ = lean_obj_once(&l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__6, &l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__6);
v___x_1436_ = lean_string_append(v___x_1435_, v___x_1434_);
return v___x_1436_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__9(void){
_start:
{
uint8_t v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; 
v___x_1439_ = 1;
v___x_1440_ = ((lean_object*)(l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__8));
v___x_1441_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1440_, v___x_1439_);
return v___x_1441_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__10(void){
_start:
{
lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; 
v___x_1442_ = lean_obj_once(&l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__9, &l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__9);
v___x_1443_ = lean_obj_once(&l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__3, &l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__3);
v___x_1444_ = lean_string_append(v___x_1443_, v___x_1442_);
return v___x_1444_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__11(void){
_start:
{
lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; 
v___x_1445_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_1446_ = lean_obj_once(&l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__10, &l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__10);
v___x_1447_ = lean_string_append(v___x_1446_, v___x_1445_);
return v___x_1447_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__14(void){
_start:
{
uint8_t v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; 
v___x_1451_ = 1;
v___x_1452_ = ((lean_object*)(l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__13));
v___x_1453_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1452_, v___x_1451_);
return v___x_1453_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__15(void){
_start:
{
lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; 
v___x_1454_ = lean_obj_once(&l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__14, &l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__14_once, _init_l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__14);
v___x_1455_ = lean_obj_once(&l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__3, &l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__3);
v___x_1456_ = lean_string_append(v___x_1455_, v___x_1454_);
return v___x_1456_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__16(void){
_start:
{
lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; 
v___x_1457_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_1458_ = lean_obj_once(&l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__15, &l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__15_once, _init_l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__15);
v___x_1459_ = lean_string_append(v___x_1458_, v___x_1457_);
return v___x_1459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson(lean_object* v_json_1460_){
_start:
{
lean_object* v___x_1461_; lean_object* v___x_1462_; 
v___x_1461_ = ((lean_object*)(l_Lean_Lsp_instToJsonChangeAnnotation_toJson___closed__0));
lean_inc(v_json_1460_);
v___x_1462_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocation_fromJson_spec__0(v_json_1460_, v___x_1461_);
if (lean_obj_tag(v___x_1462_) == 0)
{
lean_object* v_a_1463_; lean_object* v___x_1465_; uint8_t v_isShared_1466_; uint8_t v_isSharedCheck_1472_; 
lean_dec(v_json_1460_);
v_a_1463_ = lean_ctor_get(v___x_1462_, 0);
v_isSharedCheck_1472_ = !lean_is_exclusive(v___x_1462_);
if (v_isSharedCheck_1472_ == 0)
{
v___x_1465_ = v___x_1462_;
v_isShared_1466_ = v_isSharedCheck_1472_;
goto v_resetjp_1464_;
}
else
{
lean_inc(v_a_1463_);
lean_dec(v___x_1462_);
v___x_1465_ = lean_box(0);
v_isShared_1466_ = v_isSharedCheck_1472_;
goto v_resetjp_1464_;
}
v_resetjp_1464_:
{
lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1470_; 
v___x_1467_ = lean_obj_once(&l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__7, &l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__7);
v___x_1468_ = lean_string_append(v___x_1467_, v_a_1463_);
lean_dec(v_a_1463_);
if (v_isShared_1466_ == 0)
{
lean_ctor_set(v___x_1465_, 0, v___x_1468_);
v___x_1470_ = v___x_1465_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1471_; 
v_reuseFailAlloc_1471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1471_, 0, v___x_1468_);
v___x_1470_ = v_reuseFailAlloc_1471_;
goto v_reusejp_1469_;
}
v_reusejp_1469_:
{
return v___x_1470_;
}
}
}
else
{
if (lean_obj_tag(v___x_1462_) == 0)
{
lean_object* v_a_1473_; lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1480_; 
lean_dec(v_json_1460_);
v_a_1473_ = lean_ctor_get(v___x_1462_, 0);
v_isSharedCheck_1480_ = !lean_is_exclusive(v___x_1462_);
if (v_isSharedCheck_1480_ == 0)
{
v___x_1475_ = v___x_1462_;
v_isShared_1476_ = v_isSharedCheck_1480_;
goto v_resetjp_1474_;
}
else
{
lean_inc(v_a_1473_);
lean_dec(v___x_1462_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1480_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
lean_object* v___x_1478_; 
if (v_isShared_1476_ == 0)
{
lean_ctor_set_tag(v___x_1475_, 0);
v___x_1478_ = v___x_1475_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v_a_1473_);
v___x_1478_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1477_;
}
v_reusejp_1477_:
{
return v___x_1478_;
}
}
}
else
{
lean_object* v_a_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; 
v_a_1481_ = lean_ctor_get(v___x_1462_, 0);
lean_inc(v_a_1481_);
lean_dec_ref_known(v___x_1462_, 1);
v___x_1482_ = ((lean_object*)(l_Lean_Lsp_instToJsonChangeAnnotation_toJson___closed__1));
lean_inc(v_json_1460_);
v___x_1483_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonChangeAnnotation_fromJson_spec__0(v_json_1460_, v___x_1482_);
if (lean_obj_tag(v___x_1483_) == 0)
{
lean_object* v_a_1484_; lean_object* v___x_1486_; uint8_t v_isShared_1487_; uint8_t v_isSharedCheck_1493_; 
lean_dec(v_a_1481_);
lean_dec(v_json_1460_);
v_a_1484_ = lean_ctor_get(v___x_1483_, 0);
v_isSharedCheck_1493_ = !lean_is_exclusive(v___x_1483_);
if (v_isSharedCheck_1493_ == 0)
{
v___x_1486_ = v___x_1483_;
v_isShared_1487_ = v_isSharedCheck_1493_;
goto v_resetjp_1485_;
}
else
{
lean_inc(v_a_1484_);
lean_dec(v___x_1483_);
v___x_1486_ = lean_box(0);
v_isShared_1487_ = v_isSharedCheck_1493_;
goto v_resetjp_1485_;
}
v_resetjp_1485_:
{
lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1491_; 
v___x_1488_ = lean_obj_once(&l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__11, &l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__11);
v___x_1489_ = lean_string_append(v___x_1488_, v_a_1484_);
lean_dec(v_a_1484_);
if (v_isShared_1487_ == 0)
{
lean_ctor_set(v___x_1486_, 0, v___x_1489_);
v___x_1491_ = v___x_1486_;
goto v_reusejp_1490_;
}
else
{
lean_object* v_reuseFailAlloc_1492_; 
v_reuseFailAlloc_1492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1492_, 0, v___x_1489_);
v___x_1491_ = v_reuseFailAlloc_1492_;
goto v_reusejp_1490_;
}
v_reusejp_1490_:
{
return v___x_1491_;
}
}
}
else
{
if (lean_obj_tag(v___x_1483_) == 0)
{
lean_object* v_a_1494_; lean_object* v___x_1496_; uint8_t v_isShared_1497_; uint8_t v_isSharedCheck_1501_; 
lean_dec(v_a_1481_);
lean_dec(v_json_1460_);
v_a_1494_ = lean_ctor_get(v___x_1483_, 0);
v_isSharedCheck_1501_ = !lean_is_exclusive(v___x_1483_);
if (v_isSharedCheck_1501_ == 0)
{
v___x_1496_ = v___x_1483_;
v_isShared_1497_ = v_isSharedCheck_1501_;
goto v_resetjp_1495_;
}
else
{
lean_inc(v_a_1494_);
lean_dec(v___x_1483_);
v___x_1496_ = lean_box(0);
v_isShared_1497_ = v_isSharedCheck_1501_;
goto v_resetjp_1495_;
}
v_resetjp_1495_:
{
lean_object* v___x_1499_; 
if (v_isShared_1497_ == 0)
{
lean_ctor_set_tag(v___x_1496_, 0);
v___x_1499_ = v___x_1496_;
goto v_reusejp_1498_;
}
else
{
lean_object* v_reuseFailAlloc_1500_; 
v_reuseFailAlloc_1500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1500_, 0, v_a_1494_);
v___x_1499_ = v_reuseFailAlloc_1500_;
goto v_reusejp_1498_;
}
v_reusejp_1498_:
{
return v___x_1499_;
}
}
}
else
{
lean_object* v_a_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; 
v_a_1502_ = lean_ctor_get(v___x_1483_, 0);
lean_inc(v_a_1502_);
lean_dec_ref_known(v___x_1483_, 1);
v___x_1503_ = ((lean_object*)(l_Lean_Lsp_instToJsonChangeAnnotation_toJson___closed__2));
v___x_1504_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextEdit_fromJson_spec__1(v_json_1460_, v___x_1503_);
if (lean_obj_tag(v___x_1504_) == 0)
{
lean_object* v_a_1505_; lean_object* v___x_1507_; uint8_t v_isShared_1508_; uint8_t v_isSharedCheck_1514_; 
lean_dec(v_a_1502_);
lean_dec(v_a_1481_);
v_a_1505_ = lean_ctor_get(v___x_1504_, 0);
v_isSharedCheck_1514_ = !lean_is_exclusive(v___x_1504_);
if (v_isSharedCheck_1514_ == 0)
{
v___x_1507_ = v___x_1504_;
v_isShared_1508_ = v_isSharedCheck_1514_;
goto v_resetjp_1506_;
}
else
{
lean_inc(v_a_1505_);
lean_dec(v___x_1504_);
v___x_1507_ = lean_box(0);
v_isShared_1508_ = v_isSharedCheck_1514_;
goto v_resetjp_1506_;
}
v_resetjp_1506_:
{
lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1512_; 
v___x_1509_ = lean_obj_once(&l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__16, &l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__16_once, _init_l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson___closed__16);
v___x_1510_ = lean_string_append(v___x_1509_, v_a_1505_);
lean_dec(v_a_1505_);
if (v_isShared_1508_ == 0)
{
lean_ctor_set(v___x_1507_, 0, v___x_1510_);
v___x_1512_ = v___x_1507_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1513_; 
v_reuseFailAlloc_1513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1513_, 0, v___x_1510_);
v___x_1512_ = v_reuseFailAlloc_1513_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
return v___x_1512_;
}
}
}
else
{
if (lean_obj_tag(v___x_1504_) == 0)
{
lean_object* v_a_1515_; lean_object* v___x_1517_; uint8_t v_isShared_1518_; uint8_t v_isSharedCheck_1522_; 
lean_dec(v_a_1502_);
lean_dec(v_a_1481_);
v_a_1515_ = lean_ctor_get(v___x_1504_, 0);
v_isSharedCheck_1522_ = !lean_is_exclusive(v___x_1504_);
if (v_isSharedCheck_1522_ == 0)
{
v___x_1517_ = v___x_1504_;
v_isShared_1518_ = v_isSharedCheck_1522_;
goto v_resetjp_1516_;
}
else
{
lean_inc(v_a_1515_);
lean_dec(v___x_1504_);
v___x_1517_ = lean_box(0);
v_isShared_1518_ = v_isSharedCheck_1522_;
goto v_resetjp_1516_;
}
v_resetjp_1516_:
{
lean_object* v___x_1520_; 
if (v_isShared_1518_ == 0)
{
lean_ctor_set_tag(v___x_1517_, 0);
v___x_1520_ = v___x_1517_;
goto v_reusejp_1519_;
}
else
{
lean_object* v_reuseFailAlloc_1521_; 
v_reuseFailAlloc_1521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1521_, 0, v_a_1515_);
v___x_1520_ = v_reuseFailAlloc_1521_;
goto v_reusejp_1519_;
}
v_reusejp_1519_:
{
return v___x_1520_;
}
}
}
else
{
lean_object* v_a_1523_; lean_object* v___x_1525_; uint8_t v_isShared_1526_; uint8_t v_isSharedCheck_1532_; 
v_a_1523_ = lean_ctor_get(v___x_1504_, 0);
v_isSharedCheck_1532_ = !lean_is_exclusive(v___x_1504_);
if (v_isSharedCheck_1532_ == 0)
{
v___x_1525_ = v___x_1504_;
v_isShared_1526_ = v_isSharedCheck_1532_;
goto v_resetjp_1524_;
}
else
{
lean_inc(v_a_1523_);
lean_dec(v___x_1504_);
v___x_1525_ = lean_box(0);
v_isShared_1526_ = v_isSharedCheck_1532_;
goto v_resetjp_1524_;
}
v_resetjp_1524_:
{
lean_object* v___x_1527_; uint8_t v___x_1528_; lean_object* v___x_1530_; 
v___x_1527_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1527_, 0, v_a_1481_);
lean_ctor_set(v___x_1527_, 1, v_a_1523_);
v___x_1528_ = lean_unbox(v_a_1502_);
lean_dec(v_a_1502_);
lean_ctor_set_uint8(v___x_1527_, sizeof(void*)*2, v___x_1528_);
if (v_isShared_1526_ == 0)
{
lean_ctor_set(v___x_1525_, 0, v___x_1527_);
v___x_1530_ = v___x_1525_;
goto v_reusejp_1529_;
}
else
{
lean_object* v_reuseFailAlloc_1531_; 
v_reuseFailAlloc_1531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1531_, 0, v___x_1527_);
v___x_1530_ = v_reuseFailAlloc_1531_;
goto v_reusejp_1529_;
}
v_reusejp_1529_:
{
return v___x_1530_;
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
LEAN_EXPORT lean_object* l_Lean_Lsp_CreateFile_instToJsonOptions_toJson(lean_object* v_x_1537_){
_start:
{
uint8_t v_overwrite_1538_; uint8_t v_ignoreIfExists_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; 
v_overwrite_1538_ = lean_ctor_get_uint8(v_x_1537_, 0);
v_ignoreIfExists_1539_ = lean_ctor_get_uint8(v_x_1537_, 1);
v___x_1540_ = ((lean_object*)(l_Lean_Lsp_CreateFile_instToJsonOptions_toJson___closed__0));
v___x_1541_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1541_, 0, v_overwrite_1538_);
v___x_1542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1542_, 0, v___x_1540_);
lean_ctor_set(v___x_1542_, 1, v___x_1541_);
v___x_1543_ = lean_box(0);
v___x_1544_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1544_, 0, v___x_1542_);
lean_ctor_set(v___x_1544_, 1, v___x_1543_);
v___x_1545_ = ((lean_object*)(l_Lean_Lsp_CreateFile_instToJsonOptions_toJson___closed__1));
v___x_1546_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1546_, 0, v_ignoreIfExists_1539_);
v___x_1547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1547_, 0, v___x_1545_);
lean_ctor_set(v___x_1547_, 1, v___x_1546_);
v___x_1548_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1548_, 0, v___x_1547_);
lean_ctor_set(v___x_1548_, 1, v___x_1543_);
v___x_1549_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1549_, 0, v___x_1548_);
lean_ctor_set(v___x_1549_, 1, v___x_1543_);
v___x_1550_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1550_, 0, v___x_1544_);
lean_ctor_set(v___x_1550_, 1, v___x_1549_);
v___x_1551_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__2));
v___x_1552_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLocation_toJson_spec__0(v___x_1550_, v___x_1551_);
v___x_1553_ = l_Lean_Json_mkObj(v___x_1552_);
lean_dec(v___x_1552_);
return v___x_1553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_CreateFile_instToJsonOptions_toJson___boxed(lean_object* v_x_1554_){
_start:
{
lean_object* v_res_1555_; 
v_res_1555_ = l_Lean_Lsp_CreateFile_instToJsonOptions_toJson(v_x_1554_);
lean_dec_ref(v_x_1554_);
return v_res_1555_;
}
}
static lean_object* _init_l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__3(void){
_start:
{
uint8_t v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; 
v___x_1565_ = 1;
v___x_1566_ = ((lean_object*)(l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__2));
v___x_1567_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1566_, v___x_1565_);
return v___x_1567_;
}
}
static lean_object* _init_l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__4(void){
_start:
{
lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; 
v___x_1568_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__5));
v___x_1569_ = lean_obj_once(&l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__3, &l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__3_once, _init_l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__3);
v___x_1570_ = lean_string_append(v___x_1569_, v___x_1568_);
return v___x_1570_;
}
}
static lean_object* _init_l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__6(void){
_start:
{
uint8_t v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; 
v___x_1573_ = 1;
v___x_1574_ = ((lean_object*)(l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__5));
v___x_1575_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1574_, v___x_1573_);
return v___x_1575_;
}
}
static lean_object* _init_l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__7(void){
_start:
{
lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; 
v___x_1576_ = lean_obj_once(&l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__6, &l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__6_once, _init_l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__6);
v___x_1577_ = lean_obj_once(&l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__4, &l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__4_once, _init_l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__4);
v___x_1578_ = lean_string_append(v___x_1577_, v___x_1576_);
return v___x_1578_;
}
}
static lean_object* _init_l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__8(void){
_start:
{
lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; 
v___x_1579_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_1580_ = lean_obj_once(&l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__7, &l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__7_once, _init_l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__7);
v___x_1581_ = lean_string_append(v___x_1580_, v___x_1579_);
return v___x_1581_;
}
}
static lean_object* _init_l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__10(void){
_start:
{
uint8_t v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; 
v___x_1584_ = 1;
v___x_1585_ = ((lean_object*)(l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__9));
v___x_1586_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1585_, v___x_1584_);
return v___x_1586_;
}
}
static lean_object* _init_l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__11(void){
_start:
{
lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; 
v___x_1587_ = lean_obj_once(&l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__10, &l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__10_once, _init_l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__10);
v___x_1588_ = lean_obj_once(&l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__4, &l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__4_once, _init_l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__4);
v___x_1589_ = lean_string_append(v___x_1588_, v___x_1587_);
return v___x_1589_;
}
}
static lean_object* _init_l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__12(void){
_start:
{
lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; 
v___x_1590_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_1591_ = lean_obj_once(&l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__11, &l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__11_once, _init_l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__11);
v___x_1592_ = lean_string_append(v___x_1591_, v___x_1590_);
return v___x_1592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson(lean_object* v_json_1593_){
_start:
{
lean_object* v___x_1594_; lean_object* v___x_1595_; 
v___x_1594_ = ((lean_object*)(l_Lean_Lsp_CreateFile_instToJsonOptions_toJson___closed__0));
lean_inc(v_json_1593_);
v___x_1595_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonChangeAnnotation_fromJson_spec__0(v_json_1593_, v___x_1594_);
if (lean_obj_tag(v___x_1595_) == 0)
{
lean_object* v_a_1596_; lean_object* v___x_1598_; uint8_t v_isShared_1599_; uint8_t v_isSharedCheck_1605_; 
lean_dec(v_json_1593_);
v_a_1596_ = lean_ctor_get(v___x_1595_, 0);
v_isSharedCheck_1605_ = !lean_is_exclusive(v___x_1595_);
if (v_isSharedCheck_1605_ == 0)
{
v___x_1598_ = v___x_1595_;
v_isShared_1599_ = v_isSharedCheck_1605_;
goto v_resetjp_1597_;
}
else
{
lean_inc(v_a_1596_);
lean_dec(v___x_1595_);
v___x_1598_ = lean_box(0);
v_isShared_1599_ = v_isSharedCheck_1605_;
goto v_resetjp_1597_;
}
v_resetjp_1597_:
{
lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1603_; 
v___x_1600_ = lean_obj_once(&l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__8, &l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__8_once, _init_l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__8);
v___x_1601_ = lean_string_append(v___x_1600_, v_a_1596_);
lean_dec(v_a_1596_);
if (v_isShared_1599_ == 0)
{
lean_ctor_set(v___x_1598_, 0, v___x_1601_);
v___x_1603_ = v___x_1598_;
goto v_reusejp_1602_;
}
else
{
lean_object* v_reuseFailAlloc_1604_; 
v_reuseFailAlloc_1604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1604_, 0, v___x_1601_);
v___x_1603_ = v_reuseFailAlloc_1604_;
goto v_reusejp_1602_;
}
v_reusejp_1602_:
{
return v___x_1603_;
}
}
}
else
{
if (lean_obj_tag(v___x_1595_) == 0)
{
lean_object* v_a_1606_; lean_object* v___x_1608_; uint8_t v_isShared_1609_; uint8_t v_isSharedCheck_1613_; 
lean_dec(v_json_1593_);
v_a_1606_ = lean_ctor_get(v___x_1595_, 0);
v_isSharedCheck_1613_ = !lean_is_exclusive(v___x_1595_);
if (v_isSharedCheck_1613_ == 0)
{
v___x_1608_ = v___x_1595_;
v_isShared_1609_ = v_isSharedCheck_1613_;
goto v_resetjp_1607_;
}
else
{
lean_inc(v_a_1606_);
lean_dec(v___x_1595_);
v___x_1608_ = lean_box(0);
v_isShared_1609_ = v_isSharedCheck_1613_;
goto v_resetjp_1607_;
}
v_resetjp_1607_:
{
lean_object* v___x_1611_; 
if (v_isShared_1609_ == 0)
{
lean_ctor_set_tag(v___x_1608_, 0);
v___x_1611_ = v___x_1608_;
goto v_reusejp_1610_;
}
else
{
lean_object* v_reuseFailAlloc_1612_; 
v_reuseFailAlloc_1612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1612_, 0, v_a_1606_);
v___x_1611_ = v_reuseFailAlloc_1612_;
goto v_reusejp_1610_;
}
v_reusejp_1610_:
{
return v___x_1611_;
}
}
}
else
{
lean_object* v_a_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; 
v_a_1614_ = lean_ctor_get(v___x_1595_, 0);
lean_inc(v_a_1614_);
lean_dec_ref_known(v___x_1595_, 1);
v___x_1615_ = ((lean_object*)(l_Lean_Lsp_CreateFile_instToJsonOptions_toJson___closed__1));
v___x_1616_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonChangeAnnotation_fromJson_spec__0(v_json_1593_, v___x_1615_);
if (lean_obj_tag(v___x_1616_) == 0)
{
lean_object* v_a_1617_; lean_object* v___x_1619_; uint8_t v_isShared_1620_; uint8_t v_isSharedCheck_1626_; 
lean_dec(v_a_1614_);
v_a_1617_ = lean_ctor_get(v___x_1616_, 0);
v_isSharedCheck_1626_ = !lean_is_exclusive(v___x_1616_);
if (v_isSharedCheck_1626_ == 0)
{
v___x_1619_ = v___x_1616_;
v_isShared_1620_ = v_isSharedCheck_1626_;
goto v_resetjp_1618_;
}
else
{
lean_inc(v_a_1617_);
lean_dec(v___x_1616_);
v___x_1619_ = lean_box(0);
v_isShared_1620_ = v_isSharedCheck_1626_;
goto v_resetjp_1618_;
}
v_resetjp_1618_:
{
lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1624_; 
v___x_1621_ = lean_obj_once(&l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__12, &l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__12_once, _init_l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson___closed__12);
v___x_1622_ = lean_string_append(v___x_1621_, v_a_1617_);
lean_dec(v_a_1617_);
if (v_isShared_1620_ == 0)
{
lean_ctor_set(v___x_1619_, 0, v___x_1622_);
v___x_1624_ = v___x_1619_;
goto v_reusejp_1623_;
}
else
{
lean_object* v_reuseFailAlloc_1625_; 
v_reuseFailAlloc_1625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1625_, 0, v___x_1622_);
v___x_1624_ = v_reuseFailAlloc_1625_;
goto v_reusejp_1623_;
}
v_reusejp_1623_:
{
return v___x_1624_;
}
}
}
else
{
if (lean_obj_tag(v___x_1616_) == 0)
{
lean_object* v_a_1627_; lean_object* v___x_1629_; uint8_t v_isShared_1630_; uint8_t v_isSharedCheck_1634_; 
lean_dec(v_a_1614_);
v_a_1627_ = lean_ctor_get(v___x_1616_, 0);
v_isSharedCheck_1634_ = !lean_is_exclusive(v___x_1616_);
if (v_isSharedCheck_1634_ == 0)
{
v___x_1629_ = v___x_1616_;
v_isShared_1630_ = v_isSharedCheck_1634_;
goto v_resetjp_1628_;
}
else
{
lean_inc(v_a_1627_);
lean_dec(v___x_1616_);
v___x_1629_ = lean_box(0);
v_isShared_1630_ = v_isSharedCheck_1634_;
goto v_resetjp_1628_;
}
v_resetjp_1628_:
{
lean_object* v___x_1632_; 
if (v_isShared_1630_ == 0)
{
lean_ctor_set_tag(v___x_1629_, 0);
v___x_1632_ = v___x_1629_;
goto v_reusejp_1631_;
}
else
{
lean_object* v_reuseFailAlloc_1633_; 
v_reuseFailAlloc_1633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1633_, 0, v_a_1627_);
v___x_1632_ = v_reuseFailAlloc_1633_;
goto v_reusejp_1631_;
}
v_reusejp_1631_:
{
return v___x_1632_;
}
}
}
else
{
lean_object* v_a_1635_; lean_object* v___x_1637_; uint8_t v_isShared_1638_; uint8_t v_isSharedCheck_1645_; 
v_a_1635_ = lean_ctor_get(v___x_1616_, 0);
v_isSharedCheck_1645_ = !lean_is_exclusive(v___x_1616_);
if (v_isSharedCheck_1645_ == 0)
{
v___x_1637_ = v___x_1616_;
v_isShared_1638_ = v_isSharedCheck_1645_;
goto v_resetjp_1636_;
}
else
{
lean_inc(v_a_1635_);
lean_dec(v___x_1616_);
v___x_1637_ = lean_box(0);
v_isShared_1638_ = v_isSharedCheck_1645_;
goto v_resetjp_1636_;
}
v_resetjp_1636_:
{
lean_object* v___x_1639_; uint8_t v___x_1640_; uint8_t v___x_1641_; lean_object* v___x_1643_; 
v___x_1639_ = lean_alloc_ctor(0, 0, 2);
v___x_1640_ = lean_unbox(v_a_1614_);
lean_dec(v_a_1614_);
lean_ctor_set_uint8(v___x_1639_, 0, v___x_1640_);
v___x_1641_ = lean_unbox(v_a_1635_);
lean_dec(v_a_1635_);
lean_ctor_set_uint8(v___x_1639_, 1, v___x_1641_);
if (v_isShared_1638_ == 0)
{
lean_ctor_set(v___x_1637_, 0, v___x_1639_);
v___x_1643_ = v___x_1637_;
goto v_reusejp_1642_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v___x_1639_);
v___x_1643_ = v_reuseFailAlloc_1644_;
goto v_reusejp_1642_;
}
v_reusejp_1642_:
{
return v___x_1643_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DeleteFile_instToJsonOptions_toJson(lean_object* v_x_1650_){
_start:
{
uint8_t v_recursive_1651_; uint8_t v_ignoreIfNotExists_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; 
v_recursive_1651_ = lean_ctor_get_uint8(v_x_1650_, 0);
v_ignoreIfNotExists_1652_ = lean_ctor_get_uint8(v_x_1650_, 1);
v___x_1653_ = ((lean_object*)(l_Lean_Lsp_DeleteFile_instToJsonOptions_toJson___closed__0));
v___x_1654_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1654_, 0, v_recursive_1651_);
v___x_1655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1655_, 0, v___x_1653_);
lean_ctor_set(v___x_1655_, 1, v___x_1654_);
v___x_1656_ = lean_box(0);
v___x_1657_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1657_, 0, v___x_1655_);
lean_ctor_set(v___x_1657_, 1, v___x_1656_);
v___x_1658_ = ((lean_object*)(l_Lean_Lsp_DeleteFile_instToJsonOptions_toJson___closed__1));
v___x_1659_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1659_, 0, v_ignoreIfNotExists_1652_);
v___x_1660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1660_, 0, v___x_1658_);
lean_ctor_set(v___x_1660_, 1, v___x_1659_);
v___x_1661_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1661_, 0, v___x_1660_);
lean_ctor_set(v___x_1661_, 1, v___x_1656_);
v___x_1662_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1662_, 0, v___x_1661_);
lean_ctor_set(v___x_1662_, 1, v___x_1656_);
v___x_1663_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1663_, 0, v___x_1657_);
lean_ctor_set(v___x_1663_, 1, v___x_1662_);
v___x_1664_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__2));
v___x_1665_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLocation_toJson_spec__0(v___x_1663_, v___x_1664_);
v___x_1666_ = l_Lean_Json_mkObj(v___x_1665_);
lean_dec(v___x_1665_);
return v___x_1666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DeleteFile_instToJsonOptions_toJson___boxed(lean_object* v_x_1667_){
_start:
{
lean_object* v_res_1668_; 
v_res_1668_ = l_Lean_Lsp_DeleteFile_instToJsonOptions_toJson(v_x_1667_);
lean_dec_ref(v_x_1667_);
return v_res_1668_;
}
}
static lean_object* _init_l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__2(void){
_start:
{
uint8_t v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; 
v___x_1677_ = 1;
v___x_1678_ = ((lean_object*)(l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__1));
v___x_1679_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1678_, v___x_1677_);
return v___x_1679_;
}
}
static lean_object* _init_l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__3(void){
_start:
{
lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; 
v___x_1680_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__5));
v___x_1681_ = lean_obj_once(&l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__2, &l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__2_once, _init_l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__2);
v___x_1682_ = lean_string_append(v___x_1681_, v___x_1680_);
return v___x_1682_;
}
}
static lean_object* _init_l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__5(void){
_start:
{
uint8_t v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; 
v___x_1685_ = 1;
v___x_1686_ = ((lean_object*)(l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__4));
v___x_1687_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1686_, v___x_1685_);
return v___x_1687_;
}
}
static lean_object* _init_l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__6(void){
_start:
{
lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; 
v___x_1688_ = lean_obj_once(&l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__5, &l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__5_once, _init_l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__5);
v___x_1689_ = lean_obj_once(&l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__3, &l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__3_once, _init_l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__3);
v___x_1690_ = lean_string_append(v___x_1689_, v___x_1688_);
return v___x_1690_;
}
}
static lean_object* _init_l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__7(void){
_start:
{
lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; 
v___x_1691_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_1692_ = lean_obj_once(&l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__6, &l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__6_once, _init_l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__6);
v___x_1693_ = lean_string_append(v___x_1692_, v___x_1691_);
return v___x_1693_;
}
}
static lean_object* _init_l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__9(void){
_start:
{
uint8_t v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; 
v___x_1696_ = 1;
v___x_1697_ = ((lean_object*)(l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__8));
v___x_1698_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1697_, v___x_1696_);
return v___x_1698_;
}
}
static lean_object* _init_l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__10(void){
_start:
{
lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; 
v___x_1699_ = lean_obj_once(&l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__9, &l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__9_once, _init_l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__9);
v___x_1700_ = lean_obj_once(&l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__3, &l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__3_once, _init_l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__3);
v___x_1701_ = lean_string_append(v___x_1700_, v___x_1699_);
return v___x_1701_;
}
}
static lean_object* _init_l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__11(void){
_start:
{
lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; 
v___x_1702_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_1703_ = lean_obj_once(&l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__10, &l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__10_once, _init_l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__10);
v___x_1704_ = lean_string_append(v___x_1703_, v___x_1702_);
return v___x_1704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson(lean_object* v_json_1705_){
_start:
{
lean_object* v___x_1706_; lean_object* v___x_1707_; 
v___x_1706_ = ((lean_object*)(l_Lean_Lsp_DeleteFile_instToJsonOptions_toJson___closed__0));
lean_inc(v_json_1705_);
v___x_1707_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonChangeAnnotation_fromJson_spec__0(v_json_1705_, v___x_1706_);
if (lean_obj_tag(v___x_1707_) == 0)
{
lean_object* v_a_1708_; lean_object* v___x_1710_; uint8_t v_isShared_1711_; uint8_t v_isSharedCheck_1717_; 
lean_dec(v_json_1705_);
v_a_1708_ = lean_ctor_get(v___x_1707_, 0);
v_isSharedCheck_1717_ = !lean_is_exclusive(v___x_1707_);
if (v_isSharedCheck_1717_ == 0)
{
v___x_1710_ = v___x_1707_;
v_isShared_1711_ = v_isSharedCheck_1717_;
goto v_resetjp_1709_;
}
else
{
lean_inc(v_a_1708_);
lean_dec(v___x_1707_);
v___x_1710_ = lean_box(0);
v_isShared_1711_ = v_isSharedCheck_1717_;
goto v_resetjp_1709_;
}
v_resetjp_1709_:
{
lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1715_; 
v___x_1712_ = lean_obj_once(&l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__7, &l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__7_once, _init_l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__7);
v___x_1713_ = lean_string_append(v___x_1712_, v_a_1708_);
lean_dec(v_a_1708_);
if (v_isShared_1711_ == 0)
{
lean_ctor_set(v___x_1710_, 0, v___x_1713_);
v___x_1715_ = v___x_1710_;
goto v_reusejp_1714_;
}
else
{
lean_object* v_reuseFailAlloc_1716_; 
v_reuseFailAlloc_1716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1716_, 0, v___x_1713_);
v___x_1715_ = v_reuseFailAlloc_1716_;
goto v_reusejp_1714_;
}
v_reusejp_1714_:
{
return v___x_1715_;
}
}
}
else
{
if (lean_obj_tag(v___x_1707_) == 0)
{
lean_object* v_a_1718_; lean_object* v___x_1720_; uint8_t v_isShared_1721_; uint8_t v_isSharedCheck_1725_; 
lean_dec(v_json_1705_);
v_a_1718_ = lean_ctor_get(v___x_1707_, 0);
v_isSharedCheck_1725_ = !lean_is_exclusive(v___x_1707_);
if (v_isSharedCheck_1725_ == 0)
{
v___x_1720_ = v___x_1707_;
v_isShared_1721_ = v_isSharedCheck_1725_;
goto v_resetjp_1719_;
}
else
{
lean_inc(v_a_1718_);
lean_dec(v___x_1707_);
v___x_1720_ = lean_box(0);
v_isShared_1721_ = v_isSharedCheck_1725_;
goto v_resetjp_1719_;
}
v_resetjp_1719_:
{
lean_object* v___x_1723_; 
if (v_isShared_1721_ == 0)
{
lean_ctor_set_tag(v___x_1720_, 0);
v___x_1723_ = v___x_1720_;
goto v_reusejp_1722_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v_a_1718_);
v___x_1723_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1722_;
}
v_reusejp_1722_:
{
return v___x_1723_;
}
}
}
else
{
lean_object* v_a_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; 
v_a_1726_ = lean_ctor_get(v___x_1707_, 0);
lean_inc(v_a_1726_);
lean_dec_ref_known(v___x_1707_, 1);
v___x_1727_ = ((lean_object*)(l_Lean_Lsp_DeleteFile_instToJsonOptions_toJson___closed__1));
v___x_1728_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonChangeAnnotation_fromJson_spec__0(v_json_1705_, v___x_1727_);
if (lean_obj_tag(v___x_1728_) == 0)
{
lean_object* v_a_1729_; lean_object* v___x_1731_; uint8_t v_isShared_1732_; uint8_t v_isSharedCheck_1738_; 
lean_dec(v_a_1726_);
v_a_1729_ = lean_ctor_get(v___x_1728_, 0);
v_isSharedCheck_1738_ = !lean_is_exclusive(v___x_1728_);
if (v_isSharedCheck_1738_ == 0)
{
v___x_1731_ = v___x_1728_;
v_isShared_1732_ = v_isSharedCheck_1738_;
goto v_resetjp_1730_;
}
else
{
lean_inc(v_a_1729_);
lean_dec(v___x_1728_);
v___x_1731_ = lean_box(0);
v_isShared_1732_ = v_isSharedCheck_1738_;
goto v_resetjp_1730_;
}
v_resetjp_1730_:
{
lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1736_; 
v___x_1733_ = lean_obj_once(&l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__11, &l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__11_once, _init_l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson___closed__11);
v___x_1734_ = lean_string_append(v___x_1733_, v_a_1729_);
lean_dec(v_a_1729_);
if (v_isShared_1732_ == 0)
{
lean_ctor_set(v___x_1731_, 0, v___x_1734_);
v___x_1736_ = v___x_1731_;
goto v_reusejp_1735_;
}
else
{
lean_object* v_reuseFailAlloc_1737_; 
v_reuseFailAlloc_1737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1737_, 0, v___x_1734_);
v___x_1736_ = v_reuseFailAlloc_1737_;
goto v_reusejp_1735_;
}
v_reusejp_1735_:
{
return v___x_1736_;
}
}
}
else
{
if (lean_obj_tag(v___x_1728_) == 0)
{
lean_object* v_a_1739_; lean_object* v___x_1741_; uint8_t v_isShared_1742_; uint8_t v_isSharedCheck_1746_; 
lean_dec(v_a_1726_);
v_a_1739_ = lean_ctor_get(v___x_1728_, 0);
v_isSharedCheck_1746_ = !lean_is_exclusive(v___x_1728_);
if (v_isSharedCheck_1746_ == 0)
{
v___x_1741_ = v___x_1728_;
v_isShared_1742_ = v_isSharedCheck_1746_;
goto v_resetjp_1740_;
}
else
{
lean_inc(v_a_1739_);
lean_dec(v___x_1728_);
v___x_1741_ = lean_box(0);
v_isShared_1742_ = v_isSharedCheck_1746_;
goto v_resetjp_1740_;
}
v_resetjp_1740_:
{
lean_object* v___x_1744_; 
if (v_isShared_1742_ == 0)
{
lean_ctor_set_tag(v___x_1741_, 0);
v___x_1744_ = v___x_1741_;
goto v_reusejp_1743_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v_a_1739_);
v___x_1744_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1743_;
}
v_reusejp_1743_:
{
return v___x_1744_;
}
}
}
else
{
lean_object* v_a_1747_; lean_object* v___x_1749_; uint8_t v_isShared_1750_; uint8_t v_isSharedCheck_1757_; 
v_a_1747_ = lean_ctor_get(v___x_1728_, 0);
v_isSharedCheck_1757_ = !lean_is_exclusive(v___x_1728_);
if (v_isSharedCheck_1757_ == 0)
{
v___x_1749_ = v___x_1728_;
v_isShared_1750_ = v_isSharedCheck_1757_;
goto v_resetjp_1748_;
}
else
{
lean_inc(v_a_1747_);
lean_dec(v___x_1728_);
v___x_1749_ = lean_box(0);
v_isShared_1750_ = v_isSharedCheck_1757_;
goto v_resetjp_1748_;
}
v_resetjp_1748_:
{
lean_object* v___x_1751_; uint8_t v___x_1752_; uint8_t v___x_1753_; lean_object* v___x_1755_; 
v___x_1751_ = lean_alloc_ctor(0, 0, 2);
v___x_1752_ = lean_unbox(v_a_1726_);
lean_dec(v_a_1726_);
lean_ctor_set_uint8(v___x_1751_, 0, v___x_1752_);
v___x_1753_ = lean_unbox(v_a_1747_);
lean_dec(v_a_1747_);
lean_ctor_set_uint8(v___x_1751_, 1, v___x_1753_);
if (v_isShared_1750_ == 0)
{
lean_ctor_set(v___x_1749_, 0, v___x_1751_);
v___x_1755_ = v___x_1749_;
goto v_reusejp_1754_;
}
else
{
lean_object* v_reuseFailAlloc_1756_; 
v_reuseFailAlloc_1756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1756_, 0, v___x_1751_);
v___x_1755_ = v_reuseFailAlloc_1756_;
goto v_reusejp_1754_;
}
v_reusejp_1754_:
{
return v___x_1755_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonCreateFile_toJson_spec__0(lean_object* v_k_1760_, lean_object* v_x_1761_){
_start:
{
if (lean_obj_tag(v_x_1761_) == 0)
{
lean_object* v___x_1762_; 
lean_dec_ref(v_k_1760_);
v___x_1762_ = lean_box(0);
return v___x_1762_;
}
else
{
lean_object* v_val_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; 
v_val_1763_ = lean_ctor_get(v_x_1761_, 0);
v___x_1764_ = l_Lean_Lsp_CreateFile_instToJsonOptions_toJson(v_val_1763_);
v___x_1765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1765_, 0, v_k_1760_);
lean_ctor_set(v___x_1765_, 1, v___x_1764_);
v___x_1766_ = lean_box(0);
v___x_1767_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1767_, 0, v___x_1765_);
lean_ctor_set(v___x_1767_, 1, v___x_1766_);
return v___x_1767_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonCreateFile_toJson_spec__0___boxed(lean_object* v_k_1768_, lean_object* v_x_1769_){
_start:
{
lean_object* v_res_1770_; 
v_res_1770_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonCreateFile_toJson_spec__0(v_k_1768_, v_x_1769_);
lean_dec(v_x_1769_);
return v_res_1770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonCreateFile_toJson(lean_object* v_x_1772_){
_start:
{
lean_object* v_uri_1773_; lean_object* v_options_x3f_1774_; lean_object* v_annotationId_x3f_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; 
v_uri_1773_ = lean_ctor_get(v_x_1772_, 0);
lean_inc_ref(v_uri_1773_);
v_options_x3f_1774_ = lean_ctor_get(v_x_1772_, 1);
lean_inc(v_options_x3f_1774_);
v_annotationId_x3f_1775_ = lean_ctor_get(v_x_1772_, 2);
lean_inc(v_annotationId_x3f_1775_);
lean_dec_ref(v_x_1772_);
v___x_1776_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__0));
v___x_1777_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1777_, 0, v_uri_1773_);
v___x_1778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1778_, 0, v___x_1776_);
lean_ctor_set(v___x_1778_, 1, v___x_1777_);
v___x_1779_ = lean_box(0);
v___x_1780_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1780_, 0, v___x_1778_);
lean_ctor_set(v___x_1780_, 1, v___x_1779_);
v___x_1781_ = ((lean_object*)(l_Lean_Lsp_instToJsonCreateFile_toJson___closed__0));
v___x_1782_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonCreateFile_toJson_spec__0(v___x_1781_, v_options_x3f_1774_);
lean_dec(v_options_x3f_1774_);
v___x_1783_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextEdit_toJson___closed__2));
v___x_1784_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextEdit_toJson_spec__1(v___x_1783_, v_annotationId_x3f_1775_);
v___x_1785_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1785_, 0, v___x_1784_);
lean_ctor_set(v___x_1785_, 1, v___x_1779_);
v___x_1786_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1786_, 0, v___x_1782_);
lean_ctor_set(v___x_1786_, 1, v___x_1785_);
v___x_1787_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1787_, 0, v___x_1780_);
lean_ctor_set(v___x_1787_, 1, v___x_1786_);
v___x_1788_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__2));
v___x_1789_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLocation_toJson_spec__0(v___x_1787_, v___x_1788_);
v___x_1790_ = l_Lean_Json_mkObj(v___x_1789_);
lean_dec(v___x_1789_);
return v___x_1790_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCreateFile_fromJson_spec__0_spec__0(lean_object* v_x_1795_){
_start:
{
if (lean_obj_tag(v_x_1795_) == 0)
{
lean_object* v___x_1796_; 
v___x_1796_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCreateFile_fromJson_spec__0_spec__0___closed__0));
return v___x_1796_;
}
else
{
lean_object* v___x_1797_; 
v___x_1797_ = l_Lean_Lsp_CreateFile_instFromJsonOptions_fromJson(v_x_1795_);
if (lean_obj_tag(v___x_1797_) == 0)
{
lean_object* v_a_1798_; lean_object* v___x_1800_; uint8_t v_isShared_1801_; uint8_t v_isSharedCheck_1805_; 
v_a_1798_ = lean_ctor_get(v___x_1797_, 0);
v_isSharedCheck_1805_ = !lean_is_exclusive(v___x_1797_);
if (v_isSharedCheck_1805_ == 0)
{
v___x_1800_ = v___x_1797_;
v_isShared_1801_ = v_isSharedCheck_1805_;
goto v_resetjp_1799_;
}
else
{
lean_inc(v_a_1798_);
lean_dec(v___x_1797_);
v___x_1800_ = lean_box(0);
v_isShared_1801_ = v_isSharedCheck_1805_;
goto v_resetjp_1799_;
}
v_resetjp_1799_:
{
lean_object* v___x_1803_; 
if (v_isShared_1801_ == 0)
{
v___x_1803_ = v___x_1800_;
goto v_reusejp_1802_;
}
else
{
lean_object* v_reuseFailAlloc_1804_; 
v_reuseFailAlloc_1804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1804_, 0, v_a_1798_);
v___x_1803_ = v_reuseFailAlloc_1804_;
goto v_reusejp_1802_;
}
v_reusejp_1802_:
{
return v___x_1803_;
}
}
}
else
{
lean_object* v_a_1806_; lean_object* v___x_1808_; uint8_t v_isShared_1809_; uint8_t v_isSharedCheck_1814_; 
v_a_1806_ = lean_ctor_get(v___x_1797_, 0);
v_isSharedCheck_1814_ = !lean_is_exclusive(v___x_1797_);
if (v_isSharedCheck_1814_ == 0)
{
v___x_1808_ = v___x_1797_;
v_isShared_1809_ = v_isSharedCheck_1814_;
goto v_resetjp_1807_;
}
else
{
lean_inc(v_a_1806_);
lean_dec(v___x_1797_);
v___x_1808_ = lean_box(0);
v_isShared_1809_ = v_isSharedCheck_1814_;
goto v_resetjp_1807_;
}
v_resetjp_1807_:
{
lean_object* v___x_1810_; lean_object* v___x_1812_; 
v___x_1810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1810_, 0, v_a_1806_);
if (v_isShared_1809_ == 0)
{
lean_ctor_set(v___x_1808_, 0, v___x_1810_);
v___x_1812_ = v___x_1808_;
goto v_reusejp_1811_;
}
else
{
lean_object* v_reuseFailAlloc_1813_; 
v_reuseFailAlloc_1813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1813_, 0, v___x_1810_);
v___x_1812_ = v_reuseFailAlloc_1813_;
goto v_reusejp_1811_;
}
v_reusejp_1811_:
{
return v___x_1812_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCreateFile_fromJson_spec__0(lean_object* v_j_1815_, lean_object* v_k_1816_){
_start:
{
lean_object* v___x_1817_; lean_object* v___x_1818_; 
v___x_1817_ = l_Lean_Json_getObjValD(v_j_1815_, v_k_1816_);
v___x_1818_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCreateFile_fromJson_spec__0_spec__0(v___x_1817_);
return v___x_1818_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCreateFile_fromJson_spec__0___boxed(lean_object* v_j_1819_, lean_object* v_k_1820_){
_start:
{
lean_object* v_res_1821_; 
v_res_1821_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCreateFile_fromJson_spec__0(v_j_1819_, v_k_1820_);
lean_dec_ref(v_k_1820_);
return v_res_1821_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__1(void){
_start:
{
uint8_t v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; 
v___x_1826_ = 1;
v___x_1827_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__0));
v___x_1828_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1827_, v___x_1826_);
return v___x_1828_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__2(void){
_start:
{
lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; 
v___x_1829_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__5));
v___x_1830_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__1, &l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__1_once, _init_l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__1);
v___x_1831_ = lean_string_append(v___x_1830_, v___x_1829_);
return v___x_1831_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__3(void){
_start:
{
lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; 
v___x_1832_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLocation_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLocation_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLocation_fromJson___closed__8);
v___x_1833_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__2, &l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__2);
v___x_1834_ = lean_string_append(v___x_1833_, v___x_1832_);
return v___x_1834_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__4(void){
_start:
{
lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; 
v___x_1835_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_1836_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__3, &l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__3);
v___x_1837_ = lean_string_append(v___x_1836_, v___x_1835_);
return v___x_1837_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__7(void){
_start:
{
uint8_t v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; 
v___x_1841_ = 1;
v___x_1842_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__6));
v___x_1843_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1842_, v___x_1841_);
return v___x_1843_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__8(void){
_start:
{
lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; 
v___x_1844_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__7, &l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__7);
v___x_1845_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__2, &l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__2);
v___x_1846_ = lean_string_append(v___x_1845_, v___x_1844_);
return v___x_1846_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__9(void){
_start:
{
lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; 
v___x_1847_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_1848_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__8, &l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__8);
v___x_1849_ = lean_string_append(v___x_1848_, v___x_1847_);
return v___x_1849_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__10(void){
_start:
{
lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; 
v___x_1850_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__17, &l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__17_once, _init_l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__17);
v___x_1851_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__2, &l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__2);
v___x_1852_ = lean_string_append(v___x_1851_, v___x_1850_);
return v___x_1852_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__11(void){
_start:
{
lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; 
v___x_1853_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_1854_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__10, &l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__10);
v___x_1855_ = lean_string_append(v___x_1854_, v___x_1853_);
return v___x_1855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonCreateFile_fromJson(lean_object* v_json_1856_){
_start:
{
lean_object* v___x_1857_; lean_object* v___x_1858_; 
v___x_1857_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__0));
lean_inc(v_json_1856_);
v___x_1858_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocation_fromJson_spec__0(v_json_1856_, v___x_1857_);
if (lean_obj_tag(v___x_1858_) == 0)
{
lean_object* v_a_1859_; lean_object* v___x_1861_; uint8_t v_isShared_1862_; uint8_t v_isSharedCheck_1868_; 
lean_dec(v_json_1856_);
v_a_1859_ = lean_ctor_get(v___x_1858_, 0);
v_isSharedCheck_1868_ = !lean_is_exclusive(v___x_1858_);
if (v_isSharedCheck_1868_ == 0)
{
v___x_1861_ = v___x_1858_;
v_isShared_1862_ = v_isSharedCheck_1868_;
goto v_resetjp_1860_;
}
else
{
lean_inc(v_a_1859_);
lean_dec(v___x_1858_);
v___x_1861_ = lean_box(0);
v_isShared_1862_ = v_isSharedCheck_1868_;
goto v_resetjp_1860_;
}
v_resetjp_1860_:
{
lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1866_; 
v___x_1863_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__4, &l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__4);
v___x_1864_ = lean_string_append(v___x_1863_, v_a_1859_);
lean_dec(v_a_1859_);
if (v_isShared_1862_ == 0)
{
lean_ctor_set(v___x_1861_, 0, v___x_1864_);
v___x_1866_ = v___x_1861_;
goto v_reusejp_1865_;
}
else
{
lean_object* v_reuseFailAlloc_1867_; 
v_reuseFailAlloc_1867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1867_, 0, v___x_1864_);
v___x_1866_ = v_reuseFailAlloc_1867_;
goto v_reusejp_1865_;
}
v_reusejp_1865_:
{
return v___x_1866_;
}
}
}
else
{
if (lean_obj_tag(v___x_1858_) == 0)
{
lean_object* v_a_1869_; lean_object* v___x_1871_; uint8_t v_isShared_1872_; uint8_t v_isSharedCheck_1876_; 
lean_dec(v_json_1856_);
v_a_1869_ = lean_ctor_get(v___x_1858_, 0);
v_isSharedCheck_1876_ = !lean_is_exclusive(v___x_1858_);
if (v_isSharedCheck_1876_ == 0)
{
v___x_1871_ = v___x_1858_;
v_isShared_1872_ = v_isSharedCheck_1876_;
goto v_resetjp_1870_;
}
else
{
lean_inc(v_a_1869_);
lean_dec(v___x_1858_);
v___x_1871_ = lean_box(0);
v_isShared_1872_ = v_isSharedCheck_1876_;
goto v_resetjp_1870_;
}
v_resetjp_1870_:
{
lean_object* v___x_1874_; 
if (v_isShared_1872_ == 0)
{
lean_ctor_set_tag(v___x_1871_, 0);
v___x_1874_ = v___x_1871_;
goto v_reusejp_1873_;
}
else
{
lean_object* v_reuseFailAlloc_1875_; 
v_reuseFailAlloc_1875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1875_, 0, v_a_1869_);
v___x_1874_ = v_reuseFailAlloc_1875_;
goto v_reusejp_1873_;
}
v_reusejp_1873_:
{
return v___x_1874_;
}
}
}
else
{
lean_object* v_a_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; 
v_a_1877_ = lean_ctor_get(v___x_1858_, 0);
lean_inc(v_a_1877_);
lean_dec_ref_known(v___x_1858_, 1);
v___x_1878_ = ((lean_object*)(l_Lean_Lsp_instToJsonCreateFile_toJson___closed__0));
lean_inc(v_json_1856_);
v___x_1879_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCreateFile_fromJson_spec__0(v_json_1856_, v___x_1878_);
if (lean_obj_tag(v___x_1879_) == 0)
{
lean_object* v_a_1880_; lean_object* v___x_1882_; uint8_t v_isShared_1883_; uint8_t v_isSharedCheck_1889_; 
lean_dec(v_a_1877_);
lean_dec(v_json_1856_);
v_a_1880_ = lean_ctor_get(v___x_1879_, 0);
v_isSharedCheck_1889_ = !lean_is_exclusive(v___x_1879_);
if (v_isSharedCheck_1889_ == 0)
{
v___x_1882_ = v___x_1879_;
v_isShared_1883_ = v_isSharedCheck_1889_;
goto v_resetjp_1881_;
}
else
{
lean_inc(v_a_1880_);
lean_dec(v___x_1879_);
v___x_1882_ = lean_box(0);
v_isShared_1883_ = v_isSharedCheck_1889_;
goto v_resetjp_1881_;
}
v_resetjp_1881_:
{
lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1887_; 
v___x_1884_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__9, &l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__9);
v___x_1885_ = lean_string_append(v___x_1884_, v_a_1880_);
lean_dec(v_a_1880_);
if (v_isShared_1883_ == 0)
{
lean_ctor_set(v___x_1882_, 0, v___x_1885_);
v___x_1887_ = v___x_1882_;
goto v_reusejp_1886_;
}
else
{
lean_object* v_reuseFailAlloc_1888_; 
v_reuseFailAlloc_1888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1888_, 0, v___x_1885_);
v___x_1887_ = v_reuseFailAlloc_1888_;
goto v_reusejp_1886_;
}
v_reusejp_1886_:
{
return v___x_1887_;
}
}
}
else
{
if (lean_obj_tag(v___x_1879_) == 0)
{
lean_object* v_a_1890_; lean_object* v___x_1892_; uint8_t v_isShared_1893_; uint8_t v_isSharedCheck_1897_; 
lean_dec(v_a_1877_);
lean_dec(v_json_1856_);
v_a_1890_ = lean_ctor_get(v___x_1879_, 0);
v_isSharedCheck_1897_ = !lean_is_exclusive(v___x_1879_);
if (v_isSharedCheck_1897_ == 0)
{
v___x_1892_ = v___x_1879_;
v_isShared_1893_ = v_isSharedCheck_1897_;
goto v_resetjp_1891_;
}
else
{
lean_inc(v_a_1890_);
lean_dec(v___x_1879_);
v___x_1892_ = lean_box(0);
v_isShared_1893_ = v_isSharedCheck_1897_;
goto v_resetjp_1891_;
}
v_resetjp_1891_:
{
lean_object* v___x_1895_; 
if (v_isShared_1893_ == 0)
{
lean_ctor_set_tag(v___x_1892_, 0);
v___x_1895_ = v___x_1892_;
goto v_reusejp_1894_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v_a_1890_);
v___x_1895_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1894_;
}
v_reusejp_1894_:
{
return v___x_1895_;
}
}
}
else
{
lean_object* v_a_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; 
v_a_1898_ = lean_ctor_get(v___x_1879_, 0);
lean_inc(v_a_1898_);
lean_dec_ref_known(v___x_1879_, 1);
v___x_1899_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextEdit_toJson___closed__2));
v___x_1900_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextEdit_fromJson_spec__1(v_json_1856_, v___x_1899_);
if (lean_obj_tag(v___x_1900_) == 0)
{
lean_object* v_a_1901_; lean_object* v___x_1903_; uint8_t v_isShared_1904_; uint8_t v_isSharedCheck_1910_; 
lean_dec(v_a_1898_);
lean_dec(v_a_1877_);
v_a_1901_ = lean_ctor_get(v___x_1900_, 0);
v_isSharedCheck_1910_ = !lean_is_exclusive(v___x_1900_);
if (v_isSharedCheck_1910_ == 0)
{
v___x_1903_ = v___x_1900_;
v_isShared_1904_ = v_isSharedCheck_1910_;
goto v_resetjp_1902_;
}
else
{
lean_inc(v_a_1901_);
lean_dec(v___x_1900_);
v___x_1903_ = lean_box(0);
v_isShared_1904_ = v_isSharedCheck_1910_;
goto v_resetjp_1902_;
}
v_resetjp_1902_:
{
lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1908_; 
v___x_1905_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__11, &l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__11);
v___x_1906_ = lean_string_append(v___x_1905_, v_a_1901_);
lean_dec(v_a_1901_);
if (v_isShared_1904_ == 0)
{
lean_ctor_set(v___x_1903_, 0, v___x_1906_);
v___x_1908_ = v___x_1903_;
goto v_reusejp_1907_;
}
else
{
lean_object* v_reuseFailAlloc_1909_; 
v_reuseFailAlloc_1909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1909_, 0, v___x_1906_);
v___x_1908_ = v_reuseFailAlloc_1909_;
goto v_reusejp_1907_;
}
v_reusejp_1907_:
{
return v___x_1908_;
}
}
}
else
{
if (lean_obj_tag(v___x_1900_) == 0)
{
lean_object* v_a_1911_; lean_object* v___x_1913_; uint8_t v_isShared_1914_; uint8_t v_isSharedCheck_1918_; 
lean_dec(v_a_1898_);
lean_dec(v_a_1877_);
v_a_1911_ = lean_ctor_get(v___x_1900_, 0);
v_isSharedCheck_1918_ = !lean_is_exclusive(v___x_1900_);
if (v_isSharedCheck_1918_ == 0)
{
v___x_1913_ = v___x_1900_;
v_isShared_1914_ = v_isSharedCheck_1918_;
goto v_resetjp_1912_;
}
else
{
lean_inc(v_a_1911_);
lean_dec(v___x_1900_);
v___x_1913_ = lean_box(0);
v_isShared_1914_ = v_isSharedCheck_1918_;
goto v_resetjp_1912_;
}
v_resetjp_1912_:
{
lean_object* v___x_1916_; 
if (v_isShared_1914_ == 0)
{
lean_ctor_set_tag(v___x_1913_, 0);
v___x_1916_ = v___x_1913_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1917_; 
v_reuseFailAlloc_1917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1917_, 0, v_a_1911_);
v___x_1916_ = v_reuseFailAlloc_1917_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
return v___x_1916_;
}
}
}
else
{
lean_object* v_a_1919_; lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_1927_; 
v_a_1919_ = lean_ctor_get(v___x_1900_, 0);
v_isSharedCheck_1927_ = !lean_is_exclusive(v___x_1900_);
if (v_isSharedCheck_1927_ == 0)
{
v___x_1921_ = v___x_1900_;
v_isShared_1922_ = v_isSharedCheck_1927_;
goto v_resetjp_1920_;
}
else
{
lean_inc(v_a_1919_);
lean_dec(v___x_1900_);
v___x_1921_ = lean_box(0);
v_isShared_1922_ = v_isSharedCheck_1927_;
goto v_resetjp_1920_;
}
v_resetjp_1920_:
{
lean_object* v___x_1923_; lean_object* v___x_1925_; 
v___x_1923_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1923_, 0, v_a_1877_);
lean_ctor_set(v___x_1923_, 1, v_a_1898_);
lean_ctor_set(v___x_1923_, 2, v_a_1919_);
if (v_isShared_1922_ == 0)
{
lean_ctor_set(v___x_1921_, 0, v___x_1923_);
v___x_1925_ = v___x_1921_;
goto v_reusejp_1924_;
}
else
{
lean_object* v_reuseFailAlloc_1926_; 
v_reuseFailAlloc_1926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1926_, 0, v___x_1923_);
v___x_1925_ = v_reuseFailAlloc_1926_;
goto v_reusejp_1924_;
}
v_reusejp_1924_:
{
return v___x_1925_;
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
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRenameFile_toJson(lean_object* v_x_1932_){
_start:
{
lean_object* v_oldUri_1933_; lean_object* v_newUri_1934_; lean_object* v_options_x3f_1935_; lean_object* v_annotationId_x3f_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; 
v_oldUri_1933_ = lean_ctor_get(v_x_1932_, 0);
lean_inc_ref(v_oldUri_1933_);
v_newUri_1934_ = lean_ctor_get(v_x_1932_, 1);
lean_inc_ref(v_newUri_1934_);
v_options_x3f_1935_ = lean_ctor_get(v_x_1932_, 2);
lean_inc(v_options_x3f_1935_);
v_annotationId_x3f_1936_ = lean_ctor_get(v_x_1932_, 3);
lean_inc(v_annotationId_x3f_1936_);
lean_dec_ref(v_x_1932_);
v___x_1937_ = ((lean_object*)(l_Lean_Lsp_instToJsonRenameFile_toJson___closed__0));
v___x_1938_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1938_, 0, v_oldUri_1933_);
v___x_1939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1939_, 0, v___x_1937_);
lean_ctor_set(v___x_1939_, 1, v___x_1938_);
v___x_1940_ = lean_box(0);
v___x_1941_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1941_, 0, v___x_1939_);
lean_ctor_set(v___x_1941_, 1, v___x_1940_);
v___x_1942_ = ((lean_object*)(l_Lean_Lsp_instToJsonRenameFile_toJson___closed__1));
v___x_1943_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1943_, 0, v_newUri_1934_);
v___x_1944_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1944_, 0, v___x_1942_);
lean_ctor_set(v___x_1944_, 1, v___x_1943_);
v___x_1945_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1945_, 0, v___x_1944_);
lean_ctor_set(v___x_1945_, 1, v___x_1940_);
v___x_1946_ = ((lean_object*)(l_Lean_Lsp_instToJsonCreateFile_toJson___closed__0));
v___x_1947_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonCreateFile_toJson_spec__0(v___x_1946_, v_options_x3f_1935_);
lean_dec(v_options_x3f_1935_);
v___x_1948_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextEdit_toJson___closed__2));
v___x_1949_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextEdit_toJson_spec__1(v___x_1948_, v_annotationId_x3f_1936_);
v___x_1950_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1950_, 0, v___x_1949_);
lean_ctor_set(v___x_1950_, 1, v___x_1940_);
v___x_1951_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1951_, 0, v___x_1947_);
lean_ctor_set(v___x_1951_, 1, v___x_1950_);
v___x_1952_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1952_, 0, v___x_1945_);
lean_ctor_set(v___x_1952_, 1, v___x_1951_);
v___x_1953_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1953_, 0, v___x_1941_);
lean_ctor_set(v___x_1953_, 1, v___x_1952_);
v___x_1954_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__2));
v___x_1955_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLocation_toJson_spec__0(v___x_1953_, v___x_1954_);
v___x_1956_ = l_Lean_Json_mkObj(v___x_1955_);
lean_dec(v___x_1955_);
return v___x_1956_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__2(void){
_start:
{
uint8_t v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; 
v___x_1964_ = 1;
v___x_1965_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__1));
v___x_1966_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1965_, v___x_1964_);
return v___x_1966_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__3(void){
_start:
{
lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; 
v___x_1967_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__5));
v___x_1968_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__2, &l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__2);
v___x_1969_ = lean_string_append(v___x_1968_, v___x_1967_);
return v___x_1969_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__5(void){
_start:
{
uint8_t v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; 
v___x_1972_ = 1;
v___x_1973_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__4));
v___x_1974_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1973_, v___x_1972_);
return v___x_1974_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__6(void){
_start:
{
lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; 
v___x_1975_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__5, &l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__5);
v___x_1976_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__3, &l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__3);
v___x_1977_ = lean_string_append(v___x_1976_, v___x_1975_);
return v___x_1977_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__7(void){
_start:
{
lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; 
v___x_1978_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_1979_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__6, &l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__6);
v___x_1980_ = lean_string_append(v___x_1979_, v___x_1978_);
return v___x_1980_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__9(void){
_start:
{
uint8_t v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; 
v___x_1983_ = 1;
v___x_1984_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__8));
v___x_1985_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1984_, v___x_1983_);
return v___x_1985_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__10(void){
_start:
{
lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; 
v___x_1986_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__9, &l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__9);
v___x_1987_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__3, &l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__3);
v___x_1988_ = lean_string_append(v___x_1987_, v___x_1986_);
return v___x_1988_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__11(void){
_start:
{
lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; 
v___x_1989_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_1990_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__10, &l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__10);
v___x_1991_ = lean_string_append(v___x_1990_, v___x_1989_);
return v___x_1991_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__12(void){
_start:
{
lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; 
v___x_1992_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__7, &l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__7);
v___x_1993_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__3, &l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__3);
v___x_1994_ = lean_string_append(v___x_1993_, v___x_1992_);
return v___x_1994_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__13(void){
_start:
{
lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; 
v___x_1995_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_1996_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__12, &l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__12);
v___x_1997_ = lean_string_append(v___x_1996_, v___x_1995_);
return v___x_1997_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__14(void){
_start:
{
lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; 
v___x_1998_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__17, &l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__17_once, _init_l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__17);
v___x_1999_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__3, &l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__3);
v___x_2000_ = lean_string_append(v___x_1999_, v___x_1998_);
return v___x_2000_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__15(void){
_start:
{
lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; 
v___x_2001_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_2002_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__14, &l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__14_once, _init_l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__14);
v___x_2003_ = lean_string_append(v___x_2002_, v___x_2001_);
return v___x_2003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonRenameFile_fromJson(lean_object* v_json_2004_){
_start:
{
lean_object* v___x_2005_; lean_object* v___x_2006_; 
v___x_2005_ = ((lean_object*)(l_Lean_Lsp_instToJsonRenameFile_toJson___closed__0));
lean_inc(v_json_2004_);
v___x_2006_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocation_fromJson_spec__0(v_json_2004_, v___x_2005_);
if (lean_obj_tag(v___x_2006_) == 0)
{
lean_object* v_a_2007_; lean_object* v___x_2009_; uint8_t v_isShared_2010_; uint8_t v_isSharedCheck_2016_; 
lean_dec(v_json_2004_);
v_a_2007_ = lean_ctor_get(v___x_2006_, 0);
v_isSharedCheck_2016_ = !lean_is_exclusive(v___x_2006_);
if (v_isSharedCheck_2016_ == 0)
{
v___x_2009_ = v___x_2006_;
v_isShared_2010_ = v_isSharedCheck_2016_;
goto v_resetjp_2008_;
}
else
{
lean_inc(v_a_2007_);
lean_dec(v___x_2006_);
v___x_2009_ = lean_box(0);
v_isShared_2010_ = v_isSharedCheck_2016_;
goto v_resetjp_2008_;
}
v_resetjp_2008_:
{
lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2014_; 
v___x_2011_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__7, &l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__7);
v___x_2012_ = lean_string_append(v___x_2011_, v_a_2007_);
lean_dec(v_a_2007_);
if (v_isShared_2010_ == 0)
{
lean_ctor_set(v___x_2009_, 0, v___x_2012_);
v___x_2014_ = v___x_2009_;
goto v_reusejp_2013_;
}
else
{
lean_object* v_reuseFailAlloc_2015_; 
v_reuseFailAlloc_2015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2015_, 0, v___x_2012_);
v___x_2014_ = v_reuseFailAlloc_2015_;
goto v_reusejp_2013_;
}
v_reusejp_2013_:
{
return v___x_2014_;
}
}
}
else
{
if (lean_obj_tag(v___x_2006_) == 0)
{
lean_object* v_a_2017_; lean_object* v___x_2019_; uint8_t v_isShared_2020_; uint8_t v_isSharedCheck_2024_; 
lean_dec(v_json_2004_);
v_a_2017_ = lean_ctor_get(v___x_2006_, 0);
v_isSharedCheck_2024_ = !lean_is_exclusive(v___x_2006_);
if (v_isSharedCheck_2024_ == 0)
{
v___x_2019_ = v___x_2006_;
v_isShared_2020_ = v_isSharedCheck_2024_;
goto v_resetjp_2018_;
}
else
{
lean_inc(v_a_2017_);
lean_dec(v___x_2006_);
v___x_2019_ = lean_box(0);
v_isShared_2020_ = v_isSharedCheck_2024_;
goto v_resetjp_2018_;
}
v_resetjp_2018_:
{
lean_object* v___x_2022_; 
if (v_isShared_2020_ == 0)
{
lean_ctor_set_tag(v___x_2019_, 0);
v___x_2022_ = v___x_2019_;
goto v_reusejp_2021_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v_a_2017_);
v___x_2022_ = v_reuseFailAlloc_2023_;
goto v_reusejp_2021_;
}
v_reusejp_2021_:
{
return v___x_2022_;
}
}
}
else
{
lean_object* v_a_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; 
v_a_2025_ = lean_ctor_get(v___x_2006_, 0);
lean_inc(v_a_2025_);
lean_dec_ref_known(v___x_2006_, 1);
v___x_2026_ = ((lean_object*)(l_Lean_Lsp_instToJsonRenameFile_toJson___closed__1));
lean_inc(v_json_2004_);
v___x_2027_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocation_fromJson_spec__0(v_json_2004_, v___x_2026_);
if (lean_obj_tag(v___x_2027_) == 0)
{
lean_object* v_a_2028_; lean_object* v___x_2030_; uint8_t v_isShared_2031_; uint8_t v_isSharedCheck_2037_; 
lean_dec(v_a_2025_);
lean_dec(v_json_2004_);
v_a_2028_ = lean_ctor_get(v___x_2027_, 0);
v_isSharedCheck_2037_ = !lean_is_exclusive(v___x_2027_);
if (v_isSharedCheck_2037_ == 0)
{
v___x_2030_ = v___x_2027_;
v_isShared_2031_ = v_isSharedCheck_2037_;
goto v_resetjp_2029_;
}
else
{
lean_inc(v_a_2028_);
lean_dec(v___x_2027_);
v___x_2030_ = lean_box(0);
v_isShared_2031_ = v_isSharedCheck_2037_;
goto v_resetjp_2029_;
}
v_resetjp_2029_:
{
lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2035_; 
v___x_2032_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__11, &l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__11);
v___x_2033_ = lean_string_append(v___x_2032_, v_a_2028_);
lean_dec(v_a_2028_);
if (v_isShared_2031_ == 0)
{
lean_ctor_set(v___x_2030_, 0, v___x_2033_);
v___x_2035_ = v___x_2030_;
goto v_reusejp_2034_;
}
else
{
lean_object* v_reuseFailAlloc_2036_; 
v_reuseFailAlloc_2036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2036_, 0, v___x_2033_);
v___x_2035_ = v_reuseFailAlloc_2036_;
goto v_reusejp_2034_;
}
v_reusejp_2034_:
{
return v___x_2035_;
}
}
}
else
{
if (lean_obj_tag(v___x_2027_) == 0)
{
lean_object* v_a_2038_; lean_object* v___x_2040_; uint8_t v_isShared_2041_; uint8_t v_isSharedCheck_2045_; 
lean_dec(v_a_2025_);
lean_dec(v_json_2004_);
v_a_2038_ = lean_ctor_get(v___x_2027_, 0);
v_isSharedCheck_2045_ = !lean_is_exclusive(v___x_2027_);
if (v_isSharedCheck_2045_ == 0)
{
v___x_2040_ = v___x_2027_;
v_isShared_2041_ = v_isSharedCheck_2045_;
goto v_resetjp_2039_;
}
else
{
lean_inc(v_a_2038_);
lean_dec(v___x_2027_);
v___x_2040_ = lean_box(0);
v_isShared_2041_ = v_isSharedCheck_2045_;
goto v_resetjp_2039_;
}
v_resetjp_2039_:
{
lean_object* v___x_2043_; 
if (v_isShared_2041_ == 0)
{
lean_ctor_set_tag(v___x_2040_, 0);
v___x_2043_ = v___x_2040_;
goto v_reusejp_2042_;
}
else
{
lean_object* v_reuseFailAlloc_2044_; 
v_reuseFailAlloc_2044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2044_, 0, v_a_2038_);
v___x_2043_ = v_reuseFailAlloc_2044_;
goto v_reusejp_2042_;
}
v_reusejp_2042_:
{
return v___x_2043_;
}
}
}
else
{
lean_object* v_a_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; 
v_a_2046_ = lean_ctor_get(v___x_2027_, 0);
lean_inc(v_a_2046_);
lean_dec_ref_known(v___x_2027_, 1);
v___x_2047_ = ((lean_object*)(l_Lean_Lsp_instToJsonCreateFile_toJson___closed__0));
lean_inc(v_json_2004_);
v___x_2048_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCreateFile_fromJson_spec__0(v_json_2004_, v___x_2047_);
if (lean_obj_tag(v___x_2048_) == 0)
{
lean_object* v_a_2049_; lean_object* v___x_2051_; uint8_t v_isShared_2052_; uint8_t v_isSharedCheck_2058_; 
lean_dec(v_a_2046_);
lean_dec(v_a_2025_);
lean_dec(v_json_2004_);
v_a_2049_ = lean_ctor_get(v___x_2048_, 0);
v_isSharedCheck_2058_ = !lean_is_exclusive(v___x_2048_);
if (v_isSharedCheck_2058_ == 0)
{
v___x_2051_ = v___x_2048_;
v_isShared_2052_ = v_isSharedCheck_2058_;
goto v_resetjp_2050_;
}
else
{
lean_inc(v_a_2049_);
lean_dec(v___x_2048_);
v___x_2051_ = lean_box(0);
v_isShared_2052_ = v_isSharedCheck_2058_;
goto v_resetjp_2050_;
}
v_resetjp_2050_:
{
lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2056_; 
v___x_2053_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__13, &l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__13);
v___x_2054_ = lean_string_append(v___x_2053_, v_a_2049_);
lean_dec(v_a_2049_);
if (v_isShared_2052_ == 0)
{
lean_ctor_set(v___x_2051_, 0, v___x_2054_);
v___x_2056_ = v___x_2051_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v___x_2054_);
v___x_2056_ = v_reuseFailAlloc_2057_;
goto v_reusejp_2055_;
}
v_reusejp_2055_:
{
return v___x_2056_;
}
}
}
else
{
if (lean_obj_tag(v___x_2048_) == 0)
{
lean_object* v_a_2059_; lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2066_; 
lean_dec(v_a_2046_);
lean_dec(v_a_2025_);
lean_dec(v_json_2004_);
v_a_2059_ = lean_ctor_get(v___x_2048_, 0);
v_isSharedCheck_2066_ = !lean_is_exclusive(v___x_2048_);
if (v_isSharedCheck_2066_ == 0)
{
v___x_2061_ = v___x_2048_;
v_isShared_2062_ = v_isSharedCheck_2066_;
goto v_resetjp_2060_;
}
else
{
lean_inc(v_a_2059_);
lean_dec(v___x_2048_);
v___x_2061_ = lean_box(0);
v_isShared_2062_ = v_isSharedCheck_2066_;
goto v_resetjp_2060_;
}
v_resetjp_2060_:
{
lean_object* v___x_2064_; 
if (v_isShared_2062_ == 0)
{
lean_ctor_set_tag(v___x_2061_, 0);
v___x_2064_ = v___x_2061_;
goto v_reusejp_2063_;
}
else
{
lean_object* v_reuseFailAlloc_2065_; 
v_reuseFailAlloc_2065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2065_, 0, v_a_2059_);
v___x_2064_ = v_reuseFailAlloc_2065_;
goto v_reusejp_2063_;
}
v_reusejp_2063_:
{
return v___x_2064_;
}
}
}
else
{
lean_object* v_a_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; 
v_a_2067_ = lean_ctor_get(v___x_2048_, 0);
lean_inc(v_a_2067_);
lean_dec_ref_known(v___x_2048_, 1);
v___x_2068_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextEdit_toJson___closed__2));
v___x_2069_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextEdit_fromJson_spec__1(v_json_2004_, v___x_2068_);
if (lean_obj_tag(v___x_2069_) == 0)
{
lean_object* v_a_2070_; lean_object* v___x_2072_; uint8_t v_isShared_2073_; uint8_t v_isSharedCheck_2079_; 
lean_dec(v_a_2067_);
lean_dec(v_a_2046_);
lean_dec(v_a_2025_);
v_a_2070_ = lean_ctor_get(v___x_2069_, 0);
v_isSharedCheck_2079_ = !lean_is_exclusive(v___x_2069_);
if (v_isSharedCheck_2079_ == 0)
{
v___x_2072_ = v___x_2069_;
v_isShared_2073_ = v_isSharedCheck_2079_;
goto v_resetjp_2071_;
}
else
{
lean_inc(v_a_2070_);
lean_dec(v___x_2069_);
v___x_2072_ = lean_box(0);
v_isShared_2073_ = v_isSharedCheck_2079_;
goto v_resetjp_2071_;
}
v_resetjp_2071_:
{
lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2077_; 
v___x_2074_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__15, &l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__15_once, _init_l_Lean_Lsp_instFromJsonRenameFile_fromJson___closed__15);
v___x_2075_ = lean_string_append(v___x_2074_, v_a_2070_);
lean_dec(v_a_2070_);
if (v_isShared_2073_ == 0)
{
lean_ctor_set(v___x_2072_, 0, v___x_2075_);
v___x_2077_ = v___x_2072_;
goto v_reusejp_2076_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v___x_2075_);
v___x_2077_ = v_reuseFailAlloc_2078_;
goto v_reusejp_2076_;
}
v_reusejp_2076_:
{
return v___x_2077_;
}
}
}
else
{
if (lean_obj_tag(v___x_2069_) == 0)
{
lean_object* v_a_2080_; lean_object* v___x_2082_; uint8_t v_isShared_2083_; uint8_t v_isSharedCheck_2087_; 
lean_dec(v_a_2067_);
lean_dec(v_a_2046_);
lean_dec(v_a_2025_);
v_a_2080_ = lean_ctor_get(v___x_2069_, 0);
v_isSharedCheck_2087_ = !lean_is_exclusive(v___x_2069_);
if (v_isSharedCheck_2087_ == 0)
{
v___x_2082_ = v___x_2069_;
v_isShared_2083_ = v_isSharedCheck_2087_;
goto v_resetjp_2081_;
}
else
{
lean_inc(v_a_2080_);
lean_dec(v___x_2069_);
v___x_2082_ = lean_box(0);
v_isShared_2083_ = v_isSharedCheck_2087_;
goto v_resetjp_2081_;
}
v_resetjp_2081_:
{
lean_object* v___x_2085_; 
if (v_isShared_2083_ == 0)
{
lean_ctor_set_tag(v___x_2082_, 0);
v___x_2085_ = v___x_2082_;
goto v_reusejp_2084_;
}
else
{
lean_object* v_reuseFailAlloc_2086_; 
v_reuseFailAlloc_2086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2086_, 0, v_a_2080_);
v___x_2085_ = v_reuseFailAlloc_2086_;
goto v_reusejp_2084_;
}
v_reusejp_2084_:
{
return v___x_2085_;
}
}
}
else
{
lean_object* v_a_2088_; lean_object* v___x_2090_; uint8_t v_isShared_2091_; uint8_t v_isSharedCheck_2096_; 
v_a_2088_ = lean_ctor_get(v___x_2069_, 0);
v_isSharedCheck_2096_ = !lean_is_exclusive(v___x_2069_);
if (v_isSharedCheck_2096_ == 0)
{
v___x_2090_ = v___x_2069_;
v_isShared_2091_ = v_isSharedCheck_2096_;
goto v_resetjp_2089_;
}
else
{
lean_inc(v_a_2088_);
lean_dec(v___x_2069_);
v___x_2090_ = lean_box(0);
v_isShared_2091_ = v_isSharedCheck_2096_;
goto v_resetjp_2089_;
}
v_resetjp_2089_:
{
lean_object* v___x_2092_; lean_object* v___x_2094_; 
v___x_2092_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2092_, 0, v_a_2025_);
lean_ctor_set(v___x_2092_, 1, v_a_2046_);
lean_ctor_set(v___x_2092_, 2, v_a_2067_);
lean_ctor_set(v___x_2092_, 3, v_a_2088_);
if (v_isShared_2091_ == 0)
{
lean_ctor_set(v___x_2090_, 0, v___x_2092_);
v___x_2094_ = v___x_2090_;
goto v_reusejp_2093_;
}
else
{
lean_object* v_reuseFailAlloc_2095_; 
v_reuseFailAlloc_2095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2095_, 0, v___x_2092_);
v___x_2094_ = v_reuseFailAlloc_2095_;
goto v_reusejp_2093_;
}
v_reusejp_2093_:
{
return v___x_2094_;
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
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDeleteFile_toJson_spec__0(lean_object* v_k_2099_, lean_object* v_x_2100_){
_start:
{
if (lean_obj_tag(v_x_2100_) == 0)
{
lean_object* v___x_2101_; 
lean_dec_ref(v_k_2099_);
v___x_2101_ = lean_box(0);
return v___x_2101_;
}
else
{
lean_object* v_val_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; 
v_val_2102_ = lean_ctor_get(v_x_2100_, 0);
v___x_2103_ = l_Lean_Lsp_DeleteFile_instToJsonOptions_toJson(v_val_2102_);
v___x_2104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2104_, 0, v_k_2099_);
lean_ctor_set(v___x_2104_, 1, v___x_2103_);
v___x_2105_ = lean_box(0);
v___x_2106_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2106_, 0, v___x_2104_);
lean_ctor_set(v___x_2106_, 1, v___x_2105_);
return v___x_2106_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDeleteFile_toJson_spec__0___boxed(lean_object* v_k_2107_, lean_object* v_x_2108_){
_start:
{
lean_object* v_res_2109_; 
v_res_2109_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDeleteFile_toJson_spec__0(v_k_2107_, v_x_2108_);
lean_dec(v_x_2108_);
return v_res_2109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDeleteFile_toJson(lean_object* v_x_2110_){
_start:
{
lean_object* v_uri_2111_; lean_object* v_options_x3f_2112_; lean_object* v_annotationId_x3f_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; 
v_uri_2111_ = lean_ctor_get(v_x_2110_, 0);
lean_inc_ref(v_uri_2111_);
v_options_x3f_2112_ = lean_ctor_get(v_x_2110_, 1);
lean_inc(v_options_x3f_2112_);
v_annotationId_x3f_2113_ = lean_ctor_get(v_x_2110_, 2);
lean_inc(v_annotationId_x3f_2113_);
lean_dec_ref(v_x_2110_);
v___x_2114_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__0));
v___x_2115_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2115_, 0, v_uri_2111_);
v___x_2116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2116_, 0, v___x_2114_);
lean_ctor_set(v___x_2116_, 1, v___x_2115_);
v___x_2117_ = lean_box(0);
v___x_2118_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2118_, 0, v___x_2116_);
lean_ctor_set(v___x_2118_, 1, v___x_2117_);
v___x_2119_ = ((lean_object*)(l_Lean_Lsp_instToJsonCreateFile_toJson___closed__0));
v___x_2120_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDeleteFile_toJson_spec__0(v___x_2119_, v_options_x3f_2112_);
lean_dec(v_options_x3f_2112_);
v___x_2121_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextEdit_toJson___closed__2));
v___x_2122_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextEdit_toJson_spec__1(v___x_2121_, v_annotationId_x3f_2113_);
v___x_2123_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2123_, 0, v___x_2122_);
lean_ctor_set(v___x_2123_, 1, v___x_2117_);
v___x_2124_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2124_, 0, v___x_2120_);
lean_ctor_set(v___x_2124_, 1, v___x_2123_);
v___x_2125_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2125_, 0, v___x_2118_);
lean_ctor_set(v___x_2125_, 1, v___x_2124_);
v___x_2126_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__2));
v___x_2127_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLocation_toJson_spec__0(v___x_2125_, v___x_2126_);
v___x_2128_ = l_Lean_Json_mkObj(v___x_2127_);
lean_dec(v___x_2127_);
return v___x_2128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDeleteFile_fromJson_spec__0_spec__0(lean_object* v_x_2133_){
_start:
{
if (lean_obj_tag(v_x_2133_) == 0)
{
lean_object* v___x_2134_; 
v___x_2134_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDeleteFile_fromJson_spec__0_spec__0___closed__0));
return v___x_2134_;
}
else
{
lean_object* v___x_2135_; 
v___x_2135_ = l_Lean_Lsp_DeleteFile_instFromJsonOptions_fromJson(v_x_2133_);
if (lean_obj_tag(v___x_2135_) == 0)
{
lean_object* v_a_2136_; lean_object* v___x_2138_; uint8_t v_isShared_2139_; uint8_t v_isSharedCheck_2143_; 
v_a_2136_ = lean_ctor_get(v___x_2135_, 0);
v_isSharedCheck_2143_ = !lean_is_exclusive(v___x_2135_);
if (v_isSharedCheck_2143_ == 0)
{
v___x_2138_ = v___x_2135_;
v_isShared_2139_ = v_isSharedCheck_2143_;
goto v_resetjp_2137_;
}
else
{
lean_inc(v_a_2136_);
lean_dec(v___x_2135_);
v___x_2138_ = lean_box(0);
v_isShared_2139_ = v_isSharedCheck_2143_;
goto v_resetjp_2137_;
}
v_resetjp_2137_:
{
lean_object* v___x_2141_; 
if (v_isShared_2139_ == 0)
{
v___x_2141_ = v___x_2138_;
goto v_reusejp_2140_;
}
else
{
lean_object* v_reuseFailAlloc_2142_; 
v_reuseFailAlloc_2142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2142_, 0, v_a_2136_);
v___x_2141_ = v_reuseFailAlloc_2142_;
goto v_reusejp_2140_;
}
v_reusejp_2140_:
{
return v___x_2141_;
}
}
}
else
{
lean_object* v_a_2144_; lean_object* v___x_2146_; uint8_t v_isShared_2147_; uint8_t v_isSharedCheck_2152_; 
v_a_2144_ = lean_ctor_get(v___x_2135_, 0);
v_isSharedCheck_2152_ = !lean_is_exclusive(v___x_2135_);
if (v_isSharedCheck_2152_ == 0)
{
v___x_2146_ = v___x_2135_;
v_isShared_2147_ = v_isSharedCheck_2152_;
goto v_resetjp_2145_;
}
else
{
lean_inc(v_a_2144_);
lean_dec(v___x_2135_);
v___x_2146_ = lean_box(0);
v_isShared_2147_ = v_isSharedCheck_2152_;
goto v_resetjp_2145_;
}
v_resetjp_2145_:
{
lean_object* v___x_2148_; lean_object* v___x_2150_; 
v___x_2148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2148_, 0, v_a_2144_);
if (v_isShared_2147_ == 0)
{
lean_ctor_set(v___x_2146_, 0, v___x_2148_);
v___x_2150_ = v___x_2146_;
goto v_reusejp_2149_;
}
else
{
lean_object* v_reuseFailAlloc_2151_; 
v_reuseFailAlloc_2151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2151_, 0, v___x_2148_);
v___x_2150_ = v_reuseFailAlloc_2151_;
goto v_reusejp_2149_;
}
v_reusejp_2149_:
{
return v___x_2150_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDeleteFile_fromJson_spec__0(lean_object* v_j_2153_, lean_object* v_k_2154_){
_start:
{
lean_object* v___x_2155_; lean_object* v___x_2156_; 
v___x_2155_ = l_Lean_Json_getObjValD(v_j_2153_, v_k_2154_);
v___x_2156_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDeleteFile_fromJson_spec__0_spec__0(v___x_2155_);
return v___x_2156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDeleteFile_fromJson_spec__0___boxed(lean_object* v_j_2157_, lean_object* v_k_2158_){
_start:
{
lean_object* v_res_2159_; 
v_res_2159_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDeleteFile_fromJson_spec__0(v_j_2157_, v_k_2158_);
lean_dec_ref(v_k_2158_);
return v_res_2159_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__1(void){
_start:
{
uint8_t v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; 
v___x_2164_ = 1;
v___x_2165_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__0));
v___x_2166_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2165_, v___x_2164_);
return v___x_2166_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__2(void){
_start:
{
lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; 
v___x_2167_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__5));
v___x_2168_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__1, &l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__1_once, _init_l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__1);
v___x_2169_ = lean_string_append(v___x_2168_, v___x_2167_);
return v___x_2169_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__3(void){
_start:
{
lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; 
v___x_2170_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLocation_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLocation_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLocation_fromJson___closed__8);
v___x_2171_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__2, &l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__2);
v___x_2172_ = lean_string_append(v___x_2171_, v___x_2170_);
return v___x_2172_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__4(void){
_start:
{
lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; 
v___x_2173_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_2174_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__3, &l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__3);
v___x_2175_ = lean_string_append(v___x_2174_, v___x_2173_);
return v___x_2175_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__5(void){
_start:
{
lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; 
v___x_2176_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__7, &l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonCreateFile_fromJson___closed__7);
v___x_2177_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__2, &l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__2);
v___x_2178_ = lean_string_append(v___x_2177_, v___x_2176_);
return v___x_2178_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__6(void){
_start:
{
lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; 
v___x_2179_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_2180_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__5, &l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__5);
v___x_2181_ = lean_string_append(v___x_2180_, v___x_2179_);
return v___x_2181_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__7(void){
_start:
{
lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; 
v___x_2182_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__17, &l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__17_once, _init_l_Lean_Lsp_instFromJsonTextEdit_fromJson___closed__17);
v___x_2183_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__2, &l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__2);
v___x_2184_ = lean_string_append(v___x_2183_, v___x_2182_);
return v___x_2184_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__8(void){
_start:
{
lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; 
v___x_2185_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_2186_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__7, &l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__7);
v___x_2187_ = lean_string_append(v___x_2186_, v___x_2185_);
return v___x_2187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDeleteFile_fromJson(lean_object* v_json_2188_){
_start:
{
lean_object* v___x_2189_; lean_object* v___x_2190_; 
v___x_2189_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__0));
lean_inc(v_json_2188_);
v___x_2190_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocation_fromJson_spec__0(v_json_2188_, v___x_2189_);
if (lean_obj_tag(v___x_2190_) == 0)
{
lean_object* v_a_2191_; lean_object* v___x_2193_; uint8_t v_isShared_2194_; uint8_t v_isSharedCheck_2200_; 
lean_dec(v_json_2188_);
v_a_2191_ = lean_ctor_get(v___x_2190_, 0);
v_isSharedCheck_2200_ = !lean_is_exclusive(v___x_2190_);
if (v_isSharedCheck_2200_ == 0)
{
v___x_2193_ = v___x_2190_;
v_isShared_2194_ = v_isSharedCheck_2200_;
goto v_resetjp_2192_;
}
else
{
lean_inc(v_a_2191_);
lean_dec(v___x_2190_);
v___x_2193_ = lean_box(0);
v_isShared_2194_ = v_isSharedCheck_2200_;
goto v_resetjp_2192_;
}
v_resetjp_2192_:
{
lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2198_; 
v___x_2195_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__4, &l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__4);
v___x_2196_ = lean_string_append(v___x_2195_, v_a_2191_);
lean_dec(v_a_2191_);
if (v_isShared_2194_ == 0)
{
lean_ctor_set(v___x_2193_, 0, v___x_2196_);
v___x_2198_ = v___x_2193_;
goto v_reusejp_2197_;
}
else
{
lean_object* v_reuseFailAlloc_2199_; 
v_reuseFailAlloc_2199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2199_, 0, v___x_2196_);
v___x_2198_ = v_reuseFailAlloc_2199_;
goto v_reusejp_2197_;
}
v_reusejp_2197_:
{
return v___x_2198_;
}
}
}
else
{
if (lean_obj_tag(v___x_2190_) == 0)
{
lean_object* v_a_2201_; lean_object* v___x_2203_; uint8_t v_isShared_2204_; uint8_t v_isSharedCheck_2208_; 
lean_dec(v_json_2188_);
v_a_2201_ = lean_ctor_get(v___x_2190_, 0);
v_isSharedCheck_2208_ = !lean_is_exclusive(v___x_2190_);
if (v_isSharedCheck_2208_ == 0)
{
v___x_2203_ = v___x_2190_;
v_isShared_2204_ = v_isSharedCheck_2208_;
goto v_resetjp_2202_;
}
else
{
lean_inc(v_a_2201_);
lean_dec(v___x_2190_);
v___x_2203_ = lean_box(0);
v_isShared_2204_ = v_isSharedCheck_2208_;
goto v_resetjp_2202_;
}
v_resetjp_2202_:
{
lean_object* v___x_2206_; 
if (v_isShared_2204_ == 0)
{
lean_ctor_set_tag(v___x_2203_, 0);
v___x_2206_ = v___x_2203_;
goto v_reusejp_2205_;
}
else
{
lean_object* v_reuseFailAlloc_2207_; 
v_reuseFailAlloc_2207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2207_, 0, v_a_2201_);
v___x_2206_ = v_reuseFailAlloc_2207_;
goto v_reusejp_2205_;
}
v_reusejp_2205_:
{
return v___x_2206_;
}
}
}
else
{
lean_object* v_a_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; 
v_a_2209_ = lean_ctor_get(v___x_2190_, 0);
lean_inc(v_a_2209_);
lean_dec_ref_known(v___x_2190_, 1);
v___x_2210_ = ((lean_object*)(l_Lean_Lsp_instToJsonCreateFile_toJson___closed__0));
lean_inc(v_json_2188_);
v___x_2211_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDeleteFile_fromJson_spec__0(v_json_2188_, v___x_2210_);
if (lean_obj_tag(v___x_2211_) == 0)
{
lean_object* v_a_2212_; lean_object* v___x_2214_; uint8_t v_isShared_2215_; uint8_t v_isSharedCheck_2221_; 
lean_dec(v_a_2209_);
lean_dec(v_json_2188_);
v_a_2212_ = lean_ctor_get(v___x_2211_, 0);
v_isSharedCheck_2221_ = !lean_is_exclusive(v___x_2211_);
if (v_isSharedCheck_2221_ == 0)
{
v___x_2214_ = v___x_2211_;
v_isShared_2215_ = v_isSharedCheck_2221_;
goto v_resetjp_2213_;
}
else
{
lean_inc(v_a_2212_);
lean_dec(v___x_2211_);
v___x_2214_ = lean_box(0);
v_isShared_2215_ = v_isSharedCheck_2221_;
goto v_resetjp_2213_;
}
v_resetjp_2213_:
{
lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2219_; 
v___x_2216_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__6, &l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__6);
v___x_2217_ = lean_string_append(v___x_2216_, v_a_2212_);
lean_dec(v_a_2212_);
if (v_isShared_2215_ == 0)
{
lean_ctor_set(v___x_2214_, 0, v___x_2217_);
v___x_2219_ = v___x_2214_;
goto v_reusejp_2218_;
}
else
{
lean_object* v_reuseFailAlloc_2220_; 
v_reuseFailAlloc_2220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2220_, 0, v___x_2217_);
v___x_2219_ = v_reuseFailAlloc_2220_;
goto v_reusejp_2218_;
}
v_reusejp_2218_:
{
return v___x_2219_;
}
}
}
else
{
if (lean_obj_tag(v___x_2211_) == 0)
{
lean_object* v_a_2222_; lean_object* v___x_2224_; uint8_t v_isShared_2225_; uint8_t v_isSharedCheck_2229_; 
lean_dec(v_a_2209_);
lean_dec(v_json_2188_);
v_a_2222_ = lean_ctor_get(v___x_2211_, 0);
v_isSharedCheck_2229_ = !lean_is_exclusive(v___x_2211_);
if (v_isSharedCheck_2229_ == 0)
{
v___x_2224_ = v___x_2211_;
v_isShared_2225_ = v_isSharedCheck_2229_;
goto v_resetjp_2223_;
}
else
{
lean_inc(v_a_2222_);
lean_dec(v___x_2211_);
v___x_2224_ = lean_box(0);
v_isShared_2225_ = v_isSharedCheck_2229_;
goto v_resetjp_2223_;
}
v_resetjp_2223_:
{
lean_object* v___x_2227_; 
if (v_isShared_2225_ == 0)
{
lean_ctor_set_tag(v___x_2224_, 0);
v___x_2227_ = v___x_2224_;
goto v_reusejp_2226_;
}
else
{
lean_object* v_reuseFailAlloc_2228_; 
v_reuseFailAlloc_2228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2228_, 0, v_a_2222_);
v___x_2227_ = v_reuseFailAlloc_2228_;
goto v_reusejp_2226_;
}
v_reusejp_2226_:
{
return v___x_2227_;
}
}
}
else
{
lean_object* v_a_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; 
v_a_2230_ = lean_ctor_get(v___x_2211_, 0);
lean_inc(v_a_2230_);
lean_dec_ref_known(v___x_2211_, 1);
v___x_2231_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextEdit_toJson___closed__2));
v___x_2232_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextEdit_fromJson_spec__1(v_json_2188_, v___x_2231_);
if (lean_obj_tag(v___x_2232_) == 0)
{
lean_object* v_a_2233_; lean_object* v___x_2235_; uint8_t v_isShared_2236_; uint8_t v_isSharedCheck_2242_; 
lean_dec(v_a_2230_);
lean_dec(v_a_2209_);
v_a_2233_ = lean_ctor_get(v___x_2232_, 0);
v_isSharedCheck_2242_ = !lean_is_exclusive(v___x_2232_);
if (v_isSharedCheck_2242_ == 0)
{
v___x_2235_ = v___x_2232_;
v_isShared_2236_ = v_isSharedCheck_2242_;
goto v_resetjp_2234_;
}
else
{
lean_inc(v_a_2233_);
lean_dec(v___x_2232_);
v___x_2235_ = lean_box(0);
v_isShared_2236_ = v_isSharedCheck_2242_;
goto v_resetjp_2234_;
}
v_resetjp_2234_:
{
lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2240_; 
v___x_2237_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__8, &l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonDeleteFile_fromJson___closed__8);
v___x_2238_ = lean_string_append(v___x_2237_, v_a_2233_);
lean_dec(v_a_2233_);
if (v_isShared_2236_ == 0)
{
lean_ctor_set(v___x_2235_, 0, v___x_2238_);
v___x_2240_ = v___x_2235_;
goto v_reusejp_2239_;
}
else
{
lean_object* v_reuseFailAlloc_2241_; 
v_reuseFailAlloc_2241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2241_, 0, v___x_2238_);
v___x_2240_ = v_reuseFailAlloc_2241_;
goto v_reusejp_2239_;
}
v_reusejp_2239_:
{
return v___x_2240_;
}
}
}
else
{
if (lean_obj_tag(v___x_2232_) == 0)
{
lean_object* v_a_2243_; lean_object* v___x_2245_; uint8_t v_isShared_2246_; uint8_t v_isSharedCheck_2250_; 
lean_dec(v_a_2230_);
lean_dec(v_a_2209_);
v_a_2243_ = lean_ctor_get(v___x_2232_, 0);
v_isSharedCheck_2250_ = !lean_is_exclusive(v___x_2232_);
if (v_isSharedCheck_2250_ == 0)
{
v___x_2245_ = v___x_2232_;
v_isShared_2246_ = v_isSharedCheck_2250_;
goto v_resetjp_2244_;
}
else
{
lean_inc(v_a_2243_);
lean_dec(v___x_2232_);
v___x_2245_ = lean_box(0);
v_isShared_2246_ = v_isSharedCheck_2250_;
goto v_resetjp_2244_;
}
v_resetjp_2244_:
{
lean_object* v___x_2248_; 
if (v_isShared_2246_ == 0)
{
lean_ctor_set_tag(v___x_2245_, 0);
v___x_2248_ = v___x_2245_;
goto v_reusejp_2247_;
}
else
{
lean_object* v_reuseFailAlloc_2249_; 
v_reuseFailAlloc_2249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2249_, 0, v_a_2243_);
v___x_2248_ = v_reuseFailAlloc_2249_;
goto v_reusejp_2247_;
}
v_reusejp_2247_:
{
return v___x_2248_;
}
}
}
else
{
lean_object* v_a_2251_; lean_object* v___x_2253_; uint8_t v_isShared_2254_; uint8_t v_isSharedCheck_2259_; 
v_a_2251_ = lean_ctor_get(v___x_2232_, 0);
v_isSharedCheck_2259_ = !lean_is_exclusive(v___x_2232_);
if (v_isSharedCheck_2259_ == 0)
{
v___x_2253_ = v___x_2232_;
v_isShared_2254_ = v_isSharedCheck_2259_;
goto v_resetjp_2252_;
}
else
{
lean_inc(v_a_2251_);
lean_dec(v___x_2232_);
v___x_2253_ = lean_box(0);
v_isShared_2254_ = v_isSharedCheck_2259_;
goto v_resetjp_2252_;
}
v_resetjp_2252_:
{
lean_object* v___x_2255_; lean_object* v___x_2257_; 
v___x_2255_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2255_, 0, v_a_2209_);
lean_ctor_set(v___x_2255_, 1, v_a_2230_);
lean_ctor_set(v___x_2255_, 2, v_a_2251_);
if (v_isShared_2254_ == 0)
{
lean_ctor_set(v___x_2253_, 0, v___x_2255_);
v___x_2257_ = v___x_2253_;
goto v_reusejp_2256_;
}
else
{
lean_object* v_reuseFailAlloc_2258_; 
v_reuseFailAlloc_2258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2258_, 0, v___x_2255_);
v___x_2257_ = v_reuseFailAlloc_2258_;
goto v_reusejp_2256_;
}
v_reusejp_2256_:
{
return v___x_2257_;
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
LEAN_EXPORT lean_object* l_Lean_Lsp_DocumentChange_ctorIdx___impl(lean_object* v_x_2262_){
_start:
{
lean_object* v___x_2263_; 
v___x_2263_ = lean_obj_tag_nat(v_x_2262_);
return v___x_2263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DocumentChange_ctorIdx___impl___boxed(lean_object* v_x_2264_){
_start:
{
lean_object* v_res_2265_; 
v_res_2265_ = l_Lean_Lsp_DocumentChange_ctorIdx___impl(v_x_2264_);
lean_dec_ref(v_x_2264_);
return v_res_2265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DocumentChange_ctorElim___redArg(lean_object* v_t_2266_, lean_object* v_k_2267_){
_start:
{
lean_object* v_a_2268_; lean_object* v___x_2269_; 
v_a_2268_ = lean_ctor_get(v_t_2266_, 0);
lean_inc_ref(v_a_2268_);
lean_dec_ref(v_t_2266_);
v___x_2269_ = lean_apply_1(v_k_2267_, v_a_2268_);
return v___x_2269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DocumentChange_ctorElim(lean_object* v_motive_2270_, lean_object* v_ctorIdx_2271_, lean_object* v_t_2272_, lean_object* v_h_2273_, lean_object* v_k_2274_){
_start:
{
lean_object* v___x_2275_; 
v___x_2275_ = l_Lean_Lsp_DocumentChange_ctorElim___redArg(v_t_2272_, v_k_2274_);
return v___x_2275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DocumentChange_ctorElim___boxed(lean_object* v_motive_2276_, lean_object* v_ctorIdx_2277_, lean_object* v_t_2278_, lean_object* v_h_2279_, lean_object* v_k_2280_){
_start:
{
lean_object* v_res_2281_; 
v_res_2281_ = l_Lean_Lsp_DocumentChange_ctorElim(v_motive_2276_, v_ctorIdx_2277_, v_t_2278_, v_h_2279_, v_k_2280_);
lean_dec(v_ctorIdx_2277_);
return v_res_2281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DocumentChange_create_elim___redArg(lean_object* v_t_2282_, lean_object* v_create_2283_){
_start:
{
lean_object* v___x_2284_; 
v___x_2284_ = l_Lean_Lsp_DocumentChange_ctorElim___redArg(v_t_2282_, v_create_2283_);
return v___x_2284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DocumentChange_create_elim(lean_object* v_motive_2285_, lean_object* v_t_2286_, lean_object* v_h_2287_, lean_object* v_create_2288_){
_start:
{
lean_object* v___x_2289_; 
v___x_2289_ = l_Lean_Lsp_DocumentChange_ctorElim___redArg(v_t_2286_, v_create_2288_);
return v___x_2289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DocumentChange_rename_elim___redArg(lean_object* v_t_2290_, lean_object* v_rename_2291_){
_start:
{
lean_object* v___x_2292_; 
v___x_2292_ = l_Lean_Lsp_DocumentChange_ctorElim___redArg(v_t_2290_, v_rename_2291_);
return v___x_2292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DocumentChange_rename_elim(lean_object* v_motive_2293_, lean_object* v_t_2294_, lean_object* v_h_2295_, lean_object* v_rename_2296_){
_start:
{
lean_object* v___x_2297_; 
v___x_2297_ = l_Lean_Lsp_DocumentChange_ctorElim___redArg(v_t_2294_, v_rename_2296_);
return v___x_2297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DocumentChange_delete_elim___redArg(lean_object* v_t_2298_, lean_object* v_delete_2299_){
_start:
{
lean_object* v___x_2300_; 
v___x_2300_ = l_Lean_Lsp_DocumentChange_ctorElim___redArg(v_t_2298_, v_delete_2299_);
return v___x_2300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DocumentChange_delete_elim(lean_object* v_motive_2301_, lean_object* v_t_2302_, lean_object* v_h_2303_, lean_object* v_delete_2304_){
_start:
{
lean_object* v___x_2305_; 
v___x_2305_ = l_Lean_Lsp_DocumentChange_ctorElim___redArg(v_t_2302_, v_delete_2304_);
return v___x_2305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DocumentChange_edit_elim___redArg(lean_object* v_t_2306_, lean_object* v_edit_2307_){
_start:
{
lean_object* v___x_2308_; 
v___x_2308_ = l_Lean_Lsp_DocumentChange_ctorElim___redArg(v_t_2306_, v_edit_2307_);
return v___x_2308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DocumentChange_edit_elim(lean_object* v_motive_2309_, lean_object* v_t_2310_, lean_object* v_h_2311_, lean_object* v_edit_2312_){
_start:
{
lean_object* v___x_2313_; 
v___x_2313_ = l_Lean_Lsp_DocumentChange_ctorElim___redArg(v_t_2310_, v_edit_2312_);
return v___x_2313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDocumentChange___lam__0(lean_object* v_x_2324_){
_start:
{
switch(lean_obj_tag(v_x_2324_))
{
case 0:
{
lean_object* v_a_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; 
v_a_2325_ = lean_ctor_get(v_x_2324_, 0);
lean_inc_ref(v_a_2325_);
lean_dec_ref_known(v_x_2324_, 1);
v___x_2326_ = l_Lean_Lsp_instToJsonCreateFile_toJson(v_a_2325_);
v___x_2327_ = ((lean_object*)(l_Lean_Lsp_instToJsonDocumentChange___lam__0___closed__0));
v___x_2328_ = ((lean_object*)(l_Lean_Lsp_instToJsonDocumentChange___lam__0___closed__2));
v___x_2329_ = l_Lean_Json_setObjVal_x21(v___x_2326_, v___x_2327_, v___x_2328_);
return v___x_2329_;
}
case 1:
{
lean_object* v_a_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; 
v_a_2330_ = lean_ctor_get(v_x_2324_, 0);
lean_inc_ref(v_a_2330_);
lean_dec_ref_known(v_x_2324_, 1);
v___x_2331_ = l_Lean_Lsp_instToJsonRenameFile_toJson(v_a_2330_);
v___x_2332_ = ((lean_object*)(l_Lean_Lsp_instToJsonDocumentChange___lam__0___closed__0));
v___x_2333_ = ((lean_object*)(l_Lean_Lsp_instToJsonDocumentChange___lam__0___closed__4));
v___x_2334_ = l_Lean_Json_setObjVal_x21(v___x_2331_, v___x_2332_, v___x_2333_);
return v___x_2334_;
}
case 2:
{
lean_object* v_a_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; 
v_a_2335_ = lean_ctor_get(v_x_2324_, 0);
lean_inc_ref(v_a_2335_);
lean_dec_ref_known(v_x_2324_, 1);
v___x_2336_ = l_Lean_Lsp_instToJsonDeleteFile_toJson(v_a_2335_);
v___x_2337_ = ((lean_object*)(l_Lean_Lsp_instToJsonDocumentChange___lam__0___closed__0));
v___x_2338_ = ((lean_object*)(l_Lean_Lsp_instToJsonDocumentChange___lam__0___closed__6));
v___x_2339_ = l_Lean_Json_setObjVal_x21(v___x_2336_, v___x_2337_, v___x_2338_);
return v___x_2339_;
}
default: 
{
lean_object* v_a_2340_; lean_object* v___x_2341_; 
v_a_2340_ = lean_ctor_get(v_x_2324_, 0);
lean_inc_ref(v_a_2340_);
lean_dec_ref_known(v_x_2324_, 1);
v___x_2341_ = l_Lean_Lsp_instToJsonTextDocumentEdit_toJson(v_a_2340_);
return v___x_2341_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDocumentChange___lam__0(lean_object* v_kind_2345_){
_start:
{
lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; 
v___x_2346_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDocumentChange___lam__0___closed__0));
v___x_2347_ = lean_unsigned_to_nat(80u);
v___x_2348_ = l_Lean_Json_pretty(v_kind_2345_, v___x_2347_);
v___x_2349_ = lean_string_append(v___x_2346_, v___x_2348_);
lean_dec_ref(v___x_2348_);
v___x_2350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2350_, 0, v___x_2349_);
return v___x_2350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDocumentChange___lam__1(lean_object* v___f_2351_, lean_object* v_j_2352_){
_start:
{
lean_object* v___y_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; 
v___x_2374_ = ((lean_object*)(l_Lean_Lsp_instToJsonDocumentChange___lam__0___closed__0));
lean_inc(v_j_2352_);
v___x_2375_ = l_Lean_Json_getObjVal_x3f(v_j_2352_, v___x_2374_);
if (lean_obj_tag(v___x_2375_) == 0)
{
lean_dec_ref_known(v___x_2375_, 1);
lean_dec_ref(v___f_2351_);
goto v___jp_2353_;
}
else
{
lean_object* v_a_2376_; 
v_a_2376_ = lean_ctor_get(v___x_2375_, 0);
lean_inc(v_a_2376_);
lean_dec_ref_known(v___x_2375_, 1);
if (lean_obj_tag(v_a_2376_) == 3)
{
lean_object* v_s_2377_; lean_object* v___x_2378_; uint8_t v___x_2379_; 
v_s_2377_ = lean_ctor_get(v_a_2376_, 0);
v___x_2378_ = ((lean_object*)(l_Lean_Lsp_instToJsonDocumentChange___lam__0___closed__1));
v___x_2379_ = lean_string_dec_eq(v_s_2377_, v___x_2378_);
if (v___x_2379_ == 0)
{
lean_object* v___x_2380_; uint8_t v___x_2381_; 
v___x_2380_ = ((lean_object*)(l_Lean_Lsp_instToJsonDocumentChange___lam__0___closed__3));
v___x_2381_ = lean_string_dec_eq(v_s_2377_, v___x_2380_);
if (v___x_2381_ == 0)
{
lean_object* v___x_2382_; uint8_t v___x_2383_; 
v___x_2382_ = ((lean_object*)(l_Lean_Lsp_instToJsonDocumentChange___lam__0___closed__5));
v___x_2383_ = lean_string_dec_eq(v_s_2377_, v___x_2382_);
if (v___x_2383_ == 0)
{
lean_object* v___x_2384_; 
v___x_2384_ = lean_apply_1(v___f_2351_, v_a_2376_);
v___y_2373_ = v___x_2384_;
goto v___jp_2372_;
}
else
{
lean_object* v___x_2386_; uint8_t v_isShared_2387_; uint8_t v_isSharedCheck_2400_; 
lean_dec_ref(v___f_2351_);
v_isSharedCheck_2400_ = !lean_is_exclusive(v_a_2376_);
if (v_isSharedCheck_2400_ == 0)
{
lean_object* v_unused_2401_; 
v_unused_2401_ = lean_ctor_get(v_a_2376_, 0);
lean_dec(v_unused_2401_);
v___x_2386_ = v_a_2376_;
v_isShared_2387_ = v_isSharedCheck_2400_;
goto v_resetjp_2385_;
}
else
{
lean_dec(v_a_2376_);
v___x_2386_ = lean_box(0);
v_isShared_2387_ = v_isSharedCheck_2400_;
goto v_resetjp_2385_;
}
v_resetjp_2385_:
{
lean_object* v___x_2388_; 
lean_inc(v_j_2352_);
v___x_2388_ = l_Lean_Lsp_instFromJsonDeleteFile_fromJson(v_j_2352_);
if (lean_obj_tag(v___x_2388_) == 0)
{
lean_dec_ref_known(v___x_2388_, 1);
lean_del_object(v___x_2386_);
goto v___jp_2353_;
}
else
{
lean_object* v_a_2389_; lean_object* v___x_2391_; uint8_t v_isShared_2392_; uint8_t v_isSharedCheck_2399_; 
lean_dec(v_j_2352_);
v_a_2389_ = lean_ctor_get(v___x_2388_, 0);
v_isSharedCheck_2399_ = !lean_is_exclusive(v___x_2388_);
if (v_isSharedCheck_2399_ == 0)
{
v___x_2391_ = v___x_2388_;
v_isShared_2392_ = v_isSharedCheck_2399_;
goto v_resetjp_2390_;
}
else
{
lean_inc(v_a_2389_);
lean_dec(v___x_2388_);
v___x_2391_ = lean_box(0);
v_isShared_2392_ = v_isSharedCheck_2399_;
goto v_resetjp_2390_;
}
v_resetjp_2390_:
{
lean_object* v___x_2394_; 
if (v_isShared_2387_ == 0)
{
lean_ctor_set_tag(v___x_2386_, 2);
lean_ctor_set(v___x_2386_, 0, v_a_2389_);
v___x_2394_ = v___x_2386_;
goto v_reusejp_2393_;
}
else
{
lean_object* v_reuseFailAlloc_2398_; 
v_reuseFailAlloc_2398_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2398_, 0, v_a_2389_);
v___x_2394_ = v_reuseFailAlloc_2398_;
goto v_reusejp_2393_;
}
v_reusejp_2393_:
{
lean_object* v___x_2396_; 
if (v_isShared_2392_ == 0)
{
lean_ctor_set(v___x_2391_, 0, v___x_2394_);
v___x_2396_ = v___x_2391_;
goto v_reusejp_2395_;
}
else
{
lean_object* v_reuseFailAlloc_2397_; 
v_reuseFailAlloc_2397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2397_, 0, v___x_2394_);
v___x_2396_ = v_reuseFailAlloc_2397_;
goto v_reusejp_2395_;
}
v_reusejp_2395_:
{
return v___x_2396_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2403_; uint8_t v_isShared_2404_; uint8_t v_isSharedCheck_2417_; 
lean_dec_ref(v___f_2351_);
v_isSharedCheck_2417_ = !lean_is_exclusive(v_a_2376_);
if (v_isSharedCheck_2417_ == 0)
{
lean_object* v_unused_2418_; 
v_unused_2418_ = lean_ctor_get(v_a_2376_, 0);
lean_dec(v_unused_2418_);
v___x_2403_ = v_a_2376_;
v_isShared_2404_ = v_isSharedCheck_2417_;
goto v_resetjp_2402_;
}
else
{
lean_dec(v_a_2376_);
v___x_2403_ = lean_box(0);
v_isShared_2404_ = v_isSharedCheck_2417_;
goto v_resetjp_2402_;
}
v_resetjp_2402_:
{
lean_object* v___x_2405_; 
lean_inc(v_j_2352_);
v___x_2405_ = l_Lean_Lsp_instFromJsonRenameFile_fromJson(v_j_2352_);
if (lean_obj_tag(v___x_2405_) == 0)
{
lean_dec_ref_known(v___x_2405_, 1);
lean_del_object(v___x_2403_);
goto v___jp_2353_;
}
else
{
lean_object* v_a_2406_; lean_object* v___x_2408_; uint8_t v_isShared_2409_; uint8_t v_isSharedCheck_2416_; 
lean_dec(v_j_2352_);
v_a_2406_ = lean_ctor_get(v___x_2405_, 0);
v_isSharedCheck_2416_ = !lean_is_exclusive(v___x_2405_);
if (v_isSharedCheck_2416_ == 0)
{
v___x_2408_ = v___x_2405_;
v_isShared_2409_ = v_isSharedCheck_2416_;
goto v_resetjp_2407_;
}
else
{
lean_inc(v_a_2406_);
lean_dec(v___x_2405_);
v___x_2408_ = lean_box(0);
v_isShared_2409_ = v_isSharedCheck_2416_;
goto v_resetjp_2407_;
}
v_resetjp_2407_:
{
lean_object* v___x_2411_; 
if (v_isShared_2404_ == 0)
{
lean_ctor_set_tag(v___x_2403_, 1);
lean_ctor_set(v___x_2403_, 0, v_a_2406_);
v___x_2411_ = v___x_2403_;
goto v_reusejp_2410_;
}
else
{
lean_object* v_reuseFailAlloc_2415_; 
v_reuseFailAlloc_2415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2415_, 0, v_a_2406_);
v___x_2411_ = v_reuseFailAlloc_2415_;
goto v_reusejp_2410_;
}
v_reusejp_2410_:
{
lean_object* v___x_2413_; 
if (v_isShared_2409_ == 0)
{
lean_ctor_set(v___x_2408_, 0, v___x_2411_);
v___x_2413_ = v___x_2408_;
goto v_reusejp_2412_;
}
else
{
lean_object* v_reuseFailAlloc_2414_; 
v_reuseFailAlloc_2414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2414_, 0, v___x_2411_);
v___x_2413_ = v_reuseFailAlloc_2414_;
goto v_reusejp_2412_;
}
v_reusejp_2412_:
{
return v___x_2413_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2420_; uint8_t v_isShared_2421_; uint8_t v_isSharedCheck_2434_; 
lean_dec_ref(v___f_2351_);
v_isSharedCheck_2434_ = !lean_is_exclusive(v_a_2376_);
if (v_isSharedCheck_2434_ == 0)
{
lean_object* v_unused_2435_; 
v_unused_2435_ = lean_ctor_get(v_a_2376_, 0);
lean_dec(v_unused_2435_);
v___x_2420_ = v_a_2376_;
v_isShared_2421_ = v_isSharedCheck_2434_;
goto v_resetjp_2419_;
}
else
{
lean_dec(v_a_2376_);
v___x_2420_ = lean_box(0);
v_isShared_2421_ = v_isSharedCheck_2434_;
goto v_resetjp_2419_;
}
v_resetjp_2419_:
{
lean_object* v___x_2422_; 
lean_inc(v_j_2352_);
v___x_2422_ = l_Lean_Lsp_instFromJsonCreateFile_fromJson(v_j_2352_);
if (lean_obj_tag(v___x_2422_) == 0)
{
lean_dec_ref_known(v___x_2422_, 1);
lean_del_object(v___x_2420_);
goto v___jp_2353_;
}
else
{
lean_object* v_a_2423_; lean_object* v___x_2425_; uint8_t v_isShared_2426_; uint8_t v_isSharedCheck_2433_; 
lean_dec(v_j_2352_);
v_a_2423_ = lean_ctor_get(v___x_2422_, 0);
v_isSharedCheck_2433_ = !lean_is_exclusive(v___x_2422_);
if (v_isSharedCheck_2433_ == 0)
{
v___x_2425_ = v___x_2422_;
v_isShared_2426_ = v_isSharedCheck_2433_;
goto v_resetjp_2424_;
}
else
{
lean_inc(v_a_2423_);
lean_dec(v___x_2422_);
v___x_2425_ = lean_box(0);
v_isShared_2426_ = v_isSharedCheck_2433_;
goto v_resetjp_2424_;
}
v_resetjp_2424_:
{
lean_object* v___x_2428_; 
if (v_isShared_2421_ == 0)
{
lean_ctor_set_tag(v___x_2420_, 0);
lean_ctor_set(v___x_2420_, 0, v_a_2423_);
v___x_2428_ = v___x_2420_;
goto v_reusejp_2427_;
}
else
{
lean_object* v_reuseFailAlloc_2432_; 
v_reuseFailAlloc_2432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2432_, 0, v_a_2423_);
v___x_2428_ = v_reuseFailAlloc_2432_;
goto v_reusejp_2427_;
}
v_reusejp_2427_:
{
lean_object* v___x_2430_; 
if (v_isShared_2426_ == 0)
{
lean_ctor_set(v___x_2425_, 0, v___x_2428_);
v___x_2430_ = v___x_2425_;
goto v_reusejp_2429_;
}
else
{
lean_object* v_reuseFailAlloc_2431_; 
v_reuseFailAlloc_2431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2431_, 0, v___x_2428_);
v___x_2430_ = v_reuseFailAlloc_2431_;
goto v_reusejp_2429_;
}
v_reusejp_2429_:
{
return v___x_2430_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2436_; 
v___x_2436_ = lean_apply_1(v___f_2351_, v_a_2376_);
v___y_2373_ = v___x_2436_;
goto v___jp_2372_;
}
}
v___jp_2353_:
{
lean_object* v___x_2354_; 
v___x_2354_ = l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson(v_j_2352_);
if (lean_obj_tag(v___x_2354_) == 0)
{
lean_object* v_a_2355_; lean_object* v___x_2357_; uint8_t v_isShared_2358_; uint8_t v_isSharedCheck_2362_; 
v_a_2355_ = lean_ctor_get(v___x_2354_, 0);
v_isSharedCheck_2362_ = !lean_is_exclusive(v___x_2354_);
if (v_isSharedCheck_2362_ == 0)
{
v___x_2357_ = v___x_2354_;
v_isShared_2358_ = v_isSharedCheck_2362_;
goto v_resetjp_2356_;
}
else
{
lean_inc(v_a_2355_);
lean_dec(v___x_2354_);
v___x_2357_ = lean_box(0);
v_isShared_2358_ = v_isSharedCheck_2362_;
goto v_resetjp_2356_;
}
v_resetjp_2356_:
{
lean_object* v___x_2360_; 
if (v_isShared_2358_ == 0)
{
v___x_2360_ = v___x_2357_;
goto v_reusejp_2359_;
}
else
{
lean_object* v_reuseFailAlloc_2361_; 
v_reuseFailAlloc_2361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2361_, 0, v_a_2355_);
v___x_2360_ = v_reuseFailAlloc_2361_;
goto v_reusejp_2359_;
}
v_reusejp_2359_:
{
return v___x_2360_;
}
}
}
else
{
lean_object* v_a_2363_; lean_object* v___x_2365_; uint8_t v_isShared_2366_; uint8_t v_isSharedCheck_2371_; 
v_a_2363_ = lean_ctor_get(v___x_2354_, 0);
v_isSharedCheck_2371_ = !lean_is_exclusive(v___x_2354_);
if (v_isSharedCheck_2371_ == 0)
{
v___x_2365_ = v___x_2354_;
v_isShared_2366_ = v_isSharedCheck_2371_;
goto v_resetjp_2364_;
}
else
{
lean_inc(v_a_2363_);
lean_dec(v___x_2354_);
v___x_2365_ = lean_box(0);
v_isShared_2366_ = v_isSharedCheck_2371_;
goto v_resetjp_2364_;
}
v_resetjp_2364_:
{
lean_object* v___x_2367_; lean_object* v___x_2369_; 
v___x_2367_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2367_, 0, v_a_2363_);
if (v_isShared_2366_ == 0)
{
lean_ctor_set(v___x_2365_, 0, v___x_2367_);
v___x_2369_ = v___x_2365_;
goto v_reusejp_2368_;
}
else
{
lean_object* v_reuseFailAlloc_2370_; 
v_reuseFailAlloc_2370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2370_, 0, v___x_2367_);
v___x_2369_ = v_reuseFailAlloc_2370_;
goto v_reusejp_2368_;
}
v_reusejp_2368_:
{
return v___x_2369_;
}
}
}
}
v___jp_2372_:
{
if (lean_obj_tag(v___y_2373_) == 0)
{
lean_dec_ref_known(v___y_2373_, 1);
goto v___jp_2353_;
}
else
{
lean_dec(v_j_2352_);
return v___y_2373_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_map___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEdit_toJson_spec__2_spec__4_spec__7(lean_object* v_t_2441_){
_start:
{
if (lean_obj_tag(v_t_2441_) == 0)
{
lean_object* v_size_2442_; lean_object* v_k_2443_; lean_object* v_v_2444_; lean_object* v_l_2445_; lean_object* v_r_2446_; lean_object* v___x_2448_; uint8_t v_isShared_2449_; uint8_t v_isSharedCheck_2456_; 
v_size_2442_ = lean_ctor_get(v_t_2441_, 0);
v_k_2443_ = lean_ctor_get(v_t_2441_, 1);
v_v_2444_ = lean_ctor_get(v_t_2441_, 2);
v_l_2445_ = lean_ctor_get(v_t_2441_, 3);
v_r_2446_ = lean_ctor_get(v_t_2441_, 4);
v_isSharedCheck_2456_ = !lean_is_exclusive(v_t_2441_);
if (v_isSharedCheck_2456_ == 0)
{
v___x_2448_ = v_t_2441_;
v_isShared_2449_ = v_isSharedCheck_2456_;
goto v_resetjp_2447_;
}
else
{
lean_inc(v_r_2446_);
lean_inc(v_l_2445_);
lean_inc(v_v_2444_);
lean_inc(v_k_2443_);
lean_inc(v_size_2442_);
lean_dec(v_t_2441_);
v___x_2448_ = lean_box(0);
v_isShared_2449_ = v_isSharedCheck_2456_;
goto v_resetjp_2447_;
}
v_resetjp_2447_:
{
lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2454_; 
v___x_2450_ = l_Lean_Lsp_instToJsonChangeAnnotation_toJson(v_v_2444_);
v___x_2451_ = l_Std_DTreeMap_Internal_Impl_map___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEdit_toJson_spec__2_spec__4_spec__7(v_l_2445_);
v___x_2452_ = l_Std_DTreeMap_Internal_Impl_map___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEdit_toJson_spec__2_spec__4_spec__7(v_r_2446_);
if (v_isShared_2449_ == 0)
{
lean_ctor_set(v___x_2448_, 4, v___x_2452_);
lean_ctor_set(v___x_2448_, 3, v___x_2451_);
lean_ctor_set(v___x_2448_, 2, v___x_2450_);
v___x_2454_ = v___x_2448_;
goto v_reusejp_2453_;
}
else
{
lean_object* v_reuseFailAlloc_2455_; 
v_reuseFailAlloc_2455_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2455_, 0, v_size_2442_);
lean_ctor_set(v_reuseFailAlloc_2455_, 1, v_k_2443_);
lean_ctor_set(v_reuseFailAlloc_2455_, 2, v___x_2450_);
lean_ctor_set(v_reuseFailAlloc_2455_, 3, v___x_2451_);
lean_ctor_set(v_reuseFailAlloc_2455_, 4, v___x_2452_);
v___x_2454_ = v_reuseFailAlloc_2455_;
goto v_reusejp_2453_;
}
v_reusejp_2453_:
{
return v___x_2454_;
}
}
}
else
{
lean_object* v___x_2457_; 
v___x_2457_ = lean_box(1);
return v___x_2457_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEdit_toJson_spec__2_spec__4(lean_object* v_map_2458_){
_start:
{
lean_object* v___x_2459_; lean_object* v___x_2460_; 
v___x_2459_ = l_Std_DTreeMap_Internal_Impl_map___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEdit_toJson_spec__2_spec__4_spec__7(v_map_2458_);
v___x_2460_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_2460_, 0, v___x_2459_);
return v___x_2460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEdit_toJson_spec__2(lean_object* v_k_2461_, lean_object* v_x_2462_){
_start:
{
if (lean_obj_tag(v_x_2462_) == 0)
{
lean_object* v___x_2463_; 
lean_dec_ref(v_k_2461_);
v___x_2463_ = lean_box(0);
return v___x_2463_;
}
else
{
lean_object* v_val_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; 
v_val_2464_ = lean_ctor_get(v_x_2462_, 0);
lean_inc(v_val_2464_);
lean_dec_ref_known(v_x_2462_, 1);
v___x_2465_ = l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEdit_toJson_spec__2_spec__4(v_val_2464_);
v___x_2466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2466_, 0, v_k_2461_);
lean_ctor_set(v___x_2466_, 1, v___x_2465_);
v___x_2467_ = lean_box(0);
v___x_2468_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2468_, 0, v___x_2466_);
lean_ctor_set(v___x_2468_, 1, v___x_2467_);
return v___x_2468_;
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEdit_toJson_spec__1_spec__2_spec__4(size_t v_sz_2469_, size_t v_i_2470_, lean_object* v_bs_2471_){
_start:
{
uint8_t v___x_2472_; 
v___x_2472_ = lean_usize_dec_lt(v_i_2470_, v_sz_2469_);
if (v___x_2472_ == 0)
{
return v_bs_2471_;
}
else
{
lean_object* v_v_2473_; lean_object* v___x_2474_; lean_object* v_bs_x27_2475_; lean_object* v___y_2477_; 
v_v_2473_ = lean_array_uget(v_bs_2471_, v_i_2470_);
v___x_2474_ = lean_unsigned_to_nat(0u);
v_bs_x27_2475_ = lean_array_uset(v_bs_2471_, v_i_2470_, v___x_2474_);
switch(lean_obj_tag(v_v_2473_))
{
case 0:
{
lean_object* v_a_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; 
v_a_2482_ = lean_ctor_get(v_v_2473_, 0);
lean_inc_ref(v_a_2482_);
lean_dec_ref_known(v_v_2473_, 1);
v___x_2483_ = l_Lean_Lsp_instToJsonCreateFile_toJson(v_a_2482_);
v___x_2484_ = ((lean_object*)(l_Lean_Lsp_instToJsonDocumentChange___lam__0___closed__0));
v___x_2485_ = ((lean_object*)(l_Lean_Lsp_instToJsonDocumentChange___lam__0___closed__2));
v___x_2486_ = l_Lean_Json_setObjVal_x21(v___x_2483_, v___x_2484_, v___x_2485_);
v___y_2477_ = v___x_2486_;
goto v___jp_2476_;
}
case 1:
{
lean_object* v_a_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; 
v_a_2487_ = lean_ctor_get(v_v_2473_, 0);
lean_inc_ref(v_a_2487_);
lean_dec_ref_known(v_v_2473_, 1);
v___x_2488_ = l_Lean_Lsp_instToJsonRenameFile_toJson(v_a_2487_);
v___x_2489_ = ((lean_object*)(l_Lean_Lsp_instToJsonDocumentChange___lam__0___closed__0));
v___x_2490_ = ((lean_object*)(l_Lean_Lsp_instToJsonDocumentChange___lam__0___closed__4));
v___x_2491_ = l_Lean_Json_setObjVal_x21(v___x_2488_, v___x_2489_, v___x_2490_);
v___y_2477_ = v___x_2491_;
goto v___jp_2476_;
}
case 2:
{
lean_object* v_a_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; 
v_a_2492_ = lean_ctor_get(v_v_2473_, 0);
lean_inc_ref(v_a_2492_);
lean_dec_ref_known(v_v_2473_, 1);
v___x_2493_ = l_Lean_Lsp_instToJsonDeleteFile_toJson(v_a_2492_);
v___x_2494_ = ((lean_object*)(l_Lean_Lsp_instToJsonDocumentChange___lam__0___closed__0));
v___x_2495_ = ((lean_object*)(l_Lean_Lsp_instToJsonDocumentChange___lam__0___closed__6));
v___x_2496_ = l_Lean_Json_setObjVal_x21(v___x_2493_, v___x_2494_, v___x_2495_);
v___y_2477_ = v___x_2496_;
goto v___jp_2476_;
}
default: 
{
lean_object* v_a_2497_; lean_object* v___x_2498_; 
v_a_2497_ = lean_ctor_get(v_v_2473_, 0);
lean_inc_ref(v_a_2497_);
lean_dec_ref_known(v_v_2473_, 1);
v___x_2498_ = l_Lean_Lsp_instToJsonTextDocumentEdit_toJson(v_a_2497_);
v___y_2477_ = v___x_2498_;
goto v___jp_2476_;
}
}
v___jp_2476_:
{
size_t v___x_2478_; size_t v___x_2479_; lean_object* v___x_2480_; 
v___x_2478_ = ((size_t)1ULL);
v___x_2479_ = lean_usize_add(v_i_2470_, v___x_2478_);
v___x_2480_ = lean_array_uset(v_bs_x27_2475_, v_i_2470_, v___y_2477_);
v_i_2470_ = v___x_2479_;
v_bs_2471_ = v___x_2480_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEdit_toJson_spec__1_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
size_t v_sz_2469_ = stack[0].m_num;
size_t v_i_2470_ = stack[1].m_num;
lean_object* v_bs_2471_ = stack[2].m_obj;
lean_object* v_res_2499_;
v_res_2499_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEdit_toJson_spec__1_spec__2_spec__4(v_sz_2469_, v_i_2470_, v_bs_2471_);
stack->m_obj
 = v_res_2499_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEdit_toJson_spec__1_spec__2_spec__4___boxed(lean_object* v_sz_2500_, lean_object* v_i_2501_, lean_object* v_bs_2502_){
_start:
{
size_t v_sz_boxed_2503_; size_t v_i_boxed_2504_; lean_object* v_res_2505_; 
v_sz_boxed_2503_ = lean_unbox_usize(v_sz_2500_);
lean_dec(v_sz_2500_);
v_i_boxed_2504_ = lean_unbox_usize(v_i_2501_);
lean_dec(v_i_2501_);
v_res_2505_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEdit_toJson_spec__1_spec__2_spec__4(v_sz_boxed_2503_, v_i_boxed_2504_, v_bs_2502_);
return v_res_2505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEdit_toJson_spec__1_spec__2(lean_object* v_a_2506_){
_start:
{
size_t v_sz_2507_; size_t v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; 
v_sz_2507_ = lean_array_size(v_a_2506_);
v___x_2508_ = ((size_t)0ULL);
v___x_2509_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEdit_toJson_spec__1_spec__2_spec__4(v_sz_2507_, v___x_2508_, v_a_2506_);
v___x_2510_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_2510_, 0, v___x_2509_);
return v___x_2510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEdit_toJson_spec__1(lean_object* v_k_2511_, lean_object* v_x_2512_){
_start:
{
if (lean_obj_tag(v_x_2512_) == 0)
{
lean_object* v___x_2513_; 
lean_dec_ref(v_k_2511_);
v___x_2513_ = lean_box(0);
return v___x_2513_;
}
else
{
lean_object* v_val_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; 
v_val_2514_ = lean_ctor_get(v_x_2512_, 0);
lean_inc(v_val_2514_);
lean_dec_ref_known(v_x_2512_, 1);
v___x_2515_ = l_Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEdit_toJson_spec__1_spec__2(v_val_2514_);
v___x_2516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2516_, 0, v_k_2511_);
lean_ctor_set(v___x_2516_, 1, v___x_2515_);
v___x_2517_ = lean_box(0);
v___x_2518_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2518_, 0, v___x_2516_);
lean_ctor_set(v___x_2518_, 1, v___x_2517_);
return v___x_2518_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_map___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEdit_toJson_spec__0_spec__0_spec__1(lean_object* v_t_2519_){
_start:
{
if (lean_obj_tag(v_t_2519_) == 0)
{
lean_object* v_size_2520_; lean_object* v_k_2521_; lean_object* v_v_2522_; lean_object* v_l_2523_; lean_object* v_r_2524_; lean_object* v___x_2526_; uint8_t v_isShared_2527_; uint8_t v_isSharedCheck_2534_; 
v_size_2520_ = lean_ctor_get(v_t_2519_, 0);
v_k_2521_ = lean_ctor_get(v_t_2519_, 1);
v_v_2522_ = lean_ctor_get(v_t_2519_, 2);
v_l_2523_ = lean_ctor_get(v_t_2519_, 3);
v_r_2524_ = lean_ctor_get(v_t_2519_, 4);
v_isSharedCheck_2534_ = !lean_is_exclusive(v_t_2519_);
if (v_isSharedCheck_2534_ == 0)
{
v___x_2526_ = v_t_2519_;
v_isShared_2527_ = v_isSharedCheck_2534_;
goto v_resetjp_2525_;
}
else
{
lean_inc(v_r_2524_);
lean_inc(v_l_2523_);
lean_inc(v_v_2522_);
lean_inc(v_k_2521_);
lean_inc(v_size_2520_);
lean_dec(v_t_2519_);
v___x_2526_ = lean_box(0);
v_isShared_2527_ = v_isSharedCheck_2534_;
goto v_resetjp_2525_;
}
v_resetjp_2525_:
{
lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2532_; 
v___x_2528_ = l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonTextDocumentEdit_toJson_spec__0(v_v_2522_);
v___x_2529_ = l_Std_DTreeMap_Internal_Impl_map___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEdit_toJson_spec__0_spec__0_spec__1(v_l_2523_);
v___x_2530_ = l_Std_DTreeMap_Internal_Impl_map___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEdit_toJson_spec__0_spec__0_spec__1(v_r_2524_);
if (v_isShared_2527_ == 0)
{
lean_ctor_set(v___x_2526_, 4, v___x_2530_);
lean_ctor_set(v___x_2526_, 3, v___x_2529_);
lean_ctor_set(v___x_2526_, 2, v___x_2528_);
v___x_2532_ = v___x_2526_;
goto v_reusejp_2531_;
}
else
{
lean_object* v_reuseFailAlloc_2533_; 
v_reuseFailAlloc_2533_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2533_, 0, v_size_2520_);
lean_ctor_set(v_reuseFailAlloc_2533_, 1, v_k_2521_);
lean_ctor_set(v_reuseFailAlloc_2533_, 2, v___x_2528_);
lean_ctor_set(v_reuseFailAlloc_2533_, 3, v___x_2529_);
lean_ctor_set(v_reuseFailAlloc_2533_, 4, v___x_2530_);
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
lean_object* v___x_2535_; 
v___x_2535_ = lean_box(1);
return v___x_2535_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEdit_toJson_spec__0_spec__0(lean_object* v_map_2536_){
_start:
{
lean_object* v___x_2537_; lean_object* v___x_2538_; 
v___x_2537_ = l_Std_DTreeMap_Internal_Impl_map___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEdit_toJson_spec__0_spec__0_spec__1(v_map_2536_);
v___x_2538_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_2538_, 0, v___x_2537_);
return v___x_2538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEdit_toJson_spec__0(lean_object* v_k_2539_, lean_object* v_x_2540_){
_start:
{
if (lean_obj_tag(v_x_2540_) == 0)
{
lean_object* v___x_2541_; 
lean_dec_ref(v_k_2539_);
v___x_2541_ = lean_box(0);
return v___x_2541_;
}
else
{
lean_object* v_val_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; 
v_val_2542_ = lean_ctor_get(v_x_2540_, 0);
lean_inc(v_val_2542_);
lean_dec_ref_known(v_x_2540_, 1);
v___x_2543_ = l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEdit_toJson_spec__0_spec__0(v_val_2542_);
v___x_2544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2544_, 0, v_k_2539_);
lean_ctor_set(v___x_2544_, 1, v___x_2543_);
v___x_2545_ = lean_box(0);
v___x_2546_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2546_, 0, v___x_2544_);
lean_ctor_set(v___x_2546_, 1, v___x_2545_);
return v___x_2546_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonWorkspaceEdit_toJson(lean_object* v_x_2550_){
_start:
{
lean_object* v_changes_x3f_2551_; lean_object* v_documentChanges_x3f_2552_; lean_object* v_changeAnnotations_x3f_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; 
v_changes_x3f_2551_ = lean_ctor_get(v_x_2550_, 0);
lean_inc(v_changes_x3f_2551_);
v_documentChanges_x3f_2552_ = lean_ctor_get(v_x_2550_, 1);
lean_inc(v_documentChanges_x3f_2552_);
v_changeAnnotations_x3f_2553_ = lean_ctor_get(v_x_2550_, 2);
lean_inc(v_changeAnnotations_x3f_2553_);
lean_dec_ref(v_x_2550_);
v___x_2554_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkspaceEdit_toJson___closed__0));
v___x_2555_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEdit_toJson_spec__0(v___x_2554_, v_changes_x3f_2551_);
v___x_2556_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkspaceEdit_toJson___closed__1));
v___x_2557_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEdit_toJson_spec__1(v___x_2556_, v_documentChanges_x3f_2552_);
v___x_2558_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkspaceEdit_toJson___closed__2));
v___x_2559_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEdit_toJson_spec__2(v___x_2558_, v_changeAnnotations_x3f_2553_);
v___x_2560_ = lean_box(0);
v___x_2561_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2561_, 0, v___x_2559_);
lean_ctor_set(v___x_2561_, 1, v___x_2560_);
v___x_2562_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2562_, 0, v___x_2557_);
lean_ctor_set(v___x_2562_, 1, v___x_2561_);
v___x_2563_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2563_, 0, v___x_2555_);
lean_ctor_set(v___x_2563_, 1, v___x_2562_);
v___x_2564_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__2));
v___x_2565_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLocation_toJson_spec__0(v___x_2563_, v___x_2564_);
v___x_2566_ = l_Lean_Json_mkObj(v___x_2565_);
lean_dec(v___x_2565_);
return v___x_2566_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__1_spec__2_spec__4_spec__7___redArg(lean_object* v_cmp_2569_, lean_object* v_k_2570_, lean_object* v_v_2571_, lean_object* v_t_2572_){
_start:
{
if (lean_obj_tag(v_t_2572_) == 0)
{
lean_object* v_size_2573_; lean_object* v_k_2574_; lean_object* v_v_2575_; lean_object* v_l_2576_; lean_object* v_r_2577_; lean_object* v___x_2579_; uint8_t v_isShared_2580_; uint8_t v_isSharedCheck_2858_; 
v_size_2573_ = lean_ctor_get(v_t_2572_, 0);
v_k_2574_ = lean_ctor_get(v_t_2572_, 1);
v_v_2575_ = lean_ctor_get(v_t_2572_, 2);
v_l_2576_ = lean_ctor_get(v_t_2572_, 3);
v_r_2577_ = lean_ctor_get(v_t_2572_, 4);
v_isSharedCheck_2858_ = !lean_is_exclusive(v_t_2572_);
if (v_isSharedCheck_2858_ == 0)
{
v___x_2579_ = v_t_2572_;
v_isShared_2580_ = v_isSharedCheck_2858_;
goto v_resetjp_2578_;
}
else
{
lean_inc(v_r_2577_);
lean_inc(v_l_2576_);
lean_inc(v_v_2575_);
lean_inc(v_k_2574_);
lean_inc(v_size_2573_);
lean_dec(v_t_2572_);
v___x_2579_ = lean_box(0);
v_isShared_2580_ = v_isSharedCheck_2858_;
goto v_resetjp_2578_;
}
v_resetjp_2578_:
{
lean_object* v___x_2581_; uint8_t v___x_2582_; 
lean_inc_ref(v_cmp_2569_);
lean_inc(v_k_2574_);
lean_inc_ref(v_k_2570_);
v___x_2581_ = lean_apply_2(v_cmp_2569_, v_k_2570_, v_k_2574_);
v___x_2582_ = lean_unbox(v___x_2581_);
switch(v___x_2582_)
{
case 0:
{
lean_object* v_impl_2583_; lean_object* v___x_2584_; 
lean_dec(v_size_2573_);
v_impl_2583_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__1_spec__2_spec__4_spec__7___redArg(v_cmp_2569_, v_k_2570_, v_v_2571_, v_l_2576_);
v___x_2584_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_2577_) == 0)
{
lean_object* v_size_2585_; lean_object* v_size_2586_; lean_object* v_k_2587_; lean_object* v_v_2588_; lean_object* v_l_2589_; lean_object* v_r_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; uint8_t v___x_2593_; 
v_size_2585_ = lean_ctor_get(v_r_2577_, 0);
v_size_2586_ = lean_ctor_get(v_impl_2583_, 0);
v_k_2587_ = lean_ctor_get(v_impl_2583_, 1);
v_v_2588_ = lean_ctor_get(v_impl_2583_, 2);
v_l_2589_ = lean_ctor_get(v_impl_2583_, 3);
v_r_2590_ = lean_ctor_get(v_impl_2583_, 4);
lean_inc(v_r_2590_);
v___x_2591_ = lean_unsigned_to_nat(3u);
v___x_2592_ = lean_nat_mul(v___x_2591_, v_size_2585_);
v___x_2593_ = lean_nat_dec_lt(v___x_2592_, v_size_2586_);
lean_dec(v___x_2592_);
if (v___x_2593_ == 0)
{
lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2597_; 
lean_dec(v_r_2590_);
v___x_2594_ = lean_nat_add(v___x_2584_, v_size_2586_);
v___x_2595_ = lean_nat_add(v___x_2594_, v_size_2585_);
lean_dec(v___x_2594_);
if (v_isShared_2580_ == 0)
{
lean_ctor_set(v___x_2579_, 3, v_impl_2583_);
lean_ctor_set(v___x_2579_, 0, v___x_2595_);
v___x_2597_ = v___x_2579_;
goto v_reusejp_2596_;
}
else
{
lean_object* v_reuseFailAlloc_2598_; 
v_reuseFailAlloc_2598_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2598_, 0, v___x_2595_);
lean_ctor_set(v_reuseFailAlloc_2598_, 1, v_k_2574_);
lean_ctor_set(v_reuseFailAlloc_2598_, 2, v_v_2575_);
lean_ctor_set(v_reuseFailAlloc_2598_, 3, v_impl_2583_);
lean_ctor_set(v_reuseFailAlloc_2598_, 4, v_r_2577_);
v___x_2597_ = v_reuseFailAlloc_2598_;
goto v_reusejp_2596_;
}
v_reusejp_2596_:
{
return v___x_2597_;
}
}
else
{
lean_object* v___x_2600_; uint8_t v_isShared_2601_; uint8_t v_isSharedCheck_2664_; 
lean_inc(v_l_2589_);
lean_inc(v_v_2588_);
lean_inc(v_k_2587_);
lean_inc(v_size_2586_);
v_isSharedCheck_2664_ = !lean_is_exclusive(v_impl_2583_);
if (v_isSharedCheck_2664_ == 0)
{
lean_object* v_unused_2665_; lean_object* v_unused_2666_; lean_object* v_unused_2667_; lean_object* v_unused_2668_; lean_object* v_unused_2669_; 
v_unused_2665_ = lean_ctor_get(v_impl_2583_, 4);
lean_dec(v_unused_2665_);
v_unused_2666_ = lean_ctor_get(v_impl_2583_, 3);
lean_dec(v_unused_2666_);
v_unused_2667_ = lean_ctor_get(v_impl_2583_, 2);
lean_dec(v_unused_2667_);
v_unused_2668_ = lean_ctor_get(v_impl_2583_, 1);
lean_dec(v_unused_2668_);
v_unused_2669_ = lean_ctor_get(v_impl_2583_, 0);
lean_dec(v_unused_2669_);
v___x_2600_ = v_impl_2583_;
v_isShared_2601_ = v_isSharedCheck_2664_;
goto v_resetjp_2599_;
}
else
{
lean_dec(v_impl_2583_);
v___x_2600_ = lean_box(0);
v_isShared_2601_ = v_isSharedCheck_2664_;
goto v_resetjp_2599_;
}
v_resetjp_2599_:
{
lean_object* v_size_2602_; lean_object* v_size_2603_; lean_object* v_k_2604_; lean_object* v_v_2605_; lean_object* v_l_2606_; lean_object* v_r_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; uint8_t v___x_2610_; 
v_size_2602_ = lean_ctor_get(v_l_2589_, 0);
v_size_2603_ = lean_ctor_get(v_r_2590_, 0);
v_k_2604_ = lean_ctor_get(v_r_2590_, 1);
v_v_2605_ = lean_ctor_get(v_r_2590_, 2);
v_l_2606_ = lean_ctor_get(v_r_2590_, 3);
v_r_2607_ = lean_ctor_get(v_r_2590_, 4);
v___x_2608_ = lean_unsigned_to_nat(2u);
v___x_2609_ = lean_nat_mul(v___x_2608_, v_size_2602_);
v___x_2610_ = lean_nat_dec_lt(v_size_2603_, v___x_2609_);
lean_dec(v___x_2609_);
if (v___x_2610_ == 0)
{
lean_object* v___x_2612_; uint8_t v_isShared_2613_; uint8_t v_isSharedCheck_2639_; 
lean_inc(v_r_2607_);
lean_inc(v_l_2606_);
lean_inc(v_v_2605_);
lean_inc(v_k_2604_);
v_isSharedCheck_2639_ = !lean_is_exclusive(v_r_2590_);
if (v_isSharedCheck_2639_ == 0)
{
lean_object* v_unused_2640_; lean_object* v_unused_2641_; lean_object* v_unused_2642_; lean_object* v_unused_2643_; lean_object* v_unused_2644_; 
v_unused_2640_ = lean_ctor_get(v_r_2590_, 4);
lean_dec(v_unused_2640_);
v_unused_2641_ = lean_ctor_get(v_r_2590_, 3);
lean_dec(v_unused_2641_);
v_unused_2642_ = lean_ctor_get(v_r_2590_, 2);
lean_dec(v_unused_2642_);
v_unused_2643_ = lean_ctor_get(v_r_2590_, 1);
lean_dec(v_unused_2643_);
v_unused_2644_ = lean_ctor_get(v_r_2590_, 0);
lean_dec(v_unused_2644_);
v___x_2612_ = v_r_2590_;
v_isShared_2613_ = v_isSharedCheck_2639_;
goto v_resetjp_2611_;
}
else
{
lean_dec(v_r_2590_);
v___x_2612_ = lean_box(0);
v_isShared_2613_ = v_isSharedCheck_2639_;
goto v_resetjp_2611_;
}
v_resetjp_2611_:
{
lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___y_2617_; lean_object* v___y_2618_; lean_object* v___y_2619_; lean_object* v___x_2627_; lean_object* v___y_2629_; 
v___x_2614_ = lean_nat_add(v___x_2584_, v_size_2586_);
lean_dec(v_size_2586_);
v___x_2615_ = lean_nat_add(v___x_2614_, v_size_2585_);
lean_dec(v___x_2614_);
v___x_2627_ = lean_nat_add(v___x_2584_, v_size_2602_);
if (lean_obj_tag(v_l_2606_) == 0)
{
lean_object* v_size_2637_; 
v_size_2637_ = lean_ctor_get(v_l_2606_, 0);
lean_inc(v_size_2637_);
v___y_2629_ = v_size_2637_;
goto v___jp_2628_;
}
else
{
lean_object* v___x_2638_; 
v___x_2638_ = lean_unsigned_to_nat(0u);
v___y_2629_ = v___x_2638_;
goto v___jp_2628_;
}
v___jp_2616_:
{
lean_object* v___x_2620_; lean_object* v___x_2622_; 
v___x_2620_ = lean_nat_add(v___y_2617_, v___y_2619_);
lean_dec(v___y_2619_);
lean_dec(v___y_2617_);
if (v_isShared_2613_ == 0)
{
lean_ctor_set(v___x_2612_, 4, v_r_2577_);
lean_ctor_set(v___x_2612_, 3, v_r_2607_);
lean_ctor_set(v___x_2612_, 2, v_v_2575_);
lean_ctor_set(v___x_2612_, 1, v_k_2574_);
lean_ctor_set(v___x_2612_, 0, v___x_2620_);
v___x_2622_ = v___x_2612_;
goto v_reusejp_2621_;
}
else
{
lean_object* v_reuseFailAlloc_2626_; 
v_reuseFailAlloc_2626_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2626_, 0, v___x_2620_);
lean_ctor_set(v_reuseFailAlloc_2626_, 1, v_k_2574_);
lean_ctor_set(v_reuseFailAlloc_2626_, 2, v_v_2575_);
lean_ctor_set(v_reuseFailAlloc_2626_, 3, v_r_2607_);
lean_ctor_set(v_reuseFailAlloc_2626_, 4, v_r_2577_);
v___x_2622_ = v_reuseFailAlloc_2626_;
goto v_reusejp_2621_;
}
v_reusejp_2621_:
{
lean_object* v___x_2624_; 
if (v_isShared_2601_ == 0)
{
lean_ctor_set(v___x_2600_, 4, v___x_2622_);
lean_ctor_set(v___x_2600_, 3, v___y_2618_);
lean_ctor_set(v___x_2600_, 2, v_v_2605_);
lean_ctor_set(v___x_2600_, 1, v_k_2604_);
lean_ctor_set(v___x_2600_, 0, v___x_2615_);
v___x_2624_ = v___x_2600_;
goto v_reusejp_2623_;
}
else
{
lean_object* v_reuseFailAlloc_2625_; 
v_reuseFailAlloc_2625_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2625_, 0, v___x_2615_);
lean_ctor_set(v_reuseFailAlloc_2625_, 1, v_k_2604_);
lean_ctor_set(v_reuseFailAlloc_2625_, 2, v_v_2605_);
lean_ctor_set(v_reuseFailAlloc_2625_, 3, v___y_2618_);
lean_ctor_set(v_reuseFailAlloc_2625_, 4, v___x_2622_);
v___x_2624_ = v_reuseFailAlloc_2625_;
goto v_reusejp_2623_;
}
v_reusejp_2623_:
{
return v___x_2624_;
}
}
}
v___jp_2628_:
{
lean_object* v___x_2630_; lean_object* v___x_2632_; 
v___x_2630_ = lean_nat_add(v___x_2627_, v___y_2629_);
lean_dec(v___y_2629_);
lean_dec(v___x_2627_);
if (v_isShared_2580_ == 0)
{
lean_ctor_set(v___x_2579_, 4, v_l_2606_);
lean_ctor_set(v___x_2579_, 3, v_l_2589_);
lean_ctor_set(v___x_2579_, 2, v_v_2588_);
lean_ctor_set(v___x_2579_, 1, v_k_2587_);
lean_ctor_set(v___x_2579_, 0, v___x_2630_);
v___x_2632_ = v___x_2579_;
goto v_reusejp_2631_;
}
else
{
lean_object* v_reuseFailAlloc_2636_; 
v_reuseFailAlloc_2636_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2636_, 0, v___x_2630_);
lean_ctor_set(v_reuseFailAlloc_2636_, 1, v_k_2587_);
lean_ctor_set(v_reuseFailAlloc_2636_, 2, v_v_2588_);
lean_ctor_set(v_reuseFailAlloc_2636_, 3, v_l_2589_);
lean_ctor_set(v_reuseFailAlloc_2636_, 4, v_l_2606_);
v___x_2632_ = v_reuseFailAlloc_2636_;
goto v_reusejp_2631_;
}
v_reusejp_2631_:
{
lean_object* v___x_2633_; 
v___x_2633_ = lean_nat_add(v___x_2584_, v_size_2585_);
if (lean_obj_tag(v_r_2607_) == 0)
{
lean_object* v_size_2634_; 
v_size_2634_ = lean_ctor_get(v_r_2607_, 0);
lean_inc(v_size_2634_);
v___y_2617_ = v___x_2633_;
v___y_2618_ = v___x_2632_;
v___y_2619_ = v_size_2634_;
goto v___jp_2616_;
}
else
{
lean_object* v___x_2635_; 
v___x_2635_ = lean_unsigned_to_nat(0u);
v___y_2617_ = v___x_2633_;
v___y_2618_ = v___x_2632_;
v___y_2619_ = v___x_2635_;
goto v___jp_2616_;
}
}
}
}
}
else
{
lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2650_; 
lean_del_object(v___x_2579_);
v___x_2645_ = lean_nat_add(v___x_2584_, v_size_2586_);
lean_dec(v_size_2586_);
v___x_2646_ = lean_nat_add(v___x_2645_, v_size_2585_);
lean_dec(v___x_2645_);
v___x_2647_ = lean_nat_add(v___x_2584_, v_size_2585_);
v___x_2648_ = lean_nat_add(v___x_2647_, v_size_2603_);
lean_dec(v___x_2647_);
lean_inc_ref(v_r_2577_);
if (v_isShared_2601_ == 0)
{
lean_ctor_set(v___x_2600_, 4, v_r_2577_);
lean_ctor_set(v___x_2600_, 3, v_r_2590_);
lean_ctor_set(v___x_2600_, 2, v_v_2575_);
lean_ctor_set(v___x_2600_, 1, v_k_2574_);
lean_ctor_set(v___x_2600_, 0, v___x_2648_);
v___x_2650_ = v___x_2600_;
goto v_reusejp_2649_;
}
else
{
lean_object* v_reuseFailAlloc_2663_; 
v_reuseFailAlloc_2663_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2663_, 0, v___x_2648_);
lean_ctor_set(v_reuseFailAlloc_2663_, 1, v_k_2574_);
lean_ctor_set(v_reuseFailAlloc_2663_, 2, v_v_2575_);
lean_ctor_set(v_reuseFailAlloc_2663_, 3, v_r_2590_);
lean_ctor_set(v_reuseFailAlloc_2663_, 4, v_r_2577_);
v___x_2650_ = v_reuseFailAlloc_2663_;
goto v_reusejp_2649_;
}
v_reusejp_2649_:
{
lean_object* v___x_2652_; uint8_t v_isShared_2653_; uint8_t v_isSharedCheck_2657_; 
v_isSharedCheck_2657_ = !lean_is_exclusive(v_r_2577_);
if (v_isSharedCheck_2657_ == 0)
{
lean_object* v_unused_2658_; lean_object* v_unused_2659_; lean_object* v_unused_2660_; lean_object* v_unused_2661_; lean_object* v_unused_2662_; 
v_unused_2658_ = lean_ctor_get(v_r_2577_, 4);
lean_dec(v_unused_2658_);
v_unused_2659_ = lean_ctor_get(v_r_2577_, 3);
lean_dec(v_unused_2659_);
v_unused_2660_ = lean_ctor_get(v_r_2577_, 2);
lean_dec(v_unused_2660_);
v_unused_2661_ = lean_ctor_get(v_r_2577_, 1);
lean_dec(v_unused_2661_);
v_unused_2662_ = lean_ctor_get(v_r_2577_, 0);
lean_dec(v_unused_2662_);
v___x_2652_ = v_r_2577_;
v_isShared_2653_ = v_isSharedCheck_2657_;
goto v_resetjp_2651_;
}
else
{
lean_dec(v_r_2577_);
v___x_2652_ = lean_box(0);
v_isShared_2653_ = v_isSharedCheck_2657_;
goto v_resetjp_2651_;
}
v_resetjp_2651_:
{
lean_object* v___x_2655_; 
if (v_isShared_2653_ == 0)
{
lean_ctor_set(v___x_2652_, 4, v___x_2650_);
lean_ctor_set(v___x_2652_, 3, v_l_2589_);
lean_ctor_set(v___x_2652_, 2, v_v_2588_);
lean_ctor_set(v___x_2652_, 1, v_k_2587_);
lean_ctor_set(v___x_2652_, 0, v___x_2646_);
v___x_2655_ = v___x_2652_;
goto v_reusejp_2654_;
}
else
{
lean_object* v_reuseFailAlloc_2656_; 
v_reuseFailAlloc_2656_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2656_, 0, v___x_2646_);
lean_ctor_set(v_reuseFailAlloc_2656_, 1, v_k_2587_);
lean_ctor_set(v_reuseFailAlloc_2656_, 2, v_v_2588_);
lean_ctor_set(v_reuseFailAlloc_2656_, 3, v_l_2589_);
lean_ctor_set(v_reuseFailAlloc_2656_, 4, v___x_2650_);
v___x_2655_ = v_reuseFailAlloc_2656_;
goto v_reusejp_2654_;
}
v_reusejp_2654_:
{
return v___x_2655_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2670_; 
v_l_2670_ = lean_ctor_get(v_impl_2583_, 3);
if (lean_obj_tag(v_l_2670_) == 0)
{
lean_object* v_r_2671_; lean_object* v_k_2672_; lean_object* v_v_2673_; lean_object* v___x_2675_; uint8_t v_isShared_2676_; uint8_t v_isSharedCheck_2684_; 
lean_inc_ref(v_l_2670_);
v_r_2671_ = lean_ctor_get(v_impl_2583_, 4);
v_k_2672_ = lean_ctor_get(v_impl_2583_, 1);
v_v_2673_ = lean_ctor_get(v_impl_2583_, 2);
v_isSharedCheck_2684_ = !lean_is_exclusive(v_impl_2583_);
if (v_isSharedCheck_2684_ == 0)
{
lean_object* v_unused_2685_; lean_object* v_unused_2686_; 
v_unused_2685_ = lean_ctor_get(v_impl_2583_, 3);
lean_dec(v_unused_2685_);
v_unused_2686_ = lean_ctor_get(v_impl_2583_, 0);
lean_dec(v_unused_2686_);
v___x_2675_ = v_impl_2583_;
v_isShared_2676_ = v_isSharedCheck_2684_;
goto v_resetjp_2674_;
}
else
{
lean_inc(v_r_2671_);
lean_inc(v_v_2673_);
lean_inc(v_k_2672_);
lean_dec(v_impl_2583_);
v___x_2675_ = lean_box(0);
v_isShared_2676_ = v_isSharedCheck_2684_;
goto v_resetjp_2674_;
}
v_resetjp_2674_:
{
lean_object* v___x_2677_; lean_object* v___x_2679_; 
v___x_2677_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_2671_);
if (v_isShared_2676_ == 0)
{
lean_ctor_set(v___x_2675_, 3, v_r_2671_);
lean_ctor_set(v___x_2675_, 2, v_v_2575_);
lean_ctor_set(v___x_2675_, 1, v_k_2574_);
lean_ctor_set(v___x_2675_, 0, v___x_2584_);
v___x_2679_ = v___x_2675_;
goto v_reusejp_2678_;
}
else
{
lean_object* v_reuseFailAlloc_2683_; 
v_reuseFailAlloc_2683_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2683_, 0, v___x_2584_);
lean_ctor_set(v_reuseFailAlloc_2683_, 1, v_k_2574_);
lean_ctor_set(v_reuseFailAlloc_2683_, 2, v_v_2575_);
lean_ctor_set(v_reuseFailAlloc_2683_, 3, v_r_2671_);
lean_ctor_set(v_reuseFailAlloc_2683_, 4, v_r_2671_);
v___x_2679_ = v_reuseFailAlloc_2683_;
goto v_reusejp_2678_;
}
v_reusejp_2678_:
{
lean_object* v___x_2681_; 
if (v_isShared_2580_ == 0)
{
lean_ctor_set(v___x_2579_, 4, v___x_2679_);
lean_ctor_set(v___x_2579_, 3, v_l_2670_);
lean_ctor_set(v___x_2579_, 2, v_v_2673_);
lean_ctor_set(v___x_2579_, 1, v_k_2672_);
lean_ctor_set(v___x_2579_, 0, v___x_2677_);
v___x_2681_ = v___x_2579_;
goto v_reusejp_2680_;
}
else
{
lean_object* v_reuseFailAlloc_2682_; 
v_reuseFailAlloc_2682_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2682_, 0, v___x_2677_);
lean_ctor_set(v_reuseFailAlloc_2682_, 1, v_k_2672_);
lean_ctor_set(v_reuseFailAlloc_2682_, 2, v_v_2673_);
lean_ctor_set(v_reuseFailAlloc_2682_, 3, v_l_2670_);
lean_ctor_set(v_reuseFailAlloc_2682_, 4, v___x_2679_);
v___x_2681_ = v_reuseFailAlloc_2682_;
goto v_reusejp_2680_;
}
v_reusejp_2680_:
{
return v___x_2681_;
}
}
}
}
else
{
lean_object* v_r_2687_; 
v_r_2687_ = lean_ctor_get(v_impl_2583_, 4);
lean_inc(v_r_2687_);
if (lean_obj_tag(v_r_2687_) == 0)
{
lean_object* v_k_2688_; lean_object* v_v_2689_; lean_object* v___x_2691_; uint8_t v_isShared_2692_; uint8_t v_isSharedCheck_2712_; 
lean_inc(v_l_2670_);
v_k_2688_ = lean_ctor_get(v_impl_2583_, 1);
v_v_2689_ = lean_ctor_get(v_impl_2583_, 2);
v_isSharedCheck_2712_ = !lean_is_exclusive(v_impl_2583_);
if (v_isSharedCheck_2712_ == 0)
{
lean_object* v_unused_2713_; lean_object* v_unused_2714_; lean_object* v_unused_2715_; 
v_unused_2713_ = lean_ctor_get(v_impl_2583_, 4);
lean_dec(v_unused_2713_);
v_unused_2714_ = lean_ctor_get(v_impl_2583_, 3);
lean_dec(v_unused_2714_);
v_unused_2715_ = lean_ctor_get(v_impl_2583_, 0);
lean_dec(v_unused_2715_);
v___x_2691_ = v_impl_2583_;
v_isShared_2692_ = v_isSharedCheck_2712_;
goto v_resetjp_2690_;
}
else
{
lean_inc(v_v_2689_);
lean_inc(v_k_2688_);
lean_dec(v_impl_2583_);
v___x_2691_ = lean_box(0);
v_isShared_2692_ = v_isSharedCheck_2712_;
goto v_resetjp_2690_;
}
v_resetjp_2690_:
{
lean_object* v_k_2693_; lean_object* v_v_2694_; lean_object* v___x_2696_; uint8_t v_isShared_2697_; uint8_t v_isSharedCheck_2708_; 
v_k_2693_ = lean_ctor_get(v_r_2687_, 1);
v_v_2694_ = lean_ctor_get(v_r_2687_, 2);
v_isSharedCheck_2708_ = !lean_is_exclusive(v_r_2687_);
if (v_isSharedCheck_2708_ == 0)
{
lean_object* v_unused_2709_; lean_object* v_unused_2710_; lean_object* v_unused_2711_; 
v_unused_2709_ = lean_ctor_get(v_r_2687_, 4);
lean_dec(v_unused_2709_);
v_unused_2710_ = lean_ctor_get(v_r_2687_, 3);
lean_dec(v_unused_2710_);
v_unused_2711_ = lean_ctor_get(v_r_2687_, 0);
lean_dec(v_unused_2711_);
v___x_2696_ = v_r_2687_;
v_isShared_2697_ = v_isSharedCheck_2708_;
goto v_resetjp_2695_;
}
else
{
lean_inc(v_v_2694_);
lean_inc(v_k_2693_);
lean_dec(v_r_2687_);
v___x_2696_ = lean_box(0);
v_isShared_2697_ = v_isSharedCheck_2708_;
goto v_resetjp_2695_;
}
v_resetjp_2695_:
{
lean_object* v___x_2698_; lean_object* v___x_2700_; 
v___x_2698_ = lean_unsigned_to_nat(3u);
if (v_isShared_2697_ == 0)
{
lean_ctor_set(v___x_2696_, 4, v_l_2670_);
lean_ctor_set(v___x_2696_, 3, v_l_2670_);
lean_ctor_set(v___x_2696_, 2, v_v_2689_);
lean_ctor_set(v___x_2696_, 1, v_k_2688_);
lean_ctor_set(v___x_2696_, 0, v___x_2584_);
v___x_2700_ = v___x_2696_;
goto v_reusejp_2699_;
}
else
{
lean_object* v_reuseFailAlloc_2707_; 
v_reuseFailAlloc_2707_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2707_, 0, v___x_2584_);
lean_ctor_set(v_reuseFailAlloc_2707_, 1, v_k_2688_);
lean_ctor_set(v_reuseFailAlloc_2707_, 2, v_v_2689_);
lean_ctor_set(v_reuseFailAlloc_2707_, 3, v_l_2670_);
lean_ctor_set(v_reuseFailAlloc_2707_, 4, v_l_2670_);
v___x_2700_ = v_reuseFailAlloc_2707_;
goto v_reusejp_2699_;
}
v_reusejp_2699_:
{
lean_object* v___x_2702_; 
if (v_isShared_2692_ == 0)
{
lean_ctor_set(v___x_2691_, 4, v_l_2670_);
lean_ctor_set(v___x_2691_, 2, v_v_2575_);
lean_ctor_set(v___x_2691_, 1, v_k_2574_);
lean_ctor_set(v___x_2691_, 0, v___x_2584_);
v___x_2702_ = v___x_2691_;
goto v_reusejp_2701_;
}
else
{
lean_object* v_reuseFailAlloc_2706_; 
v_reuseFailAlloc_2706_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2706_, 0, v___x_2584_);
lean_ctor_set(v_reuseFailAlloc_2706_, 1, v_k_2574_);
lean_ctor_set(v_reuseFailAlloc_2706_, 2, v_v_2575_);
lean_ctor_set(v_reuseFailAlloc_2706_, 3, v_l_2670_);
lean_ctor_set(v_reuseFailAlloc_2706_, 4, v_l_2670_);
v___x_2702_ = v_reuseFailAlloc_2706_;
goto v_reusejp_2701_;
}
v_reusejp_2701_:
{
lean_object* v___x_2704_; 
if (v_isShared_2580_ == 0)
{
lean_ctor_set(v___x_2579_, 4, v___x_2702_);
lean_ctor_set(v___x_2579_, 3, v___x_2700_);
lean_ctor_set(v___x_2579_, 2, v_v_2694_);
lean_ctor_set(v___x_2579_, 1, v_k_2693_);
lean_ctor_set(v___x_2579_, 0, v___x_2698_);
v___x_2704_ = v___x_2579_;
goto v_reusejp_2703_;
}
else
{
lean_object* v_reuseFailAlloc_2705_; 
v_reuseFailAlloc_2705_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2705_, 0, v___x_2698_);
lean_ctor_set(v_reuseFailAlloc_2705_, 1, v_k_2693_);
lean_ctor_set(v_reuseFailAlloc_2705_, 2, v_v_2694_);
lean_ctor_set(v_reuseFailAlloc_2705_, 3, v___x_2700_);
lean_ctor_set(v_reuseFailAlloc_2705_, 4, v___x_2702_);
v___x_2704_ = v_reuseFailAlloc_2705_;
goto v_reusejp_2703_;
}
v_reusejp_2703_:
{
return v___x_2704_;
}
}
}
}
}
}
else
{
lean_object* v___x_2716_; lean_object* v___x_2718_; 
v___x_2716_ = lean_unsigned_to_nat(2u);
if (v_isShared_2580_ == 0)
{
lean_ctor_set(v___x_2579_, 4, v_r_2687_);
lean_ctor_set(v___x_2579_, 3, v_impl_2583_);
lean_ctor_set(v___x_2579_, 0, v___x_2716_);
v___x_2718_ = v___x_2579_;
goto v_reusejp_2717_;
}
else
{
lean_object* v_reuseFailAlloc_2719_; 
v_reuseFailAlloc_2719_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2719_, 0, v___x_2716_);
lean_ctor_set(v_reuseFailAlloc_2719_, 1, v_k_2574_);
lean_ctor_set(v_reuseFailAlloc_2719_, 2, v_v_2575_);
lean_ctor_set(v_reuseFailAlloc_2719_, 3, v_impl_2583_);
lean_ctor_set(v_reuseFailAlloc_2719_, 4, v_r_2687_);
v___x_2718_ = v_reuseFailAlloc_2719_;
goto v_reusejp_2717_;
}
v_reusejp_2717_:
{
return v___x_2718_;
}
}
}
}
}
case 1:
{
lean_object* v___x_2721_; 
lean_dec(v_v_2575_);
lean_dec(v_k_2574_);
lean_dec_ref(v_cmp_2569_);
if (v_isShared_2580_ == 0)
{
lean_ctor_set(v___x_2579_, 2, v_v_2571_);
lean_ctor_set(v___x_2579_, 1, v_k_2570_);
v___x_2721_ = v___x_2579_;
goto v_reusejp_2720_;
}
else
{
lean_object* v_reuseFailAlloc_2722_; 
v_reuseFailAlloc_2722_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2722_, 0, v_size_2573_);
lean_ctor_set(v_reuseFailAlloc_2722_, 1, v_k_2570_);
lean_ctor_set(v_reuseFailAlloc_2722_, 2, v_v_2571_);
lean_ctor_set(v_reuseFailAlloc_2722_, 3, v_l_2576_);
lean_ctor_set(v_reuseFailAlloc_2722_, 4, v_r_2577_);
v___x_2721_ = v_reuseFailAlloc_2722_;
goto v_reusejp_2720_;
}
v_reusejp_2720_:
{
return v___x_2721_;
}
}
default: 
{
lean_object* v_impl_2723_; lean_object* v___x_2724_; 
lean_dec(v_size_2573_);
v_impl_2723_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__1_spec__2_spec__4_spec__7___redArg(v_cmp_2569_, v_k_2570_, v_v_2571_, v_r_2577_);
v___x_2724_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_2576_) == 0)
{
lean_object* v_size_2725_; lean_object* v_size_2726_; lean_object* v_k_2727_; lean_object* v_v_2728_; lean_object* v_l_2729_; lean_object* v_r_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; uint8_t v___x_2733_; 
v_size_2725_ = lean_ctor_get(v_l_2576_, 0);
v_size_2726_ = lean_ctor_get(v_impl_2723_, 0);
v_k_2727_ = lean_ctor_get(v_impl_2723_, 1);
v_v_2728_ = lean_ctor_get(v_impl_2723_, 2);
v_l_2729_ = lean_ctor_get(v_impl_2723_, 3);
lean_inc(v_l_2729_);
v_r_2730_ = lean_ctor_get(v_impl_2723_, 4);
v___x_2731_ = lean_unsigned_to_nat(3u);
v___x_2732_ = lean_nat_mul(v___x_2731_, v_size_2725_);
v___x_2733_ = lean_nat_dec_lt(v___x_2732_, v_size_2726_);
lean_dec(v___x_2732_);
if (v___x_2733_ == 0)
{
lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2737_; 
lean_dec(v_l_2729_);
v___x_2734_ = lean_nat_add(v___x_2724_, v_size_2725_);
v___x_2735_ = lean_nat_add(v___x_2734_, v_size_2726_);
lean_dec(v___x_2734_);
if (v_isShared_2580_ == 0)
{
lean_ctor_set(v___x_2579_, 4, v_impl_2723_);
lean_ctor_set(v___x_2579_, 0, v___x_2735_);
v___x_2737_ = v___x_2579_;
goto v_reusejp_2736_;
}
else
{
lean_object* v_reuseFailAlloc_2738_; 
v_reuseFailAlloc_2738_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2738_, 0, v___x_2735_);
lean_ctor_set(v_reuseFailAlloc_2738_, 1, v_k_2574_);
lean_ctor_set(v_reuseFailAlloc_2738_, 2, v_v_2575_);
lean_ctor_set(v_reuseFailAlloc_2738_, 3, v_l_2576_);
lean_ctor_set(v_reuseFailAlloc_2738_, 4, v_impl_2723_);
v___x_2737_ = v_reuseFailAlloc_2738_;
goto v_reusejp_2736_;
}
v_reusejp_2736_:
{
return v___x_2737_;
}
}
else
{
lean_object* v___x_2740_; uint8_t v_isShared_2741_; uint8_t v_isSharedCheck_2802_; 
lean_inc(v_r_2730_);
lean_inc(v_v_2728_);
lean_inc(v_k_2727_);
lean_inc(v_size_2726_);
v_isSharedCheck_2802_ = !lean_is_exclusive(v_impl_2723_);
if (v_isSharedCheck_2802_ == 0)
{
lean_object* v_unused_2803_; lean_object* v_unused_2804_; lean_object* v_unused_2805_; lean_object* v_unused_2806_; lean_object* v_unused_2807_; 
v_unused_2803_ = lean_ctor_get(v_impl_2723_, 4);
lean_dec(v_unused_2803_);
v_unused_2804_ = lean_ctor_get(v_impl_2723_, 3);
lean_dec(v_unused_2804_);
v_unused_2805_ = lean_ctor_get(v_impl_2723_, 2);
lean_dec(v_unused_2805_);
v_unused_2806_ = lean_ctor_get(v_impl_2723_, 1);
lean_dec(v_unused_2806_);
v_unused_2807_ = lean_ctor_get(v_impl_2723_, 0);
lean_dec(v_unused_2807_);
v___x_2740_ = v_impl_2723_;
v_isShared_2741_ = v_isSharedCheck_2802_;
goto v_resetjp_2739_;
}
else
{
lean_dec(v_impl_2723_);
v___x_2740_ = lean_box(0);
v_isShared_2741_ = v_isSharedCheck_2802_;
goto v_resetjp_2739_;
}
v_resetjp_2739_:
{
lean_object* v_size_2742_; lean_object* v_k_2743_; lean_object* v_v_2744_; lean_object* v_l_2745_; lean_object* v_r_2746_; lean_object* v_size_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; uint8_t v___x_2750_; 
v_size_2742_ = lean_ctor_get(v_l_2729_, 0);
v_k_2743_ = lean_ctor_get(v_l_2729_, 1);
v_v_2744_ = lean_ctor_get(v_l_2729_, 2);
v_l_2745_ = lean_ctor_get(v_l_2729_, 3);
v_r_2746_ = lean_ctor_get(v_l_2729_, 4);
v_size_2747_ = lean_ctor_get(v_r_2730_, 0);
v___x_2748_ = lean_unsigned_to_nat(2u);
v___x_2749_ = lean_nat_mul(v___x_2748_, v_size_2747_);
v___x_2750_ = lean_nat_dec_lt(v_size_2742_, v___x_2749_);
lean_dec(v___x_2749_);
if (v___x_2750_ == 0)
{
lean_object* v___x_2752_; uint8_t v_isShared_2753_; uint8_t v_isSharedCheck_2778_; 
lean_inc(v_r_2746_);
lean_inc(v_l_2745_);
lean_inc(v_v_2744_);
lean_inc(v_k_2743_);
v_isSharedCheck_2778_ = !lean_is_exclusive(v_l_2729_);
if (v_isSharedCheck_2778_ == 0)
{
lean_object* v_unused_2779_; lean_object* v_unused_2780_; lean_object* v_unused_2781_; lean_object* v_unused_2782_; lean_object* v_unused_2783_; 
v_unused_2779_ = lean_ctor_get(v_l_2729_, 4);
lean_dec(v_unused_2779_);
v_unused_2780_ = lean_ctor_get(v_l_2729_, 3);
lean_dec(v_unused_2780_);
v_unused_2781_ = lean_ctor_get(v_l_2729_, 2);
lean_dec(v_unused_2781_);
v_unused_2782_ = lean_ctor_get(v_l_2729_, 1);
lean_dec(v_unused_2782_);
v_unused_2783_ = lean_ctor_get(v_l_2729_, 0);
lean_dec(v_unused_2783_);
v___x_2752_ = v_l_2729_;
v_isShared_2753_ = v_isSharedCheck_2778_;
goto v_resetjp_2751_;
}
else
{
lean_dec(v_l_2729_);
v___x_2752_ = lean_box(0);
v_isShared_2753_ = v_isSharedCheck_2778_;
goto v_resetjp_2751_;
}
v_resetjp_2751_:
{
lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___y_2757_; lean_object* v___y_2758_; lean_object* v___y_2759_; lean_object* v___y_2768_; 
v___x_2754_ = lean_nat_add(v___x_2724_, v_size_2725_);
v___x_2755_ = lean_nat_add(v___x_2754_, v_size_2726_);
lean_dec(v_size_2726_);
if (lean_obj_tag(v_l_2745_) == 0)
{
lean_object* v_size_2776_; 
v_size_2776_ = lean_ctor_get(v_l_2745_, 0);
lean_inc(v_size_2776_);
v___y_2768_ = v_size_2776_;
goto v___jp_2767_;
}
else
{
lean_object* v___x_2777_; 
v___x_2777_ = lean_unsigned_to_nat(0u);
v___y_2768_ = v___x_2777_;
goto v___jp_2767_;
}
v___jp_2756_:
{
lean_object* v___x_2760_; lean_object* v___x_2762_; 
v___x_2760_ = lean_nat_add(v___y_2757_, v___y_2759_);
lean_dec(v___y_2759_);
lean_dec(v___y_2757_);
if (v_isShared_2753_ == 0)
{
lean_ctor_set(v___x_2752_, 4, v_r_2730_);
lean_ctor_set(v___x_2752_, 3, v_r_2746_);
lean_ctor_set(v___x_2752_, 2, v_v_2728_);
lean_ctor_set(v___x_2752_, 1, v_k_2727_);
lean_ctor_set(v___x_2752_, 0, v___x_2760_);
v___x_2762_ = v___x_2752_;
goto v_reusejp_2761_;
}
else
{
lean_object* v_reuseFailAlloc_2766_; 
v_reuseFailAlloc_2766_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2766_, 0, v___x_2760_);
lean_ctor_set(v_reuseFailAlloc_2766_, 1, v_k_2727_);
lean_ctor_set(v_reuseFailAlloc_2766_, 2, v_v_2728_);
lean_ctor_set(v_reuseFailAlloc_2766_, 3, v_r_2746_);
lean_ctor_set(v_reuseFailAlloc_2766_, 4, v_r_2730_);
v___x_2762_ = v_reuseFailAlloc_2766_;
goto v_reusejp_2761_;
}
v_reusejp_2761_:
{
lean_object* v___x_2764_; 
if (v_isShared_2741_ == 0)
{
lean_ctor_set(v___x_2740_, 4, v___x_2762_);
lean_ctor_set(v___x_2740_, 3, v___y_2758_);
lean_ctor_set(v___x_2740_, 2, v_v_2744_);
lean_ctor_set(v___x_2740_, 1, v_k_2743_);
lean_ctor_set(v___x_2740_, 0, v___x_2755_);
v___x_2764_ = v___x_2740_;
goto v_reusejp_2763_;
}
else
{
lean_object* v_reuseFailAlloc_2765_; 
v_reuseFailAlloc_2765_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2765_, 0, v___x_2755_);
lean_ctor_set(v_reuseFailAlloc_2765_, 1, v_k_2743_);
lean_ctor_set(v_reuseFailAlloc_2765_, 2, v_v_2744_);
lean_ctor_set(v_reuseFailAlloc_2765_, 3, v___y_2758_);
lean_ctor_set(v_reuseFailAlloc_2765_, 4, v___x_2762_);
v___x_2764_ = v_reuseFailAlloc_2765_;
goto v_reusejp_2763_;
}
v_reusejp_2763_:
{
return v___x_2764_;
}
}
}
v___jp_2767_:
{
lean_object* v___x_2769_; lean_object* v___x_2771_; 
v___x_2769_ = lean_nat_add(v___x_2754_, v___y_2768_);
lean_dec(v___y_2768_);
lean_dec(v___x_2754_);
if (v_isShared_2580_ == 0)
{
lean_ctor_set(v___x_2579_, 4, v_l_2745_);
lean_ctor_set(v___x_2579_, 0, v___x_2769_);
v___x_2771_ = v___x_2579_;
goto v_reusejp_2770_;
}
else
{
lean_object* v_reuseFailAlloc_2775_; 
v_reuseFailAlloc_2775_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2775_, 0, v___x_2769_);
lean_ctor_set(v_reuseFailAlloc_2775_, 1, v_k_2574_);
lean_ctor_set(v_reuseFailAlloc_2775_, 2, v_v_2575_);
lean_ctor_set(v_reuseFailAlloc_2775_, 3, v_l_2576_);
lean_ctor_set(v_reuseFailAlloc_2775_, 4, v_l_2745_);
v___x_2771_ = v_reuseFailAlloc_2775_;
goto v_reusejp_2770_;
}
v_reusejp_2770_:
{
lean_object* v___x_2772_; 
v___x_2772_ = lean_nat_add(v___x_2724_, v_size_2747_);
if (lean_obj_tag(v_r_2746_) == 0)
{
lean_object* v_size_2773_; 
v_size_2773_ = lean_ctor_get(v_r_2746_, 0);
lean_inc(v_size_2773_);
v___y_2757_ = v___x_2772_;
v___y_2758_ = v___x_2771_;
v___y_2759_ = v_size_2773_;
goto v___jp_2756_;
}
else
{
lean_object* v___x_2774_; 
v___x_2774_ = lean_unsigned_to_nat(0u);
v___y_2757_ = v___x_2772_;
v___y_2758_ = v___x_2771_;
v___y_2759_ = v___x_2774_;
goto v___jp_2756_;
}
}
}
}
}
else
{
lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2788_; 
lean_del_object(v___x_2579_);
v___x_2784_ = lean_nat_add(v___x_2724_, v_size_2725_);
v___x_2785_ = lean_nat_add(v___x_2784_, v_size_2726_);
lean_dec(v_size_2726_);
v___x_2786_ = lean_nat_add(v___x_2784_, v_size_2742_);
lean_dec(v___x_2784_);
lean_inc_ref(v_l_2576_);
if (v_isShared_2741_ == 0)
{
lean_ctor_set(v___x_2740_, 4, v_l_2729_);
lean_ctor_set(v___x_2740_, 3, v_l_2576_);
lean_ctor_set(v___x_2740_, 2, v_v_2575_);
lean_ctor_set(v___x_2740_, 1, v_k_2574_);
lean_ctor_set(v___x_2740_, 0, v___x_2786_);
v___x_2788_ = v___x_2740_;
goto v_reusejp_2787_;
}
else
{
lean_object* v_reuseFailAlloc_2801_; 
v_reuseFailAlloc_2801_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2801_, 0, v___x_2786_);
lean_ctor_set(v_reuseFailAlloc_2801_, 1, v_k_2574_);
lean_ctor_set(v_reuseFailAlloc_2801_, 2, v_v_2575_);
lean_ctor_set(v_reuseFailAlloc_2801_, 3, v_l_2576_);
lean_ctor_set(v_reuseFailAlloc_2801_, 4, v_l_2729_);
v___x_2788_ = v_reuseFailAlloc_2801_;
goto v_reusejp_2787_;
}
v_reusejp_2787_:
{
lean_object* v___x_2790_; uint8_t v_isShared_2791_; uint8_t v_isSharedCheck_2795_; 
v_isSharedCheck_2795_ = !lean_is_exclusive(v_l_2576_);
if (v_isSharedCheck_2795_ == 0)
{
lean_object* v_unused_2796_; lean_object* v_unused_2797_; lean_object* v_unused_2798_; lean_object* v_unused_2799_; lean_object* v_unused_2800_; 
v_unused_2796_ = lean_ctor_get(v_l_2576_, 4);
lean_dec(v_unused_2796_);
v_unused_2797_ = lean_ctor_get(v_l_2576_, 3);
lean_dec(v_unused_2797_);
v_unused_2798_ = lean_ctor_get(v_l_2576_, 2);
lean_dec(v_unused_2798_);
v_unused_2799_ = lean_ctor_get(v_l_2576_, 1);
lean_dec(v_unused_2799_);
v_unused_2800_ = lean_ctor_get(v_l_2576_, 0);
lean_dec(v_unused_2800_);
v___x_2790_ = v_l_2576_;
v_isShared_2791_ = v_isSharedCheck_2795_;
goto v_resetjp_2789_;
}
else
{
lean_dec(v_l_2576_);
v___x_2790_ = lean_box(0);
v_isShared_2791_ = v_isSharedCheck_2795_;
goto v_resetjp_2789_;
}
v_resetjp_2789_:
{
lean_object* v___x_2793_; 
if (v_isShared_2791_ == 0)
{
lean_ctor_set(v___x_2790_, 4, v_r_2730_);
lean_ctor_set(v___x_2790_, 3, v___x_2788_);
lean_ctor_set(v___x_2790_, 2, v_v_2728_);
lean_ctor_set(v___x_2790_, 1, v_k_2727_);
lean_ctor_set(v___x_2790_, 0, v___x_2785_);
v___x_2793_ = v___x_2790_;
goto v_reusejp_2792_;
}
else
{
lean_object* v_reuseFailAlloc_2794_; 
v_reuseFailAlloc_2794_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2794_, 0, v___x_2785_);
lean_ctor_set(v_reuseFailAlloc_2794_, 1, v_k_2727_);
lean_ctor_set(v_reuseFailAlloc_2794_, 2, v_v_2728_);
lean_ctor_set(v_reuseFailAlloc_2794_, 3, v___x_2788_);
lean_ctor_set(v_reuseFailAlloc_2794_, 4, v_r_2730_);
v___x_2793_ = v_reuseFailAlloc_2794_;
goto v_reusejp_2792_;
}
v_reusejp_2792_:
{
return v___x_2793_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2808_; 
v_l_2808_ = lean_ctor_get(v_impl_2723_, 3);
lean_inc(v_l_2808_);
if (lean_obj_tag(v_l_2808_) == 0)
{
lean_object* v_r_2809_; lean_object* v_k_2810_; lean_object* v_v_2811_; lean_object* v___x_2813_; uint8_t v_isShared_2814_; uint8_t v_isSharedCheck_2834_; 
v_r_2809_ = lean_ctor_get(v_impl_2723_, 4);
v_k_2810_ = lean_ctor_get(v_impl_2723_, 1);
v_v_2811_ = lean_ctor_get(v_impl_2723_, 2);
v_isSharedCheck_2834_ = !lean_is_exclusive(v_impl_2723_);
if (v_isSharedCheck_2834_ == 0)
{
lean_object* v_unused_2835_; lean_object* v_unused_2836_; 
v_unused_2835_ = lean_ctor_get(v_impl_2723_, 3);
lean_dec(v_unused_2835_);
v_unused_2836_ = lean_ctor_get(v_impl_2723_, 0);
lean_dec(v_unused_2836_);
v___x_2813_ = v_impl_2723_;
v_isShared_2814_ = v_isSharedCheck_2834_;
goto v_resetjp_2812_;
}
else
{
lean_inc(v_r_2809_);
lean_inc(v_v_2811_);
lean_inc(v_k_2810_);
lean_dec(v_impl_2723_);
v___x_2813_ = lean_box(0);
v_isShared_2814_ = v_isSharedCheck_2834_;
goto v_resetjp_2812_;
}
v_resetjp_2812_:
{
lean_object* v_k_2815_; lean_object* v_v_2816_; lean_object* v___x_2818_; uint8_t v_isShared_2819_; uint8_t v_isSharedCheck_2830_; 
v_k_2815_ = lean_ctor_get(v_l_2808_, 1);
v_v_2816_ = lean_ctor_get(v_l_2808_, 2);
v_isSharedCheck_2830_ = !lean_is_exclusive(v_l_2808_);
if (v_isSharedCheck_2830_ == 0)
{
lean_object* v_unused_2831_; lean_object* v_unused_2832_; lean_object* v_unused_2833_; 
v_unused_2831_ = lean_ctor_get(v_l_2808_, 4);
lean_dec(v_unused_2831_);
v_unused_2832_ = lean_ctor_get(v_l_2808_, 3);
lean_dec(v_unused_2832_);
v_unused_2833_ = lean_ctor_get(v_l_2808_, 0);
lean_dec(v_unused_2833_);
v___x_2818_ = v_l_2808_;
v_isShared_2819_ = v_isSharedCheck_2830_;
goto v_resetjp_2817_;
}
else
{
lean_inc(v_v_2816_);
lean_inc(v_k_2815_);
lean_dec(v_l_2808_);
v___x_2818_ = lean_box(0);
v_isShared_2819_ = v_isSharedCheck_2830_;
goto v_resetjp_2817_;
}
v_resetjp_2817_:
{
lean_object* v___x_2820_; lean_object* v___x_2822_; 
v___x_2820_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_2809_, 2);
if (v_isShared_2819_ == 0)
{
lean_ctor_set(v___x_2818_, 4, v_r_2809_);
lean_ctor_set(v___x_2818_, 3, v_r_2809_);
lean_ctor_set(v___x_2818_, 2, v_v_2575_);
lean_ctor_set(v___x_2818_, 1, v_k_2574_);
lean_ctor_set(v___x_2818_, 0, v___x_2724_);
v___x_2822_ = v___x_2818_;
goto v_reusejp_2821_;
}
else
{
lean_object* v_reuseFailAlloc_2829_; 
v_reuseFailAlloc_2829_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2829_, 0, v___x_2724_);
lean_ctor_set(v_reuseFailAlloc_2829_, 1, v_k_2574_);
lean_ctor_set(v_reuseFailAlloc_2829_, 2, v_v_2575_);
lean_ctor_set(v_reuseFailAlloc_2829_, 3, v_r_2809_);
lean_ctor_set(v_reuseFailAlloc_2829_, 4, v_r_2809_);
v___x_2822_ = v_reuseFailAlloc_2829_;
goto v_reusejp_2821_;
}
v_reusejp_2821_:
{
lean_object* v___x_2824_; 
lean_inc(v_r_2809_);
if (v_isShared_2814_ == 0)
{
lean_ctor_set(v___x_2813_, 3, v_r_2809_);
lean_ctor_set(v___x_2813_, 0, v___x_2724_);
v___x_2824_ = v___x_2813_;
goto v_reusejp_2823_;
}
else
{
lean_object* v_reuseFailAlloc_2828_; 
v_reuseFailAlloc_2828_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2828_, 0, v___x_2724_);
lean_ctor_set(v_reuseFailAlloc_2828_, 1, v_k_2810_);
lean_ctor_set(v_reuseFailAlloc_2828_, 2, v_v_2811_);
lean_ctor_set(v_reuseFailAlloc_2828_, 3, v_r_2809_);
lean_ctor_set(v_reuseFailAlloc_2828_, 4, v_r_2809_);
v___x_2824_ = v_reuseFailAlloc_2828_;
goto v_reusejp_2823_;
}
v_reusejp_2823_:
{
lean_object* v___x_2826_; 
if (v_isShared_2580_ == 0)
{
lean_ctor_set(v___x_2579_, 4, v___x_2824_);
lean_ctor_set(v___x_2579_, 3, v___x_2822_);
lean_ctor_set(v___x_2579_, 2, v_v_2816_);
lean_ctor_set(v___x_2579_, 1, v_k_2815_);
lean_ctor_set(v___x_2579_, 0, v___x_2820_);
v___x_2826_ = v___x_2579_;
goto v_reusejp_2825_;
}
else
{
lean_object* v_reuseFailAlloc_2827_; 
v_reuseFailAlloc_2827_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2827_, 0, v___x_2820_);
lean_ctor_set(v_reuseFailAlloc_2827_, 1, v_k_2815_);
lean_ctor_set(v_reuseFailAlloc_2827_, 2, v_v_2816_);
lean_ctor_set(v_reuseFailAlloc_2827_, 3, v___x_2822_);
lean_ctor_set(v_reuseFailAlloc_2827_, 4, v___x_2824_);
v___x_2826_ = v_reuseFailAlloc_2827_;
goto v_reusejp_2825_;
}
v_reusejp_2825_:
{
return v___x_2826_;
}
}
}
}
}
}
else
{
lean_object* v_r_2837_; 
v_r_2837_ = lean_ctor_get(v_impl_2723_, 4);
lean_inc(v_r_2837_);
if (lean_obj_tag(v_r_2837_) == 0)
{
lean_object* v_k_2838_; lean_object* v_v_2839_; lean_object* v___x_2841_; uint8_t v_isShared_2842_; uint8_t v_isSharedCheck_2850_; 
v_k_2838_ = lean_ctor_get(v_impl_2723_, 1);
v_v_2839_ = lean_ctor_get(v_impl_2723_, 2);
v_isSharedCheck_2850_ = !lean_is_exclusive(v_impl_2723_);
if (v_isSharedCheck_2850_ == 0)
{
lean_object* v_unused_2851_; lean_object* v_unused_2852_; lean_object* v_unused_2853_; 
v_unused_2851_ = lean_ctor_get(v_impl_2723_, 4);
lean_dec(v_unused_2851_);
v_unused_2852_ = lean_ctor_get(v_impl_2723_, 3);
lean_dec(v_unused_2852_);
v_unused_2853_ = lean_ctor_get(v_impl_2723_, 0);
lean_dec(v_unused_2853_);
v___x_2841_ = v_impl_2723_;
v_isShared_2842_ = v_isSharedCheck_2850_;
goto v_resetjp_2840_;
}
else
{
lean_inc(v_v_2839_);
lean_inc(v_k_2838_);
lean_dec(v_impl_2723_);
v___x_2841_ = lean_box(0);
v_isShared_2842_ = v_isSharedCheck_2850_;
goto v_resetjp_2840_;
}
v_resetjp_2840_:
{
lean_object* v___x_2843_; lean_object* v___x_2845_; 
v___x_2843_ = lean_unsigned_to_nat(3u);
if (v_isShared_2842_ == 0)
{
lean_ctor_set(v___x_2841_, 4, v_l_2808_);
lean_ctor_set(v___x_2841_, 2, v_v_2575_);
lean_ctor_set(v___x_2841_, 1, v_k_2574_);
lean_ctor_set(v___x_2841_, 0, v___x_2724_);
v___x_2845_ = v___x_2841_;
goto v_reusejp_2844_;
}
else
{
lean_object* v_reuseFailAlloc_2849_; 
v_reuseFailAlloc_2849_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2849_, 0, v___x_2724_);
lean_ctor_set(v_reuseFailAlloc_2849_, 1, v_k_2574_);
lean_ctor_set(v_reuseFailAlloc_2849_, 2, v_v_2575_);
lean_ctor_set(v_reuseFailAlloc_2849_, 3, v_l_2808_);
lean_ctor_set(v_reuseFailAlloc_2849_, 4, v_l_2808_);
v___x_2845_ = v_reuseFailAlloc_2849_;
goto v_reusejp_2844_;
}
v_reusejp_2844_:
{
lean_object* v___x_2847_; 
if (v_isShared_2580_ == 0)
{
lean_ctor_set(v___x_2579_, 4, v_r_2837_);
lean_ctor_set(v___x_2579_, 3, v___x_2845_);
lean_ctor_set(v___x_2579_, 2, v_v_2839_);
lean_ctor_set(v___x_2579_, 1, v_k_2838_);
lean_ctor_set(v___x_2579_, 0, v___x_2843_);
v___x_2847_ = v___x_2579_;
goto v_reusejp_2846_;
}
else
{
lean_object* v_reuseFailAlloc_2848_; 
v_reuseFailAlloc_2848_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2848_, 0, v___x_2843_);
lean_ctor_set(v_reuseFailAlloc_2848_, 1, v_k_2838_);
lean_ctor_set(v_reuseFailAlloc_2848_, 2, v_v_2839_);
lean_ctor_set(v_reuseFailAlloc_2848_, 3, v___x_2845_);
lean_ctor_set(v_reuseFailAlloc_2848_, 4, v_r_2837_);
v___x_2847_ = v_reuseFailAlloc_2848_;
goto v_reusejp_2846_;
}
v_reusejp_2846_:
{
return v___x_2847_;
}
}
}
}
else
{
lean_object* v___x_2854_; lean_object* v___x_2856_; 
v___x_2854_ = lean_unsigned_to_nat(2u);
if (v_isShared_2580_ == 0)
{
lean_ctor_set(v___x_2579_, 4, v_impl_2723_);
lean_ctor_set(v___x_2579_, 3, v_r_2837_);
lean_ctor_set(v___x_2579_, 0, v___x_2854_);
v___x_2856_ = v___x_2579_;
goto v_reusejp_2855_;
}
else
{
lean_object* v_reuseFailAlloc_2857_; 
v_reuseFailAlloc_2857_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2857_, 0, v___x_2854_);
lean_ctor_set(v_reuseFailAlloc_2857_, 1, v_k_2574_);
lean_ctor_set(v_reuseFailAlloc_2857_, 2, v_v_2575_);
lean_ctor_set(v_reuseFailAlloc_2857_, 3, v_r_2837_);
lean_ctor_set(v_reuseFailAlloc_2857_, 4, v_impl_2723_);
v___x_2856_ = v_reuseFailAlloc_2857_;
goto v_reusejp_2855_;
}
v_reusejp_2855_:
{
return v___x_2856_;
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
lean_object* v___x_2859_; lean_object* v___x_2860_; 
lean_dec_ref(v_cmp_2569_);
v___x_2859_ = lean_unsigned_to_nat(1u);
v___x_2860_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2860_, 0, v___x_2859_);
lean_ctor_set(v___x_2860_, 1, v_k_2570_);
lean_ctor_set(v___x_2860_, 2, v_v_2571_);
lean_ctor_set(v___x_2860_, 3, v_t_2572_);
lean_ctor_set(v___x_2860_, 4, v_t_2572_);
return v___x_2860_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__2_spec__4_spec__7_spec__11(lean_object* v_cmp_2861_, lean_object* v_init_2862_, lean_object* v_x_2863_){
_start:
{
if (lean_obj_tag(v_x_2863_) == 0)
{
lean_object* v_k_2864_; lean_object* v_v_2865_; lean_object* v_l_2866_; lean_object* v_r_2867_; lean_object* v___x_2868_; 
v_k_2864_ = lean_ctor_get(v_x_2863_, 1);
lean_inc(v_k_2864_);
v_v_2865_ = lean_ctor_get(v_x_2863_, 2);
lean_inc(v_v_2865_);
v_l_2866_ = lean_ctor_get(v_x_2863_, 3);
lean_inc(v_l_2866_);
v_r_2867_ = lean_ctor_get(v_x_2863_, 4);
lean_inc(v_r_2867_);
lean_dec_ref_known(v_x_2863_, 5);
lean_inc_ref(v_cmp_2861_);
v___x_2868_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__2_spec__4_spec__7_spec__11(v_cmp_2861_, v_init_2862_, v_l_2866_);
if (lean_obj_tag(v___x_2868_) == 0)
{
lean_dec(v_r_2867_);
lean_dec(v_v_2865_);
lean_dec(v_k_2864_);
lean_dec_ref(v_cmp_2861_);
return v___x_2868_;
}
else
{
lean_object* v_a_2869_; lean_object* v___x_2870_; 
v_a_2869_ = lean_ctor_get(v___x_2868_, 0);
lean_inc(v_a_2869_);
lean_dec_ref_known(v___x_2868_, 1);
v___x_2870_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentEdit_fromJson_spec__1_spec__1(v_v_2865_);
if (lean_obj_tag(v___x_2870_) == 0)
{
lean_object* v_a_2871_; lean_object* v___x_2873_; uint8_t v_isShared_2874_; uint8_t v_isSharedCheck_2878_; 
lean_dec(v_a_2869_);
lean_dec(v_r_2867_);
lean_dec(v_k_2864_);
lean_dec_ref(v_cmp_2861_);
v_a_2871_ = lean_ctor_get(v___x_2870_, 0);
v_isSharedCheck_2878_ = !lean_is_exclusive(v___x_2870_);
if (v_isSharedCheck_2878_ == 0)
{
v___x_2873_ = v___x_2870_;
v_isShared_2874_ = v_isSharedCheck_2878_;
goto v_resetjp_2872_;
}
else
{
lean_inc(v_a_2871_);
lean_dec(v___x_2870_);
v___x_2873_ = lean_box(0);
v_isShared_2874_ = v_isSharedCheck_2878_;
goto v_resetjp_2872_;
}
v_resetjp_2872_:
{
lean_object* v___x_2876_; 
if (v_isShared_2874_ == 0)
{
v___x_2876_ = v___x_2873_;
goto v_reusejp_2875_;
}
else
{
lean_object* v_reuseFailAlloc_2877_; 
v_reuseFailAlloc_2877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2877_, 0, v_a_2871_);
v___x_2876_ = v_reuseFailAlloc_2877_;
goto v_reusejp_2875_;
}
v_reusejp_2875_:
{
return v___x_2876_;
}
}
}
else
{
lean_object* v_a_2879_; lean_object* v___x_2880_; 
v_a_2879_ = lean_ctor_get(v___x_2870_, 0);
lean_inc(v_a_2879_);
lean_dec_ref_known(v___x_2870_, 1);
lean_inc_ref(v_cmp_2861_);
v___x_2880_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__1_spec__2_spec__4_spec__7___redArg(v_cmp_2861_, v_k_2864_, v_a_2879_, v_a_2869_);
v_init_2862_ = v___x_2880_;
v_x_2863_ = v_r_2867_;
goto _start;
}
}
}
else
{
lean_object* v___x_2882_; 
lean_dec_ref(v_cmp_2861_);
v___x_2882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2882_, 0, v_init_2862_);
return v___x_2882_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__2_spec__4_spec__7(lean_object* v_cmp_2883_, lean_object* v_j_2884_){
_start:
{
lean_object* v___x_2885_; 
v___x_2885_ = l_Lean_Json_getObj_x3f(v_j_2884_);
if (lean_obj_tag(v___x_2885_) == 0)
{
lean_object* v_a_2886_; lean_object* v___x_2888_; uint8_t v_isShared_2889_; uint8_t v_isSharedCheck_2893_; 
lean_dec_ref(v_cmp_2883_);
v_a_2886_ = lean_ctor_get(v___x_2885_, 0);
v_isSharedCheck_2893_ = !lean_is_exclusive(v___x_2885_);
if (v_isSharedCheck_2893_ == 0)
{
v___x_2888_ = v___x_2885_;
v_isShared_2889_ = v_isSharedCheck_2893_;
goto v_resetjp_2887_;
}
else
{
lean_inc(v_a_2886_);
lean_dec(v___x_2885_);
v___x_2888_ = lean_box(0);
v_isShared_2889_ = v_isSharedCheck_2893_;
goto v_resetjp_2887_;
}
v_resetjp_2887_:
{
lean_object* v___x_2891_; 
if (v_isShared_2889_ == 0)
{
v___x_2891_ = v___x_2888_;
goto v_reusejp_2890_;
}
else
{
lean_object* v_reuseFailAlloc_2892_; 
v_reuseFailAlloc_2892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2892_, 0, v_a_2886_);
v___x_2891_ = v_reuseFailAlloc_2892_;
goto v_reusejp_2890_;
}
v_reusejp_2890_:
{
return v___x_2891_;
}
}
}
else
{
lean_object* v_a_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; 
v_a_2894_ = lean_ctor_get(v___x_2885_, 0);
lean_inc(v_a_2894_);
lean_dec_ref_known(v___x_2885_, 1);
v___x_2895_ = lean_box(1);
v___x_2896_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__2_spec__4_spec__7_spec__11(v_cmp_2883_, v___x_2895_, v_a_2894_);
return v___x_2896_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__2_spec__4(lean_object* v_x_2900_){
_start:
{
if (lean_obj_tag(v_x_2900_) == 0)
{
lean_object* v___x_2901_; 
v___x_2901_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__2_spec__4___closed__0));
return v___x_2901_;
}
else
{
lean_object* v___x_2902_; lean_object* v___x_2903_; 
v___x_2902_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__2_spec__4___closed__1));
v___x_2903_ = l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__2_spec__4_spec__7(v___x_2902_, v_x_2900_);
if (lean_obj_tag(v___x_2903_) == 0)
{
lean_object* v_a_2904_; lean_object* v___x_2906_; uint8_t v_isShared_2907_; uint8_t v_isSharedCheck_2911_; 
v_a_2904_ = lean_ctor_get(v___x_2903_, 0);
v_isSharedCheck_2911_ = !lean_is_exclusive(v___x_2903_);
if (v_isSharedCheck_2911_ == 0)
{
v___x_2906_ = v___x_2903_;
v_isShared_2907_ = v_isSharedCheck_2911_;
goto v_resetjp_2905_;
}
else
{
lean_inc(v_a_2904_);
lean_dec(v___x_2903_);
v___x_2906_ = lean_box(0);
v_isShared_2907_ = v_isSharedCheck_2911_;
goto v_resetjp_2905_;
}
v_resetjp_2905_:
{
lean_object* v___x_2909_; 
if (v_isShared_2907_ == 0)
{
v___x_2909_ = v___x_2906_;
goto v_reusejp_2908_;
}
else
{
lean_object* v_reuseFailAlloc_2910_; 
v_reuseFailAlloc_2910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2910_, 0, v_a_2904_);
v___x_2909_ = v_reuseFailAlloc_2910_;
goto v_reusejp_2908_;
}
v_reusejp_2908_:
{
return v___x_2909_;
}
}
}
else
{
lean_object* v_a_2912_; lean_object* v___x_2914_; uint8_t v_isShared_2915_; uint8_t v_isSharedCheck_2920_; 
v_a_2912_ = lean_ctor_get(v___x_2903_, 0);
v_isSharedCheck_2920_ = !lean_is_exclusive(v___x_2903_);
if (v_isSharedCheck_2920_ == 0)
{
v___x_2914_ = v___x_2903_;
v_isShared_2915_ = v_isSharedCheck_2920_;
goto v_resetjp_2913_;
}
else
{
lean_inc(v_a_2912_);
lean_dec(v___x_2903_);
v___x_2914_ = lean_box(0);
v_isShared_2915_ = v_isSharedCheck_2920_;
goto v_resetjp_2913_;
}
v_resetjp_2913_:
{
lean_object* v___x_2916_; lean_object* v___x_2918_; 
v___x_2916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2916_, 0, v_a_2912_);
if (v_isShared_2915_ == 0)
{
lean_ctor_set(v___x_2914_, 0, v___x_2916_);
v___x_2918_ = v___x_2914_;
goto v_reusejp_2917_;
}
else
{
lean_object* v_reuseFailAlloc_2919_; 
v_reuseFailAlloc_2919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2919_, 0, v___x_2916_);
v___x_2918_ = v_reuseFailAlloc_2919_;
goto v_reusejp_2917_;
}
v_reusejp_2917_:
{
return v___x_2918_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__2(lean_object* v_j_2921_, lean_object* v_k_2922_){
_start:
{
lean_object* v___x_2923_; lean_object* v___x_2924_; 
v___x_2923_ = l_Lean_Json_getObjValD(v_j_2921_, v_k_2922_);
v___x_2924_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__2_spec__4(v___x_2923_);
return v___x_2924_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__2___boxed(lean_object* v_j_2925_, lean_object* v_k_2926_){
_start:
{
lean_object* v_res_2927_; 
v_res_2927_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__2(v_j_2925_, v_k_2926_);
lean_dec_ref(v_k_2926_);
return v_res_2927_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__1_spec__2_spec__4_spec__8(lean_object* v_cmp_2928_, lean_object* v_init_2929_, lean_object* v_x_2930_){
_start:
{
if (lean_obj_tag(v_x_2930_) == 0)
{
lean_object* v_k_2931_; lean_object* v_v_2932_; lean_object* v_l_2933_; lean_object* v_r_2934_; lean_object* v___x_2935_; 
v_k_2931_ = lean_ctor_get(v_x_2930_, 1);
lean_inc(v_k_2931_);
v_v_2932_ = lean_ctor_get(v_x_2930_, 2);
lean_inc(v_v_2932_);
v_l_2933_ = lean_ctor_get(v_x_2930_, 3);
lean_inc(v_l_2933_);
v_r_2934_ = lean_ctor_get(v_x_2930_, 4);
lean_inc(v_r_2934_);
lean_dec_ref_known(v_x_2930_, 5);
lean_inc_ref(v_cmp_2928_);
v___x_2935_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__1_spec__2_spec__4_spec__8(v_cmp_2928_, v_init_2929_, v_l_2933_);
if (lean_obj_tag(v___x_2935_) == 0)
{
lean_dec(v_r_2934_);
lean_dec(v_v_2932_);
lean_dec(v_k_2931_);
lean_dec_ref(v_cmp_2928_);
return v___x_2935_;
}
else
{
lean_object* v_a_2936_; lean_object* v___x_2937_; 
v_a_2936_ = lean_ctor_get(v___x_2935_, 0);
lean_inc(v_a_2936_);
lean_dec_ref_known(v___x_2935_, 1);
v___x_2937_ = l_Lean_Lsp_instFromJsonChangeAnnotation_fromJson(v_v_2932_);
if (lean_obj_tag(v___x_2937_) == 0)
{
lean_object* v_a_2938_; lean_object* v___x_2940_; uint8_t v_isShared_2941_; uint8_t v_isSharedCheck_2945_; 
lean_dec(v_a_2936_);
lean_dec(v_r_2934_);
lean_dec(v_k_2931_);
lean_dec_ref(v_cmp_2928_);
v_a_2938_ = lean_ctor_get(v___x_2937_, 0);
v_isSharedCheck_2945_ = !lean_is_exclusive(v___x_2937_);
if (v_isSharedCheck_2945_ == 0)
{
v___x_2940_ = v___x_2937_;
v_isShared_2941_ = v_isSharedCheck_2945_;
goto v_resetjp_2939_;
}
else
{
lean_inc(v_a_2938_);
lean_dec(v___x_2937_);
v___x_2940_ = lean_box(0);
v_isShared_2941_ = v_isSharedCheck_2945_;
goto v_resetjp_2939_;
}
v_resetjp_2939_:
{
lean_object* v___x_2943_; 
if (v_isShared_2941_ == 0)
{
v___x_2943_ = v___x_2940_;
goto v_reusejp_2942_;
}
else
{
lean_object* v_reuseFailAlloc_2944_; 
v_reuseFailAlloc_2944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2944_, 0, v_a_2938_);
v___x_2943_ = v_reuseFailAlloc_2944_;
goto v_reusejp_2942_;
}
v_reusejp_2942_:
{
return v___x_2943_;
}
}
}
else
{
lean_object* v_a_2946_; lean_object* v___x_2947_; 
v_a_2946_ = lean_ctor_get(v___x_2937_, 0);
lean_inc(v_a_2946_);
lean_dec_ref_known(v___x_2937_, 1);
lean_inc_ref(v_cmp_2928_);
v___x_2947_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__1_spec__2_spec__4_spec__7___redArg(v_cmp_2928_, v_k_2931_, v_a_2946_, v_a_2936_);
v_init_2929_ = v___x_2947_;
v_x_2930_ = v_r_2934_;
goto _start;
}
}
}
else
{
lean_object* v___x_2949_; 
lean_dec_ref(v_cmp_2928_);
v___x_2949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2949_, 0, v_init_2929_);
return v___x_2949_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__1_spec__2_spec__4(lean_object* v_cmp_2950_, lean_object* v_j_2951_){
_start:
{
lean_object* v___x_2952_; 
v___x_2952_ = l_Lean_Json_getObj_x3f(v_j_2951_);
if (lean_obj_tag(v___x_2952_) == 0)
{
lean_object* v_a_2953_; lean_object* v___x_2955_; uint8_t v_isShared_2956_; uint8_t v_isSharedCheck_2960_; 
lean_dec_ref(v_cmp_2950_);
v_a_2953_ = lean_ctor_get(v___x_2952_, 0);
v_isSharedCheck_2960_ = !lean_is_exclusive(v___x_2952_);
if (v_isSharedCheck_2960_ == 0)
{
v___x_2955_ = v___x_2952_;
v_isShared_2956_ = v_isSharedCheck_2960_;
goto v_resetjp_2954_;
}
else
{
lean_inc(v_a_2953_);
lean_dec(v___x_2952_);
v___x_2955_ = lean_box(0);
v_isShared_2956_ = v_isSharedCheck_2960_;
goto v_resetjp_2954_;
}
v_resetjp_2954_:
{
lean_object* v___x_2958_; 
if (v_isShared_2956_ == 0)
{
v___x_2958_ = v___x_2955_;
goto v_reusejp_2957_;
}
else
{
lean_object* v_reuseFailAlloc_2959_; 
v_reuseFailAlloc_2959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2959_, 0, v_a_2953_);
v___x_2958_ = v_reuseFailAlloc_2959_;
goto v_reusejp_2957_;
}
v_reusejp_2957_:
{
return v___x_2958_;
}
}
}
else
{
lean_object* v_a_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; 
v_a_2961_ = lean_ctor_get(v___x_2952_, 0);
lean_inc(v_a_2961_);
lean_dec_ref_known(v___x_2952_, 1);
v___x_2962_ = lean_box(1);
v___x_2963_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__1_spec__2_spec__4_spec__8(v_cmp_2950_, v___x_2962_, v_a_2961_);
return v___x_2963_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__1_spec__2(lean_object* v_x_2964_){
_start:
{
if (lean_obj_tag(v_x_2964_) == 0)
{
lean_object* v___x_2965_; 
v___x_2965_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__2_spec__4___closed__0));
return v___x_2965_;
}
else
{
lean_object* v___x_2966_; lean_object* v___x_2967_; 
v___x_2966_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__2_spec__4___closed__1));
v___x_2967_ = l___private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__1_spec__2_spec__4(v___x_2966_, v_x_2964_);
if (lean_obj_tag(v___x_2967_) == 0)
{
lean_object* v_a_2968_; lean_object* v___x_2970_; uint8_t v_isShared_2971_; uint8_t v_isSharedCheck_2975_; 
v_a_2968_ = lean_ctor_get(v___x_2967_, 0);
v_isSharedCheck_2975_ = !lean_is_exclusive(v___x_2967_);
if (v_isSharedCheck_2975_ == 0)
{
v___x_2970_ = v___x_2967_;
v_isShared_2971_ = v_isSharedCheck_2975_;
goto v_resetjp_2969_;
}
else
{
lean_inc(v_a_2968_);
lean_dec(v___x_2967_);
v___x_2970_ = lean_box(0);
v_isShared_2971_ = v_isSharedCheck_2975_;
goto v_resetjp_2969_;
}
v_resetjp_2969_:
{
lean_object* v___x_2973_; 
if (v_isShared_2971_ == 0)
{
v___x_2973_ = v___x_2970_;
goto v_reusejp_2972_;
}
else
{
lean_object* v_reuseFailAlloc_2974_; 
v_reuseFailAlloc_2974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2974_, 0, v_a_2968_);
v___x_2973_ = v_reuseFailAlloc_2974_;
goto v_reusejp_2972_;
}
v_reusejp_2972_:
{
return v___x_2973_;
}
}
}
else
{
lean_object* v_a_2976_; lean_object* v___x_2978_; uint8_t v_isShared_2979_; uint8_t v_isSharedCheck_2984_; 
v_a_2976_ = lean_ctor_get(v___x_2967_, 0);
v_isSharedCheck_2984_ = !lean_is_exclusive(v___x_2967_);
if (v_isSharedCheck_2984_ == 0)
{
v___x_2978_ = v___x_2967_;
v_isShared_2979_ = v_isSharedCheck_2984_;
goto v_resetjp_2977_;
}
else
{
lean_inc(v_a_2976_);
lean_dec(v___x_2967_);
v___x_2978_ = lean_box(0);
v_isShared_2979_ = v_isSharedCheck_2984_;
goto v_resetjp_2977_;
}
v_resetjp_2977_:
{
lean_object* v___x_2980_; lean_object* v___x_2982_; 
v___x_2980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2980_, 0, v_a_2976_);
if (v_isShared_2979_ == 0)
{
lean_ctor_set(v___x_2978_, 0, v___x_2980_);
v___x_2982_ = v___x_2978_;
goto v_reusejp_2981_;
}
else
{
lean_object* v_reuseFailAlloc_2983_; 
v_reuseFailAlloc_2983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2983_, 0, v___x_2980_);
v___x_2982_ = v_reuseFailAlloc_2983_;
goto v_reusejp_2981_;
}
v_reusejp_2981_:
{
return v___x_2982_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__1(lean_object* v_j_2985_, lean_object* v_k_2986_){
_start:
{
lean_object* v___x_2987_; lean_object* v___x_2988_; 
v___x_2987_ = l_Lean_Json_getObjValD(v_j_2985_, v_k_2986_);
v___x_2988_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__1_spec__2(v___x_2987_);
return v___x_2988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__1___boxed(lean_object* v_j_2989_, lean_object* v_k_2990_){
_start:
{
lean_object* v_res_2991_; 
v_res_2991_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__1(v_j_2989_, v_k_2990_);
lean_dec_ref(v_k_2990_);
return v_res_2991_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__0_spec__0_spec__1_spec__4___lam__0(lean_object* v_kind_2992_){
_start:
{
lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; 
v___x_2993_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDocumentChange___lam__0___closed__0));
v___x_2994_ = lean_unsigned_to_nat(80u);
v___x_2995_ = l_Lean_Json_pretty(v_kind_2992_, v___x_2994_);
v___x_2996_ = lean_string_append(v___x_2993_, v___x_2995_);
lean_dec_ref(v___x_2995_);
v___x_2997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2997_, 0, v___x_2996_);
return v___x_2997_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__0_spec__0_spec__1_spec__4(size_t v_sz_2998_, size_t v_i_2999_, lean_object* v_bs_3000_){
_start:
{
uint8_t v___x_3001_; 
v___x_3001_ = lean_usize_dec_lt(v_i_2999_, v_sz_2998_);
if (v___x_3001_ == 0)
{
lean_object* v___x_3002_; 
v___x_3002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3002_, 0, v_bs_3000_);
return v___x_3002_;
}
else
{
lean_object* v_v_3003_; lean_object* v___x_3004_; lean_object* v_bs_x27_3005_; lean_object* v_a_3007_; lean_object* v___y_3025_; lean_object* v___x_3027_; lean_object* v___x_3028_; 
v_v_3003_ = lean_array_uget(v_bs_3000_, v_i_2999_);
v___x_3004_ = lean_unsigned_to_nat(0u);
v_bs_x27_3005_ = lean_array_uset(v_bs_3000_, v_i_2999_, v___x_3004_);
v___x_3027_ = ((lean_object*)(l_Lean_Lsp_instToJsonDocumentChange___lam__0___closed__0));
lean_inc(v_v_3003_);
v___x_3028_ = l_Lean_Json_getObjVal_x3f(v_v_3003_, v___x_3027_);
if (lean_obj_tag(v___x_3028_) == 0)
{
lean_dec_ref_known(v___x_3028_, 1);
goto v___jp_3012_;
}
else
{
lean_object* v_a_3029_; 
v_a_3029_ = lean_ctor_get(v___x_3028_, 0);
lean_inc(v_a_3029_);
lean_dec_ref_known(v___x_3028_, 1);
if (lean_obj_tag(v_a_3029_) == 3)
{
lean_object* v_s_3030_; lean_object* v___x_3031_; uint8_t v___x_3032_; 
v_s_3030_ = lean_ctor_get(v_a_3029_, 0);
v___x_3031_ = ((lean_object*)(l_Lean_Lsp_instToJsonDocumentChange___lam__0___closed__1));
v___x_3032_ = lean_string_dec_eq(v_s_3030_, v___x_3031_);
if (v___x_3032_ == 0)
{
lean_object* v___x_3033_; uint8_t v___x_3034_; 
v___x_3033_ = ((lean_object*)(l_Lean_Lsp_instToJsonDocumentChange___lam__0___closed__3));
v___x_3034_ = lean_string_dec_eq(v_s_3030_, v___x_3033_);
if (v___x_3034_ == 0)
{
lean_object* v___x_3035_; uint8_t v___x_3036_; 
v___x_3035_ = ((lean_object*)(l_Lean_Lsp_instToJsonDocumentChange___lam__0___closed__5));
v___x_3036_ = lean_string_dec_eq(v_s_3030_, v___x_3035_);
if (v___x_3036_ == 0)
{
lean_object* v___x_3037_; 
v___x_3037_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__0_spec__0_spec__1_spec__4___lam__0(v_a_3029_);
v___y_3025_ = v___x_3037_;
goto v___jp_3024_;
}
else
{
lean_object* v___x_3038_; 
lean_dec_ref_known(v_a_3029_, 1);
lean_inc(v_v_3003_);
v___x_3038_ = l_Lean_Lsp_instFromJsonDeleteFile_fromJson(v_v_3003_);
if (lean_obj_tag(v___x_3038_) == 0)
{
lean_dec_ref_known(v___x_3038_, 1);
goto v___jp_3012_;
}
else
{
lean_object* v_a_3039_; lean_object* v___x_3041_; uint8_t v_isShared_3042_; uint8_t v_isSharedCheck_3046_; 
lean_dec(v_v_3003_);
v_a_3039_ = lean_ctor_get(v___x_3038_, 0);
v_isSharedCheck_3046_ = !lean_is_exclusive(v___x_3038_);
if (v_isSharedCheck_3046_ == 0)
{
v___x_3041_ = v___x_3038_;
v_isShared_3042_ = v_isSharedCheck_3046_;
goto v_resetjp_3040_;
}
else
{
lean_inc(v_a_3039_);
lean_dec(v___x_3038_);
v___x_3041_ = lean_box(0);
v_isShared_3042_ = v_isSharedCheck_3046_;
goto v_resetjp_3040_;
}
v_resetjp_3040_:
{
lean_object* v___x_3044_; 
if (v_isShared_3042_ == 0)
{
lean_ctor_set_tag(v___x_3041_, 2);
v___x_3044_ = v___x_3041_;
goto v_reusejp_3043_;
}
else
{
lean_object* v_reuseFailAlloc_3045_; 
v_reuseFailAlloc_3045_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3045_, 0, v_a_3039_);
v___x_3044_ = v_reuseFailAlloc_3045_;
goto v_reusejp_3043_;
}
v_reusejp_3043_:
{
v_a_3007_ = v___x_3044_;
goto v___jp_3006_;
}
}
}
}
}
else
{
lean_object* v___x_3047_; 
lean_dec_ref_known(v_a_3029_, 1);
lean_inc(v_v_3003_);
v___x_3047_ = l_Lean_Lsp_instFromJsonRenameFile_fromJson(v_v_3003_);
if (lean_obj_tag(v___x_3047_) == 0)
{
lean_dec_ref_known(v___x_3047_, 1);
goto v___jp_3012_;
}
else
{
lean_object* v_a_3048_; lean_object* v___x_3050_; uint8_t v_isShared_3051_; uint8_t v_isSharedCheck_3055_; 
lean_dec(v_v_3003_);
v_a_3048_ = lean_ctor_get(v___x_3047_, 0);
v_isSharedCheck_3055_ = !lean_is_exclusive(v___x_3047_);
if (v_isSharedCheck_3055_ == 0)
{
v___x_3050_ = v___x_3047_;
v_isShared_3051_ = v_isSharedCheck_3055_;
goto v_resetjp_3049_;
}
else
{
lean_inc(v_a_3048_);
lean_dec(v___x_3047_);
v___x_3050_ = lean_box(0);
v_isShared_3051_ = v_isSharedCheck_3055_;
goto v_resetjp_3049_;
}
v_resetjp_3049_:
{
lean_object* v___x_3053_; 
if (v_isShared_3051_ == 0)
{
v___x_3053_ = v___x_3050_;
goto v_reusejp_3052_;
}
else
{
lean_object* v_reuseFailAlloc_3054_; 
v_reuseFailAlloc_3054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3054_, 0, v_a_3048_);
v___x_3053_ = v_reuseFailAlloc_3054_;
goto v_reusejp_3052_;
}
v_reusejp_3052_:
{
v_a_3007_ = v___x_3053_;
goto v___jp_3006_;
}
}
}
}
}
else
{
lean_object* v___x_3056_; 
lean_dec_ref_known(v_a_3029_, 1);
lean_inc(v_v_3003_);
v___x_3056_ = l_Lean_Lsp_instFromJsonCreateFile_fromJson(v_v_3003_);
if (lean_obj_tag(v___x_3056_) == 0)
{
lean_dec_ref_known(v___x_3056_, 1);
goto v___jp_3012_;
}
else
{
lean_object* v_a_3057_; lean_object* v___x_3059_; uint8_t v_isShared_3060_; uint8_t v_isSharedCheck_3064_; 
lean_dec(v_v_3003_);
v_a_3057_ = lean_ctor_get(v___x_3056_, 0);
v_isSharedCheck_3064_ = !lean_is_exclusive(v___x_3056_);
if (v_isSharedCheck_3064_ == 0)
{
v___x_3059_ = v___x_3056_;
v_isShared_3060_ = v_isSharedCheck_3064_;
goto v_resetjp_3058_;
}
else
{
lean_inc(v_a_3057_);
lean_dec(v___x_3056_);
v___x_3059_ = lean_box(0);
v_isShared_3060_ = v_isSharedCheck_3064_;
goto v_resetjp_3058_;
}
v_resetjp_3058_:
{
lean_object* v___x_3062_; 
if (v_isShared_3060_ == 0)
{
lean_ctor_set_tag(v___x_3059_, 0);
v___x_3062_ = v___x_3059_;
goto v_reusejp_3061_;
}
else
{
lean_object* v_reuseFailAlloc_3063_; 
v_reuseFailAlloc_3063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3063_, 0, v_a_3057_);
v___x_3062_ = v_reuseFailAlloc_3063_;
goto v_reusejp_3061_;
}
v_reusejp_3061_:
{
v_a_3007_ = v___x_3062_;
goto v___jp_3006_;
}
}
}
}
}
else
{
lean_object* v___x_3065_; 
v___x_3065_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__0_spec__0_spec__1_spec__4___lam__0(v_a_3029_);
v___y_3025_ = v___x_3065_;
goto v___jp_3024_;
}
}
v___jp_3006_:
{
size_t v___x_3008_; size_t v___x_3009_; lean_object* v___x_3010_; 
v___x_3008_ = ((size_t)1ULL);
v___x_3009_ = lean_usize_add(v_i_2999_, v___x_3008_);
v___x_3010_ = lean_array_uset(v_bs_x27_3005_, v_i_2999_, v_a_3007_);
v_i_2999_ = v___x_3009_;
v_bs_3000_ = v___x_3010_;
goto _start;
}
v___jp_3012_:
{
lean_object* v___x_3013_; 
v___x_3013_ = l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson(v_v_3003_);
if (lean_obj_tag(v___x_3013_) == 0)
{
lean_object* v_a_3014_; lean_object* v___x_3016_; uint8_t v_isShared_3017_; uint8_t v_isSharedCheck_3021_; 
lean_dec_ref(v_bs_x27_3005_);
v_a_3014_ = lean_ctor_get(v___x_3013_, 0);
v_isSharedCheck_3021_ = !lean_is_exclusive(v___x_3013_);
if (v_isSharedCheck_3021_ == 0)
{
v___x_3016_ = v___x_3013_;
v_isShared_3017_ = v_isSharedCheck_3021_;
goto v_resetjp_3015_;
}
else
{
lean_inc(v_a_3014_);
lean_dec(v___x_3013_);
v___x_3016_ = lean_box(0);
v_isShared_3017_ = v_isSharedCheck_3021_;
goto v_resetjp_3015_;
}
v_resetjp_3015_:
{
lean_object* v___x_3019_; 
if (v_isShared_3017_ == 0)
{
v___x_3019_ = v___x_3016_;
goto v_reusejp_3018_;
}
else
{
lean_object* v_reuseFailAlloc_3020_; 
v_reuseFailAlloc_3020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3020_, 0, v_a_3014_);
v___x_3019_ = v_reuseFailAlloc_3020_;
goto v_reusejp_3018_;
}
v_reusejp_3018_:
{
return v___x_3019_;
}
}
}
else
{
lean_object* v_a_3022_; lean_object* v___x_3023_; 
v_a_3022_ = lean_ctor_get(v___x_3013_, 0);
lean_inc(v_a_3022_);
lean_dec_ref_known(v___x_3013_, 1);
v___x_3023_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3023_, 0, v_a_3022_);
v_a_3007_ = v___x_3023_;
goto v___jp_3006_;
}
}
v___jp_3024_:
{
if (lean_obj_tag(v___y_3025_) == 0)
{
lean_dec_ref_known(v___y_3025_, 1);
goto v___jp_3012_;
}
else
{
lean_object* v_a_3026_; 
lean_dec(v_v_3003_);
v_a_3026_ = lean_ctor_get(v___y_3025_, 0);
lean_inc(v_a_3026_);
lean_dec_ref_known(v___y_3025_, 1);
v_a_3007_ = v_a_3026_;
goto v___jp_3006_;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__0_spec__0_spec__1_spec__4_0interp(lean_interpreter_value* stack)
{
size_t v_sz_2998_ = stack[0].m_num;
size_t v_i_2999_ = stack[1].m_num;
lean_object* v_bs_3000_ = stack[2].m_obj;
lean_object* v_res_3066_;
v_res_3066_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__0_spec__0_spec__1_spec__4(v_sz_2998_, v_i_2999_, v_bs_3000_);
stack->m_obj
 = v_res_3066_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_sz_3067_, lean_object* v_i_3068_, lean_object* v_bs_3069_){
_start:
{
size_t v_sz_boxed_3070_; size_t v_i_boxed_3071_; lean_object* v_res_3072_; 
v_sz_boxed_3070_ = lean_unbox_usize(v_sz_3067_);
lean_dec(v_sz_3067_);
v_i_boxed_3071_ = lean_unbox_usize(v_i_3068_);
lean_dec(v_i_3068_);
v_res_3072_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__0_spec__0_spec__1_spec__4(v_sz_boxed_3070_, v_i_boxed_3071_, v_bs_3069_);
return v_res_3072_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__0_spec__0_spec__1(lean_object* v_x_3073_){
_start:
{
if (lean_obj_tag(v_x_3073_) == 4)
{
lean_object* v_elems_3074_; size_t v_sz_3075_; size_t v___x_3076_; lean_object* v___x_3077_; 
v_elems_3074_ = lean_ctor_get(v_x_3073_, 0);
lean_inc_ref(v_elems_3074_);
lean_dec_ref_known(v_x_3073_, 1);
v_sz_3075_ = lean_array_size(v_elems_3074_);
v___x_3076_ = ((size_t)0ULL);
v___x_3077_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__0_spec__0_spec__1_spec__4(v_sz_3075_, v___x_3076_, v_elems_3074_);
return v___x_3077_;
}
else
{
lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; 
v___x_3078_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCommand_fromJson_spec__0_spec__0_spec__1___closed__0));
v___x_3079_ = lean_unsigned_to_nat(80u);
v___x_3080_ = l_Lean_Json_pretty(v_x_3073_, v___x_3079_);
v___x_3081_ = lean_string_append(v___x_3078_, v___x_3080_);
lean_dec_ref(v___x_3080_);
v___x_3082_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCommand_fromJson_spec__0_spec__0_spec__1___closed__1));
v___x_3083_ = lean_string_append(v___x_3081_, v___x_3082_);
v___x_3084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3084_, 0, v___x_3083_);
return v___x_3084_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__0_spec__0(lean_object* v_x_3087_){
_start:
{
if (lean_obj_tag(v_x_3087_) == 0)
{
lean_object* v___x_3088_; 
v___x_3088_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__0_spec__0___closed__0));
return v___x_3088_;
}
else
{
lean_object* v___x_3089_; 
v___x_3089_ = l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__0_spec__0_spec__1(v_x_3087_);
if (lean_obj_tag(v___x_3089_) == 0)
{
lean_object* v_a_3090_; lean_object* v___x_3092_; uint8_t v_isShared_3093_; uint8_t v_isSharedCheck_3097_; 
v_a_3090_ = lean_ctor_get(v___x_3089_, 0);
v_isSharedCheck_3097_ = !lean_is_exclusive(v___x_3089_);
if (v_isSharedCheck_3097_ == 0)
{
v___x_3092_ = v___x_3089_;
v_isShared_3093_ = v_isSharedCheck_3097_;
goto v_resetjp_3091_;
}
else
{
lean_inc(v_a_3090_);
lean_dec(v___x_3089_);
v___x_3092_ = lean_box(0);
v_isShared_3093_ = v_isSharedCheck_3097_;
goto v_resetjp_3091_;
}
v_resetjp_3091_:
{
lean_object* v___x_3095_; 
if (v_isShared_3093_ == 0)
{
v___x_3095_ = v___x_3092_;
goto v_reusejp_3094_;
}
else
{
lean_object* v_reuseFailAlloc_3096_; 
v_reuseFailAlloc_3096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3096_, 0, v_a_3090_);
v___x_3095_ = v_reuseFailAlloc_3096_;
goto v_reusejp_3094_;
}
v_reusejp_3094_:
{
return v___x_3095_;
}
}
}
else
{
lean_object* v_a_3098_; lean_object* v___x_3100_; uint8_t v_isShared_3101_; uint8_t v_isSharedCheck_3106_; 
v_a_3098_ = lean_ctor_get(v___x_3089_, 0);
v_isSharedCheck_3106_ = !lean_is_exclusive(v___x_3089_);
if (v_isSharedCheck_3106_ == 0)
{
v___x_3100_ = v___x_3089_;
v_isShared_3101_ = v_isSharedCheck_3106_;
goto v_resetjp_3099_;
}
else
{
lean_inc(v_a_3098_);
lean_dec(v___x_3089_);
v___x_3100_ = lean_box(0);
v_isShared_3101_ = v_isSharedCheck_3106_;
goto v_resetjp_3099_;
}
v_resetjp_3099_:
{
lean_object* v___x_3102_; lean_object* v___x_3104_; 
v___x_3102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3102_, 0, v_a_3098_);
if (v_isShared_3101_ == 0)
{
lean_ctor_set(v___x_3100_, 0, v___x_3102_);
v___x_3104_ = v___x_3100_;
goto v_reusejp_3103_;
}
else
{
lean_object* v_reuseFailAlloc_3105_; 
v_reuseFailAlloc_3105_ = lean_alloc_ctor(1, 1, 0);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__0(lean_object* v_j_3107_, lean_object* v_k_3108_){
_start:
{
lean_object* v___x_3109_; lean_object* v___x_3110_; 
v___x_3109_ = l_Lean_Json_getObjValD(v_j_3107_, v_k_3108_);
v___x_3110_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__0_spec__0(v___x_3109_);
return v___x_3110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__0___boxed(lean_object* v_j_3111_, lean_object* v_k_3112_){
_start:
{
lean_object* v_res_3113_; 
v_res_3113_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__0(v_j_3111_, v_k_3112_);
lean_dec_ref(v_k_3112_);
return v_res_3113_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__2(void){
_start:
{
uint8_t v___x_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; 
v___x_3119_ = 1;
v___x_3120_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__1));
v___x_3121_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3120_, v___x_3119_);
return v___x_3121_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__3(void){
_start:
{
lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; 
v___x_3122_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__5));
v___x_3123_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__2, &l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__2);
v___x_3124_ = lean_string_append(v___x_3123_, v___x_3122_);
return v___x_3124_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__6(void){
_start:
{
uint8_t v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; 
v___x_3128_ = 1;
v___x_3129_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__5));
v___x_3130_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3129_, v___x_3128_);
return v___x_3130_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__7(void){
_start:
{
lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; 
v___x_3131_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__6, &l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__6);
v___x_3132_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__3, &l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__3);
v___x_3133_ = lean_string_append(v___x_3132_, v___x_3131_);
return v___x_3133_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__8(void){
_start:
{
lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; 
v___x_3134_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_3135_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__7, &l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__7);
v___x_3136_ = lean_string_append(v___x_3135_, v___x_3134_);
return v___x_3136_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__11(void){
_start:
{
uint8_t v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; 
v___x_3140_ = 1;
v___x_3141_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__10));
v___x_3142_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3141_, v___x_3140_);
return v___x_3142_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__12(void){
_start:
{
lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; 
v___x_3143_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__11, &l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__11);
v___x_3144_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__3, &l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__3);
v___x_3145_ = lean_string_append(v___x_3144_, v___x_3143_);
return v___x_3145_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__13(void){
_start:
{
lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; 
v___x_3146_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_3147_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__12, &l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__12);
v___x_3148_ = lean_string_append(v___x_3147_, v___x_3146_);
return v___x_3148_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__16(void){
_start:
{
uint8_t v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; 
v___x_3152_ = 1;
v___x_3153_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__15));
v___x_3154_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3153_, v___x_3152_);
return v___x_3154_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__17(void){
_start:
{
lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; 
v___x_3155_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__16, &l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__16_once, _init_l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__16);
v___x_3156_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__3, &l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__3);
v___x_3157_ = lean_string_append(v___x_3156_, v___x_3155_);
return v___x_3157_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__18(void){
_start:
{
lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; 
v___x_3158_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_3159_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__17, &l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__17_once, _init_l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__17);
v___x_3160_ = lean_string_append(v___x_3159_, v___x_3158_);
return v___x_3160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson(lean_object* v_json_3161_){
_start:
{
lean_object* v___x_3162_; lean_object* v___x_3163_; 
v___x_3162_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkspaceEdit_toJson___closed__0));
lean_inc(v_json_3161_);
v___x_3163_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__2(v_json_3161_, v___x_3162_);
if (lean_obj_tag(v___x_3163_) == 0)
{
lean_object* v_a_3164_; lean_object* v___x_3166_; uint8_t v_isShared_3167_; uint8_t v_isSharedCheck_3173_; 
lean_dec(v_json_3161_);
v_a_3164_ = lean_ctor_get(v___x_3163_, 0);
v_isSharedCheck_3173_ = !lean_is_exclusive(v___x_3163_);
if (v_isSharedCheck_3173_ == 0)
{
v___x_3166_ = v___x_3163_;
v_isShared_3167_ = v_isSharedCheck_3173_;
goto v_resetjp_3165_;
}
else
{
lean_inc(v_a_3164_);
lean_dec(v___x_3163_);
v___x_3166_ = lean_box(0);
v_isShared_3167_ = v_isSharedCheck_3173_;
goto v_resetjp_3165_;
}
v_resetjp_3165_:
{
lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3171_; 
v___x_3168_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__8, &l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__8);
v___x_3169_ = lean_string_append(v___x_3168_, v_a_3164_);
lean_dec(v_a_3164_);
if (v_isShared_3167_ == 0)
{
lean_ctor_set(v___x_3166_, 0, v___x_3169_);
v___x_3171_ = v___x_3166_;
goto v_reusejp_3170_;
}
else
{
lean_object* v_reuseFailAlloc_3172_; 
v_reuseFailAlloc_3172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3172_, 0, v___x_3169_);
v___x_3171_ = v_reuseFailAlloc_3172_;
goto v_reusejp_3170_;
}
v_reusejp_3170_:
{
return v___x_3171_;
}
}
}
else
{
if (lean_obj_tag(v___x_3163_) == 0)
{
lean_object* v_a_3174_; lean_object* v___x_3176_; uint8_t v_isShared_3177_; uint8_t v_isSharedCheck_3181_; 
lean_dec(v_json_3161_);
v_a_3174_ = lean_ctor_get(v___x_3163_, 0);
v_isSharedCheck_3181_ = !lean_is_exclusive(v___x_3163_);
if (v_isSharedCheck_3181_ == 0)
{
v___x_3176_ = v___x_3163_;
v_isShared_3177_ = v_isSharedCheck_3181_;
goto v_resetjp_3175_;
}
else
{
lean_inc(v_a_3174_);
lean_dec(v___x_3163_);
v___x_3176_ = lean_box(0);
v_isShared_3177_ = v_isSharedCheck_3181_;
goto v_resetjp_3175_;
}
v_resetjp_3175_:
{
lean_object* v___x_3179_; 
if (v_isShared_3177_ == 0)
{
lean_ctor_set_tag(v___x_3176_, 0);
v___x_3179_ = v___x_3176_;
goto v_reusejp_3178_;
}
else
{
lean_object* v_reuseFailAlloc_3180_; 
v_reuseFailAlloc_3180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3180_, 0, v_a_3174_);
v___x_3179_ = v_reuseFailAlloc_3180_;
goto v_reusejp_3178_;
}
v_reusejp_3178_:
{
return v___x_3179_;
}
}
}
else
{
lean_object* v_a_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; 
v_a_3182_ = lean_ctor_get(v___x_3163_, 0);
lean_inc(v_a_3182_);
lean_dec_ref_known(v___x_3163_, 1);
v___x_3183_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkspaceEdit_toJson___closed__1));
lean_inc(v_json_3161_);
v___x_3184_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__0(v_json_3161_, v___x_3183_);
if (lean_obj_tag(v___x_3184_) == 0)
{
lean_object* v_a_3185_; lean_object* v___x_3187_; uint8_t v_isShared_3188_; uint8_t v_isSharedCheck_3194_; 
lean_dec(v_a_3182_);
lean_dec(v_json_3161_);
v_a_3185_ = lean_ctor_get(v___x_3184_, 0);
v_isSharedCheck_3194_ = !lean_is_exclusive(v___x_3184_);
if (v_isSharedCheck_3194_ == 0)
{
v___x_3187_ = v___x_3184_;
v_isShared_3188_ = v_isSharedCheck_3194_;
goto v_resetjp_3186_;
}
else
{
lean_inc(v_a_3185_);
lean_dec(v___x_3184_);
v___x_3187_ = lean_box(0);
v_isShared_3188_ = v_isSharedCheck_3194_;
goto v_resetjp_3186_;
}
v_resetjp_3186_:
{
lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3192_; 
v___x_3189_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__13, &l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__13);
v___x_3190_ = lean_string_append(v___x_3189_, v_a_3185_);
lean_dec(v_a_3185_);
if (v_isShared_3188_ == 0)
{
lean_ctor_set(v___x_3187_, 0, v___x_3190_);
v___x_3192_ = v___x_3187_;
goto v_reusejp_3191_;
}
else
{
lean_object* v_reuseFailAlloc_3193_; 
v_reuseFailAlloc_3193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3193_, 0, v___x_3190_);
v___x_3192_ = v_reuseFailAlloc_3193_;
goto v_reusejp_3191_;
}
v_reusejp_3191_:
{
return v___x_3192_;
}
}
}
else
{
if (lean_obj_tag(v___x_3184_) == 0)
{
lean_object* v_a_3195_; lean_object* v___x_3197_; uint8_t v_isShared_3198_; uint8_t v_isSharedCheck_3202_; 
lean_dec(v_a_3182_);
lean_dec(v_json_3161_);
v_a_3195_ = lean_ctor_get(v___x_3184_, 0);
v_isSharedCheck_3202_ = !lean_is_exclusive(v___x_3184_);
if (v_isSharedCheck_3202_ == 0)
{
v___x_3197_ = v___x_3184_;
v_isShared_3198_ = v_isSharedCheck_3202_;
goto v_resetjp_3196_;
}
else
{
lean_inc(v_a_3195_);
lean_dec(v___x_3184_);
v___x_3197_ = lean_box(0);
v_isShared_3198_ = v_isSharedCheck_3202_;
goto v_resetjp_3196_;
}
v_resetjp_3196_:
{
lean_object* v___x_3200_; 
if (v_isShared_3198_ == 0)
{
lean_ctor_set_tag(v___x_3197_, 0);
v___x_3200_ = v___x_3197_;
goto v_reusejp_3199_;
}
else
{
lean_object* v_reuseFailAlloc_3201_; 
v_reuseFailAlloc_3201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3201_, 0, v_a_3195_);
v___x_3200_ = v_reuseFailAlloc_3201_;
goto v_reusejp_3199_;
}
v_reusejp_3199_:
{
return v___x_3200_;
}
}
}
else
{
lean_object* v_a_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; 
v_a_3203_ = lean_ctor_get(v___x_3184_, 0);
lean_inc(v_a_3203_);
lean_dec_ref_known(v___x_3184_, 1);
v___x_3204_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkspaceEdit_toJson___closed__2));
v___x_3205_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__1(v_json_3161_, v___x_3204_);
if (lean_obj_tag(v___x_3205_) == 0)
{
lean_object* v_a_3206_; lean_object* v___x_3208_; uint8_t v_isShared_3209_; uint8_t v_isSharedCheck_3215_; 
lean_dec(v_a_3203_);
lean_dec(v_a_3182_);
v_a_3206_ = lean_ctor_get(v___x_3205_, 0);
v_isSharedCheck_3215_ = !lean_is_exclusive(v___x_3205_);
if (v_isSharedCheck_3215_ == 0)
{
v___x_3208_ = v___x_3205_;
v_isShared_3209_ = v_isSharedCheck_3215_;
goto v_resetjp_3207_;
}
else
{
lean_inc(v_a_3206_);
lean_dec(v___x_3205_);
v___x_3208_ = lean_box(0);
v_isShared_3209_ = v_isSharedCheck_3215_;
goto v_resetjp_3207_;
}
v_resetjp_3207_:
{
lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3213_; 
v___x_3210_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__18, &l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__18_once, _init_l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson___closed__18);
v___x_3211_ = lean_string_append(v___x_3210_, v_a_3206_);
lean_dec(v_a_3206_);
if (v_isShared_3209_ == 0)
{
lean_ctor_set(v___x_3208_, 0, v___x_3211_);
v___x_3213_ = v___x_3208_;
goto v_reusejp_3212_;
}
else
{
lean_object* v_reuseFailAlloc_3214_; 
v_reuseFailAlloc_3214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3214_, 0, v___x_3211_);
v___x_3213_ = v_reuseFailAlloc_3214_;
goto v_reusejp_3212_;
}
v_reusejp_3212_:
{
return v___x_3213_;
}
}
}
else
{
if (lean_obj_tag(v___x_3205_) == 0)
{
lean_object* v_a_3216_; lean_object* v___x_3218_; uint8_t v_isShared_3219_; uint8_t v_isSharedCheck_3223_; 
lean_dec(v_a_3203_);
lean_dec(v_a_3182_);
v_a_3216_ = lean_ctor_get(v___x_3205_, 0);
v_isSharedCheck_3223_ = !lean_is_exclusive(v___x_3205_);
if (v_isSharedCheck_3223_ == 0)
{
v___x_3218_ = v___x_3205_;
v_isShared_3219_ = v_isSharedCheck_3223_;
goto v_resetjp_3217_;
}
else
{
lean_inc(v_a_3216_);
lean_dec(v___x_3205_);
v___x_3218_ = lean_box(0);
v_isShared_3219_ = v_isSharedCheck_3223_;
goto v_resetjp_3217_;
}
v_resetjp_3217_:
{
lean_object* v___x_3221_; 
if (v_isShared_3219_ == 0)
{
lean_ctor_set_tag(v___x_3218_, 0);
v___x_3221_ = v___x_3218_;
goto v_reusejp_3220_;
}
else
{
lean_object* v_reuseFailAlloc_3222_; 
v_reuseFailAlloc_3222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3222_, 0, v_a_3216_);
v___x_3221_ = v_reuseFailAlloc_3222_;
goto v_reusejp_3220_;
}
v_reusejp_3220_:
{
return v___x_3221_;
}
}
}
else
{
lean_object* v_a_3224_; lean_object* v___x_3226_; uint8_t v_isShared_3227_; uint8_t v_isSharedCheck_3232_; 
v_a_3224_ = lean_ctor_get(v___x_3205_, 0);
v_isSharedCheck_3232_ = !lean_is_exclusive(v___x_3205_);
if (v_isSharedCheck_3232_ == 0)
{
v___x_3226_ = v___x_3205_;
v_isShared_3227_ = v_isSharedCheck_3232_;
goto v_resetjp_3225_;
}
else
{
lean_inc(v_a_3224_);
lean_dec(v___x_3205_);
v___x_3226_ = lean_box(0);
v_isShared_3227_ = v_isSharedCheck_3232_;
goto v_resetjp_3225_;
}
v_resetjp_3225_:
{
lean_object* v___x_3228_; lean_object* v___x_3230_; 
v___x_3228_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3228_, 0, v_a_3182_);
lean_ctor_set(v___x_3228_, 1, v_a_3203_);
lean_ctor_set(v___x_3228_, 2, v_a_3224_);
if (v_isShared_3227_ == 0)
{
lean_ctor_set(v___x_3226_, 0, v___x_3228_);
v___x_3230_ = v___x_3226_;
goto v_reusejp_3229_;
}
else
{
lean_object* v_reuseFailAlloc_3231_; 
v_reuseFailAlloc_3231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3231_, 0, v___x_3228_);
v___x_3230_ = v_reuseFailAlloc_3231_;
goto v_reusejp_3229_;
}
v_reusejp_3229_:
{
return v___x_3230_;
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__1_spec__2_spec__4_spec__7(lean_object* v_cmp_3233_, lean_object* v_00_u03b2_3234_, lean_object* v_k_3235_, lean_object* v_v_3236_, lean_object* v_t_3237_, lean_object* v_hl_3238_){
_start:
{
lean_object* v___x_3239_; 
v___x_3239_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Json_FromToJson_Extra_0__Lean_TreeMap_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEdit_fromJson_spec__1_spec__2_spec__4_spec__7___redArg(v_cmp_3233_, v_k_3235_, v_v_3236_, v_t_3237_);
return v___x_3239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_WorkspaceEdit_instAppend___lam__0(lean_object* v_b_u2082_3245_, lean_object* v_x_3246_){
_start:
{
lean_object* v___x_3247_; 
v___x_3247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3247_, 0, v_b_u2082_3245_);
return v___x_3247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_WorkspaceEdit_instAppend___lam__0___boxed(lean_object* v_b_u2082_3248_, lean_object* v_x_3249_){
_start:
{
lean_object* v_res_3250_; 
v_res_3250_ = l_Lean_Lsp_WorkspaceEdit_instAppend___lam__0(v_b_u2082_3248_, v_x_3249_);
lean_dec(v_x_3249_);
return v_res_3250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_WorkspaceEdit_instAppend___lam__1(lean_object* v___x_3251_, lean_object* v_t_3252_, lean_object* v_a_3253_, lean_object* v_b_u2082_3254_){
_start:
{
lean_object* v___f_3255_; lean_object* v___x_3256_; 
v___f_3255_ = lean_alloc_closure((void*)(l_Lean_Lsp_WorkspaceEdit_instAppend___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3255_, 0, v_b_u2082_3254_);
v___x_3256_ = l_Std_DTreeMap_Internal_Impl_Const_alter___redArg(v___x_3251_, v_a_3253_, v___f_3255_, v_t_3252_);
return v___x_3256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_WorkspaceEdit_instAppend___lam__2(lean_object* v_b_u2082_3257_, lean_object* v_x_3258_){
_start:
{
if (lean_obj_tag(v_x_3258_) == 0)
{
lean_object* v___x_3259_; 
v___x_3259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3259_, 0, v_b_u2082_3257_);
return v___x_3259_;
}
else
{
lean_object* v_val_3260_; lean_object* v___x_3262_; uint8_t v_isShared_3263_; uint8_t v_isSharedCheck_3268_; 
v_val_3260_ = lean_ctor_get(v_x_3258_, 0);
v_isSharedCheck_3268_ = !lean_is_exclusive(v_x_3258_);
if (v_isSharedCheck_3268_ == 0)
{
v___x_3262_ = v_x_3258_;
v_isShared_3263_ = v_isSharedCheck_3268_;
goto v_resetjp_3261_;
}
else
{
lean_inc(v_val_3260_);
lean_dec(v_x_3258_);
v___x_3262_ = lean_box(0);
v_isShared_3263_ = v_isSharedCheck_3268_;
goto v_resetjp_3261_;
}
v_resetjp_3261_:
{
lean_object* v___x_3264_; lean_object* v___x_3266_; 
v___x_3264_ = l_Array_append___redArg(v_val_3260_, v_b_u2082_3257_);
lean_dec_ref(v_b_u2082_3257_);
if (v_isShared_3263_ == 0)
{
lean_ctor_set(v___x_3262_, 0, v___x_3264_);
v___x_3266_ = v___x_3262_;
goto v_reusejp_3265_;
}
else
{
lean_object* v_reuseFailAlloc_3267_; 
v_reuseFailAlloc_3267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3267_, 0, v___x_3264_);
v___x_3266_ = v_reuseFailAlloc_3267_;
goto v_reusejp_3265_;
}
v_reusejp_3265_:
{
return v___x_3266_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_WorkspaceEdit_instAppend___lam__3(lean_object* v___x_3269_, lean_object* v_t_3270_, lean_object* v_a_3271_, lean_object* v_b_u2082_3272_){
_start:
{
lean_object* v___f_3273_; lean_object* v___x_3274_; 
v___f_3273_ = lean_alloc_closure((void*)(l_Lean_Lsp_WorkspaceEdit_instAppend___lam__2), 2, 1);
lean_closure_set(v___f_3273_, 0, v_b_u2082_3272_);
v___x_3274_ = l_Std_DTreeMap_Internal_Impl_Const_alter___redArg(v___x_3269_, v_a_3271_, v___f_3273_, v_t_3270_);
return v___x_3274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_WorkspaceEdit_instAppend___lam__4(lean_object* v_x_3279_, lean_object* v_y_3280_){
_start:
{
lean_object* v_changes_x3f_3281_; lean_object* v_documentChanges_x3f_3282_; lean_object* v_changeAnnotations_x3f_3283_; lean_object* v___y_3285_; lean_object* v___y_3286_; lean_object* v___y_3322_; 
v_changes_x3f_3281_ = lean_ctor_get(v_y_3280_, 0);
lean_inc(v_changes_x3f_3281_);
v_documentChanges_x3f_3282_ = lean_ctor_get(v_y_3280_, 1);
lean_inc(v_documentChanges_x3f_3282_);
v_changeAnnotations_x3f_3283_ = lean_ctor_get(v_y_3280_, 2);
lean_inc(v_changeAnnotations_x3f_3283_);
lean_dec_ref(v_y_3280_);
if (lean_obj_tag(v_changes_x3f_3281_) == 0)
{
lean_object* v_changes_x3f_3335_; 
v_changes_x3f_3335_ = lean_ctor_get(v_x_3279_, 0);
lean_inc(v_changes_x3f_3335_);
v___y_3322_ = v_changes_x3f_3335_;
goto v___jp_3321_;
}
else
{
lean_object* v_changes_x3f_3336_; 
v_changes_x3f_3336_ = lean_ctor_get(v_x_3279_, 0);
lean_inc(v_changes_x3f_3336_);
if (lean_obj_tag(v_changes_x3f_3336_) == 0)
{
v___y_3322_ = v_changes_x3f_3281_;
goto v___jp_3321_;
}
else
{
lean_object* v_val_3337_; lean_object* v_val_3338_; lean_object* v___x_3340_; uint8_t v_isShared_3341_; uint8_t v_isSharedCheck_3347_; 
v_val_3337_ = lean_ctor_get(v_changes_x3f_3281_, 0);
lean_inc(v_val_3337_);
lean_dec_ref_known(v_changes_x3f_3281_, 1);
v_val_3338_ = lean_ctor_get(v_changes_x3f_3336_, 0);
v_isSharedCheck_3347_ = !lean_is_exclusive(v_changes_x3f_3336_);
if (v_isSharedCheck_3347_ == 0)
{
v___x_3340_ = v_changes_x3f_3336_;
v_isShared_3341_ = v_isSharedCheck_3347_;
goto v_resetjp_3339_;
}
else
{
lean_inc(v_val_3338_);
lean_dec(v_changes_x3f_3336_);
v___x_3340_ = lean_box(0);
v_isShared_3341_ = v_isSharedCheck_3347_;
goto v_resetjp_3339_;
}
v_resetjp_3339_:
{
lean_object* v___f_3342_; lean_object* v___x_3343_; lean_object* v___x_3345_; 
v___f_3342_ = ((lean_object*)(l_Lean_Lsp_WorkspaceEdit_instAppend___lam__4___closed__1));
v___x_3343_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3342_, v_val_3338_, v_val_3337_);
if (v_isShared_3341_ == 0)
{
lean_ctor_set(v___x_3340_, 0, v___x_3343_);
v___x_3345_ = v___x_3340_;
goto v_reusejp_3344_;
}
else
{
lean_object* v_reuseFailAlloc_3346_; 
v_reuseFailAlloc_3346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3346_, 0, v___x_3343_);
v___x_3345_ = v_reuseFailAlloc_3346_;
goto v_reusejp_3344_;
}
v_reusejp_3344_:
{
v___y_3322_ = v___x_3345_;
goto v___jp_3321_;
}
}
}
}
v___jp_3284_:
{
if (lean_obj_tag(v_changeAnnotations_x3f_3283_) == 0)
{
lean_object* v_changeAnnotations_x3f_3287_; lean_object* v___x_3289_; uint8_t v_isShared_3290_; uint8_t v_isSharedCheck_3294_; 
v_changeAnnotations_x3f_3287_ = lean_ctor_get(v_x_3279_, 2);
v_isSharedCheck_3294_ = !lean_is_exclusive(v_x_3279_);
if (v_isSharedCheck_3294_ == 0)
{
lean_object* v_unused_3295_; lean_object* v_unused_3296_; 
v_unused_3295_ = lean_ctor_get(v_x_3279_, 1);
lean_dec(v_unused_3295_);
v_unused_3296_ = lean_ctor_get(v_x_3279_, 0);
lean_dec(v_unused_3296_);
v___x_3289_ = v_x_3279_;
v_isShared_3290_ = v_isSharedCheck_3294_;
goto v_resetjp_3288_;
}
else
{
lean_inc(v_changeAnnotations_x3f_3287_);
lean_dec(v_x_3279_);
v___x_3289_ = lean_box(0);
v_isShared_3290_ = v_isSharedCheck_3294_;
goto v_resetjp_3288_;
}
v_resetjp_3288_:
{
lean_object* v___x_3292_; 
if (v_isShared_3290_ == 0)
{
lean_ctor_set(v___x_3289_, 1, v___y_3286_);
lean_ctor_set(v___x_3289_, 0, v___y_3285_);
v___x_3292_ = v___x_3289_;
goto v_reusejp_3291_;
}
else
{
lean_object* v_reuseFailAlloc_3293_; 
v_reuseFailAlloc_3293_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3293_, 0, v___y_3285_);
lean_ctor_set(v_reuseFailAlloc_3293_, 1, v___y_3286_);
lean_ctor_set(v_reuseFailAlloc_3293_, 2, v_changeAnnotations_x3f_3287_);
v___x_3292_ = v_reuseFailAlloc_3293_;
goto v_reusejp_3291_;
}
v_reusejp_3291_:
{
return v___x_3292_;
}
}
}
else
{
lean_object* v_changeAnnotations_x3f_3297_; lean_object* v___x_3299_; uint8_t v_isShared_3300_; uint8_t v_isSharedCheck_3318_; 
v_changeAnnotations_x3f_3297_ = lean_ctor_get(v_x_3279_, 2);
v_isSharedCheck_3318_ = !lean_is_exclusive(v_x_3279_);
if (v_isSharedCheck_3318_ == 0)
{
lean_object* v_unused_3319_; lean_object* v_unused_3320_; 
v_unused_3319_ = lean_ctor_get(v_x_3279_, 1);
lean_dec(v_unused_3319_);
v_unused_3320_ = lean_ctor_get(v_x_3279_, 0);
lean_dec(v_unused_3320_);
v___x_3299_ = v_x_3279_;
v_isShared_3300_ = v_isSharedCheck_3318_;
goto v_resetjp_3298_;
}
else
{
lean_inc(v_changeAnnotations_x3f_3297_);
lean_dec(v_x_3279_);
v___x_3299_ = lean_box(0);
v_isShared_3300_ = v_isSharedCheck_3318_;
goto v_resetjp_3298_;
}
v_resetjp_3298_:
{
if (lean_obj_tag(v_changeAnnotations_x3f_3297_) == 0)
{
lean_object* v___x_3302_; 
if (v_isShared_3300_ == 0)
{
lean_ctor_set(v___x_3299_, 2, v_changeAnnotations_x3f_3283_);
lean_ctor_set(v___x_3299_, 1, v___y_3286_);
lean_ctor_set(v___x_3299_, 0, v___y_3285_);
v___x_3302_ = v___x_3299_;
goto v_reusejp_3301_;
}
else
{
lean_object* v_reuseFailAlloc_3303_; 
v_reuseFailAlloc_3303_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3303_, 0, v___y_3285_);
lean_ctor_set(v_reuseFailAlloc_3303_, 1, v___y_3286_);
lean_ctor_set(v_reuseFailAlloc_3303_, 2, v_changeAnnotations_x3f_3283_);
v___x_3302_ = v_reuseFailAlloc_3303_;
goto v_reusejp_3301_;
}
v_reusejp_3301_:
{
return v___x_3302_;
}
}
else
{
lean_object* v_val_3304_; lean_object* v_val_3305_; lean_object* v___x_3307_; uint8_t v_isShared_3308_; uint8_t v_isSharedCheck_3317_; 
v_val_3304_ = lean_ctor_get(v_changeAnnotations_x3f_3283_, 0);
lean_inc(v_val_3304_);
lean_dec_ref_known(v_changeAnnotations_x3f_3283_, 1);
v_val_3305_ = lean_ctor_get(v_changeAnnotations_x3f_3297_, 0);
v_isSharedCheck_3317_ = !lean_is_exclusive(v_changeAnnotations_x3f_3297_);
if (v_isSharedCheck_3317_ == 0)
{
v___x_3307_ = v_changeAnnotations_x3f_3297_;
v_isShared_3308_ = v_isSharedCheck_3317_;
goto v_resetjp_3306_;
}
else
{
lean_inc(v_val_3305_);
lean_dec(v_changeAnnotations_x3f_3297_);
v___x_3307_ = lean_box(0);
v_isShared_3308_ = v_isSharedCheck_3317_;
goto v_resetjp_3306_;
}
v_resetjp_3306_:
{
lean_object* v___f_3309_; lean_object* v___x_3310_; lean_object* v___x_3312_; 
v___f_3309_ = ((lean_object*)(l_Lean_Lsp_WorkspaceEdit_instAppend___lam__4___closed__0));
v___x_3310_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_3309_, v_val_3305_, v_val_3304_);
if (v_isShared_3308_ == 0)
{
lean_ctor_set(v___x_3307_, 0, v___x_3310_);
v___x_3312_ = v___x_3307_;
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
if (v_isShared_3300_ == 0)
{
lean_ctor_set(v___x_3299_, 2, v___x_3312_);
lean_ctor_set(v___x_3299_, 1, v___y_3286_);
lean_ctor_set(v___x_3299_, 0, v___y_3285_);
v___x_3314_ = v___x_3299_;
goto v_reusejp_3313_;
}
else
{
lean_object* v_reuseFailAlloc_3315_; 
v_reuseFailAlloc_3315_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3315_, 0, v___y_3285_);
lean_ctor_set(v_reuseFailAlloc_3315_, 1, v___y_3286_);
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
if (lean_obj_tag(v_documentChanges_x3f_3282_) == 0)
{
lean_object* v_documentChanges_x3f_3323_; 
v_documentChanges_x3f_3323_ = lean_ctor_get(v_x_3279_, 1);
lean_inc(v_documentChanges_x3f_3323_);
v___y_3285_ = v___y_3322_;
v___y_3286_ = v_documentChanges_x3f_3323_;
goto v___jp_3284_;
}
else
{
lean_object* v_documentChanges_x3f_3324_; 
v_documentChanges_x3f_3324_ = lean_ctor_get(v_x_3279_, 1);
lean_inc(v_documentChanges_x3f_3324_);
if (lean_obj_tag(v_documentChanges_x3f_3324_) == 0)
{
v___y_3285_ = v___y_3322_;
v___y_3286_ = v_documentChanges_x3f_3282_;
goto v___jp_3284_;
}
else
{
lean_object* v_val_3325_; lean_object* v_val_3326_; lean_object* v___x_3328_; uint8_t v_isShared_3329_; uint8_t v_isSharedCheck_3334_; 
v_val_3325_ = lean_ctor_get(v_documentChanges_x3f_3282_, 0);
lean_inc(v_val_3325_);
lean_dec_ref_known(v_documentChanges_x3f_3282_, 1);
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
v___y_3285_ = v___y_3322_;
v___y_3286_ = v___x_3332_;
goto v___jp_3284_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_WorkspaceEdit_ofTextDocumentEdit(lean_object* v_e_3350_){
_start:
{
lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; 
v___x_3351_ = lean_box(0);
v___x_3352_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3352_, 0, v_e_3350_);
v___x_3353_ = lean_unsigned_to_nat(1u);
v___x_3354_ = lean_mk_empty_array_with_capacity(v___x_3353_);
v___x_3355_ = lean_array_push(v___x_3354_, v___x_3352_);
v___x_3356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3356_, 0, v___x_3355_);
v___x_3357_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3357_, 0, v___x_3351_);
lean_ctor_set(v___x_3357_, 1, v___x_3356_);
lean_ctor_set(v___x_3357_, 2, v___x_3351_);
return v___x_3357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_WorkspaceEdit_ofTextEdit(lean_object* v_doc_3358_, lean_object* v_te_3359_){
_start:
{
lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; 
v___x_3360_ = lean_unsigned_to_nat(1u);
v___x_3361_ = lean_mk_empty_array_with_capacity(v___x_3360_);
v___x_3362_ = lean_array_push(v___x_3361_, v_te_3359_);
v___x_3363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3363_, 0, v_doc_3358_);
lean_ctor_set(v___x_3363_, 1, v___x_3362_);
v___x_3364_ = l_Lean_Lsp_WorkspaceEdit_ofTextDocumentEdit(v___x_3363_);
return v___x_3364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonApplyWorkspaceEditParams_toJson(lean_object* v_x_3366_){
_start:
{
lean_object* v_label_x3f_3367_; lean_object* v_edit_3368_; lean_object* v___x_3370_; uint8_t v_isShared_3371_; uint8_t v_isSharedCheck_3386_; 
v_label_x3f_3367_ = lean_ctor_get(v_x_3366_, 0);
v_edit_3368_ = lean_ctor_get(v_x_3366_, 1);
v_isSharedCheck_3386_ = !lean_is_exclusive(v_x_3366_);
if (v_isSharedCheck_3386_ == 0)
{
v___x_3370_ = v_x_3366_;
v_isShared_3371_ = v_isSharedCheck_3386_;
goto v_resetjp_3369_;
}
else
{
lean_inc(v_edit_3368_);
lean_inc(v_label_x3f_3367_);
lean_dec(v_x_3366_);
v___x_3370_ = lean_box(0);
v_isShared_3371_ = v_isSharedCheck_3386_;
goto v_resetjp_3369_;
}
v_resetjp_3369_:
{
lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3377_; 
v___x_3372_ = ((lean_object*)(l_Lean_Lsp_instToJsonChangeAnnotation_toJson___closed__0));
v___x_3373_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextEdit_toJson_spec__1(v___x_3372_, v_label_x3f_3367_);
v___x_3374_ = ((lean_object*)(l_Lean_Lsp_instToJsonApplyWorkspaceEditParams_toJson___closed__0));
v___x_3375_ = l_Lean_Lsp_instToJsonWorkspaceEdit_toJson(v_edit_3368_);
if (v_isShared_3371_ == 0)
{
lean_ctor_set(v___x_3370_, 1, v___x_3375_);
lean_ctor_set(v___x_3370_, 0, v___x_3374_);
v___x_3377_ = v___x_3370_;
goto v_reusejp_3376_;
}
else
{
lean_object* v_reuseFailAlloc_3385_; 
v_reuseFailAlloc_3385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3385_, 0, v___x_3374_);
lean_ctor_set(v_reuseFailAlloc_3385_, 1, v___x_3375_);
v___x_3377_ = v_reuseFailAlloc_3385_;
goto v_reusejp_3376_;
}
v_reusejp_3376_:
{
lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; 
v___x_3378_ = lean_box(0);
v___x_3379_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3379_, 0, v___x_3377_);
lean_ctor_set(v___x_3379_, 1, v___x_3378_);
v___x_3380_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3380_, 0, v___x_3379_);
lean_ctor_set(v___x_3380_, 1, v___x_3378_);
v___x_3381_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3381_, 0, v___x_3373_);
lean_ctor_set(v___x_3381_, 1, v___x_3380_);
v___x_3382_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__2));
v___x_3383_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLocation_toJson_spec__0(v___x_3381_, v___x_3382_);
v___x_3384_ = l_Lean_Json_mkObj(v___x_3383_);
lean_dec(v___x_3383_);
return v___x_3384_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson_spec__0(lean_object* v_j_3389_, lean_object* v_k_3390_){
_start:
{
lean_object* v___x_3391_; lean_object* v___x_3392_; 
v___x_3391_ = l_Lean_Json_getObjValD(v_j_3389_, v_k_3390_);
v___x_3392_ = l_Lean_Lsp_instFromJsonWorkspaceEdit_fromJson(v___x_3391_);
return v___x_3392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson_spec__0___boxed(lean_object* v_j_3393_, lean_object* v_k_3394_){
_start:
{
lean_object* v_res_3395_; 
v_res_3395_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson_spec__0(v_j_3393_, v_k_3394_);
lean_dec_ref(v_k_3394_);
return v_res_3395_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__2(void){
_start:
{
uint8_t v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; 
v___x_3401_ = 1;
v___x_3402_ = ((lean_object*)(l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__1));
v___x_3403_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3402_, v___x_3401_);
return v___x_3403_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__3(void){
_start:
{
lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; 
v___x_3404_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__5));
v___x_3405_ = lean_obj_once(&l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__2, &l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__2);
v___x_3406_ = lean_string_append(v___x_3405_, v___x_3404_);
return v___x_3406_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__6(void){
_start:
{
uint8_t v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; 
v___x_3410_ = 1;
v___x_3411_ = ((lean_object*)(l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__5));
v___x_3412_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3411_, v___x_3410_);
return v___x_3412_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__7(void){
_start:
{
lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; 
v___x_3413_ = lean_obj_once(&l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__6, &l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__6);
v___x_3414_ = lean_obj_once(&l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__3);
v___x_3415_ = lean_string_append(v___x_3414_, v___x_3413_);
return v___x_3415_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__8(void){
_start:
{
lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; 
v___x_3416_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_3417_ = lean_obj_once(&l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__7);
v___x_3418_ = lean_string_append(v___x_3417_, v___x_3416_);
return v___x_3418_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__10(void){
_start:
{
uint8_t v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; 
v___x_3421_ = 1;
v___x_3422_ = ((lean_object*)(l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__9));
v___x_3423_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3422_, v___x_3421_);
return v___x_3423_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__11(void){
_start:
{
lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; 
v___x_3424_ = lean_obj_once(&l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__10, &l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__10);
v___x_3425_ = lean_obj_once(&l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__3);
v___x_3426_ = lean_string_append(v___x_3425_, v___x_3424_);
return v___x_3426_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__12(void){
_start:
{
lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; 
v___x_3427_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_3428_ = lean_obj_once(&l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__11, &l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__11);
v___x_3429_ = lean_string_append(v___x_3428_, v___x_3427_);
return v___x_3429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson(lean_object* v_json_3430_){
_start:
{
lean_object* v___x_3431_; lean_object* v___x_3432_; 
v___x_3431_ = ((lean_object*)(l_Lean_Lsp_instToJsonChangeAnnotation_toJson___closed__0));
lean_inc(v_json_3430_);
v___x_3432_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextEdit_fromJson_spec__1(v_json_3430_, v___x_3431_);
if (lean_obj_tag(v___x_3432_) == 0)
{
lean_object* v_a_3433_; lean_object* v___x_3435_; uint8_t v_isShared_3436_; uint8_t v_isSharedCheck_3442_; 
lean_dec(v_json_3430_);
v_a_3433_ = lean_ctor_get(v___x_3432_, 0);
v_isSharedCheck_3442_ = !lean_is_exclusive(v___x_3432_);
if (v_isSharedCheck_3442_ == 0)
{
v___x_3435_ = v___x_3432_;
v_isShared_3436_ = v_isSharedCheck_3442_;
goto v_resetjp_3434_;
}
else
{
lean_inc(v_a_3433_);
lean_dec(v___x_3432_);
v___x_3435_ = lean_box(0);
v_isShared_3436_ = v_isSharedCheck_3442_;
goto v_resetjp_3434_;
}
v_resetjp_3434_:
{
lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3440_; 
v___x_3437_ = lean_obj_once(&l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__8);
v___x_3438_ = lean_string_append(v___x_3437_, v_a_3433_);
lean_dec(v_a_3433_);
if (v_isShared_3436_ == 0)
{
lean_ctor_set(v___x_3435_, 0, v___x_3438_);
v___x_3440_ = v___x_3435_;
goto v_reusejp_3439_;
}
else
{
lean_object* v_reuseFailAlloc_3441_; 
v_reuseFailAlloc_3441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3441_, 0, v___x_3438_);
v___x_3440_ = v_reuseFailAlloc_3441_;
goto v_reusejp_3439_;
}
v_reusejp_3439_:
{
return v___x_3440_;
}
}
}
else
{
if (lean_obj_tag(v___x_3432_) == 0)
{
lean_object* v_a_3443_; lean_object* v___x_3445_; uint8_t v_isShared_3446_; uint8_t v_isSharedCheck_3450_; 
lean_dec(v_json_3430_);
v_a_3443_ = lean_ctor_get(v___x_3432_, 0);
v_isSharedCheck_3450_ = !lean_is_exclusive(v___x_3432_);
if (v_isSharedCheck_3450_ == 0)
{
v___x_3445_ = v___x_3432_;
v_isShared_3446_ = v_isSharedCheck_3450_;
goto v_resetjp_3444_;
}
else
{
lean_inc(v_a_3443_);
lean_dec(v___x_3432_);
v___x_3445_ = lean_box(0);
v_isShared_3446_ = v_isSharedCheck_3450_;
goto v_resetjp_3444_;
}
v_resetjp_3444_:
{
lean_object* v___x_3448_; 
if (v_isShared_3446_ == 0)
{
lean_ctor_set_tag(v___x_3445_, 0);
v___x_3448_ = v___x_3445_;
goto v_reusejp_3447_;
}
else
{
lean_object* v_reuseFailAlloc_3449_; 
v_reuseFailAlloc_3449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3449_, 0, v_a_3443_);
v___x_3448_ = v_reuseFailAlloc_3449_;
goto v_reusejp_3447_;
}
v_reusejp_3447_:
{
return v___x_3448_;
}
}
}
else
{
lean_object* v_a_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; 
v_a_3451_ = lean_ctor_get(v___x_3432_, 0);
lean_inc(v_a_3451_);
lean_dec_ref_known(v___x_3432_, 1);
v___x_3452_ = ((lean_object*)(l_Lean_Lsp_instToJsonApplyWorkspaceEditParams_toJson___closed__0));
v___x_3453_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson_spec__0(v_json_3430_, v___x_3452_);
if (lean_obj_tag(v___x_3453_) == 0)
{
lean_object* v_a_3454_; lean_object* v___x_3456_; uint8_t v_isShared_3457_; uint8_t v_isSharedCheck_3463_; 
lean_dec(v_a_3451_);
v_a_3454_ = lean_ctor_get(v___x_3453_, 0);
v_isSharedCheck_3463_ = !lean_is_exclusive(v___x_3453_);
if (v_isSharedCheck_3463_ == 0)
{
v___x_3456_ = v___x_3453_;
v_isShared_3457_ = v_isSharedCheck_3463_;
goto v_resetjp_3455_;
}
else
{
lean_inc(v_a_3454_);
lean_dec(v___x_3453_);
v___x_3456_ = lean_box(0);
v_isShared_3457_ = v_isSharedCheck_3463_;
goto v_resetjp_3455_;
}
v_resetjp_3455_:
{
lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3461_; 
v___x_3458_ = lean_obj_once(&l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__12, &l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonApplyWorkspaceEditParams_fromJson___closed__12);
v___x_3459_ = lean_string_append(v___x_3458_, v_a_3454_);
lean_dec(v_a_3454_);
if (v_isShared_3457_ == 0)
{
lean_ctor_set(v___x_3456_, 0, v___x_3459_);
v___x_3461_ = v___x_3456_;
goto v_reusejp_3460_;
}
else
{
lean_object* v_reuseFailAlloc_3462_; 
v_reuseFailAlloc_3462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3462_, 0, v___x_3459_);
v___x_3461_ = v_reuseFailAlloc_3462_;
goto v_reusejp_3460_;
}
v_reusejp_3460_:
{
return v___x_3461_;
}
}
}
else
{
if (lean_obj_tag(v___x_3453_) == 0)
{
lean_object* v_a_3464_; lean_object* v___x_3466_; uint8_t v_isShared_3467_; uint8_t v_isSharedCheck_3471_; 
lean_dec(v_a_3451_);
v_a_3464_ = lean_ctor_get(v___x_3453_, 0);
v_isSharedCheck_3471_ = !lean_is_exclusive(v___x_3453_);
if (v_isSharedCheck_3471_ == 0)
{
v___x_3466_ = v___x_3453_;
v_isShared_3467_ = v_isSharedCheck_3471_;
goto v_resetjp_3465_;
}
else
{
lean_inc(v_a_3464_);
lean_dec(v___x_3453_);
v___x_3466_ = lean_box(0);
v_isShared_3467_ = v_isSharedCheck_3471_;
goto v_resetjp_3465_;
}
v_resetjp_3465_:
{
lean_object* v___x_3469_; 
if (v_isShared_3467_ == 0)
{
lean_ctor_set_tag(v___x_3466_, 0);
v___x_3469_ = v___x_3466_;
goto v_reusejp_3468_;
}
else
{
lean_object* v_reuseFailAlloc_3470_; 
v_reuseFailAlloc_3470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3470_, 0, v_a_3464_);
v___x_3469_ = v_reuseFailAlloc_3470_;
goto v_reusejp_3468_;
}
v_reusejp_3468_:
{
return v___x_3469_;
}
}
}
else
{
lean_object* v_a_3472_; lean_object* v___x_3474_; uint8_t v_isShared_3475_; uint8_t v_isSharedCheck_3480_; 
v_a_3472_ = lean_ctor_get(v___x_3453_, 0);
v_isSharedCheck_3480_ = !lean_is_exclusive(v___x_3453_);
if (v_isSharedCheck_3480_ == 0)
{
v___x_3474_ = v___x_3453_;
v_isShared_3475_ = v_isSharedCheck_3480_;
goto v_resetjp_3473_;
}
else
{
lean_inc(v_a_3472_);
lean_dec(v___x_3453_);
v___x_3474_ = lean_box(0);
v_isShared_3475_ = v_isSharedCheck_3480_;
goto v_resetjp_3473_;
}
v_resetjp_3473_:
{
lean_object* v___x_3476_; lean_object* v___x_3478_; 
v___x_3476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3476_, 0, v_a_3451_);
lean_ctor_set(v___x_3476_, 1, v_a_3472_);
if (v_isShared_3475_ == 0)
{
lean_ctor_set(v___x_3474_, 0, v___x_3476_);
v___x_3478_ = v___x_3474_;
goto v_reusejp_3477_;
}
else
{
lean_object* v_reuseFailAlloc_3479_; 
v_reuseFailAlloc_3479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3479_, 0, v___x_3476_);
v___x_3478_ = v_reuseFailAlloc_3479_;
goto v_reusejp_3477_;
}
v_reusejp_3477_:
{
return v___x_3478_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonTextDocumentItem_toJson(lean_object* v_x_3485_){
_start:
{
lean_object* v_uri_3486_; lean_object* v_languageId_3487_; lean_object* v_version_3488_; lean_object* v_text_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; 
v_uri_3486_ = lean_ctor_get(v_x_3485_, 0);
lean_inc_ref(v_uri_3486_);
v_languageId_3487_ = lean_ctor_get(v_x_3485_, 1);
lean_inc_ref(v_languageId_3487_);
v_version_3488_ = lean_ctor_get(v_x_3485_, 2);
lean_inc(v_version_3488_);
v_text_3489_ = lean_ctor_get(v_x_3485_, 3);
lean_inc_ref(v_text_3489_);
lean_dec_ref(v_x_3485_);
v___x_3490_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__0));
v___x_3491_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3491_, 0, v_uri_3486_);
v___x_3492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3492_, 0, v___x_3490_);
lean_ctor_set(v___x_3492_, 1, v___x_3491_);
v___x_3493_ = lean_box(0);
v___x_3494_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3494_, 0, v___x_3492_);
lean_ctor_set(v___x_3494_, 1, v___x_3493_);
v___x_3495_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextDocumentItem_toJson___closed__0));
v___x_3496_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3496_, 0, v_languageId_3487_);
v___x_3497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3497_, 0, v___x_3495_);
lean_ctor_set(v___x_3497_, 1, v___x_3496_);
v___x_3498_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3498_, 0, v___x_3497_);
lean_ctor_set(v___x_3498_, 1, v___x_3493_);
v___x_3499_ = ((lean_object*)(l_Lean_Lsp_instToJsonVersionedTextDocumentIdentifier_toJson___closed__0));
v___x_3500_ = l_Lean_JsonNumber_fromNat(v_version_3488_);
v___x_3501_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3501_, 0, v___x_3500_);
v___x_3502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3502_, 0, v___x_3499_);
lean_ctor_set(v___x_3502_, 1, v___x_3501_);
v___x_3503_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3503_, 0, v___x_3502_);
lean_ctor_set(v___x_3503_, 1, v___x_3493_);
v___x_3504_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextDocumentItem_toJson___closed__1));
v___x_3505_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3505_, 0, v_text_3489_);
v___x_3506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3506_, 0, v___x_3504_);
lean_ctor_set(v___x_3506_, 1, v___x_3505_);
v___x_3507_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3507_, 0, v___x_3506_);
lean_ctor_set(v___x_3507_, 1, v___x_3493_);
v___x_3508_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3508_, 0, v___x_3507_);
lean_ctor_set(v___x_3508_, 1, v___x_3493_);
v___x_3509_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3509_, 0, v___x_3503_);
lean_ctor_set(v___x_3509_, 1, v___x_3508_);
v___x_3510_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3510_, 0, v___x_3498_);
lean_ctor_set(v___x_3510_, 1, v___x_3509_);
v___x_3511_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3511_, 0, v___x_3494_);
lean_ctor_set(v___x_3511_, 1, v___x_3510_);
v___x_3512_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__2));
v___x_3513_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLocation_toJson_spec__0(v___x_3511_, v___x_3512_);
v___x_3514_ = l_Lean_Json_mkObj(v___x_3513_);
lean_dec(v___x_3513_);
return v___x_3514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentItem_fromJson_spec__0(lean_object* v_j_3517_, lean_object* v_k_3518_){
_start:
{
lean_object* v___x_3519_; lean_object* v___x_3520_; 
v___x_3519_ = l_Lean_Json_getObjValD(v_j_3517_, v_k_3518_);
v___x_3520_ = l_Lean_Json_getNat_x3f(v___x_3519_);
return v___x_3520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentItem_fromJson_spec__0___boxed(lean_object* v_j_3521_, lean_object* v_k_3522_){
_start:
{
lean_object* v_res_3523_; 
v_res_3523_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentItem_fromJson_spec__0(v_j_3521_, v_k_3522_);
lean_dec_ref(v_k_3522_);
return v_res_3523_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__2(void){
_start:
{
uint8_t v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; 
v___x_3529_ = 1;
v___x_3530_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__1));
v___x_3531_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3530_, v___x_3529_);
return v___x_3531_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__3(void){
_start:
{
lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; 
v___x_3532_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__5));
v___x_3533_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__2, &l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__2);
v___x_3534_ = lean_string_append(v___x_3533_, v___x_3532_);
return v___x_3534_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__4(void){
_start:
{
lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; 
v___x_3535_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLocation_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLocation_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLocation_fromJson___closed__8);
v___x_3536_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__3, &l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__3);
v___x_3537_ = lean_string_append(v___x_3536_, v___x_3535_);
return v___x_3537_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__5(void){
_start:
{
lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; 
v___x_3538_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_3539_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__4, &l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__4);
v___x_3540_ = lean_string_append(v___x_3539_, v___x_3538_);
return v___x_3540_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__7(void){
_start:
{
uint8_t v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; 
v___x_3543_ = 1;
v___x_3544_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__6));
v___x_3545_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3544_, v___x_3543_);
return v___x_3545_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__8(void){
_start:
{
lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; 
v___x_3546_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__7, &l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__7);
v___x_3547_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__3, &l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__3);
v___x_3548_ = lean_string_append(v___x_3547_, v___x_3546_);
return v___x_3548_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__9(void){
_start:
{
lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; 
v___x_3549_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_3550_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__8, &l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__8);
v___x_3551_ = lean_string_append(v___x_3550_, v___x_3549_);
return v___x_3551_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__11(void){
_start:
{
uint8_t v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; 
v___x_3554_ = 1;
v___x_3555_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__10));
v___x_3556_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3555_, v___x_3554_);
return v___x_3556_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__12(void){
_start:
{
lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; 
v___x_3557_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__11, &l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__11);
v___x_3558_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__3, &l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__3);
v___x_3559_ = lean_string_append(v___x_3558_, v___x_3557_);
return v___x_3559_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__13(void){
_start:
{
lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; 
v___x_3560_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_3561_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__12, &l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__12);
v___x_3562_ = lean_string_append(v___x_3561_, v___x_3560_);
return v___x_3562_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__15(void){
_start:
{
uint8_t v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; 
v___x_3565_ = 1;
v___x_3566_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__14));
v___x_3567_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3566_, v___x_3565_);
return v___x_3567_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__16(void){
_start:
{
lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; 
v___x_3568_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__15, &l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__15_once, _init_l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__15);
v___x_3569_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__3, &l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__3);
v___x_3570_ = lean_string_append(v___x_3569_, v___x_3568_);
return v___x_3570_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__17(void){
_start:
{
lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; 
v___x_3571_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_3572_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__16, &l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__16_once, _init_l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__16);
v___x_3573_ = lean_string_append(v___x_3572_, v___x_3571_);
return v___x_3573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson(lean_object* v_json_3574_){
_start:
{
lean_object* v___x_3575_; lean_object* v___x_3576_; 
v___x_3575_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__0));
lean_inc(v_json_3574_);
v___x_3576_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocation_fromJson_spec__0(v_json_3574_, v___x_3575_);
if (lean_obj_tag(v___x_3576_) == 0)
{
lean_object* v_a_3577_; lean_object* v___x_3579_; uint8_t v_isShared_3580_; uint8_t v_isSharedCheck_3586_; 
lean_dec(v_json_3574_);
v_a_3577_ = lean_ctor_get(v___x_3576_, 0);
v_isSharedCheck_3586_ = !lean_is_exclusive(v___x_3576_);
if (v_isSharedCheck_3586_ == 0)
{
v___x_3579_ = v___x_3576_;
v_isShared_3580_ = v_isSharedCheck_3586_;
goto v_resetjp_3578_;
}
else
{
lean_inc(v_a_3577_);
lean_dec(v___x_3576_);
v___x_3579_ = lean_box(0);
v_isShared_3580_ = v_isSharedCheck_3586_;
goto v_resetjp_3578_;
}
v_resetjp_3578_:
{
lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3584_; 
v___x_3581_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__5, &l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__5);
v___x_3582_ = lean_string_append(v___x_3581_, v_a_3577_);
lean_dec(v_a_3577_);
if (v_isShared_3580_ == 0)
{
lean_ctor_set(v___x_3579_, 0, v___x_3582_);
v___x_3584_ = v___x_3579_;
goto v_reusejp_3583_;
}
else
{
lean_object* v_reuseFailAlloc_3585_; 
v_reuseFailAlloc_3585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3585_, 0, v___x_3582_);
v___x_3584_ = v_reuseFailAlloc_3585_;
goto v_reusejp_3583_;
}
v_reusejp_3583_:
{
return v___x_3584_;
}
}
}
else
{
if (lean_obj_tag(v___x_3576_) == 0)
{
lean_object* v_a_3587_; lean_object* v___x_3589_; uint8_t v_isShared_3590_; uint8_t v_isSharedCheck_3594_; 
lean_dec(v_json_3574_);
v_a_3587_ = lean_ctor_get(v___x_3576_, 0);
v_isSharedCheck_3594_ = !lean_is_exclusive(v___x_3576_);
if (v_isSharedCheck_3594_ == 0)
{
v___x_3589_ = v___x_3576_;
v_isShared_3590_ = v_isSharedCheck_3594_;
goto v_resetjp_3588_;
}
else
{
lean_inc(v_a_3587_);
lean_dec(v___x_3576_);
v___x_3589_ = lean_box(0);
v_isShared_3590_ = v_isSharedCheck_3594_;
goto v_resetjp_3588_;
}
v_resetjp_3588_:
{
lean_object* v___x_3592_; 
if (v_isShared_3590_ == 0)
{
lean_ctor_set_tag(v___x_3589_, 0);
v___x_3592_ = v___x_3589_;
goto v_reusejp_3591_;
}
else
{
lean_object* v_reuseFailAlloc_3593_; 
v_reuseFailAlloc_3593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3593_, 0, v_a_3587_);
v___x_3592_ = v_reuseFailAlloc_3593_;
goto v_reusejp_3591_;
}
v_reusejp_3591_:
{
return v___x_3592_;
}
}
}
else
{
lean_object* v_a_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; 
v_a_3595_ = lean_ctor_get(v___x_3576_, 0);
lean_inc(v_a_3595_);
lean_dec_ref_known(v___x_3576_, 1);
v___x_3596_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextDocumentItem_toJson___closed__0));
lean_inc(v_json_3574_);
v___x_3597_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocation_fromJson_spec__0(v_json_3574_, v___x_3596_);
if (lean_obj_tag(v___x_3597_) == 0)
{
lean_object* v_a_3598_; lean_object* v___x_3600_; uint8_t v_isShared_3601_; uint8_t v_isSharedCheck_3607_; 
lean_dec(v_a_3595_);
lean_dec(v_json_3574_);
v_a_3598_ = lean_ctor_get(v___x_3597_, 0);
v_isSharedCheck_3607_ = !lean_is_exclusive(v___x_3597_);
if (v_isSharedCheck_3607_ == 0)
{
v___x_3600_ = v___x_3597_;
v_isShared_3601_ = v_isSharedCheck_3607_;
goto v_resetjp_3599_;
}
else
{
lean_inc(v_a_3598_);
lean_dec(v___x_3597_);
v___x_3600_ = lean_box(0);
v_isShared_3601_ = v_isSharedCheck_3607_;
goto v_resetjp_3599_;
}
v_resetjp_3599_:
{
lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3605_; 
v___x_3602_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__9, &l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__9);
v___x_3603_ = lean_string_append(v___x_3602_, v_a_3598_);
lean_dec(v_a_3598_);
if (v_isShared_3601_ == 0)
{
lean_ctor_set(v___x_3600_, 0, v___x_3603_);
v___x_3605_ = v___x_3600_;
goto v_reusejp_3604_;
}
else
{
lean_object* v_reuseFailAlloc_3606_; 
v_reuseFailAlloc_3606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3606_, 0, v___x_3603_);
v___x_3605_ = v_reuseFailAlloc_3606_;
goto v_reusejp_3604_;
}
v_reusejp_3604_:
{
return v___x_3605_;
}
}
}
else
{
if (lean_obj_tag(v___x_3597_) == 0)
{
lean_object* v_a_3608_; lean_object* v___x_3610_; uint8_t v_isShared_3611_; uint8_t v_isSharedCheck_3615_; 
lean_dec(v_a_3595_);
lean_dec(v_json_3574_);
v_a_3608_ = lean_ctor_get(v___x_3597_, 0);
v_isSharedCheck_3615_ = !lean_is_exclusive(v___x_3597_);
if (v_isSharedCheck_3615_ == 0)
{
v___x_3610_ = v___x_3597_;
v_isShared_3611_ = v_isSharedCheck_3615_;
goto v_resetjp_3609_;
}
else
{
lean_inc(v_a_3608_);
lean_dec(v___x_3597_);
v___x_3610_ = lean_box(0);
v_isShared_3611_ = v_isSharedCheck_3615_;
goto v_resetjp_3609_;
}
v_resetjp_3609_:
{
lean_object* v___x_3613_; 
if (v_isShared_3611_ == 0)
{
lean_ctor_set_tag(v___x_3610_, 0);
v___x_3613_ = v___x_3610_;
goto v_reusejp_3612_;
}
else
{
lean_object* v_reuseFailAlloc_3614_; 
v_reuseFailAlloc_3614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3614_, 0, v_a_3608_);
v___x_3613_ = v_reuseFailAlloc_3614_;
goto v_reusejp_3612_;
}
v_reusejp_3612_:
{
return v___x_3613_;
}
}
}
else
{
lean_object* v_a_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; 
v_a_3616_ = lean_ctor_get(v___x_3597_, 0);
lean_inc(v_a_3616_);
lean_dec_ref_known(v___x_3597_, 1);
v___x_3617_ = ((lean_object*)(l_Lean_Lsp_instToJsonVersionedTextDocumentIdentifier_toJson___closed__0));
lean_inc(v_json_3574_);
v___x_3618_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentItem_fromJson_spec__0(v_json_3574_, v___x_3617_);
if (lean_obj_tag(v___x_3618_) == 0)
{
lean_object* v_a_3619_; lean_object* v___x_3621_; uint8_t v_isShared_3622_; uint8_t v_isSharedCheck_3628_; 
lean_dec(v_a_3616_);
lean_dec(v_a_3595_);
lean_dec(v_json_3574_);
v_a_3619_ = lean_ctor_get(v___x_3618_, 0);
v_isSharedCheck_3628_ = !lean_is_exclusive(v___x_3618_);
if (v_isSharedCheck_3628_ == 0)
{
v___x_3621_ = v___x_3618_;
v_isShared_3622_ = v_isSharedCheck_3628_;
goto v_resetjp_3620_;
}
else
{
lean_inc(v_a_3619_);
lean_dec(v___x_3618_);
v___x_3621_ = lean_box(0);
v_isShared_3622_ = v_isSharedCheck_3628_;
goto v_resetjp_3620_;
}
v_resetjp_3620_:
{
lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v___x_3626_; 
v___x_3623_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__13, &l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__13);
v___x_3624_ = lean_string_append(v___x_3623_, v_a_3619_);
lean_dec(v_a_3619_);
if (v_isShared_3622_ == 0)
{
lean_ctor_set(v___x_3621_, 0, v___x_3624_);
v___x_3626_ = v___x_3621_;
goto v_reusejp_3625_;
}
else
{
lean_object* v_reuseFailAlloc_3627_; 
v_reuseFailAlloc_3627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3627_, 0, v___x_3624_);
v___x_3626_ = v_reuseFailAlloc_3627_;
goto v_reusejp_3625_;
}
v_reusejp_3625_:
{
return v___x_3626_;
}
}
}
else
{
if (lean_obj_tag(v___x_3618_) == 0)
{
lean_object* v_a_3629_; lean_object* v___x_3631_; uint8_t v_isShared_3632_; uint8_t v_isSharedCheck_3636_; 
lean_dec(v_a_3616_);
lean_dec(v_a_3595_);
lean_dec(v_json_3574_);
v_a_3629_ = lean_ctor_get(v___x_3618_, 0);
v_isSharedCheck_3636_ = !lean_is_exclusive(v___x_3618_);
if (v_isSharedCheck_3636_ == 0)
{
v___x_3631_ = v___x_3618_;
v_isShared_3632_ = v_isSharedCheck_3636_;
goto v_resetjp_3630_;
}
else
{
lean_inc(v_a_3629_);
lean_dec(v___x_3618_);
v___x_3631_ = lean_box(0);
v_isShared_3632_ = v_isSharedCheck_3636_;
goto v_resetjp_3630_;
}
v_resetjp_3630_:
{
lean_object* v___x_3634_; 
if (v_isShared_3632_ == 0)
{
lean_ctor_set_tag(v___x_3631_, 0);
v___x_3634_ = v___x_3631_;
goto v_reusejp_3633_;
}
else
{
lean_object* v_reuseFailAlloc_3635_; 
v_reuseFailAlloc_3635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3635_, 0, v_a_3629_);
v___x_3634_ = v_reuseFailAlloc_3635_;
goto v_reusejp_3633_;
}
v_reusejp_3633_:
{
return v___x_3634_;
}
}
}
else
{
lean_object* v_a_3637_; lean_object* v___x_3638_; lean_object* v___x_3639_; 
v_a_3637_ = lean_ctor_get(v___x_3618_, 0);
lean_inc(v_a_3637_);
lean_dec_ref_known(v___x_3618_, 1);
v___x_3638_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextDocumentItem_toJson___closed__1));
v___x_3639_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocation_fromJson_spec__0(v_json_3574_, v___x_3638_);
if (lean_obj_tag(v___x_3639_) == 0)
{
lean_object* v_a_3640_; lean_object* v___x_3642_; uint8_t v_isShared_3643_; uint8_t v_isSharedCheck_3649_; 
lean_dec(v_a_3637_);
lean_dec(v_a_3616_);
lean_dec(v_a_3595_);
v_a_3640_ = lean_ctor_get(v___x_3639_, 0);
v_isSharedCheck_3649_ = !lean_is_exclusive(v___x_3639_);
if (v_isSharedCheck_3649_ == 0)
{
v___x_3642_ = v___x_3639_;
v_isShared_3643_ = v_isSharedCheck_3649_;
goto v_resetjp_3641_;
}
else
{
lean_inc(v_a_3640_);
lean_dec(v___x_3639_);
v___x_3642_ = lean_box(0);
v_isShared_3643_ = v_isSharedCheck_3649_;
goto v_resetjp_3641_;
}
v_resetjp_3641_:
{
lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3647_; 
v___x_3644_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__17, &l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__17_once, _init_l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson___closed__17);
v___x_3645_ = lean_string_append(v___x_3644_, v_a_3640_);
lean_dec(v_a_3640_);
if (v_isShared_3643_ == 0)
{
lean_ctor_set(v___x_3642_, 0, v___x_3645_);
v___x_3647_ = v___x_3642_;
goto v_reusejp_3646_;
}
else
{
lean_object* v_reuseFailAlloc_3648_; 
v_reuseFailAlloc_3648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3648_, 0, v___x_3645_);
v___x_3647_ = v_reuseFailAlloc_3648_;
goto v_reusejp_3646_;
}
v_reusejp_3646_:
{
return v___x_3647_;
}
}
}
else
{
if (lean_obj_tag(v___x_3639_) == 0)
{
lean_object* v_a_3650_; lean_object* v___x_3652_; uint8_t v_isShared_3653_; uint8_t v_isSharedCheck_3657_; 
lean_dec(v_a_3637_);
lean_dec(v_a_3616_);
lean_dec(v_a_3595_);
v_a_3650_ = lean_ctor_get(v___x_3639_, 0);
v_isSharedCheck_3657_ = !lean_is_exclusive(v___x_3639_);
if (v_isSharedCheck_3657_ == 0)
{
v___x_3652_ = v___x_3639_;
v_isShared_3653_ = v_isSharedCheck_3657_;
goto v_resetjp_3651_;
}
else
{
lean_inc(v_a_3650_);
lean_dec(v___x_3639_);
v___x_3652_ = lean_box(0);
v_isShared_3653_ = v_isSharedCheck_3657_;
goto v_resetjp_3651_;
}
v_resetjp_3651_:
{
lean_object* v___x_3655_; 
if (v_isShared_3653_ == 0)
{
lean_ctor_set_tag(v___x_3652_, 0);
v___x_3655_ = v___x_3652_;
goto v_reusejp_3654_;
}
else
{
lean_object* v_reuseFailAlloc_3656_; 
v_reuseFailAlloc_3656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3656_, 0, v_a_3650_);
v___x_3655_ = v_reuseFailAlloc_3656_;
goto v_reusejp_3654_;
}
v_reusejp_3654_:
{
return v___x_3655_;
}
}
}
else
{
lean_object* v_a_3658_; lean_object* v___x_3660_; uint8_t v_isShared_3661_; uint8_t v_isSharedCheck_3666_; 
v_a_3658_ = lean_ctor_get(v___x_3639_, 0);
v_isSharedCheck_3666_ = !lean_is_exclusive(v___x_3639_);
if (v_isSharedCheck_3666_ == 0)
{
v___x_3660_ = v___x_3639_;
v_isShared_3661_ = v_isSharedCheck_3666_;
goto v_resetjp_3659_;
}
else
{
lean_inc(v_a_3658_);
lean_dec(v___x_3639_);
v___x_3660_ = lean_box(0);
v_isShared_3661_ = v_isSharedCheck_3666_;
goto v_resetjp_3659_;
}
v_resetjp_3659_:
{
lean_object* v___x_3662_; lean_object* v___x_3664_; 
v___x_3662_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3662_, 0, v_a_3595_);
lean_ctor_set(v___x_3662_, 1, v_a_3616_);
lean_ctor_set(v___x_3662_, 2, v_a_3637_);
lean_ctor_set(v___x_3662_, 3, v_a_3658_);
if (v_isShared_3661_ == 0)
{
lean_ctor_set(v___x_3660_, 0, v___x_3662_);
v___x_3664_ = v___x_3660_;
goto v_reusejp_3663_;
}
else
{
lean_object* v_reuseFailAlloc_3665_; 
v_reuseFailAlloc_3665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3665_, 0, v___x_3662_);
v___x_3664_ = v_reuseFailAlloc_3665_;
goto v_reusejp_3663_;
}
v_reusejp_3663_:
{
return v___x_3664_;
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
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonTextDocumentPositionParams_toJson(lean_object* v_x_3670_){
_start:
{
lean_object* v_textDocument_3671_; lean_object* v_position_3672_; lean_object* v___x_3674_; uint8_t v_isShared_3675_; uint8_t v_isSharedCheck_3692_; 
v_textDocument_3671_ = lean_ctor_get(v_x_3670_, 0);
v_position_3672_ = lean_ctor_get(v_x_3670_, 1);
v_isSharedCheck_3692_ = !lean_is_exclusive(v_x_3670_);
if (v_isSharedCheck_3692_ == 0)
{
v___x_3674_ = v_x_3670_;
v_isShared_3675_ = v_isSharedCheck_3692_;
goto v_resetjp_3673_;
}
else
{
lean_inc(v_position_3672_);
lean_inc(v_textDocument_3671_);
lean_dec(v_x_3670_);
v___x_3674_ = lean_box(0);
v_isShared_3675_ = v_isSharedCheck_3692_;
goto v_resetjp_3673_;
}
v_resetjp_3673_:
{
lean_object* v___x_3676_; lean_object* v___x_3677_; lean_object* v___x_3679_; 
v___x_3676_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextDocumentEdit_toJson___closed__0));
v___x_3677_ = l_Lean_Lsp_instToJsonTextDocumentIdentifier_toJson(v_textDocument_3671_);
if (v_isShared_3675_ == 0)
{
lean_ctor_set(v___x_3674_, 1, v___x_3677_);
lean_ctor_set(v___x_3674_, 0, v___x_3676_);
v___x_3679_ = v___x_3674_;
goto v_reusejp_3678_;
}
else
{
lean_object* v_reuseFailAlloc_3691_; 
v_reuseFailAlloc_3691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3691_, 0, v___x_3676_);
lean_ctor_set(v_reuseFailAlloc_3691_, 1, v___x_3677_);
v___x_3679_ = v_reuseFailAlloc_3691_;
goto v_reusejp_3678_;
}
v_reusejp_3678_:
{
lean_object* v___x_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; 
v___x_3680_ = lean_box(0);
v___x_3681_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3681_, 0, v___x_3679_);
lean_ctor_set(v___x_3681_, 1, v___x_3680_);
v___x_3682_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextDocumentPositionParams_toJson___closed__0));
v___x_3683_ = l_Lean_Lsp_instToJsonPosition_toJson(v_position_3672_);
v___x_3684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3684_, 0, v___x_3682_);
lean_ctor_set(v___x_3684_, 1, v___x_3683_);
v___x_3685_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3685_, 0, v___x_3684_);
lean_ctor_set(v___x_3685_, 1, v___x_3680_);
v___x_3686_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3686_, 0, v___x_3685_);
lean_ctor_set(v___x_3686_, 1, v___x_3680_);
v___x_3687_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3687_, 0, v___x_3681_);
lean_ctor_set(v___x_3687_, 1, v___x_3686_);
v___x_3688_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__2));
v___x_3689_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLocation_toJson_spec__0(v___x_3687_, v___x_3688_);
v___x_3690_ = l_Lean_Json_mkObj(v___x_3689_);
lean_dec(v___x_3689_);
return v___x_3690_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson_spec__0(lean_object* v_j_3695_, lean_object* v_k_3696_){
_start:
{
lean_object* v___x_3697_; lean_object* v___x_3698_; 
v___x_3697_ = l_Lean_Json_getObjValD(v_j_3695_, v_k_3696_);
v___x_3698_ = l_Lean_Lsp_instFromJsonTextDocumentIdentifier_fromJson(v___x_3697_);
return v___x_3698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson_spec__0___boxed(lean_object* v_j_3699_, lean_object* v_k_3700_){
_start:
{
lean_object* v_res_3701_; 
v_res_3701_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson_spec__0(v_j_3699_, v_k_3700_);
lean_dec_ref(v_k_3700_);
return v_res_3701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson_spec__1(lean_object* v_j_3702_, lean_object* v_k_3703_){
_start:
{
lean_object* v___x_3704_; lean_object* v___x_3705_; 
v___x_3704_ = l_Lean_Json_getObjValD(v_j_3702_, v_k_3703_);
v___x_3705_ = l_Lean_Lsp_instFromJsonPosition_fromJson(v___x_3704_);
return v___x_3705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson_spec__1___boxed(lean_object* v_j_3706_, lean_object* v_k_3707_){
_start:
{
lean_object* v_res_3708_; 
v_res_3708_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson_spec__1(v_j_3706_, v_k_3707_);
lean_dec_ref(v_k_3707_);
return v_res_3708_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__2(void){
_start:
{
uint8_t v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; 
v___x_3714_ = 1;
v___x_3715_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__1));
v___x_3716_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3715_, v___x_3714_);
return v___x_3716_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__3(void){
_start:
{
lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; 
v___x_3717_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__5));
v___x_3718_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__2, &l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__2);
v___x_3719_ = lean_string_append(v___x_3718_, v___x_3717_);
return v___x_3719_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; 
v___x_3720_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__5, &l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonTextDocumentEdit_fromJson___closed__5);
v___x_3721_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__3);
v___x_3722_ = lean_string_append(v___x_3721_, v___x_3720_);
return v___x_3722_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__5(void){
_start:
{
lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; 
v___x_3723_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_3724_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__4);
v___x_3725_ = lean_string_append(v___x_3724_, v___x_3723_);
return v___x_3725_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__7(void){
_start:
{
uint8_t v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; 
v___x_3728_ = 1;
v___x_3729_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__6));
v___x_3730_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3729_, v___x_3728_);
return v___x_3730_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__8(void){
_start:
{
lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; 
v___x_3731_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__7);
v___x_3732_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__3);
v___x_3733_ = lean_string_append(v___x_3732_, v___x_3731_);
return v___x_3733_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__9(void){
_start:
{
lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; 
v___x_3734_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_3735_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__8);
v___x_3736_ = lean_string_append(v___x_3735_, v___x_3734_);
return v___x_3736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson(lean_object* v_json_3737_){
_start:
{
lean_object* v___x_3738_; lean_object* v___x_3739_; 
v___x_3738_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextDocumentEdit_toJson___closed__0));
lean_inc(v_json_3737_);
v___x_3739_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson_spec__0(v_json_3737_, v___x_3738_);
if (lean_obj_tag(v___x_3739_) == 0)
{
lean_object* v_a_3740_; lean_object* v___x_3742_; uint8_t v_isShared_3743_; uint8_t v_isSharedCheck_3749_; 
lean_dec(v_json_3737_);
v_a_3740_ = lean_ctor_get(v___x_3739_, 0);
v_isSharedCheck_3749_ = !lean_is_exclusive(v___x_3739_);
if (v_isSharedCheck_3749_ == 0)
{
v___x_3742_ = v___x_3739_;
v_isShared_3743_ = v_isSharedCheck_3749_;
goto v_resetjp_3741_;
}
else
{
lean_inc(v_a_3740_);
lean_dec(v___x_3739_);
v___x_3742_ = lean_box(0);
v_isShared_3743_ = v_isSharedCheck_3749_;
goto v_resetjp_3741_;
}
v_resetjp_3741_:
{
lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3747_; 
v___x_3744_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__5, &l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__5);
v___x_3745_ = lean_string_append(v___x_3744_, v_a_3740_);
lean_dec(v_a_3740_);
if (v_isShared_3743_ == 0)
{
lean_ctor_set(v___x_3742_, 0, v___x_3745_);
v___x_3747_ = v___x_3742_;
goto v_reusejp_3746_;
}
else
{
lean_object* v_reuseFailAlloc_3748_; 
v_reuseFailAlloc_3748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3748_, 0, v___x_3745_);
v___x_3747_ = v_reuseFailAlloc_3748_;
goto v_reusejp_3746_;
}
v_reusejp_3746_:
{
return v___x_3747_;
}
}
}
else
{
if (lean_obj_tag(v___x_3739_) == 0)
{
lean_object* v_a_3750_; lean_object* v___x_3752_; uint8_t v_isShared_3753_; uint8_t v_isSharedCheck_3757_; 
lean_dec(v_json_3737_);
v_a_3750_ = lean_ctor_get(v___x_3739_, 0);
v_isSharedCheck_3757_ = !lean_is_exclusive(v___x_3739_);
if (v_isSharedCheck_3757_ == 0)
{
v___x_3752_ = v___x_3739_;
v_isShared_3753_ = v_isSharedCheck_3757_;
goto v_resetjp_3751_;
}
else
{
lean_inc(v_a_3750_);
lean_dec(v___x_3739_);
v___x_3752_ = lean_box(0);
v_isShared_3753_ = v_isSharedCheck_3757_;
goto v_resetjp_3751_;
}
v_resetjp_3751_:
{
lean_object* v___x_3755_; 
if (v_isShared_3753_ == 0)
{
lean_ctor_set_tag(v___x_3752_, 0);
v___x_3755_ = v___x_3752_;
goto v_reusejp_3754_;
}
else
{
lean_object* v_reuseFailAlloc_3756_; 
v_reuseFailAlloc_3756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3756_, 0, v_a_3750_);
v___x_3755_ = v_reuseFailAlloc_3756_;
goto v_reusejp_3754_;
}
v_reusejp_3754_:
{
return v___x_3755_;
}
}
}
else
{
lean_object* v_a_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; 
v_a_3758_ = lean_ctor_get(v___x_3739_, 0);
lean_inc(v_a_3758_);
lean_dec_ref_known(v___x_3739_, 1);
v___x_3759_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextDocumentPositionParams_toJson___closed__0));
v___x_3760_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson_spec__1(v_json_3737_, v___x_3759_);
if (lean_obj_tag(v___x_3760_) == 0)
{
lean_object* v_a_3761_; lean_object* v___x_3763_; uint8_t v_isShared_3764_; uint8_t v_isSharedCheck_3770_; 
lean_dec(v_a_3758_);
v_a_3761_ = lean_ctor_get(v___x_3760_, 0);
v_isSharedCheck_3770_ = !lean_is_exclusive(v___x_3760_);
if (v_isSharedCheck_3770_ == 0)
{
v___x_3763_ = v___x_3760_;
v_isShared_3764_ = v_isSharedCheck_3770_;
goto v_resetjp_3762_;
}
else
{
lean_inc(v_a_3761_);
lean_dec(v___x_3760_);
v___x_3763_ = lean_box(0);
v_isShared_3764_ = v_isSharedCheck_3770_;
goto v_resetjp_3762_;
}
v_resetjp_3762_:
{
lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3768_; 
v___x_3765_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__9, &l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonTextDocumentPositionParams_fromJson___closed__9);
v___x_3766_ = lean_string_append(v___x_3765_, v_a_3761_);
lean_dec(v_a_3761_);
if (v_isShared_3764_ == 0)
{
lean_ctor_set(v___x_3763_, 0, v___x_3766_);
v___x_3768_ = v___x_3763_;
goto v_reusejp_3767_;
}
else
{
lean_object* v_reuseFailAlloc_3769_; 
v_reuseFailAlloc_3769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3769_, 0, v___x_3766_);
v___x_3768_ = v_reuseFailAlloc_3769_;
goto v_reusejp_3767_;
}
v_reusejp_3767_:
{
return v___x_3768_;
}
}
}
else
{
if (lean_obj_tag(v___x_3760_) == 0)
{
lean_object* v_a_3771_; lean_object* v___x_3773_; uint8_t v_isShared_3774_; uint8_t v_isSharedCheck_3778_; 
lean_dec(v_a_3758_);
v_a_3771_ = lean_ctor_get(v___x_3760_, 0);
v_isSharedCheck_3778_ = !lean_is_exclusive(v___x_3760_);
if (v_isSharedCheck_3778_ == 0)
{
v___x_3773_ = v___x_3760_;
v_isShared_3774_ = v_isSharedCheck_3778_;
goto v_resetjp_3772_;
}
else
{
lean_inc(v_a_3771_);
lean_dec(v___x_3760_);
v___x_3773_ = lean_box(0);
v_isShared_3774_ = v_isSharedCheck_3778_;
goto v_resetjp_3772_;
}
v_resetjp_3772_:
{
lean_object* v___x_3776_; 
if (v_isShared_3774_ == 0)
{
lean_ctor_set_tag(v___x_3773_, 0);
v___x_3776_ = v___x_3773_;
goto v_reusejp_3775_;
}
else
{
lean_object* v_reuseFailAlloc_3777_; 
v_reuseFailAlloc_3777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3777_, 0, v_a_3771_);
v___x_3776_ = v_reuseFailAlloc_3777_;
goto v_reusejp_3775_;
}
v_reusejp_3775_:
{
return v___x_3776_;
}
}
}
else
{
lean_object* v_a_3779_; lean_object* v___x_3781_; uint8_t v_isShared_3782_; uint8_t v_isSharedCheck_3787_; 
v_a_3779_ = lean_ctor_get(v___x_3760_, 0);
v_isSharedCheck_3787_ = !lean_is_exclusive(v___x_3760_);
if (v_isSharedCheck_3787_ == 0)
{
v___x_3781_ = v___x_3760_;
v_isShared_3782_ = v_isSharedCheck_3787_;
goto v_resetjp_3780_;
}
else
{
lean_inc(v_a_3779_);
lean_dec(v___x_3760_);
v___x_3781_ = lean_box(0);
v_isShared_3782_ = v_isSharedCheck_3787_;
goto v_resetjp_3780_;
}
v_resetjp_3780_:
{
lean_object* v___x_3783_; lean_object* v___x_3785_; 
v___x_3783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3783_, 0, v_a_3758_);
lean_ctor_set(v___x_3783_, 1, v_a_3779_);
if (v_isShared_3782_ == 0)
{
lean_ctor_set(v___x_3781_, 0, v___x_3783_);
v___x_3785_ = v___x_3781_;
goto v_reusejp_3784_;
}
else
{
lean_object* v_reuseFailAlloc_3786_; 
v_reuseFailAlloc_3786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3786_, 0, v___x_3783_);
v___x_3785_ = v_reuseFailAlloc_3786_;
goto v_reusejp_3784_;
}
v_reusejp_3784_:
{
return v___x_3785_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToStringTextDocumentPositionParams___lam__0(lean_object* v_p_3791_){
_start:
{
lean_object* v_position_3792_; lean_object* v_textDocument_3793_; lean_object* v_line_3794_; lean_object* v_character_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; 
v_position_3792_ = lean_ctor_get(v_p_3791_, 1);
lean_inc_ref(v_position_3792_);
v_textDocument_3793_ = lean_ctor_get(v_p_3791_, 0);
lean_inc_ref(v_textDocument_3793_);
lean_dec_ref(v_p_3791_);
v_line_3794_ = lean_ctor_get(v_position_3792_, 0);
lean_inc(v_line_3794_);
v_character_3795_ = lean_ctor_get(v_position_3792_, 1);
lean_inc(v_character_3795_);
lean_dec_ref(v_position_3792_);
v___x_3796_ = ((lean_object*)(l_Lean_Lsp_instToStringTextDocumentPositionParams___lam__0___closed__0));
v___x_3797_ = lean_string_append(v_textDocument_3793_, v___x_3796_);
v___x_3798_ = l_Nat_reprFast(v_line_3794_);
v___x_3799_ = lean_string_append(v___x_3797_, v___x_3798_);
lean_dec_ref(v___x_3798_);
v___x_3800_ = lean_string_append(v___x_3799_, v___x_3796_);
v___x_3801_ = l_Nat_reprFast(v_character_3795_);
v___x_3802_ = lean_string_append(v___x_3800_, v___x_3801_);
lean_dec_ref(v___x_3801_);
return v___x_3802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDocumentFilter_toJson(lean_object* v_x_3808_){
_start:
{
lean_object* v_language_x3f_3809_; lean_object* v_scheme_x3f_3810_; lean_object* v_pattern_x3f_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; lean_object* v___x_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; 
v_language_x3f_3809_ = lean_ctor_get(v_x_3808_, 0);
lean_inc(v_language_x3f_3809_);
v_scheme_x3f_3810_ = lean_ctor_get(v_x_3808_, 1);
lean_inc(v_scheme_x3f_3810_);
v_pattern_x3f_3811_ = lean_ctor_get(v_x_3808_, 2);
lean_inc(v_pattern_x3f_3811_);
lean_dec_ref(v_x_3808_);
v___x_3812_ = ((lean_object*)(l_Lean_Lsp_instToJsonDocumentFilter_toJson___closed__0));
v___x_3813_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextEdit_toJson_spec__1(v___x_3812_, v_language_x3f_3809_);
v___x_3814_ = ((lean_object*)(l_Lean_Lsp_instToJsonDocumentFilter_toJson___closed__1));
v___x_3815_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextEdit_toJson_spec__1(v___x_3814_, v_scheme_x3f_3810_);
v___x_3816_ = ((lean_object*)(l_Lean_Lsp_instToJsonDocumentFilter_toJson___closed__2));
v___x_3817_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextEdit_toJson_spec__1(v___x_3816_, v_pattern_x3f_3811_);
v___x_3818_ = lean_box(0);
v___x_3819_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3819_, 0, v___x_3817_);
lean_ctor_set(v___x_3819_, 1, v___x_3818_);
v___x_3820_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3820_, 0, v___x_3815_);
lean_ctor_set(v___x_3820_, 1, v___x_3819_);
v___x_3821_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3821_, 0, v___x_3813_);
lean_ctor_set(v___x_3821_, 1, v___x_3820_);
v___x_3822_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__2));
v___x_3823_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLocation_toJson_spec__0(v___x_3821_, v___x_3822_);
v___x_3824_ = l_Lean_Json_mkObj(v___x_3823_);
lean_dec(v___x_3823_);
return v___x_3824_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__2(void){
_start:
{
uint8_t v___x_3832_; lean_object* v___x_3833_; lean_object* v___x_3834_; 
v___x_3832_ = 1;
v___x_3833_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__1));
v___x_3834_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3833_, v___x_3832_);
return v___x_3834_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__3(void){
_start:
{
lean_object* v___x_3835_; lean_object* v___x_3836_; lean_object* v___x_3837_; 
v___x_3835_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__5));
v___x_3836_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__2, &l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__2);
v___x_3837_ = lean_string_append(v___x_3836_, v___x_3835_);
return v___x_3837_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__6(void){
_start:
{
uint8_t v___x_3841_; lean_object* v___x_3842_; lean_object* v___x_3843_; 
v___x_3841_ = 1;
v___x_3842_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__5));
v___x_3843_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3842_, v___x_3841_);
return v___x_3843_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__7(void){
_start:
{
lean_object* v___x_3844_; lean_object* v___x_3845_; lean_object* v___x_3846_; 
v___x_3844_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__6, &l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__6);
v___x_3845_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__3, &l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__3);
v___x_3846_ = lean_string_append(v___x_3845_, v___x_3844_);
return v___x_3846_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__8(void){
_start:
{
lean_object* v___x_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; 
v___x_3847_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_3848_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__7, &l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__7);
v___x_3849_ = lean_string_append(v___x_3848_, v___x_3847_);
return v___x_3849_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__11(void){
_start:
{
uint8_t v___x_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; 
v___x_3853_ = 1;
v___x_3854_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__10));
v___x_3855_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3854_, v___x_3853_);
return v___x_3855_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__12(void){
_start:
{
lean_object* v___x_3856_; lean_object* v___x_3857_; lean_object* v___x_3858_; 
v___x_3856_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__11, &l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__11);
v___x_3857_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__3, &l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__3);
v___x_3858_ = lean_string_append(v___x_3857_, v___x_3856_);
return v___x_3858_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__13(void){
_start:
{
lean_object* v___x_3859_; lean_object* v___x_3860_; lean_object* v___x_3861_; 
v___x_3859_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_3860_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__12, &l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__12);
v___x_3861_ = lean_string_append(v___x_3860_, v___x_3859_);
return v___x_3861_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__16(void){
_start:
{
uint8_t v___x_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; 
v___x_3865_ = 1;
v___x_3866_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__15));
v___x_3867_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3866_, v___x_3865_);
return v___x_3867_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__17(void){
_start:
{
lean_object* v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; 
v___x_3868_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__16, &l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__16_once, _init_l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__16);
v___x_3869_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__3, &l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__3);
v___x_3870_ = lean_string_append(v___x_3869_, v___x_3868_);
return v___x_3870_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__18(void){
_start:
{
lean_object* v___x_3871_; lean_object* v___x_3872_; lean_object* v___x_3873_; 
v___x_3871_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_3872_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__17, &l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__17_once, _init_l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__17);
v___x_3873_ = lean_string_append(v___x_3872_, v___x_3871_);
return v___x_3873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDocumentFilter_fromJson(lean_object* v_json_3874_){
_start:
{
lean_object* v___x_3875_; lean_object* v___x_3876_; 
v___x_3875_ = ((lean_object*)(l_Lean_Lsp_instToJsonDocumentFilter_toJson___closed__0));
lean_inc(v_json_3874_);
v___x_3876_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextEdit_fromJson_spec__1(v_json_3874_, v___x_3875_);
if (lean_obj_tag(v___x_3876_) == 0)
{
lean_object* v_a_3877_; lean_object* v___x_3879_; uint8_t v_isShared_3880_; uint8_t v_isSharedCheck_3886_; 
lean_dec(v_json_3874_);
v_a_3877_ = lean_ctor_get(v___x_3876_, 0);
v_isSharedCheck_3886_ = !lean_is_exclusive(v___x_3876_);
if (v_isSharedCheck_3886_ == 0)
{
v___x_3879_ = v___x_3876_;
v_isShared_3880_ = v_isSharedCheck_3886_;
goto v_resetjp_3878_;
}
else
{
lean_inc(v_a_3877_);
lean_dec(v___x_3876_);
v___x_3879_ = lean_box(0);
v_isShared_3880_ = v_isSharedCheck_3886_;
goto v_resetjp_3878_;
}
v_resetjp_3878_:
{
lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3884_; 
v___x_3881_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__8, &l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__8);
v___x_3882_ = lean_string_append(v___x_3881_, v_a_3877_);
lean_dec(v_a_3877_);
if (v_isShared_3880_ == 0)
{
lean_ctor_set(v___x_3879_, 0, v___x_3882_);
v___x_3884_ = v___x_3879_;
goto v_reusejp_3883_;
}
else
{
lean_object* v_reuseFailAlloc_3885_; 
v_reuseFailAlloc_3885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3885_, 0, v___x_3882_);
v___x_3884_ = v_reuseFailAlloc_3885_;
goto v_reusejp_3883_;
}
v_reusejp_3883_:
{
return v___x_3884_;
}
}
}
else
{
if (lean_obj_tag(v___x_3876_) == 0)
{
lean_object* v_a_3887_; lean_object* v___x_3889_; uint8_t v_isShared_3890_; uint8_t v_isSharedCheck_3894_; 
lean_dec(v_json_3874_);
v_a_3887_ = lean_ctor_get(v___x_3876_, 0);
v_isSharedCheck_3894_ = !lean_is_exclusive(v___x_3876_);
if (v_isSharedCheck_3894_ == 0)
{
v___x_3889_ = v___x_3876_;
v_isShared_3890_ = v_isSharedCheck_3894_;
goto v_resetjp_3888_;
}
else
{
lean_inc(v_a_3887_);
lean_dec(v___x_3876_);
v___x_3889_ = lean_box(0);
v_isShared_3890_ = v_isSharedCheck_3894_;
goto v_resetjp_3888_;
}
v_resetjp_3888_:
{
lean_object* v___x_3892_; 
if (v_isShared_3890_ == 0)
{
lean_ctor_set_tag(v___x_3889_, 0);
v___x_3892_ = v___x_3889_;
goto v_reusejp_3891_;
}
else
{
lean_object* v_reuseFailAlloc_3893_; 
v_reuseFailAlloc_3893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3893_, 0, v_a_3887_);
v___x_3892_ = v_reuseFailAlloc_3893_;
goto v_reusejp_3891_;
}
v_reusejp_3891_:
{
return v___x_3892_;
}
}
}
else
{
lean_object* v_a_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; 
v_a_3895_ = lean_ctor_get(v___x_3876_, 0);
lean_inc(v_a_3895_);
lean_dec_ref_known(v___x_3876_, 1);
v___x_3896_ = ((lean_object*)(l_Lean_Lsp_instToJsonDocumentFilter_toJson___closed__1));
lean_inc(v_json_3874_);
v___x_3897_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextEdit_fromJson_spec__1(v_json_3874_, v___x_3896_);
if (lean_obj_tag(v___x_3897_) == 0)
{
lean_object* v_a_3898_; lean_object* v___x_3900_; uint8_t v_isShared_3901_; uint8_t v_isSharedCheck_3907_; 
lean_dec(v_a_3895_);
lean_dec(v_json_3874_);
v_a_3898_ = lean_ctor_get(v___x_3897_, 0);
v_isSharedCheck_3907_ = !lean_is_exclusive(v___x_3897_);
if (v_isSharedCheck_3907_ == 0)
{
v___x_3900_ = v___x_3897_;
v_isShared_3901_ = v_isSharedCheck_3907_;
goto v_resetjp_3899_;
}
else
{
lean_inc(v_a_3898_);
lean_dec(v___x_3897_);
v___x_3900_ = lean_box(0);
v_isShared_3901_ = v_isSharedCheck_3907_;
goto v_resetjp_3899_;
}
v_resetjp_3899_:
{
lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3905_; 
v___x_3902_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__13, &l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__13);
v___x_3903_ = lean_string_append(v___x_3902_, v_a_3898_);
lean_dec(v_a_3898_);
if (v_isShared_3901_ == 0)
{
lean_ctor_set(v___x_3900_, 0, v___x_3903_);
v___x_3905_ = v___x_3900_;
goto v_reusejp_3904_;
}
else
{
lean_object* v_reuseFailAlloc_3906_; 
v_reuseFailAlloc_3906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3906_, 0, v___x_3903_);
v___x_3905_ = v_reuseFailAlloc_3906_;
goto v_reusejp_3904_;
}
v_reusejp_3904_:
{
return v___x_3905_;
}
}
}
else
{
if (lean_obj_tag(v___x_3897_) == 0)
{
lean_object* v_a_3908_; lean_object* v___x_3910_; uint8_t v_isShared_3911_; uint8_t v_isSharedCheck_3915_; 
lean_dec(v_a_3895_);
lean_dec(v_json_3874_);
v_a_3908_ = lean_ctor_get(v___x_3897_, 0);
v_isSharedCheck_3915_ = !lean_is_exclusive(v___x_3897_);
if (v_isSharedCheck_3915_ == 0)
{
v___x_3910_ = v___x_3897_;
v_isShared_3911_ = v_isSharedCheck_3915_;
goto v_resetjp_3909_;
}
else
{
lean_inc(v_a_3908_);
lean_dec(v___x_3897_);
v___x_3910_ = lean_box(0);
v_isShared_3911_ = v_isSharedCheck_3915_;
goto v_resetjp_3909_;
}
v_resetjp_3909_:
{
lean_object* v___x_3913_; 
if (v_isShared_3911_ == 0)
{
lean_ctor_set_tag(v___x_3910_, 0);
v___x_3913_ = v___x_3910_;
goto v_reusejp_3912_;
}
else
{
lean_object* v_reuseFailAlloc_3914_; 
v_reuseFailAlloc_3914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3914_, 0, v_a_3908_);
v___x_3913_ = v_reuseFailAlloc_3914_;
goto v_reusejp_3912_;
}
v_reusejp_3912_:
{
return v___x_3913_;
}
}
}
else
{
lean_object* v_a_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; 
v_a_3916_ = lean_ctor_get(v___x_3897_, 0);
lean_inc(v_a_3916_);
lean_dec_ref_known(v___x_3897_, 1);
v___x_3917_ = ((lean_object*)(l_Lean_Lsp_instToJsonDocumentFilter_toJson___closed__2));
v___x_3918_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextEdit_fromJson_spec__1(v_json_3874_, v___x_3917_);
if (lean_obj_tag(v___x_3918_) == 0)
{
lean_object* v_a_3919_; lean_object* v___x_3921_; uint8_t v_isShared_3922_; uint8_t v_isSharedCheck_3928_; 
lean_dec(v_a_3916_);
lean_dec(v_a_3895_);
v_a_3919_ = lean_ctor_get(v___x_3918_, 0);
v_isSharedCheck_3928_ = !lean_is_exclusive(v___x_3918_);
if (v_isSharedCheck_3928_ == 0)
{
v___x_3921_ = v___x_3918_;
v_isShared_3922_ = v_isSharedCheck_3928_;
goto v_resetjp_3920_;
}
else
{
lean_inc(v_a_3919_);
lean_dec(v___x_3918_);
v___x_3921_ = lean_box(0);
v_isShared_3922_ = v_isSharedCheck_3928_;
goto v_resetjp_3920_;
}
v_resetjp_3920_:
{
lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3926_; 
v___x_3923_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__18, &l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__18_once, _init_l_Lean_Lsp_instFromJsonDocumentFilter_fromJson___closed__18);
v___x_3924_ = lean_string_append(v___x_3923_, v_a_3919_);
lean_dec(v_a_3919_);
if (v_isShared_3922_ == 0)
{
lean_ctor_set(v___x_3921_, 0, v___x_3924_);
v___x_3926_ = v___x_3921_;
goto v_reusejp_3925_;
}
else
{
lean_object* v_reuseFailAlloc_3927_; 
v_reuseFailAlloc_3927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3927_, 0, v___x_3924_);
v___x_3926_ = v_reuseFailAlloc_3927_;
goto v_reusejp_3925_;
}
v_reusejp_3925_:
{
return v___x_3926_;
}
}
}
else
{
if (lean_obj_tag(v___x_3918_) == 0)
{
lean_object* v_a_3929_; lean_object* v___x_3931_; uint8_t v_isShared_3932_; uint8_t v_isSharedCheck_3936_; 
lean_dec(v_a_3916_);
lean_dec(v_a_3895_);
v_a_3929_ = lean_ctor_get(v___x_3918_, 0);
v_isSharedCheck_3936_ = !lean_is_exclusive(v___x_3918_);
if (v_isSharedCheck_3936_ == 0)
{
v___x_3931_ = v___x_3918_;
v_isShared_3932_ = v_isSharedCheck_3936_;
goto v_resetjp_3930_;
}
else
{
lean_inc(v_a_3929_);
lean_dec(v___x_3918_);
v___x_3931_ = lean_box(0);
v_isShared_3932_ = v_isSharedCheck_3936_;
goto v_resetjp_3930_;
}
v_resetjp_3930_:
{
lean_object* v___x_3934_; 
if (v_isShared_3932_ == 0)
{
lean_ctor_set_tag(v___x_3931_, 0);
v___x_3934_ = v___x_3931_;
goto v_reusejp_3933_;
}
else
{
lean_object* v_reuseFailAlloc_3935_; 
v_reuseFailAlloc_3935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3935_, 0, v_a_3929_);
v___x_3934_ = v_reuseFailAlloc_3935_;
goto v_reusejp_3933_;
}
v_reusejp_3933_:
{
return v___x_3934_;
}
}
}
else
{
lean_object* v_a_3937_; lean_object* v___x_3939_; uint8_t v_isShared_3940_; uint8_t v_isSharedCheck_3945_; 
v_a_3937_ = lean_ctor_get(v___x_3918_, 0);
v_isSharedCheck_3945_ = !lean_is_exclusive(v___x_3918_);
if (v_isSharedCheck_3945_ == 0)
{
v___x_3939_ = v___x_3918_;
v_isShared_3940_ = v_isSharedCheck_3945_;
goto v_resetjp_3938_;
}
else
{
lean_inc(v_a_3937_);
lean_dec(v___x_3918_);
v___x_3939_ = lean_box(0);
v_isShared_3940_ = v_isSharedCheck_3945_;
goto v_resetjp_3938_;
}
v_resetjp_3938_:
{
lean_object* v___x_3941_; lean_object* v___x_3943_; 
v___x_3941_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3941_, 0, v_a_3895_);
lean_ctor_set(v___x_3941_, 1, v_a_3916_);
lean_ctor_set(v___x_3941_, 2, v_a_3937_);
if (v_isShared_3940_ == 0)
{
lean_ctor_set(v___x_3939_, 0, v___x_3941_);
v___x_3943_ = v___x_3939_;
goto v_reusejp_3942_;
}
else
{
lean_object* v_reuseFailAlloc_3944_; 
v_reuseFailAlloc_3944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3944_, 0, v___x_3941_);
v___x_3943_ = v_reuseFailAlloc_3944_;
goto v_reusejp_3942_;
}
v_reusejp_3942_:
{
return v___x_3943_;
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
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonStaticRegistrationOptions_toJson(lean_object* v_x_3955_){
_start:
{
lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; 
v___x_3956_ = ((lean_object*)(l_Lean_Lsp_instToJsonStaticRegistrationOptions_toJson___closed__0));
v___x_3957_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextEdit_toJson_spec__1(v___x_3956_, v_x_3955_);
v___x_3958_ = lean_box(0);
v___x_3959_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3959_, 0, v___x_3957_);
lean_ctor_set(v___x_3959_, 1, v___x_3958_);
v___x_3960_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__2));
v___x_3961_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLocation_toJson_spec__0(v___x_3959_, v___x_3960_);
v___x_3962_ = l_Lean_Json_mkObj(v___x_3961_);
lean_dec(v___x_3961_);
return v___x_3962_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonStaticRegistrationOptions_fromJson___closed__2(void){
_start:
{
uint8_t v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; 
v___x_3970_ = 1;
v___x_3971_ = ((lean_object*)(l_Lean_Lsp_instFromJsonStaticRegistrationOptions_fromJson___closed__1));
v___x_3972_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3971_, v___x_3970_);
return v___x_3972_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonStaticRegistrationOptions_fromJson___closed__3(void){
_start:
{
lean_object* v___x_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; 
v___x_3973_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__5));
v___x_3974_ = lean_obj_once(&l_Lean_Lsp_instFromJsonStaticRegistrationOptions_fromJson___closed__2, &l_Lean_Lsp_instFromJsonStaticRegistrationOptions_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonStaticRegistrationOptions_fromJson___closed__2);
v___x_3975_ = lean_string_append(v___x_3974_, v___x_3973_);
return v___x_3975_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonStaticRegistrationOptions_fromJson___closed__6(void){
_start:
{
uint8_t v___x_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; 
v___x_3979_ = 1;
v___x_3980_ = ((lean_object*)(l_Lean_Lsp_instFromJsonStaticRegistrationOptions_fromJson___closed__5));
v___x_3981_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3980_, v___x_3979_);
return v___x_3981_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonStaticRegistrationOptions_fromJson___closed__7(void){
_start:
{
lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; 
v___x_3982_ = lean_obj_once(&l_Lean_Lsp_instFromJsonStaticRegistrationOptions_fromJson___closed__6, &l_Lean_Lsp_instFromJsonStaticRegistrationOptions_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonStaticRegistrationOptions_fromJson___closed__6);
v___x_3983_ = lean_obj_once(&l_Lean_Lsp_instFromJsonStaticRegistrationOptions_fromJson___closed__3, &l_Lean_Lsp_instFromJsonStaticRegistrationOptions_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonStaticRegistrationOptions_fromJson___closed__3);
v___x_3984_ = lean_string_append(v___x_3983_, v___x_3982_);
return v___x_3984_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonStaticRegistrationOptions_fromJson___closed__8(void){
_start:
{
lean_object* v___x_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; 
v___x_3985_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_3986_ = lean_obj_once(&l_Lean_Lsp_instFromJsonStaticRegistrationOptions_fromJson___closed__7, &l_Lean_Lsp_instFromJsonStaticRegistrationOptions_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonStaticRegistrationOptions_fromJson___closed__7);
v___x_3987_ = lean_string_append(v___x_3986_, v___x_3985_);
return v___x_3987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonStaticRegistrationOptions_fromJson(lean_object* v_json_3988_){
_start:
{
lean_object* v___x_3989_; lean_object* v___x_3990_; 
v___x_3989_ = ((lean_object*)(l_Lean_Lsp_instToJsonStaticRegistrationOptions_toJson___closed__0));
v___x_3990_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextEdit_fromJson_spec__1(v_json_3988_, v___x_3989_);
if (lean_obj_tag(v___x_3990_) == 0)
{
lean_object* v_a_3991_; lean_object* v___x_3993_; uint8_t v_isShared_3994_; uint8_t v_isSharedCheck_4000_; 
v_a_3991_ = lean_ctor_get(v___x_3990_, 0);
v_isSharedCheck_4000_ = !lean_is_exclusive(v___x_3990_);
if (v_isSharedCheck_4000_ == 0)
{
v___x_3993_ = v___x_3990_;
v_isShared_3994_ = v_isSharedCheck_4000_;
goto v_resetjp_3992_;
}
else
{
lean_inc(v_a_3991_);
lean_dec(v___x_3990_);
v___x_3993_ = lean_box(0);
v_isShared_3994_ = v_isSharedCheck_4000_;
goto v_resetjp_3992_;
}
v_resetjp_3992_:
{
lean_object* v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3998_; 
v___x_3995_ = lean_obj_once(&l_Lean_Lsp_instFromJsonStaticRegistrationOptions_fromJson___closed__8, &l_Lean_Lsp_instFromJsonStaticRegistrationOptions_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonStaticRegistrationOptions_fromJson___closed__8);
v___x_3996_ = lean_string_append(v___x_3995_, v_a_3991_);
lean_dec(v_a_3991_);
if (v_isShared_3994_ == 0)
{
lean_ctor_set(v___x_3993_, 0, v___x_3996_);
v___x_3998_ = v___x_3993_;
goto v_reusejp_3997_;
}
else
{
lean_object* v_reuseFailAlloc_3999_; 
v_reuseFailAlloc_3999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3999_, 0, v___x_3996_);
v___x_3998_ = v_reuseFailAlloc_3999_;
goto v_reusejp_3997_;
}
v_reusejp_3997_:
{
return v___x_3998_;
}
}
}
else
{
if (lean_obj_tag(v___x_3990_) == 0)
{
lean_object* v_a_4001_; lean_object* v___x_4003_; uint8_t v_isShared_4004_; uint8_t v_isSharedCheck_4008_; 
v_a_4001_ = lean_ctor_get(v___x_3990_, 0);
v_isSharedCheck_4008_ = !lean_is_exclusive(v___x_3990_);
if (v_isSharedCheck_4008_ == 0)
{
v___x_4003_ = v___x_3990_;
v_isShared_4004_ = v_isSharedCheck_4008_;
goto v_resetjp_4002_;
}
else
{
lean_inc(v_a_4001_);
lean_dec(v___x_3990_);
v___x_4003_ = lean_box(0);
v_isShared_4004_ = v_isSharedCheck_4008_;
goto v_resetjp_4002_;
}
v_resetjp_4002_:
{
lean_object* v___x_4006_; 
if (v_isShared_4004_ == 0)
{
lean_ctor_set_tag(v___x_4003_, 0);
v___x_4006_ = v___x_4003_;
goto v_reusejp_4005_;
}
else
{
lean_object* v_reuseFailAlloc_4007_; 
v_reuseFailAlloc_4007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4007_, 0, v_a_4001_);
v___x_4006_ = v_reuseFailAlloc_4007_;
goto v_reusejp_4005_;
}
v_reusejp_4005_:
{
return v___x_4006_;
}
}
}
else
{
lean_object* v_a_4009_; lean_object* v___x_4011_; uint8_t v_isShared_4012_; uint8_t v_isSharedCheck_4016_; 
v_a_4009_ = lean_ctor_get(v___x_3990_, 0);
v_isSharedCheck_4016_ = !lean_is_exclusive(v___x_3990_);
if (v_isSharedCheck_4016_ == 0)
{
v___x_4011_ = v___x_3990_;
v_isShared_4012_ = v_isSharedCheck_4016_;
goto v_resetjp_4010_;
}
else
{
lean_inc(v_a_4009_);
lean_dec(v___x_3990_);
v___x_4011_ = lean_box(0);
v_isShared_4012_ = v_isSharedCheck_4016_;
goto v_resetjp_4010_;
}
v_resetjp_4010_:
{
lean_object* v___x_4014_; 
if (v_isShared_4012_ == 0)
{
v___x_4014_ = v___x_4011_;
goto v_reusejp_4013_;
}
else
{
lean_object* v_reuseFailAlloc_4015_; 
v_reuseFailAlloc_4015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4015_, 0, v_a_4009_);
v___x_4014_ = v_reuseFailAlloc_4015_;
goto v_reusejp_4013_;
}
v_reusejp_4013_:
{
return v___x_4014_;
}
}
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonTextDocumentRegistrationOptions_toJson_spec__0_spec__0_spec__1(size_t v_sz_4019_, size_t v_i_4020_, lean_object* v_bs_4021_){
_start:
{
uint8_t v___x_4022_; 
v___x_4022_ = lean_usize_dec_lt(v_i_4020_, v_sz_4019_);
if (v___x_4022_ == 0)
{
return v_bs_4021_;
}
else
{
lean_object* v_v_4023_; lean_object* v___x_4024_; lean_object* v_bs_x27_4025_; lean_object* v___x_4026_; size_t v___x_4027_; size_t v___x_4028_; lean_object* v___x_4029_; 
v_v_4023_ = lean_array_uget(v_bs_4021_, v_i_4020_);
v___x_4024_ = lean_unsigned_to_nat(0u);
v_bs_x27_4025_ = lean_array_uset(v_bs_4021_, v_i_4020_, v___x_4024_);
v___x_4026_ = l_Lean_Lsp_instToJsonDocumentFilter_toJson(v_v_4023_);
v___x_4027_ = ((size_t)1ULL);
v___x_4028_ = lean_usize_add(v_i_4020_, v___x_4027_);
v___x_4029_ = lean_array_uset(v_bs_x27_4025_, v_i_4020_, v___x_4026_);
v_i_4020_ = v___x_4028_;
v_bs_4021_ = v___x_4029_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonTextDocumentRegistrationOptions_toJson_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
size_t v_sz_4019_ = stack[0].m_num;
size_t v_i_4020_ = stack[1].m_num;
lean_object* v_bs_4021_ = stack[2].m_obj;
lean_object* v_res_4031_;
v_res_4031_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonTextDocumentRegistrationOptions_toJson_spec__0_spec__0_spec__1(v_sz_4019_, v_i_4020_, v_bs_4021_);
stack->m_obj
 = v_res_4031_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonTextDocumentRegistrationOptions_toJson_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_4032_, lean_object* v_i_4033_, lean_object* v_bs_4034_){
_start:
{
size_t v_sz_boxed_4035_; size_t v_i_boxed_4036_; lean_object* v_res_4037_; 
v_sz_boxed_4035_ = lean_unbox_usize(v_sz_4032_);
lean_dec(v_sz_4032_);
v_i_boxed_4036_ = lean_unbox_usize(v_i_4033_);
lean_dec(v_i_4033_);
v_res_4037_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonTextDocumentRegistrationOptions_toJson_spec__0_spec__0_spec__1(v_sz_boxed_4035_, v_i_boxed_4036_, v_bs_4034_);
return v_res_4037_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonTextDocumentRegistrationOptions_toJson_spec__0_spec__0(lean_object* v_a_4038_){
_start:
{
size_t v_sz_4039_; size_t v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; 
v_sz_4039_ = lean_array_size(v_a_4038_);
v___x_4040_ = ((size_t)0ULL);
v___x_4041_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonTextDocumentRegistrationOptions_toJson_spec__0_spec__0_spec__1(v_sz_4039_, v___x_4040_, v_a_4038_);
v___x_4042_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_4042_, 0, v___x_4041_);
return v___x_4042_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextDocumentRegistrationOptions_toJson_spec__0(lean_object* v_k_4043_, lean_object* v_x_4044_){
_start:
{
if (lean_obj_tag(v_x_4044_) == 0)
{
lean_object* v___x_4045_; 
lean_dec_ref(v_k_4043_);
v___x_4045_ = lean_box(0);
return v___x_4045_;
}
else
{
lean_object* v_val_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; 
v_val_4046_ = lean_ctor_get(v_x_4044_, 0);
lean_inc(v_val_4046_);
lean_dec_ref_known(v_x_4044_, 1);
v___x_4047_ = l_Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonTextDocumentRegistrationOptions_toJson_spec__0_spec__0(v_val_4046_);
v___x_4048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4048_, 0, v_k_4043_);
lean_ctor_set(v___x_4048_, 1, v___x_4047_);
v___x_4049_ = lean_box(0);
v___x_4050_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4050_, 0, v___x_4048_);
lean_ctor_set(v___x_4050_, 1, v___x_4049_);
return v___x_4050_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonTextDocumentRegistrationOptions_toJson(lean_object* v_x_4052_){
_start:
{
lean_object* v___x_4053_; lean_object* v___x_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; 
v___x_4053_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextDocumentRegistrationOptions_toJson___closed__0));
v___x_4054_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextDocumentRegistrationOptions_toJson_spec__0(v___x_4053_, v_x_4052_);
v___x_4055_ = lean_box(0);
v___x_4056_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4056_, 0, v___x_4054_);
lean_ctor_set(v___x_4056_, 1, v___x_4055_);
v___x_4057_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__2));
v___x_4058_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLocation_toJson_spec__0(v___x_4056_, v___x_4057_);
v___x_4059_ = l_Lean_Json_mkObj(v___x_4058_);
lean_dec(v___x_4058_);
return v___x_4059_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson_spec__0_spec__0_spec__1_spec__2(size_t v_sz_4062_, size_t v_i_4063_, lean_object* v_bs_4064_){
_start:
{
uint8_t v___x_4065_; 
v___x_4065_ = lean_usize_dec_lt(v_i_4063_, v_sz_4062_);
if (v___x_4065_ == 0)
{
lean_object* v___x_4066_; 
v___x_4066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4066_, 0, v_bs_4064_);
return v___x_4066_;
}
else
{
lean_object* v_v_4067_; lean_object* v___x_4068_; 
v_v_4067_ = lean_array_uget_borrowed(v_bs_4064_, v_i_4063_);
lean_inc(v_v_4067_);
v___x_4068_ = l_Lean_Lsp_instFromJsonDocumentFilter_fromJson(v_v_4067_);
if (lean_obj_tag(v___x_4068_) == 0)
{
lean_object* v_a_4069_; lean_object* v___x_4071_; uint8_t v_isShared_4072_; uint8_t v_isSharedCheck_4076_; 
lean_dec_ref(v_bs_4064_);
v_a_4069_ = lean_ctor_get(v___x_4068_, 0);
v_isSharedCheck_4076_ = !lean_is_exclusive(v___x_4068_);
if (v_isSharedCheck_4076_ == 0)
{
v___x_4071_ = v___x_4068_;
v_isShared_4072_ = v_isSharedCheck_4076_;
goto v_resetjp_4070_;
}
else
{
lean_inc(v_a_4069_);
lean_dec(v___x_4068_);
v___x_4071_ = lean_box(0);
v_isShared_4072_ = v_isSharedCheck_4076_;
goto v_resetjp_4070_;
}
v_resetjp_4070_:
{
lean_object* v___x_4074_; 
if (v_isShared_4072_ == 0)
{
v___x_4074_ = v___x_4071_;
goto v_reusejp_4073_;
}
else
{
lean_object* v_reuseFailAlloc_4075_; 
v_reuseFailAlloc_4075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4075_, 0, v_a_4069_);
v___x_4074_ = v_reuseFailAlloc_4075_;
goto v_reusejp_4073_;
}
v_reusejp_4073_:
{
return v___x_4074_;
}
}
}
else
{
lean_object* v_a_4077_; lean_object* v___x_4078_; lean_object* v_bs_x27_4079_; size_t v___x_4080_; size_t v___x_4081_; lean_object* v___x_4082_; 
v_a_4077_ = lean_ctor_get(v___x_4068_, 0);
lean_inc(v_a_4077_);
lean_dec_ref_known(v___x_4068_, 1);
v___x_4078_ = lean_unsigned_to_nat(0u);
v_bs_x27_4079_ = lean_array_uset(v_bs_4064_, v_i_4063_, v___x_4078_);
v___x_4080_ = ((size_t)1ULL);
v___x_4081_ = lean_usize_add(v_i_4063_, v___x_4080_);
v___x_4082_ = lean_array_uset(v_bs_x27_4079_, v_i_4063_, v_a_4077_);
v_i_4063_ = v___x_4081_;
v_bs_4064_ = v___x_4082_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson_spec__0_spec__0_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
size_t v_sz_4062_ = stack[0].m_num;
size_t v_i_4063_ = stack[1].m_num;
lean_object* v_bs_4064_ = stack[2].m_obj;
lean_object* v_res_4084_;
v_res_4084_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson_spec__0_spec__0_spec__1_spec__2(v_sz_4062_, v_i_4063_, v_bs_4064_);
stack->m_obj
 = v_res_4084_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_sz_4085_, lean_object* v_i_4086_, lean_object* v_bs_4087_){
_start:
{
size_t v_sz_boxed_4088_; size_t v_i_boxed_4089_; lean_object* v_res_4090_; 
v_sz_boxed_4088_ = lean_unbox_usize(v_sz_4085_);
lean_dec(v_sz_4085_);
v_i_boxed_4089_ = lean_unbox_usize(v_i_4086_);
lean_dec(v_i_4086_);
v_res_4090_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson_spec__0_spec__0_spec__1_spec__2(v_sz_boxed_4088_, v_i_boxed_4089_, v_bs_4087_);
return v_res_4090_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson_spec__0_spec__0_spec__1(lean_object* v_x_4091_){
_start:
{
if (lean_obj_tag(v_x_4091_) == 4)
{
lean_object* v_elems_4092_; size_t v_sz_4093_; size_t v___x_4094_; lean_object* v___x_4095_; 
v_elems_4092_ = lean_ctor_get(v_x_4091_, 0);
lean_inc_ref(v_elems_4092_);
lean_dec_ref_known(v_x_4091_, 1);
v_sz_4093_ = lean_array_size(v_elems_4092_);
v___x_4094_ = ((size_t)0ULL);
v___x_4095_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson_spec__0_spec__0_spec__1_spec__2(v_sz_4093_, v___x_4094_, v_elems_4092_);
return v___x_4095_;
}
else
{
lean_object* v___x_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; 
v___x_4096_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCommand_fromJson_spec__0_spec__0_spec__1___closed__0));
v___x_4097_ = lean_unsigned_to_nat(80u);
v___x_4098_ = l_Lean_Json_pretty(v_x_4091_, v___x_4097_);
v___x_4099_ = lean_string_append(v___x_4096_, v___x_4098_);
lean_dec_ref(v___x_4098_);
v___x_4100_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCommand_fromJson_spec__0_spec__0_spec__1___closed__1));
v___x_4101_ = lean_string_append(v___x_4099_, v___x_4100_);
v___x_4102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4102_, 0, v___x_4101_);
return v___x_4102_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson_spec__0_spec__0(lean_object* v_x_4105_){
_start:
{
if (lean_obj_tag(v_x_4105_) == 0)
{
lean_object* v___x_4106_; 
v___x_4106_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson_spec__0_spec__0___closed__0));
return v___x_4106_;
}
else
{
lean_object* v___x_4107_; 
v___x_4107_ = l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson_spec__0_spec__0_spec__1(v_x_4105_);
if (lean_obj_tag(v___x_4107_) == 0)
{
lean_object* v_a_4108_; lean_object* v___x_4110_; uint8_t v_isShared_4111_; uint8_t v_isSharedCheck_4115_; 
v_a_4108_ = lean_ctor_get(v___x_4107_, 0);
v_isSharedCheck_4115_ = !lean_is_exclusive(v___x_4107_);
if (v_isSharedCheck_4115_ == 0)
{
v___x_4110_ = v___x_4107_;
v_isShared_4111_ = v_isSharedCheck_4115_;
goto v_resetjp_4109_;
}
else
{
lean_inc(v_a_4108_);
lean_dec(v___x_4107_);
v___x_4110_ = lean_box(0);
v_isShared_4111_ = v_isSharedCheck_4115_;
goto v_resetjp_4109_;
}
v_resetjp_4109_:
{
lean_object* v___x_4113_; 
if (v_isShared_4111_ == 0)
{
v___x_4113_ = v___x_4110_;
goto v_reusejp_4112_;
}
else
{
lean_object* v_reuseFailAlloc_4114_; 
v_reuseFailAlloc_4114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4114_, 0, v_a_4108_);
v___x_4113_ = v_reuseFailAlloc_4114_;
goto v_reusejp_4112_;
}
v_reusejp_4112_:
{
return v___x_4113_;
}
}
}
else
{
lean_object* v_a_4116_; lean_object* v___x_4118_; uint8_t v_isShared_4119_; uint8_t v_isSharedCheck_4124_; 
v_a_4116_ = lean_ctor_get(v___x_4107_, 0);
v_isSharedCheck_4124_ = !lean_is_exclusive(v___x_4107_);
if (v_isSharedCheck_4124_ == 0)
{
v___x_4118_ = v___x_4107_;
v_isShared_4119_ = v_isSharedCheck_4124_;
goto v_resetjp_4117_;
}
else
{
lean_inc(v_a_4116_);
lean_dec(v___x_4107_);
v___x_4118_ = lean_box(0);
v_isShared_4119_ = v_isSharedCheck_4124_;
goto v_resetjp_4117_;
}
v_resetjp_4117_:
{
lean_object* v___x_4120_; lean_object* v___x_4122_; 
v___x_4120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4120_, 0, v_a_4116_);
if (v_isShared_4119_ == 0)
{
lean_ctor_set(v___x_4118_, 0, v___x_4120_);
v___x_4122_ = v___x_4118_;
goto v_reusejp_4121_;
}
else
{
lean_object* v_reuseFailAlloc_4123_; 
v_reuseFailAlloc_4123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4123_, 0, v___x_4120_);
v___x_4122_ = v_reuseFailAlloc_4123_;
goto v_reusejp_4121_;
}
v_reusejp_4121_:
{
return v___x_4122_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson_spec__0(lean_object* v_j_4125_, lean_object* v_k_4126_){
_start:
{
lean_object* v___x_4127_; lean_object* v___x_4128_; 
v___x_4127_ = l_Lean_Json_getObjValD(v_j_4125_, v_k_4126_);
v___x_4128_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson_spec__0_spec__0(v___x_4127_);
return v___x_4128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson_spec__0___boxed(lean_object* v_j_4129_, lean_object* v_k_4130_){
_start:
{
lean_object* v_res_4131_; 
v_res_4131_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson_spec__0(v_j_4129_, v_k_4130_);
lean_dec_ref(v_k_4130_);
return v_res_4131_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson___closed__2(void){
_start:
{
uint8_t v___x_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; 
v___x_4137_ = 1;
v___x_4138_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson___closed__1));
v___x_4139_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4138_, v___x_4137_);
return v___x_4139_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson___closed__3(void){
_start:
{
lean_object* v___x_4140_; lean_object* v___x_4141_; lean_object* v___x_4142_; 
v___x_4140_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__5));
v___x_4141_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson___closed__2, &l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson___closed__2);
v___x_4142_ = lean_string_append(v___x_4141_, v___x_4140_);
return v___x_4142_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson___closed__6(void){
_start:
{
uint8_t v___x_4146_; lean_object* v___x_4147_; lean_object* v___x_4148_; 
v___x_4146_ = 1;
v___x_4147_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson___closed__5));
v___x_4148_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4147_, v___x_4146_);
return v___x_4148_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson___closed__7(void){
_start:
{
lean_object* v___x_4149_; lean_object* v___x_4150_; lean_object* v___x_4151_; 
v___x_4149_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson___closed__6, &l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson___closed__6);
v___x_4150_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson___closed__3, &l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson___closed__3);
v___x_4151_ = lean_string_append(v___x_4150_, v___x_4149_);
return v___x_4151_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson___closed__8(void){
_start:
{
lean_object* v___x_4152_; lean_object* v___x_4153_; lean_object* v___x_4154_; 
v___x_4152_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_4153_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson___closed__7, &l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson___closed__7);
v___x_4154_ = lean_string_append(v___x_4153_, v___x_4152_);
return v___x_4154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson(lean_object* v_json_4155_){
_start:
{
lean_object* v___x_4156_; lean_object* v___x_4157_; 
v___x_4156_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextDocumentRegistrationOptions_toJson___closed__0));
v___x_4157_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson_spec__0(v_json_4155_, v___x_4156_);
if (lean_obj_tag(v___x_4157_) == 0)
{
lean_object* v_a_4158_; lean_object* v___x_4160_; uint8_t v_isShared_4161_; uint8_t v_isSharedCheck_4167_; 
v_a_4158_ = lean_ctor_get(v___x_4157_, 0);
v_isSharedCheck_4167_ = !lean_is_exclusive(v___x_4157_);
if (v_isSharedCheck_4167_ == 0)
{
v___x_4160_ = v___x_4157_;
v_isShared_4161_ = v_isSharedCheck_4167_;
goto v_resetjp_4159_;
}
else
{
lean_inc(v_a_4158_);
lean_dec(v___x_4157_);
v___x_4160_ = lean_box(0);
v_isShared_4161_ = v_isSharedCheck_4167_;
goto v_resetjp_4159_;
}
v_resetjp_4159_:
{
lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4165_; 
v___x_4162_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson___closed__8, &l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonTextDocumentRegistrationOptions_fromJson___closed__8);
v___x_4163_ = lean_string_append(v___x_4162_, v_a_4158_);
lean_dec(v_a_4158_);
if (v_isShared_4161_ == 0)
{
lean_ctor_set(v___x_4160_, 0, v___x_4163_);
v___x_4165_ = v___x_4160_;
goto v_reusejp_4164_;
}
else
{
lean_object* v_reuseFailAlloc_4166_; 
v_reuseFailAlloc_4166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4166_, 0, v___x_4163_);
v___x_4165_ = v_reuseFailAlloc_4166_;
goto v_reusejp_4164_;
}
v_reusejp_4164_:
{
return v___x_4165_;
}
}
}
else
{
if (lean_obj_tag(v___x_4157_) == 0)
{
lean_object* v_a_4168_; lean_object* v___x_4170_; uint8_t v_isShared_4171_; uint8_t v_isSharedCheck_4175_; 
v_a_4168_ = lean_ctor_get(v___x_4157_, 0);
v_isSharedCheck_4175_ = !lean_is_exclusive(v___x_4157_);
if (v_isSharedCheck_4175_ == 0)
{
v___x_4170_ = v___x_4157_;
v_isShared_4171_ = v_isSharedCheck_4175_;
goto v_resetjp_4169_;
}
else
{
lean_inc(v_a_4168_);
lean_dec(v___x_4157_);
v___x_4170_ = lean_box(0);
v_isShared_4171_ = v_isSharedCheck_4175_;
goto v_resetjp_4169_;
}
v_resetjp_4169_:
{
lean_object* v___x_4173_; 
if (v_isShared_4171_ == 0)
{
lean_ctor_set_tag(v___x_4170_, 0);
v___x_4173_ = v___x_4170_;
goto v_reusejp_4172_;
}
else
{
lean_object* v_reuseFailAlloc_4174_; 
v_reuseFailAlloc_4174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4174_, 0, v_a_4168_);
v___x_4173_ = v_reuseFailAlloc_4174_;
goto v_reusejp_4172_;
}
v_reusejp_4172_:
{
return v___x_4173_;
}
}
}
else
{
lean_object* v_a_4176_; lean_object* v___x_4178_; uint8_t v_isShared_4179_; uint8_t v_isSharedCheck_4183_; 
v_a_4176_ = lean_ctor_get(v___x_4157_, 0);
v_isSharedCheck_4183_ = !lean_is_exclusive(v___x_4157_);
if (v_isSharedCheck_4183_ == 0)
{
v___x_4178_ = v___x_4157_;
v_isShared_4179_ = v_isSharedCheck_4183_;
goto v_resetjp_4177_;
}
else
{
lean_inc(v_a_4176_);
lean_dec(v___x_4157_);
v___x_4178_ = lean_box(0);
v_isShared_4179_ = v_isSharedCheck_4183_;
goto v_resetjp_4177_;
}
v_resetjp_4177_:
{
lean_object* v___x_4181_; 
if (v_isShared_4179_ == 0)
{
v___x_4181_ = v___x_4178_;
goto v_reusejp_4180_;
}
else
{
lean_object* v_reuseFailAlloc_4182_; 
v_reuseFailAlloc_4182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4182_, 0, v_a_4176_);
v___x_4181_ = v_reuseFailAlloc_4182_;
goto v_reusejp_4180_;
}
v_reusejp_4180_:
{
return v___x_4181_;
}
}
}
}
}
}
lean_object* l_Lean_Lsp_MarkupKind_ctorIdx___impl(uint8_t v_x_4186_){
_start:
{
lean_object* v___x_4187_; lean_object* v___x_4188_; 
v___x_4187_ = lean_box(v_x_4186_);
v___x_4188_ = lean_obj_tag_nat(v___x_4187_);
lean_dec(v___x_4187_);
return v___x_4188_;
}
}
LEAN_EXPORT void l_Lean_Lsp_MarkupKind_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_4186_ = stack[0].m_num;
lean_object* v_res_4189_;
v_res_4189_ = l_Lean_Lsp_MarkupKind_ctorIdx___impl(v_x_4186_);
stack->m_obj
 = v_res_4189_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MarkupKind_ctorIdx___impl___boxed(lean_object* v_x_4190_){
_start:
{
uint8_t v_x_4__boxed_4191_; lean_object* v_res_4192_; 
v_x_4__boxed_4191_ = lean_unbox(v_x_4190_);
v_res_4192_ = l_Lean_Lsp_MarkupKind_ctorIdx___impl(v_x_4__boxed_4191_);
return v_res_4192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MarkupKind_ctorElim___redArg(lean_object* v_k_4193_){
_start:
{
lean_inc(v_k_4193_);
return v_k_4193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MarkupKind_ctorElim___redArg___boxed(lean_object* v_k_4194_){
_start:
{
lean_object* v_res_4195_; 
v_res_4195_ = l_Lean_Lsp_MarkupKind_ctorElim___redArg(v_k_4194_);
lean_dec(v_k_4194_);
return v_res_4195_;
}
}
lean_object* l_Lean_Lsp_MarkupKind_ctorElim(lean_object* v_motive_4196_, lean_object* v_ctorIdx_4197_, uint8_t v_t_4198_, lean_object* v_h_4199_, lean_object* v_k_4200_){
_start:
{
lean_inc(v_k_4200_);
return v_k_4200_;
}
}
LEAN_EXPORT void l_Lean_Lsp_MarkupKind_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_4197_ = stack[1].m_obj;
uint8_t v_t_4198_ = stack[2].m_num;
lean_object* v_k_4200_ = stack[4].m_obj;
lean_object* v_res_4201_;
v_res_4201_ = l_Lean_Lsp_MarkupKind_ctorElim(lean_box(0), v_ctorIdx_4197_, v_t_4198_, lean_box(0), v_k_4200_);
stack->m_obj
 = v_res_4201_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MarkupKind_ctorElim___boxed(lean_object* v_motive_4202_, lean_object* v_ctorIdx_4203_, lean_object* v_t_4204_, lean_object* v_h_4205_, lean_object* v_k_4206_){
_start:
{
uint8_t v_t_boxed_4207_; lean_object* v_res_4208_; 
v_t_boxed_4207_ = lean_unbox(v_t_4204_);
v_res_4208_ = l_Lean_Lsp_MarkupKind_ctorElim(v_motive_4202_, v_ctorIdx_4203_, v_t_boxed_4207_, v_h_4205_, v_k_4206_);
lean_dec(v_k_4206_);
lean_dec(v_ctorIdx_4203_);
return v_res_4208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MarkupKind_plaintext_elim___redArg(lean_object* v_plaintext_4209_){
_start:
{
lean_inc(v_plaintext_4209_);
return v_plaintext_4209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MarkupKind_plaintext_elim___redArg___boxed(lean_object* v_plaintext_4210_){
_start:
{
lean_object* v_res_4211_; 
v_res_4211_ = l_Lean_Lsp_MarkupKind_plaintext_elim___redArg(v_plaintext_4210_);
lean_dec(v_plaintext_4210_);
return v_res_4211_;
}
}
lean_object* l_Lean_Lsp_MarkupKind_plaintext_elim(lean_object* v_motive_4212_, uint8_t v_t_4213_, lean_object* v_h_4214_, lean_object* v_plaintext_4215_){
_start:
{
lean_inc(v_plaintext_4215_);
return v_plaintext_4215_;
}
}
LEAN_EXPORT void l_Lean_Lsp_MarkupKind_plaintext_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_4213_ = stack[1].m_num;
lean_object* v_plaintext_4215_ = stack[3].m_obj;
lean_object* v_res_4216_;
v_res_4216_ = l_Lean_Lsp_MarkupKind_plaintext_elim(lean_box(0), v_t_4213_, lean_box(0), v_plaintext_4215_);
stack->m_obj
 = v_res_4216_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MarkupKind_plaintext_elim___boxed(lean_object* v_motive_4217_, lean_object* v_t_4218_, lean_object* v_h_4219_, lean_object* v_plaintext_4220_){
_start:
{
uint8_t v_t_boxed_4221_; lean_object* v_res_4222_; 
v_t_boxed_4221_ = lean_unbox(v_t_4218_);
v_res_4222_ = l_Lean_Lsp_MarkupKind_plaintext_elim(v_motive_4217_, v_t_boxed_4221_, v_h_4219_, v_plaintext_4220_);
lean_dec(v_plaintext_4220_);
return v_res_4222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MarkupKind_markdown_elim___redArg(lean_object* v_markdown_4223_){
_start:
{
lean_inc(v_markdown_4223_);
return v_markdown_4223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MarkupKind_markdown_elim___redArg___boxed(lean_object* v_markdown_4224_){
_start:
{
lean_object* v_res_4225_; 
v_res_4225_ = l_Lean_Lsp_MarkupKind_markdown_elim___redArg(v_markdown_4224_);
lean_dec(v_markdown_4224_);
return v_res_4225_;
}
}
lean_object* l_Lean_Lsp_MarkupKind_markdown_elim(lean_object* v_motive_4226_, uint8_t v_t_4227_, lean_object* v_h_4228_, lean_object* v_markdown_4229_){
_start:
{
lean_inc(v_markdown_4229_);
return v_markdown_4229_;
}
}
LEAN_EXPORT void l_Lean_Lsp_MarkupKind_markdown_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_4227_ = stack[1].m_num;
lean_object* v_markdown_4229_ = stack[3].m_obj;
lean_object* v_res_4230_;
v_res_4230_ = l_Lean_Lsp_MarkupKind_markdown_elim(lean_box(0), v_t_4227_, lean_box(0), v_markdown_4229_);
stack->m_obj
 = v_res_4230_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MarkupKind_markdown_elim___boxed(lean_object* v_motive_4231_, lean_object* v_t_4232_, lean_object* v_h_4233_, lean_object* v_markdown_4234_){
_start:
{
uint8_t v_t_boxed_4235_; lean_object* v_res_4236_; 
v_t_boxed_4235_ = lean_unbox(v_t_4232_);
v_res_4236_ = l_Lean_Lsp_MarkupKind_markdown_elim(v_motive_4231_, v_t_boxed_4235_, v_h_4233_, v_markdown_4234_);
lean_dec(v_markdown_4234_);
return v_res_4236_;
}
}
uint8_t l_Lean_Lsp_MarkupKind_ofNat(lean_object* v_n_4237_){
_start:
{
lean_object* v___x_4238_; uint8_t v___x_4239_; 
v___x_4238_ = lean_unsigned_to_nat(0u);
v___x_4239_ = lean_nat_dec_le(v_n_4237_, v___x_4238_);
if (v___x_4239_ == 0)
{
uint8_t v___x_4240_; 
v___x_4240_ = 1;
return v___x_4240_;
}
else
{
uint8_t v___x_4241_; 
v___x_4241_ = 0;
return v___x_4241_;
}
}
}
LEAN_EXPORT void l_Lean_Lsp_MarkupKind_ofNat_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_4237_ = stack[0].m_obj;
uint8_t v_res_4242_;
v_res_4242_ = l_Lean_Lsp_MarkupKind_ofNat(v_n_4237_);
stack->m_num = v_res_4242_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_MarkupKind_ofNat___boxed(lean_object* v_n_4243_){
_start:
{
uint8_t v_res_4244_; lean_object* v_r_4245_; 
v_res_4244_ = l_Lean_Lsp_MarkupKind_ofNat(v_n_4243_);
lean_dec(v_n_4243_);
v_r_4245_ = lean_box(v_res_4244_);
return v_r_4245_;
}
}
uint8_t l_Lean_Lsp_instDecidableEqMarkupKind(uint8_t v_x_4246_, uint8_t v_y_4247_){
_start:
{
lean_object* v___x_4248_; lean_object* v___x_4249_; lean_object* v___x_4250_; lean_object* v___x_4251_; uint8_t v___x_4252_; 
v___x_4248_ = lean_box(v_x_4246_);
v___x_4249_ = lean_obj_tag_nat(v___x_4248_);
lean_dec(v___x_4248_);
v___x_4250_ = lean_box(v_y_4247_);
v___x_4251_ = lean_obj_tag_nat(v___x_4250_);
lean_dec(v___x_4250_);
v___x_4252_ = lean_nat_dec_eq(v___x_4249_, v___x_4251_);
return v___x_4252_;
}
}
LEAN_EXPORT void l_Lean_Lsp_instDecidableEqMarkupKind_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_4246_ = stack[0].m_num;
uint8_t v_y_4247_ = stack[1].m_num;
uint8_t v_res_4253_;
v_res_4253_ = l_Lean_Lsp_instDecidableEqMarkupKind(v_x_4246_, v_y_4247_);
stack->m_num = v_res_4253_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instDecidableEqMarkupKind___boxed(lean_object* v_x_4254_, lean_object* v_y_4255_){
_start:
{
uint8_t v_x_23__boxed_4256_; uint8_t v_y_24__boxed_4257_; uint8_t v_res_4258_; lean_object* v_r_4259_; 
v_x_23__boxed_4256_ = lean_unbox(v_x_4254_);
v_y_24__boxed_4257_ = lean_unbox(v_y_4255_);
v_res_4258_ = l_Lean_Lsp_instDecidableEqMarkupKind(v_x_23__boxed_4256_, v_y_24__boxed_4257_);
v_r_4259_ = lean_box(v_res_4258_);
return v_r_4259_;
}
}
uint64_t l_Lean_Lsp_instHashableMarkupKind_hash(uint8_t v_x_4260_){
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
LEAN_EXPORT void l_Lean_Lsp_instHashableMarkupKind_hash_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_4260_ = stack[0].m_num;
uint64_t v_res_4263_;
v_res_4263_ = l_Lean_Lsp_instHashableMarkupKind_hash(v_x_4260_);
stack->m_num = v_res_4263_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instHashableMarkupKind_hash___boxed(lean_object* v_x_4264_){
_start:
{
uint8_t v_x_28__boxed_4265_; uint64_t v_res_4266_; lean_object* v_r_4267_; 
v_x_28__boxed_4265_ = lean_unbox(v_x_4264_);
v_res_4266_ = l_Lean_Lsp_instHashableMarkupKind_hash(v_x_28__boxed_4265_);
v_r_4267_ = lean_box_uint64(v_res_4266_);
return v_r_4267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonMarkupKind___lam__0(lean_object* v_x_4281_){
_start:
{
if (lean_obj_tag(v_x_4281_) == 3)
{
lean_object* v_s_4284_; lean_object* v___x_4285_; uint8_t v___x_4286_; 
v_s_4284_ = lean_ctor_get(v_x_4281_, 0);
v___x_4285_ = ((lean_object*)(l_Lean_Lsp_instFromJsonMarkupKind___lam__0___closed__2));
v___x_4286_ = lean_string_dec_eq(v_s_4284_, v___x_4285_);
if (v___x_4286_ == 0)
{
lean_object* v___x_4287_; uint8_t v___x_4288_; 
v___x_4287_ = ((lean_object*)(l_Lean_Lsp_instFromJsonMarkupKind___lam__0___closed__3));
v___x_4288_ = lean_string_dec_eq(v_s_4284_, v___x_4287_);
if (v___x_4288_ == 0)
{
goto v___jp_4282_;
}
else
{
lean_object* v___x_4289_; 
v___x_4289_ = ((lean_object*)(l_Lean_Lsp_instFromJsonMarkupKind___lam__0___closed__4));
return v___x_4289_;
}
}
else
{
lean_object* v___x_4290_; 
v___x_4290_ = ((lean_object*)(l_Lean_Lsp_instFromJsonMarkupKind___lam__0___closed__5));
return v___x_4290_;
}
}
else
{
goto v___jp_4282_;
}
v___jp_4282_:
{
lean_object* v___x_4283_; 
v___x_4283_ = ((lean_object*)(l_Lean_Lsp_instFromJsonMarkupKind___lam__0___closed__1));
return v___x_4283_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonMarkupKind___lam__0___boxed(lean_object* v_x_4291_){
_start:
{
lean_object* v_res_4292_; 
v_res_4292_ = l_Lean_Lsp_instFromJsonMarkupKind___lam__0(v_x_4291_);
lean_dec(v_x_4291_);
return v_res_4292_;
}
}
lean_object* l_Lean_Lsp_instToJsonMarkupKind___lam__0(uint8_t v_x_4299_){
_start:
{
if (v_x_4299_ == 0)
{
lean_object* v___x_4300_; 
v___x_4300_ = ((lean_object*)(l_Lean_Lsp_instToJsonMarkupKind___lam__0___closed__0));
return v___x_4300_;
}
else
{
lean_object* v___x_4301_; 
v___x_4301_ = ((lean_object*)(l_Lean_Lsp_instToJsonMarkupKind___lam__0___closed__1));
return v___x_4301_;
}
}
}
LEAN_EXPORT void l_Lean_Lsp_instToJsonMarkupKind___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_4299_ = stack[0].m_num;
lean_object* v_res_4302_;
v_res_4302_ = l_Lean_Lsp_instToJsonMarkupKind___lam__0(v_x_4299_);
stack->m_obj
 = v_res_4302_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonMarkupKind___lam__0___boxed(lean_object* v_x_4303_){
_start:
{
uint8_t v_x_38__boxed_4304_; lean_object* v_res_4305_; 
v_x_38__boxed_4304_ = lean_unbox(v_x_4303_);
v_res_4305_ = l_Lean_Lsp_instToJsonMarkupKind___lam__0(v_x_38__boxed_4304_);
return v_res_4305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonMarkupContent_toJson(lean_object* v_x_4308_){
_start:
{
uint8_t v_kind_4309_; lean_object* v_value_4310_; lean_object* v___x_4311_; lean_object* v___y_4313_; 
v_kind_4309_ = lean_ctor_get_uint8(v_x_4308_, sizeof(void*)*1);
v_value_4310_ = lean_ctor_get(v_x_4308_, 0);
v___x_4311_ = ((lean_object*)(l_Lean_Lsp_instToJsonDocumentChange___lam__0___closed__0));
if (v_kind_4309_ == 0)
{
lean_object* v___x_4326_; 
v___x_4326_ = ((lean_object*)(l_Lean_Lsp_instToJsonMarkupKind___lam__0___closed__0));
v___y_4313_ = v___x_4326_;
goto v___jp_4312_;
}
else
{
lean_object* v___x_4327_; 
v___x_4327_ = ((lean_object*)(l_Lean_Lsp_instToJsonMarkupKind___lam__0___closed__1));
v___y_4313_ = v___x_4327_;
goto v___jp_4312_;
}
v___jp_4312_:
{
lean_object* v___x_4314_; lean_object* v___x_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; lean_object* v___x_4318_; lean_object* v___x_4319_; lean_object* v___x_4320_; lean_object* v___x_4321_; lean_object* v___x_4322_; lean_object* v___x_4323_; lean_object* v___x_4324_; lean_object* v___x_4325_; 
lean_inc(v___y_4313_);
v___x_4314_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4314_, 0, v___x_4311_);
lean_ctor_set(v___x_4314_, 1, v___y_4313_);
v___x_4315_ = lean_box(0);
v___x_4316_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4316_, 0, v___x_4314_);
lean_ctor_set(v___x_4316_, 1, v___x_4315_);
v___x_4317_ = ((lean_object*)(l_Lean_Lsp_instToJsonSnippetString_toJson___closed__0));
lean_inc_ref(v_value_4310_);
v___x_4318_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4318_, 0, v_value_4310_);
v___x_4319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4319_, 0, v___x_4317_);
lean_ctor_set(v___x_4319_, 1, v___x_4318_);
v___x_4320_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4320_, 0, v___x_4319_);
lean_ctor_set(v___x_4320_, 1, v___x_4315_);
v___x_4321_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4321_, 0, v___x_4320_);
lean_ctor_set(v___x_4321_, 1, v___x_4315_);
v___x_4322_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4322_, 0, v___x_4316_);
lean_ctor_set(v___x_4322_, 1, v___x_4321_);
v___x_4323_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__2));
v___x_4324_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLocation_toJson_spec__0(v___x_4322_, v___x_4323_);
v___x_4325_ = l_Lean_Json_mkObj(v___x_4324_);
lean_dec(v___x_4324_);
return v___x_4325_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonMarkupContent_toJson___boxed(lean_object* v_x_4328_){
_start:
{
lean_object* v_res_4329_; 
v_res_4329_ = l_Lean_Lsp_instToJsonMarkupContent_toJson(v_x_4328_);
lean_dec_ref(v_x_4328_);
return v_res_4329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonMarkupContent_fromJson_spec__0(lean_object* v_j_4332_, lean_object* v_k_4333_){
_start:
{
lean_object* v___x_4336_; 
v___x_4336_ = l_Lean_Json_getObjValD(v_j_4332_, v_k_4333_);
if (lean_obj_tag(v___x_4336_) == 3)
{
lean_object* v_s_4337_; lean_object* v___x_4338_; uint8_t v___x_4339_; 
v_s_4337_ = lean_ctor_get(v___x_4336_, 0);
lean_inc_ref(v_s_4337_);
lean_dec_ref_known(v___x_4336_, 1);
v___x_4338_ = ((lean_object*)(l_Lean_Lsp_instFromJsonMarkupKind___lam__0___closed__2));
v___x_4339_ = lean_string_dec_eq(v_s_4337_, v___x_4338_);
if (v___x_4339_ == 0)
{
lean_object* v___x_4340_; uint8_t v___x_4341_; 
v___x_4340_ = ((lean_object*)(l_Lean_Lsp_instFromJsonMarkupKind___lam__0___closed__3));
v___x_4341_ = lean_string_dec_eq(v_s_4337_, v___x_4340_);
lean_dec_ref(v_s_4337_);
if (v___x_4341_ == 0)
{
goto v___jp_4334_;
}
else
{
lean_object* v___x_4342_; 
v___x_4342_ = ((lean_object*)(l_Lean_Lsp_instFromJsonMarkupKind___lam__0___closed__4));
return v___x_4342_;
}
}
else
{
lean_object* v___x_4343_; 
lean_dec_ref(v_s_4337_);
v___x_4343_ = ((lean_object*)(l_Lean_Lsp_instFromJsonMarkupKind___lam__0___closed__5));
return v___x_4343_;
}
}
else
{
lean_dec(v___x_4336_);
goto v___jp_4334_;
}
v___jp_4334_:
{
lean_object* v___x_4335_; 
v___x_4335_ = ((lean_object*)(l_Lean_Lsp_instFromJsonMarkupKind___lam__0___closed__1));
return v___x_4335_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonMarkupContent_fromJson_spec__0___boxed(lean_object* v_j_4344_, lean_object* v_k_4345_){
_start:
{
lean_object* v_res_4346_; 
v_res_4346_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonMarkupContent_fromJson_spec__0(v_j_4344_, v_k_4345_);
lean_dec_ref(v_k_4345_);
return v_res_4346_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__2(void){
_start:
{
uint8_t v___x_4352_; lean_object* v___x_4353_; lean_object* v___x_4354_; 
v___x_4352_ = 1;
v___x_4353_ = ((lean_object*)(l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__1));
v___x_4354_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4353_, v___x_4352_);
return v___x_4354_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__3(void){
_start:
{
lean_object* v___x_4355_; lean_object* v___x_4356_; lean_object* v___x_4357_; 
v___x_4355_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__5));
v___x_4356_ = lean_obj_once(&l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__2, &l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__2);
v___x_4357_ = lean_string_append(v___x_4356_, v___x_4355_);
return v___x_4357_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__5(void){
_start:
{
uint8_t v___x_4360_; lean_object* v___x_4361_; lean_object* v___x_4362_; 
v___x_4360_ = 1;
v___x_4361_ = ((lean_object*)(l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__4));
v___x_4362_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4361_, v___x_4360_);
return v___x_4362_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__6(void){
_start:
{
lean_object* v___x_4363_; lean_object* v___x_4364_; lean_object* v___x_4365_; 
v___x_4363_ = lean_obj_once(&l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__5, &l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__5);
v___x_4364_ = lean_obj_once(&l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__3, &l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__3);
v___x_4365_ = lean_string_append(v___x_4364_, v___x_4363_);
return v___x_4365_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__7(void){
_start:
{
lean_object* v___x_4366_; lean_object* v___x_4367_; lean_object* v___x_4368_; 
v___x_4366_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_4367_ = lean_obj_once(&l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__6, &l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__6);
v___x_4368_ = lean_string_append(v___x_4367_, v___x_4366_);
return v___x_4368_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__8(void){
_start:
{
lean_object* v___x_4369_; lean_object* v___x_4370_; lean_object* v___x_4371_; 
v___x_4369_ = lean_obj_once(&l_Lean_Lsp_instFromJsonSnippetString_fromJson___closed__5, &l_Lean_Lsp_instFromJsonSnippetString_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonSnippetString_fromJson___closed__5);
v___x_4370_ = lean_obj_once(&l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__3, &l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__3);
v___x_4371_ = lean_string_append(v___x_4370_, v___x_4369_);
return v___x_4371_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__9(void){
_start:
{
lean_object* v___x_4372_; lean_object* v___x_4373_; lean_object* v___x_4374_; 
v___x_4372_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_4373_ = lean_obj_once(&l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__8, &l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__8);
v___x_4374_ = lean_string_append(v___x_4373_, v___x_4372_);
return v___x_4374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonMarkupContent_fromJson(lean_object* v_json_4375_){
_start:
{
lean_object* v___x_4376_; lean_object* v___x_4377_; 
v___x_4376_ = ((lean_object*)(l_Lean_Lsp_instToJsonDocumentChange___lam__0___closed__0));
lean_inc(v_json_4375_);
v___x_4377_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonMarkupContent_fromJson_spec__0(v_json_4375_, v___x_4376_);
if (lean_obj_tag(v___x_4377_) == 0)
{
lean_object* v_a_4378_; lean_object* v___x_4380_; uint8_t v_isShared_4381_; uint8_t v_isSharedCheck_4387_; 
lean_dec(v_json_4375_);
v_a_4378_ = lean_ctor_get(v___x_4377_, 0);
v_isSharedCheck_4387_ = !lean_is_exclusive(v___x_4377_);
if (v_isSharedCheck_4387_ == 0)
{
v___x_4380_ = v___x_4377_;
v_isShared_4381_ = v_isSharedCheck_4387_;
goto v_resetjp_4379_;
}
else
{
lean_inc(v_a_4378_);
lean_dec(v___x_4377_);
v___x_4380_ = lean_box(0);
v_isShared_4381_ = v_isSharedCheck_4387_;
goto v_resetjp_4379_;
}
v_resetjp_4379_:
{
lean_object* v___x_4382_; lean_object* v___x_4383_; lean_object* v___x_4385_; 
v___x_4382_ = lean_obj_once(&l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__7, &l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__7);
v___x_4383_ = lean_string_append(v___x_4382_, v_a_4378_);
lean_dec(v_a_4378_);
if (v_isShared_4381_ == 0)
{
lean_ctor_set(v___x_4380_, 0, v___x_4383_);
v___x_4385_ = v___x_4380_;
goto v_reusejp_4384_;
}
else
{
lean_object* v_reuseFailAlloc_4386_; 
v_reuseFailAlloc_4386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4386_, 0, v___x_4383_);
v___x_4385_ = v_reuseFailAlloc_4386_;
goto v_reusejp_4384_;
}
v_reusejp_4384_:
{
return v___x_4385_;
}
}
}
else
{
if (lean_obj_tag(v___x_4377_) == 0)
{
lean_object* v_a_4388_; lean_object* v___x_4390_; uint8_t v_isShared_4391_; uint8_t v_isSharedCheck_4395_; 
lean_dec(v_json_4375_);
v_a_4388_ = lean_ctor_get(v___x_4377_, 0);
v_isSharedCheck_4395_ = !lean_is_exclusive(v___x_4377_);
if (v_isSharedCheck_4395_ == 0)
{
v___x_4390_ = v___x_4377_;
v_isShared_4391_ = v_isSharedCheck_4395_;
goto v_resetjp_4389_;
}
else
{
lean_inc(v_a_4388_);
lean_dec(v___x_4377_);
v___x_4390_ = lean_box(0);
v_isShared_4391_ = v_isSharedCheck_4395_;
goto v_resetjp_4389_;
}
v_resetjp_4389_:
{
lean_object* v___x_4393_; 
if (v_isShared_4391_ == 0)
{
lean_ctor_set_tag(v___x_4390_, 0);
v___x_4393_ = v___x_4390_;
goto v_reusejp_4392_;
}
else
{
lean_object* v_reuseFailAlloc_4394_; 
v_reuseFailAlloc_4394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4394_, 0, v_a_4388_);
v___x_4393_ = v_reuseFailAlloc_4394_;
goto v_reusejp_4392_;
}
v_reusejp_4392_:
{
return v___x_4393_;
}
}
}
else
{
lean_object* v_a_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; 
v_a_4396_ = lean_ctor_get(v___x_4377_, 0);
lean_inc(v_a_4396_);
lean_dec_ref_known(v___x_4377_, 1);
v___x_4397_ = ((lean_object*)(l_Lean_Lsp_instToJsonSnippetString_toJson___closed__0));
v___x_4398_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLocation_fromJson_spec__0(v_json_4375_, v___x_4397_);
if (lean_obj_tag(v___x_4398_) == 0)
{
lean_object* v_a_4399_; lean_object* v___x_4401_; uint8_t v_isShared_4402_; uint8_t v_isSharedCheck_4408_; 
lean_dec(v_a_4396_);
v_a_4399_ = lean_ctor_get(v___x_4398_, 0);
v_isSharedCheck_4408_ = !lean_is_exclusive(v___x_4398_);
if (v_isSharedCheck_4408_ == 0)
{
v___x_4401_ = v___x_4398_;
v_isShared_4402_ = v_isSharedCheck_4408_;
goto v_resetjp_4400_;
}
else
{
lean_inc(v_a_4399_);
lean_dec(v___x_4398_);
v___x_4401_ = lean_box(0);
v_isShared_4402_ = v_isSharedCheck_4408_;
goto v_resetjp_4400_;
}
v_resetjp_4400_:
{
lean_object* v___x_4403_; lean_object* v___x_4404_; lean_object* v___x_4406_; 
v___x_4403_ = lean_obj_once(&l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__9, &l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonMarkupContent_fromJson___closed__9);
v___x_4404_ = lean_string_append(v___x_4403_, v_a_4399_);
lean_dec(v_a_4399_);
if (v_isShared_4402_ == 0)
{
lean_ctor_set(v___x_4401_, 0, v___x_4404_);
v___x_4406_ = v___x_4401_;
goto v_reusejp_4405_;
}
else
{
lean_object* v_reuseFailAlloc_4407_; 
v_reuseFailAlloc_4407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4407_, 0, v___x_4404_);
v___x_4406_ = v_reuseFailAlloc_4407_;
goto v_reusejp_4405_;
}
v_reusejp_4405_:
{
return v___x_4406_;
}
}
}
else
{
if (lean_obj_tag(v___x_4398_) == 0)
{
lean_object* v_a_4409_; lean_object* v___x_4411_; uint8_t v_isShared_4412_; uint8_t v_isSharedCheck_4416_; 
lean_dec(v_a_4396_);
v_a_4409_ = lean_ctor_get(v___x_4398_, 0);
v_isSharedCheck_4416_ = !lean_is_exclusive(v___x_4398_);
if (v_isSharedCheck_4416_ == 0)
{
v___x_4411_ = v___x_4398_;
v_isShared_4412_ = v_isSharedCheck_4416_;
goto v_resetjp_4410_;
}
else
{
lean_inc(v_a_4409_);
lean_dec(v___x_4398_);
v___x_4411_ = lean_box(0);
v_isShared_4412_ = v_isSharedCheck_4416_;
goto v_resetjp_4410_;
}
v_resetjp_4410_:
{
lean_object* v___x_4414_; 
if (v_isShared_4412_ == 0)
{
lean_ctor_set_tag(v___x_4411_, 0);
v___x_4414_ = v___x_4411_;
goto v_reusejp_4413_;
}
else
{
lean_object* v_reuseFailAlloc_4415_; 
v_reuseFailAlloc_4415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4415_, 0, v_a_4409_);
v___x_4414_ = v_reuseFailAlloc_4415_;
goto v_reusejp_4413_;
}
v_reusejp_4413_:
{
return v___x_4414_;
}
}
}
else
{
lean_object* v_a_4417_; lean_object* v___x_4419_; uint8_t v_isShared_4420_; uint8_t v_isSharedCheck_4426_; 
v_a_4417_ = lean_ctor_get(v___x_4398_, 0);
v_isSharedCheck_4426_ = !lean_is_exclusive(v___x_4398_);
if (v_isSharedCheck_4426_ == 0)
{
v___x_4419_ = v___x_4398_;
v_isShared_4420_ = v_isSharedCheck_4426_;
goto v_resetjp_4418_;
}
else
{
lean_inc(v_a_4417_);
lean_dec(v___x_4398_);
v___x_4419_ = lean_box(0);
v_isShared_4420_ = v_isSharedCheck_4426_;
goto v_resetjp_4418_;
}
v_resetjp_4418_:
{
lean_object* v___x_4421_; uint8_t v___x_4422_; lean_object* v___x_4424_; 
v___x_4421_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4421_, 0, v_a_4417_);
v___x_4422_ = lean_unbox(v_a_4396_);
lean_dec(v_a_4396_);
lean_ctor_set_uint8(v___x_4421_, sizeof(void*)*1, v___x_4422_);
if (v_isShared_4420_ == 0)
{
lean_ctor_set(v___x_4419_, 0, v___x_4421_);
v___x_4424_ = v___x_4419_;
goto v_reusejp_4423_;
}
else
{
lean_object* v_reuseFailAlloc_4425_; 
v_reuseFailAlloc_4425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4425_, 0, v___x_4421_);
v___x_4424_ = v_reuseFailAlloc_4425_;
goto v_reusejp_4423_;
}
v_reusejp_4423_:
{
return v___x_4424_;
}
}
}
}
}
}
}
}
uint8_t l_Lean_Lsp_instDecidableEqMarkupContent_decEq(lean_object* v_x_4429_, lean_object* v_x_4430_){
_start:
{
uint8_t v_kind_4431_; lean_object* v_value_4432_; uint8_t v_kind_4433_; lean_object* v_value_4434_; lean_object* v___x_4435_; lean_object* v___x_4436_; lean_object* v___x_4437_; lean_object* v___x_4438_; uint8_t v___x_4439_; 
v_kind_4431_ = lean_ctor_get_uint8(v_x_4429_, sizeof(void*)*1);
v_value_4432_ = lean_ctor_get(v_x_4429_, 0);
v_kind_4433_ = lean_ctor_get_uint8(v_x_4430_, sizeof(void*)*1);
v_value_4434_ = lean_ctor_get(v_x_4430_, 0);
v___x_4435_ = lean_box(v_kind_4431_);
v___x_4436_ = lean_obj_tag_nat(v___x_4435_);
lean_dec(v___x_4435_);
v___x_4437_ = lean_box(v_kind_4433_);
v___x_4438_ = lean_obj_tag_nat(v___x_4437_);
lean_dec(v___x_4437_);
v___x_4439_ = lean_nat_dec_eq(v___x_4436_, v___x_4438_);
if (v___x_4439_ == 0)
{
return v___x_4439_;
}
else
{
uint8_t v___x_4440_; 
v___x_4440_ = lean_string_dec_eq(v_value_4432_, v_value_4434_);
return v___x_4440_;
}
}
}
LEAN_EXPORT void l_Lean_Lsp_instDecidableEqMarkupContent_decEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4429_ = stack[0].m_obj;
lean_object* v_x_4430_ = stack[1].m_obj;
uint8_t v_res_4441_;
v_res_4441_ = l_Lean_Lsp_instDecidableEqMarkupContent_decEq(v_x_4429_, v_x_4430_);
stack->m_num = v_res_4441_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instDecidableEqMarkupContent_decEq___boxed(lean_object* v_x_4442_, lean_object* v_x_4443_){
_start:
{
uint8_t v_res_4444_; lean_object* v_r_4445_; 
v_res_4444_ = l_Lean_Lsp_instDecidableEqMarkupContent_decEq(v_x_4442_, v_x_4443_);
lean_dec_ref(v_x_4443_);
lean_dec_ref(v_x_4442_);
v_r_4445_ = lean_box(v_res_4444_);
return v_r_4445_;
}
}
uint8_t l_Lean_Lsp_instDecidableEqMarkupContent(lean_object* v_x_4446_, lean_object* v_x_4447_){
_start:
{
uint8_t v___x_4448_; 
v___x_4448_ = l_Lean_Lsp_instDecidableEqMarkupContent_decEq(v_x_4446_, v_x_4447_);
return v___x_4448_;
}
}
LEAN_EXPORT void l_Lean_Lsp_instDecidableEqMarkupContent_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4446_ = stack[0].m_obj;
lean_object* v_x_4447_ = stack[1].m_obj;
uint8_t v_res_4449_;
v_res_4449_ = l_Lean_Lsp_instDecidableEqMarkupContent(v_x_4446_, v_x_4447_);
stack->m_num = v_res_4449_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instDecidableEqMarkupContent___boxed(lean_object* v_x_4450_, lean_object* v_x_4451_){
_start:
{
uint8_t v_res_4452_; lean_object* v_r_4453_; 
v_res_4452_ = l_Lean_Lsp_instDecidableEqMarkupContent(v_x_4450_, v_x_4451_);
lean_dec_ref(v_x_4451_);
lean_dec_ref(v_x_4450_);
v_r_4453_ = lean_box(v_res_4452_);
return v_r_4453_;
}
}
uint64_t l_Lean_Lsp_instHashableMarkupContent_hash(lean_object* v_x_4454_){
_start:
{
uint8_t v_kind_4455_; lean_object* v_value_4456_; uint64_t v___x_4457_; uint64_t v___x_4458_; uint64_t v___x_4459_; uint64_t v___x_4460_; uint64_t v___x_4461_; 
v_kind_4455_ = lean_ctor_get_uint8(v_x_4454_, sizeof(void*)*1);
v_value_4456_ = lean_ctor_get(v_x_4454_, 0);
v___x_4457_ = 0ULL;
v___x_4458_ = l_Lean_Lsp_instHashableMarkupKind_hash(v_kind_4455_);
v___x_4459_ = lean_uint64_mix_hash(v___x_4457_, v___x_4458_);
v___x_4460_ = lean_string_hash(v_value_4456_);
v___x_4461_ = lean_uint64_mix_hash(v___x_4459_, v___x_4460_);
return v___x_4461_;
}
}
LEAN_EXPORT void l_Lean_Lsp_instHashableMarkupContent_hash_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4454_ = stack[0].m_obj;
uint64_t v_res_4462_;
v_res_4462_ = l_Lean_Lsp_instHashableMarkupContent_hash(v_x_4454_);
stack->m_num = v_res_4462_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instHashableMarkupContent_hash___boxed(lean_object* v_x_4463_){
_start:
{
uint64_t v_res_4464_; lean_object* v_r_4465_; 
v_res_4464_ = l_Lean_Lsp_instHashableMarkupContent_hash(v_x_4463_);
lean_dec_ref(v_x_4463_);
v_r_4465_ = lean_box_uint64(v_res_4464_);
return v_r_4465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonProgressParams_toJson___redArg(lean_object* v_inst_4470_, lean_object* v_x_4471_){
_start:
{
lean_object* v_token_4472_; lean_object* v_value_4473_; lean_object* v___x_4475_; uint8_t v_isShared_4476_; uint8_t v_isSharedCheck_4494_; 
v_token_4472_ = lean_ctor_get(v_x_4471_, 0);
v_value_4473_ = lean_ctor_get(v_x_4471_, 1);
v_isSharedCheck_4494_ = !lean_is_exclusive(v_x_4471_);
if (v_isSharedCheck_4494_ == 0)
{
v___x_4475_ = v_x_4471_;
v_isShared_4476_ = v_isSharedCheck_4494_;
goto v_resetjp_4474_;
}
else
{
lean_inc(v_value_4473_);
lean_inc(v_token_4472_);
lean_dec(v_x_4471_);
v___x_4475_ = lean_box(0);
v_isShared_4476_ = v_isSharedCheck_4494_;
goto v_resetjp_4474_;
}
v_resetjp_4474_:
{
lean_object* v___x_4477_; lean_object* v___x_4478_; lean_object* v___x_4480_; 
v___x_4477_ = ((lean_object*)(l_Lean_Lsp_instToJsonProgressParams_toJson___redArg___closed__0));
v___x_4478_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4478_, 0, v_token_4472_);
if (v_isShared_4476_ == 0)
{
lean_ctor_set(v___x_4475_, 1, v___x_4478_);
lean_ctor_set(v___x_4475_, 0, v___x_4477_);
v___x_4480_ = v___x_4475_;
goto v_reusejp_4479_;
}
else
{
lean_object* v_reuseFailAlloc_4493_; 
v_reuseFailAlloc_4493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4493_, 0, v___x_4477_);
lean_ctor_set(v_reuseFailAlloc_4493_, 1, v___x_4478_);
v___x_4480_ = v_reuseFailAlloc_4493_;
goto v_reusejp_4479_;
}
v_reusejp_4479_:
{
lean_object* v___x_4481_; lean_object* v___x_4482_; lean_object* v___x_4483_; lean_object* v___x_4484_; lean_object* v___x_4485_; lean_object* v___x_4486_; lean_object* v___x_4487_; lean_object* v___x_4488_; lean_object* v___x_4489_; lean_object* v___x_4490_; lean_object* v___x_4491_; lean_object* v___x_4492_; 
v___x_4481_ = lean_box(0);
v___x_4482_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4482_, 0, v___x_4480_);
lean_ctor_set(v___x_4482_, 1, v___x_4481_);
v___x_4483_ = ((lean_object*)(l_Lean_Lsp_instToJsonSnippetString_toJson___closed__0));
v___x_4484_ = lean_apply_1(v_inst_4470_, v_value_4473_);
v___x_4485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4485_, 0, v___x_4483_);
lean_ctor_set(v___x_4485_, 1, v___x_4484_);
v___x_4486_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4486_, 0, v___x_4485_);
lean_ctor_set(v___x_4486_, 1, v___x_4481_);
v___x_4487_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4487_, 0, v___x_4486_);
lean_ctor_set(v___x_4487_, 1, v___x_4481_);
v___x_4488_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4488_, 0, v___x_4482_);
lean_ctor_set(v___x_4488_, 1, v___x_4487_);
v___x_4489_ = ((lean_object*)(l_Lean_Lsp_instToJsonProgressParams_toJson___redArg___closed__1));
v___x_4490_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__2));
v___x_4491_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go(lean_box(0), lean_box(0), v___x_4489_, v___x_4488_, v___x_4490_);
v___x_4492_ = l_Lean_Json_mkObj(v___x_4491_);
lean_dec(v___x_4491_);
return v___x_4492_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonProgressParams_toJson(lean_object* v_00_u03b1_4495_, lean_object* v_inst_4496_, lean_object* v_x_4497_){
_start:
{
lean_object* v___x_4498_; 
v___x_4498_ = l_Lean_Lsp_instToJsonProgressParams_toJson___redArg(v_inst_4496_, v_x_4497_);
return v___x_4498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonProgressParams___redArg(lean_object* v_inst_4499_){
_start:
{
lean_object* v___x_4500_; 
v___x_4500_ = lean_alloc_closure((void*)(l_Lean_Lsp_instToJsonProgressParams_toJson), 3, 2);
lean_closure_set(v___x_4500_, 0, lean_box(0));
lean_closure_set(v___x_4500_, 1, v_inst_4499_);
return v___x_4500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonProgressParams(lean_object* v_00_u03b1_4501_, lean_object* v_inst_4502_){
_start:
{
lean_object* v___x_4503_; 
v___x_4503_ = lean_alloc_closure((void*)(l_Lean_Lsp_instToJsonProgressParams_toJson), 3, 2);
lean_closure_set(v___x_4503_, 0, lean_box(0));
lean_closure_set(v___x_4503_, 1, v_inst_4502_);
return v___x_4503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonWorkDoneProgressReport_toJson(lean_object* v_x_4507_){
_start:
{
lean_object* v_kind_4508_; lean_object* v_message_x3f_4509_; uint8_t v_cancellable_4510_; lean_object* v_percentage_x3f_4511_; lean_object* v___x_4512_; lean_object* v___x_4513_; lean_object* v___x_4514_; lean_object* v___x_4515_; lean_object* v___x_4516_; lean_object* v___x_4517_; lean_object* v___x_4518_; lean_object* v___x_4519_; lean_object* v___x_4520_; lean_object* v___x_4521_; lean_object* v___x_4522_; lean_object* v___x_4523_; lean_object* v___x_4524_; lean_object* v___x_4525_; lean_object* v___x_4526_; lean_object* v___x_4527_; lean_object* v___x_4528_; lean_object* v___x_4529_; lean_object* v___x_4530_; lean_object* v___x_4531_; 
v_kind_4508_ = lean_ctor_get(v_x_4507_, 0);
lean_inc_ref(v_kind_4508_);
v_message_x3f_4509_ = lean_ctor_get(v_x_4507_, 1);
lean_inc(v_message_x3f_4509_);
v_cancellable_4510_ = lean_ctor_get_uint8(v_x_4507_, sizeof(void*)*3);
v_percentage_x3f_4511_ = lean_ctor_get(v_x_4507_, 2);
lean_inc(v_percentage_x3f_4511_);
lean_dec_ref(v_x_4507_);
v___x_4512_ = ((lean_object*)(l_Lean_Lsp_instToJsonDocumentChange___lam__0___closed__0));
v___x_4513_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4513_, 0, v_kind_4508_);
v___x_4514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4514_, 0, v___x_4512_);
lean_ctor_set(v___x_4514_, 1, v___x_4513_);
v___x_4515_ = lean_box(0);
v___x_4516_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4516_, 0, v___x_4514_);
lean_ctor_set(v___x_4516_, 1, v___x_4515_);
v___x_4517_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkDoneProgressReport_toJson___closed__0));
v___x_4518_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextEdit_toJson_spec__1(v___x_4517_, v_message_x3f_4509_);
v___x_4519_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkDoneProgressReport_toJson___closed__1));
v___x_4520_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_4520_, 0, v_cancellable_4510_);
v___x_4521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4521_, 0, v___x_4519_);
lean_ctor_set(v___x_4521_, 1, v___x_4520_);
v___x_4522_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4522_, 0, v___x_4521_);
lean_ctor_set(v___x_4522_, 1, v___x_4515_);
v___x_4523_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkDoneProgressReport_toJson___closed__2));
v___x_4524_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonVersionedTextDocumentIdentifier_toJson_spec__0(v___x_4523_, v_percentage_x3f_4511_);
v___x_4525_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4525_, 0, v___x_4524_);
lean_ctor_set(v___x_4525_, 1, v___x_4515_);
v___x_4526_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4526_, 0, v___x_4522_);
lean_ctor_set(v___x_4526_, 1, v___x_4525_);
v___x_4527_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4527_, 0, v___x_4518_);
lean_ctor_set(v___x_4527_, 1, v___x_4526_);
v___x_4528_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4528_, 0, v___x_4516_);
lean_ctor_set(v___x_4528_, 1, v___x_4527_);
v___x_4529_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__2));
v___x_4530_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLocation_toJson_spec__0(v___x_4528_, v___x_4529_);
v___x_4531_ = l_Lean_Json_mkObj(v___x_4530_);
lean_dec(v___x_4530_);
return v___x_4531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonWorkDoneProgressBegin_toJson(lean_object* v_x_4534_){
_start:
{
lean_object* v_toWorkDoneProgressReport_4535_; lean_object* v_title_4536_; lean_object* v___x_4538_; uint8_t v_isShared_4539_; uint8_t v_isSharedCheck_4571_; 
v_toWorkDoneProgressReport_4535_ = lean_ctor_get(v_x_4534_, 0);
v_title_4536_ = lean_ctor_get(v_x_4534_, 1);
v_isSharedCheck_4571_ = !lean_is_exclusive(v_x_4534_);
if (v_isSharedCheck_4571_ == 0)
{
v___x_4538_ = v_x_4534_;
v_isShared_4539_ = v_isSharedCheck_4571_;
goto v_resetjp_4537_;
}
else
{
lean_inc(v_title_4536_);
lean_inc(v_toWorkDoneProgressReport_4535_);
lean_dec(v_x_4534_);
v___x_4538_ = lean_box(0);
v_isShared_4539_ = v_isSharedCheck_4571_;
goto v_resetjp_4537_;
}
v_resetjp_4537_:
{
lean_object* v_kind_4540_; lean_object* v_message_x3f_4541_; uint8_t v_cancellable_4542_; lean_object* v_percentage_x3f_4543_; lean_object* v___x_4544_; lean_object* v___x_4545_; lean_object* v___x_4547_; 
v_kind_4540_ = lean_ctor_get(v_toWorkDoneProgressReport_4535_, 0);
lean_inc_ref(v_kind_4540_);
v_message_x3f_4541_ = lean_ctor_get(v_toWorkDoneProgressReport_4535_, 1);
lean_inc(v_message_x3f_4541_);
v_cancellable_4542_ = lean_ctor_get_uint8(v_toWorkDoneProgressReport_4535_, sizeof(void*)*3);
v_percentage_x3f_4543_ = lean_ctor_get(v_toWorkDoneProgressReport_4535_, 2);
lean_inc(v_percentage_x3f_4543_);
lean_dec_ref(v_toWorkDoneProgressReport_4535_);
v___x_4544_ = ((lean_object*)(l_Lean_Lsp_instToJsonDocumentChange___lam__0___closed__0));
v___x_4545_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4545_, 0, v_kind_4540_);
if (v_isShared_4539_ == 0)
{
lean_ctor_set(v___x_4538_, 1, v___x_4545_);
lean_ctor_set(v___x_4538_, 0, v___x_4544_);
v___x_4547_ = v___x_4538_;
goto v_reusejp_4546_;
}
else
{
lean_object* v_reuseFailAlloc_4570_; 
v_reuseFailAlloc_4570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4570_, 0, v___x_4544_);
lean_ctor_set(v_reuseFailAlloc_4570_, 1, v___x_4545_);
v___x_4547_ = v_reuseFailAlloc_4570_;
goto v_reusejp_4546_;
}
v_reusejp_4546_:
{
lean_object* v___x_4548_; lean_object* v___x_4549_; lean_object* v___x_4550_; lean_object* v___x_4551_; lean_object* v___x_4552_; lean_object* v___x_4553_; lean_object* v___x_4554_; lean_object* v___x_4555_; lean_object* v___x_4556_; lean_object* v___x_4557_; lean_object* v___x_4558_; lean_object* v___x_4559_; lean_object* v___x_4560_; lean_object* v___x_4561_; lean_object* v___x_4562_; lean_object* v___x_4563_; lean_object* v___x_4564_; lean_object* v___x_4565_; lean_object* v___x_4566_; lean_object* v___x_4567_; lean_object* v___x_4568_; lean_object* v___x_4569_; 
v___x_4548_ = lean_box(0);
v___x_4549_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4549_, 0, v___x_4547_);
lean_ctor_set(v___x_4549_, 1, v___x_4548_);
v___x_4550_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkDoneProgressReport_toJson___closed__0));
v___x_4551_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextEdit_toJson_spec__1(v___x_4550_, v_message_x3f_4541_);
v___x_4552_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkDoneProgressReport_toJson___closed__1));
v___x_4553_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_4553_, 0, v_cancellable_4542_);
v___x_4554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4554_, 0, v___x_4552_);
lean_ctor_set(v___x_4554_, 1, v___x_4553_);
v___x_4555_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4555_, 0, v___x_4554_);
lean_ctor_set(v___x_4555_, 1, v___x_4548_);
v___x_4556_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkDoneProgressReport_toJson___closed__2));
v___x_4557_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonVersionedTextDocumentIdentifier_toJson_spec__0(v___x_4556_, v_percentage_x3f_4543_);
v___x_4558_ = ((lean_object*)(l_Lean_Lsp_instToJsonCommand_toJson___closed__0));
v___x_4559_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4559_, 0, v_title_4536_);
v___x_4560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4560_, 0, v___x_4558_);
lean_ctor_set(v___x_4560_, 1, v___x_4559_);
v___x_4561_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4561_, 0, v___x_4560_);
lean_ctor_set(v___x_4561_, 1, v___x_4548_);
v___x_4562_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4562_, 0, v___x_4561_);
lean_ctor_set(v___x_4562_, 1, v___x_4548_);
v___x_4563_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4563_, 0, v___x_4557_);
lean_ctor_set(v___x_4563_, 1, v___x_4562_);
v___x_4564_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4564_, 0, v___x_4555_);
lean_ctor_set(v___x_4564_, 1, v___x_4563_);
v___x_4565_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4565_, 0, v___x_4551_);
lean_ctor_set(v___x_4565_, 1, v___x_4564_);
v___x_4566_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4566_, 0, v___x_4549_);
lean_ctor_set(v___x_4566_, 1, v___x_4565_);
v___x_4567_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__2));
v___x_4568_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLocation_toJson_spec__0(v___x_4566_, v___x_4567_);
v___x_4569_ = l_Lean_Json_mkObj(v___x_4568_);
lean_dec(v___x_4568_);
return v___x_4569_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonWorkDoneProgressEnd_toJson(lean_object* v_x_4574_){
_start:
{
lean_object* v_kind_4575_; lean_object* v_message_x3f_4576_; lean_object* v___x_4578_; uint8_t v_isShared_4579_; uint8_t v_isSharedCheck_4594_; 
v_kind_4575_ = lean_ctor_get(v_x_4574_, 0);
v_message_x3f_4576_ = lean_ctor_get(v_x_4574_, 1);
v_isSharedCheck_4594_ = !lean_is_exclusive(v_x_4574_);
if (v_isSharedCheck_4594_ == 0)
{
v___x_4578_ = v_x_4574_;
v_isShared_4579_ = v_isSharedCheck_4594_;
goto v_resetjp_4577_;
}
else
{
lean_inc(v_message_x3f_4576_);
lean_inc(v_kind_4575_);
lean_dec(v_x_4574_);
v___x_4578_ = lean_box(0);
v_isShared_4579_ = v_isSharedCheck_4594_;
goto v_resetjp_4577_;
}
v_resetjp_4577_:
{
lean_object* v___x_4580_; lean_object* v___x_4581_; lean_object* v___x_4583_; 
v___x_4580_ = ((lean_object*)(l_Lean_Lsp_instToJsonDocumentChange___lam__0___closed__0));
v___x_4581_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4581_, 0, v_kind_4575_);
if (v_isShared_4579_ == 0)
{
lean_ctor_set(v___x_4578_, 1, v___x_4581_);
lean_ctor_set(v___x_4578_, 0, v___x_4580_);
v___x_4583_ = v___x_4578_;
goto v_reusejp_4582_;
}
else
{
lean_object* v_reuseFailAlloc_4593_; 
v_reuseFailAlloc_4593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4593_, 0, v___x_4580_);
lean_ctor_set(v_reuseFailAlloc_4593_, 1, v___x_4581_);
v___x_4583_ = v_reuseFailAlloc_4593_;
goto v_reusejp_4582_;
}
v_reusejp_4582_:
{
lean_object* v___x_4584_; lean_object* v___x_4585_; lean_object* v___x_4586_; lean_object* v___x_4587_; lean_object* v___x_4588_; lean_object* v___x_4589_; lean_object* v___x_4590_; lean_object* v___x_4591_; lean_object* v___x_4592_; 
v___x_4584_ = lean_box(0);
v___x_4585_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4585_, 0, v___x_4583_);
lean_ctor_set(v___x_4585_, 1, v___x_4584_);
v___x_4586_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkDoneProgressReport_toJson___closed__0));
v___x_4587_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextEdit_toJson_spec__1(v___x_4586_, v_message_x3f_4576_);
v___x_4588_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4588_, 0, v___x_4587_);
lean_ctor_set(v___x_4588_, 1, v___x_4584_);
v___x_4589_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4589_, 0, v___x_4585_);
lean_ctor_set(v___x_4589_, 1, v___x_4588_);
v___x_4590_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__2));
v___x_4591_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLocation_toJson_spec__0(v___x_4589_, v___x_4590_);
v___x_4592_ = l_Lean_Json_mkObj(v___x_4591_);
lean_dec(v___x_4591_);
return v___x_4592_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonWorkDoneProgressParams_toJson(lean_object* v_x_4598_){
_start:
{
lean_object* v___x_4599_; lean_object* v___x_4600_; lean_object* v___x_4601_; lean_object* v___x_4602_; lean_object* v___x_4603_; lean_object* v___x_4604_; lean_object* v___x_4605_; 
v___x_4599_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkDoneProgressParams_toJson___closed__0));
v___x_4600_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextEdit_toJson_spec__1(v___x_4599_, v_x_4598_);
v___x_4601_ = lean_box(0);
v___x_4602_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4602_, 0, v___x_4600_);
lean_ctor_set(v___x_4602_, 1, v___x_4601_);
v___x_4603_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__2));
v___x_4604_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLocation_toJson_spec__0(v___x_4602_, v___x_4603_);
v___x_4605_ = l_Lean_Json_mkObj(v___x_4604_);
lean_dec(v___x_4604_);
return v___x_4605_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkDoneProgressParams_fromJson___closed__2(void){
_start:
{
uint8_t v___x_4613_; lean_object* v___x_4614_; lean_object* v___x_4615_; 
v___x_4613_ = 1;
v___x_4614_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWorkDoneProgressParams_fromJson___closed__1));
v___x_4615_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4614_, v___x_4613_);
return v___x_4615_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkDoneProgressParams_fromJson___closed__3(void){
_start:
{
lean_object* v___x_4616_; lean_object* v___x_4617_; lean_object* v___x_4618_; 
v___x_4616_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__5));
v___x_4617_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkDoneProgressParams_fromJson___closed__2, &l_Lean_Lsp_instFromJsonWorkDoneProgressParams_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonWorkDoneProgressParams_fromJson___closed__2);
v___x_4618_ = lean_string_append(v___x_4617_, v___x_4616_);
return v___x_4618_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkDoneProgressParams_fromJson___closed__6(void){
_start:
{
uint8_t v___x_4622_; lean_object* v___x_4623_; lean_object* v___x_4624_; 
v___x_4622_ = 1;
v___x_4623_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWorkDoneProgressParams_fromJson___closed__5));
v___x_4624_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4623_, v___x_4622_);
return v___x_4624_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkDoneProgressParams_fromJson___closed__7(void){
_start:
{
lean_object* v___x_4625_; lean_object* v___x_4626_; lean_object* v___x_4627_; 
v___x_4625_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkDoneProgressParams_fromJson___closed__6, &l_Lean_Lsp_instFromJsonWorkDoneProgressParams_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonWorkDoneProgressParams_fromJson___closed__6);
v___x_4626_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkDoneProgressParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonWorkDoneProgressParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonWorkDoneProgressParams_fromJson___closed__3);
v___x_4627_ = lean_string_append(v___x_4626_, v___x_4625_);
return v___x_4627_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkDoneProgressParams_fromJson___closed__8(void){
_start:
{
lean_object* v___x_4628_; lean_object* v___x_4629_; lean_object* v___x_4630_; 
v___x_4628_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_4629_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkDoneProgressParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonWorkDoneProgressParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonWorkDoneProgressParams_fromJson___closed__7);
v___x_4630_ = lean_string_append(v___x_4629_, v___x_4628_);
return v___x_4630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonWorkDoneProgressParams_fromJson(lean_object* v_json_4631_){
_start:
{
lean_object* v___x_4632_; lean_object* v___x_4633_; 
v___x_4632_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkDoneProgressParams_toJson___closed__0));
v___x_4633_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextEdit_fromJson_spec__1(v_json_4631_, v___x_4632_);
if (lean_obj_tag(v___x_4633_) == 0)
{
lean_object* v_a_4634_; lean_object* v___x_4636_; uint8_t v_isShared_4637_; uint8_t v_isSharedCheck_4643_; 
v_a_4634_ = lean_ctor_get(v___x_4633_, 0);
v_isSharedCheck_4643_ = !lean_is_exclusive(v___x_4633_);
if (v_isSharedCheck_4643_ == 0)
{
v___x_4636_ = v___x_4633_;
v_isShared_4637_ = v_isSharedCheck_4643_;
goto v_resetjp_4635_;
}
else
{
lean_inc(v_a_4634_);
lean_dec(v___x_4633_);
v___x_4636_ = lean_box(0);
v_isShared_4637_ = v_isSharedCheck_4643_;
goto v_resetjp_4635_;
}
v_resetjp_4635_:
{
lean_object* v___x_4638_; lean_object* v___x_4639_; lean_object* v___x_4641_; 
v___x_4638_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkDoneProgressParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonWorkDoneProgressParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonWorkDoneProgressParams_fromJson___closed__8);
v___x_4639_ = lean_string_append(v___x_4638_, v_a_4634_);
lean_dec(v_a_4634_);
if (v_isShared_4637_ == 0)
{
lean_ctor_set(v___x_4636_, 0, v___x_4639_);
v___x_4641_ = v___x_4636_;
goto v_reusejp_4640_;
}
else
{
lean_object* v_reuseFailAlloc_4642_; 
v_reuseFailAlloc_4642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4642_, 0, v___x_4639_);
v___x_4641_ = v_reuseFailAlloc_4642_;
goto v_reusejp_4640_;
}
v_reusejp_4640_:
{
return v___x_4641_;
}
}
}
else
{
if (lean_obj_tag(v___x_4633_) == 0)
{
lean_object* v_a_4644_; lean_object* v___x_4646_; uint8_t v_isShared_4647_; uint8_t v_isSharedCheck_4651_; 
v_a_4644_ = lean_ctor_get(v___x_4633_, 0);
v_isSharedCheck_4651_ = !lean_is_exclusive(v___x_4633_);
if (v_isSharedCheck_4651_ == 0)
{
v___x_4646_ = v___x_4633_;
v_isShared_4647_ = v_isSharedCheck_4651_;
goto v_resetjp_4645_;
}
else
{
lean_inc(v_a_4644_);
lean_dec(v___x_4633_);
v___x_4646_ = lean_box(0);
v_isShared_4647_ = v_isSharedCheck_4651_;
goto v_resetjp_4645_;
}
v_resetjp_4645_:
{
lean_object* v___x_4649_; 
if (v_isShared_4647_ == 0)
{
lean_ctor_set_tag(v___x_4646_, 0);
v___x_4649_ = v___x_4646_;
goto v_reusejp_4648_;
}
else
{
lean_object* v_reuseFailAlloc_4650_; 
v_reuseFailAlloc_4650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4650_, 0, v_a_4644_);
v___x_4649_ = v_reuseFailAlloc_4650_;
goto v_reusejp_4648_;
}
v_reusejp_4648_:
{
return v___x_4649_;
}
}
}
else
{
lean_object* v_a_4652_; lean_object* v___x_4654_; uint8_t v_isShared_4655_; uint8_t v_isSharedCheck_4659_; 
v_a_4652_ = lean_ctor_get(v___x_4633_, 0);
v_isSharedCheck_4659_ = !lean_is_exclusive(v___x_4633_);
if (v_isSharedCheck_4659_ == 0)
{
v___x_4654_ = v___x_4633_;
v_isShared_4655_ = v_isSharedCheck_4659_;
goto v_resetjp_4653_;
}
else
{
lean_inc(v_a_4652_);
lean_dec(v___x_4633_);
v___x_4654_ = lean_box(0);
v_isShared_4655_ = v_isSharedCheck_4659_;
goto v_resetjp_4653_;
}
v_resetjp_4653_:
{
lean_object* v___x_4657_; 
if (v_isShared_4655_ == 0)
{
v___x_4657_ = v___x_4654_;
goto v_reusejp_4656_;
}
else
{
lean_object* v_reuseFailAlloc_4658_; 
v_reuseFailAlloc_4658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4658_, 0, v_a_4652_);
v___x_4657_ = v_reuseFailAlloc_4658_;
goto v_reusejp_4656_;
}
v_reusejp_4656_:
{
return v___x_4657_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonPartialResultParams_toJson(lean_object* v_x_4663_){
_start:
{
lean_object* v___x_4664_; lean_object* v___x_4665_; lean_object* v___x_4666_; lean_object* v___x_4667_; lean_object* v___x_4668_; lean_object* v___x_4669_; lean_object* v___x_4670_; 
v___x_4664_ = ((lean_object*)(l_Lean_Lsp_instToJsonPartialResultParams_toJson___closed__0));
v___x_4665_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextEdit_toJson_spec__1(v___x_4664_, v_x_4663_);
v___x_4666_ = lean_box(0);
v___x_4667_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4667_, 0, v___x_4665_);
lean_ctor_set(v___x_4667_, 1, v___x_4666_);
v___x_4668_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__2));
v___x_4669_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLocation_toJson_spec__0(v___x_4667_, v___x_4668_);
v___x_4670_ = l_Lean_Json_mkObj(v___x_4669_);
lean_dec(v___x_4669_);
return v___x_4670_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPartialResultParams_fromJson___closed__2(void){
_start:
{
uint8_t v___x_4678_; lean_object* v___x_4679_; lean_object* v___x_4680_; 
v___x_4678_ = 1;
v___x_4679_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPartialResultParams_fromJson___closed__1));
v___x_4680_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4679_, v___x_4678_);
return v___x_4680_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPartialResultParams_fromJson___closed__3(void){
_start:
{
lean_object* v___x_4681_; lean_object* v___x_4682_; lean_object* v___x_4683_; 
v___x_4681_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__5));
v___x_4682_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPartialResultParams_fromJson___closed__2, &l_Lean_Lsp_instFromJsonPartialResultParams_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonPartialResultParams_fromJson___closed__2);
v___x_4683_ = lean_string_append(v___x_4682_, v___x_4681_);
return v___x_4683_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPartialResultParams_fromJson___closed__6(void){
_start:
{
uint8_t v___x_4687_; lean_object* v___x_4688_; lean_object* v___x_4689_; 
v___x_4687_ = 1;
v___x_4688_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPartialResultParams_fromJson___closed__5));
v___x_4689_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4688_, v___x_4687_);
return v___x_4689_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPartialResultParams_fromJson___closed__7(void){
_start:
{
lean_object* v___x_4690_; lean_object* v___x_4691_; lean_object* v___x_4692_; 
v___x_4690_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPartialResultParams_fromJson___closed__6, &l_Lean_Lsp_instFromJsonPartialResultParams_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonPartialResultParams_fromJson___closed__6);
v___x_4691_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPartialResultParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonPartialResultParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonPartialResultParams_fromJson___closed__3);
v___x_4692_ = lean_string_append(v___x_4691_, v___x_4690_);
return v___x_4692_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPartialResultParams_fromJson___closed__8(void){
_start:
{
lean_object* v___x_4693_; lean_object* v___x_4694_; lean_object* v___x_4695_; 
v___x_4693_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_4694_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPartialResultParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonPartialResultParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonPartialResultParams_fromJson___closed__7);
v___x_4695_ = lean_string_append(v___x_4694_, v___x_4693_);
return v___x_4695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonPartialResultParams_fromJson(lean_object* v_json_4696_){
_start:
{
lean_object* v___x_4697_; lean_object* v___x_4698_; 
v___x_4697_ = ((lean_object*)(l_Lean_Lsp_instToJsonPartialResultParams_toJson___closed__0));
v___x_4698_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextEdit_fromJson_spec__1(v_json_4696_, v___x_4697_);
if (lean_obj_tag(v___x_4698_) == 0)
{
lean_object* v_a_4699_; lean_object* v___x_4701_; uint8_t v_isShared_4702_; uint8_t v_isSharedCheck_4708_; 
v_a_4699_ = lean_ctor_get(v___x_4698_, 0);
v_isSharedCheck_4708_ = !lean_is_exclusive(v___x_4698_);
if (v_isSharedCheck_4708_ == 0)
{
v___x_4701_ = v___x_4698_;
v_isShared_4702_ = v_isSharedCheck_4708_;
goto v_resetjp_4700_;
}
else
{
lean_inc(v_a_4699_);
lean_dec(v___x_4698_);
v___x_4701_ = lean_box(0);
v_isShared_4702_ = v_isSharedCheck_4708_;
goto v_resetjp_4700_;
}
v_resetjp_4700_:
{
lean_object* v___x_4703_; lean_object* v___x_4704_; lean_object* v___x_4706_; 
v___x_4703_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPartialResultParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonPartialResultParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonPartialResultParams_fromJson___closed__8);
v___x_4704_ = lean_string_append(v___x_4703_, v_a_4699_);
lean_dec(v_a_4699_);
if (v_isShared_4702_ == 0)
{
lean_ctor_set(v___x_4701_, 0, v___x_4704_);
v___x_4706_ = v___x_4701_;
goto v_reusejp_4705_;
}
else
{
lean_object* v_reuseFailAlloc_4707_; 
v_reuseFailAlloc_4707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4707_, 0, v___x_4704_);
v___x_4706_ = v_reuseFailAlloc_4707_;
goto v_reusejp_4705_;
}
v_reusejp_4705_:
{
return v___x_4706_;
}
}
}
else
{
if (lean_obj_tag(v___x_4698_) == 0)
{
lean_object* v_a_4709_; lean_object* v___x_4711_; uint8_t v_isShared_4712_; uint8_t v_isSharedCheck_4716_; 
v_a_4709_ = lean_ctor_get(v___x_4698_, 0);
v_isSharedCheck_4716_ = !lean_is_exclusive(v___x_4698_);
if (v_isSharedCheck_4716_ == 0)
{
v___x_4711_ = v___x_4698_;
v_isShared_4712_ = v_isSharedCheck_4716_;
goto v_resetjp_4710_;
}
else
{
lean_inc(v_a_4709_);
lean_dec(v___x_4698_);
v___x_4711_ = lean_box(0);
v_isShared_4712_ = v_isSharedCheck_4716_;
goto v_resetjp_4710_;
}
v_resetjp_4710_:
{
lean_object* v___x_4714_; 
if (v_isShared_4712_ == 0)
{
lean_ctor_set_tag(v___x_4711_, 0);
v___x_4714_ = v___x_4711_;
goto v_reusejp_4713_;
}
else
{
lean_object* v_reuseFailAlloc_4715_; 
v_reuseFailAlloc_4715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4715_, 0, v_a_4709_);
v___x_4714_ = v_reuseFailAlloc_4715_;
goto v_reusejp_4713_;
}
v_reusejp_4713_:
{
return v___x_4714_;
}
}
}
else
{
lean_object* v_a_4717_; lean_object* v___x_4719_; uint8_t v_isShared_4720_; uint8_t v_isSharedCheck_4724_; 
v_a_4717_ = lean_ctor_get(v___x_4698_, 0);
v_isSharedCheck_4724_ = !lean_is_exclusive(v___x_4698_);
if (v_isSharedCheck_4724_ == 0)
{
v___x_4719_ = v___x_4698_;
v_isShared_4720_ = v_isSharedCheck_4724_;
goto v_resetjp_4718_;
}
else
{
lean_inc(v_a_4717_);
lean_dec(v___x_4698_);
v___x_4719_ = lean_box(0);
v_isShared_4720_ = v_isSharedCheck_4724_;
goto v_resetjp_4718_;
}
v_resetjp_4718_:
{
lean_object* v___x_4722_; 
if (v_isShared_4720_ == 0)
{
v___x_4722_ = v___x_4719_;
goto v_reusejp_4721_;
}
else
{
lean_object* v_reuseFailAlloc_4723_; 
v_reuseFailAlloc_4723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4723_, 0, v_a_4717_);
v___x_4722_ = v_reuseFailAlloc_4723_;
goto v_reusejp_4721_;
}
v_reusejp_4721_:
{
return v___x_4722_;
}
}
}
}
}
}
lean_object* l_Lean_Lsp_instToJsonWorkDoneProgressOptions_toJson(uint8_t v_x_4728_){
_start:
{
lean_object* v___x_4729_; lean_object* v___x_4730_; lean_object* v___x_4731_; lean_object* v___x_4732_; lean_object* v___x_4733_; lean_object* v___x_4734_; lean_object* v___x_4735_; lean_object* v___x_4736_; lean_object* v___x_4737_; 
v___x_4729_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkDoneProgressOptions_toJson___closed__0));
v___x_4730_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_4730_, 0, v_x_4728_);
v___x_4731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4731_, 0, v___x_4729_);
lean_ctor_set(v___x_4731_, 1, v___x_4730_);
v___x_4732_ = lean_box(0);
v___x_4733_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4733_, 0, v___x_4731_);
lean_ctor_set(v___x_4733_, 1, v___x_4732_);
v___x_4734_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4734_, 0, v___x_4733_);
lean_ctor_set(v___x_4734_, 1, v___x_4732_);
v___x_4735_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__2));
v___x_4736_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLocation_toJson_spec__0(v___x_4734_, v___x_4735_);
v___x_4737_ = l_Lean_Json_mkObj(v___x_4736_);
lean_dec(v___x_4736_);
return v___x_4737_;
}
}
LEAN_EXPORT void l_Lean_Lsp_instToJsonWorkDoneProgressOptions_toJson_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_4728_ = stack[0].m_num;
lean_object* v_res_4738_;
v_res_4738_ = l_Lean_Lsp_instToJsonWorkDoneProgressOptions_toJson(v_x_4728_);
stack->m_obj
 = v_res_4738_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonWorkDoneProgressOptions_toJson___boxed(lean_object* v_x_4739_){
_start:
{
uint8_t v_x_29__boxed_4740_; lean_object* v_res_4741_; 
v_x_29__boxed_4740_ = lean_unbox(v_x_4739_);
v_res_4741_ = l_Lean_Lsp_instToJsonWorkDoneProgressOptions_toJson(v_x_29__boxed_4740_);
return v_res_4741_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkDoneProgressOptions_fromJson___closed__2(void){
_start:
{
uint8_t v___x_4749_; lean_object* v___x_4750_; lean_object* v___x_4751_; 
v___x_4749_ = 1;
v___x_4750_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWorkDoneProgressOptions_fromJson___closed__1));
v___x_4751_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4750_, v___x_4749_);
return v___x_4751_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkDoneProgressOptions_fromJson___closed__3(void){
_start:
{
lean_object* v___x_4752_; lean_object* v___x_4753_; lean_object* v___x_4754_; 
v___x_4752_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__5));
v___x_4753_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkDoneProgressOptions_fromJson___closed__2, &l_Lean_Lsp_instFromJsonWorkDoneProgressOptions_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonWorkDoneProgressOptions_fromJson___closed__2);
v___x_4754_ = lean_string_append(v___x_4753_, v___x_4752_);
return v___x_4754_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkDoneProgressOptions_fromJson___closed__5(void){
_start:
{
uint8_t v___x_4757_; lean_object* v___x_4758_; lean_object* v___x_4759_; 
v___x_4757_ = 1;
v___x_4758_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWorkDoneProgressOptions_fromJson___closed__4));
v___x_4759_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4758_, v___x_4757_);
return v___x_4759_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkDoneProgressOptions_fromJson___closed__6(void){
_start:
{
lean_object* v___x_4760_; lean_object* v___x_4761_; lean_object* v___x_4762_; 
v___x_4760_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkDoneProgressOptions_fromJson___closed__5, &l_Lean_Lsp_instFromJsonWorkDoneProgressOptions_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonWorkDoneProgressOptions_fromJson___closed__5);
v___x_4761_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkDoneProgressOptions_fromJson___closed__3, &l_Lean_Lsp_instFromJsonWorkDoneProgressOptions_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonWorkDoneProgressOptions_fromJson___closed__3);
v___x_4762_ = lean_string_append(v___x_4761_, v___x_4760_);
return v___x_4762_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkDoneProgressOptions_fromJson___closed__7(void){
_start:
{
lean_object* v___x_4763_; lean_object* v___x_4764_; lean_object* v___x_4765_; 
v___x_4763_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_4764_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkDoneProgressOptions_fromJson___closed__6, &l_Lean_Lsp_instFromJsonWorkDoneProgressOptions_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonWorkDoneProgressOptions_fromJson___closed__6);
v___x_4765_ = lean_string_append(v___x_4764_, v___x_4763_);
return v___x_4765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonWorkDoneProgressOptions_fromJson(lean_object* v_json_4766_){
_start:
{
lean_object* v___x_4767_; lean_object* v___x_4768_; 
v___x_4767_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkDoneProgressOptions_toJson___closed__0));
v___x_4768_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonChangeAnnotation_fromJson_spec__0(v_json_4766_, v___x_4767_);
if (lean_obj_tag(v___x_4768_) == 0)
{
lean_object* v_a_4769_; lean_object* v___x_4771_; uint8_t v_isShared_4772_; uint8_t v_isSharedCheck_4778_; 
v_a_4769_ = lean_ctor_get(v___x_4768_, 0);
v_isSharedCheck_4778_ = !lean_is_exclusive(v___x_4768_);
if (v_isSharedCheck_4778_ == 0)
{
v___x_4771_ = v___x_4768_;
v_isShared_4772_ = v_isSharedCheck_4778_;
goto v_resetjp_4770_;
}
else
{
lean_inc(v_a_4769_);
lean_dec(v___x_4768_);
v___x_4771_ = lean_box(0);
v_isShared_4772_ = v_isSharedCheck_4778_;
goto v_resetjp_4770_;
}
v_resetjp_4770_:
{
lean_object* v___x_4773_; lean_object* v___x_4774_; lean_object* v___x_4776_; 
v___x_4773_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkDoneProgressOptions_fromJson___closed__7, &l_Lean_Lsp_instFromJsonWorkDoneProgressOptions_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonWorkDoneProgressOptions_fromJson___closed__7);
v___x_4774_ = lean_string_append(v___x_4773_, v_a_4769_);
lean_dec(v_a_4769_);
if (v_isShared_4772_ == 0)
{
lean_ctor_set(v___x_4771_, 0, v___x_4774_);
v___x_4776_ = v___x_4771_;
goto v_reusejp_4775_;
}
else
{
lean_object* v_reuseFailAlloc_4777_; 
v_reuseFailAlloc_4777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4777_, 0, v___x_4774_);
v___x_4776_ = v_reuseFailAlloc_4777_;
goto v_reusejp_4775_;
}
v_reusejp_4775_:
{
return v___x_4776_;
}
}
}
else
{
if (lean_obj_tag(v___x_4768_) == 0)
{
lean_object* v_a_4779_; lean_object* v___x_4781_; uint8_t v_isShared_4782_; uint8_t v_isSharedCheck_4786_; 
v_a_4779_ = lean_ctor_get(v___x_4768_, 0);
v_isSharedCheck_4786_ = !lean_is_exclusive(v___x_4768_);
if (v_isSharedCheck_4786_ == 0)
{
v___x_4781_ = v___x_4768_;
v_isShared_4782_ = v_isSharedCheck_4786_;
goto v_resetjp_4780_;
}
else
{
lean_inc(v_a_4779_);
lean_dec(v___x_4768_);
v___x_4781_ = lean_box(0);
v_isShared_4782_ = v_isSharedCheck_4786_;
goto v_resetjp_4780_;
}
v_resetjp_4780_:
{
lean_object* v___x_4784_; 
if (v_isShared_4782_ == 0)
{
lean_ctor_set_tag(v___x_4781_, 0);
v___x_4784_ = v___x_4781_;
goto v_reusejp_4783_;
}
else
{
lean_object* v_reuseFailAlloc_4785_; 
v_reuseFailAlloc_4785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4785_, 0, v_a_4779_);
v___x_4784_ = v_reuseFailAlloc_4785_;
goto v_reusejp_4783_;
}
v_reusejp_4783_:
{
return v___x_4784_;
}
}
}
else
{
lean_object* v_a_4787_; lean_object* v___x_4789_; uint8_t v_isShared_4790_; uint8_t v_isSharedCheck_4794_; 
v_a_4787_ = lean_ctor_get(v___x_4768_, 0);
v_isSharedCheck_4794_ = !lean_is_exclusive(v___x_4768_);
if (v_isSharedCheck_4794_ == 0)
{
v___x_4789_ = v___x_4768_;
v_isShared_4790_ = v_isSharedCheck_4794_;
goto v_resetjp_4788_;
}
else
{
lean_inc(v_a_4787_);
lean_dec(v___x_4768_);
v___x_4789_ = lean_box(0);
v_isShared_4790_ = v_isSharedCheck_4794_;
goto v_resetjp_4788_;
}
v_resetjp_4788_:
{
lean_object* v___x_4792_; 
if (v_isShared_4790_ == 0)
{
v___x_4792_ = v___x_4789_;
goto v_reusejp_4791_;
}
else
{
lean_object* v_reuseFailAlloc_4793_; 
v_reuseFailAlloc_4793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4793_, 0, v_a_4787_);
v___x_4792_ = v_reuseFailAlloc_4793_;
goto v_reusejp_4791_;
}
v_reusejp_4791_:
{
return v___x_4792_;
}
}
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonResolveSupport_fromJson_spec__0_spec__0_spec__1(size_t v_sz_4797_, size_t v_i_4798_, lean_object* v_bs_4799_){
_start:
{
uint8_t v___x_4800_; 
v___x_4800_ = lean_usize_dec_lt(v_i_4798_, v_sz_4797_);
if (v___x_4800_ == 0)
{
lean_object* v___x_4801_; 
v___x_4801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4801_, 0, v_bs_4799_);
return v___x_4801_;
}
else
{
lean_object* v_v_4802_; lean_object* v___x_4803_; 
v_v_4802_ = lean_array_uget_borrowed(v_bs_4799_, v_i_4798_);
lean_inc(v_v_4802_);
v___x_4803_ = l_Lean_Json_getStr_x3f(v_v_4802_);
if (lean_obj_tag(v___x_4803_) == 0)
{
lean_object* v_a_4804_; lean_object* v___x_4806_; uint8_t v_isShared_4807_; uint8_t v_isSharedCheck_4811_; 
lean_dec_ref(v_bs_4799_);
v_a_4804_ = lean_ctor_get(v___x_4803_, 0);
v_isSharedCheck_4811_ = !lean_is_exclusive(v___x_4803_);
if (v_isSharedCheck_4811_ == 0)
{
v___x_4806_ = v___x_4803_;
v_isShared_4807_ = v_isSharedCheck_4811_;
goto v_resetjp_4805_;
}
else
{
lean_inc(v_a_4804_);
lean_dec(v___x_4803_);
v___x_4806_ = lean_box(0);
v_isShared_4807_ = v_isSharedCheck_4811_;
goto v_resetjp_4805_;
}
v_resetjp_4805_:
{
lean_object* v___x_4809_; 
if (v_isShared_4807_ == 0)
{
v___x_4809_ = v___x_4806_;
goto v_reusejp_4808_;
}
else
{
lean_object* v_reuseFailAlloc_4810_; 
v_reuseFailAlloc_4810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4810_, 0, v_a_4804_);
v___x_4809_ = v_reuseFailAlloc_4810_;
goto v_reusejp_4808_;
}
v_reusejp_4808_:
{
return v___x_4809_;
}
}
}
else
{
lean_object* v_a_4812_; lean_object* v___x_4813_; lean_object* v_bs_x27_4814_; size_t v___x_4815_; size_t v___x_4816_; lean_object* v___x_4817_; 
v_a_4812_ = lean_ctor_get(v___x_4803_, 0);
lean_inc(v_a_4812_);
lean_dec_ref_known(v___x_4803_, 1);
v___x_4813_ = lean_unsigned_to_nat(0u);
v_bs_x27_4814_ = lean_array_uset(v_bs_4799_, v_i_4798_, v___x_4813_);
v___x_4815_ = ((size_t)1ULL);
v___x_4816_ = lean_usize_add(v_i_4798_, v___x_4815_);
v___x_4817_ = lean_array_uset(v_bs_x27_4814_, v_i_4798_, v_a_4812_);
v_i_4798_ = v___x_4816_;
v_bs_4799_ = v___x_4817_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonResolveSupport_fromJson_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
size_t v_sz_4797_ = stack[0].m_num;
size_t v_i_4798_ = stack[1].m_num;
lean_object* v_bs_4799_ = stack[2].m_obj;
lean_object* v_res_4819_;
v_res_4819_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonResolveSupport_fromJson_spec__0_spec__0_spec__1(v_sz_4797_, v_i_4798_, v_bs_4799_);
stack->m_obj
 = v_res_4819_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonResolveSupport_fromJson_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_4820_, lean_object* v_i_4821_, lean_object* v_bs_4822_){
_start:
{
size_t v_sz_boxed_4823_; size_t v_i_boxed_4824_; lean_object* v_res_4825_; 
v_sz_boxed_4823_ = lean_unbox_usize(v_sz_4820_);
lean_dec(v_sz_4820_);
v_i_boxed_4824_ = lean_unbox_usize(v_i_4821_);
lean_dec(v_i_4821_);
v_res_4825_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonResolveSupport_fromJson_spec__0_spec__0_spec__1(v_sz_boxed_4823_, v_i_boxed_4824_, v_bs_4822_);
return v_res_4825_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonResolveSupport_fromJson_spec__0_spec__0(lean_object* v_x_4826_){
_start:
{
if (lean_obj_tag(v_x_4826_) == 4)
{
lean_object* v_elems_4827_; size_t v_sz_4828_; size_t v___x_4829_; lean_object* v___x_4830_; 
v_elems_4827_ = lean_ctor_get(v_x_4826_, 0);
lean_inc_ref(v_elems_4827_);
lean_dec_ref_known(v_x_4826_, 1);
v_sz_4828_ = lean_array_size(v_elems_4827_);
v___x_4829_ = ((size_t)0ULL);
v___x_4830_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonResolveSupport_fromJson_spec__0_spec__0_spec__1(v_sz_4828_, v___x_4829_, v_elems_4827_);
return v___x_4830_;
}
else
{
lean_object* v___x_4831_; lean_object* v___x_4832_; lean_object* v___x_4833_; lean_object* v___x_4834_; lean_object* v___x_4835_; lean_object* v___x_4836_; lean_object* v___x_4837_; 
v___x_4831_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCommand_fromJson_spec__0_spec__0_spec__1___closed__0));
v___x_4832_ = lean_unsigned_to_nat(80u);
v___x_4833_ = l_Lean_Json_pretty(v_x_4826_, v___x_4832_);
v___x_4834_ = lean_string_append(v___x_4831_, v___x_4833_);
lean_dec_ref(v___x_4833_);
v___x_4835_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCommand_fromJson_spec__0_spec__0_spec__1___closed__1));
v___x_4836_ = lean_string_append(v___x_4834_, v___x_4835_);
v___x_4837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4837_, 0, v___x_4836_);
return v___x_4837_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonResolveSupport_fromJson_spec__0(lean_object* v_j_4838_, lean_object* v_k_4839_){
_start:
{
lean_object* v___x_4840_; lean_object* v___x_4841_; 
v___x_4840_ = l_Lean_Json_getObjValD(v_j_4838_, v_k_4839_);
v___x_4841_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonResolveSupport_fromJson_spec__0_spec__0(v___x_4840_);
return v___x_4841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonResolveSupport_fromJson_spec__0___boxed(lean_object* v_j_4842_, lean_object* v_k_4843_){
_start:
{
lean_object* v_res_4844_; 
v_res_4844_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonResolveSupport_fromJson_spec__0(v_j_4842_, v_k_4843_);
lean_dec_ref(v_k_4843_);
return v_res_4844_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonResolveSupport_fromJson___closed__3(void){
_start:
{
uint8_t v___x_4851_; lean_object* v___x_4852_; lean_object* v___x_4853_; 
v___x_4851_ = 1;
v___x_4852_ = ((lean_object*)(l_Lean_Lsp_instFromJsonResolveSupport_fromJson___closed__2));
v___x_4853_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4852_, v___x_4851_);
return v___x_4853_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonResolveSupport_fromJson___closed__4(void){
_start:
{
lean_object* v___x_4854_; lean_object* v___x_4855_; lean_object* v___x_4856_; 
v___x_4854_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__5));
v___x_4855_ = lean_obj_once(&l_Lean_Lsp_instFromJsonResolveSupport_fromJson___closed__3, &l_Lean_Lsp_instFromJsonResolveSupport_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonResolveSupport_fromJson___closed__3);
v___x_4856_ = lean_string_append(v___x_4855_, v___x_4854_);
return v___x_4856_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonResolveSupport_fromJson___closed__6(void){
_start:
{
uint8_t v___x_4859_; lean_object* v___x_4860_; lean_object* v___x_4861_; 
v___x_4859_ = 1;
v___x_4860_ = ((lean_object*)(l_Lean_Lsp_instFromJsonResolveSupport_fromJson___closed__5));
v___x_4861_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4860_, v___x_4859_);
return v___x_4861_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonResolveSupport_fromJson___closed__7(void){
_start:
{
lean_object* v___x_4862_; lean_object* v___x_4863_; lean_object* v___x_4864_; 
v___x_4862_ = lean_obj_once(&l_Lean_Lsp_instFromJsonResolveSupport_fromJson___closed__6, &l_Lean_Lsp_instFromJsonResolveSupport_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonResolveSupport_fromJson___closed__6);
v___x_4863_ = lean_obj_once(&l_Lean_Lsp_instFromJsonResolveSupport_fromJson___closed__4, &l_Lean_Lsp_instFromJsonResolveSupport_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonResolveSupport_fromJson___closed__4);
v___x_4864_ = lean_string_append(v___x_4863_, v___x_4862_);
return v___x_4864_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonResolveSupport_fromJson___closed__8(void){
_start:
{
lean_object* v___x_4865_; lean_object* v___x_4866_; lean_object* v___x_4867_; 
v___x_4865_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLocation_fromJson___closed__10));
v___x_4866_ = lean_obj_once(&l_Lean_Lsp_instFromJsonResolveSupport_fromJson___closed__7, &l_Lean_Lsp_instFromJsonResolveSupport_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonResolveSupport_fromJson___closed__7);
v___x_4867_ = lean_string_append(v___x_4866_, v___x_4865_);
return v___x_4867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonResolveSupport_fromJson(lean_object* v_json_4868_){
_start:
{
lean_object* v___x_4869_; lean_object* v___x_4870_; 
v___x_4869_ = ((lean_object*)(l_Lean_Lsp_instFromJsonResolveSupport_fromJson___closed__0));
v___x_4870_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonResolveSupport_fromJson_spec__0(v_json_4868_, v___x_4869_);
if (lean_obj_tag(v___x_4870_) == 0)
{
lean_object* v_a_4871_; lean_object* v___x_4873_; uint8_t v_isShared_4874_; uint8_t v_isSharedCheck_4880_; 
v_a_4871_ = lean_ctor_get(v___x_4870_, 0);
v_isSharedCheck_4880_ = !lean_is_exclusive(v___x_4870_);
if (v_isSharedCheck_4880_ == 0)
{
v___x_4873_ = v___x_4870_;
v_isShared_4874_ = v_isSharedCheck_4880_;
goto v_resetjp_4872_;
}
else
{
lean_inc(v_a_4871_);
lean_dec(v___x_4870_);
v___x_4873_ = lean_box(0);
v_isShared_4874_ = v_isSharedCheck_4880_;
goto v_resetjp_4872_;
}
v_resetjp_4872_:
{
lean_object* v___x_4875_; lean_object* v___x_4876_; lean_object* v___x_4878_; 
v___x_4875_ = lean_obj_once(&l_Lean_Lsp_instFromJsonResolveSupport_fromJson___closed__8, &l_Lean_Lsp_instFromJsonResolveSupport_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonResolveSupport_fromJson___closed__8);
v___x_4876_ = lean_string_append(v___x_4875_, v_a_4871_);
lean_dec(v_a_4871_);
if (v_isShared_4874_ == 0)
{
lean_ctor_set(v___x_4873_, 0, v___x_4876_);
v___x_4878_ = v___x_4873_;
goto v_reusejp_4877_;
}
else
{
lean_object* v_reuseFailAlloc_4879_; 
v_reuseFailAlloc_4879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4879_, 0, v___x_4876_);
v___x_4878_ = v_reuseFailAlloc_4879_;
goto v_reusejp_4877_;
}
v_reusejp_4877_:
{
return v___x_4878_;
}
}
}
else
{
if (lean_obj_tag(v___x_4870_) == 0)
{
lean_object* v_a_4881_; lean_object* v___x_4883_; uint8_t v_isShared_4884_; uint8_t v_isSharedCheck_4888_; 
v_a_4881_ = lean_ctor_get(v___x_4870_, 0);
v_isSharedCheck_4888_ = !lean_is_exclusive(v___x_4870_);
if (v_isSharedCheck_4888_ == 0)
{
v___x_4883_ = v___x_4870_;
v_isShared_4884_ = v_isSharedCheck_4888_;
goto v_resetjp_4882_;
}
else
{
lean_inc(v_a_4881_);
lean_dec(v___x_4870_);
v___x_4883_ = lean_box(0);
v_isShared_4884_ = v_isSharedCheck_4888_;
goto v_resetjp_4882_;
}
v_resetjp_4882_:
{
lean_object* v___x_4886_; 
if (v_isShared_4884_ == 0)
{
lean_ctor_set_tag(v___x_4883_, 0);
v___x_4886_ = v___x_4883_;
goto v_reusejp_4885_;
}
else
{
lean_object* v_reuseFailAlloc_4887_; 
v_reuseFailAlloc_4887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4887_, 0, v_a_4881_);
v___x_4886_ = v_reuseFailAlloc_4887_;
goto v_reusejp_4885_;
}
v_reusejp_4885_:
{
return v___x_4886_;
}
}
}
else
{
lean_object* v_a_4889_; lean_object* v___x_4891_; uint8_t v_isShared_4892_; uint8_t v_isSharedCheck_4896_; 
v_a_4889_ = lean_ctor_get(v___x_4870_, 0);
v_isSharedCheck_4896_ = !lean_is_exclusive(v___x_4870_);
if (v_isSharedCheck_4896_ == 0)
{
v___x_4891_ = v___x_4870_;
v_isShared_4892_ = v_isSharedCheck_4896_;
goto v_resetjp_4890_;
}
else
{
lean_inc(v_a_4889_);
lean_dec(v___x_4870_);
v___x_4891_ = lean_box(0);
v_isShared_4892_ = v_isSharedCheck_4896_;
goto v_resetjp_4890_;
}
v_resetjp_4890_:
{
lean_object* v___x_4894_; 
if (v_isShared_4892_ == 0)
{
v___x_4894_ = v___x_4891_;
goto v_reusejp_4893_;
}
else
{
lean_object* v_reuseFailAlloc_4895_; 
v_reuseFailAlloc_4895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4895_, 0, v_a_4889_);
v___x_4894_ = v_reuseFailAlloc_4895_;
goto v_reusejp_4893_;
}
v_reusejp_4893_:
{
return v___x_4894_;
}
}
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonResolveSupport_toJson_spec__0_spec__0(size_t v_sz_4899_, size_t v_i_4900_, lean_object* v_bs_4901_){
_start:
{
uint8_t v___x_4902_; 
v___x_4902_ = lean_usize_dec_lt(v_i_4900_, v_sz_4899_);
if (v___x_4902_ == 0)
{
return v_bs_4901_;
}
else
{
lean_object* v_v_4903_; lean_object* v___x_4904_; lean_object* v_bs_x27_4905_; lean_object* v___x_4906_; size_t v___x_4907_; size_t v___x_4908_; lean_object* v___x_4909_; 
v_v_4903_ = lean_array_uget(v_bs_4901_, v_i_4900_);
v___x_4904_ = lean_unsigned_to_nat(0u);
v_bs_x27_4905_ = lean_array_uset(v_bs_4901_, v_i_4900_, v___x_4904_);
v___x_4906_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4906_, 0, v_v_4903_);
v___x_4907_ = ((size_t)1ULL);
v___x_4908_ = lean_usize_add(v_i_4900_, v___x_4907_);
v___x_4909_ = lean_array_uset(v_bs_x27_4905_, v_i_4900_, v___x_4906_);
v_i_4900_ = v___x_4908_;
v_bs_4901_ = v___x_4909_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonResolveSupport_toJson_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_4899_ = stack[0].m_num;
size_t v_i_4900_ = stack[1].m_num;
lean_object* v_bs_4901_ = stack[2].m_obj;
lean_object* v_res_4911_;
v_res_4911_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonResolveSupport_toJson_spec__0_spec__0(v_sz_4899_, v_i_4900_, v_bs_4901_);
stack->m_obj
 = v_res_4911_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonResolveSupport_toJson_spec__0_spec__0___boxed(lean_object* v_sz_4912_, lean_object* v_i_4913_, lean_object* v_bs_4914_){
_start:
{
size_t v_sz_boxed_4915_; size_t v_i_boxed_4916_; lean_object* v_res_4917_; 
v_sz_boxed_4915_ = lean_unbox_usize(v_sz_4912_);
lean_dec(v_sz_4912_);
v_i_boxed_4916_ = lean_unbox_usize(v_i_4913_);
lean_dec(v_i_4913_);
v_res_4917_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonResolveSupport_toJson_spec__0_spec__0(v_sz_boxed_4915_, v_i_boxed_4916_, v_bs_4914_);
return v_res_4917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonResolveSupport_toJson_spec__0(lean_object* v_a_4918_){
_start:
{
size_t v_sz_4919_; size_t v___x_4920_; lean_object* v___x_4921_; lean_object* v___x_4922_; 
v_sz_4919_ = lean_array_size(v_a_4918_);
v___x_4920_ = ((size_t)0ULL);
v___x_4921_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonResolveSupport_toJson_spec__0_spec__0(v_sz_4919_, v___x_4920_, v_a_4918_);
v___x_4922_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_4922_, 0, v___x_4921_);
return v___x_4922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonResolveSupport_toJson(lean_object* v_x_4923_){
_start:
{
lean_object* v___x_4924_; lean_object* v___x_4925_; lean_object* v___x_4926_; lean_object* v___x_4927_; lean_object* v___x_4928_; lean_object* v___x_4929_; lean_object* v___x_4930_; lean_object* v___x_4931_; lean_object* v___x_4932_; 
v___x_4924_ = ((lean_object*)(l_Lean_Lsp_instFromJsonResolveSupport_fromJson___closed__0));
v___x_4925_ = l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonResolveSupport_toJson_spec__0(v_x_4923_);
v___x_4926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4926_, 0, v___x_4924_);
lean_ctor_set(v___x_4926_, 1, v___x_4925_);
v___x_4927_ = lean_box(0);
v___x_4928_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4928_, 0, v___x_4926_);
lean_ctor_set(v___x_4928_, 1, v___x_4927_);
v___x_4929_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4929_, 0, v___x_4928_);
lean_ctor_set(v___x_4929_, 1, v___x_4927_);
v___x_4930_ = ((lean_object*)(l_Lean_Lsp_instToJsonLocation_toJson___closed__2));
v___x_4931_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonLocation_toJson_spec__0(v___x_4929_, v___x_4930_);
v___x_4932_ = l_Lean_Json_mkObj(v___x_4931_);
lean_dec(v___x_4931_);
return v___x_4932_;
}
}
lean_object* runtime_initialize_Lean_Data_Json(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Lsp_BasicAux(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_Coe(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_Lsp_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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

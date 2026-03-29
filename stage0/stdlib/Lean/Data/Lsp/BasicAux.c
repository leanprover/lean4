// Lean compiler output
// Module: Lean.Data.Lsp.BasicAux
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
lean_object* l_Lean_JsonNumber_fromNat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
lean_object* l_Lean_Json_getNat_x3f(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Lsp_instInhabitedPosition_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Lsp_instInhabitedPosition_default___closed__0 = (const lean_object*)&l_Lean_Lsp_instInhabitedPosition_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instInhabitedPosition_default = (const lean_object*)&l_Lean_Lsp_instInhabitedPosition_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instInhabitedPosition = (const lean_object*)&l_Lean_Lsp_instInhabitedPosition_default___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Lsp_instBEqPosition_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqPosition_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_instBEqPosition___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instBEqPosition_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instBEqPosition___closed__0 = (const lean_object*)&l_Lean_Lsp_instBEqPosition___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instBEqPosition = (const lean_object*)&l_Lean_Lsp_instBEqPosition___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Lsp_instOrdPosition_ord(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instOrdPosition_ord___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_instOrdPosition___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instOrdPosition_ord___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instOrdPosition___closed__0 = (const lean_object*)&l_Lean_Lsp_instOrdPosition___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instOrdPosition = (const lean_object*)&l_Lean_Lsp_instOrdPosition___closed__0_value;
LEAN_EXPORT uint64_t l_Lean_Lsp_instHashablePosition_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instHashablePosition_hash___boxed(lean_object*);
static const lean_closure_object l_Lean_Lsp_instHashablePosition___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instHashablePosition_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instHashablePosition___closed__0 = (const lean_object*)&l_Lean_Lsp_instHashablePosition___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instHashablePosition = (const lean_object*)&l_Lean_Lsp_instHashablePosition___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonPosition_toJson_spec__0(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instToJsonPosition_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "line"};
static const lean_object* l_Lean_Lsp_instToJsonPosition_toJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonPosition_toJson___closed__0_value;
static const lean_string_object l_Lean_Lsp_instToJsonPosition_toJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "character"};
static const lean_object* l_Lean_Lsp_instToJsonPosition_toJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instToJsonPosition_toJson___closed__1_value;
static const lean_array_object l_Lean_Lsp_instToJsonPosition_toJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Lsp_instToJsonPosition_toJson___closed__2 = (const lean_object*)&l_Lean_Lsp_instToJsonPosition_toJson___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonPosition_toJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonPosition___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonPosition_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonPosition___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonPosition___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonPosition = (const lean_object*)&l_Lean_Lsp_instToJsonPosition___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPosition_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPosition_fromJson_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instFromJsonPosition_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Lsp_instFromJsonPosition_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonPosition_fromJson___closed__0_value;
static const lean_string_object l_Lean_Lsp_instFromJsonPosition_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Lsp"};
static const lean_object* l_Lean_Lsp_instFromJsonPosition_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonPosition_fromJson___closed__1_value;
static const lean_string_object l_Lean_Lsp_instFromJsonPosition_fromJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Position"};
static const lean_object* l_Lean_Lsp_instFromJsonPosition_fromJson___closed__2 = (const lean_object*)&l_Lean_Lsp_instFromJsonPosition_fromJson___closed__2_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonPosition_fromJson___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonPosition_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonPosition_fromJson___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonPosition_fromJson___closed__3_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonPosition_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonPosition_fromJson___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonPosition_fromJson___closed__3_value_aux_1),((lean_object*)&l_Lean_Lsp_instFromJsonPosition_fromJson___closed__2_value),LEAN_SCALAR_PTR_LITERAL(29, 140, 170, 135, 118, 250, 230, 191)}};
static const lean_object* l_Lean_Lsp_instFromJsonPosition_fromJson___closed__3 = (const lean_object*)&l_Lean_Lsp_instFromJsonPosition_fromJson___closed__3_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonPosition_fromJson___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonPosition_fromJson___closed__4;
static const lean_string_object l_Lean_Lsp_instFromJsonPosition_fromJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lean_Lsp_instFromJsonPosition_fromJson___closed__5 = (const lean_object*)&l_Lean_Lsp_instFromJsonPosition_fromJson___closed__5_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonPosition_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonPosition_fromJson___closed__6;
static const lean_ctor_object l_Lean_Lsp_instFromJsonPosition_fromJson___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instToJsonPosition_toJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(45, 20, 170, 234, 25, 144, 248, 101)}};
static const lean_object* l_Lean_Lsp_instFromJsonPosition_fromJson___closed__7 = (const lean_object*)&l_Lean_Lsp_instFromJsonPosition_fromJson___closed__7_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonPosition_fromJson___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonPosition_fromJson___closed__8;
static lean_once_cell_t l_Lean_Lsp_instFromJsonPosition_fromJson___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonPosition_fromJson___closed__9;
static const lean_string_object l_Lean_Lsp_instFromJsonPosition_fromJson___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l_Lean_Lsp_instFromJsonPosition_fromJson___closed__10 = (const lean_object*)&l_Lean_Lsp_instFromJsonPosition_fromJson___closed__10_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonPosition_fromJson___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonPosition_fromJson___closed__11;
static const lean_ctor_object l_Lean_Lsp_instFromJsonPosition_fromJson___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instToJsonPosition_toJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(51, 241, 116, 45, 138, 85, 32, 145)}};
static const lean_object* l_Lean_Lsp_instFromJsonPosition_fromJson___closed__12 = (const lean_object*)&l_Lean_Lsp_instFromJsonPosition_fromJson___closed__12_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonPosition_fromJson___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonPosition_fromJson___closed__13;
static lean_once_cell_t l_Lean_Lsp_instFromJsonPosition_fromJson___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonPosition_fromJson___closed__14;
static lean_once_cell_t l_Lean_Lsp_instFromJsonPosition_fromJson___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonPosition_fromJson___closed__15;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonPosition_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonPosition___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonPosition_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonPosition___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonPosition___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonPosition = (const lean_object*)&l_Lean_Lsp_instFromJsonPosition___closed__0_value;
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Lsp_instReprPosition_repr_spec__0(lean_object*);
static const lean_string_object l_Lean_Lsp_instReprPosition_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Lean_Lsp_instReprPosition_repr___redArg___closed__0 = (const lean_object*)&l_Lean_Lsp_instReprPosition_repr___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_instReprPosition_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Lsp_instToJsonPosition_toJson___closed__0_value)}};
static const lean_object* l_Lean_Lsp_instReprPosition_repr___redArg___closed__1 = (const lean_object*)&l_Lean_Lsp_instReprPosition_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Lsp_instReprPosition_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instReprPosition_repr___redArg___closed__1_value)}};
static const lean_object* l_Lean_Lsp_instReprPosition_repr___redArg___closed__2 = (const lean_object*)&l_Lean_Lsp_instReprPosition_repr___redArg___closed__2_value;
static const lean_string_object l_Lean_Lsp_instReprPosition_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lean_Lsp_instReprPosition_repr___redArg___closed__3 = (const lean_object*)&l_Lean_Lsp_instReprPosition_repr___redArg___closed__3_value;
static const lean_ctor_object l_Lean_Lsp_instReprPosition_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Lsp_instReprPosition_repr___redArg___closed__3_value)}};
static const lean_object* l_Lean_Lsp_instReprPosition_repr___redArg___closed__4 = (const lean_object*)&l_Lean_Lsp_instReprPosition_repr___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Lsp_instReprPosition_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Lsp_instReprPosition_repr___redArg___closed__2_value),((lean_object*)&l_Lean_Lsp_instReprPosition_repr___redArg___closed__4_value)}};
static const lean_object* l_Lean_Lsp_instReprPosition_repr___redArg___closed__5 = (const lean_object*)&l_Lean_Lsp_instReprPosition_repr___redArg___closed__5_value;
static lean_once_cell_t l_Lean_Lsp_instReprPosition_repr___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instReprPosition_repr___redArg___closed__6;
static const lean_string_object l_Lean_Lsp_instReprPosition_repr___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lean_Lsp_instReprPosition_repr___redArg___closed__7 = (const lean_object*)&l_Lean_Lsp_instReprPosition_repr___redArg___closed__7_value;
static const lean_ctor_object l_Lean_Lsp_instReprPosition_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Lsp_instReprPosition_repr___redArg___closed__7_value)}};
static const lean_object* l_Lean_Lsp_instReprPosition_repr___redArg___closed__8 = (const lean_object*)&l_Lean_Lsp_instReprPosition_repr___redArg___closed__8_value;
static const lean_ctor_object l_Lean_Lsp_instReprPosition_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Lsp_instToJsonPosition_toJson___closed__1_value)}};
static const lean_object* l_Lean_Lsp_instReprPosition_repr___redArg___closed__9 = (const lean_object*)&l_Lean_Lsp_instReprPosition_repr___redArg___closed__9_value;
static lean_once_cell_t l_Lean_Lsp_instReprPosition_repr___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instReprPosition_repr___redArg___closed__10;
static const lean_string_object l_Lean_Lsp_instReprPosition_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Lean_Lsp_instReprPosition_repr___redArg___closed__11 = (const lean_object*)&l_Lean_Lsp_instReprPosition_repr___redArg___closed__11_value;
static lean_once_cell_t l_Lean_Lsp_instReprPosition_repr___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instReprPosition_repr___redArg___closed__12;
static lean_once_cell_t l_Lean_Lsp_instReprPosition_repr___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instReprPosition_repr___redArg___closed__13;
static const lean_ctor_object l_Lean_Lsp_instReprPosition_repr___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Lsp_instReprPosition_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_Lsp_instReprPosition_repr___redArg___closed__14 = (const lean_object*)&l_Lean_Lsp_instReprPosition_repr___redArg___closed__14_value;
static const lean_ctor_object l_Lean_Lsp_instReprPosition_repr___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Lsp_instReprPosition_repr___redArg___closed__11_value)}};
static const lean_object* l_Lean_Lsp_instReprPosition_repr___redArg___closed__15 = (const lean_object*)&l_Lean_Lsp_instReprPosition_repr___redArg___closed__15_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instReprPosition_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instReprPosition_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instReprPosition_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_instReprPosition___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instReprPosition_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instReprPosition___closed__0 = (const lean_object*)&l_Lean_Lsp_instReprPosition___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instReprPosition = (const lean_object*)&l_Lean_Lsp_instReprPosition___closed__0_value;
static const lean_string_object l_Lean_Lsp_instToStringPosition___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Lean_Lsp_instToStringPosition___lam__0___closed__0 = (const lean_object*)&l_Lean_Lsp_instToStringPosition___lam__0___closed__0_value;
static const lean_string_object l_Lean_Lsp_instToStringPosition___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_Lean_Lsp_instToStringPosition___lam__0___closed__1 = (const lean_object*)&l_Lean_Lsp_instToStringPosition___lam__0___closed__1_value;
static const lean_string_object l_Lean_Lsp_instToStringPosition___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Lean_Lsp_instToStringPosition___lam__0___closed__2 = (const lean_object*)&l_Lean_Lsp_instToStringPosition___lam__0___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToStringPosition___lam__0(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToStringPosition___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToStringPosition___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToStringPosition___closed__0 = (const lean_object*)&l_Lean_Lsp_instToStringPosition___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToStringPosition = (const lean_object*)&l_Lean_Lsp_instToStringPosition___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instLTPosition;
LEAN_EXPORT lean_object* l_Lean_Lsp_instLEPosition;
static const lean_ctor_object l_Lean_Lsp_instInhabitedRange_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Lsp_instInhabitedPosition_default___closed__0_value),((lean_object*)&l_Lean_Lsp_instInhabitedPosition_default___closed__0_value)}};
static const lean_object* l_Lean_Lsp_instInhabitedRange_default___closed__0 = (const lean_object*)&l_Lean_Lsp_instInhabitedRange_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instInhabitedRange_default = (const lean_object*)&l_Lean_Lsp_instInhabitedRange_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instInhabitedRange = (const lean_object*)&l_Lean_Lsp_instInhabitedRange_default___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Lsp_instBEqRange_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqRange_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_instBEqRange___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instBEqRange_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instBEqRange___closed__0 = (const lean_object*)&l_Lean_Lsp_instBEqRange___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instBEqRange = (const lean_object*)&l_Lean_Lsp_instBEqRange___closed__0_value;
LEAN_EXPORT uint64_t l_Lean_Lsp_instHashableRange_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instHashableRange_hash___boxed(lean_object*);
static const lean_closure_object l_Lean_Lsp_instHashableRange___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instHashableRange_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instHashableRange___closed__0 = (const lean_object*)&l_Lean_Lsp_instHashableRange___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instHashableRange = (const lean_object*)&l_Lean_Lsp_instHashableRange___closed__0_value;
static const lean_string_object l_Lean_Lsp_instToJsonRange_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "start"};
static const lean_object* l_Lean_Lsp_instToJsonRange_toJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonRange_toJson___closed__0_value;
static const lean_string_object l_Lean_Lsp_instToJsonRange_toJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "end"};
static const lean_object* l_Lean_Lsp_instToJsonRange_toJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instToJsonRange_toJson___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRange_toJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonRange___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonRange_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonRange___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonRange___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonRange = (const lean_object*)&l_Lean_Lsp_instToJsonRange___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRange_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRange_fromJson_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instFromJsonRange_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Range"};
static const lean_object* l_Lean_Lsp_instFromJsonRange_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonRange_fromJson___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonRange_fromJson___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonPosition_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonRange_fromJson___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonRange_fromJson___closed__1_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonPosition_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonRange_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonRange_fromJson___closed__1_value_aux_1),((lean_object*)&l_Lean_Lsp_instFromJsonRange_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(168, 149, 93, 6, 17, 68, 21, 203)}};
static const lean_object* l_Lean_Lsp_instFromJsonRange_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonRange_fromJson___closed__1_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonRange_fromJson___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonRange_fromJson___closed__2;
static lean_once_cell_t l_Lean_Lsp_instFromJsonRange_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonRange_fromJson___closed__3;
static const lean_ctor_object l_Lean_Lsp_instFromJsonRange_fromJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instToJsonRange_toJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(169, 129, 58, 248, 205, 160, 234, 176)}};
static const lean_object* l_Lean_Lsp_instFromJsonRange_fromJson___closed__4 = (const lean_object*)&l_Lean_Lsp_instFromJsonRange_fromJson___closed__4_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonRange_fromJson___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonRange_fromJson___closed__5;
static lean_once_cell_t l_Lean_Lsp_instFromJsonRange_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonRange_fromJson___closed__6;
static lean_once_cell_t l_Lean_Lsp_instFromJsonRange_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonRange_fromJson___closed__7;
static const lean_ctor_object l_Lean_Lsp_instFromJsonRange_fromJson___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instToJsonRange_toJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(199, 114, 144, 235, 25, 156, 115, 98)}};
static const lean_object* l_Lean_Lsp_instFromJsonRange_fromJson___closed__8 = (const lean_object*)&l_Lean_Lsp_instFromJsonRange_fromJson___closed__8_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonRange_fromJson___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonRange_fromJson___closed__9;
static lean_once_cell_t l_Lean_Lsp_instFromJsonRange_fromJson___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonRange_fromJson___closed__10;
static lean_once_cell_t l_Lean_Lsp_instFromJsonRange_fromJson___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonRange_fromJson___closed__11;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonRange_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonRange___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonRange_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonRange___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonRange___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonRange = (const lean_object*)&l_Lean_Lsp_instFromJsonRange___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Lsp_instOrdRange_ord(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instOrdRange_ord___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_instOrdRange___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instOrdRange_ord___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instOrdRange___closed__0 = (const lean_object*)&l_Lean_Lsp_instOrdRange___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instOrdRange = (const lean_object*)&l_Lean_Lsp_instOrdRange___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_instReprRange_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Lsp_instToJsonRange_toJson___closed__0_value)}};
static const lean_object* l_Lean_Lsp_instReprRange_repr___redArg___closed__0 = (const lean_object*)&l_Lean_Lsp_instReprRange_repr___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_instReprRange_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instReprRange_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_Lsp_instReprRange_repr___redArg___closed__1 = (const lean_object*)&l_Lean_Lsp_instReprRange_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Lsp_instReprRange_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Lsp_instReprRange_repr___redArg___closed__1_value),((lean_object*)&l_Lean_Lsp_instReprPosition_repr___redArg___closed__4_value)}};
static const lean_object* l_Lean_Lsp_instReprRange_repr___redArg___closed__2 = (const lean_object*)&l_Lean_Lsp_instReprRange_repr___redArg___closed__2_value;
static lean_once_cell_t l_Lean_Lsp_instReprRange_repr___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instReprRange_repr___redArg___closed__3;
static const lean_ctor_object l_Lean_Lsp_instReprRange_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Lsp_instToJsonRange_toJson___closed__1_value)}};
static const lean_object* l_Lean_Lsp_instReprRange_repr___redArg___closed__4 = (const lean_object*)&l_Lean_Lsp_instReprRange_repr___redArg___closed__4_value;
static lean_once_cell_t l_Lean_Lsp_instReprRange_repr___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instReprRange_repr___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_Lsp_instReprRange_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instReprRange_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instReprRange_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_instReprRange___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instReprRange_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instReprRange___closed__0 = (const lean_object*)&l_Lean_Lsp_instReprRange___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instReprRange = (const lean_object*)&l_Lean_Lsp_instReprRange___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instLTRange;
LEAN_EXPORT lean_object* l_Lean_Lsp_instLERange;
LEAN_EXPORT uint8_t l_Lean_Lsp_instBEqPosition_beq(lean_object* v_x_5_, lean_object* v_x_6_){
_start:
{
lean_object* v_line_7_; lean_object* v_character_8_; lean_object* v_line_9_; lean_object* v_character_10_; uint8_t v___x_11_; 
v_line_7_ = lean_ctor_get(v_x_5_, 0);
v_character_8_ = lean_ctor_get(v_x_5_, 1);
v_line_9_ = lean_ctor_get(v_x_6_, 0);
v_character_10_ = lean_ctor_get(v_x_6_, 1);
v___x_11_ = lean_nat_dec_eq(v_line_7_, v_line_9_);
if (v___x_11_ == 0)
{
return v___x_11_;
}
else
{
uint8_t v___x_12_; 
v___x_12_ = lean_nat_dec_eq(v_character_8_, v_character_10_);
return v___x_12_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqPosition_beq___boxed(lean_object* v_x_13_, lean_object* v_x_14_){
_start:
{
uint8_t v_res_15_; lean_object* v_r_16_; 
v_res_15_ = l_Lean_Lsp_instBEqPosition_beq(v_x_13_, v_x_14_);
lean_dec_ref(v_x_14_);
lean_dec_ref(v_x_13_);
v_r_16_ = lean_box(v_res_15_);
return v_r_16_;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_instOrdPosition_ord(lean_object* v_x_19_, lean_object* v_x_20_){
_start:
{
lean_object* v_line_21_; lean_object* v_character_22_; lean_object* v_line_23_; lean_object* v_character_24_; uint8_t v___x_25_; 
v_line_21_ = lean_ctor_get(v_x_19_, 0);
v_character_22_ = lean_ctor_get(v_x_19_, 1);
v_line_23_ = lean_ctor_get(v_x_20_, 0);
v_character_24_ = lean_ctor_get(v_x_20_, 1);
v___x_25_ = lean_nat_dec_lt(v_line_21_, v_line_23_);
if (v___x_25_ == 0)
{
uint8_t v___x_26_; 
v___x_26_ = lean_nat_dec_eq(v_line_21_, v_line_23_);
if (v___x_26_ == 0)
{
uint8_t v___x_27_; 
v___x_27_ = 2;
return v___x_27_;
}
else
{
uint8_t v___x_28_; 
v___x_28_ = lean_nat_dec_lt(v_character_22_, v_character_24_);
if (v___x_28_ == 0)
{
uint8_t v___x_29_; 
v___x_29_ = lean_nat_dec_eq(v_character_22_, v_character_24_);
if (v___x_29_ == 0)
{
uint8_t v___x_30_; 
v___x_30_ = 2;
return v___x_30_;
}
else
{
uint8_t v___x_31_; 
v___x_31_ = 1;
return v___x_31_;
}
}
else
{
uint8_t v___x_32_; 
v___x_32_ = 0;
return v___x_32_;
}
}
}
else
{
uint8_t v___x_33_; 
v___x_33_ = 0;
return v___x_33_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instOrdPosition_ord___boxed(lean_object* v_x_34_, lean_object* v_x_35_){
_start:
{
uint8_t v_res_36_; lean_object* v_r_37_; 
v_res_36_ = l_Lean_Lsp_instOrdPosition_ord(v_x_34_, v_x_35_);
lean_dec_ref(v_x_35_);
lean_dec_ref(v_x_34_);
v_r_37_ = lean_box(v_res_36_);
return v_r_37_;
}
}
LEAN_EXPORT uint64_t l_Lean_Lsp_instHashablePosition_hash(lean_object* v_x_40_){
_start:
{
lean_object* v_line_41_; lean_object* v_character_42_; uint64_t v___x_43_; uint64_t v___x_44_; uint64_t v___x_45_; uint64_t v___x_46_; uint64_t v___x_47_; 
v_line_41_ = lean_ctor_get(v_x_40_, 0);
v_character_42_ = lean_ctor_get(v_x_40_, 1);
v___x_43_ = 0ULL;
v___x_44_ = lean_uint64_of_nat(v_line_41_);
v___x_45_ = lean_uint64_mix_hash(v___x_43_, v___x_44_);
v___x_46_ = lean_uint64_of_nat(v_character_42_);
v___x_47_ = lean_uint64_mix_hash(v___x_45_, v___x_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instHashablePosition_hash___boxed(lean_object* v_x_48_){
_start:
{
uint64_t v_res_49_; lean_object* v_r_50_; 
v_res_49_ = l_Lean_Lsp_instHashablePosition_hash(v_x_48_);
lean_dec_ref(v_x_48_);
v_r_50_ = lean_box_uint64(v_res_49_);
return v_r_50_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonPosition_toJson_spec__0(lean_object* v_a_53_, lean_object* v_a_54_){
_start:
{
if (lean_obj_tag(v_a_53_) == 0)
{
lean_object* v___x_55_; 
v___x_55_ = lean_array_to_list(v_a_54_);
return v___x_55_;
}
else
{
lean_object* v_head_56_; lean_object* v_tail_57_; lean_object* v___x_58_; 
v_head_56_ = lean_ctor_get(v_a_53_, 0);
lean_inc(v_head_56_);
v_tail_57_ = lean_ctor_get(v_a_53_, 1);
lean_inc(v_tail_57_);
lean_dec_ref(v_a_53_);
v___x_58_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_54_, v_head_56_);
v_a_53_ = v_tail_57_;
v_a_54_ = v___x_58_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonPosition_toJson(lean_object* v_x_64_){
_start:
{
lean_object* v_line_65_; lean_object* v_character_66_; lean_object* v___x_68_; uint8_t v_isShared_69_; uint8_t v_isSharedCheck_88_; 
v_line_65_ = lean_ctor_get(v_x_64_, 0);
v_character_66_ = lean_ctor_get(v_x_64_, 1);
v_isSharedCheck_88_ = !lean_is_exclusive(v_x_64_);
if (v_isSharedCheck_88_ == 0)
{
v___x_68_ = v_x_64_;
v_isShared_69_ = v_isSharedCheck_88_;
goto v_resetjp_67_;
}
else
{
lean_inc(v_character_66_);
lean_inc(v_line_65_);
lean_dec(v_x_64_);
v___x_68_ = lean_box(0);
v_isShared_69_ = v_isSharedCheck_88_;
goto v_resetjp_67_;
}
v_resetjp_67_:
{
lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_74_; 
v___x_70_ = ((lean_object*)(l_Lean_Lsp_instToJsonPosition_toJson___closed__0));
v___x_71_ = l_Lean_JsonNumber_fromNat(v_line_65_);
v___x_72_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_72_, 0, v___x_71_);
if (v_isShared_69_ == 0)
{
lean_ctor_set(v___x_68_, 1, v___x_72_);
lean_ctor_set(v___x_68_, 0, v___x_70_);
v___x_74_ = v___x_68_;
goto v_reusejp_73_;
}
else
{
lean_object* v_reuseFailAlloc_87_; 
v_reuseFailAlloc_87_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_87_, 0, v___x_70_);
lean_ctor_set(v_reuseFailAlloc_87_, 1, v___x_72_);
v___x_74_ = v_reuseFailAlloc_87_;
goto v_reusejp_73_;
}
v_reusejp_73_:
{
lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_75_ = lean_box(0);
v___x_76_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_76_, 0, v___x_74_);
lean_ctor_set(v___x_76_, 1, v___x_75_);
v___x_77_ = ((lean_object*)(l_Lean_Lsp_instToJsonPosition_toJson___closed__1));
v___x_78_ = l_Lean_JsonNumber_fromNat(v_character_66_);
v___x_79_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_79_, 0, v___x_78_);
v___x_80_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_80_, 0, v___x_77_);
lean_ctor_set(v___x_80_, 1, v___x_79_);
v___x_81_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_81_, 0, v___x_80_);
lean_ctor_set(v___x_81_, 1, v___x_75_);
v___x_82_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_82_, 0, v___x_81_);
lean_ctor_set(v___x_82_, 1, v___x_75_);
v___x_83_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_83_, 0, v___x_76_);
lean_ctor_set(v___x_83_, 1, v___x_82_);
v___x_84_ = ((lean_object*)(l_Lean_Lsp_instToJsonPosition_toJson___closed__2));
v___x_85_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonPosition_toJson_spec__0(v___x_83_, v___x_84_);
v___x_86_ = l_Lean_Json_mkObj(v___x_85_);
return v___x_86_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPosition_fromJson_spec__0(lean_object* v_j_91_, lean_object* v_k_92_){
_start:
{
lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_93_ = l_Lean_Json_getObjValD(v_j_91_, v_k_92_);
v___x_94_ = l_Lean_Json_getNat_x3f(v___x_93_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPosition_fromJson_spec__0___boxed(lean_object* v_j_95_, lean_object* v_k_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPosition_fromJson_spec__0(v_j_95_, v_k_96_);
lean_dec_ref(v_k_96_);
return v_res_97_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPosition_fromJson___closed__4(void){
_start:
{
uint8_t v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_105_ = 1;
v___x_106_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPosition_fromJson___closed__3));
v___x_107_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_106_, v___x_105_);
return v___x_107_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPosition_fromJson___closed__6(void){
_start:
{
lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_109_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPosition_fromJson___closed__5));
v___x_110_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPosition_fromJson___closed__4, &l_Lean_Lsp_instFromJsonPosition_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonPosition_fromJson___closed__4);
v___x_111_ = lean_string_append(v___x_110_, v___x_109_);
return v___x_111_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPosition_fromJson___closed__8(void){
_start:
{
uint8_t v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_114_ = 1;
v___x_115_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPosition_fromJson___closed__7));
v___x_116_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_115_, v___x_114_);
return v___x_116_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPosition_fromJson___closed__9(void){
_start:
{
lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_117_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPosition_fromJson___closed__8, &l_Lean_Lsp_instFromJsonPosition_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonPosition_fromJson___closed__8);
v___x_118_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPosition_fromJson___closed__6, &l_Lean_Lsp_instFromJsonPosition_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonPosition_fromJson___closed__6);
v___x_119_ = lean_string_append(v___x_118_, v___x_117_);
return v___x_119_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPosition_fromJson___closed__11(void){
_start:
{
lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_121_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPosition_fromJson___closed__10));
v___x_122_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPosition_fromJson___closed__9, &l_Lean_Lsp_instFromJsonPosition_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonPosition_fromJson___closed__9);
v___x_123_ = lean_string_append(v___x_122_, v___x_121_);
return v___x_123_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPosition_fromJson___closed__13(void){
_start:
{
uint8_t v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_126_ = 1;
v___x_127_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPosition_fromJson___closed__12));
v___x_128_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_127_, v___x_126_);
return v___x_128_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPosition_fromJson___closed__14(void){
_start:
{
lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_129_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPosition_fromJson___closed__13, &l_Lean_Lsp_instFromJsonPosition_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonPosition_fromJson___closed__13);
v___x_130_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPosition_fromJson___closed__6, &l_Lean_Lsp_instFromJsonPosition_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonPosition_fromJson___closed__6);
v___x_131_ = lean_string_append(v___x_130_, v___x_129_);
return v___x_131_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPosition_fromJson___closed__15(void){
_start:
{
lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; 
v___x_132_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPosition_fromJson___closed__10));
v___x_133_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPosition_fromJson___closed__14, &l_Lean_Lsp_instFromJsonPosition_fromJson___closed__14_once, _init_l_Lean_Lsp_instFromJsonPosition_fromJson___closed__14);
v___x_134_ = lean_string_append(v___x_133_, v___x_132_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonPosition_fromJson(lean_object* v_json_135_){
_start:
{
lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_136_ = ((lean_object*)(l_Lean_Lsp_instToJsonPosition_toJson___closed__0));
lean_inc(v_json_135_);
v___x_137_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPosition_fromJson_spec__0(v_json_135_, v___x_136_);
if (lean_obj_tag(v___x_137_) == 0)
{
lean_object* v_a_138_; lean_object* v___x_140_; uint8_t v_isShared_141_; uint8_t v_isSharedCheck_147_; 
lean_dec(v_json_135_);
v_a_138_ = lean_ctor_get(v___x_137_, 0);
v_isSharedCheck_147_ = !lean_is_exclusive(v___x_137_);
if (v_isSharedCheck_147_ == 0)
{
v___x_140_ = v___x_137_;
v_isShared_141_ = v_isSharedCheck_147_;
goto v_resetjp_139_;
}
else
{
lean_inc(v_a_138_);
lean_dec(v___x_137_);
v___x_140_ = lean_box(0);
v_isShared_141_ = v_isSharedCheck_147_;
goto v_resetjp_139_;
}
v_resetjp_139_:
{
lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_145_; 
v___x_142_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPosition_fromJson___closed__11, &l_Lean_Lsp_instFromJsonPosition_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonPosition_fromJson___closed__11);
v___x_143_ = lean_string_append(v___x_142_, v_a_138_);
lean_dec(v_a_138_);
if (v_isShared_141_ == 0)
{
lean_ctor_set(v___x_140_, 0, v___x_143_);
v___x_145_ = v___x_140_;
goto v_reusejp_144_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v___x_143_);
v___x_145_ = v_reuseFailAlloc_146_;
goto v_reusejp_144_;
}
v_reusejp_144_:
{
return v___x_145_;
}
}
}
else
{
if (lean_obj_tag(v___x_137_) == 0)
{
lean_object* v_a_148_; lean_object* v___x_150_; uint8_t v_isShared_151_; uint8_t v_isSharedCheck_155_; 
lean_dec(v_json_135_);
v_a_148_ = lean_ctor_get(v___x_137_, 0);
v_isSharedCheck_155_ = !lean_is_exclusive(v___x_137_);
if (v_isSharedCheck_155_ == 0)
{
v___x_150_ = v___x_137_;
v_isShared_151_ = v_isSharedCheck_155_;
goto v_resetjp_149_;
}
else
{
lean_inc(v_a_148_);
lean_dec(v___x_137_);
v___x_150_ = lean_box(0);
v_isShared_151_ = v_isSharedCheck_155_;
goto v_resetjp_149_;
}
v_resetjp_149_:
{
lean_object* v___x_153_; 
if (v_isShared_151_ == 0)
{
lean_ctor_set_tag(v___x_150_, 0);
v___x_153_ = v___x_150_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v_a_148_);
v___x_153_ = v_reuseFailAlloc_154_;
goto v_reusejp_152_;
}
v_reusejp_152_:
{
return v___x_153_;
}
}
}
else
{
lean_object* v_a_156_; lean_object* v___x_157_; lean_object* v___x_158_; 
v_a_156_ = lean_ctor_get(v___x_137_, 0);
lean_inc(v_a_156_);
lean_dec_ref(v___x_137_);
v___x_157_ = ((lean_object*)(l_Lean_Lsp_instToJsonPosition_toJson___closed__1));
v___x_158_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPosition_fromJson_spec__0(v_json_135_, v___x_157_);
if (lean_obj_tag(v___x_158_) == 0)
{
lean_object* v_a_159_; lean_object* v___x_161_; uint8_t v_isShared_162_; uint8_t v_isSharedCheck_168_; 
lean_dec(v_a_156_);
v_a_159_ = lean_ctor_get(v___x_158_, 0);
v_isSharedCheck_168_ = !lean_is_exclusive(v___x_158_);
if (v_isSharedCheck_168_ == 0)
{
v___x_161_ = v___x_158_;
v_isShared_162_ = v_isSharedCheck_168_;
goto v_resetjp_160_;
}
else
{
lean_inc(v_a_159_);
lean_dec(v___x_158_);
v___x_161_ = lean_box(0);
v_isShared_162_ = v_isSharedCheck_168_;
goto v_resetjp_160_;
}
v_resetjp_160_:
{
lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_166_; 
v___x_163_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPosition_fromJson___closed__15, &l_Lean_Lsp_instFromJsonPosition_fromJson___closed__15_once, _init_l_Lean_Lsp_instFromJsonPosition_fromJson___closed__15);
v___x_164_ = lean_string_append(v___x_163_, v_a_159_);
lean_dec(v_a_159_);
if (v_isShared_162_ == 0)
{
lean_ctor_set(v___x_161_, 0, v___x_164_);
v___x_166_ = v___x_161_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_167_; 
v_reuseFailAlloc_167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_167_, 0, v___x_164_);
v___x_166_ = v_reuseFailAlloc_167_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
return v___x_166_;
}
}
}
else
{
if (lean_obj_tag(v___x_158_) == 0)
{
lean_object* v_a_169_; lean_object* v___x_171_; uint8_t v_isShared_172_; uint8_t v_isSharedCheck_176_; 
lean_dec(v_a_156_);
v_a_169_ = lean_ctor_get(v___x_158_, 0);
v_isSharedCheck_176_ = !lean_is_exclusive(v___x_158_);
if (v_isSharedCheck_176_ == 0)
{
v___x_171_ = v___x_158_;
v_isShared_172_ = v_isSharedCheck_176_;
goto v_resetjp_170_;
}
else
{
lean_inc(v_a_169_);
lean_dec(v___x_158_);
v___x_171_ = lean_box(0);
v_isShared_172_ = v_isSharedCheck_176_;
goto v_resetjp_170_;
}
v_resetjp_170_:
{
lean_object* v___x_174_; 
if (v_isShared_172_ == 0)
{
lean_ctor_set_tag(v___x_171_, 0);
v___x_174_ = v___x_171_;
goto v_reusejp_173_;
}
else
{
lean_object* v_reuseFailAlloc_175_; 
v_reuseFailAlloc_175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_175_, 0, v_a_169_);
v___x_174_ = v_reuseFailAlloc_175_;
goto v_reusejp_173_;
}
v_reusejp_173_:
{
return v___x_174_;
}
}
}
else
{
lean_object* v_a_177_; lean_object* v___x_179_; uint8_t v_isShared_180_; uint8_t v_isSharedCheck_185_; 
v_a_177_ = lean_ctor_get(v___x_158_, 0);
v_isSharedCheck_185_ = !lean_is_exclusive(v___x_158_);
if (v_isSharedCheck_185_ == 0)
{
v___x_179_ = v___x_158_;
v_isShared_180_ = v_isSharedCheck_185_;
goto v_resetjp_178_;
}
else
{
lean_inc(v_a_177_);
lean_dec(v___x_158_);
v___x_179_ = lean_box(0);
v_isShared_180_ = v_isSharedCheck_185_;
goto v_resetjp_178_;
}
v_resetjp_178_:
{
lean_object* v___x_181_; lean_object* v___x_183_; 
v___x_181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_181_, 0, v_a_156_);
lean_ctor_set(v___x_181_, 1, v_a_177_);
if (v_isShared_180_ == 0)
{
lean_ctor_set(v___x_179_, 0, v___x_181_);
v___x_183_ = v___x_179_;
goto v_reusejp_182_;
}
else
{
lean_object* v_reuseFailAlloc_184_; 
v_reuseFailAlloc_184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_184_, 0, v___x_181_);
v___x_183_ = v_reuseFailAlloc_184_;
goto v_reusejp_182_;
}
v_reusejp_182_:
{
return v___x_183_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Lsp_instReprPosition_repr_spec__0(lean_object* v_a_188_){
_start:
{
lean_object* v___x_189_; 
v___x_189_ = lean_nat_to_int(v_a_188_);
return v___x_189_;
}
}
static lean_object* _init_l_Lean_Lsp_instReprPosition_repr___redArg___closed__6(void){
_start:
{
lean_object* v___x_202_; lean_object* v___x_203_; 
v___x_202_ = lean_unsigned_to_nat(8u);
v___x_203_ = lean_nat_to_int(v___x_202_);
return v___x_203_;
}
}
static lean_object* _init_l_Lean_Lsp_instReprPosition_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_209_ = lean_unsigned_to_nat(13u);
v___x_210_ = lean_nat_to_int(v___x_209_);
return v___x_210_;
}
}
static lean_object* _init_l_Lean_Lsp_instReprPosition_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_212_; lean_object* v___x_213_; 
v___x_212_ = ((lean_object*)(l_Lean_Lsp_instReprPosition_repr___redArg___closed__0));
v___x_213_ = lean_string_length(v___x_212_);
return v___x_213_;
}
}
static lean_object* _init_l_Lean_Lsp_instReprPosition_repr___redArg___closed__13(void){
_start:
{
lean_object* v___x_214_; lean_object* v___x_215_; 
v___x_214_ = lean_obj_once(&l_Lean_Lsp_instReprPosition_repr___redArg___closed__12, &l_Lean_Lsp_instReprPosition_repr___redArg___closed__12_once, _init_l_Lean_Lsp_instReprPosition_repr___redArg___closed__12);
v___x_215_ = lean_nat_to_int(v___x_214_);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instReprPosition_repr___redArg(lean_object* v_x_220_){
_start:
{
lean_object* v_line_221_; lean_object* v_character_222_; lean_object* v___x_224_; uint8_t v_isShared_225_; uint8_t v_isSharedCheck_257_; 
v_line_221_ = lean_ctor_get(v_x_220_, 0);
v_character_222_ = lean_ctor_get(v_x_220_, 1);
v_isSharedCheck_257_ = !lean_is_exclusive(v_x_220_);
if (v_isSharedCheck_257_ == 0)
{
v___x_224_ = v_x_220_;
v_isShared_225_ = v_isSharedCheck_257_;
goto v_resetjp_223_;
}
else
{
lean_inc(v_character_222_);
lean_inc(v_line_221_);
lean_dec(v_x_220_);
v___x_224_ = lean_box(0);
v_isShared_225_ = v_isSharedCheck_257_;
goto v_resetjp_223_;
}
v_resetjp_223_:
{
lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_232_; 
v___x_226_ = ((lean_object*)(l_Lean_Lsp_instReprPosition_repr___redArg___closed__4));
v___x_227_ = ((lean_object*)(l_Lean_Lsp_instReprPosition_repr___redArg___closed__5));
v___x_228_ = lean_obj_once(&l_Lean_Lsp_instReprPosition_repr___redArg___closed__6, &l_Lean_Lsp_instReprPosition_repr___redArg___closed__6_once, _init_l_Lean_Lsp_instReprPosition_repr___redArg___closed__6);
v___x_229_ = l_Nat_reprFast(v_line_221_);
v___x_230_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_230_, 0, v___x_229_);
if (v_isShared_225_ == 0)
{
lean_ctor_set_tag(v___x_224_, 4);
lean_ctor_set(v___x_224_, 1, v___x_230_);
lean_ctor_set(v___x_224_, 0, v___x_228_);
v___x_232_ = v___x_224_;
goto v_reusejp_231_;
}
else
{
lean_object* v_reuseFailAlloc_256_; 
v_reuseFailAlloc_256_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_256_, 0, v___x_228_);
lean_ctor_set(v_reuseFailAlloc_256_, 1, v___x_230_);
v___x_232_ = v_reuseFailAlloc_256_;
goto v_reusejp_231_;
}
v_reusejp_231_:
{
uint8_t v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_233_ = 0;
v___x_234_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_234_, 0, v___x_232_);
lean_ctor_set_uint8(v___x_234_, sizeof(void*)*1, v___x_233_);
v___x_235_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_235_, 0, v___x_227_);
lean_ctor_set(v___x_235_, 1, v___x_234_);
v___x_236_ = ((lean_object*)(l_Lean_Lsp_instReprPosition_repr___redArg___closed__8));
v___x_237_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_237_, 0, v___x_235_);
lean_ctor_set(v___x_237_, 1, v___x_236_);
v___x_238_ = lean_box(1);
v___x_239_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_239_, 0, v___x_237_);
lean_ctor_set(v___x_239_, 1, v___x_238_);
v___x_240_ = ((lean_object*)(l_Lean_Lsp_instReprPosition_repr___redArg___closed__9));
v___x_241_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_241_, 0, v___x_239_);
lean_ctor_set(v___x_241_, 1, v___x_240_);
v___x_242_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_242_, 0, v___x_241_);
lean_ctor_set(v___x_242_, 1, v___x_226_);
v___x_243_ = lean_obj_once(&l_Lean_Lsp_instReprPosition_repr___redArg___closed__10, &l_Lean_Lsp_instReprPosition_repr___redArg___closed__10_once, _init_l_Lean_Lsp_instReprPosition_repr___redArg___closed__10);
v___x_244_ = l_Nat_reprFast(v_character_222_);
v___x_245_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_245_, 0, v___x_244_);
v___x_246_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_246_, 0, v___x_243_);
lean_ctor_set(v___x_246_, 1, v___x_245_);
v___x_247_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_247_, 0, v___x_246_);
lean_ctor_set_uint8(v___x_247_, sizeof(void*)*1, v___x_233_);
v___x_248_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_248_, 0, v___x_242_);
lean_ctor_set(v___x_248_, 1, v___x_247_);
v___x_249_ = lean_obj_once(&l_Lean_Lsp_instReprPosition_repr___redArg___closed__13, &l_Lean_Lsp_instReprPosition_repr___redArg___closed__13_once, _init_l_Lean_Lsp_instReprPosition_repr___redArg___closed__13);
v___x_250_ = ((lean_object*)(l_Lean_Lsp_instReprPosition_repr___redArg___closed__14));
v___x_251_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_251_, 0, v___x_250_);
lean_ctor_set(v___x_251_, 1, v___x_248_);
v___x_252_ = ((lean_object*)(l_Lean_Lsp_instReprPosition_repr___redArg___closed__15));
v___x_253_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_253_, 0, v___x_251_);
lean_ctor_set(v___x_253_, 1, v___x_252_);
v___x_254_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_254_, 0, v___x_249_);
lean_ctor_set(v___x_254_, 1, v___x_253_);
v___x_255_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_255_, 0, v___x_254_);
lean_ctor_set_uint8(v___x_255_, sizeof(void*)*1, v___x_233_);
return v___x_255_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instReprPosition_repr(lean_object* v_x_258_, lean_object* v_prec_259_){
_start:
{
lean_object* v___x_260_; 
v___x_260_ = l_Lean_Lsp_instReprPosition_repr___redArg(v_x_258_);
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instReprPosition_repr___boxed(lean_object* v_x_261_, lean_object* v_prec_262_){
_start:
{
lean_object* v_res_263_; 
v_res_263_ = l_Lean_Lsp_instReprPosition_repr(v_x_261_, v_prec_262_);
lean_dec(v_prec_262_);
return v_res_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToStringPosition___lam__0(lean_object* v_p_269_){
_start:
{
lean_object* v_line_270_; lean_object* v_character_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; 
v_line_270_ = lean_ctor_get(v_p_269_, 0);
lean_inc(v_line_270_);
v_character_271_ = lean_ctor_get(v_p_269_, 1);
lean_inc(v_character_271_);
lean_dec_ref(v_p_269_);
v___x_272_ = ((lean_object*)(l_Lean_Lsp_instToStringPosition___lam__0___closed__0));
v___x_273_ = l_Nat_reprFast(v_line_270_);
v___x_274_ = lean_string_append(v___x_272_, v___x_273_);
lean_dec_ref(v___x_273_);
v___x_275_ = ((lean_object*)(l_Lean_Lsp_instToStringPosition___lam__0___closed__1));
v___x_276_ = lean_string_append(v___x_274_, v___x_275_);
v___x_277_ = l_Nat_reprFast(v_character_271_);
v___x_278_ = lean_string_append(v___x_276_, v___x_277_);
lean_dec_ref(v___x_277_);
v___x_279_ = ((lean_object*)(l_Lean_Lsp_instToStringPosition___lam__0___closed__2));
v___x_280_ = lean_string_append(v___x_278_, v___x_279_);
return v___x_280_;
}
}
static lean_object* _init_l_Lean_Lsp_instLTPosition(void){
_start:
{
lean_object* v___x_283_; 
v___x_283_ = lean_box(0);
return v___x_283_;
}
}
static lean_object* _init_l_Lean_Lsp_instLEPosition(void){
_start:
{
lean_object* v___x_284_; 
v___x_284_ = lean_box(0);
return v___x_284_;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_instBEqRange_beq(lean_object* v_x_289_, lean_object* v_x_290_){
_start:
{
lean_object* v_start_291_; lean_object* v_end_292_; lean_object* v_start_293_; lean_object* v_end_294_; uint8_t v___x_295_; 
v_start_291_ = lean_ctor_get(v_x_289_, 0);
v_end_292_ = lean_ctor_get(v_x_289_, 1);
v_start_293_ = lean_ctor_get(v_x_290_, 0);
v_end_294_ = lean_ctor_get(v_x_290_, 1);
v___x_295_ = l_Lean_Lsp_instBEqPosition_beq(v_start_291_, v_start_293_);
if (v___x_295_ == 0)
{
return v___x_295_;
}
else
{
uint8_t v___x_296_; 
v___x_296_ = l_Lean_Lsp_instBEqPosition_beq(v_end_292_, v_end_294_);
return v___x_296_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqRange_beq___boxed(lean_object* v_x_297_, lean_object* v_x_298_){
_start:
{
uint8_t v_res_299_; lean_object* v_r_300_; 
v_res_299_ = l_Lean_Lsp_instBEqRange_beq(v_x_297_, v_x_298_);
lean_dec_ref(v_x_298_);
lean_dec_ref(v_x_297_);
v_r_300_ = lean_box(v_res_299_);
return v_r_300_;
}
}
LEAN_EXPORT uint64_t l_Lean_Lsp_instHashableRange_hash(lean_object* v_x_303_){
_start:
{
lean_object* v_start_304_; lean_object* v_end_305_; uint64_t v___x_306_; uint64_t v___x_307_; uint64_t v___x_308_; uint64_t v___x_309_; uint64_t v___x_310_; 
v_start_304_ = lean_ctor_get(v_x_303_, 0);
v_end_305_ = lean_ctor_get(v_x_303_, 1);
v___x_306_ = 0ULL;
v___x_307_ = l_Lean_Lsp_instHashablePosition_hash(v_start_304_);
v___x_308_ = lean_uint64_mix_hash(v___x_306_, v___x_307_);
v___x_309_ = l_Lean_Lsp_instHashablePosition_hash(v_end_305_);
v___x_310_ = lean_uint64_mix_hash(v___x_308_, v___x_309_);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instHashableRange_hash___boxed(lean_object* v_x_311_){
_start:
{
uint64_t v_res_312_; lean_object* v_r_313_; 
v_res_312_ = l_Lean_Lsp_instHashableRange_hash(v_x_311_);
lean_dec_ref(v_x_311_);
v_r_313_ = lean_box_uint64(v_res_312_);
return v_r_313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRange_toJson(lean_object* v_x_318_){
_start:
{
lean_object* v_start_319_; lean_object* v_end_320_; lean_object* v___x_322_; uint8_t v_isShared_323_; uint8_t v_isSharedCheck_340_; 
v_start_319_ = lean_ctor_get(v_x_318_, 0);
v_end_320_ = lean_ctor_get(v_x_318_, 1);
v_isSharedCheck_340_ = !lean_is_exclusive(v_x_318_);
if (v_isSharedCheck_340_ == 0)
{
v___x_322_ = v_x_318_;
v_isShared_323_ = v_isSharedCheck_340_;
goto v_resetjp_321_;
}
else
{
lean_inc(v_end_320_);
lean_inc(v_start_319_);
lean_dec(v_x_318_);
v___x_322_ = lean_box(0);
v_isShared_323_ = v_isSharedCheck_340_;
goto v_resetjp_321_;
}
v_resetjp_321_:
{
lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_327_; 
v___x_324_ = ((lean_object*)(l_Lean_Lsp_instToJsonRange_toJson___closed__0));
v___x_325_ = l_Lean_Lsp_instToJsonPosition_toJson(v_start_319_);
if (v_isShared_323_ == 0)
{
lean_ctor_set(v___x_322_, 1, v___x_325_);
lean_ctor_set(v___x_322_, 0, v___x_324_);
v___x_327_ = v___x_322_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v___x_324_);
lean_ctor_set(v_reuseFailAlloc_339_, 1, v___x_325_);
v___x_327_ = v_reuseFailAlloc_339_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_328_ = lean_box(0);
v___x_329_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_329_, 0, v___x_327_);
lean_ctor_set(v___x_329_, 1, v___x_328_);
v___x_330_ = ((lean_object*)(l_Lean_Lsp_instToJsonRange_toJson___closed__1));
v___x_331_ = l_Lean_Lsp_instToJsonPosition_toJson(v_end_320_);
v___x_332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_332_, 0, v___x_330_);
lean_ctor_set(v___x_332_, 1, v___x_331_);
v___x_333_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_333_, 0, v___x_332_);
lean_ctor_set(v___x_333_, 1, v___x_328_);
v___x_334_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_334_, 0, v___x_333_);
lean_ctor_set(v___x_334_, 1, v___x_328_);
v___x_335_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_335_, 0, v___x_329_);
lean_ctor_set(v___x_335_, 1, v___x_334_);
v___x_336_ = ((lean_object*)(l_Lean_Lsp_instToJsonPosition_toJson___closed__2));
v___x_337_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonPosition_toJson_spec__0(v___x_335_, v___x_336_);
v___x_338_ = l_Lean_Json_mkObj(v___x_337_);
return v___x_338_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRange_fromJson_spec__0(lean_object* v_j_343_, lean_object* v_k_344_){
_start:
{
lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_345_ = l_Lean_Json_getObjValD(v_j_343_, v_k_344_);
v___x_346_ = l_Lean_Lsp_instFromJsonPosition_fromJson(v___x_345_);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRange_fromJson_spec__0___boxed(lean_object* v_j_347_, lean_object* v_k_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRange_fromJson_spec__0(v_j_347_, v_k_348_);
lean_dec_ref(v_k_348_);
return v_res_349_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRange_fromJson___closed__2(void){
_start:
{
uint8_t v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_355_ = 1;
v___x_356_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRange_fromJson___closed__1));
v___x_357_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_356_, v___x_355_);
return v___x_357_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRange_fromJson___closed__3(void){
_start:
{
lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_358_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPosition_fromJson___closed__5));
v___x_359_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRange_fromJson___closed__2, &l_Lean_Lsp_instFromJsonRange_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonRange_fromJson___closed__2);
v___x_360_ = lean_string_append(v___x_359_, v___x_358_);
return v___x_360_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRange_fromJson___closed__5(void){
_start:
{
uint8_t v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_363_ = 1;
v___x_364_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRange_fromJson___closed__4));
v___x_365_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_364_, v___x_363_);
return v___x_365_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRange_fromJson___closed__6(void){
_start:
{
lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_366_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRange_fromJson___closed__5, &l_Lean_Lsp_instFromJsonRange_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonRange_fromJson___closed__5);
v___x_367_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRange_fromJson___closed__3, &l_Lean_Lsp_instFromJsonRange_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonRange_fromJson___closed__3);
v___x_368_ = lean_string_append(v___x_367_, v___x_366_);
return v___x_368_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRange_fromJson___closed__7(void){
_start:
{
lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_369_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPosition_fromJson___closed__10));
v___x_370_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRange_fromJson___closed__6, &l_Lean_Lsp_instFromJsonRange_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonRange_fromJson___closed__6);
v___x_371_ = lean_string_append(v___x_370_, v___x_369_);
return v___x_371_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRange_fromJson___closed__9(void){
_start:
{
uint8_t v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_374_ = 1;
v___x_375_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRange_fromJson___closed__8));
v___x_376_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_375_, v___x_374_);
return v___x_376_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRange_fromJson___closed__10(void){
_start:
{
lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_377_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRange_fromJson___closed__9, &l_Lean_Lsp_instFromJsonRange_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonRange_fromJson___closed__9);
v___x_378_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRange_fromJson___closed__3, &l_Lean_Lsp_instFromJsonRange_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonRange_fromJson___closed__3);
v___x_379_ = lean_string_append(v___x_378_, v___x_377_);
return v___x_379_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRange_fromJson___closed__11(void){
_start:
{
lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_380_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPosition_fromJson___closed__10));
v___x_381_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRange_fromJson___closed__10, &l_Lean_Lsp_instFromJsonRange_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonRange_fromJson___closed__10);
v___x_382_ = lean_string_append(v___x_381_, v___x_380_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonRange_fromJson(lean_object* v_json_383_){
_start:
{
lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_384_ = ((lean_object*)(l_Lean_Lsp_instToJsonRange_toJson___closed__0));
lean_inc(v_json_383_);
v___x_385_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRange_fromJson_spec__0(v_json_383_, v___x_384_);
if (lean_obj_tag(v___x_385_) == 0)
{
lean_object* v_a_386_; lean_object* v___x_388_; uint8_t v_isShared_389_; uint8_t v_isSharedCheck_395_; 
lean_dec(v_json_383_);
v_a_386_ = lean_ctor_get(v___x_385_, 0);
v_isSharedCheck_395_ = !lean_is_exclusive(v___x_385_);
if (v_isSharedCheck_395_ == 0)
{
v___x_388_ = v___x_385_;
v_isShared_389_ = v_isSharedCheck_395_;
goto v_resetjp_387_;
}
else
{
lean_inc(v_a_386_);
lean_dec(v___x_385_);
v___x_388_ = lean_box(0);
v_isShared_389_ = v_isSharedCheck_395_;
goto v_resetjp_387_;
}
v_resetjp_387_:
{
lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_393_; 
v___x_390_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRange_fromJson___closed__7, &l_Lean_Lsp_instFromJsonRange_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonRange_fromJson___closed__7);
v___x_391_ = lean_string_append(v___x_390_, v_a_386_);
lean_dec(v_a_386_);
if (v_isShared_389_ == 0)
{
lean_ctor_set(v___x_388_, 0, v___x_391_);
v___x_393_ = v___x_388_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(0, 1, 0);
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
else
{
if (lean_obj_tag(v___x_385_) == 0)
{
lean_object* v_a_396_; lean_object* v___x_398_; uint8_t v_isShared_399_; uint8_t v_isSharedCheck_403_; 
lean_dec(v_json_383_);
v_a_396_ = lean_ctor_get(v___x_385_, 0);
v_isSharedCheck_403_ = !lean_is_exclusive(v___x_385_);
if (v_isSharedCheck_403_ == 0)
{
v___x_398_ = v___x_385_;
v_isShared_399_ = v_isSharedCheck_403_;
goto v_resetjp_397_;
}
else
{
lean_inc(v_a_396_);
lean_dec(v___x_385_);
v___x_398_ = lean_box(0);
v_isShared_399_ = v_isSharedCheck_403_;
goto v_resetjp_397_;
}
v_resetjp_397_:
{
lean_object* v___x_401_; 
if (v_isShared_399_ == 0)
{
lean_ctor_set_tag(v___x_398_, 0);
v___x_401_ = v___x_398_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v_a_396_);
v___x_401_ = v_reuseFailAlloc_402_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
return v___x_401_;
}
}
}
else
{
lean_object* v_a_404_; lean_object* v___x_405_; lean_object* v___x_406_; 
v_a_404_ = lean_ctor_get(v___x_385_, 0);
lean_inc(v_a_404_);
lean_dec_ref(v___x_385_);
v___x_405_ = ((lean_object*)(l_Lean_Lsp_instToJsonRange_toJson___closed__1));
v___x_406_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRange_fromJson_spec__0(v_json_383_, v___x_405_);
if (lean_obj_tag(v___x_406_) == 0)
{
lean_object* v_a_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_416_; 
lean_dec(v_a_404_);
v_a_407_ = lean_ctor_get(v___x_406_, 0);
v_isSharedCheck_416_ = !lean_is_exclusive(v___x_406_);
if (v_isSharedCheck_416_ == 0)
{
v___x_409_ = v___x_406_;
v_isShared_410_ = v_isSharedCheck_416_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_a_407_);
lean_dec(v___x_406_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_416_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_414_; 
v___x_411_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRange_fromJson___closed__11, &l_Lean_Lsp_instFromJsonRange_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonRange_fromJson___closed__11);
v___x_412_ = lean_string_append(v___x_411_, v_a_407_);
lean_dec(v_a_407_);
if (v_isShared_410_ == 0)
{
lean_ctor_set(v___x_409_, 0, v___x_412_);
v___x_414_ = v___x_409_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_415_; 
v_reuseFailAlloc_415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_415_, 0, v___x_412_);
v___x_414_ = v_reuseFailAlloc_415_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
return v___x_414_;
}
}
}
else
{
if (lean_obj_tag(v___x_406_) == 0)
{
lean_object* v_a_417_; lean_object* v___x_419_; uint8_t v_isShared_420_; uint8_t v_isSharedCheck_424_; 
lean_dec(v_a_404_);
v_a_417_ = lean_ctor_get(v___x_406_, 0);
v_isSharedCheck_424_ = !lean_is_exclusive(v___x_406_);
if (v_isSharedCheck_424_ == 0)
{
v___x_419_ = v___x_406_;
v_isShared_420_ = v_isSharedCheck_424_;
goto v_resetjp_418_;
}
else
{
lean_inc(v_a_417_);
lean_dec(v___x_406_);
v___x_419_ = lean_box(0);
v_isShared_420_ = v_isSharedCheck_424_;
goto v_resetjp_418_;
}
v_resetjp_418_:
{
lean_object* v___x_422_; 
if (v_isShared_420_ == 0)
{
lean_ctor_set_tag(v___x_419_, 0);
v___x_422_ = v___x_419_;
goto v_reusejp_421_;
}
else
{
lean_object* v_reuseFailAlloc_423_; 
v_reuseFailAlloc_423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_423_, 0, v_a_417_);
v___x_422_ = v_reuseFailAlloc_423_;
goto v_reusejp_421_;
}
v_reusejp_421_:
{
return v___x_422_;
}
}
}
else
{
lean_object* v_a_425_; lean_object* v___x_427_; uint8_t v_isShared_428_; uint8_t v_isSharedCheck_433_; 
v_a_425_ = lean_ctor_get(v___x_406_, 0);
v_isSharedCheck_433_ = !lean_is_exclusive(v___x_406_);
if (v_isSharedCheck_433_ == 0)
{
v___x_427_ = v___x_406_;
v_isShared_428_ = v_isSharedCheck_433_;
goto v_resetjp_426_;
}
else
{
lean_inc(v_a_425_);
lean_dec(v___x_406_);
v___x_427_ = lean_box(0);
v_isShared_428_ = v_isSharedCheck_433_;
goto v_resetjp_426_;
}
v_resetjp_426_:
{
lean_object* v___x_429_; lean_object* v___x_431_; 
v___x_429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_429_, 0, v_a_404_);
lean_ctor_set(v___x_429_, 1, v_a_425_);
if (v_isShared_428_ == 0)
{
lean_ctor_set(v___x_427_, 0, v___x_429_);
v___x_431_ = v___x_427_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v___x_429_);
v___x_431_ = v_reuseFailAlloc_432_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
return v___x_431_;
}
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_instOrdRange_ord(lean_object* v_x_436_, lean_object* v_x_437_){
_start:
{
lean_object* v_start_438_; lean_object* v_end_439_; lean_object* v_start_440_; lean_object* v_end_441_; uint8_t v___x_442_; 
v_start_438_ = lean_ctor_get(v_x_436_, 0);
v_end_439_ = lean_ctor_get(v_x_436_, 1);
v_start_440_ = lean_ctor_get(v_x_437_, 0);
v_end_441_ = lean_ctor_get(v_x_437_, 1);
v___x_442_ = l_Lean_Lsp_instOrdPosition_ord(v_start_438_, v_start_440_);
if (v___x_442_ == 1)
{
uint8_t v___x_443_; 
v___x_443_ = l_Lean_Lsp_instOrdPosition_ord(v_end_439_, v_end_441_);
if (v___x_443_ == 1)
{
return v___x_443_;
}
else
{
return v___x_443_;
}
}
else
{
return v___x_442_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instOrdRange_ord___boxed(lean_object* v_x_444_, lean_object* v_x_445_){
_start:
{
uint8_t v_res_446_; lean_object* v_r_447_; 
v_res_446_ = l_Lean_Lsp_instOrdRange_ord(v_x_444_, v_x_445_);
lean_dec_ref(v_x_445_);
lean_dec_ref(v_x_444_);
v_r_447_ = lean_box(v_res_446_);
return v_r_447_;
}
}
static lean_object* _init_l_Lean_Lsp_instReprRange_repr___redArg___closed__3(void){
_start:
{
lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_458_ = lean_unsigned_to_nat(9u);
v___x_459_ = lean_nat_to_int(v___x_458_);
return v___x_459_;
}
}
static lean_object* _init_l_Lean_Lsp_instReprRange_repr___redArg___closed__5(void){
_start:
{
lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_462_ = lean_unsigned_to_nat(7u);
v___x_463_ = lean_nat_to_int(v___x_462_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instReprRange_repr___redArg(lean_object* v_x_464_){
_start:
{
lean_object* v_start_465_; lean_object* v_end_466_; lean_object* v___x_468_; uint8_t v_isShared_469_; uint8_t v_isSharedCheck_499_; 
v_start_465_ = lean_ctor_get(v_x_464_, 0);
v_end_466_ = lean_ctor_get(v_x_464_, 1);
v_isSharedCheck_499_ = !lean_is_exclusive(v_x_464_);
if (v_isSharedCheck_499_ == 0)
{
v___x_468_ = v_x_464_;
v_isShared_469_ = v_isSharedCheck_499_;
goto v_resetjp_467_;
}
else
{
lean_inc(v_end_466_);
lean_inc(v_start_465_);
lean_dec(v_x_464_);
v___x_468_ = lean_box(0);
v_isShared_469_ = v_isSharedCheck_499_;
goto v_resetjp_467_;
}
v_resetjp_467_:
{
lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_475_; 
v___x_470_ = ((lean_object*)(l_Lean_Lsp_instReprPosition_repr___redArg___closed__4));
v___x_471_ = ((lean_object*)(l_Lean_Lsp_instReprRange_repr___redArg___closed__2));
v___x_472_ = lean_obj_once(&l_Lean_Lsp_instReprRange_repr___redArg___closed__3, &l_Lean_Lsp_instReprRange_repr___redArg___closed__3_once, _init_l_Lean_Lsp_instReprRange_repr___redArg___closed__3);
v___x_473_ = l_Lean_Lsp_instReprPosition_repr___redArg(v_start_465_);
if (v_isShared_469_ == 0)
{
lean_ctor_set_tag(v___x_468_, 4);
lean_ctor_set(v___x_468_, 1, v___x_473_);
lean_ctor_set(v___x_468_, 0, v___x_472_);
v___x_475_ = v___x_468_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v___x_472_);
lean_ctor_set(v_reuseFailAlloc_498_, 1, v___x_473_);
v___x_475_ = v_reuseFailAlloc_498_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
uint8_t v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_476_ = 0;
v___x_477_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_477_, 0, v___x_475_);
lean_ctor_set_uint8(v___x_477_, sizeof(void*)*1, v___x_476_);
v___x_478_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_478_, 0, v___x_471_);
lean_ctor_set(v___x_478_, 1, v___x_477_);
v___x_479_ = ((lean_object*)(l_Lean_Lsp_instReprPosition_repr___redArg___closed__8));
v___x_480_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_480_, 0, v___x_478_);
lean_ctor_set(v___x_480_, 1, v___x_479_);
v___x_481_ = lean_box(1);
v___x_482_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_482_, 0, v___x_480_);
lean_ctor_set(v___x_482_, 1, v___x_481_);
v___x_483_ = ((lean_object*)(l_Lean_Lsp_instReprRange_repr___redArg___closed__4));
v___x_484_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_484_, 0, v___x_482_);
lean_ctor_set(v___x_484_, 1, v___x_483_);
v___x_485_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_485_, 0, v___x_484_);
lean_ctor_set(v___x_485_, 1, v___x_470_);
v___x_486_ = lean_obj_once(&l_Lean_Lsp_instReprRange_repr___redArg___closed__5, &l_Lean_Lsp_instReprRange_repr___redArg___closed__5_once, _init_l_Lean_Lsp_instReprRange_repr___redArg___closed__5);
v___x_487_ = l_Lean_Lsp_instReprPosition_repr___redArg(v_end_466_);
v___x_488_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_488_, 0, v___x_486_);
lean_ctor_set(v___x_488_, 1, v___x_487_);
v___x_489_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_489_, 0, v___x_488_);
lean_ctor_set_uint8(v___x_489_, sizeof(void*)*1, v___x_476_);
v___x_490_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_490_, 0, v___x_485_);
lean_ctor_set(v___x_490_, 1, v___x_489_);
v___x_491_ = lean_obj_once(&l_Lean_Lsp_instReprPosition_repr___redArg___closed__13, &l_Lean_Lsp_instReprPosition_repr___redArg___closed__13_once, _init_l_Lean_Lsp_instReprPosition_repr___redArg___closed__13);
v___x_492_ = ((lean_object*)(l_Lean_Lsp_instReprPosition_repr___redArg___closed__14));
v___x_493_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_493_, 0, v___x_492_);
lean_ctor_set(v___x_493_, 1, v___x_490_);
v___x_494_ = ((lean_object*)(l_Lean_Lsp_instReprPosition_repr___redArg___closed__15));
v___x_495_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_495_, 0, v___x_493_);
lean_ctor_set(v___x_495_, 1, v___x_494_);
v___x_496_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_496_, 0, v___x_491_);
lean_ctor_set(v___x_496_, 1, v___x_495_);
v___x_497_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_497_, 0, v___x_496_);
lean_ctor_set_uint8(v___x_497_, sizeof(void*)*1, v___x_476_);
return v___x_497_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instReprRange_repr(lean_object* v_x_500_, lean_object* v_prec_501_){
_start:
{
lean_object* v___x_502_; 
v___x_502_ = l_Lean_Lsp_instReprRange_repr___redArg(v_x_500_);
return v___x_502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instReprRange_repr___boxed(lean_object* v_x_503_, lean_object* v_prec_504_){
_start:
{
lean_object* v_res_505_; 
v_res_505_ = l_Lean_Lsp_instReprRange_repr(v_x_503_, v_prec_504_);
lean_dec(v_prec_504_);
return v_res_505_;
}
}
static lean_object* _init_l_Lean_Lsp_instLTRange(void){
_start:
{
lean_object* v___x_508_; 
v___x_508_ = lean_box(0);
return v___x_508_;
}
}
static lean_object* _init_l_Lean_Lsp_instLERange(void){
_start:
{
lean_object* v___x_509_; 
v___x_509_ = lean_box(0);
return v___x_509_;
}
}
lean_object* runtime_initialize_Lean_Data_Json_FromToJson_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_Lsp_BasicAux(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Data_Json_FromToJson_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Lsp_instLTPosition = _init_l_Lean_Lsp_instLTPosition();
lean_mark_persistent(l_Lean_Lsp_instLTPosition);
l_Lean_Lsp_instLEPosition = _init_l_Lean_Lsp_instLEPosition();
lean_mark_persistent(l_Lean_Lsp_instLEPosition);
l_Lean_Lsp_instLTRange = _init_l_Lean_Lsp_instLTRange();
lean_mark_persistent(l_Lean_Lsp_instLTRange);
l_Lean_Lsp_instLERange = _init_l_Lean_Lsp_instLERange();
lean_mark_persistent(l_Lean_Lsp_instLERange);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Data_Lsp_BasicAux(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Data_Json_FromToJson_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_Lsp_BasicAux(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_Json_FromToJson_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Lsp_BasicAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Data_Lsp_BasicAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Data_Lsp_BasicAux(builtin);
}
#ifdef __cplusplus
}
#endif

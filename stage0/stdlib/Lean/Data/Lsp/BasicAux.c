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
static const lean_ctor_object l_Lean_Lsp_instInhabitedPosition_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Lsp_instInhabitedPosition_default___closed__0 = (const lean_object*)&l_Lean_Lsp_instInhabitedPosition_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instInhabitedPosition_default = (const lean_object*)&l_Lean_Lsp_instInhabitedPosition_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instInhabitedPosition = (const lean_object*)&l_Lean_Lsp_instInhabitedPosition_default___closed__0_value;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Lsp_instBEqPosition_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqPosition_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_instBEqPosition___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instBEqPosition_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instBEqPosition___closed__0 = (const lean_object*)&l_Lean_Lsp_instBEqPosition___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instBEqPosition = (const lean_object*)&l_Lean_Lsp_instBEqPosition___closed__0_value;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Lsp_instOrdPosition_ord(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instOrdPosition_ord___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_instOrdPosition___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instOrdPosition_ord___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instOrdPosition___closed__0 = (const lean_object*)&l_Lean_Lsp_instOrdPosition___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instOrdPosition = (const lean_object*)&l_Lean_Lsp_instOrdPosition___closed__0_value;
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
LEAN_EXPORT uint64_t l_Lean_Lsp_instHashablePosition_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instHashablePosition_hash___boxed(lean_object*);
static const lean_closure_object l_Lean_Lsp_instHashablePosition___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instHashablePosition_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instHashablePosition___closed__0 = (const lean_object*)&l_Lean_Lsp_instHashablePosition___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instHashablePosition = (const lean_object*)&l_Lean_Lsp_instHashablePosition___closed__0_value;
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonPosition_toJson_spec__0(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instToJsonPosition_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "line"};
static const lean_object* l_Lean_Lsp_instToJsonPosition_toJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonPosition_toJson___closed__0_value;
static const lean_string_object l_Lean_Lsp_instToJsonPosition_toJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "character"};
static const lean_object* l_Lean_Lsp_instToJsonPosition_toJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instToJsonPosition_toJson___closed__1_value;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_once_cell_t l_Lean_Lsp_instToJsonPosition_toJson___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instToJsonPosition_toJson___closed__2;
lean_object* l_Lean_JsonNumber_fromNat(lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonPosition_toJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonPosition___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonPosition_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonPosition___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonPosition___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonPosition = (const lean_object*)&l_Lean_Lsp_instToJsonPosition___closed__0_value;
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
lean_object* l_Lean_Json_getNat_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPosition_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPosition_fromJson_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instFromJsonPosition_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Lsp_instFromJsonPosition_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonPosition_fromJson___closed__0_value;
static const lean_string_object l_Lean_Lsp_instFromJsonPosition_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Lsp"};
static const lean_object* l_Lean_Lsp_instFromJsonPosition_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonPosition_fromJson___closed__1_value;
static const lean_string_object l_Lean_Lsp_instFromJsonPosition_fromJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Position"};
static const lean_object* l_Lean_Lsp_instFromJsonPosition_fromJson___closed__2 = (const lean_object*)&l_Lean_Lsp_instFromJsonPosition_fromJson___closed__2_value;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Lsp_instFromJsonPosition_fromJson___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonPosition_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonPosition_fromJson___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonPosition_fromJson___closed__3_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonPosition_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonPosition_fromJson___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonPosition_fromJson___closed__3_value_aux_1),((lean_object*)&l_Lean_Lsp_instFromJsonPosition_fromJson___closed__2_value),LEAN_SCALAR_PTR_LITERAL(29, 140, 170, 135, 118, 250, 230, 191)}};
static const lean_object* l_Lean_Lsp_instFromJsonPosition_fromJson___closed__3 = (const lean_object*)&l_Lean_Lsp_instFromJsonPosition_fromJson___closed__3_value;
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
static lean_once_cell_t l_Lean_Lsp_instFromJsonPosition_fromJson___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonPosition_fromJson___closed__4;
static const lean_string_object l_Lean_Lsp_instFromJsonPosition_fromJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lean_Lsp_instFromJsonPosition_fromJson___closed__5 = (const lean_object*)&l_Lean_Lsp_instFromJsonPosition_fromJson___closed__5_value;
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Lsp_instFromJsonPosition_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonPosition_fromJson___closed__6;
lean_object* l_Lean_Name_mkStr1(lean_object*);
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
lean_object* lean_nat_to_int(lean_object*);
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
lean_object* lean_string_length(lean_object*);
static lean_once_cell_t l_Lean_Lsp_instReprPosition_repr___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instReprPosition_repr___redArg___closed__12;
static lean_once_cell_t l_Lean_Lsp_instReprPosition_repr___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instReprPosition_repr___redArg___closed__13;
static const lean_ctor_object l_Lean_Lsp_instReprPosition_repr___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Lsp_instReprPosition_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_Lsp_instReprPosition_repr___redArg___closed__14 = (const lean_object*)&l_Lean_Lsp_instReprPosition_repr___redArg___closed__14_value;
static const lean_ctor_object l_Lean_Lsp_instReprPosition_repr___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Lsp_instReprPosition_repr___redArg___closed__11_value)}};
static const lean_object* l_Lean_Lsp_instReprPosition_repr___redArg___closed__15 = (const lean_object*)&l_Lean_Lsp_instReprPosition_repr___redArg___closed__15_value;
lean_object* l_Nat_reprFast(lean_object*);
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
static lean_once_cell_t l_Lean_Lsp_instInhabitedRange_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instInhabitedRange_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_Lsp_instInhabitedRange_default;
LEAN_EXPORT lean_object* l_Lean_Lsp_instInhabitedRange;
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
LEAN_EXPORT uint8_t l_Lean_Lsp_instBEqPosition_beq(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_nat_dec_eq(x_3, x_5);
if (x_7 == 0)
{
return x_7;
}
else
{
uint8_t x_8; 
x_8 = lean_nat_dec_eq(x_4, x_6);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqPosition_beq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Lsp_instBEqPosition_beq(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_instOrdPosition_ord(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_nat_dec_lt(x_3, x_5);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = lean_nat_dec_eq(x_3, x_5);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = 2;
return x_9;
}
else
{
uint8_t x_10; 
x_10 = lean_nat_dec_lt(x_4, x_6);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = lean_nat_dec_eq(x_4, x_6);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = 2;
return x_12;
}
else
{
uint8_t x_13; 
x_13 = 1;
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = 0;
return x_14;
}
}
}
else
{
uint8_t x_15; 
x_15 = 0;
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instOrdPosition_ord___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Lsp_instOrdPosition_ord(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint64_t l_Lean_Lsp_instHashablePosition_hash(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint64_t x_4; uint64_t x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = 0;
x_5 = lean_uint64_of_nat(x_2);
x_6 = lean_uint64_mix_hash(x_4, x_5);
x_7 = lean_uint64_of_nat(x_3);
x_8 = lean_uint64_mix_hash(x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instHashablePosition_hash___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lean_Lsp_instHashablePosition_hash(x_1);
lean_dec_ref(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonPosition_toJson_spec__0(lean_object* x_1, lean_object* x_2) {
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
static lean_object* _init_l_Lean_Lsp_instToJsonPosition_toJson___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonPosition_toJson(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = ((lean_object*)(l_Lean_Lsp_instToJsonPosition_toJson___closed__0));
x_6 = l_Lean_JsonNumber_fromNat(x_3);
x_7 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_1, 1, x_7);
lean_ctor_set(x_1, 0, x_5);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
x_10 = ((lean_object*)(l_Lean_Lsp_instToJsonPosition_toJson___closed__1));
x_11 = l_Lean_JsonNumber_fromNat(x_4);
x_12 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_8);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_8);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_obj_once(&l_Lean_Lsp_instToJsonPosition_toJson___closed__2, &l_Lean_Lsp_instToJsonPosition_toJson___closed__2_once, _init_l_Lean_Lsp_instToJsonPosition_toJson___closed__2);
x_18 = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonPosition_toJson_spec__0(x_16, x_17);
x_19 = l_Lean_Json_mkObj(x_18);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_20 = lean_ctor_get(x_1, 0);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_1);
x_22 = ((lean_object*)(l_Lean_Lsp_instToJsonPosition_toJson___closed__0));
x_23 = l_Lean_JsonNumber_fromNat(x_20);
x_24 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = ((lean_object*)(l_Lean_Lsp_instToJsonPosition_toJson___closed__1));
x_29 = l_Lean_JsonNumber_fromNat(x_21);
x_30 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_26);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_26);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_27);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_obj_once(&l_Lean_Lsp_instToJsonPosition_toJson___closed__2, &l_Lean_Lsp_instToJsonPosition_toJson___closed__2_once, _init_l_Lean_Lsp_instToJsonPosition_toJson___closed__2);
x_36 = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonPosition_toJson_spec__0(x_34, x_35);
x_37 = l_Lean_Json_mkObj(x_36);
return x_37;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPosition_fromJson_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l_Lean_Json_getNat_x3f(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPosition_fromJson_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPosition_fromJson_spec__0(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPosition_fromJson___closed__4(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_Lsp_instFromJsonPosition_fromJson___closed__3));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPosition_fromJson___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Lsp_instFromJsonPosition_fromJson___closed__5));
x_2 = lean_obj_once(&l_Lean_Lsp_instFromJsonPosition_fromJson___closed__4, &l_Lean_Lsp_instFromJsonPosition_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonPosition_fromJson___closed__4);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPosition_fromJson___closed__8(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_Lsp_instFromJsonPosition_fromJson___closed__7));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPosition_fromJson___closed__9(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Lsp_instFromJsonPosition_fromJson___closed__8, &l_Lean_Lsp_instFromJsonPosition_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonPosition_fromJson___closed__8);
x_2 = lean_obj_once(&l_Lean_Lsp_instFromJsonPosition_fromJson___closed__6, &l_Lean_Lsp_instFromJsonPosition_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonPosition_fromJson___closed__6);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPosition_fromJson___closed__11(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Lsp_instFromJsonPosition_fromJson___closed__10));
x_2 = lean_obj_once(&l_Lean_Lsp_instFromJsonPosition_fromJson___closed__9, &l_Lean_Lsp_instFromJsonPosition_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonPosition_fromJson___closed__9);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPosition_fromJson___closed__13(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_Lsp_instFromJsonPosition_fromJson___closed__12));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPosition_fromJson___closed__14(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Lsp_instFromJsonPosition_fromJson___closed__13, &l_Lean_Lsp_instFromJsonPosition_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonPosition_fromJson___closed__13);
x_2 = lean_obj_once(&l_Lean_Lsp_instFromJsonPosition_fromJson___closed__6, &l_Lean_Lsp_instFromJsonPosition_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonPosition_fromJson___closed__6);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPosition_fromJson___closed__15(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Lsp_instFromJsonPosition_fromJson___closed__10));
x_2 = lean_obj_once(&l_Lean_Lsp_instFromJsonPosition_fromJson___closed__14, &l_Lean_Lsp_instFromJsonPosition_fromJson___closed__14_once, _init_l_Lean_Lsp_instFromJsonPosition_fromJson___closed__14);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonPosition_fromJson(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = ((lean_object*)(l_Lean_Lsp_instToJsonPosition_toJson___closed__0));
lean_inc(x_1);
x_3 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPosition_fromJson_spec__0(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
lean_dec(x_1);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_obj_once(&l_Lean_Lsp_instFromJsonPosition_fromJson___closed__11, &l_Lean_Lsp_instFromJsonPosition_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonPosition_fromJson___closed__11);
x_7 = lean_string_append(x_6, x_5);
lean_dec(x_5);
lean_ctor_set(x_3, 0, x_7);
return x_3;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_obj_once(&l_Lean_Lsp_instFromJsonPosition_fromJson___closed__11, &l_Lean_Lsp_instFromJsonPosition_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonPosition_fromJson___closed__11);
x_10 = lean_string_append(x_9, x_8);
lean_dec(x_8);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
else
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_12; 
lean_dec(x_1);
x_12 = !lean_is_exclusive(x_3);
if (x_12 == 0)
{
lean_ctor_set_tag(x_3, 0);
return x_3;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_3, 0);
lean_inc(x_13);
lean_dec(x_3);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_3, 0);
lean_inc(x_15);
lean_dec_ref(x_3);
x_16 = ((lean_object*)(l_Lean_Lsp_instToJsonPosition_toJson___closed__1));
x_17 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPosition_fromJson_spec__0(x_1, x_16);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
lean_dec(x_15);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_obj_once(&l_Lean_Lsp_instFromJsonPosition_fromJson___closed__15, &l_Lean_Lsp_instFromJsonPosition_fromJson___closed__15_once, _init_l_Lean_Lsp_instFromJsonPosition_fromJson___closed__15);
x_21 = lean_string_append(x_20, x_19);
lean_dec(x_19);
lean_ctor_set(x_17, 0, x_21);
return x_17;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_17, 0);
lean_inc(x_22);
lean_dec(x_17);
x_23 = lean_obj_once(&l_Lean_Lsp_instFromJsonPosition_fromJson___closed__15, &l_Lean_Lsp_instFromJsonPosition_fromJson___closed__15_once, _init_l_Lean_Lsp_instFromJsonPosition_fromJson___closed__15);
x_24 = lean_string_append(x_23, x_22);
lean_dec(x_22);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
else
{
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_26; 
lean_dec(x_15);
x_26 = !lean_is_exclusive(x_17);
if (x_26 == 0)
{
lean_ctor_set_tag(x_17, 0);
return x_17;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_17, 0);
lean_inc(x_27);
lean_dec(x_17);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_17);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_17, 0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_15);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_17, 0, x_31);
return x_17;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_17, 0);
lean_inc(x_32);
lean_dec(x_17);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_15);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Lsp_instReprPosition_repr_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_instReprPosition_repr___redArg___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_instReprPosition_repr___redArg___closed__10(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(13u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_instReprPosition_repr___redArg___closed__12(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Lsp_instReprPosition_repr___redArg___closed__0));
x_2 = lean_string_length(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_instReprPosition_repr___redArg___closed__13(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_Lsp_instReprPosition_repr___redArg___closed__12, &l_Lean_Lsp_instReprPosition_repr___redArg___closed__12_once, _init_l_Lean_Lsp_instReprPosition_repr___redArg___closed__12);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instReprPosition_repr___redArg(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = ((lean_object*)(l_Lean_Lsp_instReprPosition_repr___redArg___closed__4));
x_6 = ((lean_object*)(l_Lean_Lsp_instReprPosition_repr___redArg___closed__5));
x_7 = lean_obj_once(&l_Lean_Lsp_instReprPosition_repr___redArg___closed__6, &l_Lean_Lsp_instReprPosition_repr___redArg___closed__6_once, _init_l_Lean_Lsp_instReprPosition_repr___redArg___closed__6);
x_8 = l_Nat_reprFast(x_3);
x_9 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set_tag(x_1, 4);
lean_ctor_set(x_1, 1, x_9);
lean_ctor_set(x_1, 0, x_7);
x_10 = 0;
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_10);
x_12 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_12, 0, x_6);
lean_ctor_set(x_12, 1, x_11);
x_13 = ((lean_object*)(l_Lean_Lsp_instReprPosition_repr___redArg___closed__8));
x_14 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_box(1);
x_16 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = ((lean_object*)(l_Lean_Lsp_instReprPosition_repr___redArg___closed__9));
x_18 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_5);
x_20 = lean_obj_once(&l_Lean_Lsp_instReprPosition_repr___redArg___closed__10, &l_Lean_Lsp_instReprPosition_repr___redArg___closed__10_once, _init_l_Lean_Lsp_instReprPosition_repr___redArg___closed__10);
x_21 = l_Nat_reprFast(x_4);
x_22 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set_uint8(x_24, sizeof(void*)*1, x_10);
x_25 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_25, 0, x_19);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_obj_once(&l_Lean_Lsp_instReprPosition_repr___redArg___closed__13, &l_Lean_Lsp_instReprPosition_repr___redArg___closed__13_once, _init_l_Lean_Lsp_instReprPosition_repr___redArg___closed__13);
x_27 = ((lean_object*)(l_Lean_Lsp_instReprPosition_repr___redArg___closed__14));
x_28 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_25);
x_29 = ((lean_object*)(l_Lean_Lsp_instReprPosition_repr___redArg___closed__15));
x_30 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_31, 0, x_26);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set_uint8(x_32, sizeof(void*)*1, x_10);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_33 = lean_ctor_get(x_1, 0);
x_34 = lean_ctor_get(x_1, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_1);
x_35 = ((lean_object*)(l_Lean_Lsp_instReprPosition_repr___redArg___closed__4));
x_36 = ((lean_object*)(l_Lean_Lsp_instReprPosition_repr___redArg___closed__5));
x_37 = lean_obj_once(&l_Lean_Lsp_instReprPosition_repr___redArg___closed__6, &l_Lean_Lsp_instReprPosition_repr___redArg___closed__6_once, _init_l_Lean_Lsp_instReprPosition_repr___redArg___closed__6);
x_38 = l_Nat_reprFast(x_33);
x_39 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_40 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_39);
x_41 = 0;
x_42 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set_uint8(x_42, sizeof(void*)*1, x_41);
x_43 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_43, 0, x_36);
lean_ctor_set(x_43, 1, x_42);
x_44 = ((lean_object*)(l_Lean_Lsp_instReprPosition_repr___redArg___closed__8));
x_45 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_box(1);
x_47 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = ((lean_object*)(l_Lean_Lsp_instReprPosition_repr___redArg___closed__9));
x_49 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_35);
x_51 = lean_obj_once(&l_Lean_Lsp_instReprPosition_repr___redArg___closed__10, &l_Lean_Lsp_instReprPosition_repr___redArg___closed__10_once, _init_l_Lean_Lsp_instReprPosition_repr___redArg___closed__10);
x_52 = l_Nat_reprFast(x_34);
x_53 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_53, 0, x_52);
x_54 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_54, 0, x_51);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set_uint8(x_55, sizeof(void*)*1, x_41);
x_56 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_56, 0, x_50);
lean_ctor_set(x_56, 1, x_55);
x_57 = lean_obj_once(&l_Lean_Lsp_instReprPosition_repr___redArg___closed__13, &l_Lean_Lsp_instReprPosition_repr___redArg___closed__13_once, _init_l_Lean_Lsp_instReprPosition_repr___redArg___closed__13);
x_58 = ((lean_object*)(l_Lean_Lsp_instReprPosition_repr___redArg___closed__14));
x_59 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_56);
x_60 = ((lean_object*)(l_Lean_Lsp_instReprPosition_repr___redArg___closed__15));
x_61 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_62, 0, x_57);
lean_ctor_set(x_62, 1, x_61);
x_63 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set_uint8(x_63, sizeof(void*)*1, x_41);
return x_63;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instReprPosition_repr(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Lsp_instReprPosition_repr___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instReprPosition_repr___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Lsp_instReprPosition_repr(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToStringPosition___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec_ref(x_1);
x_4 = ((lean_object*)(l_Lean_Lsp_instToStringPosition___lam__0___closed__0));
x_5 = l_Nat_reprFast(x_2);
x_6 = lean_string_append(x_4, x_5);
lean_dec_ref(x_5);
x_7 = ((lean_object*)(l_Lean_Lsp_instToStringPosition___lam__0___closed__1));
x_8 = lean_string_append(x_6, x_7);
x_9 = l_Nat_reprFast(x_3);
x_10 = lean_string_append(x_8, x_9);
lean_dec_ref(x_9);
x_11 = ((lean_object*)(l_Lean_Lsp_instToStringPosition___lam__0___closed__2));
x_12 = lean_string_append(x_10, x_11);
return x_12;
}
}
static lean_object* _init_l_Lean_Lsp_instLTPosition(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_instLEPosition(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_instInhabitedRange_default___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Lsp_instInhabitedPosition_default));
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_instInhabitedRange_default(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_Lean_Lsp_instInhabitedRange_default___closed__0, &l_Lean_Lsp_instInhabitedRange_default___closed__0_once, _init_l_Lean_Lsp_instInhabitedRange_default___closed__0);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_instInhabitedRange(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Lsp_instInhabitedRange_default;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_instBEqRange_beq(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = l_Lean_Lsp_instBEqPosition_beq(x_3, x_5);
if (x_7 == 0)
{
return x_7;
}
else
{
uint8_t x_8; 
x_8 = l_Lean_Lsp_instBEqPosition_beq(x_4, x_6);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqRange_beq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Lsp_instBEqRange_beq(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint64_t l_Lean_Lsp_instHashableRange_hash(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint64_t x_4; uint64_t x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = 0;
x_5 = l_Lean_Lsp_instHashablePosition_hash(x_2);
x_6 = lean_uint64_mix_hash(x_4, x_5);
x_7 = l_Lean_Lsp_instHashablePosition_hash(x_3);
x_8 = lean_uint64_mix_hash(x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instHashableRange_hash___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lean_Lsp_instHashableRange_hash(x_1);
lean_dec_ref(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRange_toJson(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = ((lean_object*)(l_Lean_Lsp_instToJsonRange_toJson___closed__0));
x_6 = l_Lean_Lsp_instToJsonPosition_toJson(x_3);
lean_ctor_set(x_1, 1, x_6);
lean_ctor_set(x_1, 0, x_5);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
x_9 = ((lean_object*)(l_Lean_Lsp_instToJsonRange_toJson___closed__1));
x_10 = l_Lean_Lsp_instToJsonPosition_toJson(x_4);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_7);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_7);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_obj_once(&l_Lean_Lsp_instToJsonPosition_toJson___closed__2, &l_Lean_Lsp_instToJsonPosition_toJson___closed__2_once, _init_l_Lean_Lsp_instToJsonPosition_toJson___closed__2);
x_16 = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonPosition_toJson_spec__0(x_14, x_15);
x_17 = l_Lean_Json_mkObj(x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_18 = lean_ctor_get(x_1, 0);
x_19 = lean_ctor_get(x_1, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_1);
x_20 = ((lean_object*)(l_Lean_Lsp_instToJsonRange_toJson___closed__0));
x_21 = l_Lean_Lsp_instToJsonPosition_toJson(x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = ((lean_object*)(l_Lean_Lsp_instToJsonRange_toJson___closed__1));
x_26 = l_Lean_Lsp_instToJsonPosition_toJson(x_19);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_23);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_23);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_24);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_obj_once(&l_Lean_Lsp_instToJsonPosition_toJson___closed__2, &l_Lean_Lsp_instToJsonPosition_toJson___closed__2_once, _init_l_Lean_Lsp_instToJsonPosition_toJson___closed__2);
x_32 = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonPosition_toJson_spec__0(x_30, x_31);
x_33 = l_Lean_Json_mkObj(x_32);
return x_33;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRange_fromJson_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l_Lean_Lsp_instFromJsonPosition_fromJson(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRange_fromJson_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRange_fromJson_spec__0(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRange_fromJson___closed__2(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_Lsp_instFromJsonRange_fromJson___closed__1));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRange_fromJson___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Lsp_instFromJsonPosition_fromJson___closed__5));
x_2 = lean_obj_once(&l_Lean_Lsp_instFromJsonRange_fromJson___closed__2, &l_Lean_Lsp_instFromJsonRange_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonRange_fromJson___closed__2);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRange_fromJson___closed__5(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_Lsp_instFromJsonRange_fromJson___closed__4));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRange_fromJson___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Lsp_instFromJsonRange_fromJson___closed__5, &l_Lean_Lsp_instFromJsonRange_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonRange_fromJson___closed__5);
x_2 = lean_obj_once(&l_Lean_Lsp_instFromJsonRange_fromJson___closed__3, &l_Lean_Lsp_instFromJsonRange_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonRange_fromJson___closed__3);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRange_fromJson___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Lsp_instFromJsonPosition_fromJson___closed__10));
x_2 = lean_obj_once(&l_Lean_Lsp_instFromJsonRange_fromJson___closed__6, &l_Lean_Lsp_instFromJsonRange_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonRange_fromJson___closed__6);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRange_fromJson___closed__9(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l_Lean_Lsp_instFromJsonRange_fromJson___closed__8));
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRange_fromJson___closed__10(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Lsp_instFromJsonRange_fromJson___closed__9, &l_Lean_Lsp_instFromJsonRange_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonRange_fromJson___closed__9);
x_2 = lean_obj_once(&l_Lean_Lsp_instFromJsonRange_fromJson___closed__3, &l_Lean_Lsp_instFromJsonRange_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonRange_fromJson___closed__3);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRange_fromJson___closed__11(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Lsp_instFromJsonPosition_fromJson___closed__10));
x_2 = lean_obj_once(&l_Lean_Lsp_instFromJsonRange_fromJson___closed__10, &l_Lean_Lsp_instFromJsonRange_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonRange_fromJson___closed__10);
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonRange_fromJson(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = ((lean_object*)(l_Lean_Lsp_instToJsonRange_toJson___closed__0));
lean_inc(x_1);
x_3 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRange_fromJson_spec__0(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
lean_dec(x_1);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_obj_once(&l_Lean_Lsp_instFromJsonRange_fromJson___closed__7, &l_Lean_Lsp_instFromJsonRange_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonRange_fromJson___closed__7);
x_7 = lean_string_append(x_6, x_5);
lean_dec(x_5);
lean_ctor_set(x_3, 0, x_7);
return x_3;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_obj_once(&l_Lean_Lsp_instFromJsonRange_fromJson___closed__7, &l_Lean_Lsp_instFromJsonRange_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonRange_fromJson___closed__7);
x_10 = lean_string_append(x_9, x_8);
lean_dec(x_8);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
else
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_12; 
lean_dec(x_1);
x_12 = !lean_is_exclusive(x_3);
if (x_12 == 0)
{
lean_ctor_set_tag(x_3, 0);
return x_3;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_3, 0);
lean_inc(x_13);
lean_dec(x_3);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_3, 0);
lean_inc(x_15);
lean_dec_ref(x_3);
x_16 = ((lean_object*)(l_Lean_Lsp_instToJsonRange_toJson___closed__1));
x_17 = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRange_fromJson_spec__0(x_1, x_16);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
lean_dec(x_15);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_obj_once(&l_Lean_Lsp_instFromJsonRange_fromJson___closed__11, &l_Lean_Lsp_instFromJsonRange_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonRange_fromJson___closed__11);
x_21 = lean_string_append(x_20, x_19);
lean_dec(x_19);
lean_ctor_set(x_17, 0, x_21);
return x_17;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_17, 0);
lean_inc(x_22);
lean_dec(x_17);
x_23 = lean_obj_once(&l_Lean_Lsp_instFromJsonRange_fromJson___closed__11, &l_Lean_Lsp_instFromJsonRange_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonRange_fromJson___closed__11);
x_24 = lean_string_append(x_23, x_22);
lean_dec(x_22);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
else
{
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_26; 
lean_dec(x_15);
x_26 = !lean_is_exclusive(x_17);
if (x_26 == 0)
{
lean_ctor_set_tag(x_17, 0);
return x_17;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_17, 0);
lean_inc(x_27);
lean_dec(x_17);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_17);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_17, 0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_15);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_17, 0, x_31);
return x_17;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_17, 0);
lean_inc(x_32);
lean_dec(x_17);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_15);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_instOrdRange_ord(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = l_Lean_Lsp_instOrdPosition_ord(x_3, x_5);
if (x_7 == 1)
{
uint8_t x_8; 
x_8 = l_Lean_Lsp_instOrdPosition_ord(x_4, x_6);
if (x_8 == 1)
{
return x_8;
}
else
{
return x_8;
}
}
else
{
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instOrdRange_ord___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Lsp_instOrdRange_ord(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Lsp_instReprRange_repr___redArg___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(9u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_instReprRange_repr___redArg___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(7u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instReprRange_repr___redArg(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = ((lean_object*)(l_Lean_Lsp_instReprPosition_repr___redArg___closed__4));
x_6 = ((lean_object*)(l_Lean_Lsp_instReprRange_repr___redArg___closed__2));
x_7 = lean_obj_once(&l_Lean_Lsp_instReprRange_repr___redArg___closed__3, &l_Lean_Lsp_instReprRange_repr___redArg___closed__3_once, _init_l_Lean_Lsp_instReprRange_repr___redArg___closed__3);
x_8 = l_Lean_Lsp_instReprPosition_repr___redArg(x_3);
lean_ctor_set_tag(x_1, 4);
lean_ctor_set(x_1, 1, x_8);
lean_ctor_set(x_1, 0, x_7);
x_9 = 0;
x_10 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set_uint8(x_10, sizeof(void*)*1, x_9);
x_11 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_10);
x_12 = ((lean_object*)(l_Lean_Lsp_instReprPosition_repr___redArg___closed__8));
x_13 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_box(1);
x_15 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = ((lean_object*)(l_Lean_Lsp_instReprRange_repr___redArg___closed__4));
x_17 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_5);
x_19 = lean_obj_once(&l_Lean_Lsp_instReprRange_repr___redArg___closed__5, &l_Lean_Lsp_instReprRange_repr___redArg___closed__5_once, _init_l_Lean_Lsp_instReprRange_repr___redArg___closed__5);
x_20 = l_Lean_Lsp_instReprPosition_repr___redArg(x_4);
x_21 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set_uint8(x_22, sizeof(void*)*1, x_9);
x_23 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_23, 0, x_18);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_obj_once(&l_Lean_Lsp_instReprPosition_repr___redArg___closed__13, &l_Lean_Lsp_instReprPosition_repr___redArg___closed__13_once, _init_l_Lean_Lsp_instReprPosition_repr___redArg___closed__13);
x_25 = ((lean_object*)(l_Lean_Lsp_instReprPosition_repr___redArg___closed__14));
x_26 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
x_27 = ((lean_object*)(l_Lean_Lsp_instReprPosition_repr___redArg___closed__15));
x_28 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_29, 0, x_24);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set_uint8(x_30, sizeof(void*)*1, x_9);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_31 = lean_ctor_get(x_1, 0);
x_32 = lean_ctor_get(x_1, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_1);
x_33 = ((lean_object*)(l_Lean_Lsp_instReprPosition_repr___redArg___closed__4));
x_34 = ((lean_object*)(l_Lean_Lsp_instReprRange_repr___redArg___closed__2));
x_35 = lean_obj_once(&l_Lean_Lsp_instReprRange_repr___redArg___closed__3, &l_Lean_Lsp_instReprRange_repr___redArg___closed__3_once, _init_l_Lean_Lsp_instReprRange_repr___redArg___closed__3);
x_36 = l_Lean_Lsp_instReprPosition_repr___redArg(x_31);
x_37 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = 0;
x_39 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set_uint8(x_39, sizeof(void*)*1, x_38);
x_40 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_40, 0, x_34);
lean_ctor_set(x_40, 1, x_39);
x_41 = ((lean_object*)(l_Lean_Lsp_instReprPosition_repr___redArg___closed__8));
x_42 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_box(1);
x_44 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = ((lean_object*)(l_Lean_Lsp_instReprRange_repr___redArg___closed__4));
x_46 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_33);
x_48 = lean_obj_once(&l_Lean_Lsp_instReprRange_repr___redArg___closed__5, &l_Lean_Lsp_instReprRange_repr___redArg___closed__5_once, _init_l_Lean_Lsp_instReprRange_repr___redArg___closed__5);
x_49 = l_Lean_Lsp_instReprPosition_repr___redArg(x_32);
x_50 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set_uint8(x_51, sizeof(void*)*1, x_38);
x_52 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_52, 0, x_47);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_obj_once(&l_Lean_Lsp_instReprPosition_repr___redArg___closed__13, &l_Lean_Lsp_instReprPosition_repr___redArg___closed__13_once, _init_l_Lean_Lsp_instReprPosition_repr___redArg___closed__13);
x_54 = ((lean_object*)(l_Lean_Lsp_instReprPosition_repr___redArg___closed__14));
x_55 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_52);
x_56 = ((lean_object*)(l_Lean_Lsp_instReprPosition_repr___redArg___closed__15));
x_57 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_58, 0, x_53);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set_uint8(x_59, sizeof(void*)*1, x_38);
return x_59;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instReprRange_repr(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Lsp_instReprRange_repr___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instReprRange_repr___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Lsp_instReprRange_repr(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instLTRange(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_instLERange(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
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
l_Lean_Lsp_instLTPosition = _init_l_Lean_Lsp_instLTPosition();
lean_mark_persistent(l_Lean_Lsp_instLTPosition);
l_Lean_Lsp_instLEPosition = _init_l_Lean_Lsp_instLEPosition();
lean_mark_persistent(l_Lean_Lsp_instLEPosition);
l_Lean_Lsp_instInhabitedRange_default = _init_l_Lean_Lsp_instInhabitedRange_default();
lean_mark_persistent(l_Lean_Lsp_instInhabitedRange_default);
l_Lean_Lsp_instInhabitedRange = _init_l_Lean_Lsp_instInhabitedRange();
lean_mark_persistent(l_Lean_Lsp_instInhabitedRange);
l_Lean_Lsp_instLTRange = _init_l_Lean_Lsp_instLTRange();
lean_mark_persistent(l_Lean_Lsp_instLTRange);
l_Lean_Lsp_instLERange = _init_l_Lean_Lsp_instLERange();
lean_mark_persistent(l_Lean_Lsp_instLERange);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

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
uint8_t l_Lean_Lsp_instBEqPosition_beq(lean_object* v_x_5_, lean_object* v_x_6_){
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
LEAN_EXPORT void l_Lean_Lsp_instBEqPosition_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_5_ = stack[0].m_obj;
lean_object* v_x_6_ = stack[1].m_obj;
uint8_t v_res_13_;
v_res_13_ = l_Lean_Lsp_instBEqPosition_beq(v_x_5_, v_x_6_);
stack->m_num = v_res_13_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqPosition_beq___boxed(lean_object* v_x_14_, lean_object* v_x_15_){
_start:
{
uint8_t v_res_16_; lean_object* v_r_17_; 
v_res_16_ = l_Lean_Lsp_instBEqPosition_beq(v_x_14_, v_x_15_);
lean_dec_ref(v_x_15_);
lean_dec_ref(v_x_14_);
v_r_17_ = lean_box(v_res_16_);
return v_r_17_;
}
}
uint8_t l_Lean_Lsp_instOrdPosition_ord(lean_object* v_x_20_, lean_object* v_x_21_){
_start:
{
lean_object* v_line_22_; lean_object* v_character_23_; lean_object* v_line_24_; lean_object* v_character_25_; uint8_t v___x_26_; 
v_line_22_ = lean_ctor_get(v_x_20_, 0);
v_character_23_ = lean_ctor_get(v_x_20_, 1);
v_line_24_ = lean_ctor_get(v_x_21_, 0);
v_character_25_ = lean_ctor_get(v_x_21_, 1);
v___x_26_ = lean_nat_dec_lt(v_line_22_, v_line_24_);
if (v___x_26_ == 0)
{
uint8_t v___x_27_; 
v___x_27_ = lean_nat_dec_eq(v_line_22_, v_line_24_);
if (v___x_27_ == 0)
{
uint8_t v___x_28_; 
v___x_28_ = 2;
return v___x_28_;
}
else
{
uint8_t v___x_29_; 
v___x_29_ = lean_nat_dec_lt(v_character_23_, v_character_25_);
if (v___x_29_ == 0)
{
uint8_t v___x_30_; 
v___x_30_ = lean_nat_dec_eq(v_character_23_, v_character_25_);
if (v___x_30_ == 0)
{
uint8_t v___x_31_; 
v___x_31_ = 2;
return v___x_31_;
}
else
{
uint8_t v___x_32_; 
v___x_32_ = 1;
return v___x_32_;
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
else
{
uint8_t v___x_34_; 
v___x_34_ = 0;
return v___x_34_;
}
}
}
LEAN_EXPORT void l_Lean_Lsp_instOrdPosition_ord_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_20_ = stack[0].m_obj;
lean_object* v_x_21_ = stack[1].m_obj;
uint8_t v_res_35_;
v_res_35_ = l_Lean_Lsp_instOrdPosition_ord(v_x_20_, v_x_21_);
stack->m_num = v_res_35_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instOrdPosition_ord___boxed(lean_object* v_x_36_, lean_object* v_x_37_){
_start:
{
uint8_t v_res_38_; lean_object* v_r_39_; 
v_res_38_ = l_Lean_Lsp_instOrdPosition_ord(v_x_36_, v_x_37_);
lean_dec_ref(v_x_37_);
lean_dec_ref(v_x_36_);
v_r_39_ = lean_box(v_res_38_);
return v_r_39_;
}
}
uint64_t l_Lean_Lsp_instHashablePosition_hash(lean_object* v_x_42_){
_start:
{
lean_object* v_line_43_; lean_object* v_character_44_; uint64_t v___x_45_; uint64_t v___x_46_; uint64_t v___x_47_; uint64_t v___x_48_; uint64_t v___x_49_; 
v_line_43_ = lean_ctor_get(v_x_42_, 0);
v_character_44_ = lean_ctor_get(v_x_42_, 1);
v___x_45_ = 0ULL;
v___x_46_ = lean_uint64_of_nat(v_line_43_);
v___x_47_ = lean_uint64_mix_hash(v___x_45_, v___x_46_);
v___x_48_ = lean_uint64_of_nat(v_character_44_);
v___x_49_ = lean_uint64_mix_hash(v___x_47_, v___x_48_);
return v___x_49_;
}
}
LEAN_EXPORT void l_Lean_Lsp_instHashablePosition_hash_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_42_ = stack[0].m_obj;
uint64_t v_res_50_;
v_res_50_ = l_Lean_Lsp_instHashablePosition_hash(v_x_42_);
stack->m_num = v_res_50_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instHashablePosition_hash___boxed(lean_object* v_x_51_){
_start:
{
uint64_t v_res_52_; lean_object* v_r_53_; 
v_res_52_ = l_Lean_Lsp_instHashablePosition_hash(v_x_51_);
lean_dec_ref(v_x_51_);
v_r_53_ = lean_box_uint64(v_res_52_);
return v_r_53_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonPosition_toJson_spec__0(lean_object* v_a_56_, lean_object* v_a_57_){
_start:
{
if (lean_obj_tag(v_a_56_) == 0)
{
lean_object* v___x_58_; 
v___x_58_ = lean_array_to_list(v_a_57_);
return v___x_58_;
}
else
{
lean_object* v_head_59_; lean_object* v_tail_60_; lean_object* v___x_61_; 
v_head_59_ = lean_ctor_get(v_a_56_, 0);
lean_inc(v_head_59_);
v_tail_60_ = lean_ctor_get(v_a_56_, 1);
lean_inc(v_tail_60_);
lean_dec_ref_known(v_a_56_, 2);
v___x_61_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_57_, v_head_59_);
v_a_56_ = v_tail_60_;
v_a_57_ = v___x_61_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonPosition_toJson(lean_object* v_x_67_){
_start:
{
lean_object* v_line_68_; lean_object* v_character_69_; lean_object* v___x_71_; uint8_t v_isShared_72_; uint8_t v_isSharedCheck_91_; 
v_line_68_ = lean_ctor_get(v_x_67_, 0);
v_character_69_ = lean_ctor_get(v_x_67_, 1);
v_isSharedCheck_91_ = !lean_is_exclusive(v_x_67_);
if (v_isSharedCheck_91_ == 0)
{
v___x_71_ = v_x_67_;
v_isShared_72_ = v_isSharedCheck_91_;
goto v_resetjp_70_;
}
else
{
lean_inc(v_character_69_);
lean_inc(v_line_68_);
lean_dec(v_x_67_);
v___x_71_ = lean_box(0);
v_isShared_72_ = v_isSharedCheck_91_;
goto v_resetjp_70_;
}
v_resetjp_70_:
{
lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_77_; 
v___x_73_ = ((lean_object*)(l_Lean_Lsp_instToJsonPosition_toJson___closed__0));
v___x_74_ = l_Lean_JsonNumber_fromNat(v_line_68_);
v___x_75_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_75_, 0, v___x_74_);
if (v_isShared_72_ == 0)
{
lean_ctor_set(v___x_71_, 1, v___x_75_);
lean_ctor_set(v___x_71_, 0, v___x_73_);
v___x_77_ = v___x_71_;
goto v_reusejp_76_;
}
else
{
lean_object* v_reuseFailAlloc_90_; 
v_reuseFailAlloc_90_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_90_, 0, v___x_73_);
lean_ctor_set(v_reuseFailAlloc_90_, 1, v___x_75_);
v___x_77_ = v_reuseFailAlloc_90_;
goto v_reusejp_76_;
}
v_reusejp_76_:
{
lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_78_ = lean_box(0);
v___x_79_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_79_, 0, v___x_77_);
lean_ctor_set(v___x_79_, 1, v___x_78_);
v___x_80_ = ((lean_object*)(l_Lean_Lsp_instToJsonPosition_toJson___closed__1));
v___x_81_ = l_Lean_JsonNumber_fromNat(v_character_69_);
v___x_82_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_82_, 0, v___x_81_);
v___x_83_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_83_, 0, v___x_80_);
lean_ctor_set(v___x_83_, 1, v___x_82_);
v___x_84_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_84_, 0, v___x_83_);
lean_ctor_set(v___x_84_, 1, v___x_78_);
v___x_85_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_85_, 0, v___x_84_);
lean_ctor_set(v___x_85_, 1, v___x_78_);
v___x_86_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_86_, 0, v___x_79_);
lean_ctor_set(v___x_86_, 1, v___x_85_);
v___x_87_ = ((lean_object*)(l_Lean_Lsp_instToJsonPosition_toJson___closed__2));
v___x_88_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonPosition_toJson_spec__0(v___x_86_, v___x_87_);
v___x_89_ = l_Lean_Json_mkObj(v___x_88_);
lean_dec(v___x_88_);
return v___x_89_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPosition_fromJson_spec__0(lean_object* v_j_94_, lean_object* v_k_95_){
_start:
{
lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_96_ = l_Lean_Json_getObjValD(v_j_94_, v_k_95_);
v___x_97_ = l_Lean_Json_getNat_x3f(v___x_96_);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPosition_fromJson_spec__0___boxed(lean_object* v_j_98_, lean_object* v_k_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPosition_fromJson_spec__0(v_j_98_, v_k_99_);
lean_dec_ref(v_k_99_);
return v_res_100_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPosition_fromJson___closed__4(void){
_start:
{
uint8_t v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_108_ = 1;
v___x_109_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPosition_fromJson___closed__3));
v___x_110_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_109_, v___x_108_);
return v___x_110_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPosition_fromJson___closed__6(void){
_start:
{
lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; 
v___x_112_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPosition_fromJson___closed__5));
v___x_113_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPosition_fromJson___closed__4, &l_Lean_Lsp_instFromJsonPosition_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonPosition_fromJson___closed__4);
v___x_114_ = lean_string_append(v___x_113_, v___x_112_);
return v___x_114_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPosition_fromJson___closed__8(void){
_start:
{
uint8_t v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_117_ = 1;
v___x_118_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPosition_fromJson___closed__7));
v___x_119_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_118_, v___x_117_);
return v___x_119_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPosition_fromJson___closed__9(void){
_start:
{
lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; 
v___x_120_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPosition_fromJson___closed__8, &l_Lean_Lsp_instFromJsonPosition_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonPosition_fromJson___closed__8);
v___x_121_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPosition_fromJson___closed__6, &l_Lean_Lsp_instFromJsonPosition_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonPosition_fromJson___closed__6);
v___x_122_ = lean_string_append(v___x_121_, v___x_120_);
return v___x_122_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPosition_fromJson___closed__11(void){
_start:
{
lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_124_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPosition_fromJson___closed__10));
v___x_125_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPosition_fromJson___closed__9, &l_Lean_Lsp_instFromJsonPosition_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonPosition_fromJson___closed__9);
v___x_126_ = lean_string_append(v___x_125_, v___x_124_);
return v___x_126_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPosition_fromJson___closed__13(void){
_start:
{
uint8_t v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_129_ = 1;
v___x_130_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPosition_fromJson___closed__12));
v___x_131_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_130_, v___x_129_);
return v___x_131_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPosition_fromJson___closed__14(void){
_start:
{
lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; 
v___x_132_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPosition_fromJson___closed__13, &l_Lean_Lsp_instFromJsonPosition_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonPosition_fromJson___closed__13);
v___x_133_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPosition_fromJson___closed__6, &l_Lean_Lsp_instFromJsonPosition_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonPosition_fromJson___closed__6);
v___x_134_ = lean_string_append(v___x_133_, v___x_132_);
return v___x_134_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPosition_fromJson___closed__15(void){
_start:
{
lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_135_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPosition_fromJson___closed__10));
v___x_136_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPosition_fromJson___closed__14, &l_Lean_Lsp_instFromJsonPosition_fromJson___closed__14_once, _init_l_Lean_Lsp_instFromJsonPosition_fromJson___closed__14);
v___x_137_ = lean_string_append(v___x_136_, v___x_135_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonPosition_fromJson(lean_object* v_json_138_){
_start:
{
lean_object* v___x_139_; lean_object* v___x_140_; 
v___x_139_ = ((lean_object*)(l_Lean_Lsp_instToJsonPosition_toJson___closed__0));
lean_inc(v_json_138_);
v___x_140_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPosition_fromJson_spec__0(v_json_138_, v___x_139_);
if (lean_obj_tag(v___x_140_) == 0)
{
lean_object* v_a_141_; lean_object* v___x_143_; uint8_t v_isShared_144_; uint8_t v_isSharedCheck_150_; 
lean_dec(v_json_138_);
v_a_141_ = lean_ctor_get(v___x_140_, 0);
v_isSharedCheck_150_ = !lean_is_exclusive(v___x_140_);
if (v_isSharedCheck_150_ == 0)
{
v___x_143_ = v___x_140_;
v_isShared_144_ = v_isSharedCheck_150_;
goto v_resetjp_142_;
}
else
{
lean_inc(v_a_141_);
lean_dec(v___x_140_);
v___x_143_ = lean_box(0);
v_isShared_144_ = v_isSharedCheck_150_;
goto v_resetjp_142_;
}
v_resetjp_142_:
{
lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_148_; 
v___x_145_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPosition_fromJson___closed__11, &l_Lean_Lsp_instFromJsonPosition_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonPosition_fromJson___closed__11);
v___x_146_ = lean_string_append(v___x_145_, v_a_141_);
lean_dec(v_a_141_);
if (v_isShared_144_ == 0)
{
lean_ctor_set(v___x_143_, 0, v___x_146_);
v___x_148_ = v___x_143_;
goto v_reusejp_147_;
}
else
{
lean_object* v_reuseFailAlloc_149_; 
v_reuseFailAlloc_149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_149_, 0, v___x_146_);
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
if (lean_obj_tag(v___x_140_) == 0)
{
lean_object* v_a_151_; lean_object* v___x_153_; uint8_t v_isShared_154_; uint8_t v_isSharedCheck_158_; 
lean_dec(v_json_138_);
v_a_151_ = lean_ctor_get(v___x_140_, 0);
v_isSharedCheck_158_ = !lean_is_exclusive(v___x_140_);
if (v_isSharedCheck_158_ == 0)
{
v___x_153_ = v___x_140_;
v_isShared_154_ = v_isSharedCheck_158_;
goto v_resetjp_152_;
}
else
{
lean_inc(v_a_151_);
lean_dec(v___x_140_);
v___x_153_ = lean_box(0);
v_isShared_154_ = v_isSharedCheck_158_;
goto v_resetjp_152_;
}
v_resetjp_152_:
{
lean_object* v___x_156_; 
if (v_isShared_154_ == 0)
{
lean_ctor_set_tag(v___x_153_, 0);
v___x_156_ = v___x_153_;
goto v_reusejp_155_;
}
else
{
lean_object* v_reuseFailAlloc_157_; 
v_reuseFailAlloc_157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_157_, 0, v_a_151_);
v___x_156_ = v_reuseFailAlloc_157_;
goto v_reusejp_155_;
}
v_reusejp_155_:
{
return v___x_156_;
}
}
}
else
{
lean_object* v_a_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
v_a_159_ = lean_ctor_get(v___x_140_, 0);
lean_inc(v_a_159_);
lean_dec_ref_known(v___x_140_, 1);
v___x_160_ = ((lean_object*)(l_Lean_Lsp_instToJsonPosition_toJson___closed__1));
v___x_161_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPosition_fromJson_spec__0(v_json_138_, v___x_160_);
if (lean_obj_tag(v___x_161_) == 0)
{
lean_object* v_a_162_; lean_object* v___x_164_; uint8_t v_isShared_165_; uint8_t v_isSharedCheck_171_; 
lean_dec(v_a_159_);
v_a_162_ = lean_ctor_get(v___x_161_, 0);
v_isSharedCheck_171_ = !lean_is_exclusive(v___x_161_);
if (v_isSharedCheck_171_ == 0)
{
v___x_164_ = v___x_161_;
v_isShared_165_ = v_isSharedCheck_171_;
goto v_resetjp_163_;
}
else
{
lean_inc(v_a_162_);
lean_dec(v___x_161_);
v___x_164_ = lean_box(0);
v_isShared_165_ = v_isSharedCheck_171_;
goto v_resetjp_163_;
}
v_resetjp_163_:
{
lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_169_; 
v___x_166_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPosition_fromJson___closed__15, &l_Lean_Lsp_instFromJsonPosition_fromJson___closed__15_once, _init_l_Lean_Lsp_instFromJsonPosition_fromJson___closed__15);
v___x_167_ = lean_string_append(v___x_166_, v_a_162_);
lean_dec(v_a_162_);
if (v_isShared_165_ == 0)
{
lean_ctor_set(v___x_164_, 0, v___x_167_);
v___x_169_ = v___x_164_;
goto v_reusejp_168_;
}
else
{
lean_object* v_reuseFailAlloc_170_; 
v_reuseFailAlloc_170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v___x_167_);
v___x_169_ = v_reuseFailAlloc_170_;
goto v_reusejp_168_;
}
v_reusejp_168_:
{
return v___x_169_;
}
}
}
else
{
if (lean_obj_tag(v___x_161_) == 0)
{
lean_object* v_a_172_; lean_object* v___x_174_; uint8_t v_isShared_175_; uint8_t v_isSharedCheck_179_; 
lean_dec(v_a_159_);
v_a_172_ = lean_ctor_get(v___x_161_, 0);
v_isSharedCheck_179_ = !lean_is_exclusive(v___x_161_);
if (v_isSharedCheck_179_ == 0)
{
v___x_174_ = v___x_161_;
v_isShared_175_ = v_isSharedCheck_179_;
goto v_resetjp_173_;
}
else
{
lean_inc(v_a_172_);
lean_dec(v___x_161_);
v___x_174_ = lean_box(0);
v_isShared_175_ = v_isSharedCheck_179_;
goto v_resetjp_173_;
}
v_resetjp_173_:
{
lean_object* v___x_177_; 
if (v_isShared_175_ == 0)
{
lean_ctor_set_tag(v___x_174_, 0);
v___x_177_ = v___x_174_;
goto v_reusejp_176_;
}
else
{
lean_object* v_reuseFailAlloc_178_; 
v_reuseFailAlloc_178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_178_, 0, v_a_172_);
v___x_177_ = v_reuseFailAlloc_178_;
goto v_reusejp_176_;
}
v_reusejp_176_:
{
return v___x_177_;
}
}
}
else
{
lean_object* v_a_180_; lean_object* v___x_182_; uint8_t v_isShared_183_; uint8_t v_isSharedCheck_188_; 
v_a_180_ = lean_ctor_get(v___x_161_, 0);
v_isSharedCheck_188_ = !lean_is_exclusive(v___x_161_);
if (v_isSharedCheck_188_ == 0)
{
v___x_182_ = v___x_161_;
v_isShared_183_ = v_isSharedCheck_188_;
goto v_resetjp_181_;
}
else
{
lean_inc(v_a_180_);
lean_dec(v___x_161_);
v___x_182_ = lean_box(0);
v_isShared_183_ = v_isSharedCheck_188_;
goto v_resetjp_181_;
}
v_resetjp_181_:
{
lean_object* v___x_184_; lean_object* v___x_186_; 
v___x_184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_184_, 0, v_a_159_);
lean_ctor_set(v___x_184_, 1, v_a_180_);
if (v_isShared_183_ == 0)
{
lean_ctor_set(v___x_182_, 0, v___x_184_);
v___x_186_ = v___x_182_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_187_; 
v_reuseFailAlloc_187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_187_, 0, v___x_184_);
v___x_186_ = v_reuseFailAlloc_187_;
goto v_reusejp_185_;
}
v_reusejp_185_:
{
return v___x_186_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Lsp_instReprPosition_repr_spec__0(lean_object* v_a_191_){
_start:
{
lean_object* v___x_192_; 
v___x_192_ = lean_nat_to_int(v_a_191_);
return v___x_192_;
}
}
static lean_object* _init_l_Lean_Lsp_instReprPosition_repr___redArg___closed__6(void){
_start:
{
lean_object* v___x_205_; lean_object* v___x_206_; 
v___x_205_ = lean_unsigned_to_nat(8u);
v___x_206_ = lean_nat_to_int(v___x_205_);
return v___x_206_;
}
}
static lean_object* _init_l_Lean_Lsp_instReprPosition_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_212_; lean_object* v___x_213_; 
v___x_212_ = lean_unsigned_to_nat(13u);
v___x_213_ = lean_nat_to_int(v___x_212_);
return v___x_213_;
}
}
static lean_object* _init_l_Lean_Lsp_instReprPosition_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_215_; lean_object* v___x_216_; 
v___x_215_ = ((lean_object*)(l_Lean_Lsp_instReprPosition_repr___redArg___closed__0));
v___x_216_ = lean_string_length(v___x_215_);
return v___x_216_;
}
}
static lean_object* _init_l_Lean_Lsp_instReprPosition_repr___redArg___closed__13(void){
_start:
{
lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_217_ = lean_obj_once(&l_Lean_Lsp_instReprPosition_repr___redArg___closed__12, &l_Lean_Lsp_instReprPosition_repr___redArg___closed__12_once, _init_l_Lean_Lsp_instReprPosition_repr___redArg___closed__12);
v___x_218_ = lean_nat_to_int(v___x_217_);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instReprPosition_repr___redArg(lean_object* v_x_223_){
_start:
{
lean_object* v_line_224_; lean_object* v_character_225_; lean_object* v___x_227_; uint8_t v_isShared_228_; uint8_t v_isSharedCheck_260_; 
v_line_224_ = lean_ctor_get(v_x_223_, 0);
v_character_225_ = lean_ctor_get(v_x_223_, 1);
v_isSharedCheck_260_ = !lean_is_exclusive(v_x_223_);
if (v_isSharedCheck_260_ == 0)
{
v___x_227_ = v_x_223_;
v_isShared_228_ = v_isSharedCheck_260_;
goto v_resetjp_226_;
}
else
{
lean_inc(v_character_225_);
lean_inc(v_line_224_);
lean_dec(v_x_223_);
v___x_227_ = lean_box(0);
v_isShared_228_ = v_isSharedCheck_260_;
goto v_resetjp_226_;
}
v_resetjp_226_:
{
lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_235_; 
v___x_229_ = ((lean_object*)(l_Lean_Lsp_instReprPosition_repr___redArg___closed__4));
v___x_230_ = ((lean_object*)(l_Lean_Lsp_instReprPosition_repr___redArg___closed__5));
v___x_231_ = lean_obj_once(&l_Lean_Lsp_instReprPosition_repr___redArg___closed__6, &l_Lean_Lsp_instReprPosition_repr___redArg___closed__6_once, _init_l_Lean_Lsp_instReprPosition_repr___redArg___closed__6);
v___x_232_ = l_Nat_reprFast(v_line_224_);
v___x_233_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_233_, 0, v___x_232_);
if (v_isShared_228_ == 0)
{
lean_ctor_set_tag(v___x_227_, 4);
lean_ctor_set(v___x_227_, 1, v___x_233_);
lean_ctor_set(v___x_227_, 0, v___x_231_);
v___x_235_ = v___x_227_;
goto v_reusejp_234_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v___x_231_);
lean_ctor_set(v_reuseFailAlloc_259_, 1, v___x_233_);
v___x_235_ = v_reuseFailAlloc_259_;
goto v_reusejp_234_;
}
v_reusejp_234_:
{
uint8_t v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_236_ = 0;
v___x_237_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_237_, 0, v___x_235_);
lean_ctor_set_uint8(v___x_237_, sizeof(void*)*1, v___x_236_);
v___x_238_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_238_, 0, v___x_230_);
lean_ctor_set(v___x_238_, 1, v___x_237_);
v___x_239_ = ((lean_object*)(l_Lean_Lsp_instReprPosition_repr___redArg___closed__8));
v___x_240_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_240_, 0, v___x_238_);
lean_ctor_set(v___x_240_, 1, v___x_239_);
v___x_241_ = lean_box(1);
v___x_242_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_242_, 0, v___x_240_);
lean_ctor_set(v___x_242_, 1, v___x_241_);
v___x_243_ = ((lean_object*)(l_Lean_Lsp_instReprPosition_repr___redArg___closed__9));
v___x_244_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_244_, 0, v___x_242_);
lean_ctor_set(v___x_244_, 1, v___x_243_);
v___x_245_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_245_, 0, v___x_244_);
lean_ctor_set(v___x_245_, 1, v___x_229_);
v___x_246_ = lean_obj_once(&l_Lean_Lsp_instReprPosition_repr___redArg___closed__10, &l_Lean_Lsp_instReprPosition_repr___redArg___closed__10_once, _init_l_Lean_Lsp_instReprPosition_repr___redArg___closed__10);
v___x_247_ = l_Nat_reprFast(v_character_225_);
v___x_248_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_248_, 0, v___x_247_);
v___x_249_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_249_, 0, v___x_246_);
lean_ctor_set(v___x_249_, 1, v___x_248_);
v___x_250_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_250_, 0, v___x_249_);
lean_ctor_set_uint8(v___x_250_, sizeof(void*)*1, v___x_236_);
v___x_251_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_251_, 0, v___x_245_);
lean_ctor_set(v___x_251_, 1, v___x_250_);
v___x_252_ = lean_obj_once(&l_Lean_Lsp_instReprPosition_repr___redArg___closed__13, &l_Lean_Lsp_instReprPosition_repr___redArg___closed__13_once, _init_l_Lean_Lsp_instReprPosition_repr___redArg___closed__13);
v___x_253_ = ((lean_object*)(l_Lean_Lsp_instReprPosition_repr___redArg___closed__14));
v___x_254_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_254_, 0, v___x_253_);
lean_ctor_set(v___x_254_, 1, v___x_251_);
v___x_255_ = ((lean_object*)(l_Lean_Lsp_instReprPosition_repr___redArg___closed__15));
v___x_256_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_256_, 0, v___x_254_);
lean_ctor_set(v___x_256_, 1, v___x_255_);
v___x_257_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_257_, 0, v___x_252_);
lean_ctor_set(v___x_257_, 1, v___x_256_);
v___x_258_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_258_, 0, v___x_257_);
lean_ctor_set_uint8(v___x_258_, sizeof(void*)*1, v___x_236_);
return v___x_258_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instReprPosition_repr(lean_object* v_x_261_, lean_object* v_prec_262_){
_start:
{
lean_object* v___x_263_; 
v___x_263_ = l_Lean_Lsp_instReprPosition_repr___redArg(v_x_261_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instReprPosition_repr___boxed(lean_object* v_x_264_, lean_object* v_prec_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = l_Lean_Lsp_instReprPosition_repr(v_x_264_, v_prec_265_);
lean_dec(v_prec_265_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToStringPosition___lam__0(lean_object* v_p_272_){
_start:
{
lean_object* v_line_273_; lean_object* v_character_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; 
v_line_273_ = lean_ctor_get(v_p_272_, 0);
lean_inc(v_line_273_);
v_character_274_ = lean_ctor_get(v_p_272_, 1);
lean_inc(v_character_274_);
lean_dec_ref(v_p_272_);
v___x_275_ = ((lean_object*)(l_Lean_Lsp_instToStringPosition___lam__0___closed__0));
v___x_276_ = l_Nat_reprFast(v_line_273_);
v___x_277_ = lean_string_append(v___x_275_, v___x_276_);
lean_dec_ref(v___x_276_);
v___x_278_ = ((lean_object*)(l_Lean_Lsp_instToStringPosition___lam__0___closed__1));
v___x_279_ = lean_string_append(v___x_277_, v___x_278_);
v___x_280_ = l_Nat_reprFast(v_character_274_);
v___x_281_ = lean_string_append(v___x_279_, v___x_280_);
lean_dec_ref(v___x_280_);
v___x_282_ = ((lean_object*)(l_Lean_Lsp_instToStringPosition___lam__0___closed__2));
v___x_283_ = lean_string_append(v___x_281_, v___x_282_);
return v___x_283_;
}
}
static lean_object* _init_l_Lean_Lsp_instLTPosition(void){
_start:
{
lean_object* v___x_286_; 
v___x_286_ = lean_box(0);
return v___x_286_;
}
}
static lean_object* _init_l_Lean_Lsp_instLEPosition(void){
_start:
{
lean_object* v___x_287_; 
v___x_287_ = lean_box(0);
return v___x_287_;
}
}
uint8_t l_Lean_Lsp_instBEqRange_beq(lean_object* v_x_292_, lean_object* v_x_293_){
_start:
{
lean_object* v_start_294_; lean_object* v_end_295_; lean_object* v_start_296_; lean_object* v_end_297_; uint8_t v___x_298_; 
v_start_294_ = lean_ctor_get(v_x_292_, 0);
v_end_295_ = lean_ctor_get(v_x_292_, 1);
v_start_296_ = lean_ctor_get(v_x_293_, 0);
v_end_297_ = lean_ctor_get(v_x_293_, 1);
v___x_298_ = l_Lean_Lsp_instBEqPosition_beq(v_start_294_, v_start_296_);
if (v___x_298_ == 0)
{
return v___x_298_;
}
else
{
uint8_t v___x_299_; 
v___x_299_ = l_Lean_Lsp_instBEqPosition_beq(v_end_295_, v_end_297_);
return v___x_299_;
}
}
}
LEAN_EXPORT void l_Lean_Lsp_instBEqRange_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_292_ = stack[0].m_obj;
lean_object* v_x_293_ = stack[1].m_obj;
uint8_t v_res_300_;
v_res_300_ = l_Lean_Lsp_instBEqRange_beq(v_x_292_, v_x_293_);
stack->m_num = v_res_300_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqRange_beq___boxed(lean_object* v_x_301_, lean_object* v_x_302_){
_start:
{
uint8_t v_res_303_; lean_object* v_r_304_; 
v_res_303_ = l_Lean_Lsp_instBEqRange_beq(v_x_301_, v_x_302_);
lean_dec_ref(v_x_302_);
lean_dec_ref(v_x_301_);
v_r_304_ = lean_box(v_res_303_);
return v_r_304_;
}
}
uint64_t l_Lean_Lsp_instHashableRange_hash(lean_object* v_x_307_){
_start:
{
lean_object* v_start_308_; lean_object* v_end_309_; uint64_t v___x_310_; uint64_t v___x_311_; uint64_t v___x_312_; uint64_t v___x_313_; uint64_t v___x_314_; 
v_start_308_ = lean_ctor_get(v_x_307_, 0);
v_end_309_ = lean_ctor_get(v_x_307_, 1);
v___x_310_ = 0ULL;
v___x_311_ = l_Lean_Lsp_instHashablePosition_hash(v_start_308_);
v___x_312_ = lean_uint64_mix_hash(v___x_310_, v___x_311_);
v___x_313_ = l_Lean_Lsp_instHashablePosition_hash(v_end_309_);
v___x_314_ = lean_uint64_mix_hash(v___x_312_, v___x_313_);
return v___x_314_;
}
}
LEAN_EXPORT void l_Lean_Lsp_instHashableRange_hash_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_307_ = stack[0].m_obj;
uint64_t v_res_315_;
v_res_315_ = l_Lean_Lsp_instHashableRange_hash(v_x_307_);
stack->m_num = v_res_315_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instHashableRange_hash___boxed(lean_object* v_x_316_){
_start:
{
uint64_t v_res_317_; lean_object* v_r_318_; 
v_res_317_ = l_Lean_Lsp_instHashableRange_hash(v_x_316_);
lean_dec_ref(v_x_316_);
v_r_318_ = lean_box_uint64(v_res_317_);
return v_r_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRange_toJson(lean_object* v_x_323_){
_start:
{
lean_object* v_start_324_; lean_object* v_end_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_345_; 
v_start_324_ = lean_ctor_get(v_x_323_, 0);
v_end_325_ = lean_ctor_get(v_x_323_, 1);
v_isSharedCheck_345_ = !lean_is_exclusive(v_x_323_);
if (v_isSharedCheck_345_ == 0)
{
v___x_327_ = v_x_323_;
v_isShared_328_ = v_isSharedCheck_345_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_end_325_);
lean_inc(v_start_324_);
lean_dec(v_x_323_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_345_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_332_; 
v___x_329_ = ((lean_object*)(l_Lean_Lsp_instToJsonRange_toJson___closed__0));
v___x_330_ = l_Lean_Lsp_instToJsonPosition_toJson(v_start_324_);
if (v_isShared_328_ == 0)
{
lean_ctor_set(v___x_327_, 1, v___x_330_);
lean_ctor_set(v___x_327_, 0, v___x_329_);
v___x_332_ = v___x_327_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v___x_329_);
lean_ctor_set(v_reuseFailAlloc_344_, 1, v___x_330_);
v___x_332_ = v_reuseFailAlloc_344_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_333_ = lean_box(0);
v___x_334_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_334_, 0, v___x_332_);
lean_ctor_set(v___x_334_, 1, v___x_333_);
v___x_335_ = ((lean_object*)(l_Lean_Lsp_instToJsonRange_toJson___closed__1));
v___x_336_ = l_Lean_Lsp_instToJsonPosition_toJson(v_end_325_);
v___x_337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_337_, 0, v___x_335_);
lean_ctor_set(v___x_337_, 1, v___x_336_);
v___x_338_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_338_, 0, v___x_337_);
lean_ctor_set(v___x_338_, 1, v___x_333_);
v___x_339_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_339_, 0, v___x_338_);
lean_ctor_set(v___x_339_, 1, v___x_333_);
v___x_340_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_340_, 0, v___x_334_);
lean_ctor_set(v___x_340_, 1, v___x_339_);
v___x_341_ = ((lean_object*)(l_Lean_Lsp_instToJsonPosition_toJson___closed__2));
v___x_342_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonPosition_toJson_spec__0(v___x_340_, v___x_341_);
v___x_343_ = l_Lean_Json_mkObj(v___x_342_);
lean_dec(v___x_342_);
return v___x_343_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRange_fromJson_spec__0(lean_object* v_j_348_, lean_object* v_k_349_){
_start:
{
lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_350_ = l_Lean_Json_getObjValD(v_j_348_, v_k_349_);
v___x_351_ = l_Lean_Lsp_instFromJsonPosition_fromJson(v___x_350_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRange_fromJson_spec__0___boxed(lean_object* v_j_352_, lean_object* v_k_353_){
_start:
{
lean_object* v_res_354_; 
v_res_354_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRange_fromJson_spec__0(v_j_352_, v_k_353_);
lean_dec_ref(v_k_353_);
return v_res_354_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRange_fromJson___closed__2(void){
_start:
{
uint8_t v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; 
v___x_360_ = 1;
v___x_361_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRange_fromJson___closed__1));
v___x_362_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_361_, v___x_360_);
return v___x_362_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRange_fromJson___closed__3(void){
_start:
{
lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_363_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPosition_fromJson___closed__5));
v___x_364_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRange_fromJson___closed__2, &l_Lean_Lsp_instFromJsonRange_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonRange_fromJson___closed__2);
v___x_365_ = lean_string_append(v___x_364_, v___x_363_);
return v___x_365_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRange_fromJson___closed__5(void){
_start:
{
uint8_t v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_368_ = 1;
v___x_369_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRange_fromJson___closed__4));
v___x_370_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_369_, v___x_368_);
return v___x_370_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRange_fromJson___closed__6(void){
_start:
{
lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_371_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRange_fromJson___closed__5, &l_Lean_Lsp_instFromJsonRange_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonRange_fromJson___closed__5);
v___x_372_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRange_fromJson___closed__3, &l_Lean_Lsp_instFromJsonRange_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonRange_fromJson___closed__3);
v___x_373_ = lean_string_append(v___x_372_, v___x_371_);
return v___x_373_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRange_fromJson___closed__7(void){
_start:
{
lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_374_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPosition_fromJson___closed__10));
v___x_375_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRange_fromJson___closed__6, &l_Lean_Lsp_instFromJsonRange_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonRange_fromJson___closed__6);
v___x_376_ = lean_string_append(v___x_375_, v___x_374_);
return v___x_376_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRange_fromJson___closed__9(void){
_start:
{
uint8_t v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_379_ = 1;
v___x_380_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRange_fromJson___closed__8));
v___x_381_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_380_, v___x_379_);
return v___x_381_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRange_fromJson___closed__10(void){
_start:
{
lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; 
v___x_382_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRange_fromJson___closed__9, &l_Lean_Lsp_instFromJsonRange_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonRange_fromJson___closed__9);
v___x_383_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRange_fromJson___closed__3, &l_Lean_Lsp_instFromJsonRange_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonRange_fromJson___closed__3);
v___x_384_ = lean_string_append(v___x_383_, v___x_382_);
return v___x_384_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRange_fromJson___closed__11(void){
_start:
{
lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; 
v___x_385_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPosition_fromJson___closed__10));
v___x_386_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRange_fromJson___closed__10, &l_Lean_Lsp_instFromJsonRange_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonRange_fromJson___closed__10);
v___x_387_ = lean_string_append(v___x_386_, v___x_385_);
return v___x_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonRange_fromJson(lean_object* v_json_388_){
_start:
{
lean_object* v___x_389_; lean_object* v___x_390_; 
v___x_389_ = ((lean_object*)(l_Lean_Lsp_instToJsonRange_toJson___closed__0));
lean_inc(v_json_388_);
v___x_390_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRange_fromJson_spec__0(v_json_388_, v___x_389_);
if (lean_obj_tag(v___x_390_) == 0)
{
lean_object* v_a_391_; lean_object* v___x_393_; uint8_t v_isShared_394_; uint8_t v_isSharedCheck_400_; 
lean_dec(v_json_388_);
v_a_391_ = lean_ctor_get(v___x_390_, 0);
v_isSharedCheck_400_ = !lean_is_exclusive(v___x_390_);
if (v_isSharedCheck_400_ == 0)
{
v___x_393_ = v___x_390_;
v_isShared_394_ = v_isSharedCheck_400_;
goto v_resetjp_392_;
}
else
{
lean_inc(v_a_391_);
lean_dec(v___x_390_);
v___x_393_ = lean_box(0);
v_isShared_394_ = v_isSharedCheck_400_;
goto v_resetjp_392_;
}
v_resetjp_392_:
{
lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_398_; 
v___x_395_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRange_fromJson___closed__7, &l_Lean_Lsp_instFromJsonRange_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonRange_fromJson___closed__7);
v___x_396_ = lean_string_append(v___x_395_, v_a_391_);
lean_dec(v_a_391_);
if (v_isShared_394_ == 0)
{
lean_ctor_set(v___x_393_, 0, v___x_396_);
v___x_398_ = v___x_393_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v___x_396_);
v___x_398_ = v_reuseFailAlloc_399_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
return v___x_398_;
}
}
}
else
{
if (lean_obj_tag(v___x_390_) == 0)
{
lean_object* v_a_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_408_; 
lean_dec(v_json_388_);
v_a_401_ = lean_ctor_get(v___x_390_, 0);
v_isSharedCheck_408_ = !lean_is_exclusive(v___x_390_);
if (v_isSharedCheck_408_ == 0)
{
v___x_403_ = v___x_390_;
v_isShared_404_ = v_isSharedCheck_408_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_a_401_);
lean_dec(v___x_390_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_408_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
lean_object* v___x_406_; 
if (v_isShared_404_ == 0)
{
lean_ctor_set_tag(v___x_403_, 0);
v___x_406_ = v___x_403_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v_a_401_);
v___x_406_ = v_reuseFailAlloc_407_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
return v___x_406_;
}
}
}
else
{
lean_object* v_a_409_; lean_object* v___x_410_; lean_object* v___x_411_; 
v_a_409_ = lean_ctor_get(v___x_390_, 0);
lean_inc(v_a_409_);
lean_dec_ref_known(v___x_390_, 1);
v___x_410_ = ((lean_object*)(l_Lean_Lsp_instToJsonRange_toJson___closed__1));
v___x_411_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRange_fromJson_spec__0(v_json_388_, v___x_410_);
if (lean_obj_tag(v___x_411_) == 0)
{
lean_object* v_a_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_421_; 
lean_dec(v_a_409_);
v_a_412_ = lean_ctor_get(v___x_411_, 0);
v_isSharedCheck_421_ = !lean_is_exclusive(v___x_411_);
if (v_isSharedCheck_421_ == 0)
{
v___x_414_ = v___x_411_;
v_isShared_415_ = v_isSharedCheck_421_;
goto v_resetjp_413_;
}
else
{
lean_inc(v_a_412_);
lean_dec(v___x_411_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_421_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_419_; 
v___x_416_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRange_fromJson___closed__11, &l_Lean_Lsp_instFromJsonRange_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonRange_fromJson___closed__11);
v___x_417_ = lean_string_append(v___x_416_, v_a_412_);
lean_dec(v_a_412_);
if (v_isShared_415_ == 0)
{
lean_ctor_set(v___x_414_, 0, v___x_417_);
v___x_419_ = v___x_414_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v___x_417_);
v___x_419_ = v_reuseFailAlloc_420_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
return v___x_419_;
}
}
}
else
{
if (lean_obj_tag(v___x_411_) == 0)
{
lean_object* v_a_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_429_; 
lean_dec(v_a_409_);
v_a_422_ = lean_ctor_get(v___x_411_, 0);
v_isSharedCheck_429_ = !lean_is_exclusive(v___x_411_);
if (v_isSharedCheck_429_ == 0)
{
v___x_424_ = v___x_411_;
v_isShared_425_ = v_isSharedCheck_429_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_a_422_);
lean_dec(v___x_411_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_429_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
lean_object* v___x_427_; 
if (v_isShared_425_ == 0)
{
lean_ctor_set_tag(v___x_424_, 0);
v___x_427_ = v___x_424_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v_a_422_);
v___x_427_ = v_reuseFailAlloc_428_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
return v___x_427_;
}
}
}
else
{
lean_object* v_a_430_; lean_object* v___x_432_; uint8_t v_isShared_433_; uint8_t v_isSharedCheck_438_; 
v_a_430_ = lean_ctor_get(v___x_411_, 0);
v_isSharedCheck_438_ = !lean_is_exclusive(v___x_411_);
if (v_isSharedCheck_438_ == 0)
{
v___x_432_ = v___x_411_;
v_isShared_433_ = v_isSharedCheck_438_;
goto v_resetjp_431_;
}
else
{
lean_inc(v_a_430_);
lean_dec(v___x_411_);
v___x_432_ = lean_box(0);
v_isShared_433_ = v_isSharedCheck_438_;
goto v_resetjp_431_;
}
v_resetjp_431_:
{
lean_object* v___x_434_; lean_object* v___x_436_; 
v___x_434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_434_, 0, v_a_409_);
lean_ctor_set(v___x_434_, 1, v_a_430_);
if (v_isShared_433_ == 0)
{
lean_ctor_set(v___x_432_, 0, v___x_434_);
v___x_436_ = v___x_432_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v___x_434_);
v___x_436_ = v_reuseFailAlloc_437_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
return v___x_436_;
}
}
}
}
}
}
}
}
uint8_t l_Lean_Lsp_instOrdRange_ord(lean_object* v_x_441_, lean_object* v_x_442_){
_start:
{
lean_object* v_start_443_; lean_object* v_end_444_; lean_object* v_start_445_; lean_object* v_end_446_; uint8_t v___x_447_; 
v_start_443_ = lean_ctor_get(v_x_441_, 0);
v_end_444_ = lean_ctor_get(v_x_441_, 1);
v_start_445_ = lean_ctor_get(v_x_442_, 0);
v_end_446_ = lean_ctor_get(v_x_442_, 1);
v___x_447_ = l_Lean_Lsp_instOrdPosition_ord(v_start_443_, v_start_445_);
if (v___x_447_ == 1)
{
uint8_t v___x_448_; 
v___x_448_ = l_Lean_Lsp_instOrdPosition_ord(v_end_444_, v_end_446_);
return v___x_448_;
}
else
{
return v___x_447_;
}
}
}
LEAN_EXPORT void l_Lean_Lsp_instOrdRange_ord_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_441_ = stack[0].m_obj;
lean_object* v_x_442_ = stack[1].m_obj;
uint8_t v_res_449_;
v_res_449_ = l_Lean_Lsp_instOrdRange_ord(v_x_441_, v_x_442_);
stack->m_num = v_res_449_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instOrdRange_ord___boxed(lean_object* v_x_450_, lean_object* v_x_451_){
_start:
{
uint8_t v_res_452_; lean_object* v_r_453_; 
v_res_452_ = l_Lean_Lsp_instOrdRange_ord(v_x_450_, v_x_451_);
lean_dec_ref(v_x_451_);
lean_dec_ref(v_x_450_);
v_r_453_ = lean_box(v_res_452_);
return v_r_453_;
}
}
static lean_object* _init_l_Lean_Lsp_instReprRange_repr___redArg___closed__3(void){
_start:
{
lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_464_ = lean_unsigned_to_nat(9u);
v___x_465_ = lean_nat_to_int(v___x_464_);
return v___x_465_;
}
}
static lean_object* _init_l_Lean_Lsp_instReprRange_repr___redArg___closed__5(void){
_start:
{
lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_468_ = lean_unsigned_to_nat(7u);
v___x_469_ = lean_nat_to_int(v___x_468_);
return v___x_469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instReprRange_repr___redArg(lean_object* v_x_470_){
_start:
{
lean_object* v_start_471_; lean_object* v_end_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_505_; 
v_start_471_ = lean_ctor_get(v_x_470_, 0);
v_end_472_ = lean_ctor_get(v_x_470_, 1);
v_isSharedCheck_505_ = !lean_is_exclusive(v_x_470_);
if (v_isSharedCheck_505_ == 0)
{
v___x_474_ = v_x_470_;
v_isShared_475_ = v_isSharedCheck_505_;
goto v_resetjp_473_;
}
else
{
lean_inc(v_end_472_);
lean_inc(v_start_471_);
lean_dec(v_x_470_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_505_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_481_; 
v___x_476_ = ((lean_object*)(l_Lean_Lsp_instReprPosition_repr___redArg___closed__4));
v___x_477_ = ((lean_object*)(l_Lean_Lsp_instReprRange_repr___redArg___closed__2));
v___x_478_ = lean_obj_once(&l_Lean_Lsp_instReprRange_repr___redArg___closed__3, &l_Lean_Lsp_instReprRange_repr___redArg___closed__3_once, _init_l_Lean_Lsp_instReprRange_repr___redArg___closed__3);
v___x_479_ = l_Lean_Lsp_instReprPosition_repr___redArg(v_start_471_);
if (v_isShared_475_ == 0)
{
lean_ctor_set_tag(v___x_474_, 4);
lean_ctor_set(v___x_474_, 1, v___x_479_);
lean_ctor_set(v___x_474_, 0, v___x_478_);
v___x_481_ = v___x_474_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v___x_478_);
lean_ctor_set(v_reuseFailAlloc_504_, 1, v___x_479_);
v___x_481_ = v_reuseFailAlloc_504_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
uint8_t v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_482_ = 0;
v___x_483_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_483_, 0, v___x_481_);
lean_ctor_set_uint8(v___x_483_, sizeof(void*)*1, v___x_482_);
v___x_484_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_484_, 0, v___x_477_);
lean_ctor_set(v___x_484_, 1, v___x_483_);
v___x_485_ = ((lean_object*)(l_Lean_Lsp_instReprPosition_repr___redArg___closed__8));
v___x_486_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_486_, 0, v___x_484_);
lean_ctor_set(v___x_486_, 1, v___x_485_);
v___x_487_ = lean_box(1);
v___x_488_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_488_, 0, v___x_486_);
lean_ctor_set(v___x_488_, 1, v___x_487_);
v___x_489_ = ((lean_object*)(l_Lean_Lsp_instReprRange_repr___redArg___closed__4));
v___x_490_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_490_, 0, v___x_488_);
lean_ctor_set(v___x_490_, 1, v___x_489_);
v___x_491_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_491_, 0, v___x_490_);
lean_ctor_set(v___x_491_, 1, v___x_476_);
v___x_492_ = lean_obj_once(&l_Lean_Lsp_instReprRange_repr___redArg___closed__5, &l_Lean_Lsp_instReprRange_repr___redArg___closed__5_once, _init_l_Lean_Lsp_instReprRange_repr___redArg___closed__5);
v___x_493_ = l_Lean_Lsp_instReprPosition_repr___redArg(v_end_472_);
v___x_494_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_494_, 0, v___x_492_);
lean_ctor_set(v___x_494_, 1, v___x_493_);
v___x_495_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_495_, 0, v___x_494_);
lean_ctor_set_uint8(v___x_495_, sizeof(void*)*1, v___x_482_);
v___x_496_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_496_, 0, v___x_491_);
lean_ctor_set(v___x_496_, 1, v___x_495_);
v___x_497_ = lean_obj_once(&l_Lean_Lsp_instReprPosition_repr___redArg___closed__13, &l_Lean_Lsp_instReprPosition_repr___redArg___closed__13_once, _init_l_Lean_Lsp_instReprPosition_repr___redArg___closed__13);
v___x_498_ = ((lean_object*)(l_Lean_Lsp_instReprPosition_repr___redArg___closed__14));
v___x_499_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_499_, 0, v___x_498_);
lean_ctor_set(v___x_499_, 1, v___x_496_);
v___x_500_ = ((lean_object*)(l_Lean_Lsp_instReprPosition_repr___redArg___closed__15));
v___x_501_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_501_, 0, v___x_499_);
lean_ctor_set(v___x_501_, 1, v___x_500_);
v___x_502_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_502_, 0, v___x_497_);
lean_ctor_set(v___x_502_, 1, v___x_501_);
v___x_503_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_503_, 0, v___x_502_);
lean_ctor_set_uint8(v___x_503_, sizeof(void*)*1, v___x_482_);
return v___x_503_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instReprRange_repr(lean_object* v_x_506_, lean_object* v_prec_507_){
_start:
{
lean_object* v___x_508_; 
v___x_508_ = l_Lean_Lsp_instReprRange_repr___redArg(v_x_506_);
return v___x_508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instReprRange_repr___boxed(lean_object* v_x_509_, lean_object* v_prec_510_){
_start:
{
lean_object* v_res_511_; 
v_res_511_ = l_Lean_Lsp_instReprRange_repr(v_x_509_, v_prec_510_);
lean_dec(v_prec_510_);
return v_res_511_;
}
}
static lean_object* _init_l_Lean_Lsp_instLTRange(void){
_start:
{
lean_object* v___x_514_; 
v___x_514_ = lean_box(0);
return v___x_514_;
}
}
static lean_object* _init_l_Lean_Lsp_instLERange(void){
_start:
{
lean_object* v___x_515_; 
v___x_515_ = lean_box(0);
return v___x_515_;
}
}
lean_object* runtime_initialize_Lean_Data_Json_FromToJson_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_Lsp_BasicAux(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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

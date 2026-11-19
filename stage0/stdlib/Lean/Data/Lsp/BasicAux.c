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
lean_dec_ref_known(v_a_53_, 2);
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
lean_dec(v___x_85_);
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
lean_object* v_a_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v_a_148_ = lean_ctor_get(v___x_137_, 0);
lean_inc(v_a_148_);
lean_dec_ref_known(v___x_137_, 1);
v___x_149_ = ((lean_object*)(l_Lean_Lsp_instToJsonPosition_toJson___closed__1));
v___x_150_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPosition_fromJson_spec__0(v_json_135_, v___x_149_);
if (lean_obj_tag(v___x_150_) == 0)
{
lean_object* v_a_151_; lean_object* v___x_153_; uint8_t v_isShared_154_; uint8_t v_isSharedCheck_160_; 
lean_dec(v_a_148_);
v_a_151_ = lean_ctor_get(v___x_150_, 0);
v_isSharedCheck_160_ = !lean_is_exclusive(v___x_150_);
if (v_isSharedCheck_160_ == 0)
{
v___x_153_ = v___x_150_;
v_isShared_154_ = v_isSharedCheck_160_;
goto v_resetjp_152_;
}
else
{
lean_inc(v_a_151_);
lean_dec(v___x_150_);
v___x_153_ = lean_box(0);
v_isShared_154_ = v_isSharedCheck_160_;
goto v_resetjp_152_;
}
v_resetjp_152_:
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_158_; 
v___x_155_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPosition_fromJson___closed__15, &l_Lean_Lsp_instFromJsonPosition_fromJson___closed__15_once, _init_l_Lean_Lsp_instFromJsonPosition_fromJson___closed__15);
v___x_156_ = lean_string_append(v___x_155_, v_a_151_);
lean_dec(v_a_151_);
if (v_isShared_154_ == 0)
{
lean_ctor_set(v___x_153_, 0, v___x_156_);
v___x_158_ = v___x_153_;
goto v_reusejp_157_;
}
else
{
lean_object* v_reuseFailAlloc_159_; 
v_reuseFailAlloc_159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_159_, 0, v___x_156_);
v___x_158_ = v_reuseFailAlloc_159_;
goto v_reusejp_157_;
}
v_reusejp_157_:
{
return v___x_158_;
}
}
}
else
{
lean_object* v_a_161_; lean_object* v___x_163_; uint8_t v_isShared_164_; uint8_t v_isSharedCheck_169_; 
v_a_161_ = lean_ctor_get(v___x_150_, 0);
v_isSharedCheck_169_ = !lean_is_exclusive(v___x_150_);
if (v_isSharedCheck_169_ == 0)
{
v___x_163_ = v___x_150_;
v_isShared_164_ = v_isSharedCheck_169_;
goto v_resetjp_162_;
}
else
{
lean_inc(v_a_161_);
lean_dec(v___x_150_);
v___x_163_ = lean_box(0);
v_isShared_164_ = v_isSharedCheck_169_;
goto v_resetjp_162_;
}
v_resetjp_162_:
{
lean_object* v___x_165_; lean_object* v___x_167_; 
v___x_165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_165_, 0, v_a_148_);
lean_ctor_set(v___x_165_, 1, v_a_161_);
if (v_isShared_164_ == 0)
{
lean_ctor_set(v___x_163_, 0, v___x_165_);
v___x_167_ = v___x_163_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v___x_165_);
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
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Lsp_instReprPosition_repr_spec__0(lean_object* v_a_172_){
_start:
{
lean_object* v___x_173_; 
v___x_173_ = lean_nat_to_int(v_a_172_);
return v___x_173_;
}
}
static lean_object* _init_l_Lean_Lsp_instReprPosition_repr___redArg___closed__6(void){
_start:
{
lean_object* v___x_186_; lean_object* v___x_187_; 
v___x_186_ = lean_unsigned_to_nat(8u);
v___x_187_ = lean_nat_to_int(v___x_186_);
return v___x_187_;
}
}
static lean_object* _init_l_Lean_Lsp_instReprPosition_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_193_ = lean_unsigned_to_nat(13u);
v___x_194_ = lean_nat_to_int(v___x_193_);
return v___x_194_;
}
}
static lean_object* _init_l_Lean_Lsp_instReprPosition_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_196_ = ((lean_object*)(l_Lean_Lsp_instReprPosition_repr___redArg___closed__0));
v___x_197_ = lean_string_length(v___x_196_);
return v___x_197_;
}
}
static lean_object* _init_l_Lean_Lsp_instReprPosition_repr___redArg___closed__13(void){
_start:
{
lean_object* v___x_198_; lean_object* v___x_199_; 
v___x_198_ = lean_obj_once(&l_Lean_Lsp_instReprPosition_repr___redArg___closed__12, &l_Lean_Lsp_instReprPosition_repr___redArg___closed__12_once, _init_l_Lean_Lsp_instReprPosition_repr___redArg___closed__12);
v___x_199_ = lean_nat_to_int(v___x_198_);
return v___x_199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instReprPosition_repr___redArg(lean_object* v_x_204_){
_start:
{
lean_object* v_line_205_; lean_object* v_character_206_; lean_object* v___x_208_; uint8_t v_isShared_209_; uint8_t v_isSharedCheck_241_; 
v_line_205_ = lean_ctor_get(v_x_204_, 0);
v_character_206_ = lean_ctor_get(v_x_204_, 1);
v_isSharedCheck_241_ = !lean_is_exclusive(v_x_204_);
if (v_isSharedCheck_241_ == 0)
{
v___x_208_ = v_x_204_;
v_isShared_209_ = v_isSharedCheck_241_;
goto v_resetjp_207_;
}
else
{
lean_inc(v_character_206_);
lean_inc(v_line_205_);
lean_dec(v_x_204_);
v___x_208_ = lean_box(0);
v_isShared_209_ = v_isSharedCheck_241_;
goto v_resetjp_207_;
}
v_resetjp_207_:
{
lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_216_; 
v___x_210_ = ((lean_object*)(l_Lean_Lsp_instReprPosition_repr___redArg___closed__4));
v___x_211_ = ((lean_object*)(l_Lean_Lsp_instReprPosition_repr___redArg___closed__5));
v___x_212_ = lean_obj_once(&l_Lean_Lsp_instReprPosition_repr___redArg___closed__6, &l_Lean_Lsp_instReprPosition_repr___redArg___closed__6_once, _init_l_Lean_Lsp_instReprPosition_repr___redArg___closed__6);
v___x_213_ = l_Nat_reprFast(v_line_205_);
v___x_214_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_214_, 0, v___x_213_);
if (v_isShared_209_ == 0)
{
lean_ctor_set_tag(v___x_208_, 4);
lean_ctor_set(v___x_208_, 1, v___x_214_);
lean_ctor_set(v___x_208_, 0, v___x_212_);
v___x_216_ = v___x_208_;
goto v_reusejp_215_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v___x_212_);
lean_ctor_set(v_reuseFailAlloc_240_, 1, v___x_214_);
v___x_216_ = v_reuseFailAlloc_240_;
goto v_reusejp_215_;
}
v_reusejp_215_:
{
uint8_t v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_217_ = 0;
v___x_218_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_218_, 0, v___x_216_);
lean_ctor_set_uint8(v___x_218_, sizeof(void*)*1, v___x_217_);
v___x_219_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_219_, 0, v___x_211_);
lean_ctor_set(v___x_219_, 1, v___x_218_);
v___x_220_ = ((lean_object*)(l_Lean_Lsp_instReprPosition_repr___redArg___closed__8));
v___x_221_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_221_, 0, v___x_219_);
lean_ctor_set(v___x_221_, 1, v___x_220_);
v___x_222_ = lean_box(1);
v___x_223_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_223_, 0, v___x_221_);
lean_ctor_set(v___x_223_, 1, v___x_222_);
v___x_224_ = ((lean_object*)(l_Lean_Lsp_instReprPosition_repr___redArg___closed__9));
v___x_225_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_225_, 0, v___x_223_);
lean_ctor_set(v___x_225_, 1, v___x_224_);
v___x_226_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_226_, 0, v___x_225_);
lean_ctor_set(v___x_226_, 1, v___x_210_);
v___x_227_ = lean_obj_once(&l_Lean_Lsp_instReprPosition_repr___redArg___closed__10, &l_Lean_Lsp_instReprPosition_repr___redArg___closed__10_once, _init_l_Lean_Lsp_instReprPosition_repr___redArg___closed__10);
v___x_228_ = l_Nat_reprFast(v_character_206_);
v___x_229_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_229_, 0, v___x_228_);
v___x_230_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_230_, 0, v___x_227_);
lean_ctor_set(v___x_230_, 1, v___x_229_);
v___x_231_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_231_, 0, v___x_230_);
lean_ctor_set_uint8(v___x_231_, sizeof(void*)*1, v___x_217_);
v___x_232_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_232_, 0, v___x_226_);
lean_ctor_set(v___x_232_, 1, v___x_231_);
v___x_233_ = lean_obj_once(&l_Lean_Lsp_instReprPosition_repr___redArg___closed__13, &l_Lean_Lsp_instReprPosition_repr___redArg___closed__13_once, _init_l_Lean_Lsp_instReprPosition_repr___redArg___closed__13);
v___x_234_ = ((lean_object*)(l_Lean_Lsp_instReprPosition_repr___redArg___closed__14));
v___x_235_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_235_, 0, v___x_234_);
lean_ctor_set(v___x_235_, 1, v___x_232_);
v___x_236_ = ((lean_object*)(l_Lean_Lsp_instReprPosition_repr___redArg___closed__15));
v___x_237_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_237_, 0, v___x_235_);
lean_ctor_set(v___x_237_, 1, v___x_236_);
v___x_238_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_238_, 0, v___x_233_);
lean_ctor_set(v___x_238_, 1, v___x_237_);
v___x_239_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_239_, 0, v___x_238_);
lean_ctor_set_uint8(v___x_239_, sizeof(void*)*1, v___x_217_);
return v___x_239_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instReprPosition_repr(lean_object* v_x_242_, lean_object* v_prec_243_){
_start:
{
lean_object* v___x_244_; 
v___x_244_ = l_Lean_Lsp_instReprPosition_repr___redArg(v_x_242_);
return v___x_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instReprPosition_repr___boxed(lean_object* v_x_245_, lean_object* v_prec_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = l_Lean_Lsp_instReprPosition_repr(v_x_245_, v_prec_246_);
lean_dec(v_prec_246_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToStringPosition___lam__0(lean_object* v_p_253_){
_start:
{
lean_object* v_line_254_; lean_object* v_character_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; 
v_line_254_ = lean_ctor_get(v_p_253_, 0);
lean_inc(v_line_254_);
v_character_255_ = lean_ctor_get(v_p_253_, 1);
lean_inc(v_character_255_);
lean_dec_ref(v_p_253_);
v___x_256_ = ((lean_object*)(l_Lean_Lsp_instToStringPosition___lam__0___closed__0));
v___x_257_ = l_Nat_reprFast(v_line_254_);
v___x_258_ = lean_string_append(v___x_256_, v___x_257_);
lean_dec_ref(v___x_257_);
v___x_259_ = ((lean_object*)(l_Lean_Lsp_instToStringPosition___lam__0___closed__1));
v___x_260_ = lean_string_append(v___x_258_, v___x_259_);
v___x_261_ = l_Nat_reprFast(v_character_255_);
v___x_262_ = lean_string_append(v___x_260_, v___x_261_);
lean_dec_ref(v___x_261_);
v___x_263_ = ((lean_object*)(l_Lean_Lsp_instToStringPosition___lam__0___closed__2));
v___x_264_ = lean_string_append(v___x_262_, v___x_263_);
return v___x_264_;
}
}
static lean_object* _init_l_Lean_Lsp_instLTPosition(void){
_start:
{
lean_object* v___x_267_; 
v___x_267_ = lean_box(0);
return v___x_267_;
}
}
static lean_object* _init_l_Lean_Lsp_instLEPosition(void){
_start:
{
lean_object* v___x_268_; 
v___x_268_ = lean_box(0);
return v___x_268_;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_instBEqRange_beq(lean_object* v_x_273_, lean_object* v_x_274_){
_start:
{
lean_object* v_start_275_; lean_object* v_end_276_; lean_object* v_start_277_; lean_object* v_end_278_; uint8_t v___x_279_; 
v_start_275_ = lean_ctor_get(v_x_273_, 0);
v_end_276_ = lean_ctor_get(v_x_273_, 1);
v_start_277_ = lean_ctor_get(v_x_274_, 0);
v_end_278_ = lean_ctor_get(v_x_274_, 1);
v___x_279_ = l_Lean_Lsp_instBEqPosition_beq(v_start_275_, v_start_277_);
if (v___x_279_ == 0)
{
return v___x_279_;
}
else
{
uint8_t v___x_280_; 
v___x_280_ = l_Lean_Lsp_instBEqPosition_beq(v_end_276_, v_end_278_);
return v___x_280_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqRange_beq___boxed(lean_object* v_x_281_, lean_object* v_x_282_){
_start:
{
uint8_t v_res_283_; lean_object* v_r_284_; 
v_res_283_ = l_Lean_Lsp_instBEqRange_beq(v_x_281_, v_x_282_);
lean_dec_ref(v_x_282_);
lean_dec_ref(v_x_281_);
v_r_284_ = lean_box(v_res_283_);
return v_r_284_;
}
}
LEAN_EXPORT uint64_t l_Lean_Lsp_instHashableRange_hash(lean_object* v_x_287_){
_start:
{
lean_object* v_start_288_; lean_object* v_end_289_; uint64_t v___x_290_; uint64_t v___x_291_; uint64_t v___x_292_; uint64_t v___x_293_; uint64_t v___x_294_; 
v_start_288_ = lean_ctor_get(v_x_287_, 0);
v_end_289_ = lean_ctor_get(v_x_287_, 1);
v___x_290_ = 0ULL;
v___x_291_ = l_Lean_Lsp_instHashablePosition_hash(v_start_288_);
v___x_292_ = lean_uint64_mix_hash(v___x_290_, v___x_291_);
v___x_293_ = l_Lean_Lsp_instHashablePosition_hash(v_end_289_);
v___x_294_ = lean_uint64_mix_hash(v___x_292_, v___x_293_);
return v___x_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instHashableRange_hash___boxed(lean_object* v_x_295_){
_start:
{
uint64_t v_res_296_; lean_object* v_r_297_; 
v_res_296_ = l_Lean_Lsp_instHashableRange_hash(v_x_295_);
lean_dec_ref(v_x_295_);
v_r_297_ = lean_box_uint64(v_res_296_);
return v_r_297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRange_toJson(lean_object* v_x_302_){
_start:
{
lean_object* v_start_303_; lean_object* v_end_304_; lean_object* v___x_306_; uint8_t v_isShared_307_; uint8_t v_isSharedCheck_324_; 
v_start_303_ = lean_ctor_get(v_x_302_, 0);
v_end_304_ = lean_ctor_get(v_x_302_, 1);
v_isSharedCheck_324_ = !lean_is_exclusive(v_x_302_);
if (v_isSharedCheck_324_ == 0)
{
v___x_306_ = v_x_302_;
v_isShared_307_ = v_isSharedCheck_324_;
goto v_resetjp_305_;
}
else
{
lean_inc(v_end_304_);
lean_inc(v_start_303_);
lean_dec(v_x_302_);
v___x_306_ = lean_box(0);
v_isShared_307_ = v_isSharedCheck_324_;
goto v_resetjp_305_;
}
v_resetjp_305_:
{
lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_311_; 
v___x_308_ = ((lean_object*)(l_Lean_Lsp_instToJsonRange_toJson___closed__0));
v___x_309_ = l_Lean_Lsp_instToJsonPosition_toJson(v_start_303_);
if (v_isShared_307_ == 0)
{
lean_ctor_set(v___x_306_, 1, v___x_309_);
lean_ctor_set(v___x_306_, 0, v___x_308_);
v___x_311_ = v___x_306_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v___x_308_);
lean_ctor_set(v_reuseFailAlloc_323_, 1, v___x_309_);
v___x_311_ = v_reuseFailAlloc_323_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_312_ = lean_box(0);
v___x_313_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_313_, 0, v___x_311_);
lean_ctor_set(v___x_313_, 1, v___x_312_);
v___x_314_ = ((lean_object*)(l_Lean_Lsp_instToJsonRange_toJson___closed__1));
v___x_315_ = l_Lean_Lsp_instToJsonPosition_toJson(v_end_304_);
v___x_316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_316_, 0, v___x_314_);
lean_ctor_set(v___x_316_, 1, v___x_315_);
v___x_317_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_317_, 0, v___x_316_);
lean_ctor_set(v___x_317_, 1, v___x_312_);
v___x_318_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_318_, 0, v___x_317_);
lean_ctor_set(v___x_318_, 1, v___x_312_);
v___x_319_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_319_, 0, v___x_313_);
lean_ctor_set(v___x_319_, 1, v___x_318_);
v___x_320_ = ((lean_object*)(l_Lean_Lsp_instToJsonPosition_toJson___closed__2));
v___x_321_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonPosition_toJson_spec__0(v___x_319_, v___x_320_);
v___x_322_ = l_Lean_Json_mkObj(v___x_321_);
lean_dec(v___x_321_);
return v___x_322_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRange_fromJson_spec__0(lean_object* v_j_327_, lean_object* v_k_328_){
_start:
{
lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_329_ = l_Lean_Json_getObjValD(v_j_327_, v_k_328_);
v___x_330_ = l_Lean_Lsp_instFromJsonPosition_fromJson(v___x_329_);
return v___x_330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRange_fromJson_spec__0___boxed(lean_object* v_j_331_, lean_object* v_k_332_){
_start:
{
lean_object* v_res_333_; 
v_res_333_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRange_fromJson_spec__0(v_j_331_, v_k_332_);
lean_dec_ref(v_k_332_);
return v_res_333_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRange_fromJson___closed__2(void){
_start:
{
uint8_t v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; 
v___x_339_ = 1;
v___x_340_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRange_fromJson___closed__1));
v___x_341_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_340_, v___x_339_);
return v___x_341_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRange_fromJson___closed__3(void){
_start:
{
lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_342_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPosition_fromJson___closed__5));
v___x_343_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRange_fromJson___closed__2, &l_Lean_Lsp_instFromJsonRange_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonRange_fromJson___closed__2);
v___x_344_ = lean_string_append(v___x_343_, v___x_342_);
return v___x_344_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRange_fromJson___closed__5(void){
_start:
{
uint8_t v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_347_ = 1;
v___x_348_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRange_fromJson___closed__4));
v___x_349_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_348_, v___x_347_);
return v___x_349_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRange_fromJson___closed__6(void){
_start:
{
lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
v___x_350_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRange_fromJson___closed__5, &l_Lean_Lsp_instFromJsonRange_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonRange_fromJson___closed__5);
v___x_351_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRange_fromJson___closed__3, &l_Lean_Lsp_instFromJsonRange_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonRange_fromJson___closed__3);
v___x_352_ = lean_string_append(v___x_351_, v___x_350_);
return v___x_352_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRange_fromJson___closed__7(void){
_start:
{
lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_353_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPosition_fromJson___closed__10));
v___x_354_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRange_fromJson___closed__6, &l_Lean_Lsp_instFromJsonRange_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonRange_fromJson___closed__6);
v___x_355_ = lean_string_append(v___x_354_, v___x_353_);
return v___x_355_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRange_fromJson___closed__9(void){
_start:
{
uint8_t v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_358_ = 1;
v___x_359_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRange_fromJson___closed__8));
v___x_360_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_359_, v___x_358_);
return v___x_360_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRange_fromJson___closed__10(void){
_start:
{
lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_361_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRange_fromJson___closed__9, &l_Lean_Lsp_instFromJsonRange_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonRange_fromJson___closed__9);
v___x_362_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRange_fromJson___closed__3, &l_Lean_Lsp_instFromJsonRange_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonRange_fromJson___closed__3);
v___x_363_ = lean_string_append(v___x_362_, v___x_361_);
return v___x_363_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonRange_fromJson___closed__11(void){
_start:
{
lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; 
v___x_364_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPosition_fromJson___closed__10));
v___x_365_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRange_fromJson___closed__10, &l_Lean_Lsp_instFromJsonRange_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonRange_fromJson___closed__10);
v___x_366_ = lean_string_append(v___x_365_, v___x_364_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonRange_fromJson(lean_object* v_json_367_){
_start:
{
lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_368_ = ((lean_object*)(l_Lean_Lsp_instToJsonRange_toJson___closed__0));
lean_inc(v_json_367_);
v___x_369_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRange_fromJson_spec__0(v_json_367_, v___x_368_);
if (lean_obj_tag(v___x_369_) == 0)
{
lean_object* v_a_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_379_; 
lean_dec(v_json_367_);
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
v___x_374_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRange_fromJson___closed__7, &l_Lean_Lsp_instFromJsonRange_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonRange_fromJson___closed__7);
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
lean_object* v_a_380_; lean_object* v___x_381_; lean_object* v___x_382_; 
v_a_380_ = lean_ctor_get(v___x_369_, 0);
lean_inc(v_a_380_);
lean_dec_ref_known(v___x_369_, 1);
v___x_381_ = ((lean_object*)(l_Lean_Lsp_instToJsonRange_toJson___closed__1));
v___x_382_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonRange_fromJson_spec__0(v_json_367_, v___x_381_);
if (lean_obj_tag(v___x_382_) == 0)
{
lean_object* v_a_383_; lean_object* v___x_385_; uint8_t v_isShared_386_; uint8_t v_isSharedCheck_392_; 
lean_dec(v_a_380_);
v_a_383_ = lean_ctor_get(v___x_382_, 0);
v_isSharedCheck_392_ = !lean_is_exclusive(v___x_382_);
if (v_isSharedCheck_392_ == 0)
{
v___x_385_ = v___x_382_;
v_isShared_386_ = v_isSharedCheck_392_;
goto v_resetjp_384_;
}
else
{
lean_inc(v_a_383_);
lean_dec(v___x_382_);
v___x_385_ = lean_box(0);
v_isShared_386_ = v_isSharedCheck_392_;
goto v_resetjp_384_;
}
v_resetjp_384_:
{
lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_390_; 
v___x_387_ = lean_obj_once(&l_Lean_Lsp_instFromJsonRange_fromJson___closed__11, &l_Lean_Lsp_instFromJsonRange_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonRange_fromJson___closed__11);
v___x_388_ = lean_string_append(v___x_387_, v_a_383_);
lean_dec(v_a_383_);
if (v_isShared_386_ == 0)
{
lean_ctor_set(v___x_385_, 0, v___x_388_);
v___x_390_ = v___x_385_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v___x_388_);
v___x_390_ = v_reuseFailAlloc_391_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
return v___x_390_;
}
}
}
else
{
lean_object* v_a_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_401_; 
v_a_393_ = lean_ctor_get(v___x_382_, 0);
v_isSharedCheck_401_ = !lean_is_exclusive(v___x_382_);
if (v_isSharedCheck_401_ == 0)
{
v___x_395_ = v___x_382_;
v_isShared_396_ = v_isSharedCheck_401_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_a_393_);
lean_dec(v___x_382_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_401_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v___x_397_; lean_object* v___x_399_; 
v___x_397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_397_, 0, v_a_380_);
lean_ctor_set(v___x_397_, 1, v_a_393_);
if (v_isShared_396_ == 0)
{
lean_ctor_set(v___x_395_, 0, v___x_397_);
v___x_399_ = v___x_395_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_400_; 
v_reuseFailAlloc_400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_400_, 0, v___x_397_);
v___x_399_ = v_reuseFailAlloc_400_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
return v___x_399_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_instOrdRange_ord(lean_object* v_x_404_, lean_object* v_x_405_){
_start:
{
lean_object* v_start_406_; lean_object* v_end_407_; lean_object* v_start_408_; lean_object* v_end_409_; uint8_t v___x_410_; 
v_start_406_ = lean_ctor_get(v_x_404_, 0);
v_end_407_ = lean_ctor_get(v_x_404_, 1);
v_start_408_ = lean_ctor_get(v_x_405_, 0);
v_end_409_ = lean_ctor_get(v_x_405_, 1);
v___x_410_ = l_Lean_Lsp_instOrdPosition_ord(v_start_406_, v_start_408_);
if (v___x_410_ == 1)
{
uint8_t v___x_411_; 
v___x_411_ = l_Lean_Lsp_instOrdPosition_ord(v_end_407_, v_end_409_);
return v___x_411_;
}
else
{
return v___x_410_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instOrdRange_ord___boxed(lean_object* v_x_412_, lean_object* v_x_413_){
_start:
{
uint8_t v_res_414_; lean_object* v_r_415_; 
v_res_414_ = l_Lean_Lsp_instOrdRange_ord(v_x_412_, v_x_413_);
lean_dec_ref(v_x_413_);
lean_dec_ref(v_x_412_);
v_r_415_ = lean_box(v_res_414_);
return v_r_415_;
}
}
static lean_object* _init_l_Lean_Lsp_instReprRange_repr___redArg___closed__3(void){
_start:
{
lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_426_ = lean_unsigned_to_nat(9u);
v___x_427_ = lean_nat_to_int(v___x_426_);
return v___x_427_;
}
}
static lean_object* _init_l_Lean_Lsp_instReprRange_repr___redArg___closed__5(void){
_start:
{
lean_object* v___x_430_; lean_object* v___x_431_; 
v___x_430_ = lean_unsigned_to_nat(7u);
v___x_431_ = lean_nat_to_int(v___x_430_);
return v___x_431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instReprRange_repr___redArg(lean_object* v_x_432_){
_start:
{
lean_object* v_start_433_; lean_object* v_end_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_467_; 
v_start_433_ = lean_ctor_get(v_x_432_, 0);
v_end_434_ = lean_ctor_get(v_x_432_, 1);
v_isSharedCheck_467_ = !lean_is_exclusive(v_x_432_);
if (v_isSharedCheck_467_ == 0)
{
v___x_436_ = v_x_432_;
v_isShared_437_ = v_isSharedCheck_467_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_end_434_);
lean_inc(v_start_433_);
lean_dec(v_x_432_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_467_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_443_; 
v___x_438_ = ((lean_object*)(l_Lean_Lsp_instReprPosition_repr___redArg___closed__4));
v___x_439_ = ((lean_object*)(l_Lean_Lsp_instReprRange_repr___redArg___closed__2));
v___x_440_ = lean_obj_once(&l_Lean_Lsp_instReprRange_repr___redArg___closed__3, &l_Lean_Lsp_instReprRange_repr___redArg___closed__3_once, _init_l_Lean_Lsp_instReprRange_repr___redArg___closed__3);
v___x_441_ = l_Lean_Lsp_instReprPosition_repr___redArg(v_start_433_);
if (v_isShared_437_ == 0)
{
lean_ctor_set_tag(v___x_436_, 4);
lean_ctor_set(v___x_436_, 1, v___x_441_);
lean_ctor_set(v___x_436_, 0, v___x_440_);
v___x_443_ = v___x_436_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v___x_440_);
lean_ctor_set(v_reuseFailAlloc_466_, 1, v___x_441_);
v___x_443_ = v_reuseFailAlloc_466_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
uint8_t v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_444_ = 0;
v___x_445_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_445_, 0, v___x_443_);
lean_ctor_set_uint8(v___x_445_, sizeof(void*)*1, v___x_444_);
v___x_446_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_446_, 0, v___x_439_);
lean_ctor_set(v___x_446_, 1, v___x_445_);
v___x_447_ = ((lean_object*)(l_Lean_Lsp_instReprPosition_repr___redArg___closed__8));
v___x_448_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_448_, 0, v___x_446_);
lean_ctor_set(v___x_448_, 1, v___x_447_);
v___x_449_ = lean_box(1);
v___x_450_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_450_, 0, v___x_448_);
lean_ctor_set(v___x_450_, 1, v___x_449_);
v___x_451_ = ((lean_object*)(l_Lean_Lsp_instReprRange_repr___redArg___closed__4));
v___x_452_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_452_, 0, v___x_450_);
lean_ctor_set(v___x_452_, 1, v___x_451_);
v___x_453_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_453_, 0, v___x_452_);
lean_ctor_set(v___x_453_, 1, v___x_438_);
v___x_454_ = lean_obj_once(&l_Lean_Lsp_instReprRange_repr___redArg___closed__5, &l_Lean_Lsp_instReprRange_repr___redArg___closed__5_once, _init_l_Lean_Lsp_instReprRange_repr___redArg___closed__5);
v___x_455_ = l_Lean_Lsp_instReprPosition_repr___redArg(v_end_434_);
v___x_456_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_456_, 0, v___x_454_);
lean_ctor_set(v___x_456_, 1, v___x_455_);
v___x_457_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_457_, 0, v___x_456_);
lean_ctor_set_uint8(v___x_457_, sizeof(void*)*1, v___x_444_);
v___x_458_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_458_, 0, v___x_453_);
lean_ctor_set(v___x_458_, 1, v___x_457_);
v___x_459_ = lean_obj_once(&l_Lean_Lsp_instReprPosition_repr___redArg___closed__13, &l_Lean_Lsp_instReprPosition_repr___redArg___closed__13_once, _init_l_Lean_Lsp_instReprPosition_repr___redArg___closed__13);
v___x_460_ = ((lean_object*)(l_Lean_Lsp_instReprPosition_repr___redArg___closed__14));
v___x_461_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_461_, 0, v___x_460_);
lean_ctor_set(v___x_461_, 1, v___x_458_);
v___x_462_ = ((lean_object*)(l_Lean_Lsp_instReprPosition_repr___redArg___closed__15));
v___x_463_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_463_, 0, v___x_461_);
lean_ctor_set(v___x_463_, 1, v___x_462_);
v___x_464_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_464_, 0, v___x_459_);
lean_ctor_set(v___x_464_, 1, v___x_463_);
v___x_465_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_465_, 0, v___x_464_);
lean_ctor_set_uint8(v___x_465_, sizeof(void*)*1, v___x_444_);
return v___x_465_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instReprRange_repr(lean_object* v_x_468_, lean_object* v_prec_469_){
_start:
{
lean_object* v___x_470_; 
v___x_470_ = l_Lean_Lsp_instReprRange_repr___redArg(v_x_468_);
return v___x_470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instReprRange_repr___boxed(lean_object* v_x_471_, lean_object* v_prec_472_){
_start:
{
lean_object* v_res_473_; 
v_res_473_ = l_Lean_Lsp_instReprRange_repr(v_x_471_, v_prec_472_);
lean_dec(v_prec_472_);
return v_res_473_;
}
}
static lean_object* _init_l_Lean_Lsp_instLTRange(void){
_start:
{
lean_object* v___x_476_; 
v___x_476_ = lean_box(0);
return v___x_476_;
}
}
static lean_object* _init_l_Lean_Lsp_instLERange(void){
_start:
{
lean_object* v___x_477_; 
v___x_477_ = lean_box(0);
return v___x_477_;
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

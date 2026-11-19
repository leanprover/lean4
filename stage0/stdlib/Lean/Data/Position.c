// Lean compiler output
// Module: Lean.Data.Position
// Imports: public import Lean.Data.Json.FromToJson.Basic public import Lean.ToExpr
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
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_JsonNumber_fromNat(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
lean_object* l_Lean_Json_getNat_x3f(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_pos_x21(lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_nextn(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Nat_decLt___boxed(lean_object*, lean_object*);
lean_object* l_instDecidableEqNat___boxed(lean_object*, lean_object*);
uint8_t l_Prod_lexLtDec___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_instInhabitedPosition_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_instInhabitedPosition_default___closed__0 = (const lean_object*)&l_Lean_instInhabitedPosition_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedPosition_default = (const lean_object*)&l_Lean_instInhabitedPosition_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedPosition = (const lean_object*)&l_Lean_instInhabitedPosition_default___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_instDecidableEqPosition_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instDecidableEqPosition_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_instDecidableEqPosition(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instDecidableEqPosition___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_instReprPosition_repr_spec__0(lean_object*);
static const lean_string_object l_Lean_instReprPosition_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Lean_instReprPosition_repr___redArg___closed__0 = (const lean_object*)&l_Lean_instReprPosition_repr___redArg___closed__0_value;
static const lean_string_object l_Lean_instReprPosition_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "line"};
static const lean_object* l_Lean_instReprPosition_repr___redArg___closed__1 = (const lean_object*)&l_Lean_instReprPosition_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_instReprPosition_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprPosition_repr___redArg___closed__1_value)}};
static const lean_object* l_Lean_instReprPosition_repr___redArg___closed__2 = (const lean_object*)&l_Lean_instReprPosition_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lean_instReprPosition_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instReprPosition_repr___redArg___closed__2_value)}};
static const lean_object* l_Lean_instReprPosition_repr___redArg___closed__3 = (const lean_object*)&l_Lean_instReprPosition_repr___redArg___closed__3_value;
static const lean_string_object l_Lean_instReprPosition_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lean_instReprPosition_repr___redArg___closed__4 = (const lean_object*)&l_Lean_instReprPosition_repr___redArg___closed__4_value;
static const lean_ctor_object l_Lean_instReprPosition_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprPosition_repr___redArg___closed__4_value)}};
static const lean_object* l_Lean_instReprPosition_repr___redArg___closed__5 = (const lean_object*)&l_Lean_instReprPosition_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lean_instReprPosition_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_instReprPosition_repr___redArg___closed__3_value),((lean_object*)&l_Lean_instReprPosition_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_instReprPosition_repr___redArg___closed__6 = (const lean_object*)&l_Lean_instReprPosition_repr___redArg___closed__6_value;
static lean_once_cell_t l_Lean_instReprPosition_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instReprPosition_repr___redArg___closed__7;
static const lean_string_object l_Lean_instReprPosition_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lean_instReprPosition_repr___redArg___closed__8 = (const lean_object*)&l_Lean_instReprPosition_repr___redArg___closed__8_value;
static const lean_ctor_object l_Lean_instReprPosition_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprPosition_repr___redArg___closed__8_value)}};
static const lean_object* l_Lean_instReprPosition_repr___redArg___closed__9 = (const lean_object*)&l_Lean_instReprPosition_repr___redArg___closed__9_value;
static const lean_string_object l_Lean_instReprPosition_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "column"};
static const lean_object* l_Lean_instReprPosition_repr___redArg___closed__10 = (const lean_object*)&l_Lean_instReprPosition_repr___redArg___closed__10_value;
static const lean_ctor_object l_Lean_instReprPosition_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprPosition_repr___redArg___closed__10_value)}};
static const lean_object* l_Lean_instReprPosition_repr___redArg___closed__11 = (const lean_object*)&l_Lean_instReprPosition_repr___redArg___closed__11_value;
static lean_once_cell_t l_Lean_instReprPosition_repr___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instReprPosition_repr___redArg___closed__12;
static const lean_string_object l_Lean_instReprPosition_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Lean_instReprPosition_repr___redArg___closed__13 = (const lean_object*)&l_Lean_instReprPosition_repr___redArg___closed__13_value;
static lean_once_cell_t l_Lean_instReprPosition_repr___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instReprPosition_repr___redArg___closed__14;
static lean_once_cell_t l_Lean_instReprPosition_repr___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instReprPosition_repr___redArg___closed__15;
static const lean_ctor_object l_Lean_instReprPosition_repr___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprPosition_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_instReprPosition_repr___redArg___closed__16 = (const lean_object*)&l_Lean_instReprPosition_repr___redArg___closed__16_value;
static const lean_ctor_object l_Lean_instReprPosition_repr___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprPosition_repr___redArg___closed__13_value)}};
static const lean_object* l_Lean_instReprPosition_repr___redArg___closed__17 = (const lean_object*)&l_Lean_instReprPosition_repr___redArg___closed__17_value;
LEAN_EXPORT lean_object* l_Lean_instReprPosition_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprPosition_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprPosition_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instReprPosition___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instReprPosition_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instReprPosition___closed__0 = (const lean_object*)&l_Lean_instReprPosition___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instReprPosition = (const lean_object*)&l_Lean_instReprPosition___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonPosition_toJson_spec__0(lean_object*, lean_object*);
static const lean_array_object l_Lean_instToJsonPosition_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_instToJsonPosition_toJson___closed__0 = (const lean_object*)&l_Lean_instToJsonPosition_toJson___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instToJsonPosition_toJson(lean_object*);
static const lean_closure_object l_Lean_instToJsonPosition___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToJsonPosition_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToJsonPosition___closed__0 = (const lean_object*)&l_Lean_instToJsonPosition___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instToJsonPosition = (const lean_object*)&l_Lean_instToJsonPosition___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonPosition_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonPosition_fromJson_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_instFromJsonPosition_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_instFromJsonPosition_fromJson___closed__0 = (const lean_object*)&l_Lean_instFromJsonPosition_fromJson___closed__0_value;
static const lean_string_object l_Lean_instFromJsonPosition_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Position"};
static const lean_object* l_Lean_instFromJsonPosition_fromJson___closed__1 = (const lean_object*)&l_Lean_instFromJsonPosition_fromJson___closed__1_value;
static const lean_ctor_object l_Lean_instFromJsonPosition_fromJson___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instFromJsonPosition_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_instFromJsonPosition_fromJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instFromJsonPosition_fromJson___closed__2_value_aux_0),((lean_object*)&l_Lean_instFromJsonPosition_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(65, 243, 169, 21, 0, 54, 19, 101)}};
static const lean_object* l_Lean_instFromJsonPosition_fromJson___closed__2 = (const lean_object*)&l_Lean_instFromJsonPosition_fromJson___closed__2_value;
static lean_once_cell_t l_Lean_instFromJsonPosition_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonPosition_fromJson___closed__3;
static const lean_string_object l_Lean_instFromJsonPosition_fromJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lean_instFromJsonPosition_fromJson___closed__4 = (const lean_object*)&l_Lean_instFromJsonPosition_fromJson___closed__4_value;
static lean_once_cell_t l_Lean_instFromJsonPosition_fromJson___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonPosition_fromJson___closed__5;
static const lean_ctor_object l_Lean_instFromJsonPosition_fromJson___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instReprPosition_repr___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(45, 20, 170, 234, 25, 144, 248, 101)}};
static const lean_object* l_Lean_instFromJsonPosition_fromJson___closed__6 = (const lean_object*)&l_Lean_instFromJsonPosition_fromJson___closed__6_value;
static lean_once_cell_t l_Lean_instFromJsonPosition_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonPosition_fromJson___closed__7;
static lean_once_cell_t l_Lean_instFromJsonPosition_fromJson___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonPosition_fromJson___closed__8;
static const lean_string_object l_Lean_instFromJsonPosition_fromJson___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l_Lean_instFromJsonPosition_fromJson___closed__9 = (const lean_object*)&l_Lean_instFromJsonPosition_fromJson___closed__9_value;
static lean_once_cell_t l_Lean_instFromJsonPosition_fromJson___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonPosition_fromJson___closed__10;
static const lean_ctor_object l_Lean_instFromJsonPosition_fromJson___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instReprPosition_repr___redArg___closed__10_value),LEAN_SCALAR_PTR_LITERAL(177, 41, 36, 97, 84, 61, 112, 119)}};
static const lean_object* l_Lean_instFromJsonPosition_fromJson___closed__11 = (const lean_object*)&l_Lean_instFromJsonPosition_fromJson___closed__11_value;
static lean_once_cell_t l_Lean_instFromJsonPosition_fromJson___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonPosition_fromJson___closed__12;
static lean_once_cell_t l_Lean_instFromJsonPosition_fromJson___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonPosition_fromJson___closed__13;
static lean_once_cell_t l_Lean_instFromJsonPosition_fromJson___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instFromJsonPosition_fromJson___closed__14;
LEAN_EXPORT lean_object* l_Lean_instFromJsonPosition_fromJson(lean_object*);
static const lean_closure_object l_Lean_instFromJsonPosition___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instFromJsonPosition_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instFromJsonPosition___closed__0 = (const lean_object*)&l_Lean_instFromJsonPosition___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instFromJsonPosition = (const lean_object*)&l_Lean_instFromJsonPosition___closed__0_value;
static const lean_closure_object l_Lean_Position_lt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Nat_decLt___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Position_lt___closed__0 = (const lean_object*)&l_Lean_Position_lt___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Position_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Position_lt___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Position_instToFormat___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⟨"};
static const lean_object* l_Lean_Position_instToFormat___lam__0___closed__0 = (const lean_object*)&l_Lean_Position_instToFormat___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Position_instToFormat___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Position_instToFormat___lam__0___closed__0_value)}};
static const lean_object* l_Lean_Position_instToFormat___lam__0___closed__1 = (const lean_object*)&l_Lean_Position_instToFormat___lam__0___closed__1_value;
static const lean_string_object l_Lean_Position_instToFormat___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_Lean_Position_instToFormat___lam__0___closed__2 = (const lean_object*)&l_Lean_Position_instToFormat___lam__0___closed__2_value;
static const lean_ctor_object l_Lean_Position_instToFormat___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Position_instToFormat___lam__0___closed__2_value)}};
static const lean_object* l_Lean_Position_instToFormat___lam__0___closed__3 = (const lean_object*)&l_Lean_Position_instToFormat___lam__0___closed__3_value;
static const lean_string_object l_Lean_Position_instToFormat___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⟩"};
static const lean_object* l_Lean_Position_instToFormat___lam__0___closed__4 = (const lean_object*)&l_Lean_Position_instToFormat___lam__0___closed__4_value;
static const lean_ctor_object l_Lean_Position_instToFormat___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Position_instToFormat___lam__0___closed__4_value)}};
static const lean_object* l_Lean_Position_instToFormat___lam__0___closed__5 = (const lean_object*)&l_Lean_Position_instToFormat___lam__0___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Position_instToFormat___lam__0(lean_object*);
static const lean_closure_object l_Lean_Position_instToFormat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Position_instToFormat___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Position_instToFormat___closed__0 = (const lean_object*)&l_Lean_Position_instToFormat___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Position_instToFormat = (const lean_object*)&l_Lean_Position_instToFormat___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Position_instToString___lam__0(lean_object*);
static const lean_closure_object l_Lean_Position_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Position_instToString___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Position_instToString___closed__0 = (const lean_object*)&l_Lean_Position_instToString___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Position_instToString = (const lean_object*)&l_Lean_Position_instToString___closed__0_value;
static const lean_string_object l_Lean_Position_instToExpr___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mk"};
static const lean_object* l_Lean_Position_instToExpr___lam__0___closed__0 = (const lean_object*)&l_Lean_Position_instToExpr___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Position_instToExpr___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instFromJsonPosition_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Position_instToExpr___lam__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Position_instToExpr___lam__0___closed__1_value_aux_0),((lean_object*)&l_Lean_instFromJsonPosition_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(65, 243, 169, 21, 0, 54, 19, 101)}};
static const lean_ctor_object l_Lean_Position_instToExpr___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Position_instToExpr___lam__0___closed__1_value_aux_1),((lean_object*)&l_Lean_Position_instToExpr___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(205, 0, 160, 114, 110, 41, 100, 154)}};
static const lean_object* l_Lean_Position_instToExpr___lam__0___closed__1 = (const lean_object*)&l_Lean_Position_instToExpr___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_Position_instToExpr___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Position_instToExpr___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_Position_instToExpr___lam__0(lean_object*);
static const lean_closure_object l_Lean_Position_instToExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Position_instToExpr___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Position_instToExpr___closed__0 = (const lean_object*)&l_Lean_Position_instToExpr___closed__0_value;
static lean_once_cell_t l_Lean_Position_instToExpr___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Position_instToExpr___closed__1;
static lean_once_cell_t l_Lean_Position_instToExpr___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Position_instToExpr___closed__2;
LEAN_EXPORT lean_object* l_Lean_Position_instToExpr;
static const lean_string_object l_Lean_instInhabitedFileMap_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_instInhabitedFileMap_default___closed__0 = (const lean_object*)&l_Lean_instInhabitedFileMap_default___closed__0_value;
static const lean_array_object l_Lean_instInhabitedFileMap_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_instInhabitedFileMap_default___closed__1 = (const lean_object*)&l_Lean_instInhabitedFileMap_default___closed__1_value;
static const lean_ctor_object l_Lean_instInhabitedFileMap_default___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_instInhabitedFileMap_default___closed__0_value),((lean_object*)&l_Lean_instInhabitedFileMap_default___closed__1_value)}};
static const lean_object* l_Lean_instInhabitedFileMap_default___closed__2 = (const lean_object*)&l_Lean_instInhabitedFileMap_default___closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedFileMap_default = (const lean_object*)&l_Lean_instInhabitedFileMap_default___closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedFileMap = (const lean_object*)&l_Lean_instInhabitedFileMap_default___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_FileMap_getLastLine(lean_object*);
LEAN_EXPORT lean_object* l_Lean_FileMap_getLastLine___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_FileMap_getLine(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_FileMap_getLine___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Position_0__Lean_FileMap_ofString_loop(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_FileMap_ofString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_FileMap_ofString___closed__0 = (const lean_object*)&l_Lean_FileMap_ofString___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_FileMap_ofString(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Position_0__Lean_FileMap_toPosition_toColumn(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Position_0__Lean_FileMap_toPosition_toColumn___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Position_0__Lean_FileMap_toPosition_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Position_0__Lean_FileMap_toPosition_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_FileMap_toPosition___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_FileMap_ofPosition(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_FileMap_ofPosition___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_FileMap_lineStart(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_FileMap_lineStart___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_String_toFileMap(lean_object*);
LEAN_EXPORT uint8_t l_Lean_instDecidableEqPosition_decEq(lean_object* v_x_5_, lean_object* v_x_6_){
_start:
{
lean_object* v_line_7_; lean_object* v_column_8_; lean_object* v_line_9_; lean_object* v_column_10_; uint8_t v___x_11_; 
v_line_7_ = lean_ctor_get(v_x_5_, 0);
v_column_8_ = lean_ctor_get(v_x_5_, 1);
v_line_9_ = lean_ctor_get(v_x_6_, 0);
v_column_10_ = lean_ctor_get(v_x_6_, 1);
v___x_11_ = lean_nat_dec_eq(v_line_7_, v_line_9_);
if (v___x_11_ == 0)
{
return v___x_11_;
}
else
{
uint8_t v___x_12_; 
v___x_12_ = lean_nat_dec_eq(v_column_8_, v_column_10_);
return v___x_12_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instDecidableEqPosition_decEq___boxed(lean_object* v_x_13_, lean_object* v_x_14_){
_start:
{
uint8_t v_res_15_; lean_object* v_r_16_; 
v_res_15_ = l_Lean_instDecidableEqPosition_decEq(v_x_13_, v_x_14_);
lean_dec_ref(v_x_14_);
lean_dec_ref(v_x_13_);
v_r_16_ = lean_box(v_res_15_);
return v_r_16_;
}
}
LEAN_EXPORT uint8_t l_Lean_instDecidableEqPosition(lean_object* v_x_17_, lean_object* v_x_18_){
_start:
{
uint8_t v___x_19_; 
v___x_19_ = l_Lean_instDecidableEqPosition_decEq(v_x_17_, v_x_18_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l_Lean_instDecidableEqPosition___boxed(lean_object* v_x_20_, lean_object* v_x_21_){
_start:
{
uint8_t v_res_22_; lean_object* v_r_23_; 
v_res_22_ = l_Lean_instDecidableEqPosition(v_x_20_, v_x_21_);
lean_dec_ref(v_x_21_);
lean_dec_ref(v_x_20_);
v_r_23_ = lean_box(v_res_22_);
return v_r_23_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_instReprPosition_repr_spec__0(lean_object* v_a_24_){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = lean_nat_to_int(v_a_24_);
return v___x_25_;
}
}
static lean_object* _init_l_Lean_instReprPosition_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_39_; lean_object* v___x_40_; 
v___x_39_ = lean_unsigned_to_nat(8u);
v___x_40_ = lean_nat_to_int(v___x_39_);
return v___x_40_;
}
}
static lean_object* _init_l_Lean_instReprPosition_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_47_ = lean_unsigned_to_nat(10u);
v___x_48_ = lean_nat_to_int(v___x_47_);
return v___x_48_;
}
}
static lean_object* _init_l_Lean_instReprPosition_repr___redArg___closed__14(void){
_start:
{
lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_50_ = ((lean_object*)(l_Lean_instReprPosition_repr___redArg___closed__0));
v___x_51_ = lean_string_length(v___x_50_);
return v___x_51_;
}
}
static lean_object* _init_l_Lean_instReprPosition_repr___redArg___closed__15(void){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_52_ = lean_obj_once(&l_Lean_instReprPosition_repr___redArg___closed__14, &l_Lean_instReprPosition_repr___redArg___closed__14_once, _init_l_Lean_instReprPosition_repr___redArg___closed__14);
v___x_53_ = lean_nat_to_int(v___x_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprPosition_repr___redArg(lean_object* v_x_58_){
_start:
{
lean_object* v_line_59_; lean_object* v_column_60_; lean_object* v___x_62_; uint8_t v_isShared_63_; uint8_t v_isSharedCheck_95_; 
v_line_59_ = lean_ctor_get(v_x_58_, 0);
v_column_60_ = lean_ctor_get(v_x_58_, 1);
v_isSharedCheck_95_ = !lean_is_exclusive(v_x_58_);
if (v_isSharedCheck_95_ == 0)
{
v___x_62_ = v_x_58_;
v_isShared_63_ = v_isSharedCheck_95_;
goto v_resetjp_61_;
}
else
{
lean_inc(v_column_60_);
lean_inc(v_line_59_);
lean_dec(v_x_58_);
v___x_62_ = lean_box(0);
v_isShared_63_ = v_isSharedCheck_95_;
goto v_resetjp_61_;
}
v_resetjp_61_:
{
lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_70_; 
v___x_64_ = ((lean_object*)(l_Lean_instReprPosition_repr___redArg___closed__5));
v___x_65_ = ((lean_object*)(l_Lean_instReprPosition_repr___redArg___closed__6));
v___x_66_ = lean_obj_once(&l_Lean_instReprPosition_repr___redArg___closed__7, &l_Lean_instReprPosition_repr___redArg___closed__7_once, _init_l_Lean_instReprPosition_repr___redArg___closed__7);
v___x_67_ = l_Nat_reprFast(v_line_59_);
v___x_68_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_68_, 0, v___x_67_);
if (v_isShared_63_ == 0)
{
lean_ctor_set_tag(v___x_62_, 4);
lean_ctor_set(v___x_62_, 1, v___x_68_);
lean_ctor_set(v___x_62_, 0, v___x_66_);
v___x_70_ = v___x_62_;
goto v_reusejp_69_;
}
else
{
lean_object* v_reuseFailAlloc_94_; 
v_reuseFailAlloc_94_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_94_, 0, v___x_66_);
lean_ctor_set(v_reuseFailAlloc_94_, 1, v___x_68_);
v___x_70_ = v_reuseFailAlloc_94_;
goto v_reusejp_69_;
}
v_reusejp_69_:
{
uint8_t v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_71_ = 0;
v___x_72_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_72_, 0, v___x_70_);
lean_ctor_set_uint8(v___x_72_, sizeof(void*)*1, v___x_71_);
v___x_73_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_73_, 0, v___x_65_);
lean_ctor_set(v___x_73_, 1, v___x_72_);
v___x_74_ = ((lean_object*)(l_Lean_instReprPosition_repr___redArg___closed__9));
v___x_75_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_75_, 0, v___x_73_);
lean_ctor_set(v___x_75_, 1, v___x_74_);
v___x_76_ = lean_box(1);
v___x_77_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_77_, 0, v___x_75_);
lean_ctor_set(v___x_77_, 1, v___x_76_);
v___x_78_ = ((lean_object*)(l_Lean_instReprPosition_repr___redArg___closed__11));
v___x_79_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_79_, 0, v___x_77_);
lean_ctor_set(v___x_79_, 1, v___x_78_);
v___x_80_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_80_, 0, v___x_79_);
lean_ctor_set(v___x_80_, 1, v___x_64_);
v___x_81_ = lean_obj_once(&l_Lean_instReprPosition_repr___redArg___closed__12, &l_Lean_instReprPosition_repr___redArg___closed__12_once, _init_l_Lean_instReprPosition_repr___redArg___closed__12);
v___x_82_ = l_Nat_reprFast(v_column_60_);
v___x_83_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_83_, 0, v___x_82_);
v___x_84_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_84_, 0, v___x_81_);
lean_ctor_set(v___x_84_, 1, v___x_83_);
v___x_85_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_85_, 0, v___x_84_);
lean_ctor_set_uint8(v___x_85_, sizeof(void*)*1, v___x_71_);
v___x_86_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_86_, 0, v___x_80_);
lean_ctor_set(v___x_86_, 1, v___x_85_);
v___x_87_ = lean_obj_once(&l_Lean_instReprPosition_repr___redArg___closed__15, &l_Lean_instReprPosition_repr___redArg___closed__15_once, _init_l_Lean_instReprPosition_repr___redArg___closed__15);
v___x_88_ = ((lean_object*)(l_Lean_instReprPosition_repr___redArg___closed__16));
v___x_89_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_89_, 0, v___x_88_);
lean_ctor_set(v___x_89_, 1, v___x_86_);
v___x_90_ = ((lean_object*)(l_Lean_instReprPosition_repr___redArg___closed__17));
v___x_91_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_91_, 0, v___x_89_);
lean_ctor_set(v___x_91_, 1, v___x_90_);
v___x_92_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_92_, 0, v___x_87_);
lean_ctor_set(v___x_92_, 1, v___x_91_);
v___x_93_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_93_, 0, v___x_92_);
lean_ctor_set_uint8(v___x_93_, sizeof(void*)*1, v___x_71_);
return v___x_93_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprPosition_repr(lean_object* v_x_96_, lean_object* v_prec_97_){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = l_Lean_instReprPosition_repr___redArg(v_x_96_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprPosition_repr___boxed(lean_object* v_x_99_, lean_object* v_prec_100_){
_start:
{
lean_object* v_res_101_; 
v_res_101_ = l_Lean_instReprPosition_repr(v_x_99_, v_prec_100_);
lean_dec(v_prec_100_);
return v_res_101_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonPosition_toJson_spec__0(lean_object* v_a_104_, lean_object* v_a_105_){
_start:
{
if (lean_obj_tag(v_a_104_) == 0)
{
lean_object* v___x_106_; 
v___x_106_ = lean_array_to_list(v_a_105_);
return v___x_106_;
}
else
{
lean_object* v_head_107_; lean_object* v_tail_108_; lean_object* v___x_109_; 
v_head_107_ = lean_ctor_get(v_a_104_, 0);
lean_inc(v_head_107_);
v_tail_108_ = lean_ctor_get(v_a_104_, 1);
lean_inc(v_tail_108_);
lean_dec_ref_known(v_a_104_, 2);
v___x_109_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_105_, v_head_107_);
v_a_104_ = v_tail_108_;
v_a_105_ = v___x_109_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonPosition_toJson(lean_object* v_x_113_){
_start:
{
lean_object* v_line_114_; lean_object* v_column_115_; lean_object* v___x_117_; uint8_t v_isShared_118_; uint8_t v_isSharedCheck_137_; 
v_line_114_ = lean_ctor_get(v_x_113_, 0);
v_column_115_ = lean_ctor_get(v_x_113_, 1);
v_isSharedCheck_137_ = !lean_is_exclusive(v_x_113_);
if (v_isSharedCheck_137_ == 0)
{
v___x_117_ = v_x_113_;
v_isShared_118_ = v_isSharedCheck_137_;
goto v_resetjp_116_;
}
else
{
lean_inc(v_column_115_);
lean_inc(v_line_114_);
lean_dec(v_x_113_);
v___x_117_ = lean_box(0);
v_isShared_118_ = v_isSharedCheck_137_;
goto v_resetjp_116_;
}
v_resetjp_116_:
{
lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_123_; 
v___x_119_ = ((lean_object*)(l_Lean_instReprPosition_repr___redArg___closed__1));
v___x_120_ = l_Lean_JsonNumber_fromNat(v_line_114_);
v___x_121_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_121_, 0, v___x_120_);
if (v_isShared_118_ == 0)
{
lean_ctor_set(v___x_117_, 1, v___x_121_);
lean_ctor_set(v___x_117_, 0, v___x_119_);
v___x_123_ = v___x_117_;
goto v_reusejp_122_;
}
else
{
lean_object* v_reuseFailAlloc_136_; 
v_reuseFailAlloc_136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_136_, 0, v___x_119_);
lean_ctor_set(v_reuseFailAlloc_136_, 1, v___x_121_);
v___x_123_ = v_reuseFailAlloc_136_;
goto v_reusejp_122_;
}
v_reusejp_122_:
{
lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_124_ = lean_box(0);
v___x_125_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_125_, 0, v___x_123_);
lean_ctor_set(v___x_125_, 1, v___x_124_);
v___x_126_ = ((lean_object*)(l_Lean_instReprPosition_repr___redArg___closed__10));
v___x_127_ = l_Lean_JsonNumber_fromNat(v_column_115_);
v___x_128_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_128_, 0, v___x_127_);
v___x_129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_129_, 0, v___x_126_);
lean_ctor_set(v___x_129_, 1, v___x_128_);
v___x_130_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_130_, 0, v___x_129_);
lean_ctor_set(v___x_130_, 1, v___x_124_);
v___x_131_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_131_, 0, v___x_130_);
lean_ctor_set(v___x_131_, 1, v___x_124_);
v___x_132_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_132_, 0, v___x_125_);
lean_ctor_set(v___x_132_, 1, v___x_131_);
v___x_133_ = ((lean_object*)(l_Lean_instToJsonPosition_toJson___closed__0));
v___x_134_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonPosition_toJson_spec__0(v___x_132_, v___x_133_);
v___x_135_ = l_Lean_Json_mkObj(v___x_134_);
lean_dec(v___x_134_);
return v___x_135_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonPosition_fromJson_spec__0(lean_object* v_j_140_, lean_object* v_k_141_){
_start:
{
lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_142_ = l_Lean_Json_getObjValD(v_j_140_, v_k_141_);
v___x_143_ = l_Lean_Json_getNat_x3f(v___x_142_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonPosition_fromJson_spec__0___boxed(lean_object* v_j_144_, lean_object* v_k_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonPosition_fromJson_spec__0(v_j_144_, v_k_145_);
lean_dec_ref(v_k_145_);
return v_res_146_;
}
}
static lean_object* _init_l_Lean_instFromJsonPosition_fromJson___closed__3(void){
_start:
{
uint8_t v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_152_ = 1;
v___x_153_ = ((lean_object*)(l_Lean_instFromJsonPosition_fromJson___closed__2));
v___x_154_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_153_, v___x_152_);
return v___x_154_;
}
}
static lean_object* _init_l_Lean_instFromJsonPosition_fromJson___closed__5(void){
_start:
{
lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_156_ = ((lean_object*)(l_Lean_instFromJsonPosition_fromJson___closed__4));
v___x_157_ = lean_obj_once(&l_Lean_instFromJsonPosition_fromJson___closed__3, &l_Lean_instFromJsonPosition_fromJson___closed__3_once, _init_l_Lean_instFromJsonPosition_fromJson___closed__3);
v___x_158_ = lean_string_append(v___x_157_, v___x_156_);
return v___x_158_;
}
}
static lean_object* _init_l_Lean_instFromJsonPosition_fromJson___closed__7(void){
_start:
{
uint8_t v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_161_ = 1;
v___x_162_ = ((lean_object*)(l_Lean_instFromJsonPosition_fromJson___closed__6));
v___x_163_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_162_, v___x_161_);
return v___x_163_;
}
}
static lean_object* _init_l_Lean_instFromJsonPosition_fromJson___closed__8(void){
_start:
{
lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_164_ = lean_obj_once(&l_Lean_instFromJsonPosition_fromJson___closed__7, &l_Lean_instFromJsonPosition_fromJson___closed__7_once, _init_l_Lean_instFromJsonPosition_fromJson___closed__7);
v___x_165_ = lean_obj_once(&l_Lean_instFromJsonPosition_fromJson___closed__5, &l_Lean_instFromJsonPosition_fromJson___closed__5_once, _init_l_Lean_instFromJsonPosition_fromJson___closed__5);
v___x_166_ = lean_string_append(v___x_165_, v___x_164_);
return v___x_166_;
}
}
static lean_object* _init_l_Lean_instFromJsonPosition_fromJson___closed__10(void){
_start:
{
lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_168_ = ((lean_object*)(l_Lean_instFromJsonPosition_fromJson___closed__9));
v___x_169_ = lean_obj_once(&l_Lean_instFromJsonPosition_fromJson___closed__8, &l_Lean_instFromJsonPosition_fromJson___closed__8_once, _init_l_Lean_instFromJsonPosition_fromJson___closed__8);
v___x_170_ = lean_string_append(v___x_169_, v___x_168_);
return v___x_170_;
}
}
static lean_object* _init_l_Lean_instFromJsonPosition_fromJson___closed__12(void){
_start:
{
uint8_t v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_173_ = 1;
v___x_174_ = ((lean_object*)(l_Lean_instFromJsonPosition_fromJson___closed__11));
v___x_175_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_174_, v___x_173_);
return v___x_175_;
}
}
static lean_object* _init_l_Lean_instFromJsonPosition_fromJson___closed__13(void){
_start:
{
lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; 
v___x_176_ = lean_obj_once(&l_Lean_instFromJsonPosition_fromJson___closed__12, &l_Lean_instFromJsonPosition_fromJson___closed__12_once, _init_l_Lean_instFromJsonPosition_fromJson___closed__12);
v___x_177_ = lean_obj_once(&l_Lean_instFromJsonPosition_fromJson___closed__5, &l_Lean_instFromJsonPosition_fromJson___closed__5_once, _init_l_Lean_instFromJsonPosition_fromJson___closed__5);
v___x_178_ = lean_string_append(v___x_177_, v___x_176_);
return v___x_178_;
}
}
static lean_object* _init_l_Lean_instFromJsonPosition_fromJson___closed__14(void){
_start:
{
lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_179_ = ((lean_object*)(l_Lean_instFromJsonPosition_fromJson___closed__9));
v___x_180_ = lean_obj_once(&l_Lean_instFromJsonPosition_fromJson___closed__13, &l_Lean_instFromJsonPosition_fromJson___closed__13_once, _init_l_Lean_instFromJsonPosition_fromJson___closed__13);
v___x_181_ = lean_string_append(v___x_180_, v___x_179_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonPosition_fromJson(lean_object* v_json_182_){
_start:
{
lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_183_ = ((lean_object*)(l_Lean_instReprPosition_repr___redArg___closed__1));
lean_inc(v_json_182_);
v___x_184_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonPosition_fromJson_spec__0(v_json_182_, v___x_183_);
if (lean_obj_tag(v___x_184_) == 0)
{
lean_object* v_a_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_194_; 
lean_dec(v_json_182_);
v_a_185_ = lean_ctor_get(v___x_184_, 0);
v_isSharedCheck_194_ = !lean_is_exclusive(v___x_184_);
if (v_isSharedCheck_194_ == 0)
{
v___x_187_ = v___x_184_;
v_isShared_188_ = v_isSharedCheck_194_;
goto v_resetjp_186_;
}
else
{
lean_inc(v_a_185_);
lean_dec(v___x_184_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_194_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_192_; 
v___x_189_ = lean_obj_once(&l_Lean_instFromJsonPosition_fromJson___closed__10, &l_Lean_instFromJsonPosition_fromJson___closed__10_once, _init_l_Lean_instFromJsonPosition_fromJson___closed__10);
v___x_190_ = lean_string_append(v___x_189_, v_a_185_);
lean_dec(v_a_185_);
if (v_isShared_188_ == 0)
{
lean_ctor_set(v___x_187_, 0, v___x_190_);
v___x_192_ = v___x_187_;
goto v_reusejp_191_;
}
else
{
lean_object* v_reuseFailAlloc_193_; 
v_reuseFailAlloc_193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_193_, 0, v___x_190_);
v___x_192_ = v_reuseFailAlloc_193_;
goto v_reusejp_191_;
}
v_reusejp_191_:
{
return v___x_192_;
}
}
}
else
{
lean_object* v_a_195_; lean_object* v___x_196_; lean_object* v___x_197_; 
v_a_195_ = lean_ctor_get(v___x_184_, 0);
lean_inc(v_a_195_);
lean_dec_ref_known(v___x_184_, 1);
v___x_196_ = ((lean_object*)(l_Lean_instReprPosition_repr___redArg___closed__10));
v___x_197_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonPosition_fromJson_spec__0(v_json_182_, v___x_196_);
if (lean_obj_tag(v___x_197_) == 0)
{
lean_object* v_a_198_; lean_object* v___x_200_; uint8_t v_isShared_201_; uint8_t v_isSharedCheck_207_; 
lean_dec(v_a_195_);
v_a_198_ = lean_ctor_get(v___x_197_, 0);
v_isSharedCheck_207_ = !lean_is_exclusive(v___x_197_);
if (v_isSharedCheck_207_ == 0)
{
v___x_200_ = v___x_197_;
v_isShared_201_ = v_isSharedCheck_207_;
goto v_resetjp_199_;
}
else
{
lean_inc(v_a_198_);
lean_dec(v___x_197_);
v___x_200_ = lean_box(0);
v_isShared_201_ = v_isSharedCheck_207_;
goto v_resetjp_199_;
}
v_resetjp_199_:
{
lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_205_; 
v___x_202_ = lean_obj_once(&l_Lean_instFromJsonPosition_fromJson___closed__14, &l_Lean_instFromJsonPosition_fromJson___closed__14_once, _init_l_Lean_instFromJsonPosition_fromJson___closed__14);
v___x_203_ = lean_string_append(v___x_202_, v_a_198_);
lean_dec(v_a_198_);
if (v_isShared_201_ == 0)
{
lean_ctor_set(v___x_200_, 0, v___x_203_);
v___x_205_ = v___x_200_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_206_; 
v_reuseFailAlloc_206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_206_, 0, v___x_203_);
v___x_205_ = v_reuseFailAlloc_206_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
return v___x_205_;
}
}
}
else
{
lean_object* v_a_208_; lean_object* v___x_210_; uint8_t v_isShared_211_; uint8_t v_isSharedCheck_216_; 
v_a_208_ = lean_ctor_get(v___x_197_, 0);
v_isSharedCheck_216_ = !lean_is_exclusive(v___x_197_);
if (v_isSharedCheck_216_ == 0)
{
v___x_210_ = v___x_197_;
v_isShared_211_ = v_isSharedCheck_216_;
goto v_resetjp_209_;
}
else
{
lean_inc(v_a_208_);
lean_dec(v___x_197_);
v___x_210_ = lean_box(0);
v_isShared_211_ = v_isSharedCheck_216_;
goto v_resetjp_209_;
}
v_resetjp_209_:
{
lean_object* v___x_212_; lean_object* v___x_214_; 
v___x_212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_212_, 0, v_a_195_);
lean_ctor_set(v___x_212_, 1, v_a_208_);
if (v_isShared_211_ == 0)
{
lean_ctor_set(v___x_210_, 0, v___x_212_);
v___x_214_ = v___x_210_;
goto v_reusejp_213_;
}
else
{
lean_object* v_reuseFailAlloc_215_; 
v_reuseFailAlloc_215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v___x_212_);
v___x_214_ = v_reuseFailAlloc_215_;
goto v_reusejp_213_;
}
v_reusejp_213_:
{
return v___x_214_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Position_lt(lean_object* v_x_220_, lean_object* v_x_221_){
_start:
{
lean_object* v_line_222_; lean_object* v_column_223_; lean_object* v___x_225_; uint8_t v_isShared_226_; uint8_t v_isSharedCheck_242_; 
v_line_222_ = lean_ctor_get(v_x_220_, 0);
v_column_223_ = lean_ctor_get(v_x_220_, 1);
v_isSharedCheck_242_ = !lean_is_exclusive(v_x_220_);
if (v_isSharedCheck_242_ == 0)
{
v___x_225_ = v_x_220_;
v_isShared_226_ = v_isSharedCheck_242_;
goto v_resetjp_224_;
}
else
{
lean_inc(v_column_223_);
lean_inc(v_line_222_);
lean_dec(v_x_220_);
v___x_225_ = lean_box(0);
v_isShared_226_ = v_isSharedCheck_242_;
goto v_resetjp_224_;
}
v_resetjp_224_:
{
lean_object* v_line_227_; lean_object* v_column_228_; lean_object* v___x_230_; uint8_t v_isShared_231_; uint8_t v_isSharedCheck_241_; 
v_line_227_ = lean_ctor_get(v_x_221_, 0);
v_column_228_ = lean_ctor_get(v_x_221_, 1);
v_isSharedCheck_241_ = !lean_is_exclusive(v_x_221_);
if (v_isSharedCheck_241_ == 0)
{
v___x_230_ = v_x_221_;
v_isShared_231_ = v_isSharedCheck_241_;
goto v_resetjp_229_;
}
else
{
lean_inc(v_column_228_);
lean_inc(v_line_227_);
lean_dec(v_x_221_);
v___x_230_ = lean_box(0);
v_isShared_231_ = v_isSharedCheck_241_;
goto v_resetjp_229_;
}
v_resetjp_229_:
{
lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_235_; 
v___x_232_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___x_233_ = ((lean_object*)(l_Lean_Position_lt___closed__0));
if (v_isShared_231_ == 0)
{
lean_ctor_set(v___x_230_, 1, v_column_223_);
lean_ctor_set(v___x_230_, 0, v_line_222_);
v___x_235_ = v___x_230_;
goto v_reusejp_234_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v_line_222_);
lean_ctor_set(v_reuseFailAlloc_240_, 1, v_column_223_);
v___x_235_ = v_reuseFailAlloc_240_;
goto v_reusejp_234_;
}
v_reusejp_234_:
{
lean_object* v___x_237_; 
if (v_isShared_226_ == 0)
{
lean_ctor_set(v___x_225_, 1, v_column_228_);
lean_ctor_set(v___x_225_, 0, v_line_227_);
v___x_237_ = v___x_225_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v_line_227_);
lean_ctor_set(v_reuseFailAlloc_239_, 1, v_column_228_);
v___x_237_ = v_reuseFailAlloc_239_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
uint8_t v___x_238_; 
v___x_238_ = l_Prod_lexLtDec___redArg(v___x_232_, v___x_233_, v___x_233_, v___x_235_, v___x_237_);
return v___x_238_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Position_lt___boxed(lean_object* v_x_243_, lean_object* v_x_244_){
_start:
{
uint8_t v_res_245_; lean_object* v_r_246_; 
v_res_245_ = l_Lean_Position_lt(v_x_243_, v_x_244_);
v_r_246_ = lean_box(v_res_245_);
return v_r_246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Position_instToFormat___lam__0(lean_object* v_x_256_){
_start:
{
lean_object* v_line_257_; lean_object* v_column_258_; lean_object* v___x_260_; uint8_t v_isShared_261_; uint8_t v_isSharedCheck_275_; 
v_line_257_ = lean_ctor_get(v_x_256_, 0);
v_column_258_ = lean_ctor_get(v_x_256_, 1);
v_isSharedCheck_275_ = !lean_is_exclusive(v_x_256_);
if (v_isSharedCheck_275_ == 0)
{
v___x_260_ = v_x_256_;
v_isShared_261_ = v_isSharedCheck_275_;
goto v_resetjp_259_;
}
else
{
lean_inc(v_column_258_);
lean_inc(v_line_257_);
lean_dec(v_x_256_);
v___x_260_ = lean_box(0);
v_isShared_261_ = v_isSharedCheck_275_;
goto v_resetjp_259_;
}
v_resetjp_259_:
{
lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_266_; 
v___x_262_ = ((lean_object*)(l_Lean_Position_instToFormat___lam__0___closed__1));
v___x_263_ = l_Nat_reprFast(v_line_257_);
v___x_264_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_264_, 0, v___x_263_);
if (v_isShared_261_ == 0)
{
lean_ctor_set_tag(v___x_260_, 5);
lean_ctor_set(v___x_260_, 1, v___x_264_);
lean_ctor_set(v___x_260_, 0, v___x_262_);
v___x_266_ = v___x_260_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_274_; 
v_reuseFailAlloc_274_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_274_, 0, v___x_262_);
lean_ctor_set(v_reuseFailAlloc_274_, 1, v___x_264_);
v___x_266_ = v_reuseFailAlloc_274_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_267_ = ((lean_object*)(l_Lean_Position_instToFormat___lam__0___closed__3));
v___x_268_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_268_, 0, v___x_266_);
lean_ctor_set(v___x_268_, 1, v___x_267_);
v___x_269_ = l_Nat_reprFast(v_column_258_);
v___x_270_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_270_, 0, v___x_269_);
v___x_271_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_271_, 0, v___x_268_);
lean_ctor_set(v___x_271_, 1, v___x_270_);
v___x_272_ = ((lean_object*)(l_Lean_Position_instToFormat___lam__0___closed__5));
v___x_273_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_273_, 0, v___x_271_);
lean_ctor_set(v___x_273_, 1, v___x_272_);
return v___x_273_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Position_instToString___lam__0(lean_object* v_x_278_){
_start:
{
lean_object* v_line_279_; lean_object* v_column_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; 
v_line_279_ = lean_ctor_get(v_x_278_, 0);
lean_inc(v_line_279_);
v_column_280_ = lean_ctor_get(v_x_278_, 1);
lean_inc(v_column_280_);
lean_dec_ref(v_x_278_);
v___x_281_ = ((lean_object*)(l_Lean_Position_instToFormat___lam__0___closed__0));
v___x_282_ = l_Nat_reprFast(v_line_279_);
v___x_283_ = lean_string_append(v___x_281_, v___x_282_);
lean_dec_ref(v___x_282_);
v___x_284_ = ((lean_object*)(l_Lean_Position_instToFormat___lam__0___closed__2));
v___x_285_ = lean_string_append(v___x_283_, v___x_284_);
v___x_286_ = l_Nat_reprFast(v_column_280_);
v___x_287_ = lean_string_append(v___x_285_, v___x_286_);
lean_dec_ref(v___x_286_);
v___x_288_ = ((lean_object*)(l_Lean_Position_instToFormat___lam__0___closed__4));
v___x_289_ = lean_string_append(v___x_287_, v___x_288_);
return v___x_289_;
}
}
static lean_object* _init_l_Lean_Position_instToExpr___lam__0___closed__2(void){
_start:
{
lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_297_ = lean_box(0);
v___x_298_ = ((lean_object*)(l_Lean_Position_instToExpr___lam__0___closed__1));
v___x_299_ = l_Lean_mkConst(v___x_298_, v___x_297_);
return v___x_299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Position_instToExpr___lam__0(lean_object* v_p_300_){
_start:
{
lean_object* v_line_301_; lean_object* v_column_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
v_line_301_ = lean_ctor_get(v_p_300_, 0);
lean_inc(v_line_301_);
v_column_302_ = lean_ctor_get(v_p_300_, 1);
lean_inc(v_column_302_);
lean_dec_ref(v_p_300_);
v___x_303_ = lean_obj_once(&l_Lean_Position_instToExpr___lam__0___closed__2, &l_Lean_Position_instToExpr___lam__0___closed__2_once, _init_l_Lean_Position_instToExpr___lam__0___closed__2);
v___x_304_ = l_Lean_mkNatLit(v_line_301_);
v___x_305_ = l_Lean_mkNatLit(v_column_302_);
v___x_306_ = lean_unsigned_to_nat(2u);
v___x_307_ = lean_mk_empty_array_with_capacity(v___x_306_);
v___x_308_ = lean_array_push(v___x_307_, v___x_304_);
v___x_309_ = lean_array_push(v___x_308_, v___x_305_);
v___x_310_ = l_Lean_mkAppN(v___x_303_, v___x_309_);
lean_dec_ref(v___x_309_);
return v___x_310_;
}
}
static lean_object* _init_l_Lean_Position_instToExpr___closed__1(void){
_start:
{
lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_312_ = lean_box(0);
v___x_313_ = ((lean_object*)(l_Lean_instFromJsonPosition_fromJson___closed__2));
v___x_314_ = l_Lean_mkConst(v___x_313_, v___x_312_);
return v___x_314_;
}
}
static lean_object* _init_l_Lean_Position_instToExpr___closed__2(void){
_start:
{
lean_object* v___x_315_; lean_object* v___f_316_; lean_object* v___x_317_; 
v___x_315_ = lean_obj_once(&l_Lean_Position_instToExpr___closed__1, &l_Lean_Position_instToExpr___closed__1_once, _init_l_Lean_Position_instToExpr___closed__1);
v___f_316_ = ((lean_object*)(l_Lean_Position_instToExpr___closed__0));
v___x_317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_317_, 0, v___f_316_);
lean_ctor_set(v___x_317_, 1, v___x_315_);
return v___x_317_;
}
}
static lean_object* _init_l_Lean_Position_instToExpr(void){
_start:
{
lean_object* v___x_318_; 
v___x_318_ = lean_obj_once(&l_Lean_Position_instToExpr___closed__2, &l_Lean_Position_instToExpr___closed__2_once, _init_l_Lean_Position_instToExpr___closed__2);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_FileMap_getLastLine(lean_object* v_fmap_327_){
_start:
{
lean_object* v_positions_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v_positions_328_ = lean_ctor_get(v_fmap_327_, 1);
v___x_329_ = lean_array_get_size(v_positions_328_);
v___x_330_ = lean_unsigned_to_nat(1u);
v___x_331_ = lean_nat_sub(v___x_329_, v___x_330_);
return v___x_331_;
}
}
LEAN_EXPORT lean_object* l_Lean_FileMap_getLastLine___boxed(lean_object* v_fmap_332_){
_start:
{
lean_object* v_res_333_; 
v_res_333_ = l_Lean_FileMap_getLastLine(v_fmap_332_);
lean_dec_ref(v_fmap_332_);
return v_res_333_;
}
}
LEAN_EXPORT lean_object* l_Lean_FileMap_getLine(lean_object* v_fmap_334_, lean_object* v_x_335_){
_start:
{
lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; uint8_t v___x_339_; 
v___x_336_ = lean_unsigned_to_nat(1u);
v___x_337_ = lean_nat_add(v_x_335_, v___x_336_);
v___x_338_ = l_Lean_FileMap_getLastLine(v_fmap_334_);
v___x_339_ = lean_nat_dec_le(v___x_337_, v___x_338_);
if (v___x_339_ == 0)
{
lean_dec(v___x_337_);
return v___x_338_;
}
else
{
lean_dec(v___x_338_);
return v___x_337_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_FileMap_getLine___boxed(lean_object* v_fmap_340_, lean_object* v_x_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l_Lean_FileMap_getLine(v_fmap_340_, v_x_341_);
lean_dec(v_x_341_);
lean_dec_ref(v_fmap_340_);
return v_res_342_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Position_0__Lean_FileMap_ofString_loop(lean_object* v_s_343_, lean_object* v_i_344_, lean_object* v_ps_345_){
_start:
{
uint8_t v___x_346_; 
v___x_346_ = lean_string_utf8_at_end(v_s_343_, v_i_344_);
if (v___x_346_ == 0)
{
uint32_t v_c_347_; lean_object* v_i_348_; uint32_t v___x_349_; uint8_t v___x_350_; 
v_c_347_ = lean_string_utf8_get(v_s_343_, v_i_344_);
v_i_348_ = lean_string_utf8_next(v_s_343_, v_i_344_);
lean_dec(v_i_344_);
v___x_349_ = 10;
v___x_350_ = lean_uint32_dec_eq(v_c_347_, v___x_349_);
if (v___x_350_ == 0)
{
v_i_344_ = v_i_348_;
goto _start;
}
else
{
lean_object* v___x_352_; 
lean_inc(v_i_348_);
v___x_352_ = lean_array_push(v_ps_345_, v_i_348_);
v_i_344_ = v_i_348_;
v_ps_345_ = v___x_352_;
goto _start;
}
}
else
{
lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_354_ = lean_array_push(v_ps_345_, v_i_344_);
v___x_355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_355_, 0, v_s_343_);
lean_ctor_set(v___x_355_, 1, v___x_354_);
return v___x_355_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_FileMap_ofString(lean_object* v_s_360_){
_start:
{
lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_361_ = lean_unsigned_to_nat(0u);
v___x_362_ = ((lean_object*)(l_Lean_FileMap_ofString___closed__0));
v___x_363_ = l___private_Lean_Data_Position_0__Lean_FileMap_ofString_loop(v_s_360_, v___x_361_, v___x_362_);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Position_0__Lean_FileMap_toPosition_toColumn(lean_object* v_pos_364_, lean_object* v_str_365_, lean_object* v_i_366_, lean_object* v_c_367_){
_start:
{
uint8_t v_decide_368_; 
v_decide_368_ = lean_nat_dec_eq(v_i_366_, v_pos_364_);
if (v_decide_368_ == 0)
{
uint8_t v___x_369_; 
v___x_369_ = lean_string_utf8_at_end(v_str_365_, v_i_366_);
if (v___x_369_ == 0)
{
lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_370_ = lean_string_utf8_next(v_str_365_, v_i_366_);
lean_dec(v_i_366_);
v___x_371_ = lean_unsigned_to_nat(1u);
v___x_372_ = lean_nat_add(v_c_367_, v___x_371_);
lean_dec(v_c_367_);
v_i_366_ = v___x_370_;
v_c_367_ = v___x_372_;
goto _start;
}
else
{
lean_dec(v_i_366_);
return v_c_367_;
}
}
else
{
lean_dec(v_i_366_);
return v_c_367_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Position_0__Lean_FileMap_toPosition_toColumn___boxed(lean_object* v_pos_374_, lean_object* v_str_375_, lean_object* v_i_376_, lean_object* v_c_377_){
_start:
{
lean_object* v_res_378_; 
v_res_378_ = l___private_Lean_Data_Position_0__Lean_FileMap_toPosition_toColumn(v_pos_374_, v_str_375_, v_i_376_, v_c_377_);
lean_dec_ref(v_str_375_);
lean_dec(v_pos_374_);
return v_res_378_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Position_0__Lean_FileMap_toPosition_loop(lean_object* v_fmap_379_, lean_object* v_pos_380_, lean_object* v_str_381_, lean_object* v_ps_382_, lean_object* v_b_383_, lean_object* v_e_384_){
_start:
{
lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; uint8_t v___x_388_; 
v___x_385_ = lean_unsigned_to_nat(0u);
v___x_386_ = lean_unsigned_to_nat(1u);
v___x_387_ = lean_nat_add(v_b_383_, v___x_386_);
v___x_388_ = lean_nat_dec_eq(v_e_384_, v___x_387_);
lean_dec(v___x_387_);
if (v___x_388_ == 0)
{
lean_object* v___x_389_; lean_object* v_m_390_; lean_object* v_posM_391_; uint8_t v_decide_392_; 
v___x_389_ = lean_nat_add(v_b_383_, v_e_384_);
v_m_390_ = lean_nat_shiftr(v___x_389_, v___x_386_);
lean_dec(v___x_389_);
v_posM_391_ = lean_array_get_borrowed(v___x_385_, v_ps_382_, v_m_390_);
v_decide_392_ = lean_nat_dec_eq(v_pos_380_, v_posM_391_);
if (v_decide_392_ == 0)
{
lean_object* v___x_393_; uint8_t v___x_394_; 
v___x_393_ = lean_nat_add(v_posM_391_, v___x_386_);
v___x_394_ = lean_nat_dec_le(v___x_393_, v_pos_380_);
lean_dec(v___x_393_);
if (v___x_394_ == 0)
{
lean_dec(v_e_384_);
v_e_384_ = v_m_390_;
goto _start;
}
else
{
lean_dec(v_b_383_);
v_b_383_ = v_m_390_;
goto _start;
}
}
else
{
lean_object* v___x_397_; lean_object* v___x_398_; 
lean_dec(v_e_384_);
lean_dec(v_b_383_);
v___x_397_ = l_Lean_FileMap_getLine(v_fmap_379_, v_m_390_);
lean_dec(v_m_390_);
v___x_398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_398_, 0, v___x_397_);
lean_ctor_set(v___x_398_, 1, v___x_385_);
return v___x_398_;
}
}
else
{
lean_object* v_posB_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; 
lean_dec(v_e_384_);
v_posB_399_ = lean_array_get_borrowed(v___x_385_, v_ps_382_, v_b_383_);
v___x_400_ = l_Lean_FileMap_getLine(v_fmap_379_, v_b_383_);
lean_dec(v_b_383_);
lean_inc(v_posB_399_);
v___x_401_ = l___private_Lean_Data_Position_0__Lean_FileMap_toPosition_toColumn(v_pos_380_, v_str_381_, v_posB_399_, v___x_385_);
v___x_402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_402_, 0, v___x_400_);
lean_ctor_set(v___x_402_, 1, v___x_401_);
return v___x_402_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Position_0__Lean_FileMap_toPosition_loop___boxed(lean_object* v_fmap_403_, lean_object* v_pos_404_, lean_object* v_str_405_, lean_object* v_ps_406_, lean_object* v_b_407_, lean_object* v_e_408_){
_start:
{
lean_object* v_res_409_; 
v_res_409_ = l___private_Lean_Data_Position_0__Lean_FileMap_toPosition_loop(v_fmap_403_, v_pos_404_, v_str_405_, v_ps_406_, v_b_407_, v_e_408_);
lean_dec_ref(v_ps_406_);
lean_dec_ref(v_str_405_);
lean_dec(v_pos_404_);
lean_dec_ref(v_fmap_403_);
return v_res_409_;
}
}
LEAN_EXPORT lean_object* l_Lean_FileMap_toPosition(lean_object* v_fmap_410_, lean_object* v_pos_411_){
_start:
{
lean_object* v_source_412_; lean_object* v_positions_413_; lean_object* v___x_414_; lean_object* v___x_433_; lean_object* v___x_434_; uint8_t v___x_435_; 
v_source_412_ = lean_ctor_get(v_fmap_410_, 0);
v_positions_413_ = lean_ctor_get(v_fmap_410_, 1);
lean_inc_ref(v_positions_413_);
v___x_414_ = lean_unsigned_to_nat(0u);
v___x_433_ = lean_unsigned_to_nat(2u);
v___x_434_ = lean_array_get_size(v_positions_413_);
v___x_435_ = lean_nat_dec_le(v___x_433_, v___x_434_);
if (v___x_435_ == 0)
{
goto v___jp_415_;
}
else
{
lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; uint8_t v___x_439_; 
v___x_436_ = lean_unsigned_to_nat(1u);
v___x_437_ = lean_nat_sub(v___x_434_, v___x_436_);
v___x_438_ = lean_array_get_borrowed(v___x_414_, v_positions_413_, v___x_437_);
v___x_439_ = lean_nat_dec_le(v_pos_411_, v___x_438_);
if (v___x_439_ == 0)
{
lean_dec(v___x_437_);
goto v___jp_415_;
}
else
{
lean_object* v___x_440_; 
lean_inc_ref(v_source_412_);
v___x_440_ = l___private_Lean_Data_Position_0__Lean_FileMap_toPosition_loop(v_fmap_410_, v_pos_411_, v_source_412_, v_positions_413_, v___x_414_, v___x_437_);
lean_dec_ref(v_positions_413_);
lean_dec_ref(v_source_412_);
lean_dec_ref(v_fmap_410_);
return v___x_440_;
}
}
v___jp_415_:
{
lean_object* v___x_416_; uint8_t v___x_417_; 
v___x_416_ = lean_array_get_size(v_positions_413_);
v___x_417_ = lean_nat_dec_eq(v___x_416_, v___x_414_);
if (v___x_417_ == 0)
{
lean_object* v___x_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_429_; 
v___x_418_ = l_Lean_FileMap_getLastLine(v_fmap_410_);
v_isSharedCheck_429_ = !lean_is_exclusive(v_fmap_410_);
if (v_isSharedCheck_429_ == 0)
{
lean_object* v_unused_430_; lean_object* v_unused_431_; 
v_unused_430_ = lean_ctor_get(v_fmap_410_, 1);
lean_dec(v_unused_430_);
v_unused_431_ = lean_ctor_get(v_fmap_410_, 0);
lean_dec(v_unused_431_);
v___x_420_ = v_fmap_410_;
v_isShared_421_ = v_isSharedCheck_429_;
goto v_resetjp_419_;
}
else
{
lean_dec(v_fmap_410_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_429_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_427_; 
v___x_422_ = lean_unsigned_to_nat(1u);
v___x_423_ = lean_nat_sub(v___x_416_, v___x_422_);
v___x_424_ = lean_array_get(v___x_414_, v_positions_413_, v___x_423_);
lean_dec(v___x_423_);
lean_dec_ref(v_positions_413_);
v___x_425_ = lean_nat_sub(v_pos_411_, v___x_424_);
lean_dec(v___x_424_);
if (v_isShared_421_ == 0)
{
lean_ctor_set(v___x_420_, 1, v___x_425_);
lean_ctor_set(v___x_420_, 0, v___x_418_);
v___x_427_ = v___x_420_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v___x_418_);
lean_ctor_set(v_reuseFailAlloc_428_, 1, v___x_425_);
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
lean_object* v___x_432_; 
lean_dec_ref(v_positions_413_);
lean_dec_ref(v_fmap_410_);
v___x_432_ = ((lean_object*)(l_Lean_instInhabitedPosition_default___closed__0));
return v___x_432_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_FileMap_toPosition___boxed(lean_object* v_fmap_441_, lean_object* v_pos_442_){
_start:
{
lean_object* v_res_443_; 
v_res_443_ = l_Lean_FileMap_toPosition(v_fmap_441_, v_pos_442_);
lean_dec(v_pos_442_);
return v_res_443_;
}
}
LEAN_EXPORT lean_object* l_Lean_FileMap_ofPosition(lean_object* v_text_444_, lean_object* v_pos_445_){
_start:
{
lean_object* v_line_446_; lean_object* v_column_447_; lean_object* v_source_448_; lean_object* v_positions_449_; lean_object* v___y_451_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; uint8_t v___x_460_; 
v_line_446_ = lean_ctor_get(v_pos_445_, 0);
lean_inc(v_line_446_);
v_column_447_ = lean_ctor_get(v_pos_445_, 1);
lean_inc(v_column_447_);
lean_dec_ref(v_pos_445_);
v_source_448_ = lean_ctor_get(v_text_444_, 0);
v_positions_449_ = lean_ctor_get(v_text_444_, 1);
v___x_457_ = lean_unsigned_to_nat(1u);
v___x_458_ = lean_nat_sub(v_line_446_, v___x_457_);
lean_dec(v_line_446_);
v___x_459_ = lean_array_get_size(v_positions_449_);
v___x_460_ = lean_nat_dec_lt(v___x_458_, v___x_459_);
if (v___x_460_ == 0)
{
lean_object* v___x_461_; uint8_t v___x_462_; 
lean_dec(v___x_458_);
v___x_461_ = lean_unsigned_to_nat(0u);
v___x_462_ = lean_nat_dec_eq(v___x_459_, v___x_461_);
if (v___x_462_ == 0)
{
lean_object* v___x_463_; lean_object* v___x_464_; 
v___x_463_ = lean_nat_sub(v___x_459_, v___x_457_);
v___x_464_ = lean_array_get_borrowed(v___x_461_, v_positions_449_, v___x_463_);
lean_dec(v___x_463_);
v___y_451_ = v___x_464_;
goto v___jp_450_;
}
else
{
v___y_451_ = v___x_461_;
goto v___jp_450_;
}
}
else
{
lean_object* v___x_465_; 
v___x_465_ = lean_array_fget_borrowed(v_positions_449_, v___x_458_);
lean_dec(v___x_458_);
v___y_451_ = v___x_465_;
goto v___jp_450_;
}
v___jp_450_:
{
lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_452_ = lean_string_utf8_byte_size(v_source_448_);
v___x_453_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_source_448_);
v___x_454_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_454_, 0, v_source_448_);
lean_ctor_set(v___x_454_, 1, v___x_453_);
lean_ctor_set(v___x_454_, 2, v___x_452_);
v___x_455_ = l_String_Slice_pos_x21(v___x_454_, v___y_451_);
v___x_456_ = l_String_Slice_Pos_nextn(v___x_454_, v___x_455_, v_column_447_);
lean_dec_ref_known(v___x_454_, 3);
return v___x_456_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_FileMap_ofPosition___boxed(lean_object* v_text_466_, lean_object* v_pos_467_){
_start:
{
lean_object* v_res_468_; 
v_res_468_ = l_Lean_FileMap_ofPosition(v_text_466_, v_pos_467_);
lean_dec_ref(v_text_466_);
return v_res_468_;
}
}
LEAN_EXPORT lean_object* l_Lean_FileMap_lineStart(lean_object* v_map_469_, lean_object* v_line_470_){
_start:
{
lean_object* v_positions_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; uint8_t v___x_475_; 
v_positions_471_ = lean_ctor_get(v_map_469_, 1);
v___x_472_ = lean_unsigned_to_nat(1u);
v___x_473_ = lean_nat_sub(v_line_470_, v___x_472_);
v___x_474_ = lean_array_get_size(v_positions_471_);
v___x_475_ = lean_nat_dec_lt(v___x_473_, v___x_474_);
if (v___x_475_ == 0)
{
lean_object* v___x_476_; uint8_t v___x_477_; 
lean_dec(v___x_473_);
v___x_476_ = lean_nat_sub(v___x_474_, v___x_472_);
v___x_477_ = lean_nat_dec_lt(v___x_476_, v___x_474_);
if (v___x_477_ == 0)
{
lean_object* v___x_478_; 
lean_dec(v___x_476_);
v___x_478_ = lean_unsigned_to_nat(0u);
return v___x_478_;
}
else
{
lean_object* v___x_479_; 
v___x_479_ = lean_array_fget_borrowed(v_positions_471_, v___x_476_);
lean_dec(v___x_476_);
lean_inc(v___x_479_);
return v___x_479_;
}
}
else
{
lean_object* v___x_480_; 
v___x_480_ = lean_array_fget_borrowed(v_positions_471_, v___x_473_);
lean_dec(v___x_473_);
lean_inc(v___x_480_);
return v___x_480_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_FileMap_lineStart___boxed(lean_object* v_map_481_, lean_object* v_line_482_){
_start:
{
lean_object* v_res_483_; 
v_res_483_ = l_Lean_FileMap_lineStart(v_map_481_, v_line_482_);
lean_dec(v_line_482_);
lean_dec_ref(v_map_481_);
return v_res_483_;
}
}
LEAN_EXPORT lean_object* l_Lean_String_toFileMap(lean_object* v_s_484_){
_start:
{
lean_object* v___x_485_; 
v___x_485_ = l_Lean_FileMap_ofString(v_s_484_);
return v___x_485_;
}
}
lean_object* runtime_initialize_Lean_Data_Json_FromToJson_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_ToExpr(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_Position(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Data_Json_FromToJson_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_ToExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Position_instToExpr = _init_l_Lean_Position_instToExpr();
lean_mark_persistent(l_Lean_Position_instToExpr);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Data_Position(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Data_Json_FromToJson_Basic(uint8_t builtin);
lean_object* initialize_Lean_ToExpr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_Position(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_Json_FromToJson_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ToExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Position(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Data_Position(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Data_Position(builtin);
}
#ifdef __cplusplus
}
#endif

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
uint8_t l_Lean_instDecidableEqPosition_decEq(lean_object* v_x_5_, lean_object* v_x_6_){
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
LEAN_EXPORT void l_Lean_instDecidableEqPosition_decEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_5_ = stack[0].m_obj;
lean_object* v_x_6_ = stack[1].m_obj;
uint8_t v_res_13_;
v_res_13_ = l_Lean_instDecidableEqPosition_decEq(v_x_5_, v_x_6_);
stack->m_num = v_res_13_;
}
LEAN_EXPORT lean_object* l_Lean_instDecidableEqPosition_decEq___boxed(lean_object* v_x_14_, lean_object* v_x_15_){
_start:
{
uint8_t v_res_16_; lean_object* v_r_17_; 
v_res_16_ = l_Lean_instDecidableEqPosition_decEq(v_x_14_, v_x_15_);
lean_dec_ref(v_x_15_);
lean_dec_ref(v_x_14_);
v_r_17_ = lean_box(v_res_16_);
return v_r_17_;
}
}
uint8_t l_Lean_instDecidableEqPosition(lean_object* v_x_18_, lean_object* v_x_19_){
_start:
{
uint8_t v___x_20_; 
v___x_20_ = l_Lean_instDecidableEqPosition_decEq(v_x_18_, v_x_19_);
return v___x_20_;
}
}
LEAN_EXPORT void l_Lean_instDecidableEqPosition_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_18_ = stack[0].m_obj;
lean_object* v_x_19_ = stack[1].m_obj;
uint8_t v_res_21_;
v_res_21_ = l_Lean_instDecidableEqPosition(v_x_18_, v_x_19_);
stack->m_num = v_res_21_;
}
LEAN_EXPORT lean_object* l_Lean_instDecidableEqPosition___boxed(lean_object* v_x_22_, lean_object* v_x_23_){
_start:
{
uint8_t v_res_24_; lean_object* v_r_25_; 
v_res_24_ = l_Lean_instDecidableEqPosition(v_x_22_, v_x_23_);
lean_dec_ref(v_x_23_);
lean_dec_ref(v_x_22_);
v_r_25_ = lean_box(v_res_24_);
return v_r_25_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_instReprPosition_repr_spec__0(lean_object* v_a_26_){
_start:
{
lean_object* v___x_27_; 
v___x_27_ = lean_nat_to_int(v_a_26_);
return v___x_27_;
}
}
static lean_object* _init_l_Lean_instReprPosition_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_41_; lean_object* v___x_42_; 
v___x_41_ = lean_unsigned_to_nat(8u);
v___x_42_ = lean_nat_to_int(v___x_41_);
return v___x_42_;
}
}
static lean_object* _init_l_Lean_instReprPosition_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_49_; lean_object* v___x_50_; 
v___x_49_ = lean_unsigned_to_nat(10u);
v___x_50_ = lean_nat_to_int(v___x_49_);
return v___x_50_;
}
}
static lean_object* _init_l_Lean_instReprPosition_repr___redArg___closed__14(void){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_52_ = ((lean_object*)(l_Lean_instReprPosition_repr___redArg___closed__0));
v___x_53_ = lean_string_length(v___x_52_);
return v___x_53_;
}
}
static lean_object* _init_l_Lean_instReprPosition_repr___redArg___closed__15(void){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_54_ = lean_obj_once(&l_Lean_instReprPosition_repr___redArg___closed__14, &l_Lean_instReprPosition_repr___redArg___closed__14_once, _init_l_Lean_instReprPosition_repr___redArg___closed__14);
v___x_55_ = lean_nat_to_int(v___x_54_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprPosition_repr___redArg(lean_object* v_x_60_){
_start:
{
lean_object* v_line_61_; lean_object* v_column_62_; lean_object* v___x_64_; uint8_t v_isShared_65_; uint8_t v_isSharedCheck_97_; 
v_line_61_ = lean_ctor_get(v_x_60_, 0);
v_column_62_ = lean_ctor_get(v_x_60_, 1);
v_isSharedCheck_97_ = !lean_is_exclusive(v_x_60_);
if (v_isSharedCheck_97_ == 0)
{
v___x_64_ = v_x_60_;
v_isShared_65_ = v_isSharedCheck_97_;
goto v_resetjp_63_;
}
else
{
lean_inc(v_column_62_);
lean_inc(v_line_61_);
lean_dec(v_x_60_);
v___x_64_ = lean_box(0);
v_isShared_65_ = v_isSharedCheck_97_;
goto v_resetjp_63_;
}
v_resetjp_63_:
{
lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_72_; 
v___x_66_ = ((lean_object*)(l_Lean_instReprPosition_repr___redArg___closed__5));
v___x_67_ = ((lean_object*)(l_Lean_instReprPosition_repr___redArg___closed__6));
v___x_68_ = lean_obj_once(&l_Lean_instReprPosition_repr___redArg___closed__7, &l_Lean_instReprPosition_repr___redArg___closed__7_once, _init_l_Lean_instReprPosition_repr___redArg___closed__7);
v___x_69_ = l_Nat_reprFast(v_line_61_);
v___x_70_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_70_, 0, v___x_69_);
if (v_isShared_65_ == 0)
{
lean_ctor_set_tag(v___x_64_, 4);
lean_ctor_set(v___x_64_, 1, v___x_70_);
lean_ctor_set(v___x_64_, 0, v___x_68_);
v___x_72_ = v___x_64_;
goto v_reusejp_71_;
}
else
{
lean_object* v_reuseFailAlloc_96_; 
v_reuseFailAlloc_96_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_96_, 0, v___x_68_);
lean_ctor_set(v_reuseFailAlloc_96_, 1, v___x_70_);
v___x_72_ = v_reuseFailAlloc_96_;
goto v_reusejp_71_;
}
v_reusejp_71_:
{
uint8_t v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_73_ = 0;
v___x_74_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_74_, 0, v___x_72_);
lean_ctor_set_uint8(v___x_74_, sizeof(void*)*1, v___x_73_);
v___x_75_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_75_, 0, v___x_67_);
lean_ctor_set(v___x_75_, 1, v___x_74_);
v___x_76_ = ((lean_object*)(l_Lean_instReprPosition_repr___redArg___closed__9));
v___x_77_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_77_, 0, v___x_75_);
lean_ctor_set(v___x_77_, 1, v___x_76_);
v___x_78_ = lean_box(1);
v___x_79_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_79_, 0, v___x_77_);
lean_ctor_set(v___x_79_, 1, v___x_78_);
v___x_80_ = ((lean_object*)(l_Lean_instReprPosition_repr___redArg___closed__11));
v___x_81_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_81_, 0, v___x_79_);
lean_ctor_set(v___x_81_, 1, v___x_80_);
v___x_82_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_82_, 0, v___x_81_);
lean_ctor_set(v___x_82_, 1, v___x_66_);
v___x_83_ = lean_obj_once(&l_Lean_instReprPosition_repr___redArg___closed__12, &l_Lean_instReprPosition_repr___redArg___closed__12_once, _init_l_Lean_instReprPosition_repr___redArg___closed__12);
v___x_84_ = l_Nat_reprFast(v_column_62_);
v___x_85_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_85_, 0, v___x_84_);
v___x_86_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_86_, 0, v___x_83_);
lean_ctor_set(v___x_86_, 1, v___x_85_);
v___x_87_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_87_, 0, v___x_86_);
lean_ctor_set_uint8(v___x_87_, sizeof(void*)*1, v___x_73_);
v___x_88_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_88_, 0, v___x_82_);
lean_ctor_set(v___x_88_, 1, v___x_87_);
v___x_89_ = lean_obj_once(&l_Lean_instReprPosition_repr___redArg___closed__15, &l_Lean_instReprPosition_repr___redArg___closed__15_once, _init_l_Lean_instReprPosition_repr___redArg___closed__15);
v___x_90_ = ((lean_object*)(l_Lean_instReprPosition_repr___redArg___closed__16));
v___x_91_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_91_, 0, v___x_90_);
lean_ctor_set(v___x_91_, 1, v___x_88_);
v___x_92_ = ((lean_object*)(l_Lean_instReprPosition_repr___redArg___closed__17));
v___x_93_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_93_, 0, v___x_91_);
lean_ctor_set(v___x_93_, 1, v___x_92_);
v___x_94_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_94_, 0, v___x_89_);
lean_ctor_set(v___x_94_, 1, v___x_93_);
v___x_95_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_95_, 0, v___x_94_);
lean_ctor_set_uint8(v___x_95_, sizeof(void*)*1, v___x_73_);
return v___x_95_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprPosition_repr(lean_object* v_x_98_, lean_object* v_prec_99_){
_start:
{
lean_object* v___x_100_; 
v___x_100_ = l_Lean_instReprPosition_repr___redArg(v_x_98_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprPosition_repr___boxed(lean_object* v_x_101_, lean_object* v_prec_102_){
_start:
{
lean_object* v_res_103_; 
v_res_103_ = l_Lean_instReprPosition_repr(v_x_101_, v_prec_102_);
lean_dec(v_prec_102_);
return v_res_103_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonPosition_toJson_spec__0(lean_object* v_a_106_, lean_object* v_a_107_){
_start:
{
if (lean_obj_tag(v_a_106_) == 0)
{
lean_object* v___x_108_; 
v___x_108_ = lean_array_to_list(v_a_107_);
return v___x_108_;
}
else
{
lean_object* v_head_109_; lean_object* v_tail_110_; lean_object* v___x_111_; 
v_head_109_ = lean_ctor_get(v_a_106_, 0);
lean_inc(v_head_109_);
v_tail_110_ = lean_ctor_get(v_a_106_, 1);
lean_inc(v_tail_110_);
lean_dec_ref_known(v_a_106_, 2);
v___x_111_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_107_, v_head_109_);
v_a_106_ = v_tail_110_;
v_a_107_ = v___x_111_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonPosition_toJson(lean_object* v_x_115_){
_start:
{
lean_object* v_line_116_; lean_object* v_column_117_; lean_object* v___x_119_; uint8_t v_isShared_120_; uint8_t v_isSharedCheck_139_; 
v_line_116_ = lean_ctor_get(v_x_115_, 0);
v_column_117_ = lean_ctor_get(v_x_115_, 1);
v_isSharedCheck_139_ = !lean_is_exclusive(v_x_115_);
if (v_isSharedCheck_139_ == 0)
{
v___x_119_ = v_x_115_;
v_isShared_120_ = v_isSharedCheck_139_;
goto v_resetjp_118_;
}
else
{
lean_inc(v_column_117_);
lean_inc(v_line_116_);
lean_dec(v_x_115_);
v___x_119_ = lean_box(0);
v_isShared_120_ = v_isSharedCheck_139_;
goto v_resetjp_118_;
}
v_resetjp_118_:
{
lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_125_; 
v___x_121_ = ((lean_object*)(l_Lean_instReprPosition_repr___redArg___closed__1));
v___x_122_ = l_Lean_JsonNumber_fromNat(v_line_116_);
v___x_123_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_123_, 0, v___x_122_);
if (v_isShared_120_ == 0)
{
lean_ctor_set(v___x_119_, 1, v___x_123_);
lean_ctor_set(v___x_119_, 0, v___x_121_);
v___x_125_ = v___x_119_;
goto v_reusejp_124_;
}
else
{
lean_object* v_reuseFailAlloc_138_; 
v_reuseFailAlloc_138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_138_, 0, v___x_121_);
lean_ctor_set(v_reuseFailAlloc_138_, 1, v___x_123_);
v___x_125_ = v_reuseFailAlloc_138_;
goto v_reusejp_124_;
}
v_reusejp_124_:
{
lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_126_ = lean_box(0);
v___x_127_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_127_, 0, v___x_125_);
lean_ctor_set(v___x_127_, 1, v___x_126_);
v___x_128_ = ((lean_object*)(l_Lean_instReprPosition_repr___redArg___closed__10));
v___x_129_ = l_Lean_JsonNumber_fromNat(v_column_117_);
v___x_130_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_130_, 0, v___x_129_);
v___x_131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_131_, 0, v___x_128_);
lean_ctor_set(v___x_131_, 1, v___x_130_);
v___x_132_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_132_, 0, v___x_131_);
lean_ctor_set(v___x_132_, 1, v___x_126_);
v___x_133_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_133_, 0, v___x_132_);
lean_ctor_set(v___x_133_, 1, v___x_126_);
v___x_134_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_134_, 0, v___x_127_);
lean_ctor_set(v___x_134_, 1, v___x_133_);
v___x_135_ = ((lean_object*)(l_Lean_instToJsonPosition_toJson___closed__0));
v___x_136_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonPosition_toJson_spec__0(v___x_134_, v___x_135_);
v___x_137_ = l_Lean_Json_mkObj(v___x_136_);
lean_dec(v___x_136_);
return v___x_137_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonPosition_fromJson_spec__0(lean_object* v_j_142_, lean_object* v_k_143_){
_start:
{
lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_144_ = l_Lean_Json_getObjValD(v_j_142_, v_k_143_);
v___x_145_ = l_Lean_Json_getNat_x3f(v___x_144_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonPosition_fromJson_spec__0___boxed(lean_object* v_j_146_, lean_object* v_k_147_){
_start:
{
lean_object* v_res_148_; 
v_res_148_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonPosition_fromJson_spec__0(v_j_146_, v_k_147_);
lean_dec_ref(v_k_147_);
return v_res_148_;
}
}
static lean_object* _init_l_Lean_instFromJsonPosition_fromJson___closed__3(void){
_start:
{
uint8_t v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_154_ = 1;
v___x_155_ = ((lean_object*)(l_Lean_instFromJsonPosition_fromJson___closed__2));
v___x_156_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_155_, v___x_154_);
return v___x_156_;
}
}
static lean_object* _init_l_Lean_instFromJsonPosition_fromJson___closed__5(void){
_start:
{
lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_158_ = ((lean_object*)(l_Lean_instFromJsonPosition_fromJson___closed__4));
v___x_159_ = lean_obj_once(&l_Lean_instFromJsonPosition_fromJson___closed__3, &l_Lean_instFromJsonPosition_fromJson___closed__3_once, _init_l_Lean_instFromJsonPosition_fromJson___closed__3);
v___x_160_ = lean_string_append(v___x_159_, v___x_158_);
return v___x_160_;
}
}
static lean_object* _init_l_Lean_instFromJsonPosition_fromJson___closed__7(void){
_start:
{
uint8_t v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_163_ = 1;
v___x_164_ = ((lean_object*)(l_Lean_instFromJsonPosition_fromJson___closed__6));
v___x_165_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_164_, v___x_163_);
return v___x_165_;
}
}
static lean_object* _init_l_Lean_instFromJsonPosition_fromJson___closed__8(void){
_start:
{
lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_166_ = lean_obj_once(&l_Lean_instFromJsonPosition_fromJson___closed__7, &l_Lean_instFromJsonPosition_fromJson___closed__7_once, _init_l_Lean_instFromJsonPosition_fromJson___closed__7);
v___x_167_ = lean_obj_once(&l_Lean_instFromJsonPosition_fromJson___closed__5, &l_Lean_instFromJsonPosition_fromJson___closed__5_once, _init_l_Lean_instFromJsonPosition_fromJson___closed__5);
v___x_168_ = lean_string_append(v___x_167_, v___x_166_);
return v___x_168_;
}
}
static lean_object* _init_l_Lean_instFromJsonPosition_fromJson___closed__10(void){
_start:
{
lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
v___x_170_ = ((lean_object*)(l_Lean_instFromJsonPosition_fromJson___closed__9));
v___x_171_ = lean_obj_once(&l_Lean_instFromJsonPosition_fromJson___closed__8, &l_Lean_instFromJsonPosition_fromJson___closed__8_once, _init_l_Lean_instFromJsonPosition_fromJson___closed__8);
v___x_172_ = lean_string_append(v___x_171_, v___x_170_);
return v___x_172_;
}
}
static lean_object* _init_l_Lean_instFromJsonPosition_fromJson___closed__12(void){
_start:
{
uint8_t v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; 
v___x_175_ = 1;
v___x_176_ = ((lean_object*)(l_Lean_instFromJsonPosition_fromJson___closed__11));
v___x_177_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_176_, v___x_175_);
return v___x_177_;
}
}
static lean_object* _init_l_Lean_instFromJsonPosition_fromJson___closed__13(void){
_start:
{
lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_178_ = lean_obj_once(&l_Lean_instFromJsonPosition_fromJson___closed__12, &l_Lean_instFromJsonPosition_fromJson___closed__12_once, _init_l_Lean_instFromJsonPosition_fromJson___closed__12);
v___x_179_ = lean_obj_once(&l_Lean_instFromJsonPosition_fromJson___closed__5, &l_Lean_instFromJsonPosition_fromJson___closed__5_once, _init_l_Lean_instFromJsonPosition_fromJson___closed__5);
v___x_180_ = lean_string_append(v___x_179_, v___x_178_);
return v___x_180_;
}
}
static lean_object* _init_l_Lean_instFromJsonPosition_fromJson___closed__14(void){
_start:
{
lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_181_ = ((lean_object*)(l_Lean_instFromJsonPosition_fromJson___closed__9));
v___x_182_ = lean_obj_once(&l_Lean_instFromJsonPosition_fromJson___closed__13, &l_Lean_instFromJsonPosition_fromJson___closed__13_once, _init_l_Lean_instFromJsonPosition_fromJson___closed__13);
v___x_183_ = lean_string_append(v___x_182_, v___x_181_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonPosition_fromJson(lean_object* v_json_184_){
_start:
{
lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_185_ = ((lean_object*)(l_Lean_instReprPosition_repr___redArg___closed__1));
lean_inc(v_json_184_);
v___x_186_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonPosition_fromJson_spec__0(v_json_184_, v___x_185_);
if (lean_obj_tag(v___x_186_) == 0)
{
lean_object* v_a_187_; lean_object* v___x_189_; uint8_t v_isShared_190_; uint8_t v_isSharedCheck_196_; 
lean_dec(v_json_184_);
v_a_187_ = lean_ctor_get(v___x_186_, 0);
v_isSharedCheck_196_ = !lean_is_exclusive(v___x_186_);
if (v_isSharedCheck_196_ == 0)
{
v___x_189_ = v___x_186_;
v_isShared_190_ = v_isSharedCheck_196_;
goto v_resetjp_188_;
}
else
{
lean_inc(v_a_187_);
lean_dec(v___x_186_);
v___x_189_ = lean_box(0);
v_isShared_190_ = v_isSharedCheck_196_;
goto v_resetjp_188_;
}
v_resetjp_188_:
{
lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_194_; 
v___x_191_ = lean_obj_once(&l_Lean_instFromJsonPosition_fromJson___closed__10, &l_Lean_instFromJsonPosition_fromJson___closed__10_once, _init_l_Lean_instFromJsonPosition_fromJson___closed__10);
v___x_192_ = lean_string_append(v___x_191_, v_a_187_);
lean_dec(v_a_187_);
if (v_isShared_190_ == 0)
{
lean_ctor_set(v___x_189_, 0, v___x_192_);
v___x_194_ = v___x_189_;
goto v_reusejp_193_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v___x_192_);
v___x_194_ = v_reuseFailAlloc_195_;
goto v_reusejp_193_;
}
v_reusejp_193_:
{
return v___x_194_;
}
}
}
else
{
if (lean_obj_tag(v___x_186_) == 0)
{
lean_object* v_a_197_; lean_object* v___x_199_; uint8_t v_isShared_200_; uint8_t v_isSharedCheck_204_; 
lean_dec(v_json_184_);
v_a_197_ = lean_ctor_get(v___x_186_, 0);
v_isSharedCheck_204_ = !lean_is_exclusive(v___x_186_);
if (v_isSharedCheck_204_ == 0)
{
v___x_199_ = v___x_186_;
v_isShared_200_ = v_isSharedCheck_204_;
goto v_resetjp_198_;
}
else
{
lean_inc(v_a_197_);
lean_dec(v___x_186_);
v___x_199_ = lean_box(0);
v_isShared_200_ = v_isSharedCheck_204_;
goto v_resetjp_198_;
}
v_resetjp_198_:
{
lean_object* v___x_202_; 
if (v_isShared_200_ == 0)
{
lean_ctor_set_tag(v___x_199_, 0);
v___x_202_ = v___x_199_;
goto v_reusejp_201_;
}
else
{
lean_object* v_reuseFailAlloc_203_; 
v_reuseFailAlloc_203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_203_, 0, v_a_197_);
v___x_202_ = v_reuseFailAlloc_203_;
goto v_reusejp_201_;
}
v_reusejp_201_:
{
return v___x_202_;
}
}
}
else
{
lean_object* v_a_205_; lean_object* v___x_206_; lean_object* v___x_207_; 
v_a_205_ = lean_ctor_get(v___x_186_, 0);
lean_inc(v_a_205_);
lean_dec_ref_known(v___x_186_, 1);
v___x_206_ = ((lean_object*)(l_Lean_instReprPosition_repr___redArg___closed__10));
v___x_207_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonPosition_fromJson_spec__0(v_json_184_, v___x_206_);
if (lean_obj_tag(v___x_207_) == 0)
{
lean_object* v_a_208_; lean_object* v___x_210_; uint8_t v_isShared_211_; uint8_t v_isSharedCheck_217_; 
lean_dec(v_a_205_);
v_a_208_ = lean_ctor_get(v___x_207_, 0);
v_isSharedCheck_217_ = !lean_is_exclusive(v___x_207_);
if (v_isSharedCheck_217_ == 0)
{
v___x_210_ = v___x_207_;
v_isShared_211_ = v_isSharedCheck_217_;
goto v_resetjp_209_;
}
else
{
lean_inc(v_a_208_);
lean_dec(v___x_207_);
v___x_210_ = lean_box(0);
v_isShared_211_ = v_isSharedCheck_217_;
goto v_resetjp_209_;
}
v_resetjp_209_:
{
lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_215_; 
v___x_212_ = lean_obj_once(&l_Lean_instFromJsonPosition_fromJson___closed__14, &l_Lean_instFromJsonPosition_fromJson___closed__14_once, _init_l_Lean_instFromJsonPosition_fromJson___closed__14);
v___x_213_ = lean_string_append(v___x_212_, v_a_208_);
lean_dec(v_a_208_);
if (v_isShared_211_ == 0)
{
lean_ctor_set(v___x_210_, 0, v___x_213_);
v___x_215_ = v___x_210_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_216_; 
v_reuseFailAlloc_216_ = lean_alloc_ctor(0, 1, 0);
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
else
{
if (lean_obj_tag(v___x_207_) == 0)
{
lean_object* v_a_218_; lean_object* v___x_220_; uint8_t v_isShared_221_; uint8_t v_isSharedCheck_225_; 
lean_dec(v_a_205_);
v_a_218_ = lean_ctor_get(v___x_207_, 0);
v_isSharedCheck_225_ = !lean_is_exclusive(v___x_207_);
if (v_isSharedCheck_225_ == 0)
{
v___x_220_ = v___x_207_;
v_isShared_221_ = v_isSharedCheck_225_;
goto v_resetjp_219_;
}
else
{
lean_inc(v_a_218_);
lean_dec(v___x_207_);
v___x_220_ = lean_box(0);
v_isShared_221_ = v_isSharedCheck_225_;
goto v_resetjp_219_;
}
v_resetjp_219_:
{
lean_object* v___x_223_; 
if (v_isShared_221_ == 0)
{
lean_ctor_set_tag(v___x_220_, 0);
v___x_223_ = v___x_220_;
goto v_reusejp_222_;
}
else
{
lean_object* v_reuseFailAlloc_224_; 
v_reuseFailAlloc_224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_224_, 0, v_a_218_);
v___x_223_ = v_reuseFailAlloc_224_;
goto v_reusejp_222_;
}
v_reusejp_222_:
{
return v___x_223_;
}
}
}
else
{
lean_object* v_a_226_; lean_object* v___x_228_; uint8_t v_isShared_229_; uint8_t v_isSharedCheck_234_; 
v_a_226_ = lean_ctor_get(v___x_207_, 0);
v_isSharedCheck_234_ = !lean_is_exclusive(v___x_207_);
if (v_isSharedCheck_234_ == 0)
{
v___x_228_ = v___x_207_;
v_isShared_229_ = v_isSharedCheck_234_;
goto v_resetjp_227_;
}
else
{
lean_inc(v_a_226_);
lean_dec(v___x_207_);
v___x_228_ = lean_box(0);
v_isShared_229_ = v_isSharedCheck_234_;
goto v_resetjp_227_;
}
v_resetjp_227_:
{
lean_object* v___x_230_; lean_object* v___x_232_; 
v___x_230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_230_, 0, v_a_205_);
lean_ctor_set(v___x_230_, 1, v_a_226_);
if (v_isShared_229_ == 0)
{
lean_ctor_set(v___x_228_, 0, v___x_230_);
v___x_232_ = v___x_228_;
goto v_reusejp_231_;
}
else
{
lean_object* v_reuseFailAlloc_233_; 
v_reuseFailAlloc_233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_233_, 0, v___x_230_);
v___x_232_ = v_reuseFailAlloc_233_;
goto v_reusejp_231_;
}
v_reusejp_231_:
{
return v___x_232_;
}
}
}
}
}
}
}
}
uint8_t l_Lean_Position_lt(lean_object* v_x_238_, lean_object* v_x_239_){
_start:
{
lean_object* v_line_240_; lean_object* v_column_241_; lean_object* v___x_243_; uint8_t v_isShared_244_; uint8_t v_isSharedCheck_260_; 
v_line_240_ = lean_ctor_get(v_x_238_, 0);
v_column_241_ = lean_ctor_get(v_x_238_, 1);
v_isSharedCheck_260_ = !lean_is_exclusive(v_x_238_);
if (v_isSharedCheck_260_ == 0)
{
v___x_243_ = v_x_238_;
v_isShared_244_ = v_isSharedCheck_260_;
goto v_resetjp_242_;
}
else
{
lean_inc(v_column_241_);
lean_inc(v_line_240_);
lean_dec(v_x_238_);
v___x_243_ = lean_box(0);
v_isShared_244_ = v_isSharedCheck_260_;
goto v_resetjp_242_;
}
v_resetjp_242_:
{
lean_object* v_line_245_; lean_object* v_column_246_; lean_object* v___x_248_; uint8_t v_isShared_249_; uint8_t v_isSharedCheck_259_; 
v_line_245_ = lean_ctor_get(v_x_239_, 0);
v_column_246_ = lean_ctor_get(v_x_239_, 1);
v_isSharedCheck_259_ = !lean_is_exclusive(v_x_239_);
if (v_isSharedCheck_259_ == 0)
{
v___x_248_ = v_x_239_;
v_isShared_249_ = v_isSharedCheck_259_;
goto v_resetjp_247_;
}
else
{
lean_inc(v_column_246_);
lean_inc(v_line_245_);
lean_dec(v_x_239_);
v___x_248_ = lean_box(0);
v_isShared_249_ = v_isSharedCheck_259_;
goto v_resetjp_247_;
}
v_resetjp_247_:
{
lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_253_; 
v___x_250_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___x_251_ = ((lean_object*)(l_Lean_Position_lt___closed__0));
if (v_isShared_249_ == 0)
{
lean_ctor_set(v___x_248_, 1, v_column_241_);
lean_ctor_set(v___x_248_, 0, v_line_240_);
v___x_253_ = v___x_248_;
goto v_reusejp_252_;
}
else
{
lean_object* v_reuseFailAlloc_258_; 
v_reuseFailAlloc_258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_258_, 0, v_line_240_);
lean_ctor_set(v_reuseFailAlloc_258_, 1, v_column_241_);
v___x_253_ = v_reuseFailAlloc_258_;
goto v_reusejp_252_;
}
v_reusejp_252_:
{
lean_object* v___x_255_; 
if (v_isShared_244_ == 0)
{
lean_ctor_set(v___x_243_, 1, v_column_246_);
lean_ctor_set(v___x_243_, 0, v_line_245_);
v___x_255_ = v___x_243_;
goto v_reusejp_254_;
}
else
{
lean_object* v_reuseFailAlloc_257_; 
v_reuseFailAlloc_257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_257_, 0, v_line_245_);
lean_ctor_set(v_reuseFailAlloc_257_, 1, v_column_246_);
v___x_255_ = v_reuseFailAlloc_257_;
goto v_reusejp_254_;
}
v_reusejp_254_:
{
uint8_t v___x_256_; 
v___x_256_ = l_Prod_lexLtDec___redArg(v___x_250_, v___x_251_, v___x_251_, v___x_253_, v___x_255_);
return v___x_256_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Position_lt_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_238_ = stack[0].m_obj;
lean_object* v_x_239_ = stack[1].m_obj;
uint8_t v_res_261_;
v_res_261_ = l_Lean_Position_lt(v_x_238_, v_x_239_);
stack->m_num = v_res_261_;
}
LEAN_EXPORT lean_object* l_Lean_Position_lt___boxed(lean_object* v_x_262_, lean_object* v_x_263_){
_start:
{
uint8_t v_res_264_; lean_object* v_r_265_; 
v_res_264_ = l_Lean_Position_lt(v_x_262_, v_x_263_);
v_r_265_ = lean_box(v_res_264_);
return v_r_265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Position_instToFormat___lam__0(lean_object* v_x_275_){
_start:
{
lean_object* v_line_276_; lean_object* v_column_277_; lean_object* v___x_279_; uint8_t v_isShared_280_; uint8_t v_isSharedCheck_294_; 
v_line_276_ = lean_ctor_get(v_x_275_, 0);
v_column_277_ = lean_ctor_get(v_x_275_, 1);
v_isSharedCheck_294_ = !lean_is_exclusive(v_x_275_);
if (v_isSharedCheck_294_ == 0)
{
v___x_279_ = v_x_275_;
v_isShared_280_ = v_isSharedCheck_294_;
goto v_resetjp_278_;
}
else
{
lean_inc(v_column_277_);
lean_inc(v_line_276_);
lean_dec(v_x_275_);
v___x_279_ = lean_box(0);
v_isShared_280_ = v_isSharedCheck_294_;
goto v_resetjp_278_;
}
v_resetjp_278_:
{
lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_285_; 
v___x_281_ = ((lean_object*)(l_Lean_Position_instToFormat___lam__0___closed__1));
v___x_282_ = l_Nat_reprFast(v_line_276_);
v___x_283_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_283_, 0, v___x_282_);
if (v_isShared_280_ == 0)
{
lean_ctor_set_tag(v___x_279_, 5);
lean_ctor_set(v___x_279_, 1, v___x_283_);
lean_ctor_set(v___x_279_, 0, v___x_281_);
v___x_285_ = v___x_279_;
goto v_reusejp_284_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v___x_281_);
lean_ctor_set(v_reuseFailAlloc_293_, 1, v___x_283_);
v___x_285_ = v_reuseFailAlloc_293_;
goto v_reusejp_284_;
}
v_reusejp_284_:
{
lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_286_ = ((lean_object*)(l_Lean_Position_instToFormat___lam__0___closed__3));
v___x_287_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_287_, 0, v___x_285_);
lean_ctor_set(v___x_287_, 1, v___x_286_);
v___x_288_ = l_Nat_reprFast(v_column_277_);
v___x_289_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_289_, 0, v___x_288_);
v___x_290_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_290_, 0, v___x_287_);
lean_ctor_set(v___x_290_, 1, v___x_289_);
v___x_291_ = ((lean_object*)(l_Lean_Position_instToFormat___lam__0___closed__5));
v___x_292_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_292_, 0, v___x_290_);
lean_ctor_set(v___x_292_, 1, v___x_291_);
return v___x_292_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Position_instToString___lam__0(lean_object* v_x_297_){
_start:
{
lean_object* v_line_298_; lean_object* v_column_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; 
v_line_298_ = lean_ctor_get(v_x_297_, 0);
lean_inc(v_line_298_);
v_column_299_ = lean_ctor_get(v_x_297_, 1);
lean_inc(v_column_299_);
lean_dec_ref(v_x_297_);
v___x_300_ = ((lean_object*)(l_Lean_Position_instToFormat___lam__0___closed__0));
v___x_301_ = l_Nat_reprFast(v_line_298_);
v___x_302_ = lean_string_append(v___x_300_, v___x_301_);
lean_dec_ref(v___x_301_);
v___x_303_ = ((lean_object*)(l_Lean_Position_instToFormat___lam__0___closed__2));
v___x_304_ = lean_string_append(v___x_302_, v___x_303_);
v___x_305_ = l_Nat_reprFast(v_column_299_);
v___x_306_ = lean_string_append(v___x_304_, v___x_305_);
lean_dec_ref(v___x_305_);
v___x_307_ = ((lean_object*)(l_Lean_Position_instToFormat___lam__0___closed__4));
v___x_308_ = lean_string_append(v___x_306_, v___x_307_);
return v___x_308_;
}
}
static lean_object* _init_l_Lean_Position_instToExpr___lam__0___closed__2(void){
_start:
{
lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_316_ = lean_box(0);
v___x_317_ = ((lean_object*)(l_Lean_Position_instToExpr___lam__0___closed__1));
v___x_318_ = l_Lean_mkConst(v___x_317_, v___x_316_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Position_instToExpr___lam__0(lean_object* v_p_319_){
_start:
{
lean_object* v_line_320_; lean_object* v_column_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; 
v_line_320_ = lean_ctor_get(v_p_319_, 0);
lean_inc(v_line_320_);
v_column_321_ = lean_ctor_get(v_p_319_, 1);
lean_inc(v_column_321_);
lean_dec_ref(v_p_319_);
v___x_322_ = lean_obj_once(&l_Lean_Position_instToExpr___lam__0___closed__2, &l_Lean_Position_instToExpr___lam__0___closed__2_once, _init_l_Lean_Position_instToExpr___lam__0___closed__2);
v___x_323_ = l_Lean_mkNatLit(v_line_320_);
v___x_324_ = l_Lean_mkNatLit(v_column_321_);
v___x_325_ = lean_unsigned_to_nat(2u);
v___x_326_ = lean_mk_empty_array_with_capacity(v___x_325_);
v___x_327_ = lean_array_push(v___x_326_, v___x_323_);
v___x_328_ = lean_array_push(v___x_327_, v___x_324_);
v___x_329_ = l_Lean_mkAppN(v___x_322_, v___x_328_);
lean_dec_ref(v___x_328_);
return v___x_329_;
}
}
static lean_object* _init_l_Lean_Position_instToExpr___closed__1(void){
_start:
{
lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_331_ = lean_box(0);
v___x_332_ = ((lean_object*)(l_Lean_instFromJsonPosition_fromJson___closed__2));
v___x_333_ = l_Lean_mkConst(v___x_332_, v___x_331_);
return v___x_333_;
}
}
static lean_object* _init_l_Lean_Position_instToExpr___closed__2(void){
_start:
{
lean_object* v___x_334_; lean_object* v___f_335_; lean_object* v___x_336_; 
v___x_334_ = lean_obj_once(&l_Lean_Position_instToExpr___closed__1, &l_Lean_Position_instToExpr___closed__1_once, _init_l_Lean_Position_instToExpr___closed__1);
v___f_335_ = ((lean_object*)(l_Lean_Position_instToExpr___closed__0));
v___x_336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_336_, 0, v___f_335_);
lean_ctor_set(v___x_336_, 1, v___x_334_);
return v___x_336_;
}
}
static lean_object* _init_l_Lean_Position_instToExpr(void){
_start:
{
lean_object* v___x_337_; 
v___x_337_ = lean_obj_once(&l_Lean_Position_instToExpr___closed__2, &l_Lean_Position_instToExpr___closed__2_once, _init_l_Lean_Position_instToExpr___closed__2);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l_Lean_FileMap_getLastLine(lean_object* v_fmap_346_){
_start:
{
lean_object* v_positions_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; 
v_positions_347_ = lean_ctor_get(v_fmap_346_, 1);
v___x_348_ = lean_array_get_size(v_positions_347_);
v___x_349_ = lean_unsigned_to_nat(1u);
v___x_350_ = lean_nat_sub(v___x_348_, v___x_349_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l_Lean_FileMap_getLastLine___boxed(lean_object* v_fmap_351_){
_start:
{
lean_object* v_res_352_; 
v_res_352_ = l_Lean_FileMap_getLastLine(v_fmap_351_);
lean_dec_ref(v_fmap_351_);
return v_res_352_;
}
}
LEAN_EXPORT lean_object* l_Lean_FileMap_getLine(lean_object* v_fmap_353_, lean_object* v_x_354_){
_start:
{
lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; uint8_t v___x_358_; 
v___x_355_ = lean_unsigned_to_nat(1u);
v___x_356_ = lean_nat_add(v_x_354_, v___x_355_);
v___x_357_ = l_Lean_FileMap_getLastLine(v_fmap_353_);
v___x_358_ = lean_nat_dec_le(v___x_356_, v___x_357_);
if (v___x_358_ == 0)
{
lean_dec(v___x_356_);
return v___x_357_;
}
else
{
lean_dec(v___x_357_);
return v___x_356_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_FileMap_getLine___boxed(lean_object* v_fmap_359_, lean_object* v_x_360_){
_start:
{
lean_object* v_res_361_; 
v_res_361_ = l_Lean_FileMap_getLine(v_fmap_359_, v_x_360_);
lean_dec(v_x_360_);
lean_dec_ref(v_fmap_359_);
return v_res_361_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Position_0__Lean_FileMap_ofString_loop(lean_object* v_s_362_, lean_object* v_i_363_, lean_object* v_ps_364_){
_start:
{
uint8_t v___x_365_; 
v___x_365_ = lean_string_utf8_at_end(v_s_362_, v_i_363_);
if (v___x_365_ == 0)
{
uint32_t v_c_366_; lean_object* v_i_367_; uint32_t v___x_368_; uint8_t v___x_369_; 
v_c_366_ = lean_string_utf8_get(v_s_362_, v_i_363_);
v_i_367_ = lean_string_utf8_next(v_s_362_, v_i_363_);
lean_dec(v_i_363_);
v___x_368_ = 10;
v___x_369_ = lean_uint32_dec_eq(v_c_366_, v___x_368_);
if (v___x_369_ == 0)
{
v_i_363_ = v_i_367_;
goto _start;
}
else
{
lean_object* v___x_371_; 
lean_inc(v_i_367_);
v___x_371_ = lean_array_push(v_ps_364_, v_i_367_);
v_i_363_ = v_i_367_;
v_ps_364_ = v___x_371_;
goto _start;
}
}
else
{
lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_373_ = lean_array_push(v_ps_364_, v_i_363_);
v___x_374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_374_, 0, v_s_362_);
lean_ctor_set(v___x_374_, 1, v___x_373_);
return v___x_374_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_FileMap_ofString(lean_object* v_s_379_){
_start:
{
lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_380_ = lean_unsigned_to_nat(0u);
v___x_381_ = ((lean_object*)(l_Lean_FileMap_ofString___closed__0));
v___x_382_ = l___private_Lean_Data_Position_0__Lean_FileMap_ofString_loop(v_s_379_, v___x_380_, v___x_381_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Position_0__Lean_FileMap_toPosition_toColumn(lean_object* v_pos_383_, lean_object* v_str_384_, lean_object* v_i_385_, lean_object* v_c_386_){
_start:
{
uint8_t v_decide_387_; 
v_decide_387_ = lean_nat_dec_eq(v_i_385_, v_pos_383_);
if (v_decide_387_ == 0)
{
uint8_t v___x_388_; 
v___x_388_ = lean_string_utf8_at_end(v_str_384_, v_i_385_);
if (v___x_388_ == 0)
{
lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; 
v___x_389_ = lean_string_utf8_next(v_str_384_, v_i_385_);
lean_dec(v_i_385_);
v___x_390_ = lean_unsigned_to_nat(1u);
v___x_391_ = lean_nat_add(v_c_386_, v___x_390_);
lean_dec(v_c_386_);
v_i_385_ = v___x_389_;
v_c_386_ = v___x_391_;
goto _start;
}
else
{
lean_dec(v_i_385_);
return v_c_386_;
}
}
else
{
lean_dec(v_i_385_);
return v_c_386_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Position_0__Lean_FileMap_toPosition_toColumn___boxed(lean_object* v_pos_393_, lean_object* v_str_394_, lean_object* v_i_395_, lean_object* v_c_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l___private_Lean_Data_Position_0__Lean_FileMap_toPosition_toColumn(v_pos_393_, v_str_394_, v_i_395_, v_c_396_);
lean_dec_ref(v_str_394_);
lean_dec(v_pos_393_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Position_0__Lean_FileMap_toPosition_loop(lean_object* v_fmap_398_, lean_object* v_pos_399_, lean_object* v_str_400_, lean_object* v_ps_401_, lean_object* v_b_402_, lean_object* v_e_403_){
_start:
{
lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; uint8_t v___x_407_; 
v___x_404_ = lean_unsigned_to_nat(0u);
v___x_405_ = lean_unsigned_to_nat(1u);
v___x_406_ = lean_nat_add(v_b_402_, v___x_405_);
v___x_407_ = lean_nat_dec_eq(v_e_403_, v___x_406_);
lean_dec(v___x_406_);
if (v___x_407_ == 0)
{
lean_object* v___x_408_; lean_object* v_m_409_; lean_object* v_posM_410_; uint8_t v_decide_411_; 
v___x_408_ = lean_nat_add(v_b_402_, v_e_403_);
v_m_409_ = lean_nat_shiftr(v___x_408_, v___x_405_);
lean_dec(v___x_408_);
v_posM_410_ = lean_array_get_borrowed(v___x_404_, v_ps_401_, v_m_409_);
v_decide_411_ = lean_nat_dec_eq(v_pos_399_, v_posM_410_);
if (v_decide_411_ == 0)
{
lean_object* v___x_412_; uint8_t v___x_413_; 
v___x_412_ = lean_nat_add(v_posM_410_, v___x_405_);
v___x_413_ = lean_nat_dec_le(v___x_412_, v_pos_399_);
lean_dec(v___x_412_);
if (v___x_413_ == 0)
{
lean_dec(v_e_403_);
v_e_403_ = v_m_409_;
goto _start;
}
else
{
lean_dec(v_b_402_);
v_b_402_ = v_m_409_;
goto _start;
}
}
else
{
lean_object* v___x_416_; lean_object* v___x_417_; 
lean_dec(v_e_403_);
lean_dec(v_b_402_);
v___x_416_ = l_Lean_FileMap_getLine(v_fmap_398_, v_m_409_);
lean_dec(v_m_409_);
v___x_417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_417_, 0, v___x_416_);
lean_ctor_set(v___x_417_, 1, v___x_404_);
return v___x_417_;
}
}
else
{
lean_object* v_posB_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; 
lean_dec(v_e_403_);
v_posB_418_ = lean_array_get_borrowed(v___x_404_, v_ps_401_, v_b_402_);
v___x_419_ = l_Lean_FileMap_getLine(v_fmap_398_, v_b_402_);
lean_dec(v_b_402_);
lean_inc(v_posB_418_);
v___x_420_ = l___private_Lean_Data_Position_0__Lean_FileMap_toPosition_toColumn(v_pos_399_, v_str_400_, v_posB_418_, v___x_404_);
v___x_421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_421_, 0, v___x_419_);
lean_ctor_set(v___x_421_, 1, v___x_420_);
return v___x_421_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Position_0__Lean_FileMap_toPosition_loop___boxed(lean_object* v_fmap_422_, lean_object* v_pos_423_, lean_object* v_str_424_, lean_object* v_ps_425_, lean_object* v_b_426_, lean_object* v_e_427_){
_start:
{
lean_object* v_res_428_; 
v_res_428_ = l___private_Lean_Data_Position_0__Lean_FileMap_toPosition_loop(v_fmap_422_, v_pos_423_, v_str_424_, v_ps_425_, v_b_426_, v_e_427_);
lean_dec_ref(v_ps_425_);
lean_dec_ref(v_str_424_);
lean_dec(v_pos_423_);
lean_dec_ref(v_fmap_422_);
return v_res_428_;
}
}
LEAN_EXPORT lean_object* l_Lean_FileMap_toPosition(lean_object* v_fmap_429_, lean_object* v_pos_430_){
_start:
{
lean_object* v_source_431_; lean_object* v_positions_432_; lean_object* v___x_433_; lean_object* v___x_452_; lean_object* v___x_453_; uint8_t v___x_454_; 
v_source_431_ = lean_ctor_get(v_fmap_429_, 0);
v_positions_432_ = lean_ctor_get(v_fmap_429_, 1);
lean_inc_ref(v_positions_432_);
v___x_433_ = lean_unsigned_to_nat(0u);
v___x_452_ = lean_unsigned_to_nat(2u);
v___x_453_ = lean_array_get_size(v_positions_432_);
v___x_454_ = lean_nat_dec_le(v___x_452_, v___x_453_);
if (v___x_454_ == 0)
{
goto v___jp_434_;
}
else
{
lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; uint8_t v___x_458_; 
v___x_455_ = lean_unsigned_to_nat(1u);
v___x_456_ = lean_nat_sub(v___x_453_, v___x_455_);
v___x_457_ = lean_array_get_borrowed(v___x_433_, v_positions_432_, v___x_456_);
v___x_458_ = lean_nat_dec_le(v_pos_430_, v___x_457_);
if (v___x_458_ == 0)
{
lean_dec(v___x_456_);
goto v___jp_434_;
}
else
{
lean_object* v___x_459_; 
lean_inc_ref(v_source_431_);
v___x_459_ = l___private_Lean_Data_Position_0__Lean_FileMap_toPosition_loop(v_fmap_429_, v_pos_430_, v_source_431_, v_positions_432_, v___x_433_, v___x_456_);
lean_dec_ref(v_positions_432_);
lean_dec_ref(v_source_431_);
lean_dec_ref(v_fmap_429_);
return v___x_459_;
}
}
v___jp_434_:
{
lean_object* v___x_435_; uint8_t v___x_436_; 
v___x_435_ = lean_array_get_size(v_positions_432_);
v___x_436_ = lean_nat_dec_eq(v___x_435_, v___x_433_);
if (v___x_436_ == 0)
{
lean_object* v___x_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_448_; 
v___x_437_ = l_Lean_FileMap_getLastLine(v_fmap_429_);
v_isSharedCheck_448_ = !lean_is_exclusive(v_fmap_429_);
if (v_isSharedCheck_448_ == 0)
{
lean_object* v_unused_449_; lean_object* v_unused_450_; 
v_unused_449_ = lean_ctor_get(v_fmap_429_, 1);
lean_dec(v_unused_449_);
v_unused_450_ = lean_ctor_get(v_fmap_429_, 0);
lean_dec(v_unused_450_);
v___x_439_ = v_fmap_429_;
v_isShared_440_ = v_isSharedCheck_448_;
goto v_resetjp_438_;
}
else
{
lean_dec(v_fmap_429_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_448_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_446_; 
v___x_441_ = lean_unsigned_to_nat(1u);
v___x_442_ = lean_nat_sub(v___x_435_, v___x_441_);
v___x_443_ = lean_array_get(v___x_433_, v_positions_432_, v___x_442_);
lean_dec(v___x_442_);
lean_dec_ref(v_positions_432_);
v___x_444_ = lean_nat_sub(v_pos_430_, v___x_443_);
lean_dec(v___x_443_);
if (v_isShared_440_ == 0)
{
lean_ctor_set(v___x_439_, 1, v___x_444_);
lean_ctor_set(v___x_439_, 0, v___x_437_);
v___x_446_ = v___x_439_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v___x_437_);
lean_ctor_set(v_reuseFailAlloc_447_, 1, v___x_444_);
v___x_446_ = v_reuseFailAlloc_447_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
return v___x_446_;
}
}
}
else
{
lean_object* v___x_451_; 
lean_dec_ref(v_positions_432_);
lean_dec_ref(v_fmap_429_);
v___x_451_ = ((lean_object*)(l_Lean_instInhabitedPosition_default___closed__0));
return v___x_451_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_FileMap_toPosition___boxed(lean_object* v_fmap_460_, lean_object* v_pos_461_){
_start:
{
lean_object* v_res_462_; 
v_res_462_ = l_Lean_FileMap_toPosition(v_fmap_460_, v_pos_461_);
lean_dec(v_pos_461_);
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l_Lean_FileMap_ofPosition(lean_object* v_text_463_, lean_object* v_pos_464_){
_start:
{
lean_object* v_line_465_; lean_object* v_column_466_; lean_object* v_source_467_; lean_object* v_positions_468_; lean_object* v___y_470_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; uint8_t v___x_479_; 
v_line_465_ = lean_ctor_get(v_pos_464_, 0);
lean_inc(v_line_465_);
v_column_466_ = lean_ctor_get(v_pos_464_, 1);
lean_inc(v_column_466_);
lean_dec_ref(v_pos_464_);
v_source_467_ = lean_ctor_get(v_text_463_, 0);
v_positions_468_ = lean_ctor_get(v_text_463_, 1);
v___x_476_ = lean_unsigned_to_nat(1u);
v___x_477_ = lean_nat_sub(v_line_465_, v___x_476_);
lean_dec(v_line_465_);
v___x_478_ = lean_array_get_size(v_positions_468_);
v___x_479_ = lean_nat_dec_lt(v___x_477_, v___x_478_);
if (v___x_479_ == 0)
{
lean_object* v___x_480_; uint8_t v___x_481_; 
lean_dec(v___x_477_);
v___x_480_ = lean_unsigned_to_nat(0u);
v___x_481_ = lean_nat_dec_eq(v___x_478_, v___x_480_);
if (v___x_481_ == 0)
{
lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_482_ = lean_nat_sub(v___x_478_, v___x_476_);
v___x_483_ = lean_array_get_borrowed(v___x_480_, v_positions_468_, v___x_482_);
lean_dec(v___x_482_);
v___y_470_ = v___x_483_;
goto v___jp_469_;
}
else
{
v___y_470_ = v___x_480_;
goto v___jp_469_;
}
}
else
{
lean_object* v___x_484_; 
v___x_484_ = lean_array_fget_borrowed(v_positions_468_, v___x_477_);
lean_dec(v___x_477_);
v___y_470_ = v___x_484_;
goto v___jp_469_;
}
v___jp_469_:
{
lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; 
v___x_471_ = lean_string_utf8_byte_size(v_source_467_);
v___x_472_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_source_467_);
v___x_473_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_473_, 0, v_source_467_);
lean_ctor_set(v___x_473_, 1, v___x_472_);
lean_ctor_set(v___x_473_, 2, v___x_471_);
v___x_474_ = l_String_Slice_pos_x21(v___x_473_, v___y_470_);
v___x_475_ = l_String_Slice_Pos_nextn(v___x_473_, v___x_474_, v_column_466_);
lean_dec_ref_known(v___x_473_, 3);
return v___x_475_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_FileMap_ofPosition___boxed(lean_object* v_text_485_, lean_object* v_pos_486_){
_start:
{
lean_object* v_res_487_; 
v_res_487_ = l_Lean_FileMap_ofPosition(v_text_485_, v_pos_486_);
lean_dec_ref(v_text_485_);
return v_res_487_;
}
}
LEAN_EXPORT lean_object* l_Lean_FileMap_lineStart(lean_object* v_map_488_, lean_object* v_line_489_){
_start:
{
lean_object* v_positions_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; uint8_t v___x_494_; 
v_positions_490_ = lean_ctor_get(v_map_488_, 1);
v___x_491_ = lean_unsigned_to_nat(1u);
v___x_492_ = lean_nat_sub(v_line_489_, v___x_491_);
v___x_493_ = lean_array_get_size(v_positions_490_);
v___x_494_ = lean_nat_dec_lt(v___x_492_, v___x_493_);
if (v___x_494_ == 0)
{
lean_object* v___x_495_; uint8_t v___x_496_; 
lean_dec(v___x_492_);
v___x_495_ = lean_nat_sub(v___x_493_, v___x_491_);
v___x_496_ = lean_nat_dec_lt(v___x_495_, v___x_493_);
if (v___x_496_ == 0)
{
lean_object* v___x_497_; 
lean_dec(v___x_495_);
v___x_497_ = lean_unsigned_to_nat(0u);
return v___x_497_;
}
else
{
lean_object* v___x_498_; 
v___x_498_ = lean_array_fget_borrowed(v_positions_490_, v___x_495_);
lean_dec(v___x_495_);
lean_inc(v___x_498_);
return v___x_498_;
}
}
else
{
lean_object* v___x_499_; 
v___x_499_ = lean_array_fget_borrowed(v_positions_490_, v___x_492_);
lean_dec(v___x_492_);
lean_inc(v___x_499_);
return v___x_499_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_FileMap_lineStart___boxed(lean_object* v_map_500_, lean_object* v_line_501_){
_start:
{
lean_object* v_res_502_; 
v_res_502_ = l_Lean_FileMap_lineStart(v_map_500_, v_line_501_);
lean_dec(v_line_501_);
lean_dec_ref(v_map_500_);
return v_res_502_;
}
}
LEAN_EXPORT lean_object* l_Lean_String_toFileMap(lean_object* v_s_503_){
_start:
{
lean_object* v___x_504_; 
v___x_504_ = l_Lean_FileMap_ofString(v_s_503_);
return v___x_504_;
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

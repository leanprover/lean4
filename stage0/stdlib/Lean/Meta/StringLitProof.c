// Lean compiler output
// Module: Lean.Meta.StringLitProof
// Imports: public import Lean.Meta.AppBuilder import Init.Data.String.Csimp
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
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* l_Lean_mkRawNatLit(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_String_toListImpl(lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_StringLitProof_0__Lean_Meta_mkStringLitNeProof_firstDiff(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_StringLitProof_0__Lean_Meta_mkStringLitNeProof_firstDiff___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Meta_mkStringLitNeProof_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Char"};
static const lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Meta_mkStringLitNeProof_spec__0___closed__0 = (const lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Meta_mkStringLitNeProof_spec__0___closed__0_value;
static const lean_string_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Meta_mkStringLitNeProof_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Meta_mkStringLitNeProof_spec__0___closed__1 = (const lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Meta_mkStringLitNeProof_spec__0___closed__1_value;
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Meta_mkStringLitNeProof_spec__0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Meta_mkStringLitNeProof_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Meta_mkStringLitNeProof_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Meta_mkStringLitNeProof_spec__0___closed__2_value_aux_0),((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Meta_mkStringLitNeProof_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(27, 51, 10, 169, 25, 67, 44, 251)}};
static const lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Meta_mkStringLitNeProof_spec__0___closed__2 = (const lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Meta_mkStringLitNeProof_spec__0___closed__2_value;
static lean_once_cell_t l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Meta_mkStringLitNeProof_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Meta_mkStringLitNeProof_spec__0___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Meta_mkStringLitNeProof_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Meta_mkStringLitNeProof_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_mkStringLitNeProof___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_Meta_mkStringLitNeProof___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_mkStringLitNeProof___redArg___closed__0_value;
static const lean_string_object l_Lean_Meta_mkStringLitNeProof___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "refl"};
static const lean_object* l_Lean_Meta_mkStringLitNeProof___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_mkStringLitNeProof___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Meta_mkStringLitNeProof___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkStringLitNeProof___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l_Lean_Meta_mkStringLitNeProof___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_mkStringLitNeProof___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_mkStringLitNeProof___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(72, 6, 107, 181, 0, 125, 21, 187)}};
static const lean_object* l_Lean_Meta_mkStringLitNeProof___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_mkStringLitNeProof___redArg___closed__2_value;
static lean_once_cell_t l_Lean_Meta_mkStringLitNeProof___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkStringLitNeProof___redArg___closed__3;
static lean_once_cell_t l_Lean_Meta_mkStringLitNeProof___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkStringLitNeProof___redArg___closed__4;
static lean_once_cell_t l_Lean_Meta_mkStringLitNeProof___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkStringLitNeProof___redArg___closed__5;
static const lean_string_object l_Lean_Meta_mkStringLitNeProof___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l_Lean_Meta_mkStringLitNeProof___redArg___closed__6 = (const lean_object*)&l_Lean_Meta_mkStringLitNeProof___redArg___closed__6_value;
static const lean_ctor_object l_Lean_Meta_mkStringLitNeProof___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkStringLitNeProof___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_object* l_Lean_Meta_mkStringLitNeProof___redArg___closed__7 = (const lean_object*)&l_Lean_Meta_mkStringLitNeProof___redArg___closed__7_value;
static lean_once_cell_t l_Lean_Meta_mkStringLitNeProof___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkStringLitNeProof___redArg___closed__8;
static const lean_string_object l_Lean_Meta_mkStringLitNeProof___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_Lean_Meta_mkStringLitNeProof___redArg___closed__9 = (const lean_object*)&l_Lean_Meta_mkStringLitNeProof___redArg___closed__9_value;
static const lean_ctor_object l_Lean_Meta_mkStringLitNeProof___redArg___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkStringLitNeProof___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_Meta_mkStringLitNeProof___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_mkStringLitNeProof___redArg___closed__10_value_aux_0),((lean_object*)&l_Lean_Meta_mkStringLitNeProof___redArg___closed__9_value),LEAN_SCALAR_PTR_LITERAL(117, 151, 161, 190, 111, 237, 188, 218)}};
static const lean_object* l_Lean_Meta_mkStringLitNeProof___redArg___closed__10 = (const lean_object*)&l_Lean_Meta_mkStringLitNeProof___redArg___closed__10_value;
static lean_once_cell_t l_Lean_Meta_mkStringLitNeProof___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkStringLitNeProof___redArg___closed__11;
static lean_once_cell_t l_Lean_Meta_mkStringLitNeProof___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkStringLitNeProof___redArg___closed__12;
static const lean_string_object l_Lean_Meta_mkStringLitNeProof___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "String"};
static const lean_object* l_Lean_Meta_mkStringLitNeProof___redArg___closed__13 = (const lean_object*)&l_Lean_Meta_mkStringLitNeProof___redArg___closed__13_value;
static const lean_string_object l_Lean_Meta_mkStringLitNeProof___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Internal"};
static const lean_object* l_Lean_Meta_mkStringLitNeProof___redArg___closed__14 = (const lean_object*)&l_Lean_Meta_mkStringLitNeProof___redArg___closed__14_value;
static const lean_string_object l_Lean_Meta_mkStringLitNeProof___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "ofList_ne_ofList"};
static const lean_object* l_Lean_Meta_mkStringLitNeProof___redArg___closed__15 = (const lean_object*)&l_Lean_Meta_mkStringLitNeProof___redArg___closed__15_value;
static const lean_ctor_object l_Lean_Meta_mkStringLitNeProof___redArg___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkStringLitNeProof___redArg___closed__13_value),LEAN_SCALAR_PTR_LITERAL(6, 130, 56, 8, 41, 104, 134, 43)}};
static const lean_ctor_object l_Lean_Meta_mkStringLitNeProof___redArg___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_mkStringLitNeProof___redArg___closed__16_value_aux_0),((lean_object*)&l_Lean_Meta_mkStringLitNeProof___redArg___closed__14_value),LEAN_SCALAR_PTR_LITERAL(7, 129, 74, 87, 236, 194, 167, 197)}};
static const lean_ctor_object l_Lean_Meta_mkStringLitNeProof___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_mkStringLitNeProof___redArg___closed__16_value_aux_1),((lean_object*)&l_Lean_Meta_mkStringLitNeProof___redArg___closed__15_value),LEAN_SCALAR_PTR_LITERAL(117, 155, 195, 132, 142, 127, 213, 252)}};
static const lean_object* l_Lean_Meta_mkStringLitNeProof___redArg___closed__16 = (const lean_object*)&l_Lean_Meta_mkStringLitNeProof___redArg___closed__16_value;
static lean_once_cell_t l_Lean_Meta_mkStringLitNeProof___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkStringLitNeProof___redArg___closed__17;
static const lean_ctor_object l_Lean_Meta_mkStringLitNeProof___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Meta_mkStringLitNeProof_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_object* l_Lean_Meta_mkStringLitNeProof___redArg___closed__18 = (const lean_object*)&l_Lean_Meta_mkStringLitNeProof___redArg___closed__18_value;
static lean_once_cell_t l_Lean_Meta_mkStringLitNeProof___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkStringLitNeProof___redArg___closed__19;
static const lean_string_object l_Lean_Meta_mkStringLitNeProof___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "List"};
static const lean_object* l_Lean_Meta_mkStringLitNeProof___redArg___closed__20 = (const lean_object*)&l_Lean_Meta_mkStringLitNeProof___redArg___closed__20_value;
static const lean_string_object l_Lean_Meta_mkStringLitNeProof___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "nil"};
static const lean_object* l_Lean_Meta_mkStringLitNeProof___redArg___closed__21 = (const lean_object*)&l_Lean_Meta_mkStringLitNeProof___redArg___closed__21_value;
static const lean_ctor_object l_Lean_Meta_mkStringLitNeProof___redArg___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkStringLitNeProof___redArg___closed__20_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l_Lean_Meta_mkStringLitNeProof___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_mkStringLitNeProof___redArg___closed__22_value_aux_0),((lean_object*)&l_Lean_Meta_mkStringLitNeProof___redArg___closed__21_value),LEAN_SCALAR_PTR_LITERAL(90, 150, 134, 113, 145, 38, 173, 251)}};
static const lean_object* l_Lean_Meta_mkStringLitNeProof___redArg___closed__22 = (const lean_object*)&l_Lean_Meta_mkStringLitNeProof___redArg___closed__22_value;
static const lean_ctor_object l_Lean_Meta_mkStringLitNeProof___redArg___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_mkStringLitNeProof___redArg___closed__23 = (const lean_object*)&l_Lean_Meta_mkStringLitNeProof___redArg___closed__23_value;
static lean_once_cell_t l_Lean_Meta_mkStringLitNeProof___redArg___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkStringLitNeProof___redArg___closed__24;
static lean_once_cell_t l_Lean_Meta_mkStringLitNeProof___redArg___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkStringLitNeProof___redArg___closed__25;
static const lean_string_object l_Lean_Meta_mkStringLitNeProof___redArg___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cons"};
static const lean_object* l_Lean_Meta_mkStringLitNeProof___redArg___closed__26 = (const lean_object*)&l_Lean_Meta_mkStringLitNeProof___redArg___closed__26_value;
static const lean_ctor_object l_Lean_Meta_mkStringLitNeProof___redArg___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkStringLitNeProof___redArg___closed__20_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l_Lean_Meta_mkStringLitNeProof___redArg___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_mkStringLitNeProof___redArg___closed__27_value_aux_0),((lean_object*)&l_Lean_Meta_mkStringLitNeProof___redArg___closed__26_value),LEAN_SCALAR_PTR_LITERAL(98, 170, 59, 223, 79, 132, 139, 119)}};
static const lean_object* l_Lean_Meta_mkStringLitNeProof___redArg___closed__27 = (const lean_object*)&l_Lean_Meta_mkStringLitNeProof___redArg___closed__27_value;
static lean_once_cell_t l_Lean_Meta_mkStringLitNeProof___redArg___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkStringLitNeProof___redArg___closed__28;
static lean_once_cell_t l_Lean_Meta_mkStringLitNeProof___redArg___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkStringLitNeProof___redArg___closed__29;
LEAN_EXPORT lean_object* l_Lean_Meta_mkStringLitNeProof___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkStringLitNeProof___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkStringLitNeProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkStringLitNeProof___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Meta_stringLitCode_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Meta_stringLitCode_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldrTR___at___00Lean_Meta_stringLitCode_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_stringLitCode(lean_object*);
static const lean_string_object l_Lean_Meta_mkStringLitCodeProof___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l_Lean_Meta_mkStringLitCodeProof___closed__0 = (const lean_object*)&l_Lean_Meta_mkStringLitCodeProof___closed__0_value;
static const lean_ctor_object l_Lean_Meta_mkStringLitCodeProof___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkStringLitCodeProof___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l_Lean_Meta_mkStringLitCodeProof___closed__1 = (const lean_object*)&l_Lean_Meta_mkStringLitCodeProof___closed__1_value;
static lean_once_cell_t l_Lean_Meta_mkStringLitCodeProof___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkStringLitCodeProof___closed__2;
static const lean_string_object l_Lean_Meta_mkStringLitCodeProof___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "code_ofList"};
static const lean_object* l_Lean_Meta_mkStringLitCodeProof___closed__3 = (const lean_object*)&l_Lean_Meta_mkStringLitCodeProof___closed__3_value;
static const lean_ctor_object l_Lean_Meta_mkStringLitCodeProof___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkStringLitNeProof___redArg___closed__13_value),LEAN_SCALAR_PTR_LITERAL(6, 130, 56, 8, 41, 104, 134, 43)}};
static const lean_ctor_object l_Lean_Meta_mkStringLitCodeProof___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_mkStringLitCodeProof___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_mkStringLitNeProof___redArg___closed__14_value),LEAN_SCALAR_PTR_LITERAL(7, 129, 74, 87, 236, 194, 167, 197)}};
static const lean_ctor_object l_Lean_Meta_mkStringLitCodeProof___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_mkStringLitCodeProof___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_mkStringLitCodeProof___closed__3_value),LEAN_SCALAR_PTR_LITERAL(82, 11, 134, 93, 134, 250, 205, 54)}};
static const lean_object* l_Lean_Meta_mkStringLitCodeProof___closed__4 = (const lean_object*)&l_Lean_Meta_mkStringLitCodeProof___closed__4_value;
static lean_once_cell_t l_Lean_Meta_mkStringLitCodeProof___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkStringLitCodeProof___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_mkStringLitCodeProof(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_StringLitProof_0__Lean_Meta_mkStringLitNeProof_firstDiff(lean_object* v_a_1_, lean_object* v_a_2_, lean_object* v_a_3_){
_start:
{
if (lean_obj_tag(v_a_1_) == 1)
{
if (lean_obj_tag(v_a_2_) == 1)
{
lean_object* v_head_4_; lean_object* v_tail_5_; lean_object* v_head_6_; lean_object* v_tail_7_; uint32_t v___x_8_; uint32_t v___x_9_; uint8_t v___x_10_; 
v_head_4_ = lean_ctor_get(v_a_1_, 0);
v_tail_5_ = lean_ctor_get(v_a_1_, 1);
v_head_6_ = lean_ctor_get(v_a_2_, 0);
v_tail_7_ = lean_ctor_get(v_a_2_, 1);
v___x_8_ = lean_unbox_uint32(v_head_4_);
v___x_9_ = lean_unbox_uint32(v_head_6_);
v___x_10_ = lean_uint32_dec_eq(v___x_8_, v___x_9_);
if (v___x_10_ == 0)
{
return v_a_3_;
}
else
{
lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_11_ = lean_unsigned_to_nat(1u);
v___x_12_ = lean_nat_add(v_a_3_, v___x_11_);
lean_dec(v_a_3_);
v_a_1_ = v_tail_5_;
v_a_2_ = v_tail_7_;
v_a_3_ = v___x_12_;
goto _start;
}
}
else
{
return v_a_3_;
}
}
else
{
return v_a_3_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_StringLitProof_0__Lean_Meta_mkStringLitNeProof_firstDiff___boxed(lean_object* v_a_14_, lean_object* v_a_15_, lean_object* v_a_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = l___private_Lean_Meta_StringLitProof_0__Lean_Meta_mkStringLitNeProof_firstDiff(v_a_14_, v_a_15_, v_a_16_);
lean_dec(v_a_15_);
lean_dec(v_a_14_);
return v_res_17_;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Meta_mkStringLitNeProof_spec__0___closed__3(void){
_start:
{
lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; 
v___x_23_ = lean_box(0);
v___x_24_ = ((lean_object*)(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Meta_mkStringLitNeProof_spec__0___closed__2));
v___x_25_ = l_Lean_mkConst(v___x_24_, v___x_23_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Meta_mkStringLitNeProof_spec__0(lean_object* v_nilFn_26_, lean_object* v_consFn_27_, lean_object* v_x_28_){
_start:
{
if (lean_obj_tag(v_x_28_) == 0)
{
lean_dec_ref(v_consFn_27_);
lean_inc_ref(v_nilFn_26_);
return v_nilFn_26_;
}
else
{
lean_object* v_head_29_; lean_object* v_tail_30_; lean_object* v___x_31_; uint32_t v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; 
v_head_29_ = lean_ctor_get(v_x_28_, 0);
v_tail_30_ = lean_ctor_get(v_x_28_, 1);
v___x_31_ = lean_obj_once(&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Meta_mkStringLitNeProof_spec__0___closed__3, &l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Meta_mkStringLitNeProof_spec__0___closed__3_once, _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Meta_mkStringLitNeProof_spec__0___closed__3);
v___x_32_ = lean_unbox_uint32(v_head_29_);
v___x_33_ = lean_uint32_to_nat(v___x_32_);
v___x_34_ = l_Lean_mkRawNatLit(v___x_33_);
v___x_35_ = l_Lean_Expr_app___override(v___x_31_, v___x_34_);
lean_inc_ref(v_consFn_27_);
v___x_36_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Meta_mkStringLitNeProof_spec__0(v_nilFn_26_, v_consFn_27_, v_tail_30_);
v___x_37_ = l_Lean_mkAppB(v_consFn_27_, v___x_35_, v___x_36_);
return v___x_37_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Meta_mkStringLitNeProof_spec__0___boxed(lean_object* v_nilFn_38_, lean_object* v_consFn_39_, lean_object* v_x_40_){
_start:
{
lean_object* v_res_41_; 
v_res_41_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Meta_mkStringLitNeProof_spec__0(v_nilFn_38_, v_consFn_39_, v_x_40_);
lean_dec(v_x_40_);
lean_dec_ref(v_nilFn_38_);
return v_res_41_;
}
}
static lean_object* _init_l_Lean_Meta_mkStringLitNeProof___redArg___closed__3(void){
_start:
{
lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_47_ = lean_unsigned_to_nat(1u);
v___x_48_ = l_Lean_Level_ofNat(v___x_47_);
return v___x_48_;
}
}
static lean_object* _init_l_Lean_Meta_mkStringLitNeProof___redArg___closed__4(void){
_start:
{
lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_49_ = lean_box(0);
v___x_50_ = lean_obj_once(&l_Lean_Meta_mkStringLitNeProof___redArg___closed__3, &l_Lean_Meta_mkStringLitNeProof___redArg___closed__3_once, _init_l_Lean_Meta_mkStringLitNeProof___redArg___closed__3);
v___x_51_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_51_, 0, v___x_50_);
lean_ctor_set(v___x_51_, 1, v___x_49_);
return v___x_51_;
}
}
static lean_object* _init_l_Lean_Meta_mkStringLitNeProof___redArg___closed__5(void){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_52_ = lean_obj_once(&l_Lean_Meta_mkStringLitNeProof___redArg___closed__4, &l_Lean_Meta_mkStringLitNeProof___redArg___closed__4_once, _init_l_Lean_Meta_mkStringLitNeProof___redArg___closed__4);
v___x_53_ = ((lean_object*)(l_Lean_Meta_mkStringLitNeProof___redArg___closed__2));
v___x_54_ = l_Lean_mkConst(v___x_53_, v___x_52_);
return v___x_54_;
}
}
static lean_object* _init_l_Lean_Meta_mkStringLitNeProof___redArg___closed__8(void){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_58_ = lean_box(0);
v___x_59_ = ((lean_object*)(l_Lean_Meta_mkStringLitNeProof___redArg___closed__7));
v___x_60_ = l_Lean_mkConst(v___x_59_, v___x_58_);
return v___x_60_;
}
}
static lean_object* _init_l_Lean_Meta_mkStringLitNeProof___redArg___closed__11(void){
_start:
{
lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_65_ = lean_box(0);
v___x_66_ = ((lean_object*)(l_Lean_Meta_mkStringLitNeProof___redArg___closed__10));
v___x_67_ = l_Lean_mkConst(v___x_66_, v___x_65_);
return v___x_67_;
}
}
static lean_object* _init_l_Lean_Meta_mkStringLitNeProof___redArg___closed__12(void){
_start:
{
lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v_h_71_; 
v___x_68_ = lean_obj_once(&l_Lean_Meta_mkStringLitNeProof___redArg___closed__11, &l_Lean_Meta_mkStringLitNeProof___redArg___closed__11_once, _init_l_Lean_Meta_mkStringLitNeProof___redArg___closed__11);
v___x_69_ = lean_obj_once(&l_Lean_Meta_mkStringLitNeProof___redArg___closed__8, &l_Lean_Meta_mkStringLitNeProof___redArg___closed__8_once, _init_l_Lean_Meta_mkStringLitNeProof___redArg___closed__8);
v___x_70_ = lean_obj_once(&l_Lean_Meta_mkStringLitNeProof___redArg___closed__5, &l_Lean_Meta_mkStringLitNeProof___redArg___closed__5_once, _init_l_Lean_Meta_mkStringLitNeProof___redArg___closed__5);
v_h_71_ = l_Lean_mkAppB(v___x_70_, v___x_69_, v___x_68_);
return v_h_71_;
}
}
static lean_object* _init_l_Lean_Meta_mkStringLitNeProof___redArg___closed__17(void){
_start:
{
lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_79_ = lean_box(0);
v___x_80_ = ((lean_object*)(l_Lean_Meta_mkStringLitNeProof___redArg___closed__16));
v___x_81_ = l_Lean_mkConst(v___x_80_, v___x_79_);
return v___x_81_;
}
}
static lean_object* _init_l_Lean_Meta_mkStringLitNeProof___redArg___closed__19(void){
_start:
{
lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v_type_86_; 
v___x_84_ = lean_box(0);
v___x_85_ = ((lean_object*)(l_Lean_Meta_mkStringLitNeProof___redArg___closed__18));
v_type_86_ = l_Lean_mkConst(v___x_85_, v___x_84_);
return v_type_86_;
}
}
static lean_object* _init_l_Lean_Meta_mkStringLitNeProof___redArg___closed__24(void){
_start:
{
lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_95_ = ((lean_object*)(l_Lean_Meta_mkStringLitNeProof___redArg___closed__23));
v___x_96_ = ((lean_object*)(l_Lean_Meta_mkStringLitNeProof___redArg___closed__22));
v___x_97_ = l_Lean_mkConst(v___x_96_, v___x_95_);
return v___x_97_;
}
}
static lean_object* _init_l_Lean_Meta_mkStringLitNeProof___redArg___closed__25(void){
_start:
{
lean_object* v_type_98_; lean_object* v___x_99_; lean_object* v_nil_100_; 
v_type_98_ = lean_obj_once(&l_Lean_Meta_mkStringLitNeProof___redArg___closed__19, &l_Lean_Meta_mkStringLitNeProof___redArg___closed__19_once, _init_l_Lean_Meta_mkStringLitNeProof___redArg___closed__19);
v___x_99_ = lean_obj_once(&l_Lean_Meta_mkStringLitNeProof___redArg___closed__24, &l_Lean_Meta_mkStringLitNeProof___redArg___closed__24_once, _init_l_Lean_Meta_mkStringLitNeProof___redArg___closed__24);
v_nil_100_ = l_Lean_Expr_app___override(v___x_99_, v_type_98_);
return v_nil_100_;
}
}
static lean_object* _init_l_Lean_Meta_mkStringLitNeProof___redArg___closed__28(void){
_start:
{
lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_105_ = ((lean_object*)(l_Lean_Meta_mkStringLitNeProof___redArg___closed__23));
v___x_106_ = ((lean_object*)(l_Lean_Meta_mkStringLitNeProof___redArg___closed__27));
v___x_107_ = l_Lean_mkConst(v___x_106_, v___x_105_);
return v___x_107_;
}
}
static lean_object* _init_l_Lean_Meta_mkStringLitNeProof___redArg___closed__29(void){
_start:
{
lean_object* v_type_108_; lean_object* v___x_109_; lean_object* v_cons_110_; 
v_type_108_ = lean_obj_once(&l_Lean_Meta_mkStringLitNeProof___redArg___closed__19, &l_Lean_Meta_mkStringLitNeProof___redArg___closed__19_once, _init_l_Lean_Meta_mkStringLitNeProof___redArg___closed__19);
v___x_109_ = lean_obj_once(&l_Lean_Meta_mkStringLitNeProof___redArg___closed__28, &l_Lean_Meta_mkStringLitNeProof___redArg___closed__28_once, _init_l_Lean_Meta_mkStringLitNeProof___redArg___closed__28);
v_cons_110_ = l_Lean_Expr_app___override(v___x_109_, v_type_108_);
return v_cons_110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkStringLitNeProof___redArg(lean_object* v_s_u2081_111_, lean_object* v_s_u2082_112_){
_start:
{
lean_object* v_l_u2081_114_; lean_object* v_l_u2082_115_; lean_object* v___x_116_; lean_object* v_i_117_; lean_object* v_h_118_; lean_object* v___x_119_; lean_object* v_nil_120_; lean_object* v_cons_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; 
v_l_u2081_114_ = l_String_toListImpl(v_s_u2081_111_);
v_l_u2082_115_ = l_String_toListImpl(v_s_u2082_112_);
v___x_116_ = lean_unsigned_to_nat(0u);
v_i_117_ = l___private_Lean_Meta_StringLitProof_0__Lean_Meta_mkStringLitNeProof_firstDiff(v_l_u2081_114_, v_l_u2082_115_, v___x_116_);
v_h_118_ = lean_obj_once(&l_Lean_Meta_mkStringLitNeProof___redArg___closed__12, &l_Lean_Meta_mkStringLitNeProof___redArg___closed__12_once, _init_l_Lean_Meta_mkStringLitNeProof___redArg___closed__12);
v___x_119_ = lean_obj_once(&l_Lean_Meta_mkStringLitNeProof___redArg___closed__17, &l_Lean_Meta_mkStringLitNeProof___redArg___closed__17_once, _init_l_Lean_Meta_mkStringLitNeProof___redArg___closed__17);
v_nil_120_ = lean_obj_once(&l_Lean_Meta_mkStringLitNeProof___redArg___closed__25, &l_Lean_Meta_mkStringLitNeProof___redArg___closed__25_once, _init_l_Lean_Meta_mkStringLitNeProof___redArg___closed__25);
v_cons_121_ = lean_obj_once(&l_Lean_Meta_mkStringLitNeProof___redArg___closed__29, &l_Lean_Meta_mkStringLitNeProof___redArg___closed__29_once, _init_l_Lean_Meta_mkStringLitNeProof___redArg___closed__29);
v___x_122_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Meta_mkStringLitNeProof_spec__0(v_nil_120_, v_cons_121_, v_l_u2081_114_);
lean_dec(v_l_u2081_114_);
v___x_123_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Meta_mkStringLitNeProof_spec__0(v_nil_120_, v_cons_121_, v_l_u2082_115_);
lean_dec(v_l_u2082_115_);
v___x_124_ = l_Lean_mkRawNatLit(v_i_117_);
v___x_125_ = l_Lean_mkApp4(v___x_119_, v___x_122_, v___x_123_, v___x_124_, v_h_118_);
v___x_126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_126_, 0, v___x_125_);
return v___x_126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkStringLitNeProof___redArg___boxed(lean_object* v_s_u2081_127_, lean_object* v_s_u2082_128_, lean_object* v_a_129_){
_start:
{
lean_object* v_res_130_; 
v_res_130_ = l_Lean_Meta_mkStringLitNeProof___redArg(v_s_u2081_127_, v_s_u2082_128_);
return v_res_130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkStringLitNeProof(lean_object* v_s_u2081_131_, lean_object* v_s_u2082_132_, lean_object* v_a_133_, lean_object* v_a_134_, lean_object* v_a_135_, lean_object* v_a_136_){
_start:
{
lean_object* v___x_138_; 
v___x_138_ = l_Lean_Meta_mkStringLitNeProof___redArg(v_s_u2081_131_, v_s_u2082_132_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkStringLitNeProof___boxed(lean_object* v_s_u2081_139_, lean_object* v_s_u2082_140_, lean_object* v_a_141_, lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l_Lean_Meta_mkStringLitNeProof(v_s_u2081_139_, v_s_u2082_140_, v_a_141_, v_a_142_, v_a_143_, v_a_144_);
lean_dec(v_a_144_);
lean_dec_ref(v_a_143_);
lean_dec(v_a_142_);
lean_dec_ref(v_a_141_);
return v_res_146_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Meta_stringLitCode_spec__0_spec__0(lean_object* v_as_147_, size_t v_i_148_, size_t v_stop_149_, lean_object* v_b_150_){
_start:
{
uint8_t v___x_151_; 
v___x_151_ = lean_usize_dec_eq(v_i_148_, v_stop_149_);
if (v___x_151_ == 0)
{
size_t v___x_152_; size_t v___x_153_; lean_object* v___x_154_; uint32_t v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_152_ = ((size_t)1ULL);
v___x_153_ = lean_usize_sub(v_i_148_, v___x_152_);
v___x_154_ = lean_array_uget_borrowed(v_as_147_, v___x_153_);
v___x_155_ = lean_unbox_uint32(v___x_154_);
v___x_156_ = lean_uint32_to_nat(v___x_155_);
v___x_157_ = lean_unsigned_to_nat(1u);
v___x_158_ = lean_nat_add(v___x_156_, v___x_157_);
lean_dec(v___x_156_);
v___x_159_ = lean_unsigned_to_nat(2097152u);
v___x_160_ = lean_nat_mul(v___x_159_, v_b_150_);
lean_dec(v_b_150_);
v___x_161_ = lean_nat_add(v___x_158_, v___x_160_);
lean_dec(v___x_160_);
lean_dec(v___x_158_);
v_i_148_ = v___x_153_;
v_b_150_ = v___x_161_;
goto _start;
}
else
{
return v_b_150_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Meta_stringLitCode_spec__0_spec__0___boxed(lean_object* v_as_163_, lean_object* v_i_164_, lean_object* v_stop_165_, lean_object* v_b_166_){
_start:
{
size_t v_i_boxed_167_; size_t v_stop_boxed_168_; lean_object* v_res_169_; 
v_i_boxed_167_ = lean_unbox_usize(v_i_164_);
lean_dec(v_i_164_);
v_stop_boxed_168_ = lean_unbox_usize(v_stop_165_);
lean_dec(v_stop_165_);
v_res_169_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Meta_stringLitCode_spec__0_spec__0(v_as_163_, v_i_boxed_167_, v_stop_boxed_168_, v_b_166_);
lean_dec_ref(v_as_163_);
return v_res_169_;
}
}
LEAN_EXPORT lean_object* l_List_foldrTR___at___00Lean_Meta_stringLitCode_spec__0(lean_object* v_init_170_, lean_object* v_l_171_){
_start:
{
lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; uint8_t v___x_175_; 
v___x_172_ = lean_array_mk(v_l_171_);
v___x_173_ = lean_array_get_size(v___x_172_);
v___x_174_ = lean_unsigned_to_nat(0u);
v___x_175_ = lean_nat_dec_lt(v___x_174_, v___x_173_);
if (v___x_175_ == 0)
{
lean_dec_ref(v___x_172_);
return v_init_170_;
}
else
{
size_t v___x_176_; size_t v___x_177_; lean_object* v___x_178_; 
v___x_176_ = lean_usize_of_nat(v___x_173_);
v___x_177_ = ((size_t)0ULL);
v___x_178_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Meta_stringLitCode_spec__0_spec__0(v___x_172_, v___x_176_, v___x_177_, v_init_170_);
lean_dec_ref(v___x_172_);
return v___x_178_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_stringLitCode(lean_object* v_s_179_){
_start:
{
lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_180_ = lean_unsigned_to_nat(0u);
v___x_181_ = l_String_toListImpl(v_s_179_);
v___x_182_ = l_List_foldrTR___at___00Lean_Meta_stringLitCode_spec__0(v___x_180_, v___x_181_);
return v___x_182_;
}
}
static lean_object* _init_l_Lean_Meta_mkStringLitCodeProof___closed__2(void){
_start:
{
lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_186_ = lean_box(0);
v___x_187_ = ((lean_object*)(l_Lean_Meta_mkStringLitCodeProof___closed__1));
v___x_188_ = l_Lean_mkConst(v___x_187_, v___x_186_);
return v___x_188_;
}
}
static lean_object* _init_l_Lean_Meta_mkStringLitCodeProof___closed__5(void){
_start:
{
lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_194_ = lean_box(0);
v___x_195_ = ((lean_object*)(l_Lean_Meta_mkStringLitCodeProof___closed__4));
v___x_196_ = l_Lean_mkConst(v___x_195_, v___x_194_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkStringLitCodeProof(lean_object* v_s_197_){
_start:
{
lean_object* v___x_198_; lean_object* v_n_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v_h_202_; lean_object* v___x_203_; lean_object* v_nil_204_; lean_object* v_cons_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; 
lean_inc_ref(v_s_197_);
v___x_198_ = l_Lean_Meta_stringLitCode(v_s_197_);
v_n_199_ = l_Lean_mkRawNatLit(v___x_198_);
v___x_200_ = lean_obj_once(&l_Lean_Meta_mkStringLitNeProof___redArg___closed__5, &l_Lean_Meta_mkStringLitNeProof___redArg___closed__5_once, _init_l_Lean_Meta_mkStringLitNeProof___redArg___closed__5);
v___x_201_ = lean_obj_once(&l_Lean_Meta_mkStringLitCodeProof___closed__2, &l_Lean_Meta_mkStringLitCodeProof___closed__2_once, _init_l_Lean_Meta_mkStringLitCodeProof___closed__2);
lean_inc_ref_n(v_n_199_, 2);
v_h_202_ = l_Lean_mkAppB(v___x_200_, v___x_201_, v_n_199_);
v___x_203_ = lean_obj_once(&l_Lean_Meta_mkStringLitCodeProof___closed__5, &l_Lean_Meta_mkStringLitCodeProof___closed__5_once, _init_l_Lean_Meta_mkStringLitCodeProof___closed__5);
v_nil_204_ = lean_obj_once(&l_Lean_Meta_mkStringLitNeProof___redArg___closed__25, &l_Lean_Meta_mkStringLitNeProof___redArg___closed__25_once, _init_l_Lean_Meta_mkStringLitNeProof___redArg___closed__25);
v_cons_205_ = lean_obj_once(&l_Lean_Meta_mkStringLitNeProof___redArg___closed__29, &l_Lean_Meta_mkStringLitNeProof___redArg___closed__29_once, _init_l_Lean_Meta_mkStringLitNeProof___redArg___closed__29);
v___x_206_ = l_String_toListImpl(v_s_197_);
v___x_207_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Meta_mkStringLitNeProof_spec__0(v_nil_204_, v_cons_205_, v___x_206_);
lean_dec(v___x_206_);
v___x_208_ = l_Lean_mkApp3(v___x_203_, v___x_207_, v_n_199_, v_h_202_);
v___x_209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_209_, 0, v_n_199_);
lean_ctor_set(v___x_209_, 1, v___x_208_);
return v___x_209_;
}
}
lean_object* runtime_initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Csimp(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_StringLitProof(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Csimp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_StringLitProof(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* initialize_Init_Data_String_Csimp(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_StringLitProof(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Csimp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_StringLitProof(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_StringLitProof(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_StringLitProof(builtin);
}
#ifdef __cplusplus
}
#endif

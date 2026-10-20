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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* l_Lean_mkRawNatLit(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_String_toListImpl(lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Level_succ___override(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_mkBVar(lean_object*);
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_drop___redArg(lean_object*, lean_object*);
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
lean_object* l_List_tail_x21___redArg(lean_object*);
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_get_x21Internal___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkStringLitNeProof___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkStringLitNeProof_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkStringLitNeProof_spec__1___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkStringLitNeProof_spec__1___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkStringLitNeProof_spec__1___redArg___boxed__const__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkStringLitNeProof_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkStringLitNeProof_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l_Lean_Meta_mkStringLitNeProof___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Meta_mkStringLitNeProof_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_object* l_Lean_Meta_mkStringLitNeProof___closed__0 = (const lean_object*)&l_Lean_Meta_mkStringLitNeProof___closed__0_value;
static lean_once_cell_t l_Lean_Meta_mkStringLitNeProof___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkStringLitNeProof___closed__1;
static const lean_string_object l_Lean_Meta_mkStringLitNeProof___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "List"};
static const lean_object* l_Lean_Meta_mkStringLitNeProof___closed__2 = (const lean_object*)&l_Lean_Meta_mkStringLitNeProof___closed__2_value;
static const lean_string_object l_Lean_Meta_mkStringLitNeProof___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "nil"};
static const lean_object* l_Lean_Meta_mkStringLitNeProof___closed__3 = (const lean_object*)&l_Lean_Meta_mkStringLitNeProof___closed__3_value;
static const lean_ctor_object l_Lean_Meta_mkStringLitNeProof___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkStringLitNeProof___closed__2_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l_Lean_Meta_mkStringLitNeProof___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_mkStringLitNeProof___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_mkStringLitNeProof___closed__3_value),LEAN_SCALAR_PTR_LITERAL(90, 150, 134, 113, 145, 38, 173, 251)}};
static const lean_object* l_Lean_Meta_mkStringLitNeProof___closed__4 = (const lean_object*)&l_Lean_Meta_mkStringLitNeProof___closed__4_value;
static const lean_ctor_object l_Lean_Meta_mkStringLitNeProof___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_mkStringLitNeProof___closed__5 = (const lean_object*)&l_Lean_Meta_mkStringLitNeProof___closed__5_value;
static lean_once_cell_t l_Lean_Meta_mkStringLitNeProof___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkStringLitNeProof___closed__6;
static lean_once_cell_t l_Lean_Meta_mkStringLitNeProof___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkStringLitNeProof___closed__7;
static const lean_string_object l_Lean_Meta_mkStringLitNeProof___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cons"};
static const lean_object* l_Lean_Meta_mkStringLitNeProof___closed__8 = (const lean_object*)&l_Lean_Meta_mkStringLitNeProof___closed__8_value;
static const lean_ctor_object l_Lean_Meta_mkStringLitNeProof___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkStringLitNeProof___closed__2_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l_Lean_Meta_mkStringLitNeProof___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_mkStringLitNeProof___closed__9_value_aux_0),((lean_object*)&l_Lean_Meta_mkStringLitNeProof___closed__8_value),LEAN_SCALAR_PTR_LITERAL(98, 170, 59, 223, 79, 132, 139, 119)}};
static const lean_object* l_Lean_Meta_mkStringLitNeProof___closed__9 = (const lean_object*)&l_Lean_Meta_mkStringLitNeProof___closed__9_value;
static lean_once_cell_t l_Lean_Meta_mkStringLitNeProof___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkStringLitNeProof___closed__10;
static lean_once_cell_t l_Lean_Meta_mkStringLitNeProof___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkStringLitNeProof___closed__11;
static const lean_string_object l_Lean_Meta_mkStringLitNeProof___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "String"};
static const lean_object* l_Lean_Meta_mkStringLitNeProof___closed__12 = (const lean_object*)&l_Lean_Meta_mkStringLitNeProof___closed__12_value;
static const lean_ctor_object l_Lean_Meta_mkStringLitNeProof___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkStringLitNeProof___closed__12_value),LEAN_SCALAR_PTR_LITERAL(6, 130, 56, 8, 41, 104, 134, 43)}};
static const lean_object* l_Lean_Meta_mkStringLitNeProof___closed__13 = (const lean_object*)&l_Lean_Meta_mkStringLitNeProof___closed__13_value;
static lean_once_cell_t l_Lean_Meta_mkStringLitNeProof___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkStringLitNeProof___closed__14;
static const lean_string_object l_Lean_Meta_mkStringLitNeProof___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "ofList"};
static const lean_object* l_Lean_Meta_mkStringLitNeProof___closed__15 = (const lean_object*)&l_Lean_Meta_mkStringLitNeProof___closed__15_value;
static const lean_ctor_object l_Lean_Meta_mkStringLitNeProof___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkStringLitNeProof___closed__12_value),LEAN_SCALAR_PTR_LITERAL(6, 130, 56, 8, 41, 104, 134, 43)}};
static const lean_ctor_object l_Lean_Meta_mkStringLitNeProof___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_mkStringLitNeProof___closed__16_value_aux_0),((lean_object*)&l_Lean_Meta_mkStringLitNeProof___closed__15_value),LEAN_SCALAR_PTR_LITERAL(118, 246, 177, 142, 179, 9, 199, 233)}};
static const lean_object* l_Lean_Meta_mkStringLitNeProof___closed__16 = (const lean_object*)&l_Lean_Meta_mkStringLitNeProof___closed__16_value;
static lean_once_cell_t l_Lean_Meta_mkStringLitNeProof___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkStringLitNeProof___closed__17;
static const lean_string_object l_Lean_Meta_mkStringLitNeProof___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mt"};
static const lean_object* l_Lean_Meta_mkStringLitNeProof___closed__18 = (const lean_object*)&l_Lean_Meta_mkStringLitNeProof___closed__18_value;
static const lean_ctor_object l_Lean_Meta_mkStringLitNeProof___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkStringLitNeProof___closed__18_value),LEAN_SCALAR_PTR_LITERAL(236, 40, 53, 218, 205, 101, 166, 74)}};
static const lean_object* l_Lean_Meta_mkStringLitNeProof___closed__19 = (const lean_object*)&l_Lean_Meta_mkStringLitNeProof___closed__19_value;
static lean_once_cell_t l_Lean_Meta_mkStringLitNeProof___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkStringLitNeProof___closed__20;
static const lean_string_object l_Lean_Meta_mkStringLitNeProof___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "ofList_injective"};
static const lean_object* l_Lean_Meta_mkStringLitNeProof___closed__21 = (const lean_object*)&l_Lean_Meta_mkStringLitNeProof___closed__21_value;
static const lean_ctor_object l_Lean_Meta_mkStringLitNeProof___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkStringLitNeProof___closed__12_value),LEAN_SCALAR_PTR_LITERAL(6, 130, 56, 8, 41, 104, 134, 43)}};
static const lean_ctor_object l_Lean_Meta_mkStringLitNeProof___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_mkStringLitNeProof___closed__22_value_aux_0),((lean_object*)&l_Lean_Meta_mkStringLitNeProof___closed__21_value),LEAN_SCALAR_PTR_LITERAL(85, 99, 204, 155, 80, 133, 77, 68)}};
static const lean_object* l_Lean_Meta_mkStringLitNeProof___closed__22 = (const lean_object*)&l_Lean_Meta_mkStringLitNeProof___closed__22_value;
static lean_once_cell_t l_Lean_Meta_mkStringLitNeProof___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkStringLitNeProof___closed__23;
static const lean_ctor_object l_Lean_Meta_mkStringLitNeProof___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkStringLitNeProof___closed__2_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_object* l_Lean_Meta_mkStringLitNeProof___closed__24 = (const lean_object*)&l_Lean_Meta_mkStringLitNeProof___closed__24_value;
static lean_once_cell_t l_Lean_Meta_mkStringLitNeProof___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkStringLitNeProof___closed__25;
static lean_once_cell_t l_Lean_Meta_mkStringLitNeProof___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkStringLitNeProof___closed__26;
static const lean_string_object l_Lean_Meta_mkStringLitNeProof___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "cons_ne_nil"};
static const lean_object* l_Lean_Meta_mkStringLitNeProof___closed__27 = (const lean_object*)&l_Lean_Meta_mkStringLitNeProof___closed__27_value;
static const lean_ctor_object l_Lean_Meta_mkStringLitNeProof___closed__28_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkStringLitNeProof___closed__2_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l_Lean_Meta_mkStringLitNeProof___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_mkStringLitNeProof___closed__28_value_aux_0),((lean_object*)&l_Lean_Meta_mkStringLitNeProof___closed__27_value),LEAN_SCALAR_PTR_LITERAL(60, 170, 34, 7, 73, 41, 87, 161)}};
static const lean_object* l_Lean_Meta_mkStringLitNeProof___closed__28 = (const lean_object*)&l_Lean_Meta_mkStringLitNeProof___closed__28_value;
static lean_once_cell_t l_Lean_Meta_mkStringLitNeProof___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkStringLitNeProof___closed__29;
static const lean_string_object l_Lean_Meta_mkStringLitNeProof___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Ne"};
static const lean_object* l_Lean_Meta_mkStringLitNeProof___closed__30 = (const lean_object*)&l_Lean_Meta_mkStringLitNeProof___closed__30_value;
static const lean_string_object l_Lean_Meta_mkStringLitNeProof___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "symm"};
static const lean_object* l_Lean_Meta_mkStringLitNeProof___closed__31 = (const lean_object*)&l_Lean_Meta_mkStringLitNeProof___closed__31_value;
static const lean_ctor_object l_Lean_Meta_mkStringLitNeProof___closed__32_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkStringLitNeProof___closed__30_value),LEAN_SCALAR_PTR_LITERAL(161, 247, 70, 70, 118, 145, 235, 92)}};
static const lean_ctor_object l_Lean_Meta_mkStringLitNeProof___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_mkStringLitNeProof___closed__32_value_aux_0),((lean_object*)&l_Lean_Meta_mkStringLitNeProof___closed__31_value),LEAN_SCALAR_PTR_LITERAL(106, 137, 24, 74, 49, 62, 0, 94)}};
static const lean_object* l_Lean_Meta_mkStringLitNeProof___closed__32 = (const lean_object*)&l_Lean_Meta_mkStringLitNeProof___closed__32_value;
static const lean_string_object l_Lean_Meta_mkStringLitNeProof___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_Meta_mkStringLitNeProof___closed__33 = (const lean_object*)&l_Lean_Meta_mkStringLitNeProof___closed__33_value;
static const lean_ctor_object l_Lean_Meta_mkStringLitNeProof___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkStringLitNeProof___closed__33_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_Lean_Meta_mkStringLitNeProof___closed__34 = (const lean_object*)&l_Lean_Meta_mkStringLitNeProof___closed__34_value;
static lean_once_cell_t l_Lean_Meta_mkStringLitNeProof___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkStringLitNeProof___closed__35;
static lean_once_cell_t l_Lean_Meta_mkStringLitNeProof___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkStringLitNeProof___closed__36;
static lean_once_cell_t l_Lean_Meta_mkStringLitNeProof___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkStringLitNeProof___closed__37;
static const lean_string_object l_Lean_Meta_mkStringLitNeProof___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "l"};
static const lean_object* l_Lean_Meta_mkStringLitNeProof___closed__38 = (const lean_object*)&l_Lean_Meta_mkStringLitNeProof___closed__38_value;
static const lean_ctor_object l_Lean_Meta_mkStringLitNeProof___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkStringLitNeProof___closed__38_value),LEAN_SCALAR_PTR_LITERAL(140, 76, 64, 139, 36, 56, 191, 236)}};
static const lean_object* l_Lean_Meta_mkStringLitNeProof___closed__39 = (const lean_object*)&l_Lean_Meta_mkStringLitNeProof___closed__39_value;
static const lean_string_object l_Lean_Meta_mkStringLitNeProof___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "drop"};
static const lean_object* l_Lean_Meta_mkStringLitNeProof___closed__40 = (const lean_object*)&l_Lean_Meta_mkStringLitNeProof___closed__40_value;
static const lean_ctor_object l_Lean_Meta_mkStringLitNeProof___closed__41_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkStringLitNeProof___closed__2_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l_Lean_Meta_mkStringLitNeProof___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_mkStringLitNeProof___closed__41_value_aux_0),((lean_object*)&l_Lean_Meta_mkStringLitNeProof___closed__40_value),LEAN_SCALAR_PTR_LITERAL(106, 246, 106, 249, 224, 85, 68, 146)}};
static const lean_object* l_Lean_Meta_mkStringLitNeProof___closed__41 = (const lean_object*)&l_Lean_Meta_mkStringLitNeProof___closed__41_value;
static lean_once_cell_t l_Lean_Meta_mkStringLitNeProof___closed__42_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkStringLitNeProof___closed__42;
static const lean_string_object l_Lean_Meta_mkStringLitNeProof___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "congrArg"};
static const lean_object* l_Lean_Meta_mkStringLitNeProof___closed__43 = (const lean_object*)&l_Lean_Meta_mkStringLitNeProof___closed__43_value;
static const lean_ctor_object l_Lean_Meta_mkStringLitNeProof___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkStringLitNeProof___closed__43_value),LEAN_SCALAR_PTR_LITERAL(188, 17, 22, 243, 206, 91, 171, 36)}};
static const lean_object* l_Lean_Meta_mkStringLitNeProof___closed__44 = (const lean_object*)&l_Lean_Meta_mkStringLitNeProof___closed__44_value;
static lean_once_cell_t l_Lean_Meta_mkStringLitNeProof___closed__45_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkStringLitNeProof___closed__45;
static lean_once_cell_t l_Lean_Meta_mkStringLitNeProof___closed__46_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkStringLitNeProof___closed__46;
static const lean_string_object l_Lean_Meta_mkStringLitNeProof___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "instInhabited"};
static const lean_object* l_Lean_Meta_mkStringLitNeProof___closed__47 = (const lean_object*)&l_Lean_Meta_mkStringLitNeProof___closed__47_value;
static const lean_ctor_object l_Lean_Meta_mkStringLitNeProof___closed__48_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Meta_mkStringLitNeProof_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_ctor_object l_Lean_Meta_mkStringLitNeProof___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_mkStringLitNeProof___closed__48_value_aux_0),((lean_object*)&l_Lean_Meta_mkStringLitNeProof___closed__47_value),LEAN_SCALAR_PTR_LITERAL(235, 71, 242, 59, 163, 162, 132, 113)}};
static const lean_object* l_Lean_Meta_mkStringLitNeProof___closed__48 = (const lean_object*)&l_Lean_Meta_mkStringLitNeProof___closed__48_value;
static lean_once_cell_t l_Lean_Meta_mkStringLitNeProof___closed__49_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkStringLitNeProof___closed__49;
static const lean_string_object l_Lean_Meta_mkStringLitNeProof___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l_Lean_Meta_mkStringLitNeProof___closed__50 = (const lean_object*)&l_Lean_Meta_mkStringLitNeProof___closed__50_value;
static const lean_ctor_object l_Lean_Meta_mkStringLitNeProof___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkStringLitNeProof___closed__50_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l_Lean_Meta_mkStringLitNeProof___closed__51 = (const lean_object*)&l_Lean_Meta_mkStringLitNeProof___closed__51_value;
static lean_once_cell_t l_Lean_Meta_mkStringLitNeProof___closed__52_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkStringLitNeProof___closed__52;
static const lean_string_object l_Lean_Meta_mkStringLitNeProof___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toNat"};
static const lean_object* l_Lean_Meta_mkStringLitNeProof___closed__53 = (const lean_object*)&l_Lean_Meta_mkStringLitNeProof___closed__53_value;
static const lean_ctor_object l_Lean_Meta_mkStringLitNeProof___closed__54_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Meta_mkStringLitNeProof_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_ctor_object l_Lean_Meta_mkStringLitNeProof___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_mkStringLitNeProof___closed__54_value_aux_0),((lean_object*)&l_Lean_Meta_mkStringLitNeProof___closed__53_value),LEAN_SCALAR_PTR_LITERAL(200, 248, 141, 246, 182, 101, 131, 69)}};
static const lean_object* l_Lean_Meta_mkStringLitNeProof___closed__54 = (const lean_object*)&l_Lean_Meta_mkStringLitNeProof___closed__54_value;
static lean_once_cell_t l_Lean_Meta_mkStringLitNeProof___closed__55_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkStringLitNeProof___closed__55;
static const lean_string_object l_Lean_Meta_mkStringLitNeProof___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "get!Internal"};
static const lean_object* l_Lean_Meta_mkStringLitNeProof___closed__56 = (const lean_object*)&l_Lean_Meta_mkStringLitNeProof___closed__56_value;
static const lean_ctor_object l_Lean_Meta_mkStringLitNeProof___closed__57_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkStringLitNeProof___closed__2_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l_Lean_Meta_mkStringLitNeProof___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_mkStringLitNeProof___closed__57_value_aux_0),((lean_object*)&l_Lean_Meta_mkStringLitNeProof___closed__56_value),LEAN_SCALAR_PTR_LITERAL(70, 67, 44, 187, 22, 159, 103, 20)}};
static const lean_object* l_Lean_Meta_mkStringLitNeProof___closed__57 = (const lean_object*)&l_Lean_Meta_mkStringLitNeProof___closed__57_value;
static lean_once_cell_t l_Lean_Meta_mkStringLitNeProof___closed__58_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkStringLitNeProof___closed__58;
static const lean_string_object l_Lean_Meta_mkStringLitNeProof___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l_Lean_Meta_mkStringLitNeProof___closed__59 = (const lean_object*)&l_Lean_Meta_mkStringLitNeProof___closed__59_value;
static const lean_string_object l_Lean_Meta_mkStringLitNeProof___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_Lean_Meta_mkStringLitNeProof___closed__60 = (const lean_object*)&l_Lean_Meta_mkStringLitNeProof___closed__60_value;
static const lean_ctor_object l_Lean_Meta_mkStringLitNeProof___closed__61_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkStringLitNeProof___closed__59_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_Meta_mkStringLitNeProof___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_mkStringLitNeProof___closed__61_value_aux_0),((lean_object*)&l_Lean_Meta_mkStringLitNeProof___closed__60_value),LEAN_SCALAR_PTR_LITERAL(117, 151, 161, 190, 111, 237, 188, 218)}};
static const lean_object* l_Lean_Meta_mkStringLitNeProof___closed__61 = (const lean_object*)&l_Lean_Meta_mkStringLitNeProof___closed__61_value;
static lean_once_cell_t l_Lean_Meta_mkStringLitNeProof___closed__62_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkStringLitNeProof___closed__62;
static const lean_string_object l_Lean_Meta_mkStringLitNeProof___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "ne_of_beq_eq_false"};
static const lean_object* l_Lean_Meta_mkStringLitNeProof___closed__63 = (const lean_object*)&l_Lean_Meta_mkStringLitNeProof___closed__63_value;
static const lean_ctor_object l_Lean_Meta_mkStringLitNeProof___closed__64_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkStringLitNeProof___closed__50_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Lean_Meta_mkStringLitNeProof___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_mkStringLitNeProof___closed__64_value_aux_0),((lean_object*)&l_Lean_Meta_mkStringLitNeProof___closed__63_value),LEAN_SCALAR_PTR_LITERAL(152, 213, 144, 137, 140, 238, 73, 24)}};
static const lean_object* l_Lean_Meta_mkStringLitNeProof___closed__64 = (const lean_object*)&l_Lean_Meta_mkStringLitNeProof___closed__64_value;
static lean_once_cell_t l_Lean_Meta_mkStringLitNeProof___closed__65_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkStringLitNeProof___closed__65;
LEAN_EXPORT lean_object* l_Lean_Meta_mkStringLitNeProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkStringLitNeProof___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkStringLitNeProof_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkStringLitNeProof_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkStringLitNeProof___lam__0(lean_object* v___x_1_, lean_object* v_type_2_, lean_object* v_inhabCharExpr_3_, lean_object* v_iExpr_4_, lean_object* v___x_5_, lean_object* v_lExpr_6_){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_7_ = l_Lean_mkApp4(v___x_1_, v_type_2_, v_inhabCharExpr_3_, v_lExpr_6_, v_iExpr_4_);
v___x_8_ = l_Lean_Expr_app___override(v___x_5_, v___x_7_);
return v___x_8_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkStringLitNeProof_spec__1___redArg___boxed__const__1(void){
_start:
{
uint32_t v___x_12_; lean_object* v___x_13_; 
v___x_12_ = 65;
v___x_13_ = lean_box_uint32(v___x_12_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkStringLitNeProof_spec__1___redArg(lean_object* v_l_u2081_14_, lean_object* v_l_u2082_15_, lean_object* v_range_16_, lean_object* v_b_17_, lean_object* v_i_18_){
_start:
{
lean_object* v_stop_19_; lean_object* v_step_20_; uint8_t v___x_21_; 
v_stop_19_ = lean_ctor_get(v_range_16_, 1);
v_step_20_ = lean_ctor_get(v_range_16_, 2);
v___x_21_ = lean_nat_dec_lt(v_i_18_, v_stop_19_);
if (v___x_21_ == 0)
{
lean_dec(v_i_18_);
lean_inc_ref(v_b_17_);
return v_b_17_;
}
else
{
lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; uint32_t v___x_27_; uint32_t v___x_28_; uint8_t v___x_29_; 
v___x_22_ = lean_box(0);
v___x_23_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkStringLitNeProof_spec__1___redArg___boxed__const__1;
lean_inc_n(v_i_18_, 2);
v___x_24_ = l_List_get_x21Internal___redArg(v___x_23_, v_l_u2081_14_, v_i_18_);
v___x_25_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkStringLitNeProof_spec__1___redArg___boxed__const__1;
v___x_26_ = l_List_get_x21Internal___redArg(v___x_25_, v_l_u2082_15_, v_i_18_);
v___x_27_ = lean_unbox_uint32(v___x_24_);
lean_dec(v___x_24_);
v___x_28_ = lean_unbox_uint32(v___x_26_);
lean_dec(v___x_26_);
v___x_29_ = lean_uint32_dec_eq(v___x_27_, v___x_28_);
if (v___x_29_ == 0)
{
lean_object* v___x_30_; lean_object* v___x_31_; 
v___x_30_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_30_, 0, v_i_18_);
v___x_31_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_31_, 0, v___x_30_);
lean_ctor_set(v___x_31_, 1, v___x_22_);
return v___x_31_;
}
else
{
lean_object* v___x_32_; lean_object* v___x_33_; 
v___x_32_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkStringLitNeProof_spec__1___redArg___closed__0));
v___x_33_ = lean_nat_add(v_i_18_, v_step_20_);
lean_dec(v_i_18_);
v_b_17_ = v___x_32_;
v_i_18_ = v___x_33_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkStringLitNeProof_spec__1___redArg___boxed(lean_object* v_l_u2081_35_, lean_object* v_l_u2082_36_, lean_object* v_range_37_, lean_object* v_b_38_, lean_object* v_i_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkStringLitNeProof_spec__1___redArg(v_l_u2081_35_, v_l_u2082_36_, v_range_37_, v_b_38_, v_i_39_);
lean_dec_ref(v_b_38_);
lean_dec_ref(v_range_37_);
lean_dec(v_l_u2082_36_);
lean_dec(v_l_u2081_35_);
return v_res_40_;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Meta_mkStringLitNeProof_spec__0___closed__3(void){
_start:
{
lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_46_ = lean_box(0);
v___x_47_ = ((lean_object*)(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Meta_mkStringLitNeProof_spec__0___closed__2));
v___x_48_ = l_Lean_mkConst(v___x_47_, v___x_46_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Meta_mkStringLitNeProof_spec__0(lean_object* v_nilFn_49_, lean_object* v_consFn_50_, lean_object* v_x_51_){
_start:
{
if (lean_obj_tag(v_x_51_) == 0)
{
lean_dec_ref(v_consFn_50_);
lean_inc_ref(v_nilFn_49_);
return v_nilFn_49_;
}
else
{
lean_object* v_head_52_; lean_object* v_tail_53_; lean_object* v___x_54_; uint32_t v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
v_head_52_ = lean_ctor_get(v_x_51_, 0);
v_tail_53_ = lean_ctor_get(v_x_51_, 1);
v___x_54_ = lean_obj_once(&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Meta_mkStringLitNeProof_spec__0___closed__3, &l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Meta_mkStringLitNeProof_spec__0___closed__3_once, _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Meta_mkStringLitNeProof_spec__0___closed__3);
v___x_55_ = lean_unbox_uint32(v_head_52_);
v___x_56_ = lean_uint32_to_nat(v___x_55_);
v___x_57_ = l_Lean_mkRawNatLit(v___x_56_);
v___x_58_ = l_Lean_Expr_app___override(v___x_54_, v___x_57_);
lean_inc_ref(v_consFn_50_);
v___x_59_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Meta_mkStringLitNeProof_spec__0(v_nilFn_49_, v_consFn_50_, v_tail_53_);
v___x_60_ = l_Lean_mkAppB(v_consFn_50_, v___x_58_, v___x_59_);
return v___x_60_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Meta_mkStringLitNeProof_spec__0___boxed(lean_object* v_nilFn_61_, lean_object* v_consFn_62_, lean_object* v_x_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Meta_mkStringLitNeProof_spec__0(v_nilFn_61_, v_consFn_62_, v_x_63_);
lean_dec(v_x_63_);
lean_dec_ref(v_nilFn_61_);
return v_res_64_;
}
}
static lean_object* _init_l_Lean_Meta_mkStringLitNeProof___closed__1(void){
_start:
{
lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v_type_69_; 
v___x_67_ = lean_box(0);
v___x_68_ = ((lean_object*)(l_Lean_Meta_mkStringLitNeProof___closed__0));
v_type_69_ = l_Lean_mkConst(v___x_68_, v___x_67_);
return v_type_69_;
}
}
static lean_object* _init_l_Lean_Meta_mkStringLitNeProof___closed__6(void){
_start:
{
lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; 
v___x_78_ = ((lean_object*)(l_Lean_Meta_mkStringLitNeProof___closed__5));
v___x_79_ = ((lean_object*)(l_Lean_Meta_mkStringLitNeProof___closed__4));
v___x_80_ = l_Lean_mkConst(v___x_79_, v___x_78_);
return v___x_80_;
}
}
static lean_object* _init_l_Lean_Meta_mkStringLitNeProof___closed__7(void){
_start:
{
lean_object* v_type_81_; lean_object* v___x_82_; lean_object* v_nil_83_; 
v_type_81_ = lean_obj_once(&l_Lean_Meta_mkStringLitNeProof___closed__1, &l_Lean_Meta_mkStringLitNeProof___closed__1_once, _init_l_Lean_Meta_mkStringLitNeProof___closed__1);
v___x_82_ = lean_obj_once(&l_Lean_Meta_mkStringLitNeProof___closed__6, &l_Lean_Meta_mkStringLitNeProof___closed__6_once, _init_l_Lean_Meta_mkStringLitNeProof___closed__6);
v_nil_83_ = l_Lean_Expr_app___override(v___x_82_, v_type_81_);
return v_nil_83_;
}
}
static lean_object* _init_l_Lean_Meta_mkStringLitNeProof___closed__10(void){
_start:
{
lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_88_ = ((lean_object*)(l_Lean_Meta_mkStringLitNeProof___closed__5));
v___x_89_ = ((lean_object*)(l_Lean_Meta_mkStringLitNeProof___closed__9));
v___x_90_ = l_Lean_mkConst(v___x_89_, v___x_88_);
return v___x_90_;
}
}
static lean_object* _init_l_Lean_Meta_mkStringLitNeProof___closed__11(void){
_start:
{
lean_object* v_type_91_; lean_object* v___x_92_; lean_object* v_cons_93_; 
v_type_91_ = lean_obj_once(&l_Lean_Meta_mkStringLitNeProof___closed__1, &l_Lean_Meta_mkStringLitNeProof___closed__1_once, _init_l_Lean_Meta_mkStringLitNeProof___closed__1);
v___x_92_ = lean_obj_once(&l_Lean_Meta_mkStringLitNeProof___closed__10, &l_Lean_Meta_mkStringLitNeProof___closed__10_once, _init_l_Lean_Meta_mkStringLitNeProof___closed__10);
v_cons_93_ = l_Lean_Expr_app___override(v___x_92_, v_type_91_);
return v_cons_93_;
}
}
static lean_object* _init_l_Lean_Meta_mkStringLitNeProof___closed__14(void){
_start:
{
lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v_strType_99_; 
v___x_97_ = lean_box(0);
v___x_98_ = ((lean_object*)(l_Lean_Meta_mkStringLitNeProof___closed__13));
v_strType_99_ = l_Lean_mkConst(v___x_98_, v___x_97_);
return v_strType_99_;
}
}
static lean_object* _init_l_Lean_Meta_mkStringLitNeProof___closed__17(void){
_start:
{
lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_104_ = lean_box(0);
v___x_105_ = ((lean_object*)(l_Lean_Meta_mkStringLitNeProof___closed__16));
v___x_106_ = l_Lean_mkConst(v___x_105_, v___x_104_);
return v___x_106_;
}
}
static lean_object* _init_l_Lean_Meta_mkStringLitNeProof___closed__20(void){
_start:
{
lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_110_ = lean_box(0);
v___x_111_ = ((lean_object*)(l_Lean_Meta_mkStringLitNeProof___closed__19));
v___x_112_ = l_Lean_mkConst(v___x_111_, v___x_110_);
return v___x_112_;
}
}
static lean_object* _init_l_Lean_Meta_mkStringLitNeProof___closed__23(void){
_start:
{
lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_117_ = lean_box(0);
v___x_118_ = ((lean_object*)(l_Lean_Meta_mkStringLitNeProof___closed__22));
v___x_119_ = l_Lean_mkConst(v___x_118_, v___x_117_);
return v___x_119_;
}
}
static lean_object* _init_l_Lean_Meta_mkStringLitNeProof___closed__25(void){
_start:
{
lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_122_ = ((lean_object*)(l_Lean_Meta_mkStringLitNeProof___closed__5));
v___x_123_ = ((lean_object*)(l_Lean_Meta_mkStringLitNeProof___closed__24));
v___x_124_ = l_Lean_mkConst(v___x_123_, v___x_122_);
return v___x_124_;
}
}
static lean_object* _init_l_Lean_Meta_mkStringLitNeProof___closed__26(void){
_start:
{
lean_object* v_type_125_; lean_object* v___x_126_; lean_object* v_listCharTy_127_; 
v_type_125_ = lean_obj_once(&l_Lean_Meta_mkStringLitNeProof___closed__1, &l_Lean_Meta_mkStringLitNeProof___closed__1_once, _init_l_Lean_Meta_mkStringLitNeProof___closed__1);
v___x_126_ = lean_obj_once(&l_Lean_Meta_mkStringLitNeProof___closed__25, &l_Lean_Meta_mkStringLitNeProof___closed__25_once, _init_l_Lean_Meta_mkStringLitNeProof___closed__25);
v_listCharTy_127_ = l_Lean_Expr_app___override(v___x_126_, v_type_125_);
return v_listCharTy_127_;
}
}
static lean_object* _init_l_Lean_Meta_mkStringLitNeProof___closed__29(void){
_start:
{
lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; 
v___x_132_ = ((lean_object*)(l_Lean_Meta_mkStringLitNeProof___closed__5));
v___x_133_ = ((lean_object*)(l_Lean_Meta_mkStringLitNeProof___closed__28));
v___x_134_ = l_Lean_mkConst(v___x_133_, v___x_132_);
return v___x_134_;
}
}
static lean_object* _init_l_Lean_Meta_mkStringLitNeProof___closed__35(void){
_start:
{
lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_143_ = lean_box(0);
v___x_144_ = l_Lean_Level_succ___override(v___x_143_);
return v___x_144_;
}
}
static lean_object* _init_l_Lean_Meta_mkStringLitNeProof___closed__36(void){
_start:
{
lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_145_ = lean_box(0);
v___x_146_ = lean_obj_once(&l_Lean_Meta_mkStringLitNeProof___closed__35, &l_Lean_Meta_mkStringLitNeProof___closed__35_once, _init_l_Lean_Meta_mkStringLitNeProof___closed__35);
v___x_147_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_147_, 0, v___x_146_);
lean_ctor_set(v___x_147_, 1, v___x_145_);
return v___x_147_;
}
}
static lean_object* _init_l_Lean_Meta_mkStringLitNeProof___closed__37(void){
_start:
{
lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_148_ = lean_obj_once(&l_Lean_Meta_mkStringLitNeProof___closed__36, &l_Lean_Meta_mkStringLitNeProof___closed__36_once, _init_l_Lean_Meta_mkStringLitNeProof___closed__36);
v___x_149_ = ((lean_object*)(l_Lean_Meta_mkStringLitNeProof___closed__34));
v___x_150_ = l_Lean_mkConst(v___x_149_, v___x_148_);
return v___x_150_;
}
}
static lean_object* _init_l_Lean_Meta_mkStringLitNeProof___closed__42(void){
_start:
{
lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_158_ = ((lean_object*)(l_Lean_Meta_mkStringLitNeProof___closed__5));
v___x_159_ = ((lean_object*)(l_Lean_Meta_mkStringLitNeProof___closed__41));
v___x_160_ = l_Lean_mkConst(v___x_159_, v___x_158_);
return v___x_160_;
}
}
static lean_object* _init_l_Lean_Meta_mkStringLitNeProof___closed__45(void){
_start:
{
lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_164_ = lean_obj_once(&l_Lean_Meta_mkStringLitNeProof___closed__36, &l_Lean_Meta_mkStringLitNeProof___closed__36_once, _init_l_Lean_Meta_mkStringLitNeProof___closed__36);
v___x_165_ = lean_obj_once(&l_Lean_Meta_mkStringLitNeProof___closed__35, &l_Lean_Meta_mkStringLitNeProof___closed__35_once, _init_l_Lean_Meta_mkStringLitNeProof___closed__35);
v___x_166_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_166_, 0, v___x_165_);
lean_ctor_set(v___x_166_, 1, v___x_164_);
return v___x_166_;
}
}
static lean_object* _init_l_Lean_Meta_mkStringLitNeProof___closed__46(void){
_start:
{
lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
v___x_167_ = lean_obj_once(&l_Lean_Meta_mkStringLitNeProof___closed__45, &l_Lean_Meta_mkStringLitNeProof___closed__45_once, _init_l_Lean_Meta_mkStringLitNeProof___closed__45);
v___x_168_ = ((lean_object*)(l_Lean_Meta_mkStringLitNeProof___closed__44));
v___x_169_ = l_Lean_mkConst(v___x_168_, v___x_167_);
return v___x_169_;
}
}
static lean_object* _init_l_Lean_Meta_mkStringLitNeProof___closed__49(void){
_start:
{
lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v_inhabCharExpr_176_; 
v___x_174_ = lean_box(0);
v___x_175_ = ((lean_object*)(l_Lean_Meta_mkStringLitNeProof___closed__48));
v_inhabCharExpr_176_ = l_Lean_mkConst(v___x_175_, v___x_174_);
return v_inhabCharExpr_176_;
}
}
static lean_object* _init_l_Lean_Meta_mkStringLitNeProof___closed__52(void){
_start:
{
lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v_natConst_182_; 
v___x_180_ = lean_box(0);
v___x_181_ = ((lean_object*)(l_Lean_Meta_mkStringLitNeProof___closed__51));
v_natConst_182_ = l_Lean_mkConst(v___x_181_, v___x_180_);
return v_natConst_182_;
}
}
static lean_object* _init_l_Lean_Meta_mkStringLitNeProof___closed__55(void){
_start:
{
lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; 
v___x_187_ = lean_box(0);
v___x_188_ = ((lean_object*)(l_Lean_Meta_mkStringLitNeProof___closed__54));
v___x_189_ = l_Lean_mkConst(v___x_188_, v___x_187_);
return v___x_189_;
}
}
static lean_object* _init_l_Lean_Meta_mkStringLitNeProof___closed__58(void){
_start:
{
lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_194_ = ((lean_object*)(l_Lean_Meta_mkStringLitNeProof___closed__5));
v___x_195_ = ((lean_object*)(l_Lean_Meta_mkStringLitNeProof___closed__57));
v___x_196_ = l_Lean_mkConst(v___x_195_, v___x_194_);
return v___x_196_;
}
}
static lean_object* _init_l_Lean_Meta_mkStringLitNeProof___closed__62(void){
_start:
{
lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_202_ = lean_box(0);
v___x_203_ = ((lean_object*)(l_Lean_Meta_mkStringLitNeProof___closed__61));
v___x_204_ = l_Lean_mkConst(v___x_203_, v___x_202_);
return v___x_204_;
}
}
static lean_object* _init_l_Lean_Meta_mkStringLitNeProof___closed__65(void){
_start:
{
lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_209_ = lean_box(0);
v___x_210_ = ((lean_object*)(l_Lean_Meta_mkStringLitNeProof___closed__64));
v___x_211_ = l_Lean_mkConst(v___x_210_, v___x_209_);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkStringLitNeProof(lean_object* v_s_u2081_212_, lean_object* v_s_u2082_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_){
_start:
{
lean_object* v_l_u2081_219_; lean_object* v_l_u2082_220_; lean_object* v_type_221_; lean_object* v_nil_222_; lean_object* v___x_223_; lean_object* v_cons_224_; lean_object* v_l_u2081Expr_225_; lean_object* v_l_u2082Expr_226_; lean_object* v___y_228_; lean_object* v___y_229_; lean_object* v_listNeProof_230_; lean_object* v___y_242_; lean_object* v___y_243_; lean_object* v___y_244_; lean_object* v___y_245_; lean_object* v___y_246_; lean_object* v_listCharTy_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___y_253_; lean_object* v___y_254_; lean_object* v___y_255_; lean_object* v___y_256_; lean_object* v___y_257_; uint32_t v_fst_258_; lean_object* v_snd_259_; lean_object* v___y_273_; lean_object* v___y_274_; lean_object* v___y_275_; lean_object* v___y_327_; uint8_t v___x_335_; 
v_l_u2081_219_ = l_String_toListImpl(v_s_u2081_212_);
v_l_u2082_220_ = l_String_toListImpl(v_s_u2082_213_);
v_type_221_ = lean_obj_once(&l_Lean_Meta_mkStringLitNeProof___closed__1, &l_Lean_Meta_mkStringLitNeProof___closed__1_once, _init_l_Lean_Meta_mkStringLitNeProof___closed__1);
v_nil_222_ = lean_obj_once(&l_Lean_Meta_mkStringLitNeProof___closed__7, &l_Lean_Meta_mkStringLitNeProof___closed__7_once, _init_l_Lean_Meta_mkStringLitNeProof___closed__7);
v___x_223_ = lean_obj_once(&l_Lean_Meta_mkStringLitNeProof___closed__10, &l_Lean_Meta_mkStringLitNeProof___closed__10_once, _init_l_Lean_Meta_mkStringLitNeProof___closed__10);
v_cons_224_ = lean_obj_once(&l_Lean_Meta_mkStringLitNeProof___closed__11, &l_Lean_Meta_mkStringLitNeProof___closed__11_once, _init_l_Lean_Meta_mkStringLitNeProof___closed__11);
v_l_u2081Expr_225_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Meta_mkStringLitNeProof_spec__0(v_nil_222_, v_cons_224_, v_l_u2081_219_);
v_l_u2082Expr_226_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Meta_mkStringLitNeProof_spec__0(v_nil_222_, v_cons_224_, v_l_u2082_220_);
v_listCharTy_249_ = lean_obj_once(&l_Lean_Meta_mkStringLitNeProof___closed__26, &l_Lean_Meta_mkStringLitNeProof___closed__26_once, _init_l_Lean_Meta_mkStringLitNeProof___closed__26);
v___x_250_ = l_List_lengthTR___redArg(v_l_u2081_219_);
v___x_251_ = l_List_lengthTR___redArg(v_l_u2082_220_);
v___x_335_ = lean_nat_dec_le(v___x_250_, v___x_251_);
if (v___x_335_ == 0)
{
lean_inc(v___x_251_);
v___y_327_ = v___x_251_;
goto v___jp_326_;
}
else
{
lean_inc(v___x_250_);
v___y_327_ = v___x_250_;
goto v___jp_326_;
}
v___jp_227_:
{
lean_object* v_strType_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v_strEq_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
v_strType_231_ = lean_obj_once(&l_Lean_Meta_mkStringLitNeProof___closed__14, &l_Lean_Meta_mkStringLitNeProof___closed__14_once, _init_l_Lean_Meta_mkStringLitNeProof___closed__14);
v___x_232_ = lean_obj_once(&l_Lean_Meta_mkStringLitNeProof___closed__17, &l_Lean_Meta_mkStringLitNeProof___closed__17_once, _init_l_Lean_Meta_mkStringLitNeProof___closed__17);
lean_inc_ref(v_l_u2081Expr_225_);
v___x_233_ = l_Lean_Expr_app___override(v___x_232_, v_l_u2081Expr_225_);
lean_inc_ref(v_l_u2082Expr_226_);
v___x_234_ = l_Lean_Expr_app___override(v___x_232_, v_l_u2082Expr_226_);
v_strEq_235_ = l_Lean_mkApp3(v___y_229_, v_strType_231_, v___x_233_, v___x_234_);
v___x_236_ = lean_obj_once(&l_Lean_Meta_mkStringLitNeProof___closed__20, &l_Lean_Meta_mkStringLitNeProof___closed__20_once, _init_l_Lean_Meta_mkStringLitNeProof___closed__20);
v___x_237_ = lean_obj_once(&l_Lean_Meta_mkStringLitNeProof___closed__23, &l_Lean_Meta_mkStringLitNeProof___closed__23_once, _init_l_Lean_Meta_mkStringLitNeProof___closed__23);
v___x_238_ = l_Lean_mkAppB(v___x_237_, v_l_u2081Expr_225_, v_l_u2082Expr_226_);
v___x_239_ = l_Lean_mkApp4(v___x_236_, v_strEq_235_, v___y_228_, v___x_238_, v_listNeProof_230_);
v___x_240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_240_, 0, v___x_239_);
return v___x_240_;
}
v___jp_241_:
{
lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_247_ = lean_obj_once(&l_Lean_Meta_mkStringLitNeProof___closed__20, &l_Lean_Meta_mkStringLitNeProof___closed__20_once, _init_l_Lean_Meta_mkStringLitNeProof___closed__20);
lean_inc_ref(v___y_242_);
v___x_248_ = l_Lean_mkApp4(v___x_247_, v___y_242_, v___y_243_, v___y_244_, v___y_246_);
v___y_228_ = v___y_242_;
v___y_229_ = v___y_245_;
v_listNeProof_230_ = v___x_248_;
goto v___jp_227_;
}
v___jp_252_:
{
lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v_hdExpr_263_; lean_object* v_tlExpr_264_; lean_object* v___x_265_; lean_object* v_consNeNil_266_; uint8_t v___x_267_; 
v___x_260_ = lean_obj_once(&l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Meta_mkStringLitNeProof_spec__0___closed__3, &l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Meta_mkStringLitNeProof_spec__0___closed__3_once, _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Meta_mkStringLitNeProof_spec__0___closed__3);
v___x_261_ = lean_uint32_to_nat(v_fst_258_);
v___x_262_ = l_Lean_mkRawNatLit(v___x_261_);
v_hdExpr_263_ = l_Lean_Expr_app___override(v___x_260_, v___x_262_);
v_tlExpr_264_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Meta_mkStringLitNeProof_spec__0(v_nil_222_, v_cons_224_, v_snd_259_);
lean_dec(v_snd_259_);
v___x_265_ = lean_obj_once(&l_Lean_Meta_mkStringLitNeProof___closed__29, &l_Lean_Meta_mkStringLitNeProof___closed__29_once, _init_l_Lean_Meta_mkStringLitNeProof___closed__29);
lean_inc_ref(v_tlExpr_264_);
lean_inc_ref(v_hdExpr_263_);
v_consNeNil_266_ = l_Lean_mkApp3(v___x_265_, v_type_221_, v_hdExpr_263_, v_tlExpr_264_);
v___x_267_ = lean_nat_dec_le(v___x_250_, v___x_251_);
lean_dec(v___x_251_);
lean_dec(v___x_250_);
if (v___x_267_ == 0)
{
lean_dec_ref(v_tlExpr_264_);
lean_dec_ref(v_hdExpr_263_);
v___y_242_ = v___y_254_;
v___y_243_ = v___y_255_;
v___y_244_ = v___y_256_;
v___y_245_ = v___y_257_;
v___y_246_ = v_consNeNil_266_;
goto v___jp_241_;
}
else
{
lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_268_ = ((lean_object*)(l_Lean_Meta_mkStringLitNeProof___closed__32));
lean_inc(v___y_253_);
v___x_269_ = l_Lean_mkConst(v___x_268_, v___y_253_);
v___x_270_ = l_Lean_mkApp3(v___x_223_, v_type_221_, v_hdExpr_263_, v_tlExpr_264_);
v___x_271_ = l_Lean_mkApp4(v___x_269_, v_listCharTy_249_, v___x_270_, v_nil_222_, v_consNeNil_266_);
v___y_242_ = v___y_254_;
v___y_243_ = v___y_255_;
v___y_244_ = v___y_256_;
v___y_245_ = v___y_257_;
v___y_246_ = v___x_271_;
goto v___jp_241_;
}
}
v___jp_272_:
{
lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v_listEq_278_; uint8_t v___x_279_; 
v___x_276_ = lean_obj_once(&l_Lean_Meta_mkStringLitNeProof___closed__36, &l_Lean_Meta_mkStringLitNeProof___closed__36_once, _init_l_Lean_Meta_mkStringLitNeProof___closed__36);
v___x_277_ = lean_obj_once(&l_Lean_Meta_mkStringLitNeProof___closed__37, &l_Lean_Meta_mkStringLitNeProof___closed__37_once, _init_l_Lean_Meta_mkStringLitNeProof___closed__37);
lean_inc_ref(v_l_u2082Expr_226_);
lean_inc_ref(v_l_u2081Expr_225_);
v_listEq_278_ = l_Lean_mkApp3(v___x_277_, v_listCharTy_249_, v_l_u2081Expr_225_, v_l_u2082Expr_226_);
v___x_279_ = lean_nat_dec_lt(v___y_275_, v___y_273_);
if (v___x_279_ == 0)
{
lean_object* v_nExpr_280_; lean_object* v___x_281_; uint8_t v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v_dropFn_286_; lean_object* v_dropL1_287_; lean_object* v_dropL2_288_; lean_object* v_dropEq_289_; lean_object* v___x_290_; lean_object* v_congrArgFn_291_; uint8_t v___x_292_; 
lean_dec(v___y_275_);
lean_inc(v___y_273_);
v_nExpr_280_ = l_Lean_mkNatLit(v___y_273_);
v___x_281_ = ((lean_object*)(l_Lean_Meta_mkStringLitNeProof___closed__39));
v___x_282_ = 0;
v___x_283_ = lean_obj_once(&l_Lean_Meta_mkStringLitNeProof___closed__42, &l_Lean_Meta_mkStringLitNeProof___closed__42_once, _init_l_Lean_Meta_mkStringLitNeProof___closed__42);
v___x_284_ = l_Lean_mkBVar(v___y_274_);
lean_inc_ref_n(v_nExpr_280_, 2);
v___x_285_ = l_Lean_mkApp3(v___x_283_, v_type_221_, v_nExpr_280_, v___x_284_);
v_dropFn_286_ = l_Lean_mkLambda(v___x_281_, v___x_282_, v_listCharTy_249_, v___x_285_);
lean_inc_ref_n(v_l_u2081Expr_225_, 2);
v_dropL1_287_ = l_Lean_mkApp3(v___x_283_, v_type_221_, v_nExpr_280_, v_l_u2081Expr_225_);
lean_inc_ref_n(v_l_u2082Expr_226_, 2);
v_dropL2_288_ = l_Lean_mkApp3(v___x_283_, v_type_221_, v_nExpr_280_, v_l_u2082Expr_226_);
v_dropEq_289_ = l_Lean_mkApp3(v___x_277_, v_listCharTy_249_, v_dropL1_287_, v_dropL2_288_);
v___x_290_ = lean_obj_once(&l_Lean_Meta_mkStringLitNeProof___closed__46, &l_Lean_Meta_mkStringLitNeProof___closed__46_once, _init_l_Lean_Meta_mkStringLitNeProof___closed__46);
v_congrArgFn_291_ = l_Lean_mkApp5(v___x_290_, v_listCharTy_249_, v_listCharTy_249_, v_l_u2081Expr_225_, v_l_u2082Expr_226_, v_dropFn_286_);
v___x_292_ = lean_nat_dec_le(v___x_250_, v___x_251_);
if (v___x_292_ == 0)
{
lean_object* v_dropped_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; uint32_t v___x_297_; 
lean_dec(v_l_u2082_220_);
v_dropped_293_ = l_List_drop___redArg(v___y_273_, v_l_u2081_219_);
lean_dec(v_l_u2081_219_);
v___x_294_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkStringLitNeProof_spec__1___redArg___boxed__const__1;
v___x_295_ = l_List_head_x21___redArg(v___x_294_, v_dropped_293_);
v___x_296_ = l_List_tail_x21___redArg(v_dropped_293_);
lean_dec(v_dropped_293_);
v___x_297_ = lean_unbox_uint32(v___x_295_);
lean_dec(v___x_295_);
v___y_253_ = v___x_276_;
v___y_254_ = v_listEq_278_;
v___y_255_ = v_dropEq_289_;
v___y_256_ = v_congrArgFn_291_;
v___y_257_ = v___x_277_;
v_fst_258_ = v___x_297_;
v_snd_259_ = v___x_296_;
goto v___jp_252_;
}
else
{
lean_object* v_dropped_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; uint32_t v___x_302_; 
lean_dec(v_l_u2081_219_);
v_dropped_298_ = l_List_drop___redArg(v___y_273_, v_l_u2082_220_);
lean_dec(v_l_u2082_220_);
v___x_299_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkStringLitNeProof_spec__1___redArg___boxed__const__1;
v___x_300_ = l_List_head_x21___redArg(v___x_299_, v_dropped_298_);
v___x_301_ = l_List_tail_x21___redArg(v_dropped_298_);
lean_dec(v_dropped_298_);
v___x_302_ = lean_unbox_uint32(v___x_300_);
lean_dec(v___x_300_);
v___y_253_ = v___x_276_;
v___y_254_ = v_listEq_278_;
v___y_255_ = v_dropEq_289_;
v___y_256_ = v_congrArgFn_291_;
v___y_257_ = v___x_277_;
v_fst_258_ = v___x_302_;
v_snd_259_ = v___x_301_;
goto v___jp_252_;
}
}
else
{
lean_object* v_inhabCharExpr_303_; lean_object* v_natConst_304_; lean_object* v_iExpr_305_; lean_object* v___x_306_; uint8_t v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v_projFn_313_; lean_object* v_projL1_314_; lean_object* v_projL2_315_; lean_object* v_projEq_316_; lean_object* v___x_317_; lean_object* v_congrArgFn_318_; lean_object* v___x_319_; lean_object* v___x_320_; 
lean_dec(v___y_273_);
lean_dec(v___x_251_);
lean_dec(v___x_250_);
lean_dec(v_l_u2082_220_);
lean_dec(v_l_u2081_219_);
v_inhabCharExpr_303_ = lean_obj_once(&l_Lean_Meta_mkStringLitNeProof___closed__49, &l_Lean_Meta_mkStringLitNeProof___closed__49_once, _init_l_Lean_Meta_mkStringLitNeProof___closed__49);
v_natConst_304_ = lean_obj_once(&l_Lean_Meta_mkStringLitNeProof___closed__52, &l_Lean_Meta_mkStringLitNeProof___closed__52_once, _init_l_Lean_Meta_mkStringLitNeProof___closed__52);
v_iExpr_305_ = l_Lean_mkNatLit(v___y_275_);
v___x_306_ = ((lean_object*)(l_Lean_Meta_mkStringLitNeProof___closed__39));
v___x_307_ = 0;
v___x_308_ = lean_obj_once(&l_Lean_Meta_mkStringLitNeProof___closed__55, &l_Lean_Meta_mkStringLitNeProof___closed__55_once, _init_l_Lean_Meta_mkStringLitNeProof___closed__55);
v___x_309_ = lean_obj_once(&l_Lean_Meta_mkStringLitNeProof___closed__58, &l_Lean_Meta_mkStringLitNeProof___closed__58_once, _init_l_Lean_Meta_mkStringLitNeProof___closed__58);
v___x_310_ = l_Lean_mkBVar(v___y_274_);
lean_inc_ref_n(v_iExpr_305_, 2);
v___x_311_ = l_Lean_mkApp4(v___x_309_, v_type_221_, v_inhabCharExpr_303_, v___x_310_, v_iExpr_305_);
v___x_312_ = l_Lean_Expr_app___override(v___x_308_, v___x_311_);
v_projFn_313_ = l_Lean_mkLambda(v___x_306_, v___x_307_, v_listCharTy_249_, v___x_312_);
lean_inc_ref_n(v_l_u2081Expr_225_, 2);
v_projL1_314_ = l_Lean_Meta_mkStringLitNeProof___lam__0(v___x_309_, v_type_221_, v_inhabCharExpr_303_, v_iExpr_305_, v___x_308_, v_l_u2081Expr_225_);
lean_inc_ref_n(v_l_u2082Expr_226_, 2);
v_projL2_315_ = l_Lean_Meta_mkStringLitNeProof___lam__0(v___x_309_, v_type_221_, v_inhabCharExpr_303_, v_iExpr_305_, v___x_308_, v_l_u2082Expr_226_);
lean_inc_ref(v_projL2_315_);
lean_inc_ref(v_projL1_314_);
v_projEq_316_ = l_Lean_mkApp3(v___x_277_, v_natConst_304_, v_projL1_314_, v_projL2_315_);
v___x_317_ = lean_obj_once(&l_Lean_Meta_mkStringLitNeProof___closed__46, &l_Lean_Meta_mkStringLitNeProof___closed__46_once, _init_l_Lean_Meta_mkStringLitNeProof___closed__46);
v_congrArgFn_318_ = l_Lean_mkApp5(v___x_317_, v_listCharTy_249_, v_natConst_304_, v_l_u2081Expr_225_, v_l_u2082Expr_226_, v_projFn_313_);
v___x_319_ = lean_obj_once(&l_Lean_Meta_mkStringLitNeProof___closed__62, &l_Lean_Meta_mkStringLitNeProof___closed__62_once, _init_l_Lean_Meta_mkStringLitNeProof___closed__62);
v___x_320_ = l_Lean_Meta_mkEqRefl(v___x_319_, v_a_214_, v_a_215_, v_a_216_, v_a_217_);
if (lean_obj_tag(v___x_320_) == 0)
{
lean_object* v_a_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; 
v_a_321_ = lean_ctor_get(v___x_320_, 0);
lean_inc(v_a_321_);
lean_dec_ref_known(v___x_320_, 1);
v___x_322_ = lean_obj_once(&l_Lean_Meta_mkStringLitNeProof___closed__65, &l_Lean_Meta_mkStringLitNeProof___closed__65_once, _init_l_Lean_Meta_mkStringLitNeProof___closed__65);
v___x_323_ = l_Lean_mkApp3(v___x_322_, v_projL1_314_, v_projL2_315_, v_a_321_);
v___x_324_ = lean_obj_once(&l_Lean_Meta_mkStringLitNeProof___closed__20, &l_Lean_Meta_mkStringLitNeProof___closed__20_once, _init_l_Lean_Meta_mkStringLitNeProof___closed__20);
lean_inc_ref(v_listEq_278_);
v___x_325_ = l_Lean_mkApp4(v___x_324_, v_listEq_278_, v_projEq_316_, v_congrArgFn_318_, v___x_323_);
v___y_228_ = v_listEq_278_;
v___y_229_ = v___x_277_;
v_listNeProof_230_ = v___x_325_;
goto v___jp_227_;
}
else
{
lean_dec_ref(v_congrArgFn_318_);
lean_dec_ref(v_projEq_316_);
lean_dec_ref(v_projL2_315_);
lean_dec_ref(v_projL1_314_);
lean_dec_ref(v_listEq_278_);
lean_dec_ref(v_l_u2082Expr_226_);
lean_dec_ref(v_l_u2081Expr_225_);
return v___x_320_;
}
}
}
v___jp_326_:
{
lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v_fst_333_; 
v___x_328_ = lean_unsigned_to_nat(0u);
v___x_329_ = lean_unsigned_to_nat(1u);
lean_inc(v___y_327_);
v___x_330_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_330_, 0, v___x_328_);
lean_ctor_set(v___x_330_, 1, v___y_327_);
lean_ctor_set(v___x_330_, 2, v___x_329_);
v___x_331_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkStringLitNeProof_spec__1___redArg___closed__0));
v___x_332_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkStringLitNeProof_spec__1___redArg(v_l_u2081_219_, v_l_u2082_220_, v___x_330_, v___x_331_, v___x_328_);
lean_dec_ref_known(v___x_330_, 3);
v_fst_333_ = lean_ctor_get(v___x_332_, 0);
lean_inc(v_fst_333_);
lean_dec_ref(v___x_332_);
if (lean_obj_tag(v_fst_333_) == 0)
{
lean_inc(v___y_327_);
v___y_273_ = v___y_327_;
v___y_274_ = v___x_328_;
v___y_275_ = v___y_327_;
goto v___jp_272_;
}
else
{
lean_object* v_val_334_; 
v_val_334_ = lean_ctor_get(v_fst_333_, 0);
lean_inc(v_val_334_);
lean_dec_ref_known(v_fst_333_, 1);
v___y_273_ = v___y_327_;
v___y_274_ = v___x_328_;
v___y_275_ = v_val_334_;
goto v___jp_272_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkStringLitNeProof___boxed(lean_object* v_s_u2081_336_, lean_object* v_s_u2082_337_, lean_object* v_a_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_){
_start:
{
lean_object* v_res_343_; 
v_res_343_ = l_Lean_Meta_mkStringLitNeProof(v_s_u2081_336_, v_s_u2082_337_, v_a_338_, v_a_339_, v_a_340_, v_a_341_);
lean_dec(v_a_341_);
lean_dec_ref(v_a_340_);
lean_dec(v_a_339_);
lean_dec_ref(v_a_338_);
return v_res_343_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkStringLitNeProof_spec__1(lean_object* v_l_u2081_344_, lean_object* v_l_u2082_345_, lean_object* v_range_346_, lean_object* v_b_347_, lean_object* v_i_348_, lean_object* v_hs_349_, lean_object* v_hl_350_){
_start:
{
lean_object* v___x_351_; 
v___x_351_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkStringLitNeProof_spec__1___redArg(v_l_u2081_344_, v_l_u2082_345_, v_range_346_, v_b_347_, v_i_348_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkStringLitNeProof_spec__1___boxed(lean_object* v_l_u2081_352_, lean_object* v_l_u2082_353_, lean_object* v_range_354_, lean_object* v_b_355_, lean_object* v_i_356_, lean_object* v_hs_357_, lean_object* v_hl_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkStringLitNeProof_spec__1(v_l_u2081_352_, v_l_u2082_353_, v_range_354_, v_b_355_, v_i_356_, v_hs_357_, v_hl_358_);
lean_dec_ref(v_b_355_);
lean_dec_ref(v_range_354_);
lean_dec(v_l_u2082_353_);
lean_dec(v_l_u2081_352_);
return v_res_359_;
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
l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkStringLitNeProof_spec__1___redArg___boxed__const__1 = _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkStringLitNeProof_spec__1___redArg___boxed__const__1();
lean_mark_persistent(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkStringLitNeProof_spec__1___redArg___boxed__const__1);
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

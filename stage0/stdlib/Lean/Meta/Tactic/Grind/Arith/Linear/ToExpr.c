// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Linear.ToExpr
// Imports: public import Init.Grind.Ordered.Linarith public import Lean.ToExpr
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
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Linarith"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__2_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Poly"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__3_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "nil"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__4_value;
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__5_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__2_value),LEAN_SCALAR_PTR_LITERAL(199, 207, 141, 119, 115, 174, 198, 240)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__5_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__3_value),LEAN_SCALAR_PTR_LITERAL(37, 10, 138, 160, 35, 126, 254, 250)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__5_value_aux_3),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__4_value),LEAN_SCALAR_PTR_LITERAL(74, 252, 131, 19, 226, 216, 188, 177)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__5_value;
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__6;
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "add"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__7_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__8_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__8_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__2_value),LEAN_SCALAR_PTR_LITERAL(199, 207, 141, 119, 115, 174, 198, 240)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__8_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__8_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__3_value),LEAN_SCALAR_PTR_LITERAL(37, 10, 138, 160, 35, 126, 254, 250)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__8_value_aux_3),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__7_value),LEAN_SCALAR_PTR_LITERAL(196, 1, 15, 110, 230, 219, 186, 229)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__8_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__9;
lean_object* lean_nat_to_int(lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__10;
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Neg"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__11 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__11_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "neg"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__12 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__12_value;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__11_value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__13_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__12_value),LEAN_SCALAR_PTR_LITERAL(105, 26, 70, 221, 245, 238, 127, 238)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__13 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__13_value;
lean_object* l_Lean_Level_ofNat(lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__14;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__15;
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__16;
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Int"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__17 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__17_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__17_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__18 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__18_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__19;
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "instNegInt"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__20 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__20_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__17_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__21_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__20_value),LEAN_SCALAR_PTR_LITERAL(217, 109, 233, 1, 211, 122, 77, 88)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__21 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__21_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__22;
lean_object* l_Lean_mkNatLit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_ofPoly(lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* l_Int_toNat(lean_object*);
lean_object* l_Lean_instToExprInt_mkNat(lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Arith_Linear_instToExprPoly___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_Linear_ofPoly, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_instToExprPoly___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_instToExprPoly___closed__0_value;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_instToExprPoly___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_instToExprPoly___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_instToExprPoly___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_instToExprPoly___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_instToExprPoly___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__2_value),LEAN_SCALAR_PTR_LITERAL(199, 207, 141, 119, 115, 174, 198, 240)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_instToExprPoly___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_instToExprPoly___closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__3_value),LEAN_SCALAR_PTR_LITERAL(37, 10, 138, 160, 35, 126, 254, 250)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_instToExprPoly___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_instToExprPoly___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_instToExprPoly___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_instToExprPoly___closed__2;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_instToExprPoly___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_instToExprPoly___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instToExprPoly;
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Expr"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "zero"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__2_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__2_value),LEAN_SCALAR_PTR_LITERAL(199, 207, 141, 119, 115, 174, 198, 240)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__2_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(105, 86, 71, 240, 204, 96, 94, 7)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__2_value_aux_3),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(121, 236, 176, 123, 232, 242, 126, 4)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__3;
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "var"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__5_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__2_value),LEAN_SCALAR_PTR_LITERAL(199, 207, 141, 119, 115, 174, 198, 240)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__5_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(105, 86, 71, 240, 204, 96, 94, 7)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__5_value_aux_3),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(180, 14, 161, 210, 87, 20, 146, 171)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__6;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__7_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__7_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__2_value),LEAN_SCALAR_PTR_LITERAL(199, 207, 141, 119, 115, 174, 198, 240)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__7_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__7_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(105, 86, 71, 240, 204, 96, 94, 7)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__7_value_aux_3),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__7_value),LEAN_SCALAR_PTR_LITERAL(88, 121, 158, 198, 135, 175, 78, 144)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__7_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__8;
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "sub"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__9_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__10_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__10_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__2_value),LEAN_SCALAR_PTR_LITERAL(199, 207, 141, 119, 115, 174, 198, 240)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__10_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__10_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(105, 86, 71, 240, 204, 96, 94, 7)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__10_value_aux_3),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__9_value),LEAN_SCALAR_PTR_LITERAL(163, 244, 246, 246, 100, 198, 17, 84)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__10 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__10_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__11;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__12_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__12_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__2_value),LEAN_SCALAR_PTR_LITERAL(199, 207, 141, 119, 115, 174, 198, 240)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__12_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__12_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(105, 86, 71, 240, 204, 96, 94, 7)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__12_value_aux_3),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__12_value),LEAN_SCALAR_PTR_LITERAL(154, 99, 21, 209, 238, 42, 102, 14)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__12 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__12_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__13;
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "natMul"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__14 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__14_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__15_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__15_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__2_value),LEAN_SCALAR_PTR_LITERAL(199, 207, 141, 119, 115, 174, 198, 240)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__15_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__15_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(105, 86, 71, 240, 204, 96, 94, 7)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__15_value_aux_3),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__14_value),LEAN_SCALAR_PTR_LITERAL(50, 107, 187, 27, 62, 91, 183, 33)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__15 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__15_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__16;
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "intMul"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__17 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__17_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__18_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__18_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__18_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__2_value),LEAN_SCALAR_PTR_LITERAL(199, 207, 141, 119, 115, 174, 198, 240)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__18_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__18_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(105, 86, 71, 240, 204, 96, 94, 7)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__18_value_aux_3),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__17_value),LEAN_SCALAR_PTR_LITERAL(145, 232, 129, 173, 28, 250, 158, 19)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__18 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__18_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__19;
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_ofLinExpr(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Arith_Linear_instToExprExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_Linear_ofLinExpr, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_instToExprExpr___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_instToExprExpr___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_instToExprExpr___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_instToExprExpr___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_instToExprExpr___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_instToExprExpr___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_instToExprExpr___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__2_value),LEAN_SCALAR_PTR_LITERAL(199, 207, 141, 119, 115, 174, 198, 240)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_instToExprExpr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_instToExprExpr___closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(105, 86, 71, 240, 204, 96, 94, 7)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_instToExprExpr___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_instToExprExpr___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_instToExprExpr___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_instToExprExpr___closed__2;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_instToExprExpr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_instToExprExpr___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instToExprExpr;
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__5));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__9(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__8));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__10(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__14(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Level_ofNat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__15(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__14, &l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__14_once, _init_l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__14);
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__16(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__15, &l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__15_once, _init_l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__15);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__13));
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__19(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__18));
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__22(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__21));
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_ofPoly(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__6, &l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__6_once, _init_l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__6);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_12; uint8_t x_13; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__9, &l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__9_once, _init_l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__9);
x_12 = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__10, &l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__10_once, _init_l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__10);
x_13 = lean_int_dec_le(x_12, x_3);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__16, &l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__16_once, _init_l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__16);
x_15 = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__19, &l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__19_once, _init_l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__19);
x_16 = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__22, &l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__22_once, _init_l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__22);
x_17 = lean_int_neg(x_3);
lean_dec(x_3);
x_18 = l_Int_toNat(x_17);
lean_dec(x_17);
x_19 = l_Lean_instToExprInt_mkNat(x_18);
x_20 = l_Lean_mkApp3(x_14, x_15, x_16, x_19);
x_7 = x_20;
goto block_11;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = l_Int_toNat(x_3);
lean_dec(x_3);
x_22 = l_Lean_instToExprInt_mkNat(x_21);
x_7 = x_22;
goto block_11;
}
block_11:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Lean_mkNatLit(x_4);
x_9 = l_Lean_Meta_Grind_Arith_Linear_ofPoly(x_5);
x_10 = l_Lean_mkApp3(x_6, x_7, x_8, x_9);
return x_10;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instToExprPoly___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_instToExprPoly___closed__1));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instToExprPoly___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_instToExprPoly___closed__2, &l_Lean_Meta_Grind_Arith_Linear_instToExprPoly___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Linear_instToExprPoly___closed__2);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_instToExprPoly___closed__0));
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instToExprPoly(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_instToExprPoly___closed__3, &l_Lean_Meta_Grind_Arith_Linear_instToExprPoly___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Linear_instToExprPoly___closed__3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__2));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__5));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__8(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__7));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__11(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__10));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__13(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__12));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__16(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__15));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__19(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__18));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_ofLinExpr(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__3, &l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__3);
return x_2;
}
case 1:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec_ref(x_1);
x_4 = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__6, &l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__6_once, _init_l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__6);
x_5 = l_Lean_mkNatLit(x_3);
x_6 = l_Lean_Expr_app___override(x_4, x_5);
return x_6;
}
case 2:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec_ref(x_1);
x_9 = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__8, &l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__8_once, _init_l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__8);
x_10 = l_Lean_Meta_Grind_Arith_Linear_ofLinExpr(x_7);
x_11 = l_Lean_Meta_Grind_Arith_Linear_ofLinExpr(x_8);
x_12 = l_Lean_mkAppB(x_9, x_10, x_11);
return x_12;
}
case 3:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_dec_ref(x_1);
x_15 = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__11, &l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__11_once, _init_l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__11);
x_16 = l_Lean_Meta_Grind_Arith_Linear_ofLinExpr(x_13);
x_17 = l_Lean_Meta_Grind_Arith_Linear_ofLinExpr(x_14);
x_18 = l_Lean_mkAppB(x_15, x_16, x_17);
return x_18;
}
case 4:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
lean_dec_ref(x_1);
x_20 = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__13, &l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__13_once, _init_l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__13);
x_21 = l_Lean_Meta_Grind_Arith_Linear_ofLinExpr(x_19);
x_22 = l_Lean_Expr_app___override(x_20, x_21);
return x_22;
}
case 5:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_1, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_1, 1);
lean_inc(x_24);
lean_dec_ref(x_1);
x_25 = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__16, &l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__16_once, _init_l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__16);
x_26 = l_Lean_mkNatLit(x_23);
x_27 = l_Lean_Meta_Grind_Arith_Linear_ofLinExpr(x_24);
x_28 = l_Lean_mkAppB(x_25, x_26, x_27);
return x_28;
}
default: 
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_36; uint8_t x_37; 
x_29 = lean_ctor_get(x_1, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_1, 1);
lean_inc(x_30);
lean_dec_ref(x_1);
x_31 = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__19, &l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__19_once, _init_l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__19);
x_36 = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__10, &l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__10_once, _init_l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__10);
x_37 = lean_int_dec_le(x_36, x_29);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_38 = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__16, &l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__16_once, _init_l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__16);
x_39 = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__19, &l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__19_once, _init_l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__19);
x_40 = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__22, &l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__22_once, _init_l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__22);
x_41 = lean_int_neg(x_29);
lean_dec(x_29);
x_42 = l_Int_toNat(x_41);
lean_dec(x_41);
x_43 = l_Lean_instToExprInt_mkNat(x_42);
x_44 = l_Lean_mkApp3(x_38, x_39, x_40, x_43);
x_32 = x_44;
goto block_35;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = l_Int_toNat(x_29);
lean_dec(x_29);
x_46 = l_Lean_instToExprInt_mkNat(x_45);
x_32 = x_46;
goto block_35;
}
block_35:
{
lean_object* x_33; lean_object* x_34; 
x_33 = l_Lean_Meta_Grind_Arith_Linear_ofLinExpr(x_30);
x_34 = l_Lean_mkAppB(x_31, x_32, x_33);
return x_34;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instToExprExpr___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_instToExprExpr___closed__1));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instToExprExpr___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_instToExprExpr___closed__2, &l_Lean_Meta_Grind_Arith_Linear_instToExprExpr___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Linear_instToExprExpr___closed__2);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_instToExprExpr___closed__0));
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instToExprExpr(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_instToExprExpr___closed__3, &l_Lean_Meta_Grind_Arith_Linear_instToExprExpr___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Linear_instToExprExpr___closed__3);
return x_1;
}
}
lean_object* initialize_Init_Grind_Ordered_Linarith(uint8_t builtin);
lean_object* initialize_Lean_ToExpr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_ToExpr(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_Ordered_Linarith(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ToExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_Arith_Linear_instToExprPoly = _init_l_Lean_Meta_Grind_Arith_Linear_instToExprPoly();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_instToExprPoly);
l_Lean_Meta_Grind_Arith_Linear_instToExprExpr = _init_l_Lean_Meta_Grind_Arith_Linear_instToExprExpr();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_instToExprExpr);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

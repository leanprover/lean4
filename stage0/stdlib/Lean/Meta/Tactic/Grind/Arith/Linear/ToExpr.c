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
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* l_Int_toNat(lean_object*);
lean_object* l_Lean_instToExprInt_mkNat(lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__5_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__2_value),LEAN_SCALAR_PTR_LITERAL(199, 207, 141, 119, 115, 174, 198, 240)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__5_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__3_value),LEAN_SCALAR_PTR_LITERAL(37, 10, 138, 160, 35, 126, 254, 250)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__5_value_aux_3),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__4_value),LEAN_SCALAR_PTR_LITERAL(74, 252, 131, 19, 226, 216, 188, 177)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__5_value;
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
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__10;
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Neg"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__11 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__11_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "neg"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__12 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__12_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__11_value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__13_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__12_value),LEAN_SCALAR_PTR_LITERAL(105, 26, 70, 221, 245, 238, 127, 238)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__13 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__13_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__14;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__15;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__16;
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Int"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__17 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__17_value;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_ofPoly(lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Arith_Linear_instToExprPoly___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_Linear_ofPoly, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_instToExprPoly___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_instToExprPoly___closed__0_value;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_ofLinExpr(lean_object*);
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
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__6(void){
_start:
{
lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; 
v___x_12_ = lean_box(0);
v___x_13_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__5));
v___x_14_ = l_Lean_mkConst(v___x_13_, v___x_12_);
return v___x_14_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__9(void){
_start:
{
lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; 
v___x_22_ = lean_box(0);
v___x_23_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__8));
v___x_24_ = l_Lean_mkConst(v___x_23_, v___x_22_);
return v___x_24_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__10(void){
_start:
{
lean_object* v___x_25_; lean_object* v___x_26_; 
v___x_25_ = lean_unsigned_to_nat(0u);
v___x_26_ = lean_nat_to_int(v___x_25_);
return v___x_26_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__14(void){
_start:
{
lean_object* v___x_32_; lean_object* v___x_33_; 
v___x_32_ = lean_unsigned_to_nat(0u);
v___x_33_ = l_Lean_Level_ofNat(v___x_32_);
return v___x_33_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__15(void){
_start:
{
lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; 
v___x_34_ = lean_box(0);
v___x_35_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__14, &l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__14_once, _init_l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__14);
v___x_36_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_36_, 0, v___x_35_);
lean_ctor_set(v___x_36_, 1, v___x_34_);
return v___x_36_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__16(void){
_start:
{
lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; 
v___x_37_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__15, &l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__15_once, _init_l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__15);
v___x_38_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__13));
v___x_39_ = l_Lean_Expr_const___override(v___x_38_, v___x_37_);
return v___x_39_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__19(void){
_start:
{
lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; 
v___x_43_ = lean_box(0);
v___x_44_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__18));
v___x_45_ = l_Lean_Expr_const___override(v___x_44_, v___x_43_);
return v___x_45_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__22(void){
_start:
{
lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_50_ = lean_box(0);
v___x_51_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__21));
v___x_52_ = l_Lean_Expr_const___override(v___x_51_, v___x_50_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_ofPoly(lean_object* v_p_53_){
_start:
{
if (lean_obj_tag(v_p_53_) == 0)
{
lean_object* v___x_54_; 
v___x_54_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__6, &l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__6_once, _init_l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__6);
return v___x_54_;
}
else
{
lean_object* v_k_55_; lean_object* v_v_56_; lean_object* v_p_57_; lean_object* v___x_58_; lean_object* v___y_60_; lean_object* v___x_64_; uint8_t v___x_65_; 
v_k_55_ = lean_ctor_get(v_p_53_, 0);
lean_inc(v_k_55_);
v_v_56_ = lean_ctor_get(v_p_53_, 1);
lean_inc(v_v_56_);
v_p_57_ = lean_ctor_get(v_p_53_, 2);
lean_inc(v_p_57_);
lean_dec_ref(v_p_53_);
v___x_58_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__9, &l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__9_once, _init_l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__9);
v___x_64_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__10, &l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__10_once, _init_l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__10);
v___x_65_ = lean_int_dec_le(v___x_64_, v_k_55_);
if (v___x_65_ == 0)
{
lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_66_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__16, &l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__16_once, _init_l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__16);
v___x_67_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__19, &l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__19_once, _init_l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__19);
v___x_68_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__22, &l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__22_once, _init_l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__22);
v___x_69_ = lean_int_neg(v_k_55_);
lean_dec(v_k_55_);
v___x_70_ = l_Int_toNat(v___x_69_);
lean_dec(v___x_69_);
v___x_71_ = l_Lean_instToExprInt_mkNat(v___x_70_);
v___x_72_ = l_Lean_mkApp3(v___x_66_, v___x_67_, v___x_68_, v___x_71_);
v___y_60_ = v___x_72_;
goto v___jp_59_;
}
else
{
lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_73_ = l_Int_toNat(v_k_55_);
lean_dec(v_k_55_);
v___x_74_ = l_Lean_instToExprInt_mkNat(v___x_73_);
v___y_60_ = v___x_74_;
goto v___jp_59_;
}
v___jp_59_:
{
lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_61_ = l_Lean_mkNatLit(v_v_56_);
v___x_62_ = l_Lean_Meta_Grind_Arith_Linear_ofPoly(v_p_57_);
v___x_63_ = l_Lean_mkApp3(v___x_58_, v___y_60_, v___x_61_, v___x_62_);
return v___x_63_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instToExprPoly___closed__2(void){
_start:
{
lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; 
v___x_81_ = lean_box(0);
v___x_82_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_instToExprPoly___closed__1));
v___x_83_ = l_Lean_mkConst(v___x_82_, v___x_81_);
return v___x_83_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instToExprPoly___closed__3(void){
_start:
{
lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_84_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_instToExprPoly___closed__2, &l_Lean_Meta_Grind_Arith_Linear_instToExprPoly___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Linear_instToExprPoly___closed__2);
v___x_85_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_instToExprPoly___closed__0));
v___x_86_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_86_, 0, v___x_85_);
lean_ctor_set(v___x_86_, 1, v___x_84_);
return v___x_86_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instToExprPoly(void){
_start:
{
lean_object* v___x_87_; 
v___x_87_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_instToExprPoly___closed__3, &l_Lean_Meta_Grind_Arith_Linear_instToExprPoly___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Linear_instToExprPoly___closed__3);
return v___x_87_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__3(void){
_start:
{
lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_96_ = lean_box(0);
v___x_97_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__2));
v___x_98_ = l_Lean_mkConst(v___x_97_, v___x_96_);
return v___x_98_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__6(void){
_start:
{
lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_106_ = lean_box(0);
v___x_107_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__5));
v___x_108_ = l_Lean_mkConst(v___x_107_, v___x_106_);
return v___x_108_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__8(void){
_start:
{
lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_115_ = lean_box(0);
v___x_116_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__7));
v___x_117_ = l_Lean_mkConst(v___x_116_, v___x_115_);
return v___x_117_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__11(void){
_start:
{
lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_125_ = lean_box(0);
v___x_126_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__10));
v___x_127_ = l_Lean_mkConst(v___x_126_, v___x_125_);
return v___x_127_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__13(void){
_start:
{
lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_134_ = lean_box(0);
v___x_135_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__12));
v___x_136_ = l_Lean_mkConst(v___x_135_, v___x_134_);
return v___x_136_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__16(void){
_start:
{
lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_144_ = lean_box(0);
v___x_145_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__15));
v___x_146_ = l_Lean_mkConst(v___x_145_, v___x_144_);
return v___x_146_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__19(void){
_start:
{
lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_154_ = lean_box(0);
v___x_155_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__18));
v___x_156_ = l_Lean_mkConst(v___x_155_, v___x_154_);
return v___x_156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_ofLinExpr(lean_object* v_e_157_){
_start:
{
switch(lean_obj_tag(v_e_157_))
{
case 0:
{
lean_object* v___x_158_; 
v___x_158_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__3, &l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__3);
return v___x_158_;
}
case 1:
{
lean_object* v_i_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
v_i_159_ = lean_ctor_get(v_e_157_, 0);
lean_inc(v_i_159_);
lean_dec_ref(v_e_157_);
v___x_160_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__6, &l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__6_once, _init_l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__6);
v___x_161_ = l_Lean_mkNatLit(v_i_159_);
v___x_162_ = l_Lean_Expr_app___override(v___x_160_, v___x_161_);
return v___x_162_;
}
case 2:
{
lean_object* v_a_163_; lean_object* v_b_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
v_a_163_ = lean_ctor_get(v_e_157_, 0);
lean_inc(v_a_163_);
v_b_164_ = lean_ctor_get(v_e_157_, 1);
lean_inc(v_b_164_);
lean_dec_ref(v_e_157_);
v___x_165_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__8, &l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__8_once, _init_l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__8);
v___x_166_ = l_Lean_Meta_Grind_Arith_Linear_ofLinExpr(v_a_163_);
v___x_167_ = l_Lean_Meta_Grind_Arith_Linear_ofLinExpr(v_b_164_);
v___x_168_ = l_Lean_mkAppB(v___x_165_, v___x_166_, v___x_167_);
return v___x_168_;
}
case 3:
{
lean_object* v_a_169_; lean_object* v_b_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; 
v_a_169_ = lean_ctor_get(v_e_157_, 0);
lean_inc(v_a_169_);
v_b_170_ = lean_ctor_get(v_e_157_, 1);
lean_inc(v_b_170_);
lean_dec_ref(v_e_157_);
v___x_171_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__11, &l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__11_once, _init_l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__11);
v___x_172_ = l_Lean_Meta_Grind_Arith_Linear_ofLinExpr(v_a_169_);
v___x_173_ = l_Lean_Meta_Grind_Arith_Linear_ofLinExpr(v_b_170_);
v___x_174_ = l_Lean_mkAppB(v___x_171_, v___x_172_, v___x_173_);
return v___x_174_;
}
case 4:
{
lean_object* v_a_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; 
v_a_175_ = lean_ctor_get(v_e_157_, 0);
lean_inc(v_a_175_);
lean_dec_ref(v_e_157_);
v___x_176_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__13, &l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__13_once, _init_l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__13);
v___x_177_ = l_Lean_Meta_Grind_Arith_Linear_ofLinExpr(v_a_175_);
v___x_178_ = l_Lean_Expr_app___override(v___x_176_, v___x_177_);
return v___x_178_;
}
case 5:
{
lean_object* v_k_179_; lean_object* v_a_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
v_k_179_ = lean_ctor_get(v_e_157_, 0);
lean_inc(v_k_179_);
v_a_180_ = lean_ctor_get(v_e_157_, 1);
lean_inc(v_a_180_);
lean_dec_ref(v_e_157_);
v___x_181_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__16, &l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__16_once, _init_l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__16);
v___x_182_ = l_Lean_mkNatLit(v_k_179_);
v___x_183_ = l_Lean_Meta_Grind_Arith_Linear_ofLinExpr(v_a_180_);
v___x_184_ = l_Lean_mkAppB(v___x_181_, v___x_182_, v___x_183_);
return v___x_184_;
}
default: 
{
lean_object* v_k_185_; lean_object* v_a_186_; lean_object* v___x_187_; lean_object* v___y_189_; lean_object* v___x_192_; uint8_t v___x_193_; 
v_k_185_ = lean_ctor_get(v_e_157_, 0);
lean_inc(v_k_185_);
v_a_186_ = lean_ctor_get(v_e_157_, 1);
lean_inc(v_a_186_);
lean_dec_ref(v_e_157_);
v___x_187_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__19, &l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__19_once, _init_l_Lean_Meta_Grind_Arith_Linear_ofLinExpr___closed__19);
v___x_192_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__10, &l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__10_once, _init_l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__10);
v___x_193_ = lean_int_dec_le(v___x_192_, v_k_185_);
if (v___x_193_ == 0)
{
lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_194_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__16, &l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__16_once, _init_l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__16);
v___x_195_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__19, &l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__19_once, _init_l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__19);
v___x_196_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__22, &l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__22_once, _init_l_Lean_Meta_Grind_Arith_Linear_ofPoly___closed__22);
v___x_197_ = lean_int_neg(v_k_185_);
lean_dec(v_k_185_);
v___x_198_ = l_Int_toNat(v___x_197_);
lean_dec(v___x_197_);
v___x_199_ = l_Lean_instToExprInt_mkNat(v___x_198_);
v___x_200_ = l_Lean_mkApp3(v___x_194_, v___x_195_, v___x_196_, v___x_199_);
v___y_189_ = v___x_200_;
goto v___jp_188_;
}
else
{
lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_201_ = l_Int_toNat(v_k_185_);
lean_dec(v_k_185_);
v___x_202_ = l_Lean_instToExprInt_mkNat(v___x_201_);
v___y_189_ = v___x_202_;
goto v___jp_188_;
}
v___jp_188_:
{
lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_190_ = l_Lean_Meta_Grind_Arith_Linear_ofLinExpr(v_a_186_);
v___x_191_ = l_Lean_mkAppB(v___x_187_, v___y_189_, v___x_190_);
return v___x_191_;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instToExprExpr___closed__2(void){
_start:
{
lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_209_ = lean_box(0);
v___x_210_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_instToExprExpr___closed__1));
v___x_211_ = l_Lean_mkConst(v___x_210_, v___x_209_);
return v___x_211_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instToExprExpr___closed__3(void){
_start:
{
lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; 
v___x_212_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_instToExprExpr___closed__2, &l_Lean_Meta_Grind_Arith_Linear_instToExprExpr___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Linear_instToExprExpr___closed__2);
v___x_213_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_instToExprExpr___closed__0));
v___x_214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_214_, 0, v___x_213_);
lean_ctor_set(v___x_214_, 1, v___x_212_);
return v___x_214_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instToExprExpr(void){
_start:
{
lean_object* v___x_215_; 
v___x_215_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_instToExprExpr___closed__3, &l_Lean_Meta_Grind_Arith_Linear_instToExprExpr___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Linear_instToExprExpr___closed__3);
return v___x_215_;
}
}
lean_object* runtime_initialize_Init_Grind_Ordered_Linarith(uint8_t builtin);
lean_object* runtime_initialize_Lean_ToExpr(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_ToExpr(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Grind_Ordered_Linarith(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_ToExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_Arith_Linear_instToExprPoly = _init_l_Lean_Meta_Grind_Arith_Linear_instToExprPoly();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_instToExprPoly);
l_Lean_Meta_Grind_Arith_Linear_instToExprExpr = _init_l_Lean_Meta_Grind_Arith_Linear_instToExprExpr();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_instToExprExpr);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_ToExpr(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
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
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_ToExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_ToExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Arith_Linear_ToExpr(builtin);
}
#ifdef __cplusplus
}
#endif

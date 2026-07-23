// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.Arith.Nat.Simp
// Imports: public import Lean.Meta.Tactic.Simp.Arith.Util public import Lean.Meta.Tactic.Simp.Arith.Nat.Basic import Lean.Meta.AppBuilder
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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Arith_Nat_toLinearCnstr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith___redArg(lean_object*, lean_object*);
lean_object* l_Nat_Internal_Linear_ExprCnstr_toPoly(lean_object*);
lean_object* l_Nat_Internal_Linear_PolyCnstr_norm(lean_object*);
uint8_t l_Nat_Internal_Linear_PolyCnstr_isUnsat(lean_object*);
uint8_t l_Nat_Internal_Linear_PolyCnstr_isValid(lean_object*);
lean_object* l_Nat_Internal_Linear_PolyCnstr_toExpr(lean_object*);
lean_object* l_Lean_Meta_Simp_Arith_Nat_toContextExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr(lean_object*);
extern lean_object* l_Lean_eagerReflBoolTrue;
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkPropEq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkExpectedPropHint(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_succ___override(lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_mkNatAdd(lean_object*, lean_object*);
lean_object* l_Lean_mkNatLE(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Arith_Nat_toLinearExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_Internal_Linear_Expr_toPoly(lean_object*);
lean_object* l_Nat_Internal_Linear_Poly_norm(lean_object*);
lean_object* l_Nat_Internal_Linear_Poly_toExpr(lean_object*);
uint8_t l_Nat_Internal_Linear_instBEqExpr_beq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr(lean_object*);
lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(lean_object*, lean_object*);
lean_object* l_Lean_mkNatEq(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__0_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Internal"};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__1_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Linear"};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__2 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__2_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "ExprCnstr"};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__3 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__3_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "eq_of_toNormPoly_eq"};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__4 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(238, 85, 239, 193, 128, 115, 38, 143)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__5_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(135, 17, 186, 49, 10, 156, 173, 153)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__5_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 198, 254, 91, 59, 223, 24, 67)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__5_value_aux_3),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(74, 4, 110, 178, 182, 132, 179, 10)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__5 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__6;
static const lean_string_object l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "True"};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__7 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__7_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__7_value),LEAN_SCALAR_PTR_LITERAL(78, 21, 103, 131, 118, 13, 187, 164)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__8 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__8_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__9;
static const lean_string_object l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "eq_true_of_isValid"};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__10 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__10_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__11_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(238, 85, 239, 193, 128, 115, 38, 143)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__11_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(135, 17, 186, 49, 10, 156, 173, 153)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__11_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__11_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 198, 254, 91, 59, 223, 24, 67)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__11_value_aux_3),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__10_value),LEAN_SCALAR_PTR_LITERAL(6, 247, 73, 180, 116, 203, 39, 172)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__11 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__11_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__12;
static const lean_string_object l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "False"};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__13 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__13_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__13_value),LEAN_SCALAR_PTR_LITERAL(227, 122, 176, 177, 50, 175, 152, 12)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__14 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__14_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__15;
static const lean_string_object l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "eq_false_of_isUnsat"};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__16 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__16_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__17_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(238, 85, 239, 193, 128, 115, 38, 143)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__17_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(135, 17, 186, 49, 10, 156, 173, 153)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__17_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__17_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 198, 254, 91, 59, 223, 24, 67)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__17_value_aux_3),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__16_value),LEAN_SCALAR_PTR_LITERAL(77, 19, 233, 249, 61, 124, 14, 24)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__17 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__17_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__18;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__0_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trans"};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(157, 40, 198, 234, 16, 168, 79, 243)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__2 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__3;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__4;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__5;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__6;
static const lean_string_object l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Not"};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__7 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__7_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__7_value),LEAN_SCALAR_PTR_LITERAL(185, 11, 203, 55, 27, 192, 137, 230)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__8 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__8_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "GT"};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__9 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__9_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "gt"};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__10 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__10_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__9_value),LEAN_SCALAR_PTR_LITERAL(240, 16, 15, 58, 66, 186, 138, 31)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__11_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__10_value),LEAN_SCALAR_PTR_LITERAL(239, 75, 137, 103, 59, 22, 209, 130)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__11 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__11_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LT"};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__12 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__12_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "lt"};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__13 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__13_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__12_value),LEAN_SCALAR_PTR_LITERAL(71, 235, 154, 184, 62, 135, 30, 248)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__14_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__13_value),LEAN_SCALAR_PTR_LITERAL(54, 235, 251, 9, 4, 74, 57, 164)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__14 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__14_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "GE"};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__15 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__15_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ge"};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__16 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__16_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__15_value),LEAN_SCALAR_PTR_LITERAL(74, 169, 4, 72, 62, 21, 91, 24)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__17_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__16_value),LEAN_SCALAR_PTR_LITERAL(71, 88, 92, 156, 129, 215, 23, 77)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__17 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__17_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LE"};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__18 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__18_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "le"};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__19 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__19_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__18_value),LEAN_SCALAR_PTR_LITERAL(216, 149, 183, 186, 191, 145, 216, 115)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__20_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__19_value),LEAN_SCALAR_PTR_LITERAL(109, 14, 90, 172, 72, 170, 136, 101)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__20 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__20_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__21 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__21_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__22;
static const lean_string_object l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "not_le_eq"};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__23 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__23_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__24_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__24_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__23_value),LEAN_SCALAR_PTR_LITERAL(235, 23, 140, 144, 182, 73, 3, 60)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__24 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__24_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__25;
static const lean_string_object l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "not_ge_eq"};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__26 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__26_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__27_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__26_value),LEAN_SCALAR_PTR_LITERAL(97, 140, 123, 40, 7, 240, 190, 222)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__27 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__27_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__28;
static const lean_string_object l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "not_lt_eq"};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__29 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__29_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__30_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__30_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__29_value),LEAN_SCALAR_PTR_LITERAL(56, 71, 201, 56, 159, 252, 59, 165)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__30 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__30_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__31;
static const lean_string_object l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "not_gt_eq"};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__32 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__32_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__33_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__33_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__32_value),LEAN_SCALAR_PTR_LITERAL(68, 201, 255, 11, 36, 61, 95, 200)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__33 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__33_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__34;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Expr"};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(238, 85, 239, 193, 128, 115, 38, 143)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(135, 17, 186, 49, 10, 156, 173, 153)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(169, 249, 49, 128, 149, 247, 152, 46)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___closed__1_value_aux_3),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(235, 215, 43, 41, 40, 186, 87, 151)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__6(void){
_start:
{
lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; 
v___x_12_ = lean_box(0);
v___x_13_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__5));
v___x_14_ = l_Lean_mkConst(v___x_13_, v___x_12_);
return v___x_14_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__9(void){
_start:
{
lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; 
v___x_18_ = lean_box(0);
v___x_19_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__8));
v___x_20_ = l_Lean_mkConst(v___x_19_, v___x_18_);
return v___x_20_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__12(void){
_start:
{
lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; 
v___x_28_ = lean_box(0);
v___x_29_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__11));
v___x_30_ = l_Lean_mkConst(v___x_29_, v___x_28_);
return v___x_30_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__15(void){
_start:
{
lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; 
v___x_34_ = lean_box(0);
v___x_35_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__14));
v___x_36_ = l_Lean_mkConst(v___x_35_, v___x_34_);
return v___x_36_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__18(void){
_start:
{
lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; 
v___x_44_ = lean_box(0);
v___x_45_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__17));
v___x_46_ = l_Lean_mkConst(v___x_45_, v___x_44_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f(lean_object* v_e_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_, lean_object* v_a_51_){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = l_Lean_Meta_Simp_Arith_Nat_toLinearCnstr_x3f(v_e_47_, v_a_48_, v_a_49_, v_a_50_, v_a_51_);
if (lean_obj_tag(v___x_53_) == 0)
{
lean_object* v_a_54_; lean_object* v___x_56_; uint8_t v_isShared_57_; uint8_t v_isSharedCheck_198_; 
v_a_54_ = lean_ctor_get(v___x_53_, 0);
v_isSharedCheck_198_ = !lean_is_exclusive(v___x_53_);
if (v_isSharedCheck_198_ == 0)
{
v___x_56_ = v___x_53_;
v_isShared_57_ = v_isSharedCheck_198_;
goto v_resetjp_55_;
}
else
{
lean_inc(v_a_54_);
lean_dec(v___x_53_);
v___x_56_ = lean_box(0);
v_isShared_57_ = v_isSharedCheck_198_;
goto v_resetjp_55_;
}
v_resetjp_55_:
{
if (lean_obj_tag(v_a_54_) == 1)
{
lean_object* v_val_58_; lean_object* v___x_60_; uint8_t v_isShared_61_; uint8_t v_isSharedCheck_193_; 
lean_del_object(v___x_56_);
v_val_58_ = lean_ctor_get(v_a_54_, 0);
v_isSharedCheck_193_ = !lean_is_exclusive(v_a_54_);
if (v_isSharedCheck_193_ == 0)
{
v___x_60_ = v_a_54_;
v_isShared_61_ = v_isSharedCheck_193_;
goto v_resetjp_59_;
}
else
{
lean_inc(v_val_58_);
lean_dec(v_a_54_);
v___x_60_ = lean_box(0);
v_isShared_61_ = v_isSharedCheck_193_;
goto v_resetjp_59_;
}
v_resetjp_59_:
{
lean_object* v_fst_62_; lean_object* v_snd_63_; lean_object* v___x_65_; uint8_t v_isShared_66_; uint8_t v_isSharedCheck_192_; 
v_fst_62_ = lean_ctor_get(v_val_58_, 0);
v_snd_63_ = lean_ctor_get(v_val_58_, 1);
v_isSharedCheck_192_ = !lean_is_exclusive(v_val_58_);
if (v_isSharedCheck_192_ == 0)
{
v___x_65_ = v_val_58_;
v_isShared_66_ = v_isSharedCheck_192_;
goto v_resetjp_64_;
}
else
{
lean_inc(v_snd_63_);
lean_inc(v_fst_62_);
lean_dec(v_val_58_);
v___x_65_ = lean_box(0);
v_isShared_66_ = v_isSharedCheck_192_;
goto v_resetjp_64_;
}
v_resetjp_64_:
{
lean_object* v___x_67_; 
lean_inc(v_fst_62_);
v___x_67_ = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith___redArg(v_snd_63_, v_fst_62_);
if (lean_obj_tag(v___x_67_) == 0)
{
lean_object* v_a_68_; lean_object* v___x_69_; lean_object* v___x_70_; uint8_t v___x_71_; 
v_a_68_ = lean_ctor_get(v___x_67_, 0);
lean_inc(v_a_68_);
lean_dec_ref_known(v___x_67_, 1);
lean_inc(v_fst_62_);
v___x_69_ = l_Nat_Internal_Linear_ExprCnstr_toPoly(v_fst_62_);
v___x_70_ = l_Nat_Internal_Linear_PolyCnstr_norm(v___x_69_);
v___x_71_ = l_Nat_Internal_Linear_PolyCnstr_isUnsat(v___x_70_);
if (v___x_71_ == 0)
{
uint8_t v___x_72_; 
v___x_72_ = l_Nat_Internal_Linear_PolyCnstr_isValid(v___x_70_);
if (v___x_72_ == 0)
{
lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_73_ = l_Nat_Internal_Linear_PolyCnstr_toExpr(v___x_70_);
lean_inc_ref(v___x_73_);
v___x_74_ = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith___redArg(v_snd_63_, v___x_73_);
if (lean_obj_tag(v___x_74_) == 0)
{
lean_object* v_a_75_; lean_object* v___x_77_; uint8_t v_isShared_78_; uint8_t v_isSharedCheck_115_; 
v_a_75_ = lean_ctor_get(v___x_74_, 0);
v_isSharedCheck_115_ = !lean_is_exclusive(v___x_74_);
if (v_isSharedCheck_115_ == 0)
{
v___x_77_ = v___x_74_;
v_isShared_78_ = v_isSharedCheck_115_;
goto v_resetjp_76_;
}
else
{
lean_inc(v_a_75_);
lean_dec(v___x_74_);
v___x_77_ = lean_box(0);
v_isShared_78_ = v_isSharedCheck_115_;
goto v_resetjp_76_;
}
v_resetjp_76_:
{
uint8_t v___x_110_; 
v___x_110_ = lean_expr_eqv(v_a_75_, v_a_68_);
if (v___x_110_ == 0)
{
lean_del_object(v___x_77_);
goto v___jp_79_;
}
else
{
if (v___x_72_ == 0)
{
lean_object* v___x_111_; lean_object* v___x_113_; 
lean_dec(v_a_75_);
lean_dec_ref(v___x_73_);
lean_dec(v_a_68_);
lean_del_object(v___x_65_);
lean_dec(v_snd_63_);
lean_dec(v_fst_62_);
lean_del_object(v___x_60_);
v___x_111_ = lean_box(0);
if (v_isShared_78_ == 0)
{
lean_ctor_set(v___x_77_, 0, v___x_111_);
v___x_113_ = v___x_77_;
goto v_reusejp_112_;
}
else
{
lean_object* v_reuseFailAlloc_114_; 
v_reuseFailAlloc_114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_114_, 0, v___x_111_);
v___x_113_ = v_reuseFailAlloc_114_;
goto v_reusejp_112_;
}
v_reusejp_112_:
{
return v___x_113_;
}
}
else
{
lean_del_object(v___x_77_);
goto v___jp_79_;
}
}
v___jp_79_:
{
lean_object* v___x_80_; 
v___x_80_ = l_Lean_Meta_Simp_Arith_Nat_toContextExpr(v_snd_63_, v_a_48_, v_a_49_, v_a_50_, v_a_51_);
if (lean_obj_tag(v___x_80_) == 0)
{
lean_object* v_a_81_; lean_object* v___x_83_; uint8_t v_isShared_84_; uint8_t v_isSharedCheck_101_; 
v_a_81_ = lean_ctor_get(v___x_80_, 0);
v_isSharedCheck_101_ = !lean_is_exclusive(v___x_80_);
if (v_isSharedCheck_101_ == 0)
{
v___x_83_ = v___x_80_;
v_isShared_84_ = v_isSharedCheck_101_;
goto v_resetjp_82_;
}
else
{
lean_inc(v_a_81_);
lean_dec(v___x_80_);
v___x_83_ = lean_box(0);
v_isShared_84_ = v_isSharedCheck_101_;
goto v_resetjp_82_;
}
v_resetjp_82_:
{
lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_93_; 
v___x_85_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__6, &l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__6_once, _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__6);
v___x_86_ = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr(v_fst_62_);
v___x_87_ = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr(v___x_73_);
v___x_88_ = l_Lean_eagerReflBoolTrue;
v___x_89_ = l_Lean_mkApp4(v___x_85_, v_a_81_, v___x_86_, v___x_87_, v___x_88_);
lean_inc(v_a_75_);
v___x_90_ = l_Lean_mkPropEq(v_a_68_, v_a_75_);
v___x_91_ = l_Lean_Meta_mkExpectedPropHint(v___x_89_, v___x_90_);
if (v_isShared_66_ == 0)
{
lean_ctor_set(v___x_65_, 1, v___x_91_);
lean_ctor_set(v___x_65_, 0, v_a_75_);
v___x_93_ = v___x_65_;
goto v_reusejp_92_;
}
else
{
lean_object* v_reuseFailAlloc_100_; 
v_reuseFailAlloc_100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_100_, 0, v_a_75_);
lean_ctor_set(v_reuseFailAlloc_100_, 1, v___x_91_);
v___x_93_ = v_reuseFailAlloc_100_;
goto v_reusejp_92_;
}
v_reusejp_92_:
{
lean_object* v___x_95_; 
if (v_isShared_61_ == 0)
{
lean_ctor_set(v___x_60_, 0, v___x_93_);
v___x_95_ = v___x_60_;
goto v_reusejp_94_;
}
else
{
lean_object* v_reuseFailAlloc_99_; 
v_reuseFailAlloc_99_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_99_, 0, v___x_93_);
v___x_95_ = v_reuseFailAlloc_99_;
goto v_reusejp_94_;
}
v_reusejp_94_:
{
lean_object* v___x_97_; 
if (v_isShared_84_ == 0)
{
lean_ctor_set(v___x_83_, 0, v___x_95_);
v___x_97_ = v___x_83_;
goto v_reusejp_96_;
}
else
{
lean_object* v_reuseFailAlloc_98_; 
v_reuseFailAlloc_98_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_98_, 0, v___x_95_);
v___x_97_ = v_reuseFailAlloc_98_;
goto v_reusejp_96_;
}
v_reusejp_96_:
{
return v___x_97_;
}
}
}
}
}
else
{
lean_object* v_a_102_; lean_object* v___x_104_; uint8_t v_isShared_105_; uint8_t v_isSharedCheck_109_; 
lean_dec(v_a_75_);
lean_dec_ref(v___x_73_);
lean_dec(v_a_68_);
lean_del_object(v___x_65_);
lean_dec(v_fst_62_);
lean_del_object(v___x_60_);
v_a_102_ = lean_ctor_get(v___x_80_, 0);
v_isSharedCheck_109_ = !lean_is_exclusive(v___x_80_);
if (v_isSharedCheck_109_ == 0)
{
v___x_104_ = v___x_80_;
v_isShared_105_ = v_isSharedCheck_109_;
goto v_resetjp_103_;
}
else
{
lean_inc(v_a_102_);
lean_dec(v___x_80_);
v___x_104_ = lean_box(0);
v_isShared_105_ = v_isSharedCheck_109_;
goto v_resetjp_103_;
}
v_resetjp_103_:
{
lean_object* v___x_107_; 
if (v_isShared_105_ == 0)
{
v___x_107_ = v___x_104_;
goto v_reusejp_106_;
}
else
{
lean_object* v_reuseFailAlloc_108_; 
v_reuseFailAlloc_108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_108_, 0, v_a_102_);
v___x_107_ = v_reuseFailAlloc_108_;
goto v_reusejp_106_;
}
v_reusejp_106_:
{
return v___x_107_;
}
}
}
}
}
}
else
{
lean_object* v_a_116_; lean_object* v___x_118_; uint8_t v_isShared_119_; uint8_t v_isSharedCheck_123_; 
lean_dec_ref(v___x_73_);
lean_dec(v_a_68_);
lean_del_object(v___x_65_);
lean_dec(v_snd_63_);
lean_dec(v_fst_62_);
lean_del_object(v___x_60_);
v_a_116_ = lean_ctor_get(v___x_74_, 0);
v_isSharedCheck_123_ = !lean_is_exclusive(v___x_74_);
if (v_isSharedCheck_123_ == 0)
{
v___x_118_ = v___x_74_;
v_isShared_119_ = v_isSharedCheck_123_;
goto v_resetjp_117_;
}
else
{
lean_inc(v_a_116_);
lean_dec(v___x_74_);
v___x_118_ = lean_box(0);
v_isShared_119_ = v_isSharedCheck_123_;
goto v_resetjp_117_;
}
v_resetjp_117_:
{
lean_object* v___x_121_; 
if (v_isShared_119_ == 0)
{
v___x_121_ = v___x_118_;
goto v_reusejp_120_;
}
else
{
lean_object* v_reuseFailAlloc_122_; 
v_reuseFailAlloc_122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_122_, 0, v_a_116_);
v___x_121_ = v_reuseFailAlloc_122_;
goto v_reusejp_120_;
}
v_reusejp_120_:
{
return v___x_121_;
}
}
}
}
else
{
lean_object* v___x_124_; 
lean_dec_ref(v___x_70_);
v___x_124_ = l_Lean_Meta_Simp_Arith_Nat_toContextExpr(v_snd_63_, v_a_48_, v_a_49_, v_a_50_, v_a_51_);
if (lean_obj_tag(v___x_124_) == 0)
{
lean_object* v_a_125_; lean_object* v___x_127_; uint8_t v_isShared_128_; uint8_t v_isSharedCheck_145_; 
v_a_125_ = lean_ctor_get(v___x_124_, 0);
v_isSharedCheck_145_ = !lean_is_exclusive(v___x_124_);
if (v_isSharedCheck_145_ == 0)
{
v___x_127_ = v___x_124_;
v_isShared_128_ = v_isSharedCheck_145_;
goto v_resetjp_126_;
}
else
{
lean_inc(v_a_125_);
lean_dec(v___x_124_);
v___x_127_ = lean_box(0);
v_isShared_128_ = v_isSharedCheck_145_;
goto v_resetjp_126_;
}
v_resetjp_126_:
{
lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_137_; 
v___x_129_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__9, &l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__9_once, _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__9);
v___x_130_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__12, &l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__12_once, _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__12);
v___x_131_ = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr(v_fst_62_);
v___x_132_ = l_Lean_eagerReflBoolTrue;
v___x_133_ = l_Lean_mkApp3(v___x_130_, v_a_125_, v___x_131_, v___x_132_);
v___x_134_ = l_Lean_mkPropEq(v_a_68_, v___x_129_);
v___x_135_ = l_Lean_Meta_mkExpectedPropHint(v___x_133_, v___x_134_);
if (v_isShared_66_ == 0)
{
lean_ctor_set(v___x_65_, 1, v___x_135_);
lean_ctor_set(v___x_65_, 0, v___x_129_);
v___x_137_ = v___x_65_;
goto v_reusejp_136_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v___x_129_);
lean_ctor_set(v_reuseFailAlloc_144_, 1, v___x_135_);
v___x_137_ = v_reuseFailAlloc_144_;
goto v_reusejp_136_;
}
v_reusejp_136_:
{
lean_object* v___x_139_; 
if (v_isShared_61_ == 0)
{
lean_ctor_set(v___x_60_, 0, v___x_137_);
v___x_139_ = v___x_60_;
goto v_reusejp_138_;
}
else
{
lean_object* v_reuseFailAlloc_143_; 
v_reuseFailAlloc_143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_143_, 0, v___x_137_);
v___x_139_ = v_reuseFailAlloc_143_;
goto v_reusejp_138_;
}
v_reusejp_138_:
{
lean_object* v___x_141_; 
if (v_isShared_128_ == 0)
{
lean_ctor_set(v___x_127_, 0, v___x_139_);
v___x_141_ = v___x_127_;
goto v_reusejp_140_;
}
else
{
lean_object* v_reuseFailAlloc_142_; 
v_reuseFailAlloc_142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_142_, 0, v___x_139_);
v___x_141_ = v_reuseFailAlloc_142_;
goto v_reusejp_140_;
}
v_reusejp_140_:
{
return v___x_141_;
}
}
}
}
}
else
{
lean_object* v_a_146_; lean_object* v___x_148_; uint8_t v_isShared_149_; uint8_t v_isSharedCheck_153_; 
lean_dec(v_a_68_);
lean_del_object(v___x_65_);
lean_dec(v_fst_62_);
lean_del_object(v___x_60_);
v_a_146_ = lean_ctor_get(v___x_124_, 0);
v_isSharedCheck_153_ = !lean_is_exclusive(v___x_124_);
if (v_isSharedCheck_153_ == 0)
{
v___x_148_ = v___x_124_;
v_isShared_149_ = v_isSharedCheck_153_;
goto v_resetjp_147_;
}
else
{
lean_inc(v_a_146_);
lean_dec(v___x_124_);
v___x_148_ = lean_box(0);
v_isShared_149_ = v_isSharedCheck_153_;
goto v_resetjp_147_;
}
v_resetjp_147_:
{
lean_object* v___x_151_; 
if (v_isShared_149_ == 0)
{
v___x_151_ = v___x_148_;
goto v_reusejp_150_;
}
else
{
lean_object* v_reuseFailAlloc_152_; 
v_reuseFailAlloc_152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_152_, 0, v_a_146_);
v___x_151_ = v_reuseFailAlloc_152_;
goto v_reusejp_150_;
}
v_reusejp_150_:
{
return v___x_151_;
}
}
}
}
}
else
{
lean_object* v___x_154_; 
lean_dec_ref(v___x_70_);
v___x_154_ = l_Lean_Meta_Simp_Arith_Nat_toContextExpr(v_snd_63_, v_a_48_, v_a_49_, v_a_50_, v_a_51_);
if (lean_obj_tag(v___x_154_) == 0)
{
lean_object* v_a_155_; lean_object* v___x_157_; uint8_t v_isShared_158_; uint8_t v_isSharedCheck_175_; 
v_a_155_ = lean_ctor_get(v___x_154_, 0);
v_isSharedCheck_175_ = !lean_is_exclusive(v___x_154_);
if (v_isSharedCheck_175_ == 0)
{
v___x_157_ = v___x_154_;
v_isShared_158_ = v_isSharedCheck_175_;
goto v_resetjp_156_;
}
else
{
lean_inc(v_a_155_);
lean_dec(v___x_154_);
v___x_157_ = lean_box(0);
v_isShared_158_ = v_isSharedCheck_175_;
goto v_resetjp_156_;
}
v_resetjp_156_:
{
lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_167_; 
v___x_159_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__15, &l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__15_once, _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__15);
v___x_160_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__18, &l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__18_once, _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__18);
v___x_161_ = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr(v_fst_62_);
v___x_162_ = l_Lean_eagerReflBoolTrue;
v___x_163_ = l_Lean_mkApp3(v___x_160_, v_a_155_, v___x_161_, v___x_162_);
v___x_164_ = l_Lean_mkPropEq(v_a_68_, v___x_159_);
v___x_165_ = l_Lean_Meta_mkExpectedPropHint(v___x_163_, v___x_164_);
if (v_isShared_66_ == 0)
{
lean_ctor_set(v___x_65_, 1, v___x_165_);
lean_ctor_set(v___x_65_, 0, v___x_159_);
v___x_167_ = v___x_65_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_174_; 
v_reuseFailAlloc_174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_174_, 0, v___x_159_);
lean_ctor_set(v_reuseFailAlloc_174_, 1, v___x_165_);
v___x_167_ = v_reuseFailAlloc_174_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
lean_object* v___x_169_; 
if (v_isShared_61_ == 0)
{
lean_ctor_set(v___x_60_, 0, v___x_167_);
v___x_169_ = v___x_60_;
goto v_reusejp_168_;
}
else
{
lean_object* v_reuseFailAlloc_173_; 
v_reuseFailAlloc_173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_173_, 0, v___x_167_);
v___x_169_ = v_reuseFailAlloc_173_;
goto v_reusejp_168_;
}
v_reusejp_168_:
{
lean_object* v___x_171_; 
if (v_isShared_158_ == 0)
{
lean_ctor_set(v___x_157_, 0, v___x_169_);
v___x_171_ = v___x_157_;
goto v_reusejp_170_;
}
else
{
lean_object* v_reuseFailAlloc_172_; 
v_reuseFailAlloc_172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_172_, 0, v___x_169_);
v___x_171_ = v_reuseFailAlloc_172_;
goto v_reusejp_170_;
}
v_reusejp_170_:
{
return v___x_171_;
}
}
}
}
}
else
{
lean_object* v_a_176_; lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_183_; 
lean_dec(v_a_68_);
lean_del_object(v___x_65_);
lean_dec(v_fst_62_);
lean_del_object(v___x_60_);
v_a_176_ = lean_ctor_get(v___x_154_, 0);
v_isSharedCheck_183_ = !lean_is_exclusive(v___x_154_);
if (v_isSharedCheck_183_ == 0)
{
v___x_178_ = v___x_154_;
v_isShared_179_ = v_isSharedCheck_183_;
goto v_resetjp_177_;
}
else
{
lean_inc(v_a_176_);
lean_dec(v___x_154_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_183_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
lean_object* v___x_181_; 
if (v_isShared_179_ == 0)
{
v___x_181_ = v___x_178_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_182_; 
v_reuseFailAlloc_182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_182_, 0, v_a_176_);
v___x_181_ = v_reuseFailAlloc_182_;
goto v_reusejp_180_;
}
v_reusejp_180_:
{
return v___x_181_;
}
}
}
}
}
else
{
lean_object* v_a_184_; lean_object* v___x_186_; uint8_t v_isShared_187_; uint8_t v_isSharedCheck_191_; 
lean_del_object(v___x_65_);
lean_dec(v_snd_63_);
lean_dec(v_fst_62_);
lean_del_object(v___x_60_);
v_a_184_ = lean_ctor_get(v___x_67_, 0);
v_isSharedCheck_191_ = !lean_is_exclusive(v___x_67_);
if (v_isSharedCheck_191_ == 0)
{
v___x_186_ = v___x_67_;
v_isShared_187_ = v_isSharedCheck_191_;
goto v_resetjp_185_;
}
else
{
lean_inc(v_a_184_);
lean_dec(v___x_67_);
v___x_186_ = lean_box(0);
v_isShared_187_ = v_isSharedCheck_191_;
goto v_resetjp_185_;
}
v_resetjp_185_:
{
lean_object* v___x_189_; 
if (v_isShared_187_ == 0)
{
v___x_189_ = v___x_186_;
goto v_reusejp_188_;
}
else
{
lean_object* v_reuseFailAlloc_190_; 
v_reuseFailAlloc_190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_190_, 0, v_a_184_);
v___x_189_ = v_reuseFailAlloc_190_;
goto v_reusejp_188_;
}
v_reusejp_188_:
{
return v___x_189_;
}
}
}
}
}
}
else
{
lean_object* v___x_194_; lean_object* v___x_196_; 
lean_dec(v_a_54_);
v___x_194_ = lean_box(0);
if (v_isShared_57_ == 0)
{
lean_ctor_set(v___x_56_, 0, v___x_194_);
v___x_196_ = v___x_56_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_197_; 
v_reuseFailAlloc_197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_197_, 0, v___x_194_);
v___x_196_ = v_reuseFailAlloc_197_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
return v___x_196_;
}
}
}
}
else
{
lean_object* v_a_199_; lean_object* v___x_201_; uint8_t v_isShared_202_; uint8_t v_isSharedCheck_206_; 
v_a_199_ = lean_ctor_get(v___x_53_, 0);
v_isSharedCheck_206_ = !lean_is_exclusive(v___x_53_);
if (v_isSharedCheck_206_ == 0)
{
v___x_201_ = v___x_53_;
v_isShared_202_ = v_isSharedCheck_206_;
goto v_resetjp_200_;
}
else
{
lean_inc(v_a_199_);
lean_dec(v___x_53_);
v___x_201_ = lean_box(0);
v_isShared_202_ = v_isSharedCheck_206_;
goto v_resetjp_200_;
}
v_resetjp_200_:
{
lean_object* v___x_204_; 
if (v_isShared_202_ == 0)
{
v___x_204_ = v___x_201_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v_a_199_);
v___x_204_ = v_reuseFailAlloc_205_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
return v___x_204_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___boxed(lean_object* v_e_207_, lean_object* v_a_208_, lean_object* v_a_209_, lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_){
_start:
{
lean_object* v_res_213_; 
v_res_213_ = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f(v_e_207_, v_a_208_, v_a_209_, v_a_210_, v_a_211_);
lean_dec(v_a_211_);
lean_dec_ref(v_a_210_);
lean_dec(v_a_209_);
lean_dec_ref(v_a_208_);
return v_res_213_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__3(void){
_start:
{
lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_219_ = lean_box(0);
v___x_220_ = l_Lean_Level_succ___override(v___x_219_);
return v___x_220_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__4(void){
_start:
{
lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_221_ = lean_box(0);
v___x_222_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__3, &l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__3_once, _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__3);
v___x_223_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_223_, 0, v___x_222_);
lean_ctor_set(v___x_223_, 1, v___x_221_);
return v___x_223_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__5(void){
_start:
{
lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_224_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__4, &l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__4_once, _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__4);
v___x_225_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__2));
v___x_226_ = l_Lean_mkConst(v___x_225_, v___x_224_);
return v___x_226_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__6(void){
_start:
{
lean_object* v___x_227_; lean_object* v___x_228_; 
v___x_227_ = lean_box(0);
v___x_228_ = l_Lean_mkSort(v___x_227_);
return v___x_228_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__22(void){
_start:
{
lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_254_ = lean_unsigned_to_nat(1u);
v___x_255_ = l_Lean_mkNatLit(v___x_254_);
return v___x_255_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__25(void){
_start:
{
lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; 
v___x_260_ = lean_box(0);
v___x_261_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__24));
v___x_262_ = l_Lean_mkConst(v___x_261_, v___x_260_);
return v___x_262_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__28(void){
_start:
{
lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; 
v___x_267_ = lean_box(0);
v___x_268_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__27));
v___x_269_ = l_Lean_mkConst(v___x_268_, v___x_267_);
return v___x_269_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__31(void){
_start:
{
lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_274_ = lean_box(0);
v___x_275_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__30));
v___x_276_ = l_Lean_mkConst(v___x_275_, v___x_274_);
return v___x_276_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__34(void){
_start:
{
lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_281_ = lean_box(0);
v___x_282_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__33));
v___x_283_ = l_Lean_mkConst(v___x_282_, v___x_281_);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f(lean_object* v_e_284_, lean_object* v_a_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_){
_start:
{
lean_object* v_val_294_; lean_object* v_h_u2081_295_; lean_object* v___y_296_; lean_object* v___y_297_; lean_object* v___y_298_; lean_object* v___y_299_; lean_object* v___x_334_; lean_object* v___x_335_; uint8_t v___x_336_; 
v___x_334_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__8));
v___x_335_ = lean_unsigned_to_nat(1u);
v___x_336_ = l_Lean_Expr_isAppOfArity(v_e_284_, v___x_334_, v___x_335_);
if (v___x_336_ == 0)
{
lean_object* v___x_337_; 
v___x_337_ = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f(v_e_284_, v_a_285_, v_a_286_, v_a_287_, v_a_288_);
return v___x_337_;
}
else
{
lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_338_ = l_Lean_Expr_appArg_x21(v_e_284_);
v___x_339_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v___x_338_, v_a_286_);
if (lean_obj_tag(v___x_339_) == 0)
{
lean_object* v_a_340_; lean_object* v___x_341_; uint8_t v___x_342_; 
v_a_340_ = lean_ctor_get(v___x_339_, 0);
lean_inc(v_a_340_);
lean_dec_ref_known(v___x_339_, 1);
v___x_341_ = l_Lean_Expr_cleanupAnnotations(v_a_340_);
v___x_342_ = l_Lean_Expr_isApp(v___x_341_);
if (v___x_342_ == 0)
{
lean_dec_ref(v___x_341_);
lean_dec_ref(v_e_284_);
goto v___jp_290_;
}
else
{
lean_object* v_arg_343_; lean_object* v___x_344_; uint8_t v___x_345_; 
v_arg_343_ = lean_ctor_get(v___x_341_, 1);
lean_inc_ref(v_arg_343_);
v___x_344_ = l_Lean_Expr_appFnCleanup___redArg(v___x_341_);
v___x_345_ = l_Lean_Expr_isApp(v___x_344_);
if (v___x_345_ == 0)
{
lean_dec_ref(v___x_344_);
lean_dec_ref(v_arg_343_);
lean_dec_ref(v_e_284_);
goto v___jp_290_;
}
else
{
lean_object* v_arg_346_; lean_object* v___x_347_; uint8_t v___x_348_; 
v_arg_346_ = lean_ctor_get(v___x_344_, 1);
lean_inc_ref(v_arg_346_);
v___x_347_ = l_Lean_Expr_appFnCleanup___redArg(v___x_344_);
v___x_348_ = l_Lean_Expr_isApp(v___x_347_);
if (v___x_348_ == 0)
{
lean_dec_ref(v___x_347_);
lean_dec_ref(v_arg_346_);
lean_dec_ref(v_arg_343_);
lean_dec_ref(v_e_284_);
goto v___jp_290_;
}
else
{
lean_object* v___x_349_; uint8_t v___x_350_; 
v___x_349_ = l_Lean_Expr_appFnCleanup___redArg(v___x_347_);
v___x_350_ = l_Lean_Expr_isApp(v___x_349_);
if (v___x_350_ == 0)
{
lean_dec_ref(v___x_349_);
lean_dec_ref(v_arg_346_);
lean_dec_ref(v_arg_343_);
lean_dec_ref(v_e_284_);
goto v___jp_290_;
}
else
{
lean_object* v_arg_351_; lean_object* v___x_352_; lean_object* v___x_353_; uint8_t v___x_354_; 
v_arg_351_ = lean_ctor_get(v___x_349_, 1);
lean_inc_ref(v_arg_351_);
v___x_352_ = l_Lean_Expr_appFnCleanup___redArg(v___x_349_);
v___x_353_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__11));
v___x_354_ = l_Lean_Expr_isConstOf(v___x_352_, v___x_353_);
if (v___x_354_ == 0)
{
lean_object* v___x_355_; uint8_t v___x_356_; 
v___x_355_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__14));
v___x_356_ = l_Lean_Expr_isConstOf(v___x_352_, v___x_355_);
if (v___x_356_ == 0)
{
lean_object* v___x_357_; uint8_t v___x_358_; 
v___x_357_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__17));
v___x_358_ = l_Lean_Expr_isConstOf(v___x_352_, v___x_357_);
if (v___x_358_ == 0)
{
lean_object* v___x_359_; uint8_t v___x_360_; 
v___x_359_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__20));
v___x_360_ = l_Lean_Expr_isConstOf(v___x_352_, v___x_359_);
lean_dec_ref(v___x_352_);
if (v___x_360_ == 0)
{
lean_dec_ref(v_arg_351_);
lean_dec_ref(v_arg_346_);
lean_dec_ref(v_arg_343_);
lean_dec_ref(v_e_284_);
goto v___jp_290_;
}
else
{
lean_object* v___x_361_; 
v___x_361_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_351_, v_a_286_);
if (lean_obj_tag(v___x_361_) == 0)
{
lean_object* v_a_362_; lean_object* v___x_363_; lean_object* v___x_364_; uint8_t v___x_365_; 
v_a_362_ = lean_ctor_get(v___x_361_, 0);
lean_inc(v_a_362_);
lean_dec_ref_known(v___x_361_, 1);
v___x_363_ = l_Lean_Expr_cleanupAnnotations(v_a_362_);
v___x_364_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__21));
v___x_365_ = l_Lean_Expr_isConstOf(v___x_363_, v___x_364_);
lean_dec_ref(v___x_363_);
if (v___x_365_ == 0)
{
lean_dec_ref(v_arg_346_);
lean_dec_ref(v_arg_343_);
lean_dec_ref(v_e_284_);
goto v___jp_290_;
}
else
{
lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_366_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__22, &l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__22_once, _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__22);
lean_inc_ref(v_arg_343_);
v___x_367_ = l_Lean_mkNatAdd(v_arg_343_, v___x_366_);
lean_inc_ref(v_arg_346_);
v___x_368_ = l_Lean_mkNatLE(v___x_367_, v_arg_346_);
v___x_369_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__25, &l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__25_once, _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__25);
v___x_370_ = l_Lean_mkAppB(v___x_369_, v_arg_346_, v_arg_343_);
v_val_294_ = v___x_368_;
v_h_u2081_295_ = v___x_370_;
v___y_296_ = v_a_285_;
v___y_297_ = v_a_286_;
v___y_298_ = v_a_287_;
v___y_299_ = v_a_288_;
goto v___jp_293_;
}
}
else
{
lean_object* v_a_371_; lean_object* v___x_373_; uint8_t v_isShared_374_; uint8_t v_isSharedCheck_378_; 
lean_dec_ref(v_arg_346_);
lean_dec_ref(v_arg_343_);
lean_dec_ref(v_e_284_);
v_a_371_ = lean_ctor_get(v___x_361_, 0);
v_isSharedCheck_378_ = !lean_is_exclusive(v___x_361_);
if (v_isSharedCheck_378_ == 0)
{
v___x_373_ = v___x_361_;
v_isShared_374_ = v_isSharedCheck_378_;
goto v_resetjp_372_;
}
else
{
lean_inc(v_a_371_);
lean_dec(v___x_361_);
v___x_373_ = lean_box(0);
v_isShared_374_ = v_isSharedCheck_378_;
goto v_resetjp_372_;
}
v_resetjp_372_:
{
lean_object* v___x_376_; 
if (v_isShared_374_ == 0)
{
v___x_376_ = v___x_373_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v_a_371_);
v___x_376_ = v_reuseFailAlloc_377_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
return v___x_376_;
}
}
}
}
}
else
{
lean_object* v___x_379_; 
lean_dec_ref(v___x_352_);
v___x_379_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_351_, v_a_286_);
if (lean_obj_tag(v___x_379_) == 0)
{
lean_object* v_a_380_; lean_object* v___x_381_; lean_object* v___x_382_; uint8_t v___x_383_; 
v_a_380_ = lean_ctor_get(v___x_379_, 0);
lean_inc(v_a_380_);
lean_dec_ref_known(v___x_379_, 1);
v___x_381_ = l_Lean_Expr_cleanupAnnotations(v_a_380_);
v___x_382_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__21));
v___x_383_ = l_Lean_Expr_isConstOf(v___x_381_, v___x_382_);
lean_dec_ref(v___x_381_);
if (v___x_383_ == 0)
{
lean_dec_ref(v_arg_346_);
lean_dec_ref(v_arg_343_);
lean_dec_ref(v_e_284_);
goto v___jp_290_;
}
else
{
lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; 
v___x_384_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__22, &l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__22_once, _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__22);
lean_inc_ref(v_arg_346_);
v___x_385_ = l_Lean_mkNatAdd(v_arg_346_, v___x_384_);
lean_inc_ref(v_arg_343_);
v___x_386_ = l_Lean_mkNatLE(v___x_385_, v_arg_343_);
v___x_387_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__28, &l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__28_once, _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__28);
v___x_388_ = l_Lean_mkAppB(v___x_387_, v_arg_346_, v_arg_343_);
v_val_294_ = v___x_386_;
v_h_u2081_295_ = v___x_388_;
v___y_296_ = v_a_285_;
v___y_297_ = v_a_286_;
v___y_298_ = v_a_287_;
v___y_299_ = v_a_288_;
goto v___jp_293_;
}
}
else
{
lean_object* v_a_389_; lean_object* v___x_391_; uint8_t v_isShared_392_; uint8_t v_isSharedCheck_396_; 
lean_dec_ref(v_arg_346_);
lean_dec_ref(v_arg_343_);
lean_dec_ref(v_e_284_);
v_a_389_ = lean_ctor_get(v___x_379_, 0);
v_isSharedCheck_396_ = !lean_is_exclusive(v___x_379_);
if (v_isSharedCheck_396_ == 0)
{
v___x_391_ = v___x_379_;
v_isShared_392_ = v_isSharedCheck_396_;
goto v_resetjp_390_;
}
else
{
lean_inc(v_a_389_);
lean_dec(v___x_379_);
v___x_391_ = lean_box(0);
v_isShared_392_ = v_isSharedCheck_396_;
goto v_resetjp_390_;
}
v_resetjp_390_:
{
lean_object* v___x_394_; 
if (v_isShared_392_ == 0)
{
v___x_394_ = v___x_391_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v_a_389_);
v___x_394_ = v_reuseFailAlloc_395_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
return v___x_394_;
}
}
}
}
}
else
{
lean_object* v___x_397_; 
lean_dec_ref(v___x_352_);
v___x_397_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_351_, v_a_286_);
if (lean_obj_tag(v___x_397_) == 0)
{
lean_object* v_a_398_; lean_object* v___x_399_; lean_object* v___x_400_; uint8_t v___x_401_; 
v_a_398_ = lean_ctor_get(v___x_397_, 0);
lean_inc(v_a_398_);
lean_dec_ref_known(v___x_397_, 1);
v___x_399_ = l_Lean_Expr_cleanupAnnotations(v_a_398_);
v___x_400_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__21));
v___x_401_ = l_Lean_Expr_isConstOf(v___x_399_, v___x_400_);
lean_dec_ref(v___x_399_);
if (v___x_401_ == 0)
{
lean_dec_ref(v_arg_346_);
lean_dec_ref(v_arg_343_);
lean_dec_ref(v_e_284_);
goto v___jp_290_;
}
else
{
lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; 
lean_inc_ref(v_arg_346_);
lean_inc_ref(v_arg_343_);
v___x_402_ = l_Lean_mkNatLE(v_arg_343_, v_arg_346_);
v___x_403_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__31, &l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__31_once, _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__31);
v___x_404_ = l_Lean_mkAppB(v___x_403_, v_arg_346_, v_arg_343_);
v_val_294_ = v___x_402_;
v_h_u2081_295_ = v___x_404_;
v___y_296_ = v_a_285_;
v___y_297_ = v_a_286_;
v___y_298_ = v_a_287_;
v___y_299_ = v_a_288_;
goto v___jp_293_;
}
}
else
{
lean_object* v_a_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_412_; 
lean_dec_ref(v_arg_346_);
lean_dec_ref(v_arg_343_);
lean_dec_ref(v_e_284_);
v_a_405_ = lean_ctor_get(v___x_397_, 0);
v_isSharedCheck_412_ = !lean_is_exclusive(v___x_397_);
if (v_isSharedCheck_412_ == 0)
{
v___x_407_ = v___x_397_;
v_isShared_408_ = v_isSharedCheck_412_;
goto v_resetjp_406_;
}
else
{
lean_inc(v_a_405_);
lean_dec(v___x_397_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_412_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
lean_object* v___x_410_; 
if (v_isShared_408_ == 0)
{
v___x_410_ = v___x_407_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v_a_405_);
v___x_410_ = v_reuseFailAlloc_411_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
return v___x_410_;
}
}
}
}
}
else
{
lean_object* v___x_413_; 
lean_dec_ref(v___x_352_);
v___x_413_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_351_, v_a_286_);
if (lean_obj_tag(v___x_413_) == 0)
{
lean_object* v_a_414_; lean_object* v___x_415_; lean_object* v___x_416_; uint8_t v___x_417_; 
v_a_414_ = lean_ctor_get(v___x_413_, 0);
lean_inc(v_a_414_);
lean_dec_ref_known(v___x_413_, 1);
v___x_415_ = l_Lean_Expr_cleanupAnnotations(v_a_414_);
v___x_416_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__21));
v___x_417_ = l_Lean_Expr_isConstOf(v___x_415_, v___x_416_);
lean_dec_ref(v___x_415_);
if (v___x_417_ == 0)
{
lean_dec_ref(v_arg_346_);
lean_dec_ref(v_arg_343_);
lean_dec_ref(v_e_284_);
goto v___jp_290_;
}
else
{
lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; 
lean_inc_ref(v_arg_343_);
lean_inc_ref(v_arg_346_);
v___x_418_ = l_Lean_mkNatLE(v_arg_346_, v_arg_343_);
v___x_419_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__34, &l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__34_once, _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__34);
v___x_420_ = l_Lean_mkAppB(v___x_419_, v_arg_346_, v_arg_343_);
v_val_294_ = v___x_418_;
v_h_u2081_295_ = v___x_420_;
v___y_296_ = v_a_285_;
v___y_297_ = v_a_286_;
v___y_298_ = v_a_287_;
v___y_299_ = v_a_288_;
goto v___jp_293_;
}
}
else
{
lean_object* v_a_421_; lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_428_; 
lean_dec_ref(v_arg_346_);
lean_dec_ref(v_arg_343_);
lean_dec_ref(v_e_284_);
v_a_421_ = lean_ctor_get(v___x_413_, 0);
v_isSharedCheck_428_ = !lean_is_exclusive(v___x_413_);
if (v_isSharedCheck_428_ == 0)
{
v___x_423_ = v___x_413_;
v_isShared_424_ = v_isSharedCheck_428_;
goto v_resetjp_422_;
}
else
{
lean_inc(v_a_421_);
lean_dec(v___x_413_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_428_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
lean_object* v___x_426_; 
if (v_isShared_424_ == 0)
{
v___x_426_ = v___x_423_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_427_; 
v_reuseFailAlloc_427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_427_, 0, v_a_421_);
v___x_426_ = v_reuseFailAlloc_427_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
return v___x_426_;
}
}
}
}
}
}
}
}
}
else
{
lean_object* v_a_429_; lean_object* v___x_431_; uint8_t v_isShared_432_; uint8_t v_isSharedCheck_436_; 
lean_dec_ref(v_e_284_);
v_a_429_ = lean_ctor_get(v___x_339_, 0);
v_isSharedCheck_436_ = !lean_is_exclusive(v___x_339_);
if (v_isSharedCheck_436_ == 0)
{
v___x_431_ = v___x_339_;
v_isShared_432_ = v_isSharedCheck_436_;
goto v_resetjp_430_;
}
else
{
lean_inc(v_a_429_);
lean_dec(v___x_339_);
v___x_431_ = lean_box(0);
v_isShared_432_ = v_isSharedCheck_436_;
goto v_resetjp_430_;
}
v_resetjp_430_:
{
lean_object* v___x_434_; 
if (v_isShared_432_ == 0)
{
v___x_434_ = v___x_431_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v_a_429_);
v___x_434_ = v_reuseFailAlloc_435_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
return v___x_434_;
}
}
}
}
v___jp_290_:
{
lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_291_ = lean_box(0);
v___x_292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_292_, 0, v___x_291_);
return v___x_292_;
}
v___jp_293_:
{
lean_object* v___x_300_; 
lean_inc_ref(v_val_294_);
v___x_300_ = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f(v_val_294_, v___y_296_, v___y_297_, v___y_298_, v___y_299_);
if (lean_obj_tag(v___x_300_) == 0)
{
lean_object* v_a_301_; lean_object* v___x_303_; uint8_t v_isShared_304_; uint8_t v_isSharedCheck_333_; 
v_a_301_ = lean_ctor_get(v___x_300_, 0);
v_isSharedCheck_333_ = !lean_is_exclusive(v___x_300_);
if (v_isSharedCheck_333_ == 0)
{
v___x_303_ = v___x_300_;
v_isShared_304_ = v_isSharedCheck_333_;
goto v_resetjp_302_;
}
else
{
lean_inc(v_a_301_);
lean_dec(v___x_300_);
v___x_303_ = lean_box(0);
v_isShared_304_ = v_isSharedCheck_333_;
goto v_resetjp_302_;
}
v_resetjp_302_:
{
if (lean_obj_tag(v_a_301_) == 1)
{
lean_object* v_val_305_; lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_327_; 
v_val_305_ = lean_ctor_get(v_a_301_, 0);
v_isSharedCheck_327_ = !lean_is_exclusive(v_a_301_);
if (v_isSharedCheck_327_ == 0)
{
v___x_307_ = v_a_301_;
v_isShared_308_ = v_isSharedCheck_327_;
goto v_resetjp_306_;
}
else
{
lean_inc(v_val_305_);
lean_dec(v_a_301_);
v___x_307_ = lean_box(0);
v_isShared_308_ = v_isSharedCheck_327_;
goto v_resetjp_306_;
}
v_resetjp_306_:
{
lean_object* v_fst_309_; lean_object* v_snd_310_; lean_object* v___x_312_; uint8_t v_isShared_313_; uint8_t v_isSharedCheck_326_; 
v_fst_309_ = lean_ctor_get(v_val_305_, 0);
v_snd_310_ = lean_ctor_get(v_val_305_, 1);
v_isSharedCheck_326_ = !lean_is_exclusive(v_val_305_);
if (v_isSharedCheck_326_ == 0)
{
v___x_312_ = v_val_305_;
v_isShared_313_ = v_isSharedCheck_326_;
goto v_resetjp_311_;
}
else
{
lean_inc(v_snd_310_);
lean_inc(v_fst_309_);
lean_dec(v_val_305_);
v___x_312_ = lean_box(0);
v_isShared_313_ = v_isSharedCheck_326_;
goto v_resetjp_311_;
}
v_resetjp_311_:
{
lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_318_; 
v___x_314_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__5, &l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__5_once, _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__5);
v___x_315_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__6, &l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__6_once, _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__6);
lean_inc(v_fst_309_);
v___x_316_ = l_Lean_mkApp6(v___x_314_, v___x_315_, v_e_284_, v_val_294_, v_fst_309_, v_h_u2081_295_, v_snd_310_);
if (v_isShared_313_ == 0)
{
lean_ctor_set(v___x_312_, 1, v___x_316_);
v___x_318_ = v___x_312_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v_fst_309_);
lean_ctor_set(v_reuseFailAlloc_325_, 1, v___x_316_);
v___x_318_ = v_reuseFailAlloc_325_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
lean_object* v___x_320_; 
if (v_isShared_308_ == 0)
{
lean_ctor_set(v___x_307_, 0, v___x_318_);
v___x_320_ = v___x_307_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v___x_318_);
v___x_320_ = v_reuseFailAlloc_324_;
goto v_reusejp_319_;
}
v_reusejp_319_:
{
lean_object* v___x_322_; 
if (v_isShared_304_ == 0)
{
lean_ctor_set(v___x_303_, 0, v___x_320_);
v___x_322_ = v___x_303_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v___x_320_);
v___x_322_ = v_reuseFailAlloc_323_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
return v___x_322_;
}
}
}
}
}
}
else
{
lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_331_; 
lean_dec(v_a_301_);
lean_dec_ref(v_e_284_);
v___x_328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_328_, 0, v_val_294_);
lean_ctor_set(v___x_328_, 1, v_h_u2081_295_);
v___x_329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_329_, 0, v___x_328_);
if (v_isShared_304_ == 0)
{
lean_ctor_set(v___x_303_, 0, v___x_329_);
v___x_331_ = v___x_303_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v___x_329_);
v___x_331_ = v_reuseFailAlloc_332_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
return v___x_331_;
}
}
}
}
else
{
lean_dec_ref(v_h_u2081_295_);
lean_dec_ref(v_val_294_);
lean_dec_ref(v_e_284_);
return v___x_300_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___boxed(lean_object* v_e_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_){
_start:
{
lean_object* v_res_443_; 
v_res_443_ = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f(v_e_437_, v_a_438_, v_a_439_, v_a_440_, v_a_441_);
lean_dec(v_a_441_);
lean_dec_ref(v_a_440_);
lean_dec(v_a_439_);
lean_dec_ref(v_a_438_);
return v_res_443_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___closed__2(void){
_start:
{
lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; 
v___x_451_ = lean_box(0);
v___x_452_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___closed__1));
v___x_453_ = l_Lean_mkConst(v___x_452_, v___x_451_);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f(lean_object* v_input_454_, lean_object* v_a_455_, lean_object* v_a_456_, lean_object* v_a_457_, lean_object* v_a_458_){
_start:
{
lean_object* v___x_460_; 
v___x_460_ = l_Lean_Meta_Simp_Arith_Nat_toLinearExpr(v_input_454_, v_a_455_, v_a_456_, v_a_457_, v_a_458_);
if (lean_obj_tag(v___x_460_) == 0)
{
lean_object* v_a_461_; lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_527_; 
v_a_461_ = lean_ctor_get(v___x_460_, 0);
v_isSharedCheck_527_ = !lean_is_exclusive(v___x_460_);
if (v_isSharedCheck_527_ == 0)
{
v___x_463_ = v___x_460_;
v_isShared_464_ = v_isSharedCheck_527_;
goto v_resetjp_462_;
}
else
{
lean_inc(v_a_461_);
lean_dec(v___x_460_);
v___x_463_ = lean_box(0);
v_isShared_464_ = v_isSharedCheck_527_;
goto v_resetjp_462_;
}
v_resetjp_462_:
{
lean_object* v_fst_465_; lean_object* v_snd_466_; lean_object* v___x_468_; uint8_t v_isShared_469_; uint8_t v_isSharedCheck_526_; 
v_fst_465_ = lean_ctor_get(v_a_461_, 0);
v_snd_466_ = lean_ctor_get(v_a_461_, 1);
v_isSharedCheck_526_ = !lean_is_exclusive(v_a_461_);
if (v_isSharedCheck_526_ == 0)
{
v___x_468_ = v_a_461_;
v_isShared_469_ = v_isSharedCheck_526_;
goto v_resetjp_467_;
}
else
{
lean_inc(v_snd_466_);
lean_inc(v_fst_465_);
lean_dec(v_a_461_);
v___x_468_ = lean_box(0);
v_isShared_469_ = v_isSharedCheck_526_;
goto v_resetjp_467_;
}
v_resetjp_467_:
{
lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; uint8_t v___x_473_; 
v___x_470_ = l_Nat_Internal_Linear_Expr_toPoly(v_fst_465_);
v___x_471_ = l_Nat_Internal_Linear_Poly_norm(v___x_470_);
v___x_472_ = l_Nat_Internal_Linear_Poly_toExpr(v___x_471_);
v___x_473_ = l_Nat_Internal_Linear_instBEqExpr_beq(v___x_472_, v_fst_465_);
if (v___x_473_ == 0)
{
lean_object* v___x_474_; 
lean_del_object(v___x_463_);
lean_inc(v_snd_466_);
v___x_474_ = l_Lean_Meta_Simp_Arith_Nat_toContextExpr(v_snd_466_, v_a_455_, v_a_456_, v_a_457_, v_a_458_);
if (lean_obj_tag(v___x_474_) == 0)
{
lean_object* v_a_475_; lean_object* v___x_476_; lean_object* v___x_477_; 
v_a_475_ = lean_ctor_get(v___x_474_, 0);
lean_inc(v_a_475_);
lean_dec_ref_known(v___x_474_, 1);
lean_inc(v_fst_465_);
v___x_476_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr(v_fst_465_);
v___x_477_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(v_snd_466_, v_fst_465_);
if (lean_obj_tag(v___x_477_) == 0)
{
lean_object* v_a_478_; lean_object* v___x_479_; lean_object* v___x_480_; 
v_a_478_ = lean_ctor_get(v___x_477_, 0);
lean_inc(v_a_478_);
lean_dec_ref_known(v___x_477_, 1);
lean_inc_ref(v___x_472_);
v___x_479_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr(v___x_472_);
v___x_480_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(v_snd_466_, v___x_472_);
lean_dec(v_snd_466_);
if (lean_obj_tag(v___x_480_) == 0)
{
lean_object* v_a_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_497_; 
v_a_481_ = lean_ctor_get(v___x_480_, 0);
v_isSharedCheck_497_ = !lean_is_exclusive(v___x_480_);
if (v_isSharedCheck_497_ == 0)
{
v___x_483_ = v___x_480_;
v_isShared_484_ = v_isSharedCheck_497_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_a_481_);
lean_dec(v___x_480_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_497_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_491_; 
v___x_485_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___closed__2, &l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___closed__2_once, _init_l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___closed__2);
v___x_486_ = l_Lean_eagerReflBoolTrue;
v___x_487_ = l_Lean_mkApp4(v___x_485_, v_a_475_, v___x_476_, v___x_479_, v___x_486_);
lean_inc(v_a_481_);
v___x_488_ = l_Lean_mkNatEq(v_a_478_, v_a_481_);
v___x_489_ = l_Lean_Meta_mkExpectedPropHint(v___x_487_, v___x_488_);
if (v_isShared_469_ == 0)
{
lean_ctor_set(v___x_468_, 1, v___x_489_);
lean_ctor_set(v___x_468_, 0, v_a_481_);
v___x_491_ = v___x_468_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v_a_481_);
lean_ctor_set(v_reuseFailAlloc_496_, 1, v___x_489_);
v___x_491_ = v_reuseFailAlloc_496_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
lean_object* v___x_492_; lean_object* v___x_494_; 
v___x_492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_492_, 0, v___x_491_);
if (v_isShared_484_ == 0)
{
lean_ctor_set(v___x_483_, 0, v___x_492_);
v___x_494_ = v___x_483_;
goto v_reusejp_493_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v___x_492_);
v___x_494_ = v_reuseFailAlloc_495_;
goto v_reusejp_493_;
}
v_reusejp_493_:
{
return v___x_494_;
}
}
}
}
else
{
lean_object* v_a_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_505_; 
lean_dec_ref(v___x_479_);
lean_dec(v_a_478_);
lean_dec_ref(v___x_476_);
lean_dec(v_a_475_);
lean_del_object(v___x_468_);
v_a_498_ = lean_ctor_get(v___x_480_, 0);
v_isSharedCheck_505_ = !lean_is_exclusive(v___x_480_);
if (v_isSharedCheck_505_ == 0)
{
v___x_500_ = v___x_480_;
v_isShared_501_ = v_isSharedCheck_505_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_a_498_);
lean_dec(v___x_480_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_505_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
lean_object* v___x_503_; 
if (v_isShared_501_ == 0)
{
v___x_503_ = v___x_500_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v_a_498_);
v___x_503_ = v_reuseFailAlloc_504_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
return v___x_503_;
}
}
}
}
else
{
lean_object* v_a_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_513_; 
lean_dec_ref(v___x_476_);
lean_dec(v_a_475_);
lean_dec_ref(v___x_472_);
lean_del_object(v___x_468_);
lean_dec(v_snd_466_);
v_a_506_ = lean_ctor_get(v___x_477_, 0);
v_isSharedCheck_513_ = !lean_is_exclusive(v___x_477_);
if (v_isSharedCheck_513_ == 0)
{
v___x_508_ = v___x_477_;
v_isShared_509_ = v_isSharedCheck_513_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_a_506_);
lean_dec(v___x_477_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_513_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v___x_511_; 
if (v_isShared_509_ == 0)
{
v___x_511_ = v___x_508_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v_a_506_);
v___x_511_ = v_reuseFailAlloc_512_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
return v___x_511_;
}
}
}
}
else
{
lean_object* v_a_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_521_; 
lean_dec_ref(v___x_472_);
lean_del_object(v___x_468_);
lean_dec(v_snd_466_);
lean_dec(v_fst_465_);
v_a_514_ = lean_ctor_get(v___x_474_, 0);
v_isSharedCheck_521_ = !lean_is_exclusive(v___x_474_);
if (v_isSharedCheck_521_ == 0)
{
v___x_516_ = v___x_474_;
v_isShared_517_ = v_isSharedCheck_521_;
goto v_resetjp_515_;
}
else
{
lean_inc(v_a_514_);
lean_dec(v___x_474_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_521_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
lean_object* v___x_519_; 
if (v_isShared_517_ == 0)
{
v___x_519_ = v___x_516_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v_a_514_);
v___x_519_ = v_reuseFailAlloc_520_;
goto v_reusejp_518_;
}
v_reusejp_518_:
{
return v___x_519_;
}
}
}
}
else
{
lean_object* v___x_522_; lean_object* v___x_524_; 
lean_dec_ref(v___x_472_);
lean_del_object(v___x_468_);
lean_dec(v_snd_466_);
lean_dec(v_fst_465_);
v___x_522_ = lean_box(0);
if (v_isShared_464_ == 0)
{
lean_ctor_set(v___x_463_, 0, v___x_522_);
v___x_524_ = v___x_463_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v___x_522_);
v___x_524_ = v_reuseFailAlloc_525_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
return v___x_524_;
}
}
}
}
}
else
{
lean_object* v_a_528_; lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_535_; 
v_a_528_ = lean_ctor_get(v___x_460_, 0);
v_isSharedCheck_535_ = !lean_is_exclusive(v___x_460_);
if (v_isSharedCheck_535_ == 0)
{
v___x_530_ = v___x_460_;
v_isShared_531_ = v_isSharedCheck_535_;
goto v_resetjp_529_;
}
else
{
lean_inc(v_a_528_);
lean_dec(v___x_460_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_535_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
lean_object* v___x_533_; 
if (v_isShared_531_ == 0)
{
v___x_533_ = v___x_530_;
goto v_reusejp_532_;
}
else
{
lean_object* v_reuseFailAlloc_534_; 
v_reuseFailAlloc_534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_534_, 0, v_a_528_);
v___x_533_ = v_reuseFailAlloc_534_;
goto v_reusejp_532_;
}
v_reusejp_532_:
{
return v___x_533_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___boxed(lean_object* v_input_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_, lean_object* v_a_540_, lean_object* v_a_541_){
_start:
{
lean_object* v_res_542_; 
v_res_542_ = l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f(v_input_536_, v_a_537_, v_a_538_, v_a_539_, v_a_540_);
lean_dec(v_a_540_);
lean_dec_ref(v_a_539_);
lean_dec(v_a_538_);
lean_dec_ref(v_a_537_);
return v_res_542_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Arith_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Arith_Nat_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_AppBuilder(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Arith_Nat_Simp(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Simp_Arith_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Simp_Arith_Nat_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Simp_Arith_Nat_Simp(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Simp_Arith_Util(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Simp_Arith_Nat_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Simp_Arith_Nat_Simp(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Simp_Arith_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Arith_Nat_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Simp_Arith_Nat_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Simp_Arith_Nat_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Simp_Arith_Nat_Simp(builtin);
}
#ifdef __cplusplus
}
#endif

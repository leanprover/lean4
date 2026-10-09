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
lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f(lean_object* v_e_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_, lean_object* v_a_51_){
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
lean_object* v___x_124_; lean_object* v___x_125_; 
lean_dec_ref(v___x_70_);
v___x_124_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__9, &l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__9_once, _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__9);
v___x_125_ = l_Lean_Meta_Simp_Arith_Nat_toContextExpr(v_snd_63_, v_a_48_, v_a_49_, v_a_50_, v_a_51_);
if (lean_obj_tag(v___x_125_) == 0)
{
lean_object* v_a_126_; lean_object* v___x_128_; uint8_t v_isShared_129_; uint8_t v_isSharedCheck_145_; 
v_a_126_ = lean_ctor_get(v___x_125_, 0);
v_isSharedCheck_145_ = !lean_is_exclusive(v___x_125_);
if (v_isSharedCheck_145_ == 0)
{
v___x_128_ = v___x_125_;
v_isShared_129_ = v_isSharedCheck_145_;
goto v_resetjp_127_;
}
else
{
lean_inc(v_a_126_);
lean_dec(v___x_125_);
v___x_128_ = lean_box(0);
v_isShared_129_ = v_isSharedCheck_145_;
goto v_resetjp_127_;
}
v_resetjp_127_:
{
lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_137_; 
v___x_130_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__12, &l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__12_once, _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__12);
v___x_131_ = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr(v_fst_62_);
v___x_132_ = l_Lean_eagerReflBoolTrue;
v___x_133_ = l_Lean_mkApp3(v___x_130_, v_a_126_, v___x_131_, v___x_132_);
v___x_134_ = l_Lean_mkPropEq(v_a_68_, v___x_124_);
v___x_135_ = l_Lean_Meta_mkExpectedPropHint(v___x_133_, v___x_134_);
if (v_isShared_66_ == 0)
{
lean_ctor_set(v___x_65_, 1, v___x_135_);
lean_ctor_set(v___x_65_, 0, v___x_124_);
v___x_137_ = v___x_65_;
goto v_reusejp_136_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v___x_124_);
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
if (v_isShared_129_ == 0)
{
lean_ctor_set(v___x_128_, 0, v___x_139_);
v___x_141_ = v___x_128_;
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
v_a_146_ = lean_ctor_get(v___x_125_, 0);
v_isSharedCheck_153_ = !lean_is_exclusive(v___x_125_);
if (v_isSharedCheck_153_ == 0)
{
v___x_148_ = v___x_125_;
v_isShared_149_ = v_isSharedCheck_153_;
goto v_resetjp_147_;
}
else
{
lean_inc(v_a_146_);
lean_dec(v___x_125_);
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
lean_object* v___x_154_; lean_object* v___x_155_; 
lean_dec_ref(v___x_70_);
v___x_154_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__15, &l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__15_once, _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__15);
v___x_155_ = l_Lean_Meta_Simp_Arith_Nat_toContextExpr(v_snd_63_, v_a_48_, v_a_49_, v_a_50_, v_a_51_);
if (lean_obj_tag(v___x_155_) == 0)
{
lean_object* v_a_156_; lean_object* v___x_158_; uint8_t v_isShared_159_; uint8_t v_isSharedCheck_175_; 
v_a_156_ = lean_ctor_get(v___x_155_, 0);
v_isSharedCheck_175_ = !lean_is_exclusive(v___x_155_);
if (v_isSharedCheck_175_ == 0)
{
v___x_158_ = v___x_155_;
v_isShared_159_ = v_isSharedCheck_175_;
goto v_resetjp_157_;
}
else
{
lean_inc(v_a_156_);
lean_dec(v___x_155_);
v___x_158_ = lean_box(0);
v_isShared_159_ = v_isSharedCheck_175_;
goto v_resetjp_157_;
}
v_resetjp_157_:
{
lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_167_; 
v___x_160_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__18, &l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__18_once, _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__18);
v___x_161_ = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr(v_fst_62_);
v___x_162_ = l_Lean_eagerReflBoolTrue;
v___x_163_ = l_Lean_mkApp3(v___x_160_, v_a_156_, v___x_161_, v___x_162_);
v___x_164_ = l_Lean_mkPropEq(v_a_68_, v___x_154_);
v___x_165_ = l_Lean_Meta_mkExpectedPropHint(v___x_163_, v___x_164_);
if (v_isShared_66_ == 0)
{
lean_ctor_set(v___x_65_, 1, v___x_165_);
lean_ctor_set(v___x_65_, 0, v___x_154_);
v___x_167_ = v___x_65_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_174_; 
v_reuseFailAlloc_174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_174_, 0, v___x_154_);
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
if (v_isShared_159_ == 0)
{
lean_ctor_set(v___x_158_, 0, v___x_169_);
v___x_171_ = v___x_158_;
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
v_a_176_ = lean_ctor_get(v___x_155_, 0);
v_isSharedCheck_183_ = !lean_is_exclusive(v___x_155_);
if (v_isSharedCheck_183_ == 0)
{
v___x_178_ = v___x_155_;
v_isShared_179_ = v_isSharedCheck_183_;
goto v_resetjp_177_;
}
else
{
lean_inc(v_a_176_);
lean_dec(v___x_155_);
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
LEAN_EXPORT void l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_47_ = stack[0].m_obj;
lean_object* v_a_48_ = stack[1].m_obj;
lean_object* v_a_49_ = stack[2].m_obj;
lean_object* v_a_50_ = stack[3].m_obj;
lean_object* v_a_51_ = stack[4].m_obj;
lean_object* v_res_207_;
v_res_207_ = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f(v_e_47_, v_a_48_, v_a_49_, v_a_50_, v_a_51_);
stack->m_obj
 = v_res_207_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___boxed(lean_object* v_e_208_, lean_object* v_a_209_, lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_, lean_object* v_a_213_){
_start:
{
lean_object* v_res_214_; 
v_res_214_ = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f(v_e_208_, v_a_209_, v_a_210_, v_a_211_, v_a_212_);
lean_dec(v_a_212_);
lean_dec_ref(v_a_211_);
lean_dec(v_a_210_);
lean_dec_ref(v_a_209_);
return v_res_214_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__3(void){
_start:
{
lean_object* v___x_220_; lean_object* v___x_221_; 
v___x_220_ = lean_box(0);
v___x_221_ = l_Lean_Level_succ___override(v___x_220_);
return v___x_221_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__4(void){
_start:
{
lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_222_ = lean_box(0);
v___x_223_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__3, &l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__3_once, _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__3);
v___x_224_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_224_, 0, v___x_223_);
lean_ctor_set(v___x_224_, 1, v___x_222_);
return v___x_224_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__5(void){
_start:
{
lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; 
v___x_225_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__4, &l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__4_once, _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__4);
v___x_226_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__2));
v___x_227_ = l_Lean_mkConst(v___x_226_, v___x_225_);
return v___x_227_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__6(void){
_start:
{
lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_228_ = lean_box(0);
v___x_229_ = l_Lean_mkSort(v___x_228_);
return v___x_229_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__22(void){
_start:
{
lean_object* v___x_255_; lean_object* v___x_256_; 
v___x_255_ = lean_unsigned_to_nat(1u);
v___x_256_ = l_Lean_mkNatLit(v___x_255_);
return v___x_256_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__25(void){
_start:
{
lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; 
v___x_261_ = lean_box(0);
v___x_262_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__24));
v___x_263_ = l_Lean_mkConst(v___x_262_, v___x_261_);
return v___x_263_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__28(void){
_start:
{
lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_268_ = lean_box(0);
v___x_269_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__27));
v___x_270_ = l_Lean_mkConst(v___x_269_, v___x_268_);
return v___x_270_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__31(void){
_start:
{
lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_275_ = lean_box(0);
v___x_276_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__30));
v___x_277_ = l_Lean_mkConst(v___x_276_, v___x_275_);
return v___x_277_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__34(void){
_start:
{
lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_282_ = lean_box(0);
v___x_283_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__33));
v___x_284_ = l_Lean_mkConst(v___x_283_, v___x_282_);
return v___x_284_;
}
}
lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f(lean_object* v_e_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_){
_start:
{
lean_object* v_val_292_; lean_object* v_h_u2081_293_; lean_object* v___y_294_; lean_object* v___y_295_; lean_object* v___y_296_; lean_object* v___y_297_; lean_object* v___x_335_; lean_object* v___x_336_; uint8_t v___x_337_; 
v___x_335_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__8));
v___x_336_ = lean_unsigned_to_nat(1u);
v___x_337_ = l_Lean_Expr_isAppOfArity(v_e_285_, v___x_335_, v___x_336_);
if (v___x_337_ == 0)
{
lean_object* v___x_338_; 
v___x_338_ = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f(v_e_285_, v_a_286_, v_a_287_, v_a_288_, v_a_289_);
return v___x_338_;
}
else
{
lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_339_ = l_Lean_Expr_appArg_x21(v_e_285_);
v___x_340_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v___x_339_, v_a_287_);
if (lean_obj_tag(v___x_340_) == 0)
{
lean_object* v_a_341_; lean_object* v___x_342_; uint8_t v___x_343_; 
v_a_341_ = lean_ctor_get(v___x_340_, 0);
lean_inc(v_a_341_);
lean_dec_ref_known(v___x_340_, 1);
v___x_342_ = l_Lean_Expr_cleanupAnnotations(v_a_341_);
v___x_343_ = l_Lean_Expr_isApp(v___x_342_);
if (v___x_343_ == 0)
{
lean_dec_ref(v___x_342_);
lean_dec_ref(v_e_285_);
goto v___jp_332_;
}
else
{
lean_object* v_arg_344_; lean_object* v___x_345_; uint8_t v___x_346_; 
v_arg_344_ = lean_ctor_get(v___x_342_, 1);
lean_inc_ref(v_arg_344_);
v___x_345_ = l_Lean_Expr_appFnCleanup___redArg(v___x_342_);
v___x_346_ = l_Lean_Expr_isApp(v___x_345_);
if (v___x_346_ == 0)
{
lean_dec_ref(v___x_345_);
lean_dec_ref(v_arg_344_);
lean_dec_ref(v_e_285_);
goto v___jp_332_;
}
else
{
lean_object* v_arg_347_; lean_object* v___x_348_; uint8_t v___x_349_; 
v_arg_347_ = lean_ctor_get(v___x_345_, 1);
lean_inc_ref(v_arg_347_);
v___x_348_ = l_Lean_Expr_appFnCleanup___redArg(v___x_345_);
v___x_349_ = l_Lean_Expr_isApp(v___x_348_);
if (v___x_349_ == 0)
{
lean_dec_ref(v___x_348_);
lean_dec_ref(v_arg_347_);
lean_dec_ref(v_arg_344_);
lean_dec_ref(v_e_285_);
goto v___jp_332_;
}
else
{
lean_object* v___x_350_; uint8_t v___x_351_; 
v___x_350_ = l_Lean_Expr_appFnCleanup___redArg(v___x_348_);
v___x_351_ = l_Lean_Expr_isApp(v___x_350_);
if (v___x_351_ == 0)
{
lean_dec_ref(v___x_350_);
lean_dec_ref(v_arg_347_);
lean_dec_ref(v_arg_344_);
lean_dec_ref(v_e_285_);
goto v___jp_332_;
}
else
{
lean_object* v_arg_352_; lean_object* v___x_353_; lean_object* v___x_354_; uint8_t v___x_355_; 
v_arg_352_ = lean_ctor_get(v___x_350_, 1);
lean_inc_ref(v_arg_352_);
v___x_353_ = l_Lean_Expr_appFnCleanup___redArg(v___x_350_);
v___x_354_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__11));
v___x_355_ = l_Lean_Expr_isConstOf(v___x_353_, v___x_354_);
if (v___x_355_ == 0)
{
lean_object* v___x_356_; uint8_t v___x_357_; 
v___x_356_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__14));
v___x_357_ = l_Lean_Expr_isConstOf(v___x_353_, v___x_356_);
if (v___x_357_ == 0)
{
lean_object* v___x_358_; uint8_t v___x_359_; 
v___x_358_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__17));
v___x_359_ = l_Lean_Expr_isConstOf(v___x_353_, v___x_358_);
if (v___x_359_ == 0)
{
lean_object* v___x_360_; uint8_t v___x_361_; 
v___x_360_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__20));
v___x_361_ = l_Lean_Expr_isConstOf(v___x_353_, v___x_360_);
lean_dec_ref(v___x_353_);
if (v___x_361_ == 0)
{
lean_dec_ref(v_arg_352_);
lean_dec_ref(v_arg_347_);
lean_dec_ref(v_arg_344_);
lean_dec_ref(v_e_285_);
goto v___jp_332_;
}
else
{
lean_object* v___x_362_; 
v___x_362_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_352_, v_a_287_);
if (lean_obj_tag(v___x_362_) == 0)
{
lean_object* v_a_363_; lean_object* v___x_364_; lean_object* v___x_365_; uint8_t v___x_366_; 
v_a_363_ = lean_ctor_get(v___x_362_, 0);
lean_inc(v_a_363_);
lean_dec_ref_known(v___x_362_, 1);
v___x_364_ = l_Lean_Expr_cleanupAnnotations(v_a_363_);
v___x_365_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__21));
v___x_366_ = l_Lean_Expr_isConstOf(v___x_364_, v___x_365_);
lean_dec_ref(v___x_364_);
if (v___x_366_ == 0)
{
lean_dec_ref(v_arg_347_);
lean_dec_ref(v_arg_344_);
lean_dec_ref(v_e_285_);
goto v___jp_332_;
}
else
{
lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_367_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__22, &l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__22_once, _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__22);
lean_inc_ref(v_arg_344_);
v___x_368_ = l_Lean_mkNatAdd(v_arg_344_, v___x_367_);
lean_inc_ref(v_arg_347_);
v___x_369_ = l_Lean_mkNatLE(v___x_368_, v_arg_347_);
v___x_370_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__25, &l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__25_once, _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__25);
v___x_371_ = l_Lean_mkAppB(v___x_370_, v_arg_347_, v_arg_344_);
v_val_292_ = v___x_369_;
v_h_u2081_293_ = v___x_371_;
v___y_294_ = v_a_286_;
v___y_295_ = v_a_287_;
v___y_296_ = v_a_288_;
v___y_297_ = v_a_289_;
goto v___jp_291_;
}
}
else
{
lean_object* v_a_372_; lean_object* v___x_374_; uint8_t v_isShared_375_; uint8_t v_isSharedCheck_379_; 
lean_dec_ref(v_arg_347_);
lean_dec_ref(v_arg_344_);
lean_dec_ref(v_e_285_);
v_a_372_ = lean_ctor_get(v___x_362_, 0);
v_isSharedCheck_379_ = !lean_is_exclusive(v___x_362_);
if (v_isSharedCheck_379_ == 0)
{
v___x_374_ = v___x_362_;
v_isShared_375_ = v_isSharedCheck_379_;
goto v_resetjp_373_;
}
else
{
lean_inc(v_a_372_);
lean_dec(v___x_362_);
v___x_374_ = lean_box(0);
v_isShared_375_ = v_isSharedCheck_379_;
goto v_resetjp_373_;
}
v_resetjp_373_:
{
lean_object* v___x_377_; 
if (v_isShared_375_ == 0)
{
v___x_377_ = v___x_374_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v_a_372_);
v___x_377_ = v_reuseFailAlloc_378_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
return v___x_377_;
}
}
}
}
}
else
{
lean_object* v___x_380_; 
lean_dec_ref(v___x_353_);
v___x_380_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_352_, v_a_287_);
if (lean_obj_tag(v___x_380_) == 0)
{
lean_object* v_a_381_; lean_object* v___x_382_; lean_object* v___x_383_; uint8_t v___x_384_; 
v_a_381_ = lean_ctor_get(v___x_380_, 0);
lean_inc(v_a_381_);
lean_dec_ref_known(v___x_380_, 1);
v___x_382_ = l_Lean_Expr_cleanupAnnotations(v_a_381_);
v___x_383_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__21));
v___x_384_ = l_Lean_Expr_isConstOf(v___x_382_, v___x_383_);
lean_dec_ref(v___x_382_);
if (v___x_384_ == 0)
{
lean_dec_ref(v_arg_347_);
lean_dec_ref(v_arg_344_);
lean_dec_ref(v_e_285_);
goto v___jp_332_;
}
else
{
lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; 
v___x_385_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__22, &l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__22_once, _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__22);
lean_inc_ref(v_arg_347_);
v___x_386_ = l_Lean_mkNatAdd(v_arg_347_, v___x_385_);
lean_inc_ref(v_arg_344_);
v___x_387_ = l_Lean_mkNatLE(v___x_386_, v_arg_344_);
v___x_388_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__28, &l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__28_once, _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__28);
v___x_389_ = l_Lean_mkAppB(v___x_388_, v_arg_347_, v_arg_344_);
v_val_292_ = v___x_387_;
v_h_u2081_293_ = v___x_389_;
v___y_294_ = v_a_286_;
v___y_295_ = v_a_287_;
v___y_296_ = v_a_288_;
v___y_297_ = v_a_289_;
goto v___jp_291_;
}
}
else
{
lean_object* v_a_390_; lean_object* v___x_392_; uint8_t v_isShared_393_; uint8_t v_isSharedCheck_397_; 
lean_dec_ref(v_arg_347_);
lean_dec_ref(v_arg_344_);
lean_dec_ref(v_e_285_);
v_a_390_ = lean_ctor_get(v___x_380_, 0);
v_isSharedCheck_397_ = !lean_is_exclusive(v___x_380_);
if (v_isSharedCheck_397_ == 0)
{
v___x_392_ = v___x_380_;
v_isShared_393_ = v_isSharedCheck_397_;
goto v_resetjp_391_;
}
else
{
lean_inc(v_a_390_);
lean_dec(v___x_380_);
v___x_392_ = lean_box(0);
v_isShared_393_ = v_isSharedCheck_397_;
goto v_resetjp_391_;
}
v_resetjp_391_:
{
lean_object* v___x_395_; 
if (v_isShared_393_ == 0)
{
v___x_395_ = v___x_392_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v_a_390_);
v___x_395_ = v_reuseFailAlloc_396_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
return v___x_395_;
}
}
}
}
}
else
{
lean_object* v___x_398_; 
lean_dec_ref(v___x_353_);
v___x_398_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_352_, v_a_287_);
if (lean_obj_tag(v___x_398_) == 0)
{
lean_object* v_a_399_; lean_object* v___x_400_; lean_object* v___x_401_; uint8_t v___x_402_; 
v_a_399_ = lean_ctor_get(v___x_398_, 0);
lean_inc(v_a_399_);
lean_dec_ref_known(v___x_398_, 1);
v___x_400_ = l_Lean_Expr_cleanupAnnotations(v_a_399_);
v___x_401_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__21));
v___x_402_ = l_Lean_Expr_isConstOf(v___x_400_, v___x_401_);
lean_dec_ref(v___x_400_);
if (v___x_402_ == 0)
{
lean_dec_ref(v_arg_347_);
lean_dec_ref(v_arg_344_);
lean_dec_ref(v_e_285_);
goto v___jp_332_;
}
else
{
lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; 
lean_inc_ref(v_arg_347_);
lean_inc_ref(v_arg_344_);
v___x_403_ = l_Lean_mkNatLE(v_arg_344_, v_arg_347_);
v___x_404_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__31, &l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__31_once, _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__31);
v___x_405_ = l_Lean_mkAppB(v___x_404_, v_arg_347_, v_arg_344_);
v_val_292_ = v___x_403_;
v_h_u2081_293_ = v___x_405_;
v___y_294_ = v_a_286_;
v___y_295_ = v_a_287_;
v___y_296_ = v_a_288_;
v___y_297_ = v_a_289_;
goto v___jp_291_;
}
}
else
{
lean_object* v_a_406_; lean_object* v___x_408_; uint8_t v_isShared_409_; uint8_t v_isSharedCheck_413_; 
lean_dec_ref(v_arg_347_);
lean_dec_ref(v_arg_344_);
lean_dec_ref(v_e_285_);
v_a_406_ = lean_ctor_get(v___x_398_, 0);
v_isSharedCheck_413_ = !lean_is_exclusive(v___x_398_);
if (v_isSharedCheck_413_ == 0)
{
v___x_408_ = v___x_398_;
v_isShared_409_ = v_isSharedCheck_413_;
goto v_resetjp_407_;
}
else
{
lean_inc(v_a_406_);
lean_dec(v___x_398_);
v___x_408_ = lean_box(0);
v_isShared_409_ = v_isSharedCheck_413_;
goto v_resetjp_407_;
}
v_resetjp_407_:
{
lean_object* v___x_411_; 
if (v_isShared_409_ == 0)
{
v___x_411_ = v___x_408_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v_a_406_);
v___x_411_ = v_reuseFailAlloc_412_;
goto v_reusejp_410_;
}
v_reusejp_410_:
{
return v___x_411_;
}
}
}
}
}
else
{
lean_object* v___x_414_; 
lean_dec_ref(v___x_353_);
v___x_414_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_352_, v_a_287_);
if (lean_obj_tag(v___x_414_) == 0)
{
lean_object* v_a_415_; lean_object* v___x_416_; lean_object* v___x_417_; uint8_t v___x_418_; 
v_a_415_ = lean_ctor_get(v___x_414_, 0);
lean_inc(v_a_415_);
lean_dec_ref_known(v___x_414_, 1);
v___x_416_ = l_Lean_Expr_cleanupAnnotations(v_a_415_);
v___x_417_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__21));
v___x_418_ = l_Lean_Expr_isConstOf(v___x_416_, v___x_417_);
lean_dec_ref(v___x_416_);
if (v___x_418_ == 0)
{
lean_dec_ref(v_arg_347_);
lean_dec_ref(v_arg_344_);
lean_dec_ref(v_e_285_);
goto v___jp_332_;
}
else
{
lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; 
lean_inc_ref(v_arg_344_);
lean_inc_ref(v_arg_347_);
v___x_419_ = l_Lean_mkNatLE(v_arg_347_, v_arg_344_);
v___x_420_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__34, &l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__34_once, _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__34);
v___x_421_ = l_Lean_mkAppB(v___x_420_, v_arg_347_, v_arg_344_);
v_val_292_ = v___x_419_;
v_h_u2081_293_ = v___x_421_;
v___y_294_ = v_a_286_;
v___y_295_ = v_a_287_;
v___y_296_ = v_a_288_;
v___y_297_ = v_a_289_;
goto v___jp_291_;
}
}
else
{
lean_object* v_a_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_429_; 
lean_dec_ref(v_arg_347_);
lean_dec_ref(v_arg_344_);
lean_dec_ref(v_e_285_);
v_a_422_ = lean_ctor_get(v___x_414_, 0);
v_isSharedCheck_429_ = !lean_is_exclusive(v___x_414_);
if (v_isSharedCheck_429_ == 0)
{
v___x_424_ = v___x_414_;
v_isShared_425_ = v_isSharedCheck_429_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_a_422_);
lean_dec(v___x_414_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_429_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
lean_object* v___x_427_; 
if (v_isShared_425_ == 0)
{
v___x_427_ = v___x_424_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(1, 1, 0);
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
}
}
}
}
}
}
else
{
lean_object* v_a_430_; lean_object* v___x_432_; uint8_t v_isShared_433_; uint8_t v_isSharedCheck_437_; 
lean_dec_ref(v_e_285_);
v_a_430_ = lean_ctor_get(v___x_340_, 0);
v_isSharedCheck_437_ = !lean_is_exclusive(v___x_340_);
if (v_isSharedCheck_437_ == 0)
{
v___x_432_ = v___x_340_;
v_isShared_433_ = v_isSharedCheck_437_;
goto v_resetjp_431_;
}
else
{
lean_inc(v_a_430_);
lean_dec(v___x_340_);
v___x_432_ = lean_box(0);
v_isShared_433_ = v_isSharedCheck_437_;
goto v_resetjp_431_;
}
v_resetjp_431_:
{
lean_object* v___x_435_; 
if (v_isShared_433_ == 0)
{
v___x_435_ = v___x_432_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v_a_430_);
v___x_435_ = v_reuseFailAlloc_436_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
return v___x_435_;
}
}
}
}
v___jp_291_:
{
lean_object* v___x_298_; 
lean_inc_ref(v_val_292_);
v___x_298_ = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f(v_val_292_, v___y_294_, v___y_295_, v___y_296_, v___y_297_);
if (lean_obj_tag(v___x_298_) == 0)
{
lean_object* v_a_299_; lean_object* v___x_301_; uint8_t v_isShared_302_; uint8_t v_isSharedCheck_331_; 
v_a_299_ = lean_ctor_get(v___x_298_, 0);
v_isSharedCheck_331_ = !lean_is_exclusive(v___x_298_);
if (v_isSharedCheck_331_ == 0)
{
v___x_301_ = v___x_298_;
v_isShared_302_ = v_isSharedCheck_331_;
goto v_resetjp_300_;
}
else
{
lean_inc(v_a_299_);
lean_dec(v___x_298_);
v___x_301_ = lean_box(0);
v_isShared_302_ = v_isSharedCheck_331_;
goto v_resetjp_300_;
}
v_resetjp_300_:
{
if (lean_obj_tag(v_a_299_) == 1)
{
lean_object* v_val_303_; lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_325_; 
v_val_303_ = lean_ctor_get(v_a_299_, 0);
v_isSharedCheck_325_ = !lean_is_exclusive(v_a_299_);
if (v_isSharedCheck_325_ == 0)
{
v___x_305_ = v_a_299_;
v_isShared_306_ = v_isSharedCheck_325_;
goto v_resetjp_304_;
}
else
{
lean_inc(v_val_303_);
lean_dec(v_a_299_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_325_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
lean_object* v_fst_307_; lean_object* v_snd_308_; lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_324_; 
v_fst_307_ = lean_ctor_get(v_val_303_, 0);
v_snd_308_ = lean_ctor_get(v_val_303_, 1);
v_isSharedCheck_324_ = !lean_is_exclusive(v_val_303_);
if (v_isSharedCheck_324_ == 0)
{
v___x_310_ = v_val_303_;
v_isShared_311_ = v_isSharedCheck_324_;
goto v_resetjp_309_;
}
else
{
lean_inc(v_snd_308_);
lean_inc(v_fst_307_);
lean_dec(v_val_303_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_324_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_316_; 
v___x_312_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__5, &l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__5_once, _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__5);
v___x_313_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__6, &l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__6_once, _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__6);
lean_inc(v_fst_307_);
v___x_314_ = l_Lean_mkApp6(v___x_312_, v___x_313_, v_e_285_, v_val_292_, v_fst_307_, v_h_u2081_293_, v_snd_308_);
if (v_isShared_311_ == 0)
{
lean_ctor_set(v___x_310_, 1, v___x_314_);
v___x_316_ = v___x_310_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v_fst_307_);
lean_ctor_set(v_reuseFailAlloc_323_, 1, v___x_314_);
v___x_316_ = v_reuseFailAlloc_323_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
lean_object* v___x_318_; 
if (v_isShared_306_ == 0)
{
lean_ctor_set(v___x_305_, 0, v___x_316_);
v___x_318_ = v___x_305_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v___x_316_);
v___x_318_ = v_reuseFailAlloc_322_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
lean_object* v___x_320_; 
if (v_isShared_302_ == 0)
{
lean_ctor_set(v___x_301_, 0, v___x_318_);
v___x_320_ = v___x_301_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_321_; 
v_reuseFailAlloc_321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_321_, 0, v___x_318_);
v___x_320_ = v_reuseFailAlloc_321_;
goto v_reusejp_319_;
}
v_reusejp_319_:
{
return v___x_320_;
}
}
}
}
}
}
else
{
lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_329_; 
lean_dec(v_a_299_);
lean_dec_ref(v_e_285_);
v___x_326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_326_, 0, v_val_292_);
lean_ctor_set(v___x_326_, 1, v_h_u2081_293_);
v___x_327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_327_, 0, v___x_326_);
if (v_isShared_302_ == 0)
{
lean_ctor_set(v___x_301_, 0, v___x_327_);
v___x_329_ = v___x_301_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v___x_327_);
v___x_329_ = v_reuseFailAlloc_330_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
return v___x_329_;
}
}
}
}
else
{
lean_dec_ref(v_h_u2081_293_);
lean_dec_ref(v_val_292_);
lean_dec_ref(v_e_285_);
return v___x_298_;
}
}
v___jp_332_:
{
lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_333_ = lean_box(0);
v___x_334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_334_, 0, v___x_333_);
return v___x_334_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_285_ = stack[0].m_obj;
lean_object* v_a_286_ = stack[1].m_obj;
lean_object* v_a_287_ = stack[2].m_obj;
lean_object* v_a_288_ = stack[3].m_obj;
lean_object* v_a_289_ = stack[4].m_obj;
lean_object* v_res_438_;
v_res_438_ = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f(v_e_285_, v_a_286_, v_a_287_, v_a_288_, v_a_289_);
stack->m_obj
 = v_res_438_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___boxed(lean_object* v_e_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_443_, lean_object* v_a_444_){
_start:
{
lean_object* v_res_445_; 
v_res_445_ = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f(v_e_439_, v_a_440_, v_a_441_, v_a_442_, v_a_443_);
lean_dec(v_a_443_);
lean_dec_ref(v_a_442_);
lean_dec(v_a_441_);
lean_dec_ref(v_a_440_);
return v_res_445_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___closed__2(void){
_start:
{
lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; 
v___x_453_ = lean_box(0);
v___x_454_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___closed__1));
v___x_455_ = l_Lean_mkConst(v___x_454_, v___x_453_);
return v___x_455_;
}
}
lean_object* l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f(lean_object* v_input_456_, lean_object* v_a_457_, lean_object* v_a_458_, lean_object* v_a_459_, lean_object* v_a_460_){
_start:
{
lean_object* v___x_462_; 
v___x_462_ = l_Lean_Meta_Simp_Arith_Nat_toLinearExpr(v_input_456_, v_a_457_, v_a_458_, v_a_459_, v_a_460_);
if (lean_obj_tag(v___x_462_) == 0)
{
lean_object* v_a_463_; lean_object* v___x_465_; uint8_t v_isShared_466_; uint8_t v_isSharedCheck_529_; 
v_a_463_ = lean_ctor_get(v___x_462_, 0);
v_isSharedCheck_529_ = !lean_is_exclusive(v___x_462_);
if (v_isSharedCheck_529_ == 0)
{
v___x_465_ = v___x_462_;
v_isShared_466_ = v_isSharedCheck_529_;
goto v_resetjp_464_;
}
else
{
lean_inc(v_a_463_);
lean_dec(v___x_462_);
v___x_465_ = lean_box(0);
v_isShared_466_ = v_isSharedCheck_529_;
goto v_resetjp_464_;
}
v_resetjp_464_:
{
lean_object* v_fst_467_; lean_object* v_snd_468_; lean_object* v___x_470_; uint8_t v_isShared_471_; uint8_t v_isSharedCheck_528_; 
v_fst_467_ = lean_ctor_get(v_a_463_, 0);
v_snd_468_ = lean_ctor_get(v_a_463_, 1);
v_isSharedCheck_528_ = !lean_is_exclusive(v_a_463_);
if (v_isSharedCheck_528_ == 0)
{
v___x_470_ = v_a_463_;
v_isShared_471_ = v_isSharedCheck_528_;
goto v_resetjp_469_;
}
else
{
lean_inc(v_snd_468_);
lean_inc(v_fst_467_);
lean_dec(v_a_463_);
v___x_470_ = lean_box(0);
v_isShared_471_ = v_isSharedCheck_528_;
goto v_resetjp_469_;
}
v_resetjp_469_:
{
lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; uint8_t v___x_475_; 
v___x_472_ = l_Nat_Internal_Linear_Expr_toPoly(v_fst_467_);
v___x_473_ = l_Nat_Internal_Linear_Poly_norm(v___x_472_);
v___x_474_ = l_Nat_Internal_Linear_Poly_toExpr(v___x_473_);
v___x_475_ = l_Nat_Internal_Linear_instBEqExpr_beq(v___x_474_, v_fst_467_);
if (v___x_475_ == 0)
{
lean_object* v___x_476_; 
lean_del_object(v___x_465_);
lean_inc(v_snd_468_);
v___x_476_ = l_Lean_Meta_Simp_Arith_Nat_toContextExpr(v_snd_468_, v_a_457_, v_a_458_, v_a_459_, v_a_460_);
if (lean_obj_tag(v___x_476_) == 0)
{
lean_object* v_a_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; 
v_a_477_ = lean_ctor_get(v___x_476_, 0);
lean_inc(v_a_477_);
lean_dec_ref_known(v___x_476_, 1);
v___x_478_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___closed__2, &l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___closed__2_once, _init_l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___closed__2);
lean_inc(v_fst_467_);
v___x_479_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr(v_fst_467_);
lean_inc_ref(v___x_474_);
v___x_480_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr(v___x_474_);
v___x_481_ = l_Lean_eagerReflBoolTrue;
v___x_482_ = l_Lean_mkApp4(v___x_478_, v_a_477_, v___x_479_, v___x_480_, v___x_481_);
v___x_483_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(v_snd_468_, v_fst_467_);
if (lean_obj_tag(v___x_483_) == 0)
{
lean_object* v_a_484_; lean_object* v___x_485_; 
v_a_484_ = lean_ctor_get(v___x_483_, 0);
lean_inc(v_a_484_);
lean_dec_ref_known(v___x_483_, 1);
v___x_485_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(v_snd_468_, v___x_474_);
lean_dec(v_snd_468_);
if (lean_obj_tag(v___x_485_) == 0)
{
lean_object* v_a_486_; lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_499_; 
v_a_486_ = lean_ctor_get(v___x_485_, 0);
v_isSharedCheck_499_ = !lean_is_exclusive(v___x_485_);
if (v_isSharedCheck_499_ == 0)
{
v___x_488_ = v___x_485_;
v_isShared_489_ = v_isSharedCheck_499_;
goto v_resetjp_487_;
}
else
{
lean_inc(v_a_486_);
lean_dec(v___x_485_);
v___x_488_ = lean_box(0);
v_isShared_489_ = v_isSharedCheck_499_;
goto v_resetjp_487_;
}
v_resetjp_487_:
{
lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_493_; 
lean_inc(v_a_486_);
v___x_490_ = l_Lean_mkNatEq(v_a_484_, v_a_486_);
v___x_491_ = l_Lean_Meta_mkExpectedPropHint(v___x_482_, v___x_490_);
if (v_isShared_471_ == 0)
{
lean_ctor_set(v___x_470_, 1, v___x_491_);
lean_ctor_set(v___x_470_, 0, v_a_486_);
v___x_493_ = v___x_470_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v_a_486_);
lean_ctor_set(v_reuseFailAlloc_498_, 1, v___x_491_);
v___x_493_ = v_reuseFailAlloc_498_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
lean_object* v___x_494_; lean_object* v___x_496_; 
v___x_494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_494_, 0, v___x_493_);
if (v_isShared_489_ == 0)
{
lean_ctor_set(v___x_488_, 0, v___x_494_);
v___x_496_ = v___x_488_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v___x_494_);
v___x_496_ = v_reuseFailAlloc_497_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
return v___x_496_;
}
}
}
}
else
{
lean_object* v_a_500_; lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_507_; 
lean_dec(v_a_484_);
lean_dec_ref(v___x_482_);
lean_del_object(v___x_470_);
v_a_500_ = lean_ctor_get(v___x_485_, 0);
v_isSharedCheck_507_ = !lean_is_exclusive(v___x_485_);
if (v_isSharedCheck_507_ == 0)
{
v___x_502_ = v___x_485_;
v_isShared_503_ = v_isSharedCheck_507_;
goto v_resetjp_501_;
}
else
{
lean_inc(v_a_500_);
lean_dec(v___x_485_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_507_;
goto v_resetjp_501_;
}
v_resetjp_501_:
{
lean_object* v___x_505_; 
if (v_isShared_503_ == 0)
{
v___x_505_ = v___x_502_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v_a_500_);
v___x_505_ = v_reuseFailAlloc_506_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
return v___x_505_;
}
}
}
}
else
{
lean_object* v_a_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_515_; 
lean_dec_ref(v___x_482_);
lean_dec_ref(v___x_474_);
lean_del_object(v___x_470_);
lean_dec(v_snd_468_);
v_a_508_ = lean_ctor_get(v___x_483_, 0);
v_isSharedCheck_515_ = !lean_is_exclusive(v___x_483_);
if (v_isSharedCheck_515_ == 0)
{
v___x_510_ = v___x_483_;
v_isShared_511_ = v_isSharedCheck_515_;
goto v_resetjp_509_;
}
else
{
lean_inc(v_a_508_);
lean_dec(v___x_483_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_515_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
lean_object* v___x_513_; 
if (v_isShared_511_ == 0)
{
v___x_513_ = v___x_510_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v_a_508_);
v___x_513_ = v_reuseFailAlloc_514_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
return v___x_513_;
}
}
}
}
else
{
lean_object* v_a_516_; lean_object* v___x_518_; uint8_t v_isShared_519_; uint8_t v_isSharedCheck_523_; 
lean_dec_ref(v___x_474_);
lean_del_object(v___x_470_);
lean_dec(v_snd_468_);
lean_dec(v_fst_467_);
v_a_516_ = lean_ctor_get(v___x_476_, 0);
v_isSharedCheck_523_ = !lean_is_exclusive(v___x_476_);
if (v_isSharedCheck_523_ == 0)
{
v___x_518_ = v___x_476_;
v_isShared_519_ = v_isSharedCheck_523_;
goto v_resetjp_517_;
}
else
{
lean_inc(v_a_516_);
lean_dec(v___x_476_);
v___x_518_ = lean_box(0);
v_isShared_519_ = v_isSharedCheck_523_;
goto v_resetjp_517_;
}
v_resetjp_517_:
{
lean_object* v___x_521_; 
if (v_isShared_519_ == 0)
{
v___x_521_ = v___x_518_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v_a_516_);
v___x_521_ = v_reuseFailAlloc_522_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
return v___x_521_;
}
}
}
}
else
{
lean_object* v___x_524_; lean_object* v___x_526_; 
lean_dec_ref(v___x_474_);
lean_del_object(v___x_470_);
lean_dec(v_snd_468_);
lean_dec(v_fst_467_);
v___x_524_ = lean_box(0);
if (v_isShared_466_ == 0)
{
lean_ctor_set(v___x_465_, 0, v___x_524_);
v___x_526_ = v___x_465_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v___x_524_);
v___x_526_ = v_reuseFailAlloc_527_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
return v___x_526_;
}
}
}
}
}
else
{
lean_object* v_a_530_; lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_537_; 
v_a_530_ = lean_ctor_get(v___x_462_, 0);
v_isSharedCheck_537_ = !lean_is_exclusive(v___x_462_);
if (v_isSharedCheck_537_ == 0)
{
v___x_532_ = v___x_462_;
v_isShared_533_ = v_isSharedCheck_537_;
goto v_resetjp_531_;
}
else
{
lean_inc(v_a_530_);
lean_dec(v___x_462_);
v___x_532_ = lean_box(0);
v_isShared_533_ = v_isSharedCheck_537_;
goto v_resetjp_531_;
}
v_resetjp_531_:
{
lean_object* v___x_535_; 
if (v_isShared_533_ == 0)
{
v___x_535_ = v___x_532_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v_a_530_);
v___x_535_ = v_reuseFailAlloc_536_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
return v___x_535_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_input_456_ = stack[0].m_obj;
lean_object* v_a_457_ = stack[1].m_obj;
lean_object* v_a_458_ = stack[2].m_obj;
lean_object* v_a_459_ = stack[3].m_obj;
lean_object* v_a_460_ = stack[4].m_obj;
lean_object* v_res_538_;
v_res_538_ = l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f(v_input_456_, v_a_457_, v_a_458_, v_a_459_, v_a_460_);
stack->m_obj
 = v_res_538_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___boxed(lean_object* v_input_539_, lean_object* v_a_540_, lean_object* v_a_541_, lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_){
_start:
{
lean_object* v_res_545_; 
v_res_545_ = l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f(v_input_539_, v_a_540_, v_a_541_, v_a_542_, v_a_543_);
lean_dec(v_a_543_);
lean_dec_ref(v_a_542_);
lean_dec(v_a_541_);
lean_dec_ref(v_a_540_);
return v_res_545_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Arith_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Arith_Nat_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_AppBuilder(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Arith_Nat_Simp(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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

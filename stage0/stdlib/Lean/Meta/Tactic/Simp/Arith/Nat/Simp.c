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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Arith_Nat_toLinearCnstr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith___redArg(lean_object*, lean_object*);
lean_object* l_Nat_Linear_ExprCnstr_toPoly(lean_object*);
lean_object* l_Nat_Linear_PolyCnstr_norm(lean_object*);
uint8_t l_Nat_Linear_PolyCnstr_isUnsat(lean_object*);
uint8_t l_Nat_Linear_PolyCnstr_isValid(lean_object*);
lean_object* l_Nat_Linear_PolyCnstr_toExpr(lean_object*);
lean_object* l_Lean_Meta_Simp_Arith_Nat_toContextExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Nat_Linear_Expr_toPoly(lean_object*);
lean_object* l_Nat_Linear_Poly_norm(lean_object*);
lean_object* l_Nat_Linear_Poly_toExpr(lean_object*);
uint8_t l_Nat_Linear_instBEqExpr_beq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr(lean_object*);
lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(lean_object*, lean_object*);
lean_object* l_Lean_mkNatEq(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__0_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Linear"};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__1_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "ExprCnstr"};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__2 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__2_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "eq_of_toNormPoly_eq"};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__3 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(54, 114, 89, 174, 224, 251, 5, 100)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(57, 237, 130, 75, 136, 172, 225, 105)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__4_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__3_value),LEAN_SCALAR_PTR_LITERAL(27, 13, 52, 42, 204, 20, 168, 83)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__4 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__5;
static const lean_string_object l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "True"};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__6 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__6_value),LEAN_SCALAR_PTR_LITERAL(78, 21, 103, 131, 118, 13, 187, 164)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__7 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__7_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__8;
static const lean_string_object l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "eq_true_of_isValid"};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__9 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__9_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__10_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(54, 114, 89, 174, 224, 251, 5, 100)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__10_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(57, 237, 130, 75, 136, 172, 225, 105)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__10_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__9_value),LEAN_SCALAR_PTR_LITERAL(95, 37, 226, 130, 224, 94, 123, 63)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__10 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__10_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__11;
static const lean_string_object l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "False"};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__12 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__12_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__12_value),LEAN_SCALAR_PTR_LITERAL(227, 122, 176, 177, 50, 175, 152, 12)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__13 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__13_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__14;
static const lean_string_object l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "eq_false_of_isUnsat"};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__15 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__15_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__16_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(54, 114, 89, 174, 224, 251, 5, 100)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__16_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(57, 237, 130, 75, 136, 172, 225, 105)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__16_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__15_value),LEAN_SCALAR_PTR_LITERAL(36, 37, 117, 209, 20, 7, 0, 148)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__16 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__16_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__17;
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
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(54, 114, 89, 174, 224, 251, 5, 100)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(132, 220, 159, 13, 188, 193, 50, 74)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__3_value),LEAN_SCALAR_PTR_LITERAL(186, 39, 67, 138, 229, 80, 178, 141)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__5(void){
_start:
{
lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_10_ = lean_box(0);
v___x_11_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__4));
v___x_12_ = l_Lean_mkConst(v___x_11_, v___x_10_);
return v___x_12_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__8(void){
_start:
{
lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; 
v___x_16_ = lean_box(0);
v___x_17_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__7));
v___x_18_ = l_Lean_mkConst(v___x_17_, v___x_16_);
return v___x_18_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__11(void){
_start:
{
lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; 
v___x_25_ = lean_box(0);
v___x_26_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__10));
v___x_27_ = l_Lean_mkConst(v___x_26_, v___x_25_);
return v___x_27_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__14(void){
_start:
{
lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; 
v___x_31_ = lean_box(0);
v___x_32_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__13));
v___x_33_ = l_Lean_mkConst(v___x_32_, v___x_31_);
return v___x_33_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__17(void){
_start:
{
lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; 
v___x_40_ = lean_box(0);
v___x_41_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__16));
v___x_42_ = l_Lean_mkConst(v___x_41_, v___x_40_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f(lean_object* v_e_43_, lean_object* v_a_44_, lean_object* v_a_45_, lean_object* v_a_46_, lean_object* v_a_47_){
_start:
{
lean_object* v___x_49_; 
v___x_49_ = l_Lean_Meta_Simp_Arith_Nat_toLinearCnstr_x3f(v_e_43_, v_a_44_, v_a_45_, v_a_46_, v_a_47_);
if (lean_obj_tag(v___x_49_) == 0)
{
lean_object* v_a_50_; lean_object* v___x_52_; uint8_t v_isShared_53_; uint8_t v_isSharedCheck_194_; 
v_a_50_ = lean_ctor_get(v___x_49_, 0);
v_isSharedCheck_194_ = !lean_is_exclusive(v___x_49_);
if (v_isSharedCheck_194_ == 0)
{
v___x_52_ = v___x_49_;
v_isShared_53_ = v_isSharedCheck_194_;
goto v_resetjp_51_;
}
else
{
lean_inc(v_a_50_);
lean_dec(v___x_49_);
v___x_52_ = lean_box(0);
v_isShared_53_ = v_isSharedCheck_194_;
goto v_resetjp_51_;
}
v_resetjp_51_:
{
if (lean_obj_tag(v_a_50_) == 1)
{
lean_object* v_val_54_; lean_object* v___x_56_; uint8_t v_isShared_57_; uint8_t v_isSharedCheck_189_; 
lean_del_object(v___x_52_);
v_val_54_ = lean_ctor_get(v_a_50_, 0);
v_isSharedCheck_189_ = !lean_is_exclusive(v_a_50_);
if (v_isSharedCheck_189_ == 0)
{
v___x_56_ = v_a_50_;
v_isShared_57_ = v_isSharedCheck_189_;
goto v_resetjp_55_;
}
else
{
lean_inc(v_val_54_);
lean_dec(v_a_50_);
v___x_56_ = lean_box(0);
v_isShared_57_ = v_isSharedCheck_189_;
goto v_resetjp_55_;
}
v_resetjp_55_:
{
lean_object* v_fst_58_; lean_object* v_snd_59_; lean_object* v___x_61_; uint8_t v_isShared_62_; uint8_t v_isSharedCheck_188_; 
v_fst_58_ = lean_ctor_get(v_val_54_, 0);
v_snd_59_ = lean_ctor_get(v_val_54_, 1);
v_isSharedCheck_188_ = !lean_is_exclusive(v_val_54_);
if (v_isSharedCheck_188_ == 0)
{
v___x_61_ = v_val_54_;
v_isShared_62_ = v_isSharedCheck_188_;
goto v_resetjp_60_;
}
else
{
lean_inc(v_snd_59_);
lean_inc(v_fst_58_);
lean_dec(v_val_54_);
v___x_61_ = lean_box(0);
v_isShared_62_ = v_isSharedCheck_188_;
goto v_resetjp_60_;
}
v_resetjp_60_:
{
lean_object* v___x_63_; 
lean_inc(v_fst_58_);
v___x_63_ = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith___redArg(v_snd_59_, v_fst_58_);
if (lean_obj_tag(v___x_63_) == 0)
{
lean_object* v_a_64_; lean_object* v___x_65_; lean_object* v___x_66_; uint8_t v___x_67_; 
v_a_64_ = lean_ctor_get(v___x_63_, 0);
lean_inc(v_a_64_);
lean_dec_ref(v___x_63_);
lean_inc(v_fst_58_);
v___x_65_ = l_Nat_Linear_ExprCnstr_toPoly(v_fst_58_);
v___x_66_ = l_Nat_Linear_PolyCnstr_norm(v___x_65_);
v___x_67_ = l_Nat_Linear_PolyCnstr_isUnsat(v___x_66_);
if (v___x_67_ == 0)
{
uint8_t v___x_68_; 
v___x_68_ = l_Nat_Linear_PolyCnstr_isValid(v___x_66_);
if (v___x_68_ == 0)
{
lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_69_ = l_Nat_Linear_PolyCnstr_toExpr(v___x_66_);
lean_inc_ref(v___x_69_);
v___x_70_ = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith___redArg(v_snd_59_, v___x_69_);
if (lean_obj_tag(v___x_70_) == 0)
{
lean_object* v_a_71_; lean_object* v___x_73_; uint8_t v_isShared_74_; uint8_t v_isSharedCheck_111_; 
v_a_71_ = lean_ctor_get(v___x_70_, 0);
v_isSharedCheck_111_ = !lean_is_exclusive(v___x_70_);
if (v_isSharedCheck_111_ == 0)
{
v___x_73_ = v___x_70_;
v_isShared_74_ = v_isSharedCheck_111_;
goto v_resetjp_72_;
}
else
{
lean_inc(v_a_71_);
lean_dec(v___x_70_);
v___x_73_ = lean_box(0);
v_isShared_74_ = v_isSharedCheck_111_;
goto v_resetjp_72_;
}
v_resetjp_72_:
{
uint8_t v___x_106_; 
v___x_106_ = lean_expr_eqv(v_a_71_, v_a_64_);
if (v___x_106_ == 0)
{
lean_del_object(v___x_73_);
goto v___jp_75_;
}
else
{
if (v___x_68_ == 0)
{
lean_object* v___x_107_; lean_object* v___x_109_; 
lean_dec(v_a_71_);
lean_dec_ref(v___x_69_);
lean_dec(v_a_64_);
lean_del_object(v___x_61_);
lean_dec(v_snd_59_);
lean_dec(v_fst_58_);
lean_del_object(v___x_56_);
v___x_107_ = lean_box(0);
if (v_isShared_74_ == 0)
{
lean_ctor_set(v___x_73_, 0, v___x_107_);
v___x_109_ = v___x_73_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_110_; 
v_reuseFailAlloc_110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_110_, 0, v___x_107_);
v___x_109_ = v_reuseFailAlloc_110_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
return v___x_109_;
}
}
else
{
lean_del_object(v___x_73_);
goto v___jp_75_;
}
}
v___jp_75_:
{
lean_object* v___x_76_; 
v___x_76_ = l_Lean_Meta_Simp_Arith_Nat_toContextExpr(v_snd_59_, v_a_44_, v_a_45_, v_a_46_, v_a_47_);
if (lean_obj_tag(v___x_76_) == 0)
{
lean_object* v_a_77_; lean_object* v___x_79_; uint8_t v_isShared_80_; uint8_t v_isSharedCheck_97_; 
v_a_77_ = lean_ctor_get(v___x_76_, 0);
v_isSharedCheck_97_ = !lean_is_exclusive(v___x_76_);
if (v_isSharedCheck_97_ == 0)
{
v___x_79_ = v___x_76_;
v_isShared_80_ = v_isSharedCheck_97_;
goto v_resetjp_78_;
}
else
{
lean_inc(v_a_77_);
lean_dec(v___x_76_);
v___x_79_ = lean_box(0);
v_isShared_80_ = v_isSharedCheck_97_;
goto v_resetjp_78_;
}
v_resetjp_78_:
{
lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_89_; 
v___x_81_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__5, &l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__5_once, _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__5);
v___x_82_ = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr(v_fst_58_);
v___x_83_ = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr(v___x_69_);
v___x_84_ = l_Lean_eagerReflBoolTrue;
v___x_85_ = l_Lean_mkApp4(v___x_81_, v_a_77_, v___x_82_, v___x_83_, v___x_84_);
lean_inc(v_a_71_);
v___x_86_ = l_Lean_mkPropEq(v_a_64_, v_a_71_);
v___x_87_ = l_Lean_Meta_mkExpectedPropHint(v___x_85_, v___x_86_);
if (v_isShared_62_ == 0)
{
lean_ctor_set(v___x_61_, 1, v___x_87_);
lean_ctor_set(v___x_61_, 0, v_a_71_);
v___x_89_ = v___x_61_;
goto v_reusejp_88_;
}
else
{
lean_object* v_reuseFailAlloc_96_; 
v_reuseFailAlloc_96_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_96_, 0, v_a_71_);
lean_ctor_set(v_reuseFailAlloc_96_, 1, v___x_87_);
v___x_89_ = v_reuseFailAlloc_96_;
goto v_reusejp_88_;
}
v_reusejp_88_:
{
lean_object* v___x_91_; 
if (v_isShared_57_ == 0)
{
lean_ctor_set(v___x_56_, 0, v___x_89_);
v___x_91_ = v___x_56_;
goto v_reusejp_90_;
}
else
{
lean_object* v_reuseFailAlloc_95_; 
v_reuseFailAlloc_95_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_95_, 0, v___x_89_);
v___x_91_ = v_reuseFailAlloc_95_;
goto v_reusejp_90_;
}
v_reusejp_90_:
{
lean_object* v___x_93_; 
if (v_isShared_80_ == 0)
{
lean_ctor_set(v___x_79_, 0, v___x_91_);
v___x_93_ = v___x_79_;
goto v_reusejp_92_;
}
else
{
lean_object* v_reuseFailAlloc_94_; 
v_reuseFailAlloc_94_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_94_, 0, v___x_91_);
v___x_93_ = v_reuseFailAlloc_94_;
goto v_reusejp_92_;
}
v_reusejp_92_:
{
return v___x_93_;
}
}
}
}
}
else
{
lean_object* v_a_98_; lean_object* v___x_100_; uint8_t v_isShared_101_; uint8_t v_isSharedCheck_105_; 
lean_dec(v_a_71_);
lean_dec_ref(v___x_69_);
lean_dec(v_a_64_);
lean_del_object(v___x_61_);
lean_dec(v_fst_58_);
lean_del_object(v___x_56_);
v_a_98_ = lean_ctor_get(v___x_76_, 0);
v_isSharedCheck_105_ = !lean_is_exclusive(v___x_76_);
if (v_isSharedCheck_105_ == 0)
{
v___x_100_ = v___x_76_;
v_isShared_101_ = v_isSharedCheck_105_;
goto v_resetjp_99_;
}
else
{
lean_inc(v_a_98_);
lean_dec(v___x_76_);
v___x_100_ = lean_box(0);
v_isShared_101_ = v_isSharedCheck_105_;
goto v_resetjp_99_;
}
v_resetjp_99_:
{
lean_object* v___x_103_; 
if (v_isShared_101_ == 0)
{
v___x_103_ = v___x_100_;
goto v_reusejp_102_;
}
else
{
lean_object* v_reuseFailAlloc_104_; 
v_reuseFailAlloc_104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_104_, 0, v_a_98_);
v___x_103_ = v_reuseFailAlloc_104_;
goto v_reusejp_102_;
}
v_reusejp_102_:
{
return v___x_103_;
}
}
}
}
}
}
else
{
lean_object* v_a_112_; lean_object* v___x_114_; uint8_t v_isShared_115_; uint8_t v_isSharedCheck_119_; 
lean_dec_ref(v___x_69_);
lean_dec(v_a_64_);
lean_del_object(v___x_61_);
lean_dec(v_snd_59_);
lean_dec(v_fst_58_);
lean_del_object(v___x_56_);
v_a_112_ = lean_ctor_get(v___x_70_, 0);
v_isSharedCheck_119_ = !lean_is_exclusive(v___x_70_);
if (v_isSharedCheck_119_ == 0)
{
v___x_114_ = v___x_70_;
v_isShared_115_ = v_isSharedCheck_119_;
goto v_resetjp_113_;
}
else
{
lean_inc(v_a_112_);
lean_dec(v___x_70_);
v___x_114_ = lean_box(0);
v_isShared_115_ = v_isSharedCheck_119_;
goto v_resetjp_113_;
}
v_resetjp_113_:
{
lean_object* v___x_117_; 
if (v_isShared_115_ == 0)
{
v___x_117_ = v___x_114_;
goto v_reusejp_116_;
}
else
{
lean_object* v_reuseFailAlloc_118_; 
v_reuseFailAlloc_118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_118_, 0, v_a_112_);
v___x_117_ = v_reuseFailAlloc_118_;
goto v_reusejp_116_;
}
v_reusejp_116_:
{
return v___x_117_;
}
}
}
}
else
{
lean_object* v___x_120_; 
lean_dec_ref(v___x_66_);
v___x_120_ = l_Lean_Meta_Simp_Arith_Nat_toContextExpr(v_snd_59_, v_a_44_, v_a_45_, v_a_46_, v_a_47_);
if (lean_obj_tag(v___x_120_) == 0)
{
lean_object* v_a_121_; lean_object* v___x_123_; uint8_t v_isShared_124_; uint8_t v_isSharedCheck_141_; 
v_a_121_ = lean_ctor_get(v___x_120_, 0);
v_isSharedCheck_141_ = !lean_is_exclusive(v___x_120_);
if (v_isSharedCheck_141_ == 0)
{
v___x_123_ = v___x_120_;
v_isShared_124_ = v_isSharedCheck_141_;
goto v_resetjp_122_;
}
else
{
lean_inc(v_a_121_);
lean_dec(v___x_120_);
v___x_123_ = lean_box(0);
v_isShared_124_ = v_isSharedCheck_141_;
goto v_resetjp_122_;
}
v_resetjp_122_:
{
lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_133_; 
v___x_125_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__8, &l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__8_once, _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__8);
v___x_126_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__11, &l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__11_once, _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__11);
v___x_127_ = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr(v_fst_58_);
v___x_128_ = l_Lean_eagerReflBoolTrue;
v___x_129_ = l_Lean_mkApp3(v___x_126_, v_a_121_, v___x_127_, v___x_128_);
v___x_130_ = l_Lean_mkPropEq(v_a_64_, v___x_125_);
v___x_131_ = l_Lean_Meta_mkExpectedPropHint(v___x_129_, v___x_130_);
if (v_isShared_62_ == 0)
{
lean_ctor_set(v___x_61_, 1, v___x_131_);
lean_ctor_set(v___x_61_, 0, v___x_125_);
v___x_133_ = v___x_61_;
goto v_reusejp_132_;
}
else
{
lean_object* v_reuseFailAlloc_140_; 
v_reuseFailAlloc_140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_140_, 0, v___x_125_);
lean_ctor_set(v_reuseFailAlloc_140_, 1, v___x_131_);
v___x_133_ = v_reuseFailAlloc_140_;
goto v_reusejp_132_;
}
v_reusejp_132_:
{
lean_object* v___x_135_; 
if (v_isShared_57_ == 0)
{
lean_ctor_set(v___x_56_, 0, v___x_133_);
v___x_135_ = v___x_56_;
goto v_reusejp_134_;
}
else
{
lean_object* v_reuseFailAlloc_139_; 
v_reuseFailAlloc_139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_139_, 0, v___x_133_);
v___x_135_ = v_reuseFailAlloc_139_;
goto v_reusejp_134_;
}
v_reusejp_134_:
{
lean_object* v___x_137_; 
if (v_isShared_124_ == 0)
{
lean_ctor_set(v___x_123_, 0, v___x_135_);
v___x_137_ = v___x_123_;
goto v_reusejp_136_;
}
else
{
lean_object* v_reuseFailAlloc_138_; 
v_reuseFailAlloc_138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_138_, 0, v___x_135_);
v___x_137_ = v_reuseFailAlloc_138_;
goto v_reusejp_136_;
}
v_reusejp_136_:
{
return v___x_137_;
}
}
}
}
}
else
{
lean_object* v_a_142_; lean_object* v___x_144_; uint8_t v_isShared_145_; uint8_t v_isSharedCheck_149_; 
lean_dec(v_a_64_);
lean_del_object(v___x_61_);
lean_dec(v_fst_58_);
lean_del_object(v___x_56_);
v_a_142_ = lean_ctor_get(v___x_120_, 0);
v_isSharedCheck_149_ = !lean_is_exclusive(v___x_120_);
if (v_isSharedCheck_149_ == 0)
{
v___x_144_ = v___x_120_;
v_isShared_145_ = v_isSharedCheck_149_;
goto v_resetjp_143_;
}
else
{
lean_inc(v_a_142_);
lean_dec(v___x_120_);
v___x_144_ = lean_box(0);
v_isShared_145_ = v_isSharedCheck_149_;
goto v_resetjp_143_;
}
v_resetjp_143_:
{
lean_object* v___x_147_; 
if (v_isShared_145_ == 0)
{
v___x_147_ = v___x_144_;
goto v_reusejp_146_;
}
else
{
lean_object* v_reuseFailAlloc_148_; 
v_reuseFailAlloc_148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_148_, 0, v_a_142_);
v___x_147_ = v_reuseFailAlloc_148_;
goto v_reusejp_146_;
}
v_reusejp_146_:
{
return v___x_147_;
}
}
}
}
}
else
{
lean_object* v___x_150_; 
lean_dec_ref(v___x_66_);
v___x_150_ = l_Lean_Meta_Simp_Arith_Nat_toContextExpr(v_snd_59_, v_a_44_, v_a_45_, v_a_46_, v_a_47_);
if (lean_obj_tag(v___x_150_) == 0)
{
lean_object* v_a_151_; lean_object* v___x_153_; uint8_t v_isShared_154_; uint8_t v_isSharedCheck_171_; 
v_a_151_ = lean_ctor_get(v___x_150_, 0);
v_isSharedCheck_171_ = !lean_is_exclusive(v___x_150_);
if (v_isSharedCheck_171_ == 0)
{
v___x_153_ = v___x_150_;
v_isShared_154_ = v_isSharedCheck_171_;
goto v_resetjp_152_;
}
else
{
lean_inc(v_a_151_);
lean_dec(v___x_150_);
v___x_153_ = lean_box(0);
v_isShared_154_ = v_isSharedCheck_171_;
goto v_resetjp_152_;
}
v_resetjp_152_:
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_163_; 
v___x_155_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__14, &l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__14_once, _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__14);
v___x_156_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__17, &l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__17_once, _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__17);
v___x_157_ = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr(v_fst_58_);
v___x_158_ = l_Lean_eagerReflBoolTrue;
v___x_159_ = l_Lean_mkApp3(v___x_156_, v_a_151_, v___x_157_, v___x_158_);
v___x_160_ = l_Lean_mkPropEq(v_a_64_, v___x_155_);
v___x_161_ = l_Lean_Meta_mkExpectedPropHint(v___x_159_, v___x_160_);
if (v_isShared_62_ == 0)
{
lean_ctor_set(v___x_61_, 1, v___x_161_);
lean_ctor_set(v___x_61_, 0, v___x_155_);
v___x_163_ = v___x_61_;
goto v_reusejp_162_;
}
else
{
lean_object* v_reuseFailAlloc_170_; 
v_reuseFailAlloc_170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v___x_155_);
lean_ctor_set(v_reuseFailAlloc_170_, 1, v___x_161_);
v___x_163_ = v_reuseFailAlloc_170_;
goto v_reusejp_162_;
}
v_reusejp_162_:
{
lean_object* v___x_165_; 
if (v_isShared_57_ == 0)
{
lean_ctor_set(v___x_56_, 0, v___x_163_);
v___x_165_ = v___x_56_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_169_; 
v_reuseFailAlloc_169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_169_, 0, v___x_163_);
v___x_165_ = v_reuseFailAlloc_169_;
goto v_reusejp_164_;
}
v_reusejp_164_:
{
lean_object* v___x_167_; 
if (v_isShared_154_ == 0)
{
lean_ctor_set(v___x_153_, 0, v___x_165_);
v___x_167_ = v___x_153_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_172_; lean_object* v___x_174_; uint8_t v_isShared_175_; uint8_t v_isSharedCheck_179_; 
lean_dec(v_a_64_);
lean_del_object(v___x_61_);
lean_dec(v_fst_58_);
lean_del_object(v___x_56_);
v_a_172_ = lean_ctor_get(v___x_150_, 0);
v_isSharedCheck_179_ = !lean_is_exclusive(v___x_150_);
if (v_isSharedCheck_179_ == 0)
{
v___x_174_ = v___x_150_;
v_isShared_175_ = v_isSharedCheck_179_;
goto v_resetjp_173_;
}
else
{
lean_inc(v_a_172_);
lean_dec(v___x_150_);
v___x_174_ = lean_box(0);
v_isShared_175_ = v_isSharedCheck_179_;
goto v_resetjp_173_;
}
v_resetjp_173_:
{
lean_object* v___x_177_; 
if (v_isShared_175_ == 0)
{
v___x_177_ = v___x_174_;
goto v_reusejp_176_;
}
else
{
lean_object* v_reuseFailAlloc_178_; 
v_reuseFailAlloc_178_ = lean_alloc_ctor(1, 1, 0);
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
}
}
else
{
lean_object* v_a_180_; lean_object* v___x_182_; uint8_t v_isShared_183_; uint8_t v_isSharedCheck_187_; 
lean_del_object(v___x_61_);
lean_dec(v_snd_59_);
lean_dec(v_fst_58_);
lean_del_object(v___x_56_);
v_a_180_ = lean_ctor_get(v___x_63_, 0);
v_isSharedCheck_187_ = !lean_is_exclusive(v___x_63_);
if (v_isSharedCheck_187_ == 0)
{
v___x_182_ = v___x_63_;
v_isShared_183_ = v_isSharedCheck_187_;
goto v_resetjp_181_;
}
else
{
lean_inc(v_a_180_);
lean_dec(v___x_63_);
v___x_182_ = lean_box(0);
v_isShared_183_ = v_isSharedCheck_187_;
goto v_resetjp_181_;
}
v_resetjp_181_:
{
lean_object* v___x_185_; 
if (v_isShared_183_ == 0)
{
v___x_185_ = v___x_182_;
goto v_reusejp_184_;
}
else
{
lean_object* v_reuseFailAlloc_186_; 
v_reuseFailAlloc_186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_186_, 0, v_a_180_);
v___x_185_ = v_reuseFailAlloc_186_;
goto v_reusejp_184_;
}
v_reusejp_184_:
{
return v___x_185_;
}
}
}
}
}
}
else
{
lean_object* v___x_190_; lean_object* v___x_192_; 
lean_dec(v_a_50_);
v___x_190_ = lean_box(0);
if (v_isShared_53_ == 0)
{
lean_ctor_set(v___x_52_, 0, v___x_190_);
v___x_192_ = v___x_52_;
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
}
else
{
lean_object* v_a_195_; lean_object* v___x_197_; uint8_t v_isShared_198_; uint8_t v_isSharedCheck_202_; 
v_a_195_ = lean_ctor_get(v___x_49_, 0);
v_isSharedCheck_202_ = !lean_is_exclusive(v___x_49_);
if (v_isSharedCheck_202_ == 0)
{
v___x_197_ = v___x_49_;
v_isShared_198_ = v_isSharedCheck_202_;
goto v_resetjp_196_;
}
else
{
lean_inc(v_a_195_);
lean_dec(v___x_49_);
v___x_197_ = lean_box(0);
v_isShared_198_ = v_isSharedCheck_202_;
goto v_resetjp_196_;
}
v_resetjp_196_:
{
lean_object* v___x_200_; 
if (v_isShared_198_ == 0)
{
v___x_200_ = v___x_197_;
goto v_reusejp_199_;
}
else
{
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_201_, 0, v_a_195_);
v___x_200_ = v_reuseFailAlloc_201_;
goto v_reusejp_199_;
}
v_reusejp_199_:
{
return v___x_200_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___boxed(lean_object* v_e_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f(v_e_203_, v_a_204_, v_a_205_, v_a_206_, v_a_207_);
lean_dec(v_a_207_);
lean_dec_ref(v_a_206_);
lean_dec(v_a_205_);
lean_dec_ref(v_a_204_);
return v_res_209_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__3(void){
_start:
{
lean_object* v___x_215_; lean_object* v___x_216_; 
v___x_215_ = lean_box(0);
v___x_216_ = l_Lean_Level_succ___override(v___x_215_);
return v___x_216_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__4(void){
_start:
{
lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; 
v___x_217_ = lean_box(0);
v___x_218_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__3, &l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__3_once, _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__3);
v___x_219_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_219_, 0, v___x_218_);
lean_ctor_set(v___x_219_, 1, v___x_217_);
return v___x_219_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__5(void){
_start:
{
lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_220_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__4, &l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__4_once, _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__4);
v___x_221_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__2));
v___x_222_ = l_Lean_mkConst(v___x_221_, v___x_220_);
return v___x_222_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__6(void){
_start:
{
lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_223_ = lean_box(0);
v___x_224_ = l_Lean_mkSort(v___x_223_);
return v___x_224_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__22(void){
_start:
{
lean_object* v___x_250_; lean_object* v___x_251_; 
v___x_250_ = lean_unsigned_to_nat(1u);
v___x_251_ = l_Lean_mkNatLit(v___x_250_);
return v___x_251_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__25(void){
_start:
{
lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_256_ = lean_box(0);
v___x_257_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__24));
v___x_258_ = l_Lean_mkConst(v___x_257_, v___x_256_);
return v___x_258_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__28(void){
_start:
{
lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_263_ = lean_box(0);
v___x_264_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__27));
v___x_265_ = l_Lean_mkConst(v___x_264_, v___x_263_);
return v___x_265_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__31(void){
_start:
{
lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_270_ = lean_box(0);
v___x_271_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__30));
v___x_272_ = l_Lean_mkConst(v___x_271_, v___x_270_);
return v___x_272_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__34(void){
_start:
{
lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_277_ = lean_box(0);
v___x_278_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__33));
v___x_279_ = l_Lean_mkConst(v___x_278_, v___x_277_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f(lean_object* v_e_280_, lean_object* v_a_281_, lean_object* v_a_282_, lean_object* v_a_283_, lean_object* v_a_284_){
_start:
{
lean_object* v_val_290_; lean_object* v_h_u2081_291_; lean_object* v___y_292_; lean_object* v___y_293_; lean_object* v___y_294_; lean_object* v___y_295_; lean_object* v___x_330_; lean_object* v___x_331_; uint8_t v___x_332_; 
v___x_330_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__8));
v___x_331_ = lean_unsigned_to_nat(1u);
v___x_332_ = l_Lean_Expr_isAppOfArity(v_e_280_, v___x_330_, v___x_331_);
if (v___x_332_ == 0)
{
lean_object* v___x_333_; 
v___x_333_ = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f(v_e_280_, v_a_281_, v_a_282_, v_a_283_, v_a_284_);
return v___x_333_;
}
else
{
lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_334_ = l_Lean_Expr_appArg_x21(v_e_280_);
v___x_335_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v___x_334_, v_a_282_);
if (lean_obj_tag(v___x_335_) == 0)
{
lean_object* v_a_336_; lean_object* v___x_337_; uint8_t v___x_338_; 
v_a_336_ = lean_ctor_get(v___x_335_, 0);
lean_inc(v_a_336_);
lean_dec_ref(v___x_335_);
v___x_337_ = l_Lean_Expr_cleanupAnnotations(v_a_336_);
v___x_338_ = l_Lean_Expr_isApp(v___x_337_);
if (v___x_338_ == 0)
{
lean_dec_ref(v___x_337_);
lean_dec_ref(v_e_280_);
goto v___jp_286_;
}
else
{
lean_object* v_arg_339_; lean_object* v___x_340_; uint8_t v___x_341_; 
v_arg_339_ = lean_ctor_get(v___x_337_, 1);
lean_inc_ref(v_arg_339_);
v___x_340_ = l_Lean_Expr_appFnCleanup___redArg(v___x_337_);
v___x_341_ = l_Lean_Expr_isApp(v___x_340_);
if (v___x_341_ == 0)
{
lean_dec_ref(v___x_340_);
lean_dec_ref(v_arg_339_);
lean_dec_ref(v_e_280_);
goto v___jp_286_;
}
else
{
lean_object* v_arg_342_; lean_object* v___x_343_; uint8_t v___x_344_; 
v_arg_342_ = lean_ctor_get(v___x_340_, 1);
lean_inc_ref(v_arg_342_);
v___x_343_ = l_Lean_Expr_appFnCleanup___redArg(v___x_340_);
v___x_344_ = l_Lean_Expr_isApp(v___x_343_);
if (v___x_344_ == 0)
{
lean_dec_ref(v___x_343_);
lean_dec_ref(v_arg_342_);
lean_dec_ref(v_arg_339_);
lean_dec_ref(v_e_280_);
goto v___jp_286_;
}
else
{
lean_object* v___x_345_; uint8_t v___x_346_; 
v___x_345_ = l_Lean_Expr_appFnCleanup___redArg(v___x_343_);
v___x_346_ = l_Lean_Expr_isApp(v___x_345_);
if (v___x_346_ == 0)
{
lean_dec_ref(v___x_345_);
lean_dec_ref(v_arg_342_);
lean_dec_ref(v_arg_339_);
lean_dec_ref(v_e_280_);
goto v___jp_286_;
}
else
{
lean_object* v_arg_347_; lean_object* v___x_348_; lean_object* v___x_349_; uint8_t v___x_350_; 
v_arg_347_ = lean_ctor_get(v___x_345_, 1);
lean_inc_ref(v_arg_347_);
v___x_348_ = l_Lean_Expr_appFnCleanup___redArg(v___x_345_);
v___x_349_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__11));
v___x_350_ = l_Lean_Expr_isConstOf(v___x_348_, v___x_349_);
if (v___x_350_ == 0)
{
lean_object* v___x_351_; uint8_t v___x_352_; 
v___x_351_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__14));
v___x_352_ = l_Lean_Expr_isConstOf(v___x_348_, v___x_351_);
if (v___x_352_ == 0)
{
lean_object* v___x_353_; uint8_t v___x_354_; 
v___x_353_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__17));
v___x_354_ = l_Lean_Expr_isConstOf(v___x_348_, v___x_353_);
if (v___x_354_ == 0)
{
lean_object* v___x_355_; uint8_t v___x_356_; 
v___x_355_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__20));
v___x_356_ = l_Lean_Expr_isConstOf(v___x_348_, v___x_355_);
lean_dec_ref(v___x_348_);
if (v___x_356_ == 0)
{
lean_dec_ref(v_arg_347_);
lean_dec_ref(v_arg_342_);
lean_dec_ref(v_arg_339_);
lean_dec_ref(v_e_280_);
goto v___jp_286_;
}
else
{
lean_object* v___x_357_; 
v___x_357_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_347_, v_a_282_);
if (lean_obj_tag(v___x_357_) == 0)
{
lean_object* v_a_358_; lean_object* v___x_359_; lean_object* v___x_360_; uint8_t v___x_361_; 
v_a_358_ = lean_ctor_get(v___x_357_, 0);
lean_inc(v_a_358_);
lean_dec_ref(v___x_357_);
v___x_359_ = l_Lean_Expr_cleanupAnnotations(v_a_358_);
v___x_360_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__21));
v___x_361_ = l_Lean_Expr_isConstOf(v___x_359_, v___x_360_);
lean_dec_ref(v___x_359_);
if (v___x_361_ == 0)
{
lean_dec_ref(v_arg_342_);
lean_dec_ref(v_arg_339_);
lean_dec_ref(v_e_280_);
goto v___jp_286_;
}
else
{
lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; 
v___x_362_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__22, &l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__22_once, _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__22);
lean_inc_ref(v_arg_339_);
v___x_363_ = l_Lean_mkNatAdd(v_arg_339_, v___x_362_);
lean_inc_ref(v_arg_342_);
v___x_364_ = l_Lean_mkNatLE(v___x_363_, v_arg_342_);
v___x_365_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__25, &l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__25_once, _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__25);
v___x_366_ = l_Lean_mkAppB(v___x_365_, v_arg_342_, v_arg_339_);
v_val_290_ = v___x_364_;
v_h_u2081_291_ = v___x_366_;
v___y_292_ = v_a_281_;
v___y_293_ = v_a_282_;
v___y_294_ = v_a_283_;
v___y_295_ = v_a_284_;
goto v___jp_289_;
}
}
else
{
lean_object* v_a_367_; lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_374_; 
lean_dec_ref(v_arg_342_);
lean_dec_ref(v_arg_339_);
lean_dec_ref(v_e_280_);
v_a_367_ = lean_ctor_get(v___x_357_, 0);
v_isSharedCheck_374_ = !lean_is_exclusive(v___x_357_);
if (v_isSharedCheck_374_ == 0)
{
v___x_369_ = v___x_357_;
v_isShared_370_ = v_isSharedCheck_374_;
goto v_resetjp_368_;
}
else
{
lean_inc(v_a_367_);
lean_dec(v___x_357_);
v___x_369_ = lean_box(0);
v_isShared_370_ = v_isSharedCheck_374_;
goto v_resetjp_368_;
}
v_resetjp_368_:
{
lean_object* v___x_372_; 
if (v_isShared_370_ == 0)
{
v___x_372_ = v___x_369_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v_a_367_);
v___x_372_ = v_reuseFailAlloc_373_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
return v___x_372_;
}
}
}
}
}
else
{
lean_object* v___x_375_; 
lean_dec_ref(v___x_348_);
v___x_375_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_347_, v_a_282_);
if (lean_obj_tag(v___x_375_) == 0)
{
lean_object* v_a_376_; lean_object* v___x_377_; lean_object* v___x_378_; uint8_t v___x_379_; 
v_a_376_ = lean_ctor_get(v___x_375_, 0);
lean_inc(v_a_376_);
lean_dec_ref(v___x_375_);
v___x_377_ = l_Lean_Expr_cleanupAnnotations(v_a_376_);
v___x_378_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__21));
v___x_379_ = l_Lean_Expr_isConstOf(v___x_377_, v___x_378_);
lean_dec_ref(v___x_377_);
if (v___x_379_ == 0)
{
lean_dec_ref(v_arg_342_);
lean_dec_ref(v_arg_339_);
lean_dec_ref(v_e_280_);
goto v___jp_286_;
}
else
{
lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; 
v___x_380_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__22, &l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__22_once, _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__22);
lean_inc_ref(v_arg_342_);
v___x_381_ = l_Lean_mkNatAdd(v_arg_342_, v___x_380_);
lean_inc_ref(v_arg_339_);
v___x_382_ = l_Lean_mkNatLE(v___x_381_, v_arg_339_);
v___x_383_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__28, &l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__28_once, _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__28);
v___x_384_ = l_Lean_mkAppB(v___x_383_, v_arg_342_, v_arg_339_);
v_val_290_ = v___x_382_;
v_h_u2081_291_ = v___x_384_;
v___y_292_ = v_a_281_;
v___y_293_ = v_a_282_;
v___y_294_ = v_a_283_;
v___y_295_ = v_a_284_;
goto v___jp_289_;
}
}
else
{
lean_object* v_a_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_392_; 
lean_dec_ref(v_arg_342_);
lean_dec_ref(v_arg_339_);
lean_dec_ref(v_e_280_);
v_a_385_ = lean_ctor_get(v___x_375_, 0);
v_isSharedCheck_392_ = !lean_is_exclusive(v___x_375_);
if (v_isSharedCheck_392_ == 0)
{
v___x_387_ = v___x_375_;
v_isShared_388_ = v_isSharedCheck_392_;
goto v_resetjp_386_;
}
else
{
lean_inc(v_a_385_);
lean_dec(v___x_375_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_392_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
lean_object* v___x_390_; 
if (v_isShared_388_ == 0)
{
v___x_390_ = v___x_387_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v_a_385_);
v___x_390_ = v_reuseFailAlloc_391_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
return v___x_390_;
}
}
}
}
}
else
{
lean_object* v___x_393_; 
lean_dec_ref(v___x_348_);
v___x_393_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_347_, v_a_282_);
if (lean_obj_tag(v___x_393_) == 0)
{
lean_object* v_a_394_; lean_object* v___x_395_; lean_object* v___x_396_; uint8_t v___x_397_; 
v_a_394_ = lean_ctor_get(v___x_393_, 0);
lean_inc(v_a_394_);
lean_dec_ref(v___x_393_);
v___x_395_ = l_Lean_Expr_cleanupAnnotations(v_a_394_);
v___x_396_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__21));
v___x_397_ = l_Lean_Expr_isConstOf(v___x_395_, v___x_396_);
lean_dec_ref(v___x_395_);
if (v___x_397_ == 0)
{
lean_dec_ref(v_arg_342_);
lean_dec_ref(v_arg_339_);
lean_dec_ref(v_e_280_);
goto v___jp_286_;
}
else
{
lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; 
lean_inc_ref(v_arg_342_);
lean_inc_ref(v_arg_339_);
v___x_398_ = l_Lean_mkNatLE(v_arg_339_, v_arg_342_);
v___x_399_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__31, &l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__31_once, _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__31);
v___x_400_ = l_Lean_mkAppB(v___x_399_, v_arg_342_, v_arg_339_);
v_val_290_ = v___x_398_;
v_h_u2081_291_ = v___x_400_;
v___y_292_ = v_a_281_;
v___y_293_ = v_a_282_;
v___y_294_ = v_a_283_;
v___y_295_ = v_a_284_;
goto v___jp_289_;
}
}
else
{
lean_object* v_a_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_408_; 
lean_dec_ref(v_arg_342_);
lean_dec_ref(v_arg_339_);
lean_dec_ref(v_e_280_);
v_a_401_ = lean_ctor_get(v___x_393_, 0);
v_isSharedCheck_408_ = !lean_is_exclusive(v___x_393_);
if (v_isSharedCheck_408_ == 0)
{
v___x_403_ = v___x_393_;
v_isShared_404_ = v_isSharedCheck_408_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_a_401_);
lean_dec(v___x_393_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_408_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
lean_object* v___x_406_; 
if (v_isShared_404_ == 0)
{
v___x_406_ = v___x_403_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(1, 1, 0);
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
}
}
else
{
lean_object* v___x_409_; 
lean_dec_ref(v___x_348_);
v___x_409_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_347_, v_a_282_);
if (lean_obj_tag(v___x_409_) == 0)
{
lean_object* v_a_410_; lean_object* v___x_411_; lean_object* v___x_412_; uint8_t v___x_413_; 
v_a_410_ = lean_ctor_get(v___x_409_, 0);
lean_inc(v_a_410_);
lean_dec_ref(v___x_409_);
v___x_411_ = l_Lean_Expr_cleanupAnnotations(v_a_410_);
v___x_412_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__21));
v___x_413_ = l_Lean_Expr_isConstOf(v___x_411_, v___x_412_);
lean_dec_ref(v___x_411_);
if (v___x_413_ == 0)
{
lean_dec_ref(v_arg_342_);
lean_dec_ref(v_arg_339_);
lean_dec_ref(v_e_280_);
goto v___jp_286_;
}
else
{
lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; 
lean_inc_ref(v_arg_339_);
lean_inc_ref(v_arg_342_);
v___x_414_ = l_Lean_mkNatLE(v_arg_342_, v_arg_339_);
v___x_415_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__34, &l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__34_once, _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__34);
v___x_416_ = l_Lean_mkAppB(v___x_415_, v_arg_342_, v_arg_339_);
v_val_290_ = v___x_414_;
v_h_u2081_291_ = v___x_416_;
v___y_292_ = v_a_281_;
v___y_293_ = v_a_282_;
v___y_294_ = v_a_283_;
v___y_295_ = v_a_284_;
goto v___jp_289_;
}
}
else
{
lean_object* v_a_417_; lean_object* v___x_419_; uint8_t v_isShared_420_; uint8_t v_isSharedCheck_424_; 
lean_dec_ref(v_arg_342_);
lean_dec_ref(v_arg_339_);
lean_dec_ref(v_e_280_);
v_a_417_ = lean_ctor_get(v___x_409_, 0);
v_isSharedCheck_424_ = !lean_is_exclusive(v___x_409_);
if (v_isSharedCheck_424_ == 0)
{
v___x_419_ = v___x_409_;
v_isShared_420_ = v_isSharedCheck_424_;
goto v_resetjp_418_;
}
else
{
lean_inc(v_a_417_);
lean_dec(v___x_409_);
v___x_419_ = lean_box(0);
v_isShared_420_ = v_isSharedCheck_424_;
goto v_resetjp_418_;
}
v_resetjp_418_:
{
lean_object* v___x_422_; 
if (v_isShared_420_ == 0)
{
v___x_422_ = v___x_419_;
goto v_reusejp_421_;
}
else
{
lean_object* v_reuseFailAlloc_423_; 
v_reuseFailAlloc_423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_423_, 0, v_a_417_);
v___x_422_ = v_reuseFailAlloc_423_;
goto v_reusejp_421_;
}
v_reusejp_421_:
{
return v___x_422_;
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
lean_object* v_a_425_; lean_object* v___x_427_; uint8_t v_isShared_428_; uint8_t v_isSharedCheck_432_; 
lean_dec_ref(v_e_280_);
v_a_425_ = lean_ctor_get(v___x_335_, 0);
v_isSharedCheck_432_ = !lean_is_exclusive(v___x_335_);
if (v_isSharedCheck_432_ == 0)
{
v___x_427_ = v___x_335_;
v_isShared_428_ = v_isSharedCheck_432_;
goto v_resetjp_426_;
}
else
{
lean_inc(v_a_425_);
lean_dec(v___x_335_);
v___x_427_ = lean_box(0);
v_isShared_428_ = v_isSharedCheck_432_;
goto v_resetjp_426_;
}
v_resetjp_426_:
{
lean_object* v___x_430_; 
if (v_isShared_428_ == 0)
{
v___x_430_ = v___x_427_;
goto v_reusejp_429_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v_a_425_);
v___x_430_ = v_reuseFailAlloc_431_;
goto v_reusejp_429_;
}
v_reusejp_429_:
{
return v___x_430_;
}
}
}
}
v___jp_286_:
{
lean_object* v___x_287_; lean_object* v___x_288_; 
v___x_287_ = lean_box(0);
v___x_288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_288_, 0, v___x_287_);
return v___x_288_;
}
v___jp_289_:
{
lean_object* v___x_296_; 
lean_inc_ref(v_val_290_);
v___x_296_ = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f(v_val_290_, v___y_292_, v___y_293_, v___y_294_, v___y_295_);
if (lean_obj_tag(v___x_296_) == 0)
{
lean_object* v_a_297_; lean_object* v___x_299_; uint8_t v_isShared_300_; uint8_t v_isSharedCheck_329_; 
v_a_297_ = lean_ctor_get(v___x_296_, 0);
v_isSharedCheck_329_ = !lean_is_exclusive(v___x_296_);
if (v_isSharedCheck_329_ == 0)
{
v___x_299_ = v___x_296_;
v_isShared_300_ = v_isSharedCheck_329_;
goto v_resetjp_298_;
}
else
{
lean_inc(v_a_297_);
lean_dec(v___x_296_);
v___x_299_ = lean_box(0);
v_isShared_300_ = v_isSharedCheck_329_;
goto v_resetjp_298_;
}
v_resetjp_298_:
{
if (lean_obj_tag(v_a_297_) == 1)
{
lean_object* v_val_301_; lean_object* v___x_303_; uint8_t v_isShared_304_; uint8_t v_isSharedCheck_323_; 
v_val_301_ = lean_ctor_get(v_a_297_, 0);
v_isSharedCheck_323_ = !lean_is_exclusive(v_a_297_);
if (v_isSharedCheck_323_ == 0)
{
v___x_303_ = v_a_297_;
v_isShared_304_ = v_isSharedCheck_323_;
goto v_resetjp_302_;
}
else
{
lean_inc(v_val_301_);
lean_dec(v_a_297_);
v___x_303_ = lean_box(0);
v_isShared_304_ = v_isSharedCheck_323_;
goto v_resetjp_302_;
}
v_resetjp_302_:
{
lean_object* v_fst_305_; lean_object* v_snd_306_; lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_322_; 
v_fst_305_ = lean_ctor_get(v_val_301_, 0);
v_snd_306_ = lean_ctor_get(v_val_301_, 1);
v_isSharedCheck_322_ = !lean_is_exclusive(v_val_301_);
if (v_isSharedCheck_322_ == 0)
{
v___x_308_ = v_val_301_;
v_isShared_309_ = v_isSharedCheck_322_;
goto v_resetjp_307_;
}
else
{
lean_inc(v_snd_306_);
lean_inc(v_fst_305_);
lean_dec(v_val_301_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_322_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_314_; 
v___x_310_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__5, &l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__5_once, _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__5);
v___x_311_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__6, &l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__6_once, _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__6);
lean_inc(v_fst_305_);
v___x_312_ = l_Lean_mkApp6(v___x_310_, v___x_311_, v_e_280_, v_val_290_, v_fst_305_, v_h_u2081_291_, v_snd_306_);
if (v_isShared_309_ == 0)
{
lean_ctor_set(v___x_308_, 1, v___x_312_);
v___x_314_ = v___x_308_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_321_; 
v_reuseFailAlloc_321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_321_, 0, v_fst_305_);
lean_ctor_set(v_reuseFailAlloc_321_, 1, v___x_312_);
v___x_314_ = v_reuseFailAlloc_321_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
lean_object* v___x_316_; 
if (v_isShared_304_ == 0)
{
lean_ctor_set(v___x_303_, 0, v___x_314_);
v___x_316_ = v___x_303_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v___x_314_);
v___x_316_ = v_reuseFailAlloc_320_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
lean_object* v___x_318_; 
if (v_isShared_300_ == 0)
{
lean_ctor_set(v___x_299_, 0, v___x_316_);
v___x_318_ = v___x_299_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v___x_316_);
v___x_318_ = v_reuseFailAlloc_319_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
return v___x_318_;
}
}
}
}
}
}
else
{
lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_327_; 
lean_dec(v_a_297_);
lean_dec_ref(v_e_280_);
v___x_324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_324_, 0, v_val_290_);
lean_ctor_set(v___x_324_, 1, v_h_u2081_291_);
v___x_325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_325_, 0, v___x_324_);
if (v_isShared_300_ == 0)
{
lean_ctor_set(v___x_299_, 0, v___x_325_);
v___x_327_ = v___x_299_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v___x_325_);
v___x_327_ = v_reuseFailAlloc_328_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
return v___x_327_;
}
}
}
}
else
{
lean_dec_ref(v_h_u2081_291_);
lean_dec_ref(v_val_290_);
lean_dec_ref(v_e_280_);
return v___x_296_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___boxed(lean_object* v_e_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_){
_start:
{
lean_object* v_res_439_; 
v_res_439_ = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f(v_e_433_, v_a_434_, v_a_435_, v_a_436_, v_a_437_);
lean_dec(v_a_437_);
lean_dec_ref(v_a_436_);
lean_dec(v_a_435_);
lean_dec_ref(v_a_434_);
return v_res_439_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___closed__2(void){
_start:
{
lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; 
v___x_446_ = lean_box(0);
v___x_447_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___closed__1));
v___x_448_ = l_Lean_mkConst(v___x_447_, v___x_446_);
return v___x_448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f(lean_object* v_input_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_){
_start:
{
lean_object* v___x_455_; 
v___x_455_ = l_Lean_Meta_Simp_Arith_Nat_toLinearExpr(v_input_449_, v_a_450_, v_a_451_, v_a_452_, v_a_453_);
if (lean_obj_tag(v___x_455_) == 0)
{
lean_object* v_a_456_; lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_522_; 
v_a_456_ = lean_ctor_get(v___x_455_, 0);
v_isSharedCheck_522_ = !lean_is_exclusive(v___x_455_);
if (v_isSharedCheck_522_ == 0)
{
v___x_458_ = v___x_455_;
v_isShared_459_ = v_isSharedCheck_522_;
goto v_resetjp_457_;
}
else
{
lean_inc(v_a_456_);
lean_dec(v___x_455_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_522_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
lean_object* v_fst_460_; lean_object* v_snd_461_; lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_521_; 
v_fst_460_ = lean_ctor_get(v_a_456_, 0);
v_snd_461_ = lean_ctor_get(v_a_456_, 1);
v_isSharedCheck_521_ = !lean_is_exclusive(v_a_456_);
if (v_isSharedCheck_521_ == 0)
{
v___x_463_ = v_a_456_;
v_isShared_464_ = v_isSharedCheck_521_;
goto v_resetjp_462_;
}
else
{
lean_inc(v_snd_461_);
lean_inc(v_fst_460_);
lean_dec(v_a_456_);
v___x_463_ = lean_box(0);
v_isShared_464_ = v_isSharedCheck_521_;
goto v_resetjp_462_;
}
v_resetjp_462_:
{
lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; uint8_t v___x_468_; 
v___x_465_ = l_Nat_Linear_Expr_toPoly(v_fst_460_);
v___x_466_ = l_Nat_Linear_Poly_norm(v___x_465_);
v___x_467_ = l_Nat_Linear_Poly_toExpr(v___x_466_);
v___x_468_ = l_Nat_Linear_instBEqExpr_beq(v___x_467_, v_fst_460_);
if (v___x_468_ == 0)
{
lean_object* v___x_469_; 
lean_del_object(v___x_458_);
lean_inc(v_snd_461_);
v___x_469_ = l_Lean_Meta_Simp_Arith_Nat_toContextExpr(v_snd_461_, v_a_450_, v_a_451_, v_a_452_, v_a_453_);
if (lean_obj_tag(v___x_469_) == 0)
{
lean_object* v_a_470_; lean_object* v___x_471_; lean_object* v___x_472_; 
v_a_470_ = lean_ctor_get(v___x_469_, 0);
lean_inc(v_a_470_);
lean_dec_ref(v___x_469_);
lean_inc(v_fst_460_);
v___x_471_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr(v_fst_460_);
v___x_472_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(v_snd_461_, v_fst_460_);
if (lean_obj_tag(v___x_472_) == 0)
{
lean_object* v_a_473_; lean_object* v___x_474_; lean_object* v___x_475_; 
v_a_473_ = lean_ctor_get(v___x_472_, 0);
lean_inc(v_a_473_);
lean_dec_ref(v___x_472_);
lean_inc_ref(v___x_467_);
v___x_474_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr(v___x_467_);
v___x_475_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(v_snd_461_, v___x_467_);
lean_dec(v_snd_461_);
if (lean_obj_tag(v___x_475_) == 0)
{
lean_object* v_a_476_; lean_object* v___x_478_; uint8_t v_isShared_479_; uint8_t v_isSharedCheck_492_; 
v_a_476_ = lean_ctor_get(v___x_475_, 0);
v_isSharedCheck_492_ = !lean_is_exclusive(v___x_475_);
if (v_isSharedCheck_492_ == 0)
{
v___x_478_ = v___x_475_;
v_isShared_479_ = v_isSharedCheck_492_;
goto v_resetjp_477_;
}
else
{
lean_inc(v_a_476_);
lean_dec(v___x_475_);
v___x_478_ = lean_box(0);
v_isShared_479_ = v_isSharedCheck_492_;
goto v_resetjp_477_;
}
v_resetjp_477_:
{
lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_486_; 
v___x_480_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___closed__2, &l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___closed__2_once, _init_l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___closed__2);
v___x_481_ = l_Lean_eagerReflBoolTrue;
v___x_482_ = l_Lean_mkApp4(v___x_480_, v_a_470_, v___x_471_, v___x_474_, v___x_481_);
lean_inc(v_a_476_);
v___x_483_ = l_Lean_mkNatEq(v_a_473_, v_a_476_);
v___x_484_ = l_Lean_Meta_mkExpectedPropHint(v___x_482_, v___x_483_);
if (v_isShared_464_ == 0)
{
lean_ctor_set(v___x_463_, 1, v___x_484_);
lean_ctor_set(v___x_463_, 0, v_a_476_);
v___x_486_ = v___x_463_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v_a_476_);
lean_ctor_set(v_reuseFailAlloc_491_, 1, v___x_484_);
v___x_486_ = v_reuseFailAlloc_491_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
lean_object* v___x_487_; lean_object* v___x_489_; 
v___x_487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_487_, 0, v___x_486_);
if (v_isShared_479_ == 0)
{
lean_ctor_set(v___x_478_, 0, v___x_487_);
v___x_489_ = v___x_478_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_490_; 
v_reuseFailAlloc_490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_490_, 0, v___x_487_);
v___x_489_ = v_reuseFailAlloc_490_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
return v___x_489_;
}
}
}
}
else
{
lean_object* v_a_493_; lean_object* v___x_495_; uint8_t v_isShared_496_; uint8_t v_isSharedCheck_500_; 
lean_dec_ref(v___x_474_);
lean_dec(v_a_473_);
lean_dec_ref(v___x_471_);
lean_dec(v_a_470_);
lean_del_object(v___x_463_);
v_a_493_ = lean_ctor_get(v___x_475_, 0);
v_isSharedCheck_500_ = !lean_is_exclusive(v___x_475_);
if (v_isSharedCheck_500_ == 0)
{
v___x_495_ = v___x_475_;
v_isShared_496_ = v_isSharedCheck_500_;
goto v_resetjp_494_;
}
else
{
lean_inc(v_a_493_);
lean_dec(v___x_475_);
v___x_495_ = lean_box(0);
v_isShared_496_ = v_isSharedCheck_500_;
goto v_resetjp_494_;
}
v_resetjp_494_:
{
lean_object* v___x_498_; 
if (v_isShared_496_ == 0)
{
v___x_498_ = v___x_495_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v_a_493_);
v___x_498_ = v_reuseFailAlloc_499_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
return v___x_498_;
}
}
}
}
else
{
lean_object* v_a_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_508_; 
lean_dec_ref(v___x_471_);
lean_dec(v_a_470_);
lean_dec_ref(v___x_467_);
lean_del_object(v___x_463_);
lean_dec(v_snd_461_);
v_a_501_ = lean_ctor_get(v___x_472_, 0);
v_isSharedCheck_508_ = !lean_is_exclusive(v___x_472_);
if (v_isSharedCheck_508_ == 0)
{
v___x_503_ = v___x_472_;
v_isShared_504_ = v_isSharedCheck_508_;
goto v_resetjp_502_;
}
else
{
lean_inc(v_a_501_);
lean_dec(v___x_472_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_508_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
lean_object* v___x_506_; 
if (v_isShared_504_ == 0)
{
v___x_506_ = v___x_503_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v_a_501_);
v___x_506_ = v_reuseFailAlloc_507_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
return v___x_506_;
}
}
}
}
else
{
lean_object* v_a_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_516_; 
lean_dec_ref(v___x_467_);
lean_del_object(v___x_463_);
lean_dec(v_snd_461_);
lean_dec(v_fst_460_);
v_a_509_ = lean_ctor_get(v___x_469_, 0);
v_isSharedCheck_516_ = !lean_is_exclusive(v___x_469_);
if (v_isSharedCheck_516_ == 0)
{
v___x_511_ = v___x_469_;
v_isShared_512_ = v_isSharedCheck_516_;
goto v_resetjp_510_;
}
else
{
lean_inc(v_a_509_);
lean_dec(v___x_469_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_516_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
lean_object* v___x_514_; 
if (v_isShared_512_ == 0)
{
v___x_514_ = v___x_511_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v_a_509_);
v___x_514_ = v_reuseFailAlloc_515_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
return v___x_514_;
}
}
}
}
else
{
lean_object* v___x_517_; lean_object* v___x_519_; 
lean_dec_ref(v___x_467_);
lean_del_object(v___x_463_);
lean_dec(v_snd_461_);
lean_dec(v_fst_460_);
v___x_517_ = lean_box(0);
if (v_isShared_459_ == 0)
{
lean_ctor_set(v___x_458_, 0, v___x_517_);
v___x_519_ = v___x_458_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v___x_517_);
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
}
else
{
lean_object* v_a_523_; lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_530_; 
v_a_523_ = lean_ctor_get(v___x_455_, 0);
v_isSharedCheck_530_ = !lean_is_exclusive(v___x_455_);
if (v_isSharedCheck_530_ == 0)
{
v___x_525_ = v___x_455_;
v_isShared_526_ = v_isSharedCheck_530_;
goto v_resetjp_524_;
}
else
{
lean_inc(v_a_523_);
lean_dec(v___x_455_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_530_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
lean_object* v___x_528_; 
if (v_isShared_526_ == 0)
{
v___x_528_ = v___x_525_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v_a_523_);
v___x_528_ = v_reuseFailAlloc_529_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
return v___x_528_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___boxed(lean_object* v_input_531_, lean_object* v_a_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_){
_start:
{
lean_object* v_res_537_; 
v_res_537_ = l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f(v_input_531_, v_a_532_, v_a_533_, v_a_534_, v_a_535_);
lean_dec(v_a_535_);
lean_dec_ref(v_a_534_);
lean_dec(v_a_533_);
lean_dec_ref(v_a_532_);
return v_res_537_;
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

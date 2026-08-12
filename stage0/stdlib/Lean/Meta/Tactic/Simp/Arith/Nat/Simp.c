// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.Arith.Nat.Simp
// Imports: public import Lean.Meta.Tactic.Simp.Arith.Util public import Lean.Meta.Tactic.Simp.Arith.Nat.Basic import Lean.Meta.AppBuilder import Lean.OrderLevel
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
lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_leCarrierIsSort(lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_mkNatAdd(lean_object*, lean_object*);
lean_object* l_Lean_mkNatLE(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
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
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__35;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__36;
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
v___x_67_ = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith___redArg(v_snd_63_, v_fst_62_, v_a_50_, v_a_51_);
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
v___x_74_ = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith___redArg(v_snd_63_, v___x_73_, v_a_50_, v_a_51_);
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
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__35(void){
_start:
{
lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_284_ = lean_unsigned_to_nat(0u);
v___x_285_ = l_Lean_Level_ofNat(v___x_284_);
return v___x_285_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__36(void){
_start:
{
lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_286_ = lean_unsigned_to_nat(1u);
v___x_287_ = l_Lean_Level_ofNat(v___x_286_);
return v___x_287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f(lean_object* v_e_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_){
_start:
{
lean_object* v_val_295_; lean_object* v_h_u2081_296_; lean_object* v___y_297_; lean_object* v___y_298_; lean_object* v___y_299_; lean_object* v___y_300_; lean_object* v___x_338_; lean_object* v___x_339_; uint8_t v___x_340_; 
v___x_338_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__8));
v___x_339_ = lean_unsigned_to_nat(1u);
v___x_340_ = l_Lean_Expr_isAppOfArity(v_e_288_, v___x_338_, v___x_339_);
if (v___x_340_ == 0)
{
lean_object* v___x_341_; 
v___x_341_ = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f(v_e_288_, v_a_289_, v_a_290_, v_a_291_, v_a_292_);
return v___x_341_;
}
else
{
lean_object* v___x_342_; 
v___x_342_ = l_Lean_leCarrierIsSort(v_a_291_, v_a_292_);
if (lean_obj_tag(v___x_342_) == 0)
{
lean_object* v_a_343_; lean_object* v___x_344_; lean_object* v_leLvl_346_; lean_object* v___y_347_; lean_object* v___y_348_; lean_object* v___y_349_; lean_object* v___y_350_; uint8_t v___x_449_; 
v_a_343_ = lean_ctor_get(v___x_342_, 0);
lean_inc(v_a_343_);
lean_dec_ref_known(v___x_342_, 1);
v___x_344_ = l_Lean_Expr_appArg_x21(v_e_288_);
v___x_449_ = lean_unbox(v_a_343_);
lean_dec(v_a_343_);
if (v___x_449_ == 0)
{
lean_object* v___x_450_; 
v___x_450_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__35, &l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__35_once, _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__35);
v_leLvl_346_ = v___x_450_;
v___y_347_ = v_a_289_;
v___y_348_ = v_a_290_;
v___y_349_ = v_a_291_;
v___y_350_ = v_a_292_;
goto v___jp_345_;
}
else
{
lean_object* v___x_451_; 
v___x_451_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__36, &l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__36_once, _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__36);
v_leLvl_346_ = v___x_451_;
v___y_347_ = v_a_289_;
v___y_348_ = v_a_290_;
v___y_349_ = v_a_291_;
v___y_350_ = v_a_292_;
goto v___jp_345_;
}
v___jp_345_:
{
lean_object* v___x_351_; 
v___x_351_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v___x_344_, v___y_348_);
if (lean_obj_tag(v___x_351_) == 0)
{
lean_object* v_a_352_; lean_object* v___x_353_; uint8_t v___x_354_; 
v_a_352_ = lean_ctor_get(v___x_351_, 0);
lean_inc(v_a_352_);
lean_dec_ref_known(v___x_351_, 1);
v___x_353_ = l_Lean_Expr_cleanupAnnotations(v_a_352_);
v___x_354_ = l_Lean_Expr_isApp(v___x_353_);
if (v___x_354_ == 0)
{
lean_dec_ref(v___x_353_);
lean_dec_ref(v_e_288_);
goto v___jp_335_;
}
else
{
lean_object* v_arg_355_; lean_object* v___x_356_; uint8_t v___x_357_; 
v_arg_355_ = lean_ctor_get(v___x_353_, 1);
lean_inc_ref(v_arg_355_);
v___x_356_ = l_Lean_Expr_appFnCleanup___redArg(v___x_353_);
v___x_357_ = l_Lean_Expr_isApp(v___x_356_);
if (v___x_357_ == 0)
{
lean_dec_ref(v___x_356_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_e_288_);
goto v___jp_335_;
}
else
{
lean_object* v_arg_358_; lean_object* v___x_359_; uint8_t v___x_360_; 
v_arg_358_ = lean_ctor_get(v___x_356_, 1);
lean_inc_ref(v_arg_358_);
v___x_359_ = l_Lean_Expr_appFnCleanup___redArg(v___x_356_);
v___x_360_ = l_Lean_Expr_isApp(v___x_359_);
if (v___x_360_ == 0)
{
lean_dec_ref(v___x_359_);
lean_dec_ref(v_arg_358_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_e_288_);
goto v___jp_335_;
}
else
{
lean_object* v___x_361_; uint8_t v___x_362_; 
v___x_361_ = l_Lean_Expr_appFnCleanup___redArg(v___x_359_);
v___x_362_ = l_Lean_Expr_isApp(v___x_361_);
if (v___x_362_ == 0)
{
lean_dec_ref(v___x_361_);
lean_dec_ref(v_arg_358_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_e_288_);
goto v___jp_335_;
}
else
{
lean_object* v_arg_363_; lean_object* v___x_364_; lean_object* v___x_365_; uint8_t v___x_366_; 
v_arg_363_ = lean_ctor_get(v___x_361_, 1);
lean_inc_ref(v_arg_363_);
v___x_364_ = l_Lean_Expr_appFnCleanup___redArg(v___x_361_);
v___x_365_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__11));
v___x_366_ = l_Lean_Expr_isConstOf(v___x_364_, v___x_365_);
if (v___x_366_ == 0)
{
lean_object* v___x_367_; uint8_t v___x_368_; 
v___x_367_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__14));
v___x_368_ = l_Lean_Expr_isConstOf(v___x_364_, v___x_367_);
if (v___x_368_ == 0)
{
lean_object* v___x_369_; uint8_t v___x_370_; 
v___x_369_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__17));
v___x_370_ = l_Lean_Expr_isConstOf(v___x_364_, v___x_369_);
if (v___x_370_ == 0)
{
lean_object* v___x_371_; uint8_t v___x_372_; 
v___x_371_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__20));
v___x_372_ = l_Lean_Expr_isConstOf(v___x_364_, v___x_371_);
lean_dec_ref(v___x_364_);
if (v___x_372_ == 0)
{
lean_dec_ref(v_arg_363_);
lean_dec_ref(v_arg_358_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_e_288_);
goto v___jp_335_;
}
else
{
lean_object* v___x_373_; 
v___x_373_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_363_, v___y_348_);
if (lean_obj_tag(v___x_373_) == 0)
{
lean_object* v_a_374_; lean_object* v___x_375_; lean_object* v___x_376_; uint8_t v___x_377_; 
v_a_374_ = lean_ctor_get(v___x_373_, 0);
lean_inc(v_a_374_);
lean_dec_ref_known(v___x_373_, 1);
v___x_375_ = l_Lean_Expr_cleanupAnnotations(v_a_374_);
v___x_376_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__21));
v___x_377_ = l_Lean_Expr_isConstOf(v___x_375_, v___x_376_);
lean_dec_ref(v___x_375_);
if (v___x_377_ == 0)
{
lean_dec_ref(v_arg_358_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_e_288_);
goto v___jp_335_;
}
else
{
lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_378_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__22, &l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__22_once, _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__22);
lean_inc_ref(v_arg_355_);
v___x_379_ = l_Lean_mkNatAdd(v_arg_355_, v___x_378_);
lean_inc_ref(v_arg_358_);
lean_inc(v_leLvl_346_);
v___x_380_ = l_Lean_mkNatLE(v_leLvl_346_, v___x_379_, v_arg_358_);
v___x_381_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__25, &l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__25_once, _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__25);
v___x_382_ = l_Lean_mkAppB(v___x_381_, v_arg_358_, v_arg_355_);
v_val_295_ = v___x_380_;
v_h_u2081_296_ = v___x_382_;
v___y_297_ = v___y_347_;
v___y_298_ = v___y_348_;
v___y_299_ = v___y_349_;
v___y_300_ = v___y_350_;
goto v___jp_294_;
}
}
else
{
lean_object* v_a_383_; lean_object* v___x_385_; uint8_t v_isShared_386_; uint8_t v_isSharedCheck_390_; 
lean_dec_ref(v_arg_358_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_e_288_);
v_a_383_ = lean_ctor_get(v___x_373_, 0);
v_isSharedCheck_390_ = !lean_is_exclusive(v___x_373_);
if (v_isSharedCheck_390_ == 0)
{
v___x_385_ = v___x_373_;
v_isShared_386_ = v_isSharedCheck_390_;
goto v_resetjp_384_;
}
else
{
lean_inc(v_a_383_);
lean_dec(v___x_373_);
v___x_385_ = lean_box(0);
v_isShared_386_ = v_isSharedCheck_390_;
goto v_resetjp_384_;
}
v_resetjp_384_:
{
lean_object* v___x_388_; 
if (v_isShared_386_ == 0)
{
v___x_388_ = v___x_385_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v_a_383_);
v___x_388_ = v_reuseFailAlloc_389_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
return v___x_388_;
}
}
}
}
}
else
{
lean_object* v___x_391_; 
lean_dec_ref(v___x_364_);
v___x_391_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_363_, v___y_348_);
if (lean_obj_tag(v___x_391_) == 0)
{
lean_object* v_a_392_; lean_object* v___x_393_; lean_object* v___x_394_; uint8_t v___x_395_; 
v_a_392_ = lean_ctor_get(v___x_391_, 0);
lean_inc(v_a_392_);
lean_dec_ref_known(v___x_391_, 1);
v___x_393_ = l_Lean_Expr_cleanupAnnotations(v_a_392_);
v___x_394_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__21));
v___x_395_ = l_Lean_Expr_isConstOf(v___x_393_, v___x_394_);
lean_dec_ref(v___x_393_);
if (v___x_395_ == 0)
{
lean_dec_ref(v_arg_358_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_e_288_);
goto v___jp_335_;
}
else
{
lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; 
v___x_396_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__22, &l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__22_once, _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__22);
lean_inc_ref(v_arg_358_);
v___x_397_ = l_Lean_mkNatAdd(v_arg_358_, v___x_396_);
lean_inc_ref(v_arg_355_);
lean_inc(v_leLvl_346_);
v___x_398_ = l_Lean_mkNatLE(v_leLvl_346_, v___x_397_, v_arg_355_);
v___x_399_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__28, &l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__28_once, _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__28);
v___x_400_ = l_Lean_mkAppB(v___x_399_, v_arg_358_, v_arg_355_);
v_val_295_ = v___x_398_;
v_h_u2081_296_ = v___x_400_;
v___y_297_ = v___y_347_;
v___y_298_ = v___y_348_;
v___y_299_ = v___y_349_;
v___y_300_ = v___y_350_;
goto v___jp_294_;
}
}
else
{
lean_object* v_a_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_408_; 
lean_dec_ref(v_arg_358_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_e_288_);
v_a_401_ = lean_ctor_get(v___x_391_, 0);
v_isSharedCheck_408_ = !lean_is_exclusive(v___x_391_);
if (v_isSharedCheck_408_ == 0)
{
v___x_403_ = v___x_391_;
v_isShared_404_ = v_isSharedCheck_408_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_a_401_);
lean_dec(v___x_391_);
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
lean_dec_ref(v___x_364_);
v___x_409_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_363_, v___y_348_);
if (lean_obj_tag(v___x_409_) == 0)
{
lean_object* v_a_410_; lean_object* v___x_411_; lean_object* v___x_412_; uint8_t v___x_413_; 
v_a_410_ = lean_ctor_get(v___x_409_, 0);
lean_inc(v_a_410_);
lean_dec_ref_known(v___x_409_, 1);
v___x_411_ = l_Lean_Expr_cleanupAnnotations(v_a_410_);
v___x_412_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__21));
v___x_413_ = l_Lean_Expr_isConstOf(v___x_411_, v___x_412_);
lean_dec_ref(v___x_411_);
if (v___x_413_ == 0)
{
lean_dec_ref(v_arg_358_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_e_288_);
goto v___jp_335_;
}
else
{
lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; 
lean_inc_ref(v_arg_358_);
lean_inc_ref(v_arg_355_);
lean_inc(v_leLvl_346_);
v___x_414_ = l_Lean_mkNatLE(v_leLvl_346_, v_arg_355_, v_arg_358_);
v___x_415_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__31, &l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__31_once, _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__31);
v___x_416_ = l_Lean_mkAppB(v___x_415_, v_arg_358_, v_arg_355_);
v_val_295_ = v___x_414_;
v_h_u2081_296_ = v___x_416_;
v___y_297_ = v___y_347_;
v___y_298_ = v___y_348_;
v___y_299_ = v___y_349_;
v___y_300_ = v___y_350_;
goto v___jp_294_;
}
}
else
{
lean_object* v_a_417_; lean_object* v___x_419_; uint8_t v_isShared_420_; uint8_t v_isSharedCheck_424_; 
lean_dec_ref(v_arg_358_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_e_288_);
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
else
{
lean_object* v___x_425_; 
lean_dec_ref(v___x_364_);
v___x_425_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_363_, v___y_348_);
if (lean_obj_tag(v___x_425_) == 0)
{
lean_object* v_a_426_; lean_object* v___x_427_; lean_object* v___x_428_; uint8_t v___x_429_; 
v_a_426_ = lean_ctor_get(v___x_425_, 0);
lean_inc(v_a_426_);
lean_dec_ref_known(v___x_425_, 1);
v___x_427_ = l_Lean_Expr_cleanupAnnotations(v_a_426_);
v___x_428_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__21));
v___x_429_ = l_Lean_Expr_isConstOf(v___x_427_, v___x_428_);
lean_dec_ref(v___x_427_);
if (v___x_429_ == 0)
{
lean_dec_ref(v_arg_358_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_e_288_);
goto v___jp_335_;
}
else
{
lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; 
lean_inc_ref(v_arg_355_);
lean_inc_ref(v_arg_358_);
lean_inc(v_leLvl_346_);
v___x_430_ = l_Lean_mkNatLE(v_leLvl_346_, v_arg_358_, v_arg_355_);
v___x_431_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__34, &l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__34_once, _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__34);
v___x_432_ = l_Lean_mkAppB(v___x_431_, v_arg_358_, v_arg_355_);
v_val_295_ = v___x_430_;
v_h_u2081_296_ = v___x_432_;
v___y_297_ = v___y_347_;
v___y_298_ = v___y_348_;
v___y_299_ = v___y_349_;
v___y_300_ = v___y_350_;
goto v___jp_294_;
}
}
else
{
lean_object* v_a_433_; lean_object* v___x_435_; uint8_t v_isShared_436_; uint8_t v_isSharedCheck_440_; 
lean_dec_ref(v_arg_358_);
lean_dec_ref(v_arg_355_);
lean_dec_ref(v_e_288_);
v_a_433_ = lean_ctor_get(v___x_425_, 0);
v_isSharedCheck_440_ = !lean_is_exclusive(v___x_425_);
if (v_isSharedCheck_440_ == 0)
{
v___x_435_ = v___x_425_;
v_isShared_436_ = v_isSharedCheck_440_;
goto v_resetjp_434_;
}
else
{
lean_inc(v_a_433_);
lean_dec(v___x_425_);
v___x_435_ = lean_box(0);
v_isShared_436_ = v_isSharedCheck_440_;
goto v_resetjp_434_;
}
v_resetjp_434_:
{
lean_object* v___x_438_; 
if (v_isShared_436_ == 0)
{
v___x_438_ = v___x_435_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v_a_433_);
v___x_438_ = v_reuseFailAlloc_439_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
return v___x_438_;
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
lean_object* v_a_441_; lean_object* v___x_443_; uint8_t v_isShared_444_; uint8_t v_isSharedCheck_448_; 
lean_dec_ref(v_e_288_);
v_a_441_ = lean_ctor_get(v___x_351_, 0);
v_isSharedCheck_448_ = !lean_is_exclusive(v___x_351_);
if (v_isSharedCheck_448_ == 0)
{
v___x_443_ = v___x_351_;
v_isShared_444_ = v_isSharedCheck_448_;
goto v_resetjp_442_;
}
else
{
lean_inc(v_a_441_);
lean_dec(v___x_351_);
v___x_443_ = lean_box(0);
v_isShared_444_ = v_isSharedCheck_448_;
goto v_resetjp_442_;
}
v_resetjp_442_:
{
lean_object* v___x_446_; 
if (v_isShared_444_ == 0)
{
v___x_446_ = v___x_443_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v_a_441_);
v___x_446_ = v_reuseFailAlloc_447_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
return v___x_446_;
}
}
}
}
}
else
{
lean_object* v_a_452_; lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_459_; 
lean_dec_ref(v_e_288_);
v_a_452_ = lean_ctor_get(v___x_342_, 0);
v_isSharedCheck_459_ = !lean_is_exclusive(v___x_342_);
if (v_isSharedCheck_459_ == 0)
{
v___x_454_ = v___x_342_;
v_isShared_455_ = v_isSharedCheck_459_;
goto v_resetjp_453_;
}
else
{
lean_inc(v_a_452_);
lean_dec(v___x_342_);
v___x_454_ = lean_box(0);
v_isShared_455_ = v_isSharedCheck_459_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
lean_object* v___x_457_; 
if (v_isShared_455_ == 0)
{
v___x_457_ = v___x_454_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v_a_452_);
v___x_457_ = v_reuseFailAlloc_458_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
return v___x_457_;
}
}
}
}
v___jp_294_:
{
lean_object* v___x_301_; 
lean_inc_ref(v_val_295_);
v___x_301_ = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f(v_val_295_, v___y_297_, v___y_298_, v___y_299_, v___y_300_);
if (lean_obj_tag(v___x_301_) == 0)
{
lean_object* v_a_302_; lean_object* v___x_304_; uint8_t v_isShared_305_; uint8_t v_isSharedCheck_334_; 
v_a_302_ = lean_ctor_get(v___x_301_, 0);
v_isSharedCheck_334_ = !lean_is_exclusive(v___x_301_);
if (v_isSharedCheck_334_ == 0)
{
v___x_304_ = v___x_301_;
v_isShared_305_ = v_isSharedCheck_334_;
goto v_resetjp_303_;
}
else
{
lean_inc(v_a_302_);
lean_dec(v___x_301_);
v___x_304_ = lean_box(0);
v_isShared_305_ = v_isSharedCheck_334_;
goto v_resetjp_303_;
}
v_resetjp_303_:
{
if (lean_obj_tag(v_a_302_) == 1)
{
lean_object* v_val_306_; lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_328_; 
v_val_306_ = lean_ctor_get(v_a_302_, 0);
v_isSharedCheck_328_ = !lean_is_exclusive(v_a_302_);
if (v_isSharedCheck_328_ == 0)
{
v___x_308_ = v_a_302_;
v_isShared_309_ = v_isSharedCheck_328_;
goto v_resetjp_307_;
}
else
{
lean_inc(v_val_306_);
lean_dec(v_a_302_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_328_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
lean_object* v_fst_310_; lean_object* v_snd_311_; lean_object* v___x_313_; uint8_t v_isShared_314_; uint8_t v_isSharedCheck_327_; 
v_fst_310_ = lean_ctor_get(v_val_306_, 0);
v_snd_311_ = lean_ctor_get(v_val_306_, 1);
v_isSharedCheck_327_ = !lean_is_exclusive(v_val_306_);
if (v_isSharedCheck_327_ == 0)
{
v___x_313_ = v_val_306_;
v_isShared_314_ = v_isSharedCheck_327_;
goto v_resetjp_312_;
}
else
{
lean_inc(v_snd_311_);
lean_inc(v_fst_310_);
lean_dec(v_val_306_);
v___x_313_ = lean_box(0);
v_isShared_314_ = v_isSharedCheck_327_;
goto v_resetjp_312_;
}
v_resetjp_312_:
{
lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_319_; 
v___x_315_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__5, &l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__5_once, _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__5);
v___x_316_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__6, &l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__6_once, _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__6);
lean_inc(v_fst_310_);
v___x_317_ = l_Lean_mkApp6(v___x_315_, v___x_316_, v_e_288_, v_val_295_, v_fst_310_, v_h_u2081_296_, v_snd_311_);
if (v_isShared_314_ == 0)
{
lean_ctor_set(v___x_313_, 1, v___x_317_);
v___x_319_ = v___x_313_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v_fst_310_);
lean_ctor_set(v_reuseFailAlloc_326_, 1, v___x_317_);
v___x_319_ = v_reuseFailAlloc_326_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
lean_object* v___x_321_; 
if (v_isShared_309_ == 0)
{
lean_ctor_set(v___x_308_, 0, v___x_319_);
v___x_321_ = v___x_308_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v___x_319_);
v___x_321_ = v_reuseFailAlloc_325_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
lean_object* v___x_323_; 
if (v_isShared_305_ == 0)
{
lean_ctor_set(v___x_304_, 0, v___x_321_);
v___x_323_ = v___x_304_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v___x_321_);
v___x_323_ = v_reuseFailAlloc_324_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
return v___x_323_;
}
}
}
}
}
}
else
{
lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_332_; 
lean_dec(v_a_302_);
lean_dec_ref(v_e_288_);
v___x_329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_329_, 0, v_val_295_);
lean_ctor_set(v___x_329_, 1, v_h_u2081_296_);
v___x_330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_330_, 0, v___x_329_);
if (v_isShared_305_ == 0)
{
lean_ctor_set(v___x_304_, 0, v___x_330_);
v___x_332_ = v___x_304_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v___x_330_);
v___x_332_ = v_reuseFailAlloc_333_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
return v___x_332_;
}
}
}
}
else
{
lean_dec_ref(v_h_u2081_296_);
lean_dec_ref(v_val_295_);
lean_dec_ref(v_e_288_);
return v___x_301_;
}
}
v___jp_335_:
{
lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_336_ = lean_box(0);
v___x_337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_337_, 0, v___x_336_);
return v___x_337_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___boxed(lean_object* v_e_460_, lean_object* v_a_461_, lean_object* v_a_462_, lean_object* v_a_463_, lean_object* v_a_464_, lean_object* v_a_465_){
_start:
{
lean_object* v_res_466_; 
v_res_466_ = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f(v_e_460_, v_a_461_, v_a_462_, v_a_463_, v_a_464_);
lean_dec(v_a_464_);
lean_dec_ref(v_a_463_);
lean_dec(v_a_462_);
lean_dec_ref(v_a_461_);
return v_res_466_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___closed__2(void){
_start:
{
lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_474_ = lean_box(0);
v___x_475_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___closed__1));
v___x_476_ = l_Lean_mkConst(v___x_475_, v___x_474_);
return v___x_476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f(lean_object* v_input_477_, lean_object* v_a_478_, lean_object* v_a_479_, lean_object* v_a_480_, lean_object* v_a_481_){
_start:
{
lean_object* v___x_483_; 
v___x_483_ = l_Lean_Meta_Simp_Arith_Nat_toLinearExpr(v_input_477_, v_a_478_, v_a_479_, v_a_480_, v_a_481_);
if (lean_obj_tag(v___x_483_) == 0)
{
lean_object* v_a_484_; lean_object* v___x_486_; uint8_t v_isShared_487_; uint8_t v_isSharedCheck_550_; 
v_a_484_ = lean_ctor_get(v___x_483_, 0);
v_isSharedCheck_550_ = !lean_is_exclusive(v___x_483_);
if (v_isSharedCheck_550_ == 0)
{
v___x_486_ = v___x_483_;
v_isShared_487_ = v_isSharedCheck_550_;
goto v_resetjp_485_;
}
else
{
lean_inc(v_a_484_);
lean_dec(v___x_483_);
v___x_486_ = lean_box(0);
v_isShared_487_ = v_isSharedCheck_550_;
goto v_resetjp_485_;
}
v_resetjp_485_:
{
lean_object* v_fst_488_; lean_object* v_snd_489_; lean_object* v___x_491_; uint8_t v_isShared_492_; uint8_t v_isSharedCheck_549_; 
v_fst_488_ = lean_ctor_get(v_a_484_, 0);
v_snd_489_ = lean_ctor_get(v_a_484_, 1);
v_isSharedCheck_549_ = !lean_is_exclusive(v_a_484_);
if (v_isSharedCheck_549_ == 0)
{
v___x_491_ = v_a_484_;
v_isShared_492_ = v_isSharedCheck_549_;
goto v_resetjp_490_;
}
else
{
lean_inc(v_snd_489_);
lean_inc(v_fst_488_);
lean_dec(v_a_484_);
v___x_491_ = lean_box(0);
v_isShared_492_ = v_isSharedCheck_549_;
goto v_resetjp_490_;
}
v_resetjp_490_:
{
lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; uint8_t v___x_496_; 
v___x_493_ = l_Nat_Internal_Linear_Expr_toPoly(v_fst_488_);
v___x_494_ = l_Nat_Internal_Linear_Poly_norm(v___x_493_);
v___x_495_ = l_Nat_Internal_Linear_Poly_toExpr(v___x_494_);
v___x_496_ = l_Nat_Internal_Linear_instBEqExpr_beq(v___x_495_, v_fst_488_);
if (v___x_496_ == 0)
{
lean_object* v___x_497_; 
lean_del_object(v___x_486_);
lean_inc(v_snd_489_);
v___x_497_ = l_Lean_Meta_Simp_Arith_Nat_toContextExpr(v_snd_489_, v_a_478_, v_a_479_, v_a_480_, v_a_481_);
if (lean_obj_tag(v___x_497_) == 0)
{
lean_object* v_a_498_; lean_object* v___x_499_; lean_object* v___x_500_; 
v_a_498_ = lean_ctor_get(v___x_497_, 0);
lean_inc(v_a_498_);
lean_dec_ref_known(v___x_497_, 1);
lean_inc(v_fst_488_);
v___x_499_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr(v_fst_488_);
v___x_500_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(v_snd_489_, v_fst_488_);
if (lean_obj_tag(v___x_500_) == 0)
{
lean_object* v_a_501_; lean_object* v___x_502_; lean_object* v___x_503_; 
v_a_501_ = lean_ctor_get(v___x_500_, 0);
lean_inc(v_a_501_);
lean_dec_ref_known(v___x_500_, 1);
lean_inc_ref(v___x_495_);
v___x_502_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr(v___x_495_);
v___x_503_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(v_snd_489_, v___x_495_);
lean_dec(v_snd_489_);
if (lean_obj_tag(v___x_503_) == 0)
{
lean_object* v_a_504_; lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_520_; 
v_a_504_ = lean_ctor_get(v___x_503_, 0);
v_isSharedCheck_520_ = !lean_is_exclusive(v___x_503_);
if (v_isSharedCheck_520_ == 0)
{
v___x_506_ = v___x_503_;
v_isShared_507_ = v_isSharedCheck_520_;
goto v_resetjp_505_;
}
else
{
lean_inc(v_a_504_);
lean_dec(v___x_503_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_520_;
goto v_resetjp_505_;
}
v_resetjp_505_:
{
lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_514_; 
v___x_508_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___closed__2, &l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___closed__2_once, _init_l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___closed__2);
v___x_509_ = l_Lean_eagerReflBoolTrue;
v___x_510_ = l_Lean_mkApp4(v___x_508_, v_a_498_, v___x_499_, v___x_502_, v___x_509_);
lean_inc(v_a_504_);
v___x_511_ = l_Lean_mkNatEq(v_a_501_, v_a_504_);
v___x_512_ = l_Lean_Meta_mkExpectedPropHint(v___x_510_, v___x_511_);
if (v_isShared_492_ == 0)
{
lean_ctor_set(v___x_491_, 1, v___x_512_);
lean_ctor_set(v___x_491_, 0, v_a_504_);
v___x_514_ = v___x_491_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v_a_504_);
lean_ctor_set(v_reuseFailAlloc_519_, 1, v___x_512_);
v___x_514_ = v_reuseFailAlloc_519_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
lean_object* v___x_515_; lean_object* v___x_517_; 
v___x_515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_515_, 0, v___x_514_);
if (v_isShared_507_ == 0)
{
lean_ctor_set(v___x_506_, 0, v___x_515_);
v___x_517_ = v___x_506_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v___x_515_);
v___x_517_ = v_reuseFailAlloc_518_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
return v___x_517_;
}
}
}
}
else
{
lean_object* v_a_521_; lean_object* v___x_523_; uint8_t v_isShared_524_; uint8_t v_isSharedCheck_528_; 
lean_dec_ref(v___x_502_);
lean_dec(v_a_501_);
lean_dec_ref(v___x_499_);
lean_dec(v_a_498_);
lean_del_object(v___x_491_);
v_a_521_ = lean_ctor_get(v___x_503_, 0);
v_isSharedCheck_528_ = !lean_is_exclusive(v___x_503_);
if (v_isSharedCheck_528_ == 0)
{
v___x_523_ = v___x_503_;
v_isShared_524_ = v_isSharedCheck_528_;
goto v_resetjp_522_;
}
else
{
lean_inc(v_a_521_);
lean_dec(v___x_503_);
v___x_523_ = lean_box(0);
v_isShared_524_ = v_isSharedCheck_528_;
goto v_resetjp_522_;
}
v_resetjp_522_:
{
lean_object* v___x_526_; 
if (v_isShared_524_ == 0)
{
v___x_526_ = v___x_523_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v_a_521_);
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
else
{
lean_object* v_a_529_; lean_object* v___x_531_; uint8_t v_isShared_532_; uint8_t v_isSharedCheck_536_; 
lean_dec_ref(v___x_499_);
lean_dec(v_a_498_);
lean_dec_ref(v___x_495_);
lean_del_object(v___x_491_);
lean_dec(v_snd_489_);
v_a_529_ = lean_ctor_get(v___x_500_, 0);
v_isSharedCheck_536_ = !lean_is_exclusive(v___x_500_);
if (v_isSharedCheck_536_ == 0)
{
v___x_531_ = v___x_500_;
v_isShared_532_ = v_isSharedCheck_536_;
goto v_resetjp_530_;
}
else
{
lean_inc(v_a_529_);
lean_dec(v___x_500_);
v___x_531_ = lean_box(0);
v_isShared_532_ = v_isSharedCheck_536_;
goto v_resetjp_530_;
}
v_resetjp_530_:
{
lean_object* v___x_534_; 
if (v_isShared_532_ == 0)
{
v___x_534_ = v___x_531_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v_a_529_);
v___x_534_ = v_reuseFailAlloc_535_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
return v___x_534_;
}
}
}
}
else
{
lean_object* v_a_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_544_; 
lean_dec_ref(v___x_495_);
lean_del_object(v___x_491_);
lean_dec(v_snd_489_);
lean_dec(v_fst_488_);
v_a_537_ = lean_ctor_get(v___x_497_, 0);
v_isSharedCheck_544_ = !lean_is_exclusive(v___x_497_);
if (v_isSharedCheck_544_ == 0)
{
v___x_539_ = v___x_497_;
v_isShared_540_ = v_isSharedCheck_544_;
goto v_resetjp_538_;
}
else
{
lean_inc(v_a_537_);
lean_dec(v___x_497_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_544_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
lean_object* v___x_542_; 
if (v_isShared_540_ == 0)
{
v___x_542_ = v___x_539_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v_a_537_);
v___x_542_ = v_reuseFailAlloc_543_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
return v___x_542_;
}
}
}
}
else
{
lean_object* v___x_545_; lean_object* v___x_547_; 
lean_dec_ref(v___x_495_);
lean_del_object(v___x_491_);
lean_dec(v_snd_489_);
lean_dec(v_fst_488_);
v___x_545_ = lean_box(0);
if (v_isShared_487_ == 0)
{
lean_ctor_set(v___x_486_, 0, v___x_545_);
v___x_547_ = v___x_486_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v___x_545_);
v___x_547_ = v_reuseFailAlloc_548_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
return v___x_547_;
}
}
}
}
}
else
{
lean_object* v_a_551_; lean_object* v___x_553_; uint8_t v_isShared_554_; uint8_t v_isSharedCheck_558_; 
v_a_551_ = lean_ctor_get(v___x_483_, 0);
v_isSharedCheck_558_ = !lean_is_exclusive(v___x_483_);
if (v_isSharedCheck_558_ == 0)
{
v___x_553_ = v___x_483_;
v_isShared_554_ = v_isSharedCheck_558_;
goto v_resetjp_552_;
}
else
{
lean_inc(v_a_551_);
lean_dec(v___x_483_);
v___x_553_ = lean_box(0);
v_isShared_554_ = v_isSharedCheck_558_;
goto v_resetjp_552_;
}
v_resetjp_552_:
{
lean_object* v___x_556_; 
if (v_isShared_554_ == 0)
{
v___x_556_ = v___x_553_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v_a_551_);
v___x_556_ = v_reuseFailAlloc_557_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
return v___x_556_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___boxed(lean_object* v_input_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_){
_start:
{
lean_object* v_res_565_; 
v_res_565_ = l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f(v_input_559_, v_a_560_, v_a_561_, v_a_562_, v_a_563_);
lean_dec(v_a_563_);
lean_dec_ref(v_a_562_);
lean_dec(v_a_561_);
lean_dec_ref(v_a_560_);
return v_res_565_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Arith_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Arith_Nat_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* runtime_initialize_Lean_OrderLevel(uint8_t builtin);
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
res = runtime_initialize_Lean_OrderLevel(builtin);
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
lean_object* initialize_Lean_OrderLevel(uint8_t builtin);
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
res = initialize_Lean_OrderLevel(builtin);
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

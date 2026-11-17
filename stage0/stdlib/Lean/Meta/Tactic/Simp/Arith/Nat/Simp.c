// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.Arith.Nat.Simp
// Imports: public import Lean.Meta.Tactic.Simp.Arith.Util public import Lean.Meta.Tactic.Simp.Arith.Nat.Basic import Lean.Meta.AppBuilder import Lean.CoreM
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
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Arith_Nat_toContextExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr(lean_object*);
extern lean_object* l_Lean_eagerReflBoolTrue;
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkPropEq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkExpectedPropHint(lean_object*, lean_object*);
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
lean_object* l_Lean_mkNatLE(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_leCarrierIsSort(lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "eq_of_toNormPoly_eq_k"};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__4 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(238, 85, 239, 193, 128, 115, 38, 143)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__5_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(135, 17, 186, 49, 10, 156, 173, 153)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__5_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 198, 254, 91, 59, 223, 24, 67)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__5_value_aux_3),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(227, 9, 137, 205, 20, 133, 43, 136)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__5 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__6;
static const lean_string_object l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "True"};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__7 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__7_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__7_value),LEAN_SCALAR_PTR_LITERAL(78, 21, 103, 131, 118, 13, 187, 164)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__8 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__8_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__9;
static const lean_string_object l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "eq_true_of_isValid_k"};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__10 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__10_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__11_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(238, 85, 239, 193, 128, 115, 38, 143)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__11_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(135, 17, 186, 49, 10, 156, 173, 153)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__11_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__11_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 198, 254, 91, 59, 223, 24, 67)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__11_value_aux_3),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__10_value),LEAN_SCALAR_PTR_LITERAL(116, 228, 183, 209, 187, 44, 126, 120)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__11 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__11_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__12;
static const lean_string_object l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "False"};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__13 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__13_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__13_value),LEAN_SCALAR_PTR_LITERAL(227, 122, 176, 177, 50, 175, 152, 12)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__14 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__14_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__15;
static const lean_string_object l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "eq_false_of_isUnsat_k"};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__16 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__16_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__17_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(238, 85, 239, 193, 128, 115, 38, 143)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__17_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(135, 17, 186, 49, 10, 156, 173, 153)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__17_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__17_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 198, 254, 91, 59, 223, 24, 67)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__17_value_aux_3),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__16_value),LEAN_SCALAR_PTR_LITERAL(196, 75, 175, 116, 78, 85, 28, 18)}};
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
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___closed__1_value_aux_3),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(18, 109, 86, 76, 135, 85, 216, 37)}};
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
lean_object* v_a_54_; lean_object* v___x_56_; uint8_t v_isShared_57_; uint8_t v_isSharedCheck_197_; 
v_a_54_ = lean_ctor_get(v___x_53_, 0);
v_isSharedCheck_197_ = !lean_is_exclusive(v___x_53_);
if (v_isSharedCheck_197_ == 0)
{
v___x_56_ = v___x_53_;
v_isShared_57_ = v_isSharedCheck_197_;
goto v_resetjp_55_;
}
else
{
lean_inc(v_a_54_);
lean_dec(v___x_53_);
v___x_56_ = lean_box(0);
v_isShared_57_ = v_isSharedCheck_197_;
goto v_resetjp_55_;
}
v_resetjp_55_:
{
if (lean_obj_tag(v_a_54_) == 1)
{
lean_object* v_val_58_; lean_object* v___x_60_; uint8_t v_isShared_61_; uint8_t v_isSharedCheck_192_; 
lean_del_object(v___x_56_);
v_val_58_ = lean_ctor_get(v_a_54_, 0);
v_isSharedCheck_192_ = !lean_is_exclusive(v_a_54_);
if (v_isSharedCheck_192_ == 0)
{
v___x_60_ = v_a_54_;
v_isShared_61_ = v_isSharedCheck_192_;
goto v_resetjp_59_;
}
else
{
lean_inc(v_val_58_);
lean_dec(v_a_54_);
v___x_60_ = lean_box(0);
v_isShared_61_ = v_isSharedCheck_192_;
goto v_resetjp_59_;
}
v_resetjp_59_:
{
lean_object* v_fst_62_; lean_object* v_snd_63_; lean_object* v___x_65_; uint8_t v_isShared_66_; uint8_t v_isSharedCheck_191_; 
v_fst_62_ = lean_ctor_get(v_val_58_, 0);
v_snd_63_ = lean_ctor_get(v_val_58_, 1);
v_isSharedCheck_191_ = !lean_is_exclusive(v_val_58_);
if (v_isSharedCheck_191_ == 0)
{
v___x_65_ = v_val_58_;
v_isShared_66_ = v_isSharedCheck_191_;
goto v_resetjp_64_;
}
else
{
lean_inc(v_snd_63_);
lean_inc(v_fst_62_);
lean_dec(v_val_58_);
v___x_65_ = lean_box(0);
v_isShared_66_ = v_isSharedCheck_191_;
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
lean_object* v_a_75_; lean_object* v___x_77_; uint8_t v_isShared_78_; uint8_t v_isSharedCheck_114_; 
v_a_75_ = lean_ctor_get(v___x_74_, 0);
v_isSharedCheck_114_ = !lean_is_exclusive(v___x_74_);
if (v_isSharedCheck_114_ == 0)
{
v___x_77_ = v___x_74_;
v_isShared_78_ = v_isSharedCheck_114_;
goto v_resetjp_76_;
}
else
{
lean_inc(v_a_75_);
lean_dec(v___x_74_);
v___x_77_ = lean_box(0);
v_isShared_78_ = v_isSharedCheck_114_;
goto v_resetjp_76_;
}
v_resetjp_76_:
{
uint8_t v___x_79_; 
v___x_79_ = lean_expr_eqv(v_a_75_, v_a_68_);
if (v___x_79_ == 0)
{
lean_object* v___x_80_; 
lean_del_object(v___x_77_);
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
else
{
lean_object* v___x_110_; lean_object* v___x_112_; 
lean_dec(v_a_75_);
lean_dec_ref(v___x_73_);
lean_dec(v_a_68_);
lean_del_object(v___x_65_);
lean_dec(v_snd_63_);
lean_dec(v_fst_62_);
lean_del_object(v___x_60_);
v___x_110_ = lean_box(0);
if (v_isShared_78_ == 0)
{
lean_ctor_set(v___x_77_, 0, v___x_110_);
v___x_112_ = v___x_77_;
goto v_reusejp_111_;
}
else
{
lean_object* v_reuseFailAlloc_113_; 
v_reuseFailAlloc_113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_113_, 0, v___x_110_);
v___x_112_ = v_reuseFailAlloc_113_;
goto v_reusejp_111_;
}
v_reusejp_111_:
{
return v___x_112_;
}
}
}
}
else
{
lean_object* v_a_115_; lean_object* v___x_117_; uint8_t v_isShared_118_; uint8_t v_isSharedCheck_122_; 
lean_dec_ref(v___x_73_);
lean_dec(v_a_68_);
lean_del_object(v___x_65_);
lean_dec(v_snd_63_);
lean_dec(v_fst_62_);
lean_del_object(v___x_60_);
v_a_115_ = lean_ctor_get(v___x_74_, 0);
v_isSharedCheck_122_ = !lean_is_exclusive(v___x_74_);
if (v_isSharedCheck_122_ == 0)
{
v___x_117_ = v___x_74_;
v_isShared_118_ = v_isSharedCheck_122_;
goto v_resetjp_116_;
}
else
{
lean_inc(v_a_115_);
lean_dec(v___x_74_);
v___x_117_ = lean_box(0);
v_isShared_118_ = v_isSharedCheck_122_;
goto v_resetjp_116_;
}
v_resetjp_116_:
{
lean_object* v___x_120_; 
if (v_isShared_118_ == 0)
{
v___x_120_ = v___x_117_;
goto v_reusejp_119_;
}
else
{
lean_object* v_reuseFailAlloc_121_; 
v_reuseFailAlloc_121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_121_, 0, v_a_115_);
v___x_120_ = v_reuseFailAlloc_121_;
goto v_reusejp_119_;
}
v_reusejp_119_:
{
return v___x_120_;
}
}
}
}
else
{
lean_object* v___x_123_; lean_object* v___x_124_; 
lean_dec_ref(v___x_70_);
v___x_123_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__9, &l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__9_once, _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__9);
v___x_124_ = l_Lean_Meta_Simp_Arith_Nat_toContextExpr(v_snd_63_, v_a_48_, v_a_49_, v_a_50_, v_a_51_);
if (lean_obj_tag(v___x_124_) == 0)
{
lean_object* v_a_125_; lean_object* v___x_127_; uint8_t v_isShared_128_; uint8_t v_isSharedCheck_144_; 
v_a_125_ = lean_ctor_get(v___x_124_, 0);
v_isSharedCheck_144_ = !lean_is_exclusive(v___x_124_);
if (v_isSharedCheck_144_ == 0)
{
v___x_127_ = v___x_124_;
v_isShared_128_ = v_isSharedCheck_144_;
goto v_resetjp_126_;
}
else
{
lean_inc(v_a_125_);
lean_dec(v___x_124_);
v___x_127_ = lean_box(0);
v_isShared_128_ = v_isSharedCheck_144_;
goto v_resetjp_126_;
}
v_resetjp_126_:
{
lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_136_; 
v___x_129_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__12, &l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__12_once, _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__12);
v___x_130_ = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr(v_fst_62_);
v___x_131_ = l_Lean_eagerReflBoolTrue;
v___x_132_ = l_Lean_mkApp3(v___x_129_, v_a_125_, v___x_130_, v___x_131_);
v___x_133_ = l_Lean_mkPropEq(v_a_68_, v___x_123_);
v___x_134_ = l_Lean_Meta_mkExpectedPropHint(v___x_132_, v___x_133_);
if (v_isShared_66_ == 0)
{
lean_ctor_set(v___x_65_, 1, v___x_134_);
lean_ctor_set(v___x_65_, 0, v___x_123_);
v___x_136_ = v___x_65_;
goto v_reusejp_135_;
}
else
{
lean_object* v_reuseFailAlloc_143_; 
v_reuseFailAlloc_143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_143_, 0, v___x_123_);
lean_ctor_set(v_reuseFailAlloc_143_, 1, v___x_134_);
v___x_136_ = v_reuseFailAlloc_143_;
goto v_reusejp_135_;
}
v_reusejp_135_:
{
lean_object* v___x_138_; 
if (v_isShared_61_ == 0)
{
lean_ctor_set(v___x_60_, 0, v___x_136_);
v___x_138_ = v___x_60_;
goto v_reusejp_137_;
}
else
{
lean_object* v_reuseFailAlloc_142_; 
v_reuseFailAlloc_142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_142_, 0, v___x_136_);
v___x_138_ = v_reuseFailAlloc_142_;
goto v_reusejp_137_;
}
v_reusejp_137_:
{
lean_object* v___x_140_; 
if (v_isShared_128_ == 0)
{
lean_ctor_set(v___x_127_, 0, v___x_138_);
v___x_140_ = v___x_127_;
goto v_reusejp_139_;
}
else
{
lean_object* v_reuseFailAlloc_141_; 
v_reuseFailAlloc_141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_141_, 0, v___x_138_);
v___x_140_ = v_reuseFailAlloc_141_;
goto v_reusejp_139_;
}
v_reusejp_139_:
{
return v___x_140_;
}
}
}
}
}
else
{
lean_object* v_a_145_; lean_object* v___x_147_; uint8_t v_isShared_148_; uint8_t v_isSharedCheck_152_; 
lean_dec(v_a_68_);
lean_del_object(v___x_65_);
lean_dec(v_fst_62_);
lean_del_object(v___x_60_);
v_a_145_ = lean_ctor_get(v___x_124_, 0);
v_isSharedCheck_152_ = !lean_is_exclusive(v___x_124_);
if (v_isSharedCheck_152_ == 0)
{
v___x_147_ = v___x_124_;
v_isShared_148_ = v_isSharedCheck_152_;
goto v_resetjp_146_;
}
else
{
lean_inc(v_a_145_);
lean_dec(v___x_124_);
v___x_147_ = lean_box(0);
v_isShared_148_ = v_isSharedCheck_152_;
goto v_resetjp_146_;
}
v_resetjp_146_:
{
lean_object* v___x_150_; 
if (v_isShared_148_ == 0)
{
v___x_150_ = v___x_147_;
goto v_reusejp_149_;
}
else
{
lean_object* v_reuseFailAlloc_151_; 
v_reuseFailAlloc_151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_151_, 0, v_a_145_);
v___x_150_ = v_reuseFailAlloc_151_;
goto v_reusejp_149_;
}
v_reusejp_149_:
{
return v___x_150_;
}
}
}
}
}
else
{
lean_object* v___x_153_; lean_object* v___x_154_; 
lean_dec_ref(v___x_70_);
v___x_153_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__15, &l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__15_once, _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__15);
v___x_154_ = l_Lean_Meta_Simp_Arith_Nat_toContextExpr(v_snd_63_, v_a_48_, v_a_49_, v_a_50_, v_a_51_);
if (lean_obj_tag(v___x_154_) == 0)
{
lean_object* v_a_155_; lean_object* v___x_157_; uint8_t v_isShared_158_; uint8_t v_isSharedCheck_174_; 
v_a_155_ = lean_ctor_get(v___x_154_, 0);
v_isSharedCheck_174_ = !lean_is_exclusive(v___x_154_);
if (v_isSharedCheck_174_ == 0)
{
v___x_157_ = v___x_154_;
v_isShared_158_ = v_isSharedCheck_174_;
goto v_resetjp_156_;
}
else
{
lean_inc(v_a_155_);
lean_dec(v___x_154_);
v___x_157_ = lean_box(0);
v_isShared_158_ = v_isSharedCheck_174_;
goto v_resetjp_156_;
}
v_resetjp_156_:
{
lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_166_; 
v___x_159_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__18, &l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__18_once, _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__18);
v___x_160_ = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr(v_fst_62_);
v___x_161_ = l_Lean_eagerReflBoolTrue;
v___x_162_ = l_Lean_mkApp3(v___x_159_, v_a_155_, v___x_160_, v___x_161_);
v___x_163_ = l_Lean_mkPropEq(v_a_68_, v___x_153_);
v___x_164_ = l_Lean_Meta_mkExpectedPropHint(v___x_162_, v___x_163_);
if (v_isShared_66_ == 0)
{
lean_ctor_set(v___x_65_, 1, v___x_164_);
lean_ctor_set(v___x_65_, 0, v___x_153_);
v___x_166_ = v___x_65_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_173_; 
v_reuseFailAlloc_173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_173_, 0, v___x_153_);
lean_ctor_set(v_reuseFailAlloc_173_, 1, v___x_164_);
v___x_166_ = v_reuseFailAlloc_173_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
lean_object* v___x_168_; 
if (v_isShared_61_ == 0)
{
lean_ctor_set(v___x_60_, 0, v___x_166_);
v___x_168_ = v___x_60_;
goto v_reusejp_167_;
}
else
{
lean_object* v_reuseFailAlloc_172_; 
v_reuseFailAlloc_172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_172_, 0, v___x_166_);
v___x_168_ = v_reuseFailAlloc_172_;
goto v_reusejp_167_;
}
v_reusejp_167_:
{
lean_object* v___x_170_; 
if (v_isShared_158_ == 0)
{
lean_ctor_set(v___x_157_, 0, v___x_168_);
v___x_170_ = v___x_157_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v___x_168_);
v___x_170_ = v_reuseFailAlloc_171_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
return v___x_170_;
}
}
}
}
}
else
{
lean_object* v_a_175_; lean_object* v___x_177_; uint8_t v_isShared_178_; uint8_t v_isSharedCheck_182_; 
lean_dec(v_a_68_);
lean_del_object(v___x_65_);
lean_dec(v_fst_62_);
lean_del_object(v___x_60_);
v_a_175_ = lean_ctor_get(v___x_154_, 0);
v_isSharedCheck_182_ = !lean_is_exclusive(v___x_154_);
if (v_isSharedCheck_182_ == 0)
{
v___x_177_ = v___x_154_;
v_isShared_178_ = v_isSharedCheck_182_;
goto v_resetjp_176_;
}
else
{
lean_inc(v_a_175_);
lean_dec(v___x_154_);
v___x_177_ = lean_box(0);
v_isShared_178_ = v_isSharedCheck_182_;
goto v_resetjp_176_;
}
v_resetjp_176_:
{
lean_object* v___x_180_; 
if (v_isShared_178_ == 0)
{
v___x_180_ = v___x_177_;
goto v_reusejp_179_;
}
else
{
lean_object* v_reuseFailAlloc_181_; 
v_reuseFailAlloc_181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_181_, 0, v_a_175_);
v___x_180_ = v_reuseFailAlloc_181_;
goto v_reusejp_179_;
}
v_reusejp_179_:
{
return v___x_180_;
}
}
}
}
}
else
{
lean_object* v_a_183_; lean_object* v___x_185_; uint8_t v_isShared_186_; uint8_t v_isSharedCheck_190_; 
lean_del_object(v___x_65_);
lean_dec(v_snd_63_);
lean_dec(v_fst_62_);
lean_del_object(v___x_60_);
v_a_183_ = lean_ctor_get(v___x_67_, 0);
v_isSharedCheck_190_ = !lean_is_exclusive(v___x_67_);
if (v_isSharedCheck_190_ == 0)
{
v___x_185_ = v___x_67_;
v_isShared_186_ = v_isSharedCheck_190_;
goto v_resetjp_184_;
}
else
{
lean_inc(v_a_183_);
lean_dec(v___x_67_);
v___x_185_ = lean_box(0);
v_isShared_186_ = v_isSharedCheck_190_;
goto v_resetjp_184_;
}
v_resetjp_184_:
{
lean_object* v___x_188_; 
if (v_isShared_186_ == 0)
{
v___x_188_ = v___x_185_;
goto v_reusejp_187_;
}
else
{
lean_object* v_reuseFailAlloc_189_; 
v_reuseFailAlloc_189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_189_, 0, v_a_183_);
v___x_188_ = v_reuseFailAlloc_189_;
goto v_reusejp_187_;
}
v_reusejp_187_:
{
return v___x_188_;
}
}
}
}
}
}
else
{
lean_object* v___x_193_; lean_object* v___x_195_; 
lean_dec(v_a_54_);
v___x_193_ = lean_box(0);
if (v_isShared_57_ == 0)
{
lean_ctor_set(v___x_56_, 0, v___x_193_);
v___x_195_ = v___x_56_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_196_; 
v_reuseFailAlloc_196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_196_, 0, v___x_193_);
v___x_195_ = v_reuseFailAlloc_196_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
return v___x_195_;
}
}
}
}
else
{
lean_object* v_a_198_; lean_object* v___x_200_; uint8_t v_isShared_201_; uint8_t v_isSharedCheck_205_; 
v_a_198_ = lean_ctor_get(v___x_53_, 0);
v_isSharedCheck_205_ = !lean_is_exclusive(v___x_53_);
if (v_isSharedCheck_205_ == 0)
{
v___x_200_ = v___x_53_;
v_isShared_201_ = v_isSharedCheck_205_;
goto v_resetjp_199_;
}
else
{
lean_inc(v_a_198_);
lean_dec(v___x_53_);
v___x_200_ = lean_box(0);
v_isShared_201_ = v_isSharedCheck_205_;
goto v_resetjp_199_;
}
v_resetjp_199_:
{
lean_object* v___x_203_; 
if (v_isShared_201_ == 0)
{
v___x_203_ = v___x_200_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v_a_198_);
v___x_203_ = v_reuseFailAlloc_204_;
goto v_reusejp_202_;
}
v_reusejp_202_:
{
return v___x_203_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___boxed(lean_object* v_e_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_, lean_object* v_a_210_, lean_object* v_a_211_){
_start:
{
lean_object* v_res_212_; 
v_res_212_ = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f(v_e_206_, v_a_207_, v_a_208_, v_a_209_, v_a_210_);
lean_dec(v_a_210_);
lean_dec_ref(v_a_209_);
lean_dec(v_a_208_);
lean_dec_ref(v_a_207_);
return v_res_212_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__3(void){
_start:
{
lean_object* v___x_218_; lean_object* v___x_219_; 
v___x_218_ = lean_box(0);
v___x_219_ = l_Lean_Level_succ___override(v___x_218_);
return v___x_219_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__4(void){
_start:
{
lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_220_ = lean_box(0);
v___x_221_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__3, &l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__3_once, _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__3);
v___x_222_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_222_, 0, v___x_221_);
lean_ctor_set(v___x_222_, 1, v___x_220_);
return v___x_222_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__5(void){
_start:
{
lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; 
v___x_223_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__4, &l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__4_once, _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__4);
v___x_224_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__2));
v___x_225_ = l_Lean_mkConst(v___x_224_, v___x_223_);
return v___x_225_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__6(void){
_start:
{
lean_object* v___x_226_; lean_object* v___x_227_; 
v___x_226_ = lean_box(0);
v___x_227_ = l_Lean_mkSort(v___x_226_);
return v___x_227_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__22(void){
_start:
{
lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_253_ = lean_unsigned_to_nat(1u);
v___x_254_ = l_Lean_mkNatLit(v___x_253_);
return v___x_254_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__25(void){
_start:
{
lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; 
v___x_259_ = lean_box(0);
v___x_260_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__24));
v___x_261_ = l_Lean_mkConst(v___x_260_, v___x_259_);
return v___x_261_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__28(void){
_start:
{
lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_266_ = lean_box(0);
v___x_267_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__27));
v___x_268_ = l_Lean_mkConst(v___x_267_, v___x_266_);
return v___x_268_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__31(void){
_start:
{
lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_273_ = lean_box(0);
v___x_274_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__30));
v___x_275_ = l_Lean_mkConst(v___x_274_, v___x_273_);
return v___x_275_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__34(void){
_start:
{
lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_280_ = lean_box(0);
v___x_281_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__33));
v___x_282_ = l_Lean_mkConst(v___x_281_, v___x_280_);
return v___x_282_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__35(void){
_start:
{
lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_283_ = lean_unsigned_to_nat(0u);
v___x_284_ = l_Lean_Level_ofNat(v___x_283_);
return v___x_284_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__36(void){
_start:
{
lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_285_ = lean_unsigned_to_nat(1u);
v___x_286_ = l_Lean_Level_ofNat(v___x_285_);
return v___x_286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f(lean_object* v_e_287_, lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_){
_start:
{
lean_object* v_val_294_; lean_object* v_h_u2081_295_; lean_object* v___y_296_; lean_object* v___y_297_; lean_object* v___y_298_; lean_object* v___y_299_; lean_object* v___x_337_; lean_object* v___x_338_; uint8_t v___x_339_; 
v___x_337_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__8));
v___x_338_ = lean_unsigned_to_nat(1u);
v___x_339_ = l_Lean_Expr_isAppOfArity(v_e_287_, v___x_337_, v___x_338_);
if (v___x_339_ == 0)
{
lean_object* v___x_340_; 
v___x_340_ = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f(v_e_287_, v_a_288_, v_a_289_, v_a_290_, v_a_291_);
return v___x_340_;
}
else
{
lean_object* v___x_341_; lean_object* v_leLvl_343_; lean_object* v___y_344_; lean_object* v___y_345_; lean_object* v___y_346_; lean_object* v___y_347_; lean_object* v___x_446_; 
v___x_341_ = l_Lean_Expr_appArg_x21(v_e_287_);
v___x_446_ = l_Lean_leCarrierIsSort(v_a_290_, v_a_291_);
if (lean_obj_tag(v___x_446_) == 0)
{
lean_object* v_a_447_; uint8_t v___x_448_; 
v_a_447_ = lean_ctor_get(v___x_446_, 0);
lean_inc(v_a_447_);
lean_dec_ref_known(v___x_446_, 1);
v___x_448_ = lean_unbox(v_a_447_);
lean_dec(v_a_447_);
if (v___x_448_ == 0)
{
lean_object* v___x_449_; 
v___x_449_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__35, &l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__35_once, _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__35);
v_leLvl_343_ = v___x_449_;
v___y_344_ = v_a_288_;
v___y_345_ = v_a_289_;
v___y_346_ = v_a_290_;
v___y_347_ = v_a_291_;
goto v___jp_342_;
}
else
{
lean_object* v___x_450_; 
v___x_450_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__36, &l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__36_once, _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__36);
v_leLvl_343_ = v___x_450_;
v___y_344_ = v_a_288_;
v___y_345_ = v_a_289_;
v___y_346_ = v_a_290_;
v___y_347_ = v_a_291_;
goto v___jp_342_;
}
}
else
{
lean_object* v_a_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_458_; 
lean_dec_ref(v___x_341_);
lean_dec_ref(v_e_287_);
v_a_451_ = lean_ctor_get(v___x_446_, 0);
v_isSharedCheck_458_ = !lean_is_exclusive(v___x_446_);
if (v_isSharedCheck_458_ == 0)
{
v___x_453_ = v___x_446_;
v_isShared_454_ = v_isSharedCheck_458_;
goto v_resetjp_452_;
}
else
{
lean_inc(v_a_451_);
lean_dec(v___x_446_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_458_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
lean_object* v___x_456_; 
if (v_isShared_454_ == 0)
{
v___x_456_ = v___x_453_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v_a_451_);
v___x_456_ = v_reuseFailAlloc_457_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
return v___x_456_;
}
}
}
v___jp_342_:
{
lean_object* v___x_348_; 
v___x_348_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v___x_341_, v___y_345_);
if (lean_obj_tag(v___x_348_) == 0)
{
lean_object* v_a_349_; lean_object* v___x_350_; uint8_t v___x_351_; 
v_a_349_ = lean_ctor_get(v___x_348_, 0);
lean_inc(v_a_349_);
lean_dec_ref_known(v___x_348_, 1);
v___x_350_ = l_Lean_Expr_cleanupAnnotations(v_a_349_);
lean_dec(v_a_349_);
v___x_351_ = l_Lean_Expr_isApp(v___x_350_);
if (v___x_351_ == 0)
{
lean_dec_ref(v___x_350_);
lean_dec_ref(v_e_287_);
goto v___jp_334_;
}
else
{
lean_object* v___x_352_; uint8_t v___x_353_; 
v___x_352_ = l_Lean_Expr_appFnCleanup___redArg(v___x_350_);
v___x_353_ = l_Lean_Expr_isApp(v___x_352_);
if (v___x_353_ == 0)
{
lean_dec_ref(v___x_352_);
lean_dec_ref(v___x_350_);
lean_dec_ref(v_e_287_);
goto v___jp_334_;
}
else
{
lean_object* v___x_354_; uint8_t v___x_355_; 
v___x_354_ = l_Lean_Expr_appFnCleanup___redArg(v___x_352_);
v___x_355_ = l_Lean_Expr_isApp(v___x_354_);
if (v___x_355_ == 0)
{
lean_dec_ref(v___x_354_);
lean_dec_ref(v___x_352_);
lean_dec_ref(v___x_350_);
lean_dec_ref(v_e_287_);
goto v___jp_334_;
}
else
{
lean_object* v___x_356_; uint8_t v___x_357_; 
v___x_356_ = l_Lean_Expr_appFnCleanup___redArg(v___x_354_);
lean_dec_ref(v___x_354_);
v___x_357_ = l_Lean_Expr_isApp(v___x_356_);
if (v___x_357_ == 0)
{
lean_dec_ref(v___x_356_);
lean_dec_ref(v___x_352_);
lean_dec_ref(v___x_350_);
lean_dec_ref(v_e_287_);
goto v___jp_334_;
}
else
{
lean_object* v_arg_358_; lean_object* v_arg_359_; lean_object* v_arg_360_; lean_object* v___x_361_; lean_object* v___x_362_; uint8_t v___x_363_; 
v_arg_358_ = lean_ctor_get(v___x_350_, 1);
lean_inc_ref(v_arg_358_);
lean_dec_ref(v___x_350_);
v_arg_359_ = lean_ctor_get(v___x_352_, 1);
lean_inc_ref(v_arg_359_);
lean_dec_ref(v___x_352_);
v_arg_360_ = lean_ctor_get(v___x_356_, 1);
lean_inc_ref(v_arg_360_);
v___x_361_ = l_Lean_Expr_appFnCleanup___redArg(v___x_356_);
lean_dec_ref(v___x_356_);
v___x_362_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__11));
v___x_363_ = l_Lean_Expr_isConstOf(v___x_361_, v___x_362_);
if (v___x_363_ == 0)
{
lean_object* v___x_364_; uint8_t v___x_365_; 
v___x_364_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__14));
v___x_365_ = l_Lean_Expr_isConstOf(v___x_361_, v___x_364_);
if (v___x_365_ == 0)
{
lean_object* v___x_366_; uint8_t v___x_367_; 
v___x_366_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__17));
v___x_367_ = l_Lean_Expr_isConstOf(v___x_361_, v___x_366_);
if (v___x_367_ == 0)
{
lean_object* v___x_368_; uint8_t v___x_369_; 
v___x_368_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__20));
v___x_369_ = l_Lean_Expr_isConstOf(v___x_361_, v___x_368_);
lean_dec_ref(v___x_361_);
if (v___x_369_ == 0)
{
lean_dec_ref(v_arg_360_);
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_358_);
lean_dec_ref(v_e_287_);
goto v___jp_334_;
}
else
{
lean_object* v___x_370_; 
v___x_370_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_360_, v___y_345_);
if (lean_obj_tag(v___x_370_) == 0)
{
lean_object* v_a_371_; lean_object* v___x_372_; lean_object* v___x_373_; uint8_t v___x_374_; 
v_a_371_ = lean_ctor_get(v___x_370_, 0);
lean_inc(v_a_371_);
lean_dec_ref_known(v___x_370_, 1);
v___x_372_ = l_Lean_Expr_cleanupAnnotations(v_a_371_);
lean_dec(v_a_371_);
v___x_373_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__21));
v___x_374_ = l_Lean_Expr_isConstOf(v___x_372_, v___x_373_);
lean_dec_ref(v___x_372_);
if (v___x_374_ == 0)
{
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_358_);
lean_dec_ref(v_e_287_);
goto v___jp_334_;
}
else
{
lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_375_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__22, &l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__22_once, _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__22);
lean_inc_ref(v_arg_358_);
v___x_376_ = l_Lean_mkNatAdd(v_arg_358_, v___x_375_);
lean_inc_ref(v_arg_359_);
lean_inc(v_leLvl_343_);
v___x_377_ = l_Lean_mkNatLE(v_leLvl_343_, v___x_376_, v_arg_359_);
v___x_378_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__25, &l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__25_once, _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__25);
v___x_379_ = l_Lean_mkAppB(v___x_378_, v_arg_359_, v_arg_358_);
v_val_294_ = v___x_377_;
v_h_u2081_295_ = v___x_379_;
v___y_296_ = v___y_344_;
v___y_297_ = v___y_345_;
v___y_298_ = v___y_346_;
v___y_299_ = v___y_347_;
goto v___jp_293_;
}
}
else
{
lean_object* v_a_380_; lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_387_; 
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_358_);
lean_dec_ref(v_e_287_);
v_a_380_ = lean_ctor_get(v___x_370_, 0);
v_isSharedCheck_387_ = !lean_is_exclusive(v___x_370_);
if (v_isSharedCheck_387_ == 0)
{
v___x_382_ = v___x_370_;
v_isShared_383_ = v_isSharedCheck_387_;
goto v_resetjp_381_;
}
else
{
lean_inc(v_a_380_);
lean_dec(v___x_370_);
v___x_382_ = lean_box(0);
v_isShared_383_ = v_isSharedCheck_387_;
goto v_resetjp_381_;
}
v_resetjp_381_:
{
lean_object* v___x_385_; 
if (v_isShared_383_ == 0)
{
v___x_385_ = v___x_382_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_386_; 
v_reuseFailAlloc_386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_386_, 0, v_a_380_);
v___x_385_ = v_reuseFailAlloc_386_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
return v___x_385_;
}
}
}
}
}
else
{
lean_object* v___x_388_; 
lean_dec_ref(v___x_361_);
v___x_388_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_360_, v___y_345_);
if (lean_obj_tag(v___x_388_) == 0)
{
lean_object* v_a_389_; lean_object* v___x_390_; lean_object* v___x_391_; uint8_t v___x_392_; 
v_a_389_ = lean_ctor_get(v___x_388_, 0);
lean_inc(v_a_389_);
lean_dec_ref_known(v___x_388_, 1);
v___x_390_ = l_Lean_Expr_cleanupAnnotations(v_a_389_);
lean_dec(v_a_389_);
v___x_391_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__21));
v___x_392_ = l_Lean_Expr_isConstOf(v___x_390_, v___x_391_);
lean_dec_ref(v___x_390_);
if (v___x_392_ == 0)
{
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_358_);
lean_dec_ref(v_e_287_);
goto v___jp_334_;
}
else
{
lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_393_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__22, &l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__22_once, _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__22);
lean_inc_ref(v_arg_359_);
v___x_394_ = l_Lean_mkNatAdd(v_arg_359_, v___x_393_);
lean_inc_ref(v_arg_358_);
lean_inc(v_leLvl_343_);
v___x_395_ = l_Lean_mkNatLE(v_leLvl_343_, v___x_394_, v_arg_358_);
v___x_396_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__28, &l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__28_once, _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__28);
v___x_397_ = l_Lean_mkAppB(v___x_396_, v_arg_359_, v_arg_358_);
v_val_294_ = v___x_395_;
v_h_u2081_295_ = v___x_397_;
v___y_296_ = v___y_344_;
v___y_297_ = v___y_345_;
v___y_298_ = v___y_346_;
v___y_299_ = v___y_347_;
goto v___jp_293_;
}
}
else
{
lean_object* v_a_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_405_; 
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_358_);
lean_dec_ref(v_e_287_);
v_a_398_ = lean_ctor_get(v___x_388_, 0);
v_isSharedCheck_405_ = !lean_is_exclusive(v___x_388_);
if (v_isSharedCheck_405_ == 0)
{
v___x_400_ = v___x_388_;
v_isShared_401_ = v_isSharedCheck_405_;
goto v_resetjp_399_;
}
else
{
lean_inc(v_a_398_);
lean_dec(v___x_388_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_405_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
lean_object* v___x_403_; 
if (v_isShared_401_ == 0)
{
v___x_403_ = v___x_400_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v_a_398_);
v___x_403_ = v_reuseFailAlloc_404_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
return v___x_403_;
}
}
}
}
}
else
{
lean_object* v___x_406_; 
lean_dec_ref(v___x_361_);
v___x_406_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_360_, v___y_345_);
if (lean_obj_tag(v___x_406_) == 0)
{
lean_object* v_a_407_; lean_object* v___x_408_; lean_object* v___x_409_; uint8_t v___x_410_; 
v_a_407_ = lean_ctor_get(v___x_406_, 0);
lean_inc(v_a_407_);
lean_dec_ref_known(v___x_406_, 1);
v___x_408_ = l_Lean_Expr_cleanupAnnotations(v_a_407_);
lean_dec(v_a_407_);
v___x_409_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__21));
v___x_410_ = l_Lean_Expr_isConstOf(v___x_408_, v___x_409_);
lean_dec_ref(v___x_408_);
if (v___x_410_ == 0)
{
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_358_);
lean_dec_ref(v_e_287_);
goto v___jp_334_;
}
else
{
lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; 
lean_inc_ref(v_arg_359_);
lean_inc_ref(v_arg_358_);
lean_inc(v_leLvl_343_);
v___x_411_ = l_Lean_mkNatLE(v_leLvl_343_, v_arg_358_, v_arg_359_);
v___x_412_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__31, &l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__31_once, _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__31);
v___x_413_ = l_Lean_mkAppB(v___x_412_, v_arg_359_, v_arg_358_);
v_val_294_ = v___x_411_;
v_h_u2081_295_ = v___x_413_;
v___y_296_ = v___y_344_;
v___y_297_ = v___y_345_;
v___y_298_ = v___y_346_;
v___y_299_ = v___y_347_;
goto v___jp_293_;
}
}
else
{
lean_object* v_a_414_; lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_421_; 
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_358_);
lean_dec_ref(v_e_287_);
v_a_414_ = lean_ctor_get(v___x_406_, 0);
v_isSharedCheck_421_ = !lean_is_exclusive(v___x_406_);
if (v_isSharedCheck_421_ == 0)
{
v___x_416_ = v___x_406_;
v_isShared_417_ = v_isSharedCheck_421_;
goto v_resetjp_415_;
}
else
{
lean_inc(v_a_414_);
lean_dec(v___x_406_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_421_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
lean_object* v___x_419_; 
if (v_isShared_417_ == 0)
{
v___x_419_ = v___x_416_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v_a_414_);
v___x_419_ = v_reuseFailAlloc_420_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
return v___x_419_;
}
}
}
}
}
else
{
lean_object* v___x_422_; 
lean_dec_ref(v___x_361_);
v___x_422_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_360_, v___y_345_);
if (lean_obj_tag(v___x_422_) == 0)
{
lean_object* v_a_423_; lean_object* v___x_424_; lean_object* v___x_425_; uint8_t v___x_426_; 
v_a_423_ = lean_ctor_get(v___x_422_, 0);
lean_inc(v_a_423_);
lean_dec_ref_known(v___x_422_, 1);
v___x_424_ = l_Lean_Expr_cleanupAnnotations(v_a_423_);
lean_dec(v_a_423_);
v___x_425_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__21));
v___x_426_ = l_Lean_Expr_isConstOf(v___x_424_, v___x_425_);
lean_dec_ref(v___x_424_);
if (v___x_426_ == 0)
{
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_358_);
lean_dec_ref(v_e_287_);
goto v___jp_334_;
}
else
{
lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; 
lean_inc_ref(v_arg_358_);
lean_inc_ref(v_arg_359_);
lean_inc(v_leLvl_343_);
v___x_427_ = l_Lean_mkNatLE(v_leLvl_343_, v_arg_359_, v_arg_358_);
v___x_428_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__34, &l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__34_once, _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__34);
v___x_429_ = l_Lean_mkAppB(v___x_428_, v_arg_359_, v_arg_358_);
v_val_294_ = v___x_427_;
v_h_u2081_295_ = v___x_429_;
v___y_296_ = v___y_344_;
v___y_297_ = v___y_345_;
v___y_298_ = v___y_346_;
v___y_299_ = v___y_347_;
goto v___jp_293_;
}
}
else
{
lean_object* v_a_430_; lean_object* v___x_432_; uint8_t v_isShared_433_; uint8_t v_isSharedCheck_437_; 
lean_dec_ref(v_arg_359_);
lean_dec_ref(v_arg_358_);
lean_dec_ref(v_e_287_);
v_a_430_ = lean_ctor_get(v___x_422_, 0);
v_isSharedCheck_437_ = !lean_is_exclusive(v___x_422_);
if (v_isSharedCheck_437_ == 0)
{
v___x_432_ = v___x_422_;
v_isShared_433_ = v_isSharedCheck_437_;
goto v_resetjp_431_;
}
else
{
lean_inc(v_a_430_);
lean_dec(v___x_422_);
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
}
}
}
}
}
else
{
lean_object* v_a_438_; lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_445_; 
lean_dec_ref(v_e_287_);
v_a_438_ = lean_ctor_get(v___x_348_, 0);
v_isSharedCheck_445_ = !lean_is_exclusive(v___x_348_);
if (v_isSharedCheck_445_ == 0)
{
v___x_440_ = v___x_348_;
v_isShared_441_ = v_isSharedCheck_445_;
goto v_resetjp_439_;
}
else
{
lean_inc(v_a_438_);
lean_dec(v___x_348_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_445_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
lean_object* v___x_443_; 
if (v_isShared_441_ == 0)
{
v___x_443_ = v___x_440_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v_a_438_);
v___x_443_ = v_reuseFailAlloc_444_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
return v___x_443_;
}
}
}
}
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
v___x_316_ = l_Lean_mkApp6(v___x_314_, v___x_315_, v_e_287_, v_val_294_, v_fst_309_, v_h_u2081_295_, v_snd_310_);
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
lean_dec_ref(v_e_287_);
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
lean_dec_ref(v_e_287_);
return v___x_300_;
}
}
v___jp_334_:
{
lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_335_ = lean_box(0);
v___x_336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_336_, 0, v___x_335_);
return v___x_336_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___boxed(lean_object* v_e_459_, lean_object* v_a_460_, lean_object* v_a_461_, lean_object* v_a_462_, lean_object* v_a_463_, lean_object* v_a_464_){
_start:
{
lean_object* v_res_465_; 
v_res_465_ = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f(v_e_459_, v_a_460_, v_a_461_, v_a_462_, v_a_463_);
lean_dec(v_a_463_);
lean_dec_ref(v_a_462_);
lean_dec(v_a_461_);
lean_dec_ref(v_a_460_);
return v_res_465_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___closed__2(void){
_start:
{
lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; 
v___x_473_ = lean_box(0);
v___x_474_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___closed__1));
v___x_475_ = l_Lean_mkConst(v___x_474_, v___x_473_);
return v___x_475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f(lean_object* v_input_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_, lean_object* v_a_480_){
_start:
{
lean_object* v___x_482_; 
v___x_482_ = l_Lean_Meta_Simp_Arith_Nat_toLinearExpr(v_input_476_, v_a_477_, v_a_478_, v_a_479_, v_a_480_);
if (lean_obj_tag(v___x_482_) == 0)
{
lean_object* v_a_483_; lean_object* v___x_485_; uint8_t v_isShared_486_; uint8_t v_isSharedCheck_549_; 
v_a_483_ = lean_ctor_get(v___x_482_, 0);
v_isSharedCheck_549_ = !lean_is_exclusive(v___x_482_);
if (v_isSharedCheck_549_ == 0)
{
v___x_485_ = v___x_482_;
v_isShared_486_ = v_isSharedCheck_549_;
goto v_resetjp_484_;
}
else
{
lean_inc(v_a_483_);
lean_dec(v___x_482_);
v___x_485_ = lean_box(0);
v_isShared_486_ = v_isSharedCheck_549_;
goto v_resetjp_484_;
}
v_resetjp_484_:
{
lean_object* v_fst_487_; lean_object* v_snd_488_; lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_548_; 
v_fst_487_ = lean_ctor_get(v_a_483_, 0);
v_snd_488_ = lean_ctor_get(v_a_483_, 1);
v_isSharedCheck_548_ = !lean_is_exclusive(v_a_483_);
if (v_isSharedCheck_548_ == 0)
{
v___x_490_ = v_a_483_;
v_isShared_491_ = v_isSharedCheck_548_;
goto v_resetjp_489_;
}
else
{
lean_inc(v_snd_488_);
lean_inc(v_fst_487_);
lean_dec(v_a_483_);
v___x_490_ = lean_box(0);
v_isShared_491_ = v_isSharedCheck_548_;
goto v_resetjp_489_;
}
v_resetjp_489_:
{
lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; uint8_t v___x_495_; 
v___x_492_ = l_Nat_Internal_Linear_Expr_toPoly(v_fst_487_);
v___x_493_ = l_Nat_Internal_Linear_Poly_norm(v___x_492_);
v___x_494_ = l_Nat_Internal_Linear_Poly_toExpr(v___x_493_);
v___x_495_ = l_Nat_Internal_Linear_instBEqExpr_beq(v___x_494_, v_fst_487_);
if (v___x_495_ == 0)
{
lean_object* v___x_496_; 
lean_del_object(v___x_485_);
lean_inc(v_snd_488_);
v___x_496_ = l_Lean_Meta_Simp_Arith_Nat_toContextExpr(v_snd_488_, v_a_477_, v_a_478_, v_a_479_, v_a_480_);
if (lean_obj_tag(v___x_496_) == 0)
{
lean_object* v_a_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; 
v_a_497_ = lean_ctor_get(v___x_496_, 0);
lean_inc(v_a_497_);
lean_dec_ref_known(v___x_496_, 1);
v___x_498_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___closed__2, &l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___closed__2_once, _init_l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___closed__2);
lean_inc(v_fst_487_);
v___x_499_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr(v_fst_487_);
lean_inc_ref(v___x_494_);
v___x_500_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr(v___x_494_);
v___x_501_ = l_Lean_eagerReflBoolTrue;
v___x_502_ = l_Lean_mkApp4(v___x_498_, v_a_497_, v___x_499_, v___x_500_, v___x_501_);
v___x_503_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(v_snd_488_, v_fst_487_);
if (lean_obj_tag(v___x_503_) == 0)
{
lean_object* v_a_504_; lean_object* v___x_505_; 
v_a_504_ = lean_ctor_get(v___x_503_, 0);
lean_inc(v_a_504_);
lean_dec_ref_known(v___x_503_, 1);
v___x_505_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(v_snd_488_, v___x_494_);
lean_dec(v_snd_488_);
if (lean_obj_tag(v___x_505_) == 0)
{
lean_object* v_a_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_519_; 
v_a_506_ = lean_ctor_get(v___x_505_, 0);
v_isSharedCheck_519_ = !lean_is_exclusive(v___x_505_);
if (v_isSharedCheck_519_ == 0)
{
v___x_508_ = v___x_505_;
v_isShared_509_ = v_isSharedCheck_519_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_a_506_);
lean_dec(v___x_505_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_519_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_513_; 
lean_inc(v_a_506_);
v___x_510_ = l_Lean_mkNatEq(v_a_504_, v_a_506_);
v___x_511_ = l_Lean_Meta_mkExpectedPropHint(v___x_502_, v___x_510_);
if (v_isShared_491_ == 0)
{
lean_ctor_set(v___x_490_, 1, v___x_511_);
lean_ctor_set(v___x_490_, 0, v_a_506_);
v___x_513_ = v___x_490_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v_a_506_);
lean_ctor_set(v_reuseFailAlloc_518_, 1, v___x_511_);
v___x_513_ = v_reuseFailAlloc_518_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
lean_object* v___x_514_; lean_object* v___x_516_; 
v___x_514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_514_, 0, v___x_513_);
if (v_isShared_509_ == 0)
{
lean_ctor_set(v___x_508_, 0, v___x_514_);
v___x_516_ = v___x_508_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v___x_514_);
v___x_516_ = v_reuseFailAlloc_517_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
return v___x_516_;
}
}
}
}
else
{
lean_object* v_a_520_; lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_527_; 
lean_dec(v_a_504_);
lean_dec_ref(v___x_502_);
lean_del_object(v___x_490_);
v_a_520_ = lean_ctor_get(v___x_505_, 0);
v_isSharedCheck_527_ = !lean_is_exclusive(v___x_505_);
if (v_isSharedCheck_527_ == 0)
{
v___x_522_ = v___x_505_;
v_isShared_523_ = v_isSharedCheck_527_;
goto v_resetjp_521_;
}
else
{
lean_inc(v_a_520_);
lean_dec(v___x_505_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_527_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
lean_object* v___x_525_; 
if (v_isShared_523_ == 0)
{
v___x_525_ = v___x_522_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v_a_520_);
v___x_525_ = v_reuseFailAlloc_526_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
return v___x_525_;
}
}
}
}
else
{
lean_object* v_a_528_; lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_535_; 
lean_dec_ref(v___x_502_);
lean_dec_ref(v___x_494_);
lean_del_object(v___x_490_);
lean_dec(v_snd_488_);
v_a_528_ = lean_ctor_get(v___x_503_, 0);
v_isSharedCheck_535_ = !lean_is_exclusive(v___x_503_);
if (v_isSharedCheck_535_ == 0)
{
v___x_530_ = v___x_503_;
v_isShared_531_ = v_isSharedCheck_535_;
goto v_resetjp_529_;
}
else
{
lean_inc(v_a_528_);
lean_dec(v___x_503_);
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
else
{
lean_object* v_a_536_; lean_object* v___x_538_; uint8_t v_isShared_539_; uint8_t v_isSharedCheck_543_; 
lean_dec_ref(v___x_494_);
lean_del_object(v___x_490_);
lean_dec(v_snd_488_);
lean_dec(v_fst_487_);
v_a_536_ = lean_ctor_get(v___x_496_, 0);
v_isSharedCheck_543_ = !lean_is_exclusive(v___x_496_);
if (v_isSharedCheck_543_ == 0)
{
v___x_538_ = v___x_496_;
v_isShared_539_ = v_isSharedCheck_543_;
goto v_resetjp_537_;
}
else
{
lean_inc(v_a_536_);
lean_dec(v___x_496_);
v___x_538_ = lean_box(0);
v_isShared_539_ = v_isSharedCheck_543_;
goto v_resetjp_537_;
}
v_resetjp_537_:
{
lean_object* v___x_541_; 
if (v_isShared_539_ == 0)
{
v___x_541_ = v___x_538_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v_a_536_);
v___x_541_ = v_reuseFailAlloc_542_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
return v___x_541_;
}
}
}
}
else
{
lean_object* v___x_544_; lean_object* v___x_546_; 
lean_dec_ref(v___x_494_);
lean_del_object(v___x_490_);
lean_dec(v_snd_488_);
lean_dec(v_fst_487_);
v___x_544_ = lean_box(0);
if (v_isShared_486_ == 0)
{
lean_ctor_set(v___x_485_, 0, v___x_544_);
v___x_546_ = v___x_485_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v___x_544_);
v___x_546_ = v_reuseFailAlloc_547_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
return v___x_546_;
}
}
}
}
}
else
{
lean_object* v_a_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_557_; 
v_a_550_ = lean_ctor_get(v___x_482_, 0);
v_isSharedCheck_557_ = !lean_is_exclusive(v___x_482_);
if (v_isSharedCheck_557_ == 0)
{
v___x_552_ = v___x_482_;
v_isShared_553_ = v_isSharedCheck_557_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_a_550_);
lean_dec(v___x_482_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_557_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
lean_object* v___x_555_; 
if (v_isShared_553_ == 0)
{
v___x_555_ = v___x_552_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v_a_550_);
v___x_555_ = v_reuseFailAlloc_556_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
return v___x_555_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___boxed(lean_object* v_input_558_, lean_object* v_a_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_){
_start:
{
lean_object* v_res_564_; 
v_res_564_ = l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f(v_input_558_, v_a_559_, v_a_560_, v_a_561_, v_a_562_);
lean_dec(v_a_562_);
lean_dec_ref(v_a_561_);
lean_dec(v_a_560_);
lean_dec_ref(v_a_559_);
return v_res_564_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Arith_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Arith_Nat_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* runtime_initialize_Lean_CoreM(uint8_t builtin);
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
res = runtime_initialize_Lean_CoreM(builtin);
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
lean_object* initialize_Lean_CoreM(uint8_t builtin);
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
res = initialize_Lean_CoreM(builtin);
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

// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.Arith.Int.Simp
// Imports: public import Lean.Meta.Tactic.Simp.Arith.Util public import Lean.Meta.Tactic.Simp.Arith.Int.Basic
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
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_gcd(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIntLit(lean_object*);
lean_object* l_Lean_Level_succ___override(lean_object*);
lean_object* l_Lean_Meta_Simp_Arith_Int_toLinearExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Internal_Linear_Expr_norm(lean_object*);
lean_object* l_Int_Internal_Linear_Poly_toExpr(lean_object*);
uint8_t l_Int_Internal_Linear_instBEqExpr_beq(lean_object*, lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* l_Lean_Meta_Simp_Arith_Int_toContextExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(lean_object*);
lean_object* l_Int_Internal_Linear_Expr_denoteExpr___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly(lean_object*);
lean_object* l_Int_Internal_Linear_Poly_denoteExpr___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_eagerReflBoolTrue;
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIntEq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkExpectedPropHint(lean_object*, lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* l_Lean_mkPropEq(lean_object*, lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Internal_Linear_Poly_getConst(lean_object*);
lean_object* l_Int_Internal_Linear_Poly_div(lean_object*, lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_mkIntLE(lean_object*, lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* l_Int_toNat(lean_object*);
lean_object* l_Lean_instToExprInt_mkNat(lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Arith_Int_leCnstr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Int_Internal_Linear_Poly_isUnsatLe(lean_object*);
uint8_t l_Int_Internal_Linear_Poly_isValidLe(lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_mkIntAdd(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Arith_Int_dvdCnstr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIntDvd(lean_object*, lean_object*);
lean_object* l_Int_Internal_Linear_Poly_gcdCoeffs(lean_object*, lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Arith_Int_eqCnstr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
uint8_t l_Int_Internal_Linear_Poly_isUnsatEq(lean_object*);
uint8_t l_Int_Internal_Linear_Poly_isValidEq(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Simp_0__Int_Internal_Linear_Poly_gcdAll_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Simp_0__Int_Internal_Linear_Poly_gcdAll_go___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_gcdAll(lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_gcdAll___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Simp_0__Int_Internal_Linear_Poly_gcdCoeffs_x27_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Simp_0__Int_Internal_Linear_Poly_gcdCoeffs_x27_go___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_gcdCoeffs_x27(lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_gcdCoeffs_x27___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_Simp_Arith_Int_simpEq_x3f_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Int"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Internal"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Linear"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__2 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__2_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "norm_eq_var_const"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__3 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(80, 75, 231, 118, 66, 61, 134, 150)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(57, 190, 3, 113, 15, 121, 86, 21)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__4_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__3_value),LEAN_SCALAR_PTR_LITERAL(110, 3, 128, 209, 83, 119, 41, 246)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__4 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "False"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__7 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__7_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__7_value),LEAN_SCALAR_PTR_LITERAL(227, 122, 176, 177, 50, 175, 152, 12)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__9;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "eq_eq_false_of_divCoeff"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__10 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__10_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__11_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(80, 75, 231, 118, 66, 61, 134, 150)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__11_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(57, 190, 3, 113, 15, 121, 86, 21)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__11_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__10_value),LEAN_SCALAR_PTR_LITERAL(166, 111, 217, 210, 57, 89, 97, 230)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__11 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__11_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__12;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Neg"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__13 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__13_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "neg"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__14 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__14_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__13_value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__15_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__14_value),LEAN_SCALAR_PTR_LITERAL(105, 26, 70, 221, 245, 238, 127, 238)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__15 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__15_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__16;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "instNegInt"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__21 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__21_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__21_value),LEAN_SCALAR_PTR_LITERAL(217, 109, 233, 1, 211, 122, 77, 88)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__24;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "norm_eq_coeff"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__25 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__25_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__26_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__26_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(80, 75, 231, 118, 66, 61, 134, 150)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__26_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__26_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(57, 190, 3, 113, 15, 121, 86, 21)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__26_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__25_value),LEAN_SCALAR_PTR_LITERAL(160, 202, 127, 206, 181, 96, 119, 97)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__26 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__26_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__27;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "norm_eq"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__28 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__28_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__29_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__29_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__29_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(80, 75, 231, 118, 66, 61, 134, 150)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__29_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__29_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(57, 190, 3, 113, 15, 121, 86, 21)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__29_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__28_value),LEAN_SCALAR_PTR_LITERAL(97, 114, 204, 9, 138, 244, 137, 99)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__29 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__29_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__31;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__32;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "norm_eq_var"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__33 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__33_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__34_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__34_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__34_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(80, 75, 231, 118, 66, 61, 134, 150)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__34_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__34_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(57, 190, 3, 113, 15, 121, 86, 21)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__34_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__33_value),LEAN_SCALAR_PTR_LITERAL(18, 165, 157, 183, 182, 21, 11, 103)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__34 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__34_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__35;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__36;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "True"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__37 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__37_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__37_value),LEAN_SCALAR_PTR_LITERAL(78, 21, 103, 131, 118, 13, 187, 164)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__38 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__38_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__39_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__39;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "eq_eq_true"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__40 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__40_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__41_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__41_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__41_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(80, 75, 231, 118, 66, 61, 134, 150)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__41_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__41_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(57, 190, 3, 113, 15, 121, 86, 21)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__41_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__40_value),LEAN_SCALAR_PTR_LITERAL(203, 67, 11, 240, 218, 30, 121, 196)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__41 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__41_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__42_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__42;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "eq_eq_false"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__43 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__43_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__44_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__44_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__44_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(80, 75, 231, 118, 66, 61, 134, 150)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__44_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__44_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(57, 190, 3, 113, 15, 121, 86, 21)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__44_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__43_value),LEAN_SCALAR_PTR_LITERAL(246, 204, 242, 159, 237, 232, 61, 227)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__44 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__44_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__45_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__45;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "norm_le_coeff"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(80, 75, 231, 118, 66, 61, 134, 150)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(57, 190, 3, 113, 15, 121, 86, 21)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(77, 37, 231, 141, 181, 61, 212, 111)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__2;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "norm_le_coeff_tight"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__3 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(80, 75, 231, 118, 66, 61, 134, 150)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(57, 190, 3, 113, 15, 121, 86, 21)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__4_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__3_value),LEAN_SCALAR_PTR_LITERAL(169, 84, 17, 148, 219, 118, 189, 43)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__4 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__5;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "norm_le"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__6 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__7_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(80, 75, 231, 118, 66, 61, 134, 150)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__7_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(57, 190, 3, 113, 15, 121, 86, 21)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__7_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__6_value),LEAN_SCALAR_PTR_LITERAL(93, 21, 225, 1, 193, 118, 239, 219)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__7 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__7_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__8;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "le_eq_true"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__9 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__9_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__10_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(80, 75, 231, 118, 66, 61, 134, 150)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__10_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(57, 190, 3, 113, 15, 121, 86, 21)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__10_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__9_value),LEAN_SCALAR_PTR_LITERAL(157, 27, 219, 76, 37, 196, 87, 77)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__10 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__10_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__11;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "le_eq_false"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__12 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__12_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__13_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(80, 75, 231, 118, 66, 61, 134, 150)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__13_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(57, 190, 3, 113, 15, 121, 86, 21)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__13_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__12_value),LEAN_SCALAR_PTR_LITERAL(65, 108, 55, 118, 18, 74, 38, 151)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__13 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__13_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__14;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LE"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__15 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__15_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "le"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__16 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__16_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__15_value),LEAN_SCALAR_PTR_LITERAL(216, 149, 183, 186, 191, 145, 216, 115)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__17_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__16_value),LEAN_SCALAR_PTR_LITERAL(109, 14, 90, 172, 72, 170, 136, 101)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__17 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__17_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__0_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trans"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(157, 40, 198, 234, 16, 168, 79, 243)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__2 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__3;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__4;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__5;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__6;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Not"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__7 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__7_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__7_value),LEAN_SCALAR_PTR_LITERAL(185, 11, 203, 55, 27, 192, 137, 230)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__8 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__8_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "GT"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__9 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__9_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "gt"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__10 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__10_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__9_value),LEAN_SCALAR_PTR_LITERAL(240, 16, 15, 58, 66, 186, 138, 31)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__11_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__10_value),LEAN_SCALAR_PTR_LITERAL(239, 75, 137, 103, 59, 22, 209, 130)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__11 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__11_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LT"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__12 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__12_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "lt"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__13 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__13_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__12_value),LEAN_SCALAR_PTR_LITERAL(71, 235, 154, 184, 62, 135, 30, 248)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__14_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__13_value),LEAN_SCALAR_PTR_LITERAL(54, 235, 251, 9, 4, 74, 57, 164)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__14 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__14_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "GE"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__15 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__15_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ge"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__16 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__16_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__15_value),LEAN_SCALAR_PTR_LITERAL(74, 169, 4, 72, 62, 21, 91, 24)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__17_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__16_value),LEAN_SCALAR_PTR_LITERAL(71, 88, 92, 156, 129, 215, 23, 77)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__17 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__17_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__18;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "not_le_eq"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__19 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__19_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__20_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__19_value),LEAN_SCALAR_PTR_LITERAL(77, 74, 162, 108, 148, 71, 165, 71)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__20 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__20_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__21;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "not_ge_eq"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__22 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__22_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__23_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__22_value),LEAN_SCALAR_PTR_LITERAL(87, 141, 152, 40, 61, 44, 151, 4)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__23 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__23_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__24;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "not_lt_eq"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__25 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__25_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__26_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__25_value),LEAN_SCALAR_PTR_LITERAL(214, 41, 233, 126, 147, 68, 29, 47)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__26 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__26_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__27;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "not_gt_eq"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__28 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__28_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__29_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__29_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__28_value),LEAN_SCALAR_PTR_LITERAL(250, 161, 48, 12, 204, 229, 102, 4)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__29 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__29_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__30;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lam__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "norm_dvd_gcd"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(80, 75, 231, 118, 66, 61, 134, 150)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(57, 190, 3, 113, 15, 121, 86, 21)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(28, 232, 181, 248, 19, 12, 233, 169)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__2;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "norm_dvd"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__3 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(80, 75, 231, 118, 66, 61, 134, 150)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(57, 190, 3, 113, 15, 121, 86, 21)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__4_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__3_value),LEAN_SCALAR_PTR_LITERAL(131, 13, 167, 71, 102, 170, 234, 147)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__4 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__5;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "dvd_eq_false"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__6 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__7_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(80, 75, 231, 118, 66, 61, 134, 150)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__7_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(57, 190, 3, 113, 15, 121, 86, 21)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__7_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__6_value),LEAN_SCALAR_PTR_LITERAL(65, 145, 10, 79, 196, 12, 17, 141)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__7 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__7_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__8;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Expr"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__0_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "eq_of_norm_eq"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(80, 75, 231, 118, 66, 61, 134, 150)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__2_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(57, 190, 3, 113, 15, 121, 86, 21)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__2_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(151, 251, 136, 155, 162, 62, 241, 107)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__2_value_aux_3),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(164, 40, 229, 149, 41, 35, 142, 101)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__2 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Simp_0__Int_Internal_Linear_Poly_gcdAll_go(lean_object* v_k_1_, lean_object* v_p_2_){
_start:
{
lean_object* v___x_3_; uint8_t v___x_4_; 
v___x_3_ = lean_unsigned_to_nat(1u);
v___x_4_ = lean_nat_dec_eq(v_k_1_, v___x_3_);
if (v___x_4_ == 0)
{
if (lean_obj_tag(v_p_2_) == 0)
{
lean_object* v_k_5_; lean_object* v___x_6_; lean_object* v___x_7_; 
v_k_5_ = lean_ctor_get(v_p_2_, 0);
v___x_6_ = lean_nat_abs(v_k_5_);
v___x_7_ = lean_nat_gcd(v_k_1_, v___x_6_);
lean_dec(v___x_6_);
lean_dec(v_k_1_);
return v___x_7_;
}
else
{
lean_object* v_k_8_; lean_object* v_p_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v_k_8_ = lean_ctor_get(v_p_2_, 0);
v_p_9_ = lean_ctor_get(v_p_2_, 2);
v___x_10_ = lean_nat_abs(v_k_8_);
v___x_11_ = lean_nat_gcd(v_k_1_, v___x_10_);
lean_dec(v___x_10_);
lean_dec(v_k_1_);
v_k_1_ = v___x_11_;
v_p_2_ = v_p_9_;
goto _start;
}
}
else
{
return v_k_1_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Simp_0__Int_Internal_Linear_Poly_gcdAll_go___boxed(lean_object* v_k_13_, lean_object* v_p_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Simp_0__Int_Internal_Linear_Poly_gcdAll_go(v_k_13_, v_p_14_);
lean_dec_ref(v_p_14_);
return v_res_15_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_gcdAll(lean_object* v_x_16_){
_start:
{
if (lean_obj_tag(v_x_16_) == 0)
{
lean_object* v_k_17_; lean_object* v___x_18_; 
v_k_17_ = lean_ctor_get(v_x_16_, 0);
v___x_18_ = lean_nat_abs(v_k_17_);
return v___x_18_;
}
else
{
lean_object* v_k_19_; lean_object* v_p_20_; lean_object* v___x_21_; lean_object* v___x_22_; 
v_k_19_ = lean_ctor_get(v_x_16_, 0);
v_p_20_ = lean_ctor_get(v_x_16_, 2);
v___x_21_ = lean_nat_abs(v_k_19_);
v___x_22_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Simp_0__Int_Internal_Linear_Poly_gcdAll_go(v___x_21_, v_p_20_);
return v___x_22_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_gcdAll___boxed(lean_object* v_x_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Int_Internal_Linear_Poly_gcdAll(v_x_23_);
lean_dec_ref(v_x_23_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Simp_0__Int_Internal_Linear_Poly_gcdCoeffs_x27_go(lean_object* v_k_25_, lean_object* v_p_26_){
_start:
{
lean_object* v___x_27_; uint8_t v___x_28_; 
v___x_27_ = lean_unsigned_to_nat(1u);
v___x_28_ = lean_nat_dec_eq(v_k_25_, v___x_27_);
if (v___x_28_ == 0)
{
if (lean_obj_tag(v_p_26_) == 0)
{
return v_k_25_;
}
else
{
lean_object* v_k_29_; lean_object* v_p_30_; lean_object* v___x_31_; lean_object* v___x_32_; 
v_k_29_ = lean_ctor_get(v_p_26_, 0);
v_p_30_ = lean_ctor_get(v_p_26_, 2);
v___x_31_ = lean_nat_abs(v_k_29_);
v___x_32_ = lean_nat_gcd(v_k_25_, v___x_31_);
lean_dec(v___x_31_);
lean_dec(v_k_25_);
v_k_25_ = v___x_32_;
v_p_26_ = v_p_30_;
goto _start;
}
}
else
{
return v_k_25_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Simp_0__Int_Internal_Linear_Poly_gcdCoeffs_x27_go___boxed(lean_object* v_k_34_, lean_object* v_p_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Simp_0__Int_Internal_Linear_Poly_gcdCoeffs_x27_go(v_k_34_, v_p_35_);
lean_dec_ref(v_p_35_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_gcdCoeffs_x27(lean_object* v_x_37_){
_start:
{
if (lean_obj_tag(v_x_37_) == 0)
{
lean_object* v___x_38_; 
v___x_38_ = lean_unsigned_to_nat(1u);
return v___x_38_;
}
else
{
lean_object* v_k_39_; lean_object* v_p_40_; lean_object* v___x_41_; lean_object* v___x_42_; 
v_k_39_ = lean_ctor_get(v_x_37_, 0);
v_p_40_ = lean_ctor_get(v_x_37_, 2);
v___x_41_ = lean_nat_abs(v_k_39_);
v___x_42_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Simp_0__Int_Internal_Linear_Poly_gcdCoeffs_x27_go(v___x_41_, v_p_40_);
return v___x_42_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_gcdCoeffs_x27___boxed(lean_object* v_x_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l_Int_Internal_Linear_Poly_gcdCoeffs_x27(v_x_43_);
lean_dec_ref(v_x_43_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_Simp_Arith_Int_simpEq_x3f_spec__0(lean_object* v_a_45_){
_start:
{
lean_object* v___x_46_; 
v___x_46_ = lean_nat_to_int(v_a_45_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__0(lean_object* v___x_47_, lean_object* v_snd_48_, lean_object* v_x_49_){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = lean_array_get_borrowed(v___x_47_, v_snd_48_, v_x_49_);
lean_inc(v___x_50_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__0___boxed(lean_object* v___x_51_, lean_object* v_snd_52_, lean_object* v_x_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__0(v___x_51_, v_snd_52_, v_x_53_);
lean_dec(v_x_53_);
lean_dec_ref(v_snd_52_);
lean_dec_ref(v___x_51_);
return v_res_54_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5(void){
_start:
{
lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_64_ = lean_box(0);
v___x_65_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__4));
v___x_66_ = l_Lean_mkConst(v___x_65_, v___x_64_);
return v___x_66_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6(void){
_start:
{
lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_67_ = lean_unsigned_to_nat(0u);
v___x_68_ = lean_nat_to_int(v___x_67_);
return v___x_68_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__9(void){
_start:
{
lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_72_ = lean_box(0);
v___x_73_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8));
v___x_74_ = l_Lean_mkConst(v___x_73_, v___x_72_);
return v___x_74_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__12(void){
_start:
{
lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; 
v___x_81_ = lean_box(0);
v___x_82_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__11));
v___x_83_ = l_Lean_mkConst(v___x_82_, v___x_81_);
return v___x_83_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__16(void){
_start:
{
lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_89_ = lean_unsigned_to_nat(0u);
v___x_90_ = l_Lean_Level_ofNat(v___x_89_);
return v___x_90_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17(void){
_start:
{
lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_91_ = lean_box(0);
v___x_92_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__16, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__16_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__16);
v___x_93_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_93_, 0, v___x_92_);
lean_ctor_set(v___x_93_, 1, v___x_91_);
return v___x_93_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18(void){
_start:
{
lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_94_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17);
v___x_95_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__15));
v___x_96_ = l_Lean_Expr_const___override(v___x_95_, v___x_94_);
return v___x_96_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20(void){
_start:
{
lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_99_ = lean_box(0);
v___x_100_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19));
v___x_101_ = l_Lean_Expr_const___override(v___x_100_, v___x_99_);
return v___x_101_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23(void){
_start:
{
lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_106_ = lean_box(0);
v___x_107_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22));
v___x_108_ = l_Lean_Expr_const___override(v___x_107_, v___x_106_);
return v___x_108_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__24(void){
_start:
{
lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_109_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6);
v___x_110_ = l_Lean_mkIntLit(v___x_109_);
return v___x_110_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__27(void){
_start:
{
lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_117_ = lean_box(0);
v___x_118_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__26));
v___x_119_ = l_Lean_mkConst(v___x_118_, v___x_117_);
return v___x_119_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30(void){
_start:
{
lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_126_ = lean_box(0);
v___x_127_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__29));
v___x_128_ = l_Lean_mkConst(v___x_127_, v___x_126_);
return v___x_128_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__31(void){
_start:
{
lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_129_ = lean_unsigned_to_nat(1u);
v___x_130_ = lean_nat_to_int(v___x_129_);
return v___x_130_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__32(void){
_start:
{
lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_131_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__31, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__31_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__31);
v___x_132_ = lean_int_neg(v___x_131_);
return v___x_132_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__35(void){
_start:
{
lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_139_ = lean_box(0);
v___x_140_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__34));
v___x_141_ = l_Lean_mkConst(v___x_140_, v___x_139_);
return v___x_141_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__36(void){
_start:
{
lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_142_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6);
v___x_143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_143_, 0, v___x_142_);
return v___x_143_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__39(void){
_start:
{
lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_147_ = lean_box(0);
v___x_148_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__38));
v___x_149_ = l_Lean_mkConst(v___x_148_, v___x_147_);
return v___x_149_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__42(void){
_start:
{
lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_156_ = lean_box(0);
v___x_157_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__41));
v___x_158_ = l_Lean_mkConst(v___x_157_, v___x_156_);
return v___x_158_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__45(void){
_start:
{
lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_165_ = lean_box(0);
v___x_166_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__44));
v___x_167_ = l_Lean_mkConst(v___x_166_, v___x_165_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f(lean_object* v_e_168_, lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_){
_start:
{
lean_object* v___x_174_; 
v___x_174_ = l_Lean_Meta_Simp_Arith_Int_eqCnstr_x3f(v_e_168_, v_a_169_, v_a_170_, v_a_171_, v_a_172_);
if (lean_obj_tag(v___x_174_) == 0)
{
lean_object* v_a_175_; lean_object* v___x_177_; uint8_t v_isShared_178_; uint8_t v_isSharedCheck_555_; 
v_a_175_ = lean_ctor_get(v___x_174_, 0);
v_isSharedCheck_555_ = !lean_is_exclusive(v___x_174_);
if (v_isSharedCheck_555_ == 0)
{
v___x_177_ = v___x_174_;
v_isShared_178_ = v_isSharedCheck_555_;
goto v_resetjp_176_;
}
else
{
lean_inc(v_a_175_);
lean_dec(v___x_174_);
v___x_177_ = lean_box(0);
v_isShared_178_ = v_isSharedCheck_555_;
goto v_resetjp_176_;
}
v_resetjp_176_:
{
if (lean_obj_tag(v_a_175_) == 1)
{
lean_object* v_val_179_; lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_550_; 
v_val_179_ = lean_ctor_get(v_a_175_, 0);
v_isSharedCheck_550_ = !lean_is_exclusive(v_a_175_);
if (v_isSharedCheck_550_ == 0)
{
v___x_181_ = v_a_175_;
v_isShared_182_ = v_isSharedCheck_550_;
goto v_resetjp_180_;
}
else
{
lean_inc(v_val_179_);
lean_dec(v_a_175_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_550_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
lean_object* v_snd_183_; lean_object* v_fst_184_; lean_object* v___x_186_; uint8_t v_isShared_187_; uint8_t v_isSharedCheck_549_; 
v_snd_183_ = lean_ctor_get(v_val_179_, 1);
v_fst_184_ = lean_ctor_get(v_val_179_, 0);
v_isSharedCheck_549_ = !lean_is_exclusive(v_val_179_);
if (v_isSharedCheck_549_ == 0)
{
v___x_186_ = v_val_179_;
v_isShared_187_ = v_isSharedCheck_549_;
goto v_resetjp_185_;
}
else
{
lean_inc(v_snd_183_);
lean_inc(v_fst_184_);
lean_dec(v_val_179_);
v___x_186_ = lean_box(0);
v_isShared_187_ = v_isSharedCheck_549_;
goto v_resetjp_185_;
}
v_resetjp_185_:
{
lean_object* v_fst_188_; lean_object* v_snd_189_; lean_object* v___x_191_; uint8_t v_isShared_192_; uint8_t v_isSharedCheck_548_; 
v_fst_188_ = lean_ctor_get(v_snd_183_, 0);
v_snd_189_ = lean_ctor_get(v_snd_183_, 1);
v_isSharedCheck_548_ = !lean_is_exclusive(v_snd_183_);
if (v_isSharedCheck_548_ == 0)
{
v___x_191_ = v_snd_183_;
v_isShared_192_ = v_isSharedCheck_548_;
goto v_resetjp_190_;
}
else
{
lean_inc(v_snd_189_);
lean_inc(v_fst_188_);
lean_dec(v_snd_183_);
v___x_191_ = lean_box(0);
v_isShared_192_ = v_isSharedCheck_548_;
goto v_resetjp_190_;
}
v_resetjp_190_:
{
lean_object* v___x_193_; lean_object* v___f_194_; lean_object* v___x_195_; 
v___x_193_ = l_Lean_instInhabitedExpr;
lean_inc(v_snd_189_);
v___f_194_ = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__0___boxed), 3, 2);
lean_closure_set(v___f_194_, 0, v___x_193_);
lean_closure_set(v___f_194_, 1, v_snd_189_);
lean_inc(v_fst_184_);
lean_inc_ref(v___f_194_);
v___x_195_ = l_Int_Internal_Linear_Expr_denoteExpr___redArg(v___f_194_, v_fst_184_);
if (lean_obj_tag(v___x_195_) == 0)
{
lean_object* v_a_196_; lean_object* v___x_198_; uint8_t v_isShared_199_; uint8_t v_isSharedCheck_539_; 
v_a_196_ = lean_ctor_get(v___x_195_, 0);
v_isSharedCheck_539_ = !lean_is_exclusive(v___x_195_);
if (v_isSharedCheck_539_ == 0)
{
v___x_198_ = v___x_195_;
v_isShared_199_ = v_isSharedCheck_539_;
goto v_resetjp_197_;
}
else
{
lean_inc(v_a_196_);
lean_dec(v___x_195_);
v___x_198_ = lean_box(0);
v_isShared_199_ = v_isSharedCheck_539_;
goto v_resetjp_197_;
}
v_resetjp_197_:
{
lean_object* v___x_200_; 
lean_inc(v_fst_188_);
lean_inc_ref(v___f_194_);
v___x_200_ = l_Int_Internal_Linear_Expr_denoteExpr___redArg(v___f_194_, v_fst_188_);
if (lean_obj_tag(v___x_200_) == 0)
{
lean_object* v_a_201_; lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_530_; 
v_a_201_ = lean_ctor_get(v___x_200_, 0);
v_isSharedCheck_530_ = !lean_is_exclusive(v___x_200_);
if (v_isSharedCheck_530_ == 0)
{
v___x_203_ = v___x_200_;
v_isShared_204_ = v_isSharedCheck_530_;
goto v_resetjp_202_;
}
else
{
lean_inc(v_a_201_);
lean_dec(v___x_200_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_530_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
lean_object* v___x_205_; lean_object* v___y_207_; lean_object* v___y_208_; lean_object* v___y_209_; lean_object* v___y_210_; lean_object* v___y_211_; lean_object* v___y_212_; lean_object* v___y_227_; lean_object* v___y_228_; lean_object* v___y_229_; lean_object* v___y_230_; lean_object* v___y_231_; lean_object* v___y_232_; lean_object* v___y_233_; lean_object* v___y_246_; lean_object* v___y_247_; lean_object* v___y_248_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___y_285_; lean_object* v___y_286_; lean_object* v___y_287_; lean_object* v___y_288_; uint8_t v___y_398_; uint8_t v___x_470_; 
v___x_205_ = l_Lean_mkIntEq(v_a_196_, v_a_201_);
lean_inc(v_fst_188_);
lean_inc(v_fst_184_);
v___x_282_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_282_, 0, v_fst_184_);
lean_ctor_set(v___x_282_, 1, v_fst_188_);
v___x_283_ = l_Int_Internal_Linear_Expr_norm(v___x_282_);
lean_dec_ref_known(v___x_282_, 2);
v___x_470_ = l_Int_Internal_Linear_Poly_isUnsatEq(v___x_283_);
if (v___x_470_ == 0)
{
uint8_t v___x_471_; 
v___x_471_ = l_Int_Internal_Linear_Poly_isValidEq(v___x_283_);
if (v___x_471_ == 0)
{
lean_object* v___x_472_; uint8_t v___x_473_; 
lean_inc_ref(v___x_283_);
v___x_472_ = l_Int_Internal_Linear_Poly_toExpr(v___x_283_);
v___x_473_ = l_Int_Internal_Linear_instBEqExpr_beq(v___x_472_, v_fst_184_);
lean_dec_ref(v___x_472_);
if (v___x_473_ == 0)
{
v___y_398_ = v___x_473_;
goto v___jp_397_;
}
else
{
lean_object* v___x_474_; uint8_t v___x_475_; 
v___x_474_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__36, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__36_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__36);
v___x_475_ = l_Int_Internal_Linear_instBEqExpr_beq(v_fst_188_, v___x_474_);
v___y_398_ = v___x_475_;
goto v___jp_397_;
}
}
else
{
lean_object* v___x_476_; 
lean_dec_ref(v___x_283_);
lean_del_object(v___x_203_);
lean_del_object(v___x_198_);
lean_dec_ref(v___f_194_);
lean_del_object(v___x_191_);
lean_del_object(v___x_186_);
lean_del_object(v___x_181_);
lean_del_object(v___x_177_);
v___x_476_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(v_snd_189_, v_a_169_, v_a_170_, v_a_171_, v_a_172_);
if (lean_obj_tag(v___x_476_) == 0)
{
lean_object* v_a_477_; lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_494_; 
v_a_477_ = lean_ctor_get(v___x_476_, 0);
v_isSharedCheck_494_ = !lean_is_exclusive(v___x_476_);
if (v_isSharedCheck_494_ == 0)
{
v___x_479_ = v___x_476_;
v_isShared_480_ = v_isSharedCheck_494_;
goto v_resetjp_478_;
}
else
{
lean_inc(v_a_477_);
lean_dec(v___x_476_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_494_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_492_; 
v___x_481_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__39, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__39_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__39);
v___x_482_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__42, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__42_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__42);
v___x_483_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_184_);
v___x_484_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_188_);
v___x_485_ = l_Lean_eagerReflBoolTrue;
v___x_486_ = l_Lean_mkApp4(v___x_482_, v_a_477_, v___x_483_, v___x_484_, v___x_485_);
v___x_487_ = l_Lean_mkPropEq(v___x_205_, v___x_481_);
v___x_488_ = l_Lean_Meta_mkExpectedPropHint(v___x_486_, v___x_487_);
v___x_489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_489_, 0, v___x_481_);
lean_ctor_set(v___x_489_, 1, v___x_488_);
v___x_490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_490_, 0, v___x_489_);
if (v_isShared_480_ == 0)
{
lean_ctor_set(v___x_479_, 0, v___x_490_);
v___x_492_ = v___x_479_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v___x_490_);
v___x_492_ = v_reuseFailAlloc_493_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
return v___x_492_;
}
}
}
else
{
lean_object* v_a_495_; lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_502_; 
lean_dec_ref(v___x_205_);
lean_dec(v_fst_188_);
lean_dec(v_fst_184_);
v_a_495_ = lean_ctor_get(v___x_476_, 0);
v_isSharedCheck_502_ = !lean_is_exclusive(v___x_476_);
if (v_isSharedCheck_502_ == 0)
{
v___x_497_ = v___x_476_;
v_isShared_498_ = v_isSharedCheck_502_;
goto v_resetjp_496_;
}
else
{
lean_inc(v_a_495_);
lean_dec(v___x_476_);
v___x_497_ = lean_box(0);
v_isShared_498_ = v_isSharedCheck_502_;
goto v_resetjp_496_;
}
v_resetjp_496_:
{
lean_object* v___x_500_; 
if (v_isShared_498_ == 0)
{
v___x_500_ = v___x_497_;
goto v_reusejp_499_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v_a_495_);
v___x_500_ = v_reuseFailAlloc_501_;
goto v_reusejp_499_;
}
v_reusejp_499_:
{
return v___x_500_;
}
}
}
}
}
else
{
lean_object* v___x_503_; 
lean_dec_ref(v___x_283_);
lean_del_object(v___x_203_);
lean_del_object(v___x_198_);
lean_dec_ref(v___f_194_);
lean_del_object(v___x_191_);
lean_del_object(v___x_186_);
lean_del_object(v___x_181_);
lean_del_object(v___x_177_);
v___x_503_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(v_snd_189_, v_a_169_, v_a_170_, v_a_171_, v_a_172_);
if (lean_obj_tag(v___x_503_) == 0)
{
lean_object* v_a_504_; lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_521_; 
v_a_504_ = lean_ctor_get(v___x_503_, 0);
v_isSharedCheck_521_ = !lean_is_exclusive(v___x_503_);
if (v_isSharedCheck_521_ == 0)
{
v___x_506_ = v___x_503_;
v_isShared_507_ = v_isSharedCheck_521_;
goto v_resetjp_505_;
}
else
{
lean_inc(v_a_504_);
lean_dec(v___x_503_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_521_;
goto v_resetjp_505_;
}
v_resetjp_505_:
{
lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_519_; 
v___x_508_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__9, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__9_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__9);
v___x_509_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__45, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__45_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__45);
v___x_510_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_184_);
v___x_511_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_188_);
v___x_512_ = l_Lean_eagerReflBoolTrue;
v___x_513_ = l_Lean_mkApp4(v___x_509_, v_a_504_, v___x_510_, v___x_511_, v___x_512_);
v___x_514_ = l_Lean_mkPropEq(v___x_205_, v___x_508_);
v___x_515_ = l_Lean_Meta_mkExpectedPropHint(v___x_513_, v___x_514_);
v___x_516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_516_, 0, v___x_508_);
lean_ctor_set(v___x_516_, 1, v___x_515_);
v___x_517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_517_, 0, v___x_516_);
if (v_isShared_507_ == 0)
{
lean_ctor_set(v___x_506_, 0, v___x_517_);
v___x_519_ = v___x_506_;
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
else
{
lean_object* v_a_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_529_; 
lean_dec_ref(v___x_205_);
lean_dec(v_fst_188_);
lean_dec(v_fst_184_);
v_a_522_ = lean_ctor_get(v___x_503_, 0);
v_isSharedCheck_529_ = !lean_is_exclusive(v___x_503_);
if (v_isSharedCheck_529_ == 0)
{
v___x_524_ = v___x_503_;
v_isShared_525_ = v_isSharedCheck_529_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_a_522_);
lean_dec(v___x_503_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_529_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
lean_object* v___x_527_; 
if (v_isShared_525_ == 0)
{
v___x_527_ = v___x_524_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v_a_522_);
v___x_527_ = v_reuseFailAlloc_528_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
return v___x_527_;
}
}
}
}
v___jp_206_:
{
lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_218_; 
v___x_213_ = l_Lean_eagerReflBoolTrue;
lean_inc_ref(v___y_210_);
v___x_214_ = l_Lean_mkApp5(v___y_210_, v___y_211_, v___y_208_, v___y_209_, v___y_212_, v___x_213_);
lean_inc_ref_n(v___y_207_, 2);
v___x_215_ = l_Lean_mkPropEq(v___x_205_, v___y_207_);
v___x_216_ = l_Lean_Meta_mkExpectedPropHint(v___x_214_, v___x_215_);
if (v_isShared_192_ == 0)
{
lean_ctor_set(v___x_191_, 1, v___x_216_);
lean_ctor_set(v___x_191_, 0, v___y_207_);
v___x_218_ = v___x_191_;
goto v_reusejp_217_;
}
else
{
lean_object* v_reuseFailAlloc_225_; 
v_reuseFailAlloc_225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_225_, 0, v___y_207_);
lean_ctor_set(v_reuseFailAlloc_225_, 1, v___x_216_);
v___x_218_ = v_reuseFailAlloc_225_;
goto v_reusejp_217_;
}
v_reusejp_217_:
{
lean_object* v___x_220_; 
if (v_isShared_182_ == 0)
{
lean_ctor_set(v___x_181_, 0, v___x_218_);
v___x_220_ = v___x_181_;
goto v_reusejp_219_;
}
else
{
lean_object* v_reuseFailAlloc_224_; 
v_reuseFailAlloc_224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_224_, 0, v___x_218_);
v___x_220_ = v_reuseFailAlloc_224_;
goto v_reusejp_219_;
}
v_reusejp_219_:
{
lean_object* v___x_222_; 
if (v_isShared_204_ == 0)
{
lean_ctor_set(v___x_203_, 0, v___x_220_);
v___x_222_ = v___x_203_;
goto v_reusejp_221_;
}
else
{
lean_object* v_reuseFailAlloc_223_; 
v_reuseFailAlloc_223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_223_, 0, v___x_220_);
v___x_222_ = v_reuseFailAlloc_223_;
goto v_reusejp_221_;
}
v_reusejp_221_:
{
return v___x_222_;
}
}
}
}
v___jp_226_:
{
lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_239_; 
v___x_234_ = l_Lean_eagerReflBoolTrue;
lean_inc_ref(v___y_229_);
v___x_235_ = l_Lean_mkApp6(v___y_229_, v___y_231_, v___y_227_, v___y_230_, v___y_232_, v___y_233_, v___x_234_);
lean_inc_ref(v___y_228_);
v___x_236_ = l_Lean_mkPropEq(v___x_205_, v___y_228_);
v___x_237_ = l_Lean_Meta_mkExpectedPropHint(v___x_235_, v___x_236_);
if (v_isShared_187_ == 0)
{
lean_ctor_set(v___x_186_, 1, v___x_237_);
lean_ctor_set(v___x_186_, 0, v___y_228_);
v___x_239_ = v___x_186_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v___y_228_);
lean_ctor_set(v_reuseFailAlloc_244_, 1, v___x_237_);
v___x_239_ = v_reuseFailAlloc_244_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
lean_object* v___x_240_; lean_object* v___x_242_; 
v___x_240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_240_, 0, v___x_239_);
if (v_isShared_199_ == 0)
{
lean_ctor_set(v___x_198_, 0, v___x_240_);
v___x_242_ = v___x_198_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v___x_240_);
v___x_242_ = v_reuseFailAlloc_243_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
return v___x_242_;
}
}
}
v___jp_245_:
{
lean_object* v___x_249_; uint8_t v___x_250_; 
lean_inc_ref(v___y_248_);
v___x_249_ = l_Lean_mkIntEq(v___y_246_, v___y_248_);
v___x_250_ = lean_expr_eqv(v___x_249_, v___x_205_);
if (v___x_250_ == 0)
{
lean_object* v___x_251_; 
lean_del_object(v___x_177_);
v___x_251_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(v_snd_189_, v_a_169_, v_a_170_, v_a_171_, v_a_172_);
if (lean_obj_tag(v___x_251_) == 0)
{
lean_object* v_a_252_; lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_269_; 
v_a_252_ = lean_ctor_get(v___x_251_, 0);
v_isSharedCheck_269_ = !lean_is_exclusive(v___x_251_);
if (v_isSharedCheck_269_ == 0)
{
v___x_254_ = v___x_251_;
v_isShared_255_ = v_isSharedCheck_269_;
goto v_resetjp_253_;
}
else
{
lean_inc(v_a_252_);
lean_dec(v___x_251_);
v___x_254_ = lean_box(0);
v_isShared_255_ = v_isSharedCheck_269_;
goto v_resetjp_253_;
}
v_resetjp_253_:
{
lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_267_; 
v___x_256_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5);
v___x_257_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_184_);
v___x_258_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_188_);
v___x_259_ = l_Lean_mkNatLit(v___y_247_);
v___x_260_ = l_Lean_eagerReflBoolTrue;
v___x_261_ = l_Lean_mkApp6(v___x_256_, v_a_252_, v___x_257_, v___x_258_, v___x_259_, v___y_248_, v___x_260_);
lean_inc_ref(v___x_249_);
v___x_262_ = l_Lean_mkPropEq(v___x_205_, v___x_249_);
v___x_263_ = l_Lean_Meta_mkExpectedPropHint(v___x_261_, v___x_262_);
v___x_264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_264_, 0, v___x_249_);
lean_ctor_set(v___x_264_, 1, v___x_263_);
v___x_265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_265_, 0, v___x_264_);
if (v_isShared_255_ == 0)
{
lean_ctor_set(v___x_254_, 0, v___x_265_);
v___x_267_ = v___x_254_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v___x_265_);
v___x_267_ = v_reuseFailAlloc_268_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
return v___x_267_;
}
}
}
else
{
lean_object* v_a_270_; lean_object* v___x_272_; uint8_t v_isShared_273_; uint8_t v_isSharedCheck_277_; 
lean_dec_ref(v___x_249_);
lean_dec_ref(v___y_248_);
lean_dec(v___y_247_);
lean_dec_ref(v___x_205_);
lean_dec(v_fst_188_);
lean_dec(v_fst_184_);
v_a_270_ = lean_ctor_get(v___x_251_, 0);
v_isSharedCheck_277_ = !lean_is_exclusive(v___x_251_);
if (v_isSharedCheck_277_ == 0)
{
v___x_272_ = v___x_251_;
v_isShared_273_ = v_isSharedCheck_277_;
goto v_resetjp_271_;
}
else
{
lean_inc(v_a_270_);
lean_dec(v___x_251_);
v___x_272_ = lean_box(0);
v_isShared_273_ = v_isSharedCheck_277_;
goto v_resetjp_271_;
}
v_resetjp_271_:
{
lean_object* v___x_275_; 
if (v_isShared_273_ == 0)
{
v___x_275_ = v___x_272_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v_a_270_);
v___x_275_ = v_reuseFailAlloc_276_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
return v___x_275_;
}
}
}
}
else
{
lean_object* v___x_278_; lean_object* v___x_280_; 
lean_dec_ref(v___x_249_);
lean_dec_ref(v___y_248_);
lean_dec(v___y_247_);
lean_dec_ref(v___x_205_);
lean_dec(v_snd_189_);
lean_dec(v_fst_188_);
lean_dec(v_fst_184_);
v___x_278_ = lean_box(0);
if (v_isShared_178_ == 0)
{
lean_ctor_set(v___x_177_, 0, v___x_278_);
v___x_280_ = v___x_177_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v___x_278_);
v___x_280_ = v_reuseFailAlloc_281_;
goto v_reusejp_279_;
}
v_reusejp_279_:
{
return v___x_280_;
}
}
}
v___jp_284_:
{
lean_object* v___x_289_; lean_object* v___x_290_; uint8_t v___x_291_; 
v___x_289_ = l_Int_Internal_Linear_Poly_gcdCoeffs_x27(v___x_283_);
v___x_290_ = lean_unsigned_to_nat(1u);
v___x_291_ = lean_nat_dec_eq(v___x_289_, v___x_290_);
if (v___x_291_ == 0)
{
lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; uint8_t v___x_296_; 
v___x_292_ = l_Int_Internal_Linear_Poly_getConst(v___x_283_);
v___x_293_ = lean_nat_to_int(v___x_289_);
v___x_294_ = lean_int_emod(v___x_292_, v___x_293_);
lean_dec(v___x_292_);
v___x_295_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6);
v___x_296_ = lean_int_dec_eq(v___x_294_, v___x_295_);
lean_dec(v___x_294_);
if (v___x_296_ == 0)
{
lean_object* v___x_297_; 
lean_dec_ref(v___x_283_);
lean_del_object(v___x_198_);
lean_dec_ref(v___f_194_);
lean_del_object(v___x_186_);
v___x_297_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(v_snd_189_, v___y_285_, v___y_286_, v___y_287_, v___y_288_);
if (lean_obj_tag(v___x_297_) == 0)
{
lean_object* v_a_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; uint8_t v___x_303_; 
v_a_298_ = lean_ctor_get(v___x_297_, 0);
lean_inc(v_a_298_);
lean_dec_ref_known(v___x_297_, 1);
v___x_299_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__9, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__9_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__9);
v___x_300_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__12, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__12_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__12);
v___x_301_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_184_);
v___x_302_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_188_);
v___x_303_ = lean_int_dec_le(v___x_295_, v___x_293_);
if (v___x_303_ == 0)
{
lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_304_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18);
v___x_305_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20);
v___x_306_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23);
v___x_307_ = lean_int_neg(v___x_293_);
lean_dec(v___x_293_);
v___x_308_ = l_Int_toNat(v___x_307_);
lean_dec(v___x_307_);
v___x_309_ = l_Lean_instToExprInt_mkNat(v___x_308_);
v___x_310_ = l_Lean_mkApp3(v___x_304_, v___x_305_, v___x_306_, v___x_309_);
v___y_207_ = v___x_299_;
v___y_208_ = v___x_301_;
v___y_209_ = v___x_302_;
v___y_210_ = v___x_300_;
v___y_211_ = v_a_298_;
v___y_212_ = v___x_310_;
goto v___jp_206_;
}
else
{
lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_311_ = l_Int_toNat(v___x_293_);
lean_dec(v___x_293_);
v___x_312_ = l_Lean_instToExprInt_mkNat(v___x_311_);
v___y_207_ = v___x_299_;
v___y_208_ = v___x_301_;
v___y_209_ = v___x_302_;
v___y_210_ = v___x_300_;
v___y_211_ = v_a_298_;
v___y_212_ = v___x_312_;
goto v___jp_206_;
}
}
else
{
lean_object* v_a_313_; lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_320_; 
lean_dec(v___x_293_);
lean_dec_ref(v___x_205_);
lean_del_object(v___x_203_);
lean_del_object(v___x_191_);
lean_dec(v_fst_188_);
lean_dec(v_fst_184_);
lean_del_object(v___x_181_);
v_a_313_ = lean_ctor_get(v___x_297_, 0);
v_isSharedCheck_320_ = !lean_is_exclusive(v___x_297_);
if (v_isSharedCheck_320_ == 0)
{
v___x_315_ = v___x_297_;
v_isShared_316_ = v_isSharedCheck_320_;
goto v_resetjp_314_;
}
else
{
lean_inc(v_a_313_);
lean_dec(v___x_297_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_320_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
lean_object* v___x_318_; 
if (v_isShared_316_ == 0)
{
v___x_318_ = v___x_315_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v_a_313_);
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
else
{
lean_object* v___x_321_; lean_object* v___x_322_; 
lean_del_object(v___x_203_);
lean_del_object(v___x_191_);
lean_del_object(v___x_181_);
v___x_321_ = l_Int_Internal_Linear_Poly_div(v___x_293_, v___x_283_);
lean_inc_ref(v___x_321_);
v___x_322_ = l_Int_Internal_Linear_Poly_denoteExpr___redArg(v___f_194_, v___x_321_);
if (lean_obj_tag(v___x_322_) == 0)
{
lean_object* v_a_323_; lean_object* v___x_324_; 
v_a_323_ = lean_ctor_get(v___x_322_, 0);
lean_inc(v_a_323_);
lean_dec_ref_known(v___x_322_, 1);
v___x_324_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(v_snd_189_, v___y_285_, v___y_286_, v___y_287_, v___y_288_);
if (lean_obj_tag(v___x_324_) == 0)
{
lean_object* v_a_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; uint8_t v___x_332_; 
v_a_325_ = lean_ctor_get(v___x_324_, 0);
lean_inc(v_a_325_);
lean_dec_ref_known(v___x_324_, 1);
v___x_326_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__24, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__24_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__24);
v___x_327_ = l_Lean_mkIntEq(v_a_323_, v___x_326_);
v___x_328_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__27, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__27_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__27);
v___x_329_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_184_);
v___x_330_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_188_);
v___x_331_ = l_Lean_Meta_Simp_Arith_Int_ofPoly(v___x_321_);
v___x_332_ = lean_int_dec_le(v___x_295_, v___x_293_);
if (v___x_332_ == 0)
{
lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_333_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18);
v___x_334_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20);
v___x_335_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23);
v___x_336_ = lean_int_neg(v___x_293_);
lean_dec(v___x_293_);
v___x_337_ = l_Int_toNat(v___x_336_);
lean_dec(v___x_336_);
v___x_338_ = l_Lean_instToExprInt_mkNat(v___x_337_);
v___x_339_ = l_Lean_mkApp3(v___x_333_, v___x_334_, v___x_335_, v___x_338_);
v___y_227_ = v___x_329_;
v___y_228_ = v___x_327_;
v___y_229_ = v___x_328_;
v___y_230_ = v___x_330_;
v___y_231_ = v_a_325_;
v___y_232_ = v___x_331_;
v___y_233_ = v___x_339_;
goto v___jp_226_;
}
else
{
lean_object* v___x_340_; lean_object* v___x_341_; 
v___x_340_ = l_Int_toNat(v___x_293_);
lean_dec(v___x_293_);
v___x_341_ = l_Lean_instToExprInt_mkNat(v___x_340_);
v___y_227_ = v___x_329_;
v___y_228_ = v___x_327_;
v___y_229_ = v___x_328_;
v___y_230_ = v___x_330_;
v___y_231_ = v_a_325_;
v___y_232_ = v___x_331_;
v___y_233_ = v___x_341_;
goto v___jp_226_;
}
}
else
{
lean_object* v_a_342_; lean_object* v___x_344_; uint8_t v_isShared_345_; uint8_t v_isSharedCheck_349_; 
lean_dec(v_a_323_);
lean_dec_ref(v___x_321_);
lean_dec(v___x_293_);
lean_dec_ref(v___x_205_);
lean_del_object(v___x_198_);
lean_dec(v_fst_188_);
lean_del_object(v___x_186_);
lean_dec(v_fst_184_);
v_a_342_ = lean_ctor_get(v___x_324_, 0);
v_isSharedCheck_349_ = !lean_is_exclusive(v___x_324_);
if (v_isSharedCheck_349_ == 0)
{
v___x_344_ = v___x_324_;
v_isShared_345_ = v_isSharedCheck_349_;
goto v_resetjp_343_;
}
else
{
lean_inc(v_a_342_);
lean_dec(v___x_324_);
v___x_344_ = lean_box(0);
v_isShared_345_ = v_isSharedCheck_349_;
goto v_resetjp_343_;
}
v_resetjp_343_:
{
lean_object* v___x_347_; 
if (v_isShared_345_ == 0)
{
v___x_347_ = v___x_344_;
goto v_reusejp_346_;
}
else
{
lean_object* v_reuseFailAlloc_348_; 
v_reuseFailAlloc_348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_348_, 0, v_a_342_);
v___x_347_ = v_reuseFailAlloc_348_;
goto v_reusejp_346_;
}
v_reusejp_346_:
{
return v___x_347_;
}
}
}
}
else
{
lean_object* v_a_350_; lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_357_; 
lean_dec_ref(v___x_321_);
lean_dec(v___x_293_);
lean_dec_ref(v___x_205_);
lean_del_object(v___x_198_);
lean_dec(v_snd_189_);
lean_dec(v_fst_188_);
lean_del_object(v___x_186_);
lean_dec(v_fst_184_);
v_a_350_ = lean_ctor_get(v___x_322_, 0);
v_isSharedCheck_357_ = !lean_is_exclusive(v___x_322_);
if (v_isSharedCheck_357_ == 0)
{
v___x_352_ = v___x_322_;
v_isShared_353_ = v_isSharedCheck_357_;
goto v_resetjp_351_;
}
else
{
lean_inc(v_a_350_);
lean_dec(v___x_322_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_357_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
lean_object* v___x_355_; 
if (v_isShared_353_ == 0)
{
v___x_355_ = v___x_352_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v_a_350_);
v___x_355_ = v_reuseFailAlloc_356_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
return v___x_355_;
}
}
}
}
}
else
{
lean_object* v___x_358_; 
lean_dec(v___x_289_);
lean_del_object(v___x_203_);
lean_del_object(v___x_198_);
lean_del_object(v___x_191_);
lean_del_object(v___x_186_);
lean_del_object(v___x_181_);
lean_inc_ref(v___x_283_);
v___x_358_ = l_Int_Internal_Linear_Poly_denoteExpr___redArg(v___f_194_, v___x_283_);
if (lean_obj_tag(v___x_358_) == 0)
{
lean_object* v_a_359_; lean_object* v___x_360_; 
v_a_359_ = lean_ctor_get(v___x_358_, 0);
lean_inc(v_a_359_);
lean_dec_ref_known(v___x_358_, 1);
v___x_360_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(v_snd_189_, v___y_285_, v___y_286_, v___y_287_, v___y_288_);
if (lean_obj_tag(v___x_360_) == 0)
{
lean_object* v_a_361_; lean_object* v___x_363_; uint8_t v_isShared_364_; uint8_t v_isSharedCheck_380_; 
v_a_361_ = lean_ctor_get(v___x_360_, 0);
v_isSharedCheck_380_ = !lean_is_exclusive(v___x_360_);
if (v_isSharedCheck_380_ == 0)
{
v___x_363_ = v___x_360_;
v_isShared_364_ = v_isSharedCheck_380_;
goto v_resetjp_362_;
}
else
{
lean_inc(v_a_361_);
lean_dec(v___x_360_);
v___x_363_ = lean_box(0);
v_isShared_364_ = v_isSharedCheck_380_;
goto v_resetjp_362_;
}
v_resetjp_362_:
{
lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_378_; 
v___x_365_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__24, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__24_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__24);
v___x_366_ = l_Lean_mkIntEq(v_a_359_, v___x_365_);
v___x_367_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30);
v___x_368_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_184_);
v___x_369_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_188_);
v___x_370_ = l_Lean_Meta_Simp_Arith_Int_ofPoly(v___x_283_);
v___x_371_ = l_Lean_eagerReflBoolTrue;
v___x_372_ = l_Lean_mkApp5(v___x_367_, v_a_361_, v___x_368_, v___x_369_, v___x_370_, v___x_371_);
lean_inc_ref(v___x_366_);
v___x_373_ = l_Lean_mkPropEq(v___x_205_, v___x_366_);
v___x_374_ = l_Lean_Meta_mkExpectedPropHint(v___x_372_, v___x_373_);
v___x_375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_375_, 0, v___x_366_);
lean_ctor_set(v___x_375_, 1, v___x_374_);
v___x_376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_376_, 0, v___x_375_);
if (v_isShared_364_ == 0)
{
lean_ctor_set(v___x_363_, 0, v___x_376_);
v___x_378_ = v___x_363_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v___x_376_);
v___x_378_ = v_reuseFailAlloc_379_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
return v___x_378_;
}
}
}
else
{
lean_object* v_a_381_; lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_388_; 
lean_dec(v_a_359_);
lean_dec_ref(v___x_283_);
lean_dec_ref(v___x_205_);
lean_dec(v_fst_188_);
lean_dec(v_fst_184_);
v_a_381_ = lean_ctor_get(v___x_360_, 0);
v_isSharedCheck_388_ = !lean_is_exclusive(v___x_360_);
if (v_isSharedCheck_388_ == 0)
{
v___x_383_ = v___x_360_;
v_isShared_384_ = v_isSharedCheck_388_;
goto v_resetjp_382_;
}
else
{
lean_inc(v_a_381_);
lean_dec(v___x_360_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_388_;
goto v_resetjp_382_;
}
v_resetjp_382_:
{
lean_object* v___x_386_; 
if (v_isShared_384_ == 0)
{
v___x_386_ = v___x_383_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_387_; 
v_reuseFailAlloc_387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_387_, 0, v_a_381_);
v___x_386_ = v_reuseFailAlloc_387_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
return v___x_386_;
}
}
}
}
else
{
lean_object* v_a_389_; lean_object* v___x_391_; uint8_t v_isShared_392_; uint8_t v_isSharedCheck_396_; 
lean_dec_ref(v___x_283_);
lean_dec_ref(v___x_205_);
lean_dec(v_snd_189_);
lean_dec(v_fst_188_);
lean_dec(v_fst_184_);
v_a_389_ = lean_ctor_get(v___x_358_, 0);
v_isSharedCheck_396_ = !lean_is_exclusive(v___x_358_);
if (v_isSharedCheck_396_ == 0)
{
v___x_391_ = v___x_358_;
v_isShared_392_ = v_isSharedCheck_396_;
goto v_resetjp_390_;
}
else
{
lean_inc(v_a_389_);
lean_dec(v___x_358_);
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
v___jp_397_:
{
if (v___y_398_ == 0)
{
if (lean_obj_tag(v___x_283_) == 1)
{
lean_object* v_k_399_; lean_object* v_v_400_; lean_object* v_p_401_; lean_object* v___x_402_; uint8_t v___x_403_; 
v_k_399_ = lean_ctor_get(v___x_283_, 0);
lean_inc(v_k_399_);
v_v_400_ = lean_ctor_get(v___x_283_, 1);
lean_inc(v_v_400_);
v_p_401_ = lean_ctor_get(v___x_283_, 2);
lean_inc_ref(v_p_401_);
v___x_402_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__31, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__31_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__31);
v___x_403_ = lean_int_dec_eq(v_k_399_, v___x_402_);
lean_dec(v_k_399_);
if (v___x_403_ == 0)
{
lean_dec_ref(v_p_401_);
lean_dec(v_v_400_);
lean_del_object(v___x_177_);
v___y_285_ = v_a_169_;
v___y_286_ = v_a_170_;
v___y_287_ = v_a_171_;
v___y_288_ = v_a_172_;
goto v___jp_284_;
}
else
{
if (lean_obj_tag(v_p_401_) == 0)
{
lean_object* v_k_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; uint8_t v___x_408_; 
lean_dec_ref_known(v___x_283_, 3);
lean_del_object(v___x_203_);
lean_del_object(v___x_198_);
lean_dec_ref(v___f_194_);
lean_del_object(v___x_191_);
lean_del_object(v___x_186_);
lean_del_object(v___x_181_);
v_k_404_ = lean_ctor_get(v_p_401_, 0);
lean_inc(v_k_404_);
lean_dec_ref_known(v_p_401_, 1);
v___x_405_ = lean_array_get_borrowed(v___x_193_, v_snd_189_, v_v_400_);
v___x_406_ = lean_int_neg(v_k_404_);
lean_dec(v_k_404_);
v___x_407_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6);
v___x_408_ = lean_int_dec_le(v___x_407_, v___x_406_);
if (v___x_408_ == 0)
{
lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; 
v___x_409_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18);
v___x_410_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20);
v___x_411_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23);
v___x_412_ = lean_int_neg(v___x_406_);
lean_dec(v___x_406_);
v___x_413_ = l_Int_toNat(v___x_412_);
lean_dec(v___x_412_);
v___x_414_ = l_Lean_instToExprInt_mkNat(v___x_413_);
v___x_415_ = l_Lean_mkApp3(v___x_409_, v___x_410_, v___x_411_, v___x_414_);
lean_inc(v___x_405_);
v___y_246_ = v___x_405_;
v___y_247_ = v_v_400_;
v___y_248_ = v___x_415_;
goto v___jp_245_;
}
else
{
lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_416_ = l_Int_toNat(v___x_406_);
lean_dec(v___x_406_);
v___x_417_ = l_Lean_instToExprInt_mkNat(v___x_416_);
lean_inc(v___x_405_);
v___y_246_ = v___x_405_;
v___y_247_ = v_v_400_;
v___y_248_ = v___x_417_;
goto v___jp_245_;
}
}
else
{
lean_object* v_k_418_; lean_object* v_v_419_; lean_object* v_p_420_; lean_object* v___x_421_; uint8_t v___x_422_; 
lean_del_object(v___x_177_);
v_k_418_ = lean_ctor_get(v_p_401_, 0);
lean_inc(v_k_418_);
v_v_419_ = lean_ctor_get(v_p_401_, 1);
lean_inc(v_v_419_);
v_p_420_ = lean_ctor_get(v_p_401_, 2);
lean_inc_ref(v_p_420_);
lean_dec_ref_known(v_p_401_, 3);
v___x_421_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__32, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__32_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__32);
v___x_422_ = lean_int_dec_eq(v_k_418_, v___x_421_);
lean_dec(v_k_418_);
if (v___x_422_ == 0)
{
lean_dec_ref(v_p_420_);
lean_dec(v_v_419_);
lean_dec(v_v_400_);
v___y_285_ = v_a_169_;
v___y_286_ = v_a_170_;
v___y_287_ = v_a_171_;
v___y_288_ = v_a_172_;
goto v___jp_284_;
}
else
{
if (lean_obj_tag(v_p_420_) == 0)
{
lean_object* v_k_423_; lean_object* v___x_425_; uint8_t v_isShared_426_; uint8_t v_isSharedCheck_467_; 
v_k_423_ = lean_ctor_get(v_p_420_, 0);
v_isSharedCheck_467_ = !lean_is_exclusive(v_p_420_);
if (v_isSharedCheck_467_ == 0)
{
v___x_425_ = v_p_420_;
v_isShared_426_ = v_isSharedCheck_467_;
goto v_resetjp_424_;
}
else
{
lean_inc(v_k_423_);
lean_dec(v_p_420_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_467_;
goto v_resetjp_424_;
}
v_resetjp_424_:
{
lean_object* v___x_427_; uint8_t v___x_428_; 
v___x_427_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6);
v___x_428_ = lean_int_dec_eq(v_k_423_, v___x_427_);
lean_dec(v_k_423_);
if (v___x_428_ == 0)
{
lean_del_object(v___x_425_);
lean_dec(v_v_419_);
lean_dec(v_v_400_);
v___y_285_ = v_a_169_;
v___y_286_ = v_a_170_;
v___y_287_ = v_a_171_;
v___y_288_ = v_a_172_;
goto v___jp_284_;
}
else
{
lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; uint8_t v___x_432_; 
lean_dec_ref_known(v___x_283_, 3);
lean_del_object(v___x_203_);
lean_del_object(v___x_198_);
lean_dec_ref(v___f_194_);
lean_del_object(v___x_191_);
lean_del_object(v___x_186_);
lean_del_object(v___x_181_);
v___x_429_ = lean_array_get_borrowed(v___x_193_, v_snd_189_, v_v_400_);
v___x_430_ = lean_array_get_borrowed(v___x_193_, v_snd_189_, v_v_419_);
lean_inc(v___x_430_);
lean_inc(v___x_429_);
v___x_431_ = l_Lean_mkIntEq(v___x_429_, v___x_430_);
v___x_432_ = lean_expr_eqv(v___x_431_, v___x_205_);
if (v___x_432_ == 0)
{
lean_object* v___x_433_; 
v___x_433_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(v_snd_189_, v_a_169_, v_a_170_, v_a_171_, v_a_172_);
if (lean_obj_tag(v___x_433_) == 0)
{
lean_object* v_a_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_454_; 
v_a_434_ = lean_ctor_get(v___x_433_, 0);
v_isSharedCheck_454_ = !lean_is_exclusive(v___x_433_);
if (v_isSharedCheck_454_ == 0)
{
v___x_436_ = v___x_433_;
v_isShared_437_ = v_isSharedCheck_454_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_a_434_);
lean_dec(v___x_433_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_454_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_449_; 
v___x_438_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__35, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__35_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__35);
v___x_439_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_184_);
v___x_440_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_188_);
v___x_441_ = l_Lean_mkNatLit(v_v_400_);
v___x_442_ = l_Lean_mkNatLit(v_v_419_);
v___x_443_ = l_Lean_eagerReflBoolTrue;
v___x_444_ = l_Lean_mkApp6(v___x_438_, v_a_434_, v___x_439_, v___x_440_, v___x_441_, v___x_442_, v___x_443_);
lean_inc_ref(v___x_431_);
v___x_445_ = l_Lean_mkPropEq(v___x_205_, v___x_431_);
v___x_446_ = l_Lean_Meta_mkExpectedPropHint(v___x_444_, v___x_445_);
v___x_447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_447_, 0, v___x_431_);
lean_ctor_set(v___x_447_, 1, v___x_446_);
if (v_isShared_426_ == 0)
{
lean_ctor_set_tag(v___x_425_, 1);
lean_ctor_set(v___x_425_, 0, v___x_447_);
v___x_449_ = v___x_425_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v___x_447_);
v___x_449_ = v_reuseFailAlloc_453_;
goto v_reusejp_448_;
}
v_reusejp_448_:
{
lean_object* v___x_451_; 
if (v_isShared_437_ == 0)
{
lean_ctor_set(v___x_436_, 0, v___x_449_);
v___x_451_ = v___x_436_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v___x_449_);
v___x_451_ = v_reuseFailAlloc_452_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
return v___x_451_;
}
}
}
}
else
{
lean_object* v_a_455_; lean_object* v___x_457_; uint8_t v_isShared_458_; uint8_t v_isSharedCheck_462_; 
lean_dec_ref(v___x_431_);
lean_del_object(v___x_425_);
lean_dec(v_v_419_);
lean_dec(v_v_400_);
lean_dec_ref(v___x_205_);
lean_dec(v_fst_188_);
lean_dec(v_fst_184_);
v_a_455_ = lean_ctor_get(v___x_433_, 0);
v_isSharedCheck_462_ = !lean_is_exclusive(v___x_433_);
if (v_isSharedCheck_462_ == 0)
{
v___x_457_ = v___x_433_;
v_isShared_458_ = v_isSharedCheck_462_;
goto v_resetjp_456_;
}
else
{
lean_inc(v_a_455_);
lean_dec(v___x_433_);
v___x_457_ = lean_box(0);
v_isShared_458_ = v_isSharedCheck_462_;
goto v_resetjp_456_;
}
v_resetjp_456_:
{
lean_object* v___x_460_; 
if (v_isShared_458_ == 0)
{
v___x_460_ = v___x_457_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v_a_455_);
v___x_460_ = v_reuseFailAlloc_461_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
return v___x_460_;
}
}
}
}
else
{
lean_object* v___x_463_; lean_object* v___x_465_; 
lean_dec_ref(v___x_431_);
lean_dec(v_v_419_);
lean_dec(v_v_400_);
lean_dec_ref(v___x_205_);
lean_dec(v_snd_189_);
lean_dec(v_fst_188_);
lean_dec(v_fst_184_);
v___x_463_ = lean_box(0);
if (v_isShared_426_ == 0)
{
lean_ctor_set(v___x_425_, 0, v___x_463_);
v___x_465_ = v___x_425_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v___x_463_);
v___x_465_ = v_reuseFailAlloc_466_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
return v___x_465_;
}
}
}
}
}
else
{
lean_dec_ref(v_p_420_);
lean_dec(v_v_419_);
lean_dec(v_v_400_);
v___y_285_ = v_a_169_;
v___y_286_ = v_a_170_;
v___y_287_ = v_a_171_;
v___y_288_ = v_a_172_;
goto v___jp_284_;
}
}
}
}
}
else
{
lean_del_object(v___x_177_);
v___y_285_ = v_a_169_;
v___y_286_ = v_a_170_;
v___y_287_ = v_a_171_;
v___y_288_ = v_a_172_;
goto v___jp_284_;
}
}
else
{
lean_object* v___x_468_; lean_object* v___x_469_; 
lean_dec_ref(v___x_283_);
lean_dec_ref(v___x_205_);
lean_del_object(v___x_203_);
lean_del_object(v___x_198_);
lean_dec_ref(v___f_194_);
lean_del_object(v___x_191_);
lean_dec(v_snd_189_);
lean_dec(v_fst_188_);
lean_del_object(v___x_186_);
lean_dec(v_fst_184_);
lean_del_object(v___x_181_);
lean_del_object(v___x_177_);
v___x_468_ = lean_box(0);
v___x_469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_469_, 0, v___x_468_);
return v___x_469_;
}
}
}
}
else
{
lean_object* v_a_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_538_; 
lean_del_object(v___x_198_);
lean_dec(v_a_196_);
lean_dec_ref(v___f_194_);
lean_del_object(v___x_191_);
lean_dec(v_snd_189_);
lean_dec(v_fst_188_);
lean_del_object(v___x_186_);
lean_dec(v_fst_184_);
lean_del_object(v___x_181_);
lean_del_object(v___x_177_);
v_a_531_ = lean_ctor_get(v___x_200_, 0);
v_isSharedCheck_538_ = !lean_is_exclusive(v___x_200_);
if (v_isSharedCheck_538_ == 0)
{
v___x_533_ = v___x_200_;
v_isShared_534_ = v_isSharedCheck_538_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_a_531_);
lean_dec(v___x_200_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_538_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
lean_object* v___x_536_; 
if (v_isShared_534_ == 0)
{
v___x_536_ = v___x_533_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v_a_531_);
v___x_536_ = v_reuseFailAlloc_537_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
return v___x_536_;
}
}
}
}
}
else
{
lean_object* v_a_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_547_; 
lean_dec_ref(v___f_194_);
lean_del_object(v___x_191_);
lean_dec(v_snd_189_);
lean_dec(v_fst_188_);
lean_del_object(v___x_186_);
lean_dec(v_fst_184_);
lean_del_object(v___x_181_);
lean_del_object(v___x_177_);
v_a_540_ = lean_ctor_get(v___x_195_, 0);
v_isSharedCheck_547_ = !lean_is_exclusive(v___x_195_);
if (v_isSharedCheck_547_ == 0)
{
v___x_542_ = v___x_195_;
v_isShared_543_ = v_isSharedCheck_547_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_a_540_);
lean_dec(v___x_195_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_547_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
lean_object* v___x_545_; 
if (v_isShared_543_ == 0)
{
v___x_545_ = v___x_542_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v_a_540_);
v___x_545_ = v_reuseFailAlloc_546_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
return v___x_545_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_551_; lean_object* v___x_553_; 
lean_dec(v_a_175_);
v___x_551_ = lean_box(0);
if (v_isShared_178_ == 0)
{
lean_ctor_set(v___x_177_, 0, v___x_551_);
v___x_553_ = v___x_177_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v___x_551_);
v___x_553_ = v_reuseFailAlloc_554_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
return v___x_553_;
}
}
}
}
else
{
lean_object* v_a_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_563_; 
v_a_556_ = lean_ctor_get(v___x_174_, 0);
v_isSharedCheck_563_ = !lean_is_exclusive(v___x_174_);
if (v_isSharedCheck_563_ == 0)
{
v___x_558_ = v___x_174_;
v_isShared_559_ = v_isSharedCheck_563_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_a_556_);
lean_dec(v___x_174_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_563_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
lean_object* v___x_561_; 
if (v_isShared_559_ == 0)
{
v___x_561_ = v___x_558_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v_a_556_);
v___x_561_ = v_reuseFailAlloc_562_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
return v___x_561_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___boxed(lean_object* v_e_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_, lean_object* v_a_569_){
_start:
{
lean_object* v_res_570_; 
v_res_570_ = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f(v_e_564_, v_a_565_, v_a_566_, v_a_567_, v_a_568_);
lean_dec(v_a_568_);
lean_dec_ref(v_a_567_);
lean_dec(v_a_566_);
lean_dec_ref(v_a_565_);
return v_res_570_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__2(void){
_start:
{
lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; 
v___x_577_ = lean_box(0);
v___x_578_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__1));
v___x_579_ = l_Lean_mkConst(v___x_578_, v___x_577_);
return v___x_579_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__5(void){
_start:
{
lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; 
v___x_586_ = lean_box(0);
v___x_587_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__4));
v___x_588_ = l_Lean_mkConst(v___x_587_, v___x_586_);
return v___x_588_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__8(void){
_start:
{
lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; 
v___x_595_ = lean_box(0);
v___x_596_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__7));
v___x_597_ = l_Lean_mkConst(v___x_596_, v___x_595_);
return v___x_597_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__11(void){
_start:
{
lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; 
v___x_604_ = lean_box(0);
v___x_605_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__10));
v___x_606_ = l_Lean_mkConst(v___x_605_, v___x_604_);
return v___x_606_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__14(void){
_start:
{
lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_613_ = lean_box(0);
v___x_614_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__13));
v___x_615_ = l_Lean_mkConst(v___x_614_, v___x_613_);
return v___x_615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f(lean_object* v_e_621_, uint8_t v_checkIfModified_622_, lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_, lean_object* v_a_626_){
_start:
{
lean_object* v___y_629_; lean_object* v___y_630_; lean_object* v_h_631_; lean_object* v___y_638_; lean_object* v___y_639_; lean_object* v___y_640_; lean_object* v___y_641_; lean_object* v___y_642_; lean_object* v___y_643_; lean_object* v___y_644_; lean_object* v___y_645_; lean_object* v___y_649_; lean_object* v___y_650_; lean_object* v___y_651_; lean_object* v___y_652_; lean_object* v___y_653_; lean_object* v___y_654_; lean_object* v___y_655_; lean_object* v___y_656_; lean_object* v___y_660_; lean_object* v___y_661_; lean_object* v___y_662_; lean_object* v___y_663_; lean_object* v___y_664_; lean_object* v___y_665_; lean_object* v___x_775_; uint8_t v___y_777_; lean_object* v___x_915_; uint8_t v___x_916_; 
v___x_775_ = l_Lean_instInhabitedExpr;
v___x_915_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__17));
v___x_916_ = l_Lean_Expr_isAppOf(v_e_621_, v___x_915_);
if (v___x_916_ == 0)
{
v___y_777_ = v___x_916_;
goto v___jp_776_;
}
else
{
v___y_777_ = v_checkIfModified_622_;
goto v___jp_776_;
}
v___jp_628_:
{
lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; 
lean_inc_ref(v___y_630_);
v___x_632_ = l_Lean_mkPropEq(v___y_629_, v___y_630_);
v___x_633_ = l_Lean_Meta_mkExpectedPropHint(v_h_631_, v___x_632_);
v___x_634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_634_, 0, v___y_630_);
lean_ctor_set(v___x_634_, 1, v___x_633_);
v___x_635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_635_, 0, v___x_634_);
v___x_636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_636_, 0, v___x_635_);
return v___x_636_;
}
v___jp_637_:
{
lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_646_ = l_Lean_eagerReflBoolTrue;
lean_inc_ref(v___y_639_);
v___x_647_ = l_Lean_mkApp6(v___y_639_, v___y_641_, v___y_644_, v___y_640_, v___y_638_, v___y_645_, v___x_646_);
v___y_629_ = v___y_642_;
v___y_630_ = v___y_643_;
v_h_631_ = v___x_647_;
goto v___jp_628_;
}
v___jp_648_:
{
lean_object* v___x_657_; lean_object* v___x_658_; 
v___x_657_ = l_Lean_eagerReflBoolTrue;
lean_inc_ref(v___y_649_);
v___x_658_ = l_Lean_mkApp6(v___y_649_, v___y_655_, v___y_654_, v___y_651_, v___y_650_, v___y_656_, v___x_657_);
v___y_629_ = v___y_652_;
v___y_630_ = v___y_653_;
v_h_631_ = v___x_658_;
goto v___jp_628_;
}
v___jp_659_:
{
lean_object* v___x_666_; lean_object* v___x_667_; uint8_t v___x_668_; 
v___x_666_ = l_Int_Internal_Linear_Poly_gcdCoeffs_x27(v___y_665_);
v___x_667_ = lean_unsigned_to_nat(1u);
v___x_668_ = lean_nat_dec_eq(v___x_666_, v___x_667_);
if (v___x_668_ == 0)
{
lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; 
v___x_669_ = l_Int_Internal_Linear_Poly_getConst(v___y_665_);
v___x_670_ = lean_nat_to_int(v___x_666_);
v___x_671_ = l_Int_Internal_Linear_Poly_div(v___x_670_, v___y_665_);
lean_inc_ref(v___x_671_);
v___x_672_ = l_Int_Internal_Linear_Poly_denoteExpr___redArg(v___y_661_, v___x_671_);
if (lean_obj_tag(v___x_672_) == 0)
{
lean_object* v_a_673_; lean_object* v___x_674_; lean_object* v___x_675_; uint8_t v___x_676_; uint8_t v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; 
v_a_673_ = lean_ctor_get(v___x_672_, 0);
lean_inc(v_a_673_);
lean_dec_ref_known(v___x_672_, 1);
v___x_674_ = lean_int_emod(v___x_669_, v___x_670_);
lean_dec(v___x_669_);
v___x_675_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6);
v___x_676_ = lean_int_dec_eq(v___x_674_, v___x_675_);
lean_dec(v___x_674_);
v___x_677_ = lean_bool_not(v___x_676_);
v___x_678_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__24, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__24_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__24);
v___x_679_ = l_Lean_mkIntLE(v_a_673_, v___x_678_);
if (v___x_677_ == 0)
{
lean_object* v___x_680_; 
v___x_680_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(v___y_664_, v_a_623_, v_a_624_, v_a_625_, v_a_626_);
if (lean_obj_tag(v___x_680_) == 0)
{
lean_object* v_a_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; uint8_t v___x_686_; 
v_a_681_ = lean_ctor_get(v___x_680_, 0);
lean_inc(v_a_681_);
lean_dec_ref_known(v___x_680_, 1);
v___x_682_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__2, &l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__2_once, _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__2);
v___x_683_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v___y_662_);
v___x_684_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v___y_660_);
v___x_685_ = l_Lean_Meta_Simp_Arith_Int_ofPoly(v___x_671_);
v___x_686_ = lean_int_dec_le(v___x_675_, v___x_670_);
if (v___x_686_ == 0)
{
lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_687_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18);
v___x_688_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20);
v___x_689_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23);
v___x_690_ = lean_int_neg(v___x_670_);
lean_dec(v___x_670_);
v___x_691_ = l_Int_toNat(v___x_690_);
lean_dec(v___x_690_);
v___x_692_ = l_Lean_instToExprInt_mkNat(v___x_691_);
v___x_693_ = l_Lean_mkApp3(v___x_687_, v___x_688_, v___x_689_, v___x_692_);
v___y_649_ = v___x_682_;
v___y_650_ = v___x_685_;
v___y_651_ = v___x_684_;
v___y_652_ = v___y_663_;
v___y_653_ = v___x_679_;
v___y_654_ = v___x_683_;
v___y_655_ = v_a_681_;
v___y_656_ = v___x_693_;
goto v___jp_648_;
}
else
{
lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_694_ = l_Int_toNat(v___x_670_);
lean_dec(v___x_670_);
v___x_695_ = l_Lean_instToExprInt_mkNat(v___x_694_);
v___y_649_ = v___x_682_;
v___y_650_ = v___x_685_;
v___y_651_ = v___x_684_;
v___y_652_ = v___y_663_;
v___y_653_ = v___x_679_;
v___y_654_ = v___x_683_;
v___y_655_ = v_a_681_;
v___y_656_ = v___x_695_;
goto v___jp_648_;
}
}
else
{
lean_object* v_a_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_703_; 
lean_dec_ref(v___x_679_);
lean_dec_ref(v___x_671_);
lean_dec(v___x_670_);
lean_dec_ref(v___y_663_);
lean_dec_ref(v___y_662_);
lean_dec_ref(v___y_660_);
v_a_696_ = lean_ctor_get(v___x_680_, 0);
v_isSharedCheck_703_ = !lean_is_exclusive(v___x_680_);
if (v_isSharedCheck_703_ == 0)
{
v___x_698_ = v___x_680_;
v_isShared_699_ = v_isSharedCheck_703_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_a_696_);
lean_dec(v___x_680_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_703_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___x_701_; 
if (v_isShared_699_ == 0)
{
v___x_701_ = v___x_698_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v_a_696_);
v___x_701_ = v_reuseFailAlloc_702_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
return v___x_701_;
}
}
}
}
else
{
lean_object* v___x_704_; 
v___x_704_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(v___y_664_, v_a_623_, v_a_624_, v_a_625_, v_a_626_);
if (lean_obj_tag(v___x_704_) == 0)
{
lean_object* v_a_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; uint8_t v___x_710_; 
v_a_705_ = lean_ctor_get(v___x_704_, 0);
lean_inc(v_a_705_);
lean_dec_ref_known(v___x_704_, 1);
v___x_706_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__5, &l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__5_once, _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__5);
v___x_707_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v___y_662_);
v___x_708_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v___y_660_);
v___x_709_ = l_Lean_Meta_Simp_Arith_Int_ofPoly(v___x_671_);
v___x_710_ = lean_int_dec_le(v___x_675_, v___x_670_);
if (v___x_710_ == 0)
{
lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; 
v___x_711_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18);
v___x_712_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20);
v___x_713_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23);
v___x_714_ = lean_int_neg(v___x_670_);
lean_dec(v___x_670_);
v___x_715_ = l_Int_toNat(v___x_714_);
lean_dec(v___x_714_);
v___x_716_ = l_Lean_instToExprInt_mkNat(v___x_715_);
v___x_717_ = l_Lean_mkApp3(v___x_711_, v___x_712_, v___x_713_, v___x_716_);
v___y_638_ = v___x_709_;
v___y_639_ = v___x_706_;
v___y_640_ = v___x_708_;
v___y_641_ = v_a_705_;
v___y_642_ = v___y_663_;
v___y_643_ = v___x_679_;
v___y_644_ = v___x_707_;
v___y_645_ = v___x_717_;
goto v___jp_637_;
}
else
{
lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_718_ = l_Int_toNat(v___x_670_);
lean_dec(v___x_670_);
v___x_719_ = l_Lean_instToExprInt_mkNat(v___x_718_);
v___y_638_ = v___x_709_;
v___y_639_ = v___x_706_;
v___y_640_ = v___x_708_;
v___y_641_ = v_a_705_;
v___y_642_ = v___y_663_;
v___y_643_ = v___x_679_;
v___y_644_ = v___x_707_;
v___y_645_ = v___x_719_;
goto v___jp_637_;
}
}
else
{
lean_object* v_a_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_727_; 
lean_dec_ref(v___x_679_);
lean_dec_ref(v___x_671_);
lean_dec(v___x_670_);
lean_dec_ref(v___y_663_);
lean_dec_ref(v___y_662_);
lean_dec_ref(v___y_660_);
v_a_720_ = lean_ctor_get(v___x_704_, 0);
v_isSharedCheck_727_ = !lean_is_exclusive(v___x_704_);
if (v_isSharedCheck_727_ == 0)
{
v___x_722_ = v___x_704_;
v_isShared_723_ = v_isSharedCheck_727_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_a_720_);
lean_dec(v___x_704_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_727_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
lean_object* v___x_725_; 
if (v_isShared_723_ == 0)
{
v___x_725_ = v___x_722_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v_a_720_);
v___x_725_ = v_reuseFailAlloc_726_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
return v___x_725_;
}
}
}
}
}
else
{
lean_object* v_a_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_735_; 
lean_dec_ref(v___x_671_);
lean_dec(v___x_670_);
lean_dec(v___x_669_);
lean_dec_ref(v___y_664_);
lean_dec_ref(v___y_663_);
lean_dec_ref(v___y_662_);
lean_dec_ref(v___y_660_);
v_a_728_ = lean_ctor_get(v___x_672_, 0);
v_isSharedCheck_735_ = !lean_is_exclusive(v___x_672_);
if (v_isSharedCheck_735_ == 0)
{
v___x_730_ = v___x_672_;
v_isShared_731_ = v_isSharedCheck_735_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_a_728_);
lean_dec(v___x_672_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_735_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v___x_733_; 
if (v_isShared_731_ == 0)
{
v___x_733_ = v___x_730_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v_a_728_);
v___x_733_ = v_reuseFailAlloc_734_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
return v___x_733_;
}
}
}
}
else
{
lean_object* v___x_736_; 
lean_dec(v___x_666_);
lean_inc_ref(v___y_665_);
v___x_736_ = l_Int_Internal_Linear_Poly_denoteExpr___redArg(v___y_661_, v___y_665_);
if (lean_obj_tag(v___x_736_) == 0)
{
lean_object* v_a_737_; lean_object* v___x_738_; 
v_a_737_ = lean_ctor_get(v___x_736_, 0);
lean_inc(v_a_737_);
lean_dec_ref_known(v___x_736_, 1);
v___x_738_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(v___y_664_, v_a_623_, v_a_624_, v_a_625_, v_a_626_);
if (lean_obj_tag(v___x_738_) == 0)
{
lean_object* v_a_739_; lean_object* v___x_741_; uint8_t v_isShared_742_; uint8_t v_isSharedCheck_758_; 
v_a_739_ = lean_ctor_get(v___x_738_, 0);
v_isSharedCheck_758_ = !lean_is_exclusive(v___x_738_);
if (v_isSharedCheck_758_ == 0)
{
v___x_741_ = v___x_738_;
v_isShared_742_ = v_isSharedCheck_758_;
goto v_resetjp_740_;
}
else
{
lean_inc(v_a_739_);
lean_dec(v___x_738_);
v___x_741_ = lean_box(0);
v_isShared_742_ = v_isSharedCheck_758_;
goto v_resetjp_740_;
}
v_resetjp_740_:
{
lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_756_; 
v___x_743_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__24, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__24_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__24);
v___x_744_ = l_Lean_mkIntLE(v_a_737_, v___x_743_);
v___x_745_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__8, &l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__8_once, _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__8);
v___x_746_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v___y_662_);
v___x_747_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v___y_660_);
v___x_748_ = l_Lean_Meta_Simp_Arith_Int_ofPoly(v___y_665_);
v___x_749_ = l_Lean_eagerReflBoolTrue;
v___x_750_ = l_Lean_mkApp5(v___x_745_, v_a_739_, v___x_746_, v___x_747_, v___x_748_, v___x_749_);
lean_inc_ref(v___x_744_);
v___x_751_ = l_Lean_mkPropEq(v___y_663_, v___x_744_);
v___x_752_ = l_Lean_Meta_mkExpectedPropHint(v___x_750_, v___x_751_);
v___x_753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_753_, 0, v___x_744_);
lean_ctor_set(v___x_753_, 1, v___x_752_);
v___x_754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_754_, 0, v___x_753_);
if (v_isShared_742_ == 0)
{
lean_ctor_set(v___x_741_, 0, v___x_754_);
v___x_756_ = v___x_741_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v___x_754_);
v___x_756_ = v_reuseFailAlloc_757_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
return v___x_756_;
}
}
}
else
{
lean_object* v_a_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_766_; 
lean_dec(v_a_737_);
lean_dec_ref(v___y_665_);
lean_dec_ref(v___y_663_);
lean_dec_ref(v___y_662_);
lean_dec_ref(v___y_660_);
v_a_759_ = lean_ctor_get(v___x_738_, 0);
v_isSharedCheck_766_ = !lean_is_exclusive(v___x_738_);
if (v_isSharedCheck_766_ == 0)
{
v___x_761_ = v___x_738_;
v_isShared_762_ = v_isSharedCheck_766_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_a_759_);
lean_dec(v___x_738_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_766_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v___x_764_; 
if (v_isShared_762_ == 0)
{
v___x_764_ = v___x_761_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v_a_759_);
v___x_764_ = v_reuseFailAlloc_765_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
return v___x_764_;
}
}
}
}
else
{
lean_object* v_a_767_; lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_774_; 
lean_dec_ref(v___y_665_);
lean_dec_ref(v___y_664_);
lean_dec_ref(v___y_663_);
lean_dec_ref(v___y_662_);
lean_dec_ref(v___y_660_);
v_a_767_ = lean_ctor_get(v___x_736_, 0);
v_isSharedCheck_774_ = !lean_is_exclusive(v___x_736_);
if (v_isSharedCheck_774_ == 0)
{
v___x_769_ = v___x_736_;
v_isShared_770_ = v_isSharedCheck_774_;
goto v_resetjp_768_;
}
else
{
lean_inc(v_a_767_);
lean_dec(v___x_736_);
v___x_769_ = lean_box(0);
v_isShared_770_ = v_isSharedCheck_774_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
lean_object* v___x_772_; 
if (v_isShared_770_ == 0)
{
v___x_772_ = v___x_769_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v_a_767_);
v___x_772_ = v_reuseFailAlloc_773_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
return v___x_772_;
}
}
}
}
}
v___jp_776_:
{
lean_object* v___x_778_; 
v___x_778_ = l_Lean_Meta_Simp_Arith_Int_leCnstr_x3f(v_e_621_, v_a_623_, v_a_624_, v_a_625_, v_a_626_);
if (lean_obj_tag(v___x_778_) == 0)
{
lean_object* v_a_779_; lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_906_; 
v_a_779_ = lean_ctor_get(v___x_778_, 0);
v_isSharedCheck_906_ = !lean_is_exclusive(v___x_778_);
if (v_isSharedCheck_906_ == 0)
{
v___x_781_ = v___x_778_;
v_isShared_782_ = v_isSharedCheck_906_;
goto v_resetjp_780_;
}
else
{
lean_inc(v_a_779_);
lean_dec(v___x_778_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_906_;
goto v_resetjp_780_;
}
v_resetjp_780_:
{
if (lean_obj_tag(v_a_779_) == 1)
{
lean_object* v_val_783_; lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_901_; 
lean_del_object(v___x_781_);
v_val_783_ = lean_ctor_get(v_a_779_, 0);
v_isSharedCheck_901_ = !lean_is_exclusive(v_a_779_);
if (v_isSharedCheck_901_ == 0)
{
v___x_785_ = v_a_779_;
v_isShared_786_ = v_isSharedCheck_901_;
goto v_resetjp_784_;
}
else
{
lean_inc(v_val_783_);
lean_dec(v_a_779_);
v___x_785_ = lean_box(0);
v_isShared_786_ = v_isSharedCheck_901_;
goto v_resetjp_784_;
}
v_resetjp_784_:
{
lean_object* v_snd_787_; lean_object* v_fst_788_; lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_900_; 
v_snd_787_ = lean_ctor_get(v_val_783_, 1);
v_fst_788_ = lean_ctor_get(v_val_783_, 0);
v_isSharedCheck_900_ = !lean_is_exclusive(v_val_783_);
if (v_isSharedCheck_900_ == 0)
{
v___x_790_ = v_val_783_;
v_isShared_791_ = v_isSharedCheck_900_;
goto v_resetjp_789_;
}
else
{
lean_inc(v_snd_787_);
lean_inc(v_fst_788_);
lean_dec(v_val_783_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_900_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v_fst_792_; lean_object* v_snd_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_899_; 
v_fst_792_ = lean_ctor_get(v_snd_787_, 0);
v_snd_793_ = lean_ctor_get(v_snd_787_, 1);
v_isSharedCheck_899_ = !lean_is_exclusive(v_snd_787_);
if (v_isSharedCheck_899_ == 0)
{
v___x_795_ = v_snd_787_;
v_isShared_796_ = v_isSharedCheck_899_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_snd_793_);
lean_inc(v_fst_792_);
lean_dec(v_snd_787_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_899_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v___f_797_; lean_object* v___x_798_; 
lean_inc(v_snd_793_);
v___f_797_ = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__0___boxed), 3, 2);
lean_closure_set(v___f_797_, 0, v___x_775_);
lean_closure_set(v___f_797_, 1, v_snd_793_);
lean_inc(v_fst_788_);
lean_inc_ref(v___f_797_);
v___x_798_ = l_Int_Internal_Linear_Expr_denoteExpr___redArg(v___f_797_, v_fst_788_);
if (lean_obj_tag(v___x_798_) == 0)
{
lean_object* v_a_799_; lean_object* v___x_800_; 
v_a_799_ = lean_ctor_get(v___x_798_, 0);
lean_inc(v_a_799_);
lean_dec_ref_known(v___x_798_, 1);
lean_inc(v_fst_792_);
lean_inc_ref(v___f_797_);
v___x_800_ = l_Int_Internal_Linear_Expr_denoteExpr___redArg(v___f_797_, v_fst_792_);
if (lean_obj_tag(v___x_800_) == 0)
{
lean_object* v_a_801_; lean_object* v___x_803_; uint8_t v_isShared_804_; uint8_t v_isSharedCheck_882_; 
v_a_801_ = lean_ctor_get(v___x_800_, 0);
v_isSharedCheck_882_ = !lean_is_exclusive(v___x_800_);
if (v_isSharedCheck_882_ == 0)
{
v___x_803_ = v___x_800_;
v_isShared_804_ = v_isSharedCheck_882_;
goto v_resetjp_802_;
}
else
{
lean_inc(v_a_801_);
lean_dec(v___x_800_);
v___x_803_ = lean_box(0);
v_isShared_804_ = v_isSharedCheck_882_;
goto v_resetjp_802_;
}
v_resetjp_802_:
{
lean_object* v___x_805_; lean_object* v___x_807_; 
v___x_805_ = l_Lean_mkIntLE(v_a_799_, v_a_801_);
lean_inc(v_fst_792_);
lean_inc(v_fst_788_);
if (v_isShared_791_ == 0)
{
lean_ctor_set_tag(v___x_790_, 3);
lean_ctor_set(v___x_790_, 1, v_fst_792_);
v___x_807_ = v___x_790_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v_fst_788_);
lean_ctor_set(v_reuseFailAlloc_881_, 1, v_fst_792_);
v___x_807_ = v_reuseFailAlloc_881_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
lean_object* v___x_808_; uint8_t v___x_809_; 
v___x_808_ = l_Int_Internal_Linear_Expr_norm(v___x_807_);
lean_dec_ref(v___x_807_);
v___x_809_ = l_Int_Internal_Linear_Poly_isUnsatLe(v___x_808_);
if (v___x_809_ == 0)
{
uint8_t v___x_810_; 
v___x_810_ = l_Int_Internal_Linear_Poly_isValidLe(v___x_808_);
if (v___x_810_ == 0)
{
lean_del_object(v___x_795_);
lean_del_object(v___x_785_);
if (v___y_777_ == 0)
{
lean_del_object(v___x_803_);
v___y_660_ = v_fst_792_;
v___y_661_ = v___f_797_;
v___y_662_ = v_fst_788_;
v___y_663_ = v___x_805_;
v___y_664_ = v_snd_793_;
v___y_665_ = v___x_808_;
goto v___jp_659_;
}
else
{
lean_object* v___x_811_; uint8_t v___x_812_; 
lean_inc_ref(v___x_808_);
v___x_811_ = l_Int_Internal_Linear_Poly_toExpr(v___x_808_);
v___x_812_ = l_Int_Internal_Linear_instBEqExpr_beq(v___x_811_, v_fst_788_);
lean_dec_ref(v___x_811_);
if (v___x_812_ == 0)
{
lean_del_object(v___x_803_);
v___y_660_ = v_fst_792_;
v___y_661_ = v___f_797_;
v___y_662_ = v_fst_788_;
v___y_663_ = v___x_805_;
v___y_664_ = v_snd_793_;
v___y_665_ = v___x_808_;
goto v___jp_659_;
}
else
{
lean_object* v___x_813_; uint8_t v___x_814_; 
v___x_813_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__36, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__36_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__36);
v___x_814_ = l_Int_Internal_Linear_instBEqExpr_beq(v_fst_792_, v___x_813_);
if (v___x_814_ == 0)
{
lean_del_object(v___x_803_);
v___y_660_ = v_fst_792_;
v___y_661_ = v___f_797_;
v___y_662_ = v_fst_788_;
v___y_663_ = v___x_805_;
v___y_664_ = v_snd_793_;
v___y_665_ = v___x_808_;
goto v___jp_659_;
}
else
{
lean_object* v___x_815_; lean_object* v___x_817_; 
lean_dec_ref(v___x_808_);
lean_dec_ref(v___x_805_);
lean_dec_ref(v___f_797_);
lean_dec(v_snd_793_);
lean_dec(v_fst_792_);
lean_dec(v_fst_788_);
v___x_815_ = lean_box(0);
if (v_isShared_804_ == 0)
{
lean_ctor_set(v___x_803_, 0, v___x_815_);
v___x_817_ = v___x_803_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v___x_815_);
v___x_817_ = v_reuseFailAlloc_818_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
return v___x_817_;
}
}
}
}
}
else
{
lean_object* v___x_819_; 
lean_dec_ref(v___x_808_);
lean_del_object(v___x_803_);
lean_dec_ref(v___f_797_);
v___x_819_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(v_snd_793_, v_a_623_, v_a_624_, v_a_625_, v_a_626_);
if (lean_obj_tag(v___x_819_) == 0)
{
lean_object* v_a_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_841_; 
v_a_820_ = lean_ctor_get(v___x_819_, 0);
v_isSharedCheck_841_ = !lean_is_exclusive(v___x_819_);
if (v_isSharedCheck_841_ == 0)
{
v___x_822_ = v___x_819_;
v_isShared_823_ = v_isSharedCheck_841_;
goto v_resetjp_821_;
}
else
{
lean_inc(v_a_820_);
lean_dec(v___x_819_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_841_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_833_; 
v___x_824_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__39, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__39_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__39);
v___x_825_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__11, &l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__11_once, _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__11);
v___x_826_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_788_);
v___x_827_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_792_);
v___x_828_ = l_Lean_eagerReflBoolTrue;
v___x_829_ = l_Lean_mkApp4(v___x_825_, v_a_820_, v___x_826_, v___x_827_, v___x_828_);
v___x_830_ = l_Lean_mkPropEq(v___x_805_, v___x_824_);
v___x_831_ = l_Lean_Meta_mkExpectedPropHint(v___x_829_, v___x_830_);
if (v_isShared_796_ == 0)
{
lean_ctor_set(v___x_795_, 1, v___x_831_);
lean_ctor_set(v___x_795_, 0, v___x_824_);
v___x_833_ = v___x_795_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v___x_824_);
lean_ctor_set(v_reuseFailAlloc_840_, 1, v___x_831_);
v___x_833_ = v_reuseFailAlloc_840_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
lean_object* v___x_835_; 
if (v_isShared_786_ == 0)
{
lean_ctor_set(v___x_785_, 0, v___x_833_);
v___x_835_ = v___x_785_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v___x_833_);
v___x_835_ = v_reuseFailAlloc_839_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
lean_object* v___x_837_; 
if (v_isShared_823_ == 0)
{
lean_ctor_set(v___x_822_, 0, v___x_835_);
v___x_837_ = v___x_822_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v___x_835_);
v___x_837_ = v_reuseFailAlloc_838_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
return v___x_837_;
}
}
}
}
}
else
{
lean_object* v_a_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_849_; 
lean_dec_ref(v___x_805_);
lean_del_object(v___x_795_);
lean_dec(v_fst_792_);
lean_dec(v_fst_788_);
lean_del_object(v___x_785_);
v_a_842_ = lean_ctor_get(v___x_819_, 0);
v_isSharedCheck_849_ = !lean_is_exclusive(v___x_819_);
if (v_isSharedCheck_849_ == 0)
{
v___x_844_ = v___x_819_;
v_isShared_845_ = v_isSharedCheck_849_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_a_842_);
lean_dec(v___x_819_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_849_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v___x_847_; 
if (v_isShared_845_ == 0)
{
v___x_847_ = v___x_844_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v_a_842_);
v___x_847_ = v_reuseFailAlloc_848_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
return v___x_847_;
}
}
}
}
}
else
{
lean_object* v___x_850_; 
lean_dec_ref(v___x_808_);
lean_del_object(v___x_803_);
lean_dec_ref(v___f_797_);
v___x_850_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(v_snd_793_, v_a_623_, v_a_624_, v_a_625_, v_a_626_);
if (lean_obj_tag(v___x_850_) == 0)
{
lean_object* v_a_851_; lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_872_; 
v_a_851_ = lean_ctor_get(v___x_850_, 0);
v_isSharedCheck_872_ = !lean_is_exclusive(v___x_850_);
if (v_isSharedCheck_872_ == 0)
{
v___x_853_ = v___x_850_;
v_isShared_854_ = v_isSharedCheck_872_;
goto v_resetjp_852_;
}
else
{
lean_inc(v_a_851_);
lean_dec(v___x_850_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_872_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_864_; 
v___x_855_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__9, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__9_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__9);
v___x_856_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__14, &l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__14_once, _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__14);
v___x_857_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_788_);
v___x_858_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_792_);
v___x_859_ = l_Lean_eagerReflBoolTrue;
v___x_860_ = l_Lean_mkApp4(v___x_856_, v_a_851_, v___x_857_, v___x_858_, v___x_859_);
v___x_861_ = l_Lean_mkPropEq(v___x_805_, v___x_855_);
v___x_862_ = l_Lean_Meta_mkExpectedPropHint(v___x_860_, v___x_861_);
if (v_isShared_796_ == 0)
{
lean_ctor_set(v___x_795_, 1, v___x_862_);
lean_ctor_set(v___x_795_, 0, v___x_855_);
v___x_864_ = v___x_795_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v___x_855_);
lean_ctor_set(v_reuseFailAlloc_871_, 1, v___x_862_);
v___x_864_ = v_reuseFailAlloc_871_;
goto v_reusejp_863_;
}
v_reusejp_863_:
{
lean_object* v___x_866_; 
if (v_isShared_786_ == 0)
{
lean_ctor_set(v___x_785_, 0, v___x_864_);
v___x_866_ = v___x_785_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v___x_864_);
v___x_866_ = v_reuseFailAlloc_870_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
lean_object* v___x_868_; 
if (v_isShared_854_ == 0)
{
lean_ctor_set(v___x_853_, 0, v___x_866_);
v___x_868_ = v___x_853_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v___x_866_);
v___x_868_ = v_reuseFailAlloc_869_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
return v___x_868_;
}
}
}
}
}
else
{
lean_object* v_a_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_880_; 
lean_dec_ref(v___x_805_);
lean_del_object(v___x_795_);
lean_dec(v_fst_792_);
lean_dec(v_fst_788_);
lean_del_object(v___x_785_);
v_a_873_ = lean_ctor_get(v___x_850_, 0);
v_isSharedCheck_880_ = !lean_is_exclusive(v___x_850_);
if (v_isSharedCheck_880_ == 0)
{
v___x_875_ = v___x_850_;
v_isShared_876_ = v_isSharedCheck_880_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_a_873_);
lean_dec(v___x_850_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_880_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
lean_object* v___x_878_; 
if (v_isShared_876_ == 0)
{
v___x_878_ = v___x_875_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v_a_873_);
v___x_878_ = v_reuseFailAlloc_879_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
return v___x_878_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_883_; lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_890_; 
lean_dec(v_a_799_);
lean_dec_ref(v___f_797_);
lean_del_object(v___x_795_);
lean_dec(v_snd_793_);
lean_dec(v_fst_792_);
lean_del_object(v___x_790_);
lean_dec(v_fst_788_);
lean_del_object(v___x_785_);
v_a_883_ = lean_ctor_get(v___x_800_, 0);
v_isSharedCheck_890_ = !lean_is_exclusive(v___x_800_);
if (v_isSharedCheck_890_ == 0)
{
v___x_885_ = v___x_800_;
v_isShared_886_ = v_isSharedCheck_890_;
goto v_resetjp_884_;
}
else
{
lean_inc(v_a_883_);
lean_dec(v___x_800_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_890_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
lean_object* v___x_888_; 
if (v_isShared_886_ == 0)
{
v___x_888_ = v___x_885_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v_a_883_);
v___x_888_ = v_reuseFailAlloc_889_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
return v___x_888_;
}
}
}
}
else
{
lean_object* v_a_891_; lean_object* v___x_893_; uint8_t v_isShared_894_; uint8_t v_isSharedCheck_898_; 
lean_dec_ref(v___f_797_);
lean_del_object(v___x_795_);
lean_dec(v_snd_793_);
lean_dec(v_fst_792_);
lean_del_object(v___x_790_);
lean_dec(v_fst_788_);
lean_del_object(v___x_785_);
v_a_891_ = lean_ctor_get(v___x_798_, 0);
v_isSharedCheck_898_ = !lean_is_exclusive(v___x_798_);
if (v_isSharedCheck_898_ == 0)
{
v___x_893_ = v___x_798_;
v_isShared_894_ = v_isSharedCheck_898_;
goto v_resetjp_892_;
}
else
{
lean_inc(v_a_891_);
lean_dec(v___x_798_);
v___x_893_ = lean_box(0);
v_isShared_894_ = v_isSharedCheck_898_;
goto v_resetjp_892_;
}
v_resetjp_892_:
{
lean_object* v___x_896_; 
if (v_isShared_894_ == 0)
{
v___x_896_ = v___x_893_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v_a_891_);
v___x_896_ = v_reuseFailAlloc_897_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
return v___x_896_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_902_; lean_object* v___x_904_; 
lean_dec(v_a_779_);
v___x_902_ = lean_box(0);
if (v_isShared_782_ == 0)
{
lean_ctor_set(v___x_781_, 0, v___x_902_);
v___x_904_ = v___x_781_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v___x_902_);
v___x_904_ = v_reuseFailAlloc_905_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
return v___x_904_;
}
}
}
}
else
{
lean_object* v_a_907_; lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_914_; 
v_a_907_ = lean_ctor_get(v___x_778_, 0);
v_isSharedCheck_914_ = !lean_is_exclusive(v___x_778_);
if (v_isSharedCheck_914_ == 0)
{
v___x_909_ = v___x_778_;
v_isShared_910_ = v_isSharedCheck_914_;
goto v_resetjp_908_;
}
else
{
lean_inc(v_a_907_);
lean_dec(v___x_778_);
v___x_909_ = lean_box(0);
v_isShared_910_ = v_isSharedCheck_914_;
goto v_resetjp_908_;
}
v_resetjp_908_:
{
lean_object* v___x_912_; 
if (v_isShared_910_ == 0)
{
v___x_912_ = v___x_909_;
goto v_reusejp_911_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v_a_907_);
v___x_912_ = v_reuseFailAlloc_913_;
goto v_reusejp_911_;
}
v_reusejp_911_:
{
return v___x_912_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___boxed(lean_object* v_e_917_, lean_object* v_checkIfModified_918_, lean_object* v_a_919_, lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_, lean_object* v_a_923_){
_start:
{
uint8_t v_checkIfModified_boxed_924_; lean_object* v_res_925_; 
v_checkIfModified_boxed_924_ = lean_unbox(v_checkIfModified_918_);
v_res_925_ = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f(v_e_917_, v_checkIfModified_boxed_924_, v_a_919_, v_a_920_, v_a_921_, v_a_922_);
lean_dec(v_a_922_);
lean_dec_ref(v_a_921_);
lean_dec(v_a_920_);
lean_dec_ref(v_a_919_);
return v_res_925_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__3(void){
_start:
{
lean_object* v___x_931_; lean_object* v___x_932_; 
v___x_931_ = lean_box(0);
v___x_932_ = l_Lean_Level_succ___override(v___x_931_);
return v___x_932_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__4(void){
_start:
{
lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; 
v___x_933_ = lean_box(0);
v___x_934_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__3, &l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__3_once, _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__3);
v___x_935_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_935_, 0, v___x_934_);
lean_ctor_set(v___x_935_, 1, v___x_933_);
return v___x_935_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__5(void){
_start:
{
lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; 
v___x_936_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__4, &l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__4_once, _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__4);
v___x_937_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__2));
v___x_938_ = l_Lean_mkConst(v___x_937_, v___x_936_);
return v___x_938_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__6(void){
_start:
{
lean_object* v___x_939_; lean_object* v___x_940_; 
v___x_939_ = lean_box(0);
v___x_940_ = l_Lean_mkSort(v___x_939_);
return v___x_940_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__18(void){
_start:
{
lean_object* v___x_959_; lean_object* v___x_960_; 
v___x_959_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__31, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__31_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__31);
v___x_960_ = l_Lean_mkIntLit(v___x_959_);
return v___x_960_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__21(void){
_start:
{
lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_965_ = lean_box(0);
v___x_966_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__20));
v___x_967_ = l_Lean_mkConst(v___x_966_, v___x_965_);
return v___x_967_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__24(void){
_start:
{
lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; 
v___x_972_ = lean_box(0);
v___x_973_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__23));
v___x_974_ = l_Lean_mkConst(v___x_973_, v___x_972_);
return v___x_974_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__27(void){
_start:
{
lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; 
v___x_979_ = lean_box(0);
v___x_980_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__26));
v___x_981_ = l_Lean_mkConst(v___x_980_, v___x_979_);
return v___x_981_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__30(void){
_start:
{
lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; 
v___x_986_ = lean_box(0);
v___x_987_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__29));
v___x_988_ = l_Lean_mkConst(v___x_987_, v___x_986_);
return v___x_988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f(lean_object* v_e_989_, lean_object* v_a_990_, lean_object* v_a_991_, lean_object* v_a_992_, lean_object* v_a_993_){
_start:
{
lean_object* v_val_999_; lean_object* v_h_u2081_1000_; lean_object* v___y_1001_; lean_object* v___y_1002_; lean_object* v___y_1003_; lean_object* v___y_1004_; lean_object* v___x_1040_; lean_object* v___x_1041_; uint8_t v___x_1042_; 
v___x_1040_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__8));
v___x_1041_ = lean_unsigned_to_nat(1u);
v___x_1042_ = l_Lean_Expr_isAppOfArity(v_e_989_, v___x_1040_, v___x_1041_);
if (v___x_1042_ == 0)
{
uint8_t v___x_1043_; lean_object* v___x_1044_; 
v___x_1043_ = 1;
v___x_1044_ = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f(v_e_989_, v___x_1043_, v_a_990_, v_a_991_, v_a_992_, v_a_993_);
return v___x_1044_;
}
else
{
lean_object* v___x_1045_; lean_object* v___x_1046_; 
v___x_1045_ = l_Lean_Expr_appArg_x21(v_e_989_);
v___x_1046_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v___x_1045_, v_a_991_);
if (lean_obj_tag(v___x_1046_) == 0)
{
lean_object* v_a_1047_; lean_object* v___x_1048_; uint8_t v___x_1049_; 
v_a_1047_ = lean_ctor_get(v___x_1046_, 0);
lean_inc(v_a_1047_);
lean_dec_ref_known(v___x_1046_, 1);
v___x_1048_ = l_Lean_Expr_cleanupAnnotations(v_a_1047_);
v___x_1049_ = l_Lean_Expr_isApp(v___x_1048_);
if (v___x_1049_ == 0)
{
lean_dec_ref(v___x_1048_);
lean_dec_ref(v_e_989_);
goto v___jp_995_;
}
else
{
lean_object* v_arg_1050_; lean_object* v___x_1051_; uint8_t v___x_1052_; 
v_arg_1050_ = lean_ctor_get(v___x_1048_, 1);
lean_inc_ref(v_arg_1050_);
v___x_1051_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1048_);
v___x_1052_ = l_Lean_Expr_isApp(v___x_1051_);
if (v___x_1052_ == 0)
{
lean_dec_ref(v___x_1051_);
lean_dec_ref(v_arg_1050_);
lean_dec_ref(v_e_989_);
goto v___jp_995_;
}
else
{
lean_object* v_arg_1053_; lean_object* v___x_1054_; uint8_t v___x_1055_; 
v_arg_1053_ = lean_ctor_get(v___x_1051_, 1);
lean_inc_ref(v_arg_1053_);
v___x_1054_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1051_);
v___x_1055_ = l_Lean_Expr_isApp(v___x_1054_);
if (v___x_1055_ == 0)
{
lean_dec_ref(v___x_1054_);
lean_dec_ref(v_arg_1053_);
lean_dec_ref(v_arg_1050_);
lean_dec_ref(v_e_989_);
goto v___jp_995_;
}
else
{
lean_object* v___x_1056_; uint8_t v___x_1057_; 
v___x_1056_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1054_);
v___x_1057_ = l_Lean_Expr_isApp(v___x_1056_);
if (v___x_1057_ == 0)
{
lean_dec_ref(v___x_1056_);
lean_dec_ref(v_arg_1053_);
lean_dec_ref(v_arg_1050_);
lean_dec_ref(v_e_989_);
goto v___jp_995_;
}
else
{
lean_object* v_arg_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; uint8_t v___x_1061_; 
v_arg_1058_ = lean_ctor_get(v___x_1056_, 1);
lean_inc_ref(v_arg_1058_);
v___x_1059_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1056_);
v___x_1060_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__11));
v___x_1061_ = l_Lean_Expr_isConstOf(v___x_1059_, v___x_1060_);
if (v___x_1061_ == 0)
{
lean_object* v___x_1062_; uint8_t v___x_1063_; 
v___x_1062_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__14));
v___x_1063_ = l_Lean_Expr_isConstOf(v___x_1059_, v___x_1062_);
if (v___x_1063_ == 0)
{
lean_object* v___x_1064_; uint8_t v___x_1065_; 
v___x_1064_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__17));
v___x_1065_ = l_Lean_Expr_isConstOf(v___x_1059_, v___x_1064_);
if (v___x_1065_ == 0)
{
lean_object* v___x_1066_; uint8_t v___x_1067_; 
v___x_1066_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__17));
v___x_1067_ = l_Lean_Expr_isConstOf(v___x_1059_, v___x_1066_);
lean_dec_ref(v___x_1059_);
if (v___x_1067_ == 0)
{
lean_dec_ref(v_arg_1058_);
lean_dec_ref(v_arg_1053_);
lean_dec_ref(v_arg_1050_);
lean_dec_ref(v_e_989_);
goto v___jp_995_;
}
else
{
lean_object* v___x_1068_; 
v___x_1068_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_1058_, v_a_991_);
if (lean_obj_tag(v___x_1068_) == 0)
{
lean_object* v_a_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; uint8_t v___x_1072_; 
v_a_1069_ = lean_ctor_get(v___x_1068_, 0);
lean_inc(v_a_1069_);
lean_dec_ref_known(v___x_1068_, 1);
v___x_1070_ = l_Lean_Expr_cleanupAnnotations(v_a_1069_);
v___x_1071_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19));
v___x_1072_ = l_Lean_Expr_isConstOf(v___x_1070_, v___x_1071_);
lean_dec_ref(v___x_1070_);
if (v___x_1072_ == 0)
{
lean_dec_ref(v_arg_1053_);
lean_dec_ref(v_arg_1050_);
lean_dec_ref(v_e_989_);
goto v___jp_995_;
}
else
{
lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; 
v___x_1073_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__18, &l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__18_once, _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__18);
lean_inc_ref(v_arg_1050_);
v___x_1074_ = l_Lean_mkIntAdd(v_arg_1050_, v___x_1073_);
lean_inc_ref(v_arg_1053_);
v___x_1075_ = l_Lean_mkIntLE(v___x_1074_, v_arg_1053_);
v___x_1076_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__21, &l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__21_once, _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__21);
v___x_1077_ = l_Lean_mkAppB(v___x_1076_, v_arg_1053_, v_arg_1050_);
v_val_999_ = v___x_1075_;
v_h_u2081_1000_ = v___x_1077_;
v___y_1001_ = v_a_990_;
v___y_1002_ = v_a_991_;
v___y_1003_ = v_a_992_;
v___y_1004_ = v_a_993_;
goto v___jp_998_;
}
}
else
{
lean_object* v_a_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1085_; 
lean_dec_ref(v_arg_1053_);
lean_dec_ref(v_arg_1050_);
lean_dec_ref(v_e_989_);
v_a_1078_ = lean_ctor_get(v___x_1068_, 0);
v_isSharedCheck_1085_ = !lean_is_exclusive(v___x_1068_);
if (v_isSharedCheck_1085_ == 0)
{
v___x_1080_ = v___x_1068_;
v_isShared_1081_ = v_isSharedCheck_1085_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_a_1078_);
lean_dec(v___x_1068_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1085_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
lean_object* v___x_1083_; 
if (v_isShared_1081_ == 0)
{
v___x_1083_ = v___x_1080_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v_a_1078_);
v___x_1083_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
return v___x_1083_;
}
}
}
}
}
else
{
lean_object* v___x_1086_; 
lean_dec_ref(v___x_1059_);
v___x_1086_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_1058_, v_a_991_);
if (lean_obj_tag(v___x_1086_) == 0)
{
lean_object* v_a_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; uint8_t v___x_1090_; 
v_a_1087_ = lean_ctor_get(v___x_1086_, 0);
lean_inc(v_a_1087_);
lean_dec_ref_known(v___x_1086_, 1);
v___x_1088_ = l_Lean_Expr_cleanupAnnotations(v_a_1087_);
v___x_1089_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19));
v___x_1090_ = l_Lean_Expr_isConstOf(v___x_1088_, v___x_1089_);
lean_dec_ref(v___x_1088_);
if (v___x_1090_ == 0)
{
lean_dec_ref(v_arg_1053_);
lean_dec_ref(v_arg_1050_);
lean_dec_ref(v_e_989_);
goto v___jp_995_;
}
else
{
lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; 
v___x_1091_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__18, &l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__18_once, _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__18);
lean_inc_ref(v_arg_1053_);
v___x_1092_ = l_Lean_mkIntAdd(v_arg_1053_, v___x_1091_);
lean_inc_ref(v_arg_1050_);
v___x_1093_ = l_Lean_mkIntLE(v___x_1092_, v_arg_1050_);
v___x_1094_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__24, &l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__24_once, _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__24);
v___x_1095_ = l_Lean_mkAppB(v___x_1094_, v_arg_1053_, v_arg_1050_);
v_val_999_ = v___x_1093_;
v_h_u2081_1000_ = v___x_1095_;
v___y_1001_ = v_a_990_;
v___y_1002_ = v_a_991_;
v___y_1003_ = v_a_992_;
v___y_1004_ = v_a_993_;
goto v___jp_998_;
}
}
else
{
lean_object* v_a_1096_; lean_object* v___x_1098_; uint8_t v_isShared_1099_; uint8_t v_isSharedCheck_1103_; 
lean_dec_ref(v_arg_1053_);
lean_dec_ref(v_arg_1050_);
lean_dec_ref(v_e_989_);
v_a_1096_ = lean_ctor_get(v___x_1086_, 0);
v_isSharedCheck_1103_ = !lean_is_exclusive(v___x_1086_);
if (v_isSharedCheck_1103_ == 0)
{
v___x_1098_ = v___x_1086_;
v_isShared_1099_ = v_isSharedCheck_1103_;
goto v_resetjp_1097_;
}
else
{
lean_inc(v_a_1096_);
lean_dec(v___x_1086_);
v___x_1098_ = lean_box(0);
v_isShared_1099_ = v_isSharedCheck_1103_;
goto v_resetjp_1097_;
}
v_resetjp_1097_:
{
lean_object* v___x_1101_; 
if (v_isShared_1099_ == 0)
{
v___x_1101_ = v___x_1098_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v_a_1096_);
v___x_1101_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
return v___x_1101_;
}
}
}
}
}
else
{
lean_object* v___x_1104_; 
lean_dec_ref(v___x_1059_);
v___x_1104_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_1058_, v_a_991_);
if (lean_obj_tag(v___x_1104_) == 0)
{
lean_object* v_a_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; uint8_t v___x_1108_; 
v_a_1105_ = lean_ctor_get(v___x_1104_, 0);
lean_inc(v_a_1105_);
lean_dec_ref_known(v___x_1104_, 1);
v___x_1106_ = l_Lean_Expr_cleanupAnnotations(v_a_1105_);
v___x_1107_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19));
v___x_1108_ = l_Lean_Expr_isConstOf(v___x_1106_, v___x_1107_);
lean_dec_ref(v___x_1106_);
if (v___x_1108_ == 0)
{
lean_dec_ref(v_arg_1053_);
lean_dec_ref(v_arg_1050_);
lean_dec_ref(v_e_989_);
goto v___jp_995_;
}
else
{
lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; 
lean_inc_ref(v_arg_1053_);
lean_inc_ref(v_arg_1050_);
v___x_1109_ = l_Lean_mkIntLE(v_arg_1050_, v_arg_1053_);
v___x_1110_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__27, &l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__27_once, _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__27);
v___x_1111_ = l_Lean_mkAppB(v___x_1110_, v_arg_1053_, v_arg_1050_);
v_val_999_ = v___x_1109_;
v_h_u2081_1000_ = v___x_1111_;
v___y_1001_ = v_a_990_;
v___y_1002_ = v_a_991_;
v___y_1003_ = v_a_992_;
v___y_1004_ = v_a_993_;
goto v___jp_998_;
}
}
else
{
lean_object* v_a_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1119_; 
lean_dec_ref(v_arg_1053_);
lean_dec_ref(v_arg_1050_);
lean_dec_ref(v_e_989_);
v_a_1112_ = lean_ctor_get(v___x_1104_, 0);
v_isSharedCheck_1119_ = !lean_is_exclusive(v___x_1104_);
if (v_isSharedCheck_1119_ == 0)
{
v___x_1114_ = v___x_1104_;
v_isShared_1115_ = v_isSharedCheck_1119_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_a_1112_);
lean_dec(v___x_1104_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1119_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
lean_object* v___x_1117_; 
if (v_isShared_1115_ == 0)
{
v___x_1117_ = v___x_1114_;
goto v_reusejp_1116_;
}
else
{
lean_object* v_reuseFailAlloc_1118_; 
v_reuseFailAlloc_1118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1118_, 0, v_a_1112_);
v___x_1117_ = v_reuseFailAlloc_1118_;
goto v_reusejp_1116_;
}
v_reusejp_1116_:
{
return v___x_1117_;
}
}
}
}
}
else
{
lean_object* v___x_1120_; 
lean_dec_ref(v___x_1059_);
v___x_1120_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_1058_, v_a_991_);
if (lean_obj_tag(v___x_1120_) == 0)
{
lean_object* v_a_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; uint8_t v___x_1124_; 
v_a_1121_ = lean_ctor_get(v___x_1120_, 0);
lean_inc(v_a_1121_);
lean_dec_ref_known(v___x_1120_, 1);
v___x_1122_ = l_Lean_Expr_cleanupAnnotations(v_a_1121_);
v___x_1123_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19));
v___x_1124_ = l_Lean_Expr_isConstOf(v___x_1122_, v___x_1123_);
lean_dec_ref(v___x_1122_);
if (v___x_1124_ == 0)
{
lean_dec_ref(v_arg_1053_);
lean_dec_ref(v_arg_1050_);
lean_dec_ref(v_e_989_);
goto v___jp_995_;
}
else
{
lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; 
lean_inc_ref(v_arg_1050_);
lean_inc_ref(v_arg_1053_);
v___x_1125_ = l_Lean_mkIntLE(v_arg_1053_, v_arg_1050_);
v___x_1126_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__30, &l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__30_once, _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__30);
v___x_1127_ = l_Lean_mkAppB(v___x_1126_, v_arg_1053_, v_arg_1050_);
v_val_999_ = v___x_1125_;
v_h_u2081_1000_ = v___x_1127_;
v___y_1001_ = v_a_990_;
v___y_1002_ = v_a_991_;
v___y_1003_ = v_a_992_;
v___y_1004_ = v_a_993_;
goto v___jp_998_;
}
}
else
{
lean_object* v_a_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1135_; 
lean_dec_ref(v_arg_1053_);
lean_dec_ref(v_arg_1050_);
lean_dec_ref(v_e_989_);
v_a_1128_ = lean_ctor_get(v___x_1120_, 0);
v_isSharedCheck_1135_ = !lean_is_exclusive(v___x_1120_);
if (v_isSharedCheck_1135_ == 0)
{
v___x_1130_ = v___x_1120_;
v_isShared_1131_ = v_isSharedCheck_1135_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_a_1128_);
lean_dec(v___x_1120_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1135_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
lean_object* v___x_1133_; 
if (v_isShared_1131_ == 0)
{
v___x_1133_ = v___x_1130_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v_a_1128_);
v___x_1133_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
return v___x_1133_;
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
lean_object* v_a_1136_; lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1143_; 
lean_dec_ref(v_e_989_);
v_a_1136_ = lean_ctor_get(v___x_1046_, 0);
v_isSharedCheck_1143_ = !lean_is_exclusive(v___x_1046_);
if (v_isSharedCheck_1143_ == 0)
{
v___x_1138_ = v___x_1046_;
v_isShared_1139_ = v_isSharedCheck_1143_;
goto v_resetjp_1137_;
}
else
{
lean_inc(v_a_1136_);
lean_dec(v___x_1046_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1143_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
lean_object* v___x_1141_; 
if (v_isShared_1139_ == 0)
{
v___x_1141_ = v___x_1138_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1142_; 
v_reuseFailAlloc_1142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1142_, 0, v_a_1136_);
v___x_1141_ = v_reuseFailAlloc_1142_;
goto v_reusejp_1140_;
}
v_reusejp_1140_:
{
return v___x_1141_;
}
}
}
}
v___jp_995_:
{
lean_object* v___x_996_; lean_object* v___x_997_; 
v___x_996_ = lean_box(0);
v___x_997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_997_, 0, v___x_996_);
return v___x_997_;
}
v___jp_998_:
{
uint8_t v___x_1005_; lean_object* v___x_1006_; 
v___x_1005_ = 0;
lean_inc_ref(v_val_999_);
v___x_1006_ = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f(v_val_999_, v___x_1005_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_);
if (lean_obj_tag(v___x_1006_) == 0)
{
lean_object* v_a_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1039_; 
v_a_1007_ = lean_ctor_get(v___x_1006_, 0);
v_isSharedCheck_1039_ = !lean_is_exclusive(v___x_1006_);
if (v_isSharedCheck_1039_ == 0)
{
v___x_1009_ = v___x_1006_;
v_isShared_1010_ = v_isSharedCheck_1039_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_a_1007_);
lean_dec(v___x_1006_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1039_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
if (lean_obj_tag(v_a_1007_) == 1)
{
lean_object* v_val_1011_; lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1033_; 
v_val_1011_ = lean_ctor_get(v_a_1007_, 0);
v_isSharedCheck_1033_ = !lean_is_exclusive(v_a_1007_);
if (v_isSharedCheck_1033_ == 0)
{
v___x_1013_ = v_a_1007_;
v_isShared_1014_ = v_isSharedCheck_1033_;
goto v_resetjp_1012_;
}
else
{
lean_inc(v_val_1011_);
lean_dec(v_a_1007_);
v___x_1013_ = lean_box(0);
v_isShared_1014_ = v_isSharedCheck_1033_;
goto v_resetjp_1012_;
}
v_resetjp_1012_:
{
lean_object* v_fst_1015_; lean_object* v_snd_1016_; lean_object* v___x_1018_; uint8_t v_isShared_1019_; uint8_t v_isSharedCheck_1032_; 
v_fst_1015_ = lean_ctor_get(v_val_1011_, 0);
v_snd_1016_ = lean_ctor_get(v_val_1011_, 1);
v_isSharedCheck_1032_ = !lean_is_exclusive(v_val_1011_);
if (v_isSharedCheck_1032_ == 0)
{
v___x_1018_ = v_val_1011_;
v_isShared_1019_ = v_isSharedCheck_1032_;
goto v_resetjp_1017_;
}
else
{
lean_inc(v_snd_1016_);
lean_inc(v_fst_1015_);
lean_dec(v_val_1011_);
v___x_1018_ = lean_box(0);
v_isShared_1019_ = v_isSharedCheck_1032_;
goto v_resetjp_1017_;
}
v_resetjp_1017_:
{
lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1024_; 
v___x_1020_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__5, &l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__5_once, _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__5);
v___x_1021_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__6, &l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__6_once, _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__6);
lean_inc(v_fst_1015_);
v___x_1022_ = l_Lean_mkApp6(v___x_1020_, v___x_1021_, v_e_989_, v_val_999_, v_fst_1015_, v_h_u2081_1000_, v_snd_1016_);
if (v_isShared_1019_ == 0)
{
lean_ctor_set(v___x_1018_, 1, v___x_1022_);
v___x_1024_ = v___x_1018_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1031_; 
v_reuseFailAlloc_1031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1031_, 0, v_fst_1015_);
lean_ctor_set(v_reuseFailAlloc_1031_, 1, v___x_1022_);
v___x_1024_ = v_reuseFailAlloc_1031_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
lean_object* v___x_1026_; 
if (v_isShared_1014_ == 0)
{
lean_ctor_set(v___x_1013_, 0, v___x_1024_);
v___x_1026_ = v___x_1013_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v___x_1024_);
v___x_1026_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
lean_object* v___x_1028_; 
if (v_isShared_1010_ == 0)
{
lean_ctor_set(v___x_1009_, 0, v___x_1026_);
v___x_1028_ = v___x_1009_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v___x_1026_);
v___x_1028_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
return v___x_1028_;
}
}
}
}
}
}
else
{
lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1037_; 
lean_dec(v_a_1007_);
lean_dec_ref(v_e_989_);
v___x_1034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1034_, 0, v_val_999_);
lean_ctor_set(v___x_1034_, 1, v_h_u2081_1000_);
v___x_1035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1035_, 0, v___x_1034_);
if (v_isShared_1010_ == 0)
{
lean_ctor_set(v___x_1009_, 0, v___x_1035_);
v___x_1037_ = v___x_1009_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v___x_1035_);
v___x_1037_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
return v___x_1037_;
}
}
}
}
else
{
lean_dec_ref(v_h_u2081_1000_);
lean_dec_ref(v_val_999_);
lean_dec_ref(v_e_989_);
return v___x_1006_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___boxed(lean_object* v_e_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_){
_start:
{
lean_object* v_res_1150_; 
v_res_1150_ = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f(v_e_1144_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_);
lean_dec(v_a_1148_);
lean_dec_ref(v_a_1147_);
lean_dec(v_a_1146_);
lean_dec_ref(v_a_1145_);
return v_res_1150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lam__0(lean_object* v_snd_1151_, lean_object* v_x_1152_){
_start:
{
lean_object* v___x_1153_; lean_object* v___x_1154_; 
v___x_1153_ = l_Lean_instInhabitedExpr;
v___x_1154_ = lean_array_get_borrowed(v___x_1153_, v_snd_1151_, v_x_1152_);
lean_inc(v___x_1154_);
return v___x_1154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lam__0___boxed(lean_object* v_snd_1155_, lean_object* v_x_1156_){
_start:
{
lean_object* v_res_1157_; 
v_res_1157_ = l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lam__0(v_snd_1155_, v_x_1156_);
lean_dec(v_x_1156_);
lean_dec_ref(v_snd_1155_);
return v_res_1157_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__2(void){
_start:
{
lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; 
v___x_1164_ = lean_box(0);
v___x_1165_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__1));
v___x_1166_ = l_Lean_mkConst(v___x_1165_, v___x_1164_);
return v___x_1166_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__5(void){
_start:
{
lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; 
v___x_1173_ = lean_box(0);
v___x_1174_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__4));
v___x_1175_ = l_Lean_mkConst(v___x_1174_, v___x_1173_);
return v___x_1175_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__8(void){
_start:
{
lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; 
v___x_1182_ = lean_box(0);
v___x_1183_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__7));
v___x_1184_ = l_Lean_mkConst(v___x_1183_, v___x_1182_);
return v___x_1184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f(lean_object* v_e_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_){
_start:
{
lean_object* v___y_1192_; lean_object* v___y_1193_; lean_object* v_h_1194_; lean_object* v___y_1201_; lean_object* v___y_1202_; lean_object* v___y_1203_; lean_object* v___y_1204_; lean_object* v___y_1205_; lean_object* v___y_1206_; lean_object* v___y_1207_; lean_object* v___y_1208_; lean_object* v___y_1209_; lean_object* v___x_1212_; 
v___x_1212_ = l_Lean_Meta_Simp_Arith_Int_dvdCnstr_x3f(v_e_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_);
if (lean_obj_tag(v___x_1212_) == 0)
{
lean_object* v_a_1213_; lean_object* v___x_1215_; uint8_t v_isShared_1216_; uint8_t v_isSharedCheck_1379_; 
v_a_1213_ = lean_ctor_get(v___x_1212_, 0);
v_isSharedCheck_1379_ = !lean_is_exclusive(v___x_1212_);
if (v_isSharedCheck_1379_ == 0)
{
v___x_1215_ = v___x_1212_;
v_isShared_1216_ = v_isSharedCheck_1379_;
goto v_resetjp_1214_;
}
else
{
lean_inc(v_a_1213_);
lean_dec(v___x_1212_);
v___x_1215_ = lean_box(0);
v_isShared_1216_ = v_isSharedCheck_1379_;
goto v_resetjp_1214_;
}
v_resetjp_1214_:
{
if (lean_obj_tag(v_a_1213_) == 1)
{
lean_object* v_val_1217_; lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1374_; 
v_val_1217_ = lean_ctor_get(v_a_1213_, 0);
v_isSharedCheck_1374_ = !lean_is_exclusive(v_a_1213_);
if (v_isSharedCheck_1374_ == 0)
{
v___x_1219_ = v_a_1213_;
v_isShared_1220_ = v_isSharedCheck_1374_;
goto v_resetjp_1218_;
}
else
{
lean_inc(v_val_1217_);
lean_dec(v_a_1213_);
v___x_1219_ = lean_box(0);
v_isShared_1220_ = v_isSharedCheck_1374_;
goto v_resetjp_1218_;
}
v_resetjp_1218_:
{
lean_object* v_snd_1221_; lean_object* v_fst_1222_; lean_object* v_fst_1223_; lean_object* v_snd_1224_; lean_object* v___x_1226_; uint8_t v_isShared_1227_; uint8_t v_isSharedCheck_1373_; 
v_snd_1221_ = lean_ctor_get(v_val_1217_, 1);
lean_inc(v_snd_1221_);
v_fst_1222_ = lean_ctor_get(v_val_1217_, 0);
lean_inc(v_fst_1222_);
lean_dec(v_val_1217_);
v_fst_1223_ = lean_ctor_get(v_snd_1221_, 0);
v_snd_1224_ = lean_ctor_get(v_snd_1221_, 1);
v_isSharedCheck_1373_ = !lean_is_exclusive(v_snd_1221_);
if (v_isSharedCheck_1373_ == 0)
{
v___x_1226_ = v_snd_1221_;
v_isShared_1227_ = v_isSharedCheck_1373_;
goto v_resetjp_1225_;
}
else
{
lean_inc(v_snd_1224_);
lean_inc(v_fst_1223_);
lean_dec(v_snd_1221_);
v___x_1226_ = lean_box(0);
v_isShared_1227_ = v_isSharedCheck_1373_;
goto v_resetjp_1225_;
}
v_resetjp_1225_:
{
lean_object* v___x_1228_; lean_object* v___y_1230_; lean_object* v___y_1231_; lean_object* v___y_1232_; lean_object* v___y_1233_; lean_object* v___y_1234_; lean_object* v___y_1235_; uint8_t v___x_1277_; 
v___x_1228_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6);
v___x_1277_ = lean_int_dec_eq(v_fst_1222_, v___x_1228_);
if (v___x_1277_ == 0)
{
lean_object* v___f_1278_; lean_object* v___x_1279_; 
lean_del_object(v___x_1215_);
lean_inc(v_snd_1224_);
v___f_1278_ = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1278_, 0, v_snd_1224_);
lean_inc(v_fst_1223_);
lean_inc_ref(v___f_1278_);
v___x_1279_ = l_Int_Internal_Linear_Expr_denoteExpr___redArg(v___f_1278_, v_fst_1223_);
if (lean_obj_tag(v___x_1279_) == 0)
{
lean_object* v_a_1280_; lean_object* v___x_1282_; uint8_t v_isShared_1283_; uint8_t v_isSharedCheck_1360_; 
v_a_1280_ = lean_ctor_get(v___x_1279_, 0);
v_isSharedCheck_1360_ = !lean_is_exclusive(v___x_1279_);
if (v_isSharedCheck_1360_ == 0)
{
v___x_1282_ = v___x_1279_;
v_isShared_1283_ = v_isSharedCheck_1360_;
goto v_resetjp_1281_;
}
else
{
lean_inc(v_a_1280_);
lean_dec(v___x_1279_);
v___x_1282_ = lean_box(0);
v_isShared_1283_ = v_isSharedCheck_1360_;
goto v_resetjp_1281_;
}
v_resetjp_1281_:
{
lean_object* v___y_1285_; uint8_t v___x_1350_; 
v___x_1350_ = lean_int_dec_le(v___x_1228_, v_fst_1222_);
if (v___x_1350_ == 0)
{
lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; 
v___x_1351_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18);
v___x_1352_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20);
v___x_1353_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23);
v___x_1354_ = lean_int_neg(v_fst_1222_);
v___x_1355_ = l_Int_toNat(v___x_1354_);
lean_dec(v___x_1354_);
v___x_1356_ = l_Lean_instToExprInt_mkNat(v___x_1355_);
v___x_1357_ = l_Lean_mkApp3(v___x_1351_, v___x_1352_, v___x_1353_, v___x_1356_);
v___y_1285_ = v___x_1357_;
goto v___jp_1284_;
}
else
{
lean_object* v___x_1358_; lean_object* v___x_1359_; 
v___x_1358_ = l_Int_toNat(v_fst_1222_);
v___x_1359_ = l_Lean_instToExprInt_mkNat(v___x_1358_);
v___y_1285_ = v___x_1359_;
goto v___jp_1284_;
}
v___jp_1284_:
{
lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; uint8_t v___x_1291_; 
lean_inc_ref(v___y_1285_);
v___x_1286_ = l_Lean_mkIntDvd(v___y_1285_, v_a_1280_);
v___x_1287_ = l_Int_Internal_Linear_Expr_norm(v_fst_1223_);
lean_inc(v_fst_1222_);
v___x_1288_ = l_Int_Internal_Linear_Poly_gcdCoeffs(v___x_1287_, v_fst_1222_);
v___x_1289_ = l_Int_Internal_Linear_Poly_getConst(v___x_1287_);
v___x_1290_ = lean_int_emod(v___x_1289_, v___x_1288_);
lean_dec(v___x_1289_);
v___x_1291_ = lean_int_dec_eq(v___x_1290_, v___x_1228_);
lean_dec(v___x_1290_);
if (v___x_1291_ == 0)
{
lean_object* v___x_1292_; 
lean_dec(v___x_1288_);
lean_dec_ref(v___x_1287_);
lean_del_object(v___x_1282_);
lean_dec_ref(v___f_1278_);
lean_dec(v_fst_1222_);
v___x_1292_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(v_snd_1224_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_);
if (lean_obj_tag(v___x_1292_) == 0)
{
lean_object* v_a_1293_; lean_object* v___x_1295_; uint8_t v_isShared_1296_; uint8_t v_isSharedCheck_1313_; 
v_a_1293_ = lean_ctor_get(v___x_1292_, 0);
v_isSharedCheck_1313_ = !lean_is_exclusive(v___x_1292_);
if (v_isSharedCheck_1313_ == 0)
{
v___x_1295_ = v___x_1292_;
v_isShared_1296_ = v_isSharedCheck_1313_;
goto v_resetjp_1294_;
}
else
{
lean_inc(v_a_1293_);
lean_dec(v___x_1292_);
v___x_1295_ = lean_box(0);
v_isShared_1296_ = v_isSharedCheck_1313_;
goto v_resetjp_1294_;
}
v_resetjp_1294_:
{
lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1305_; 
v___x_1297_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__9, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__9_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__9);
v___x_1298_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__8, &l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__8_once, _init_l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__8);
v___x_1299_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_1223_);
v___x_1300_ = l_Lean_eagerReflBoolTrue;
v___x_1301_ = l_Lean_mkApp4(v___x_1298_, v_a_1293_, v___y_1285_, v___x_1299_, v___x_1300_);
v___x_1302_ = l_Lean_mkPropEq(v___x_1286_, v___x_1297_);
v___x_1303_ = l_Lean_Meta_mkExpectedPropHint(v___x_1301_, v___x_1302_);
if (v_isShared_1227_ == 0)
{
lean_ctor_set(v___x_1226_, 1, v___x_1303_);
lean_ctor_set(v___x_1226_, 0, v___x_1297_);
v___x_1305_ = v___x_1226_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v___x_1297_);
lean_ctor_set(v_reuseFailAlloc_1312_, 1, v___x_1303_);
v___x_1305_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
lean_object* v___x_1307_; 
if (v_isShared_1220_ == 0)
{
lean_ctor_set(v___x_1219_, 0, v___x_1305_);
v___x_1307_ = v___x_1219_;
goto v_reusejp_1306_;
}
else
{
lean_object* v_reuseFailAlloc_1311_; 
v_reuseFailAlloc_1311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1311_, 0, v___x_1305_);
v___x_1307_ = v_reuseFailAlloc_1311_;
goto v_reusejp_1306_;
}
v_reusejp_1306_:
{
lean_object* v___x_1309_; 
if (v_isShared_1296_ == 0)
{
lean_ctor_set(v___x_1295_, 0, v___x_1307_);
v___x_1309_ = v___x_1295_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v___x_1307_);
v___x_1309_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
return v___x_1309_;
}
}
}
}
}
else
{
lean_object* v_a_1314_; lean_object* v___x_1316_; uint8_t v_isShared_1317_; uint8_t v_isSharedCheck_1321_; 
lean_dec_ref(v___x_1286_);
lean_dec_ref(v___y_1285_);
lean_del_object(v___x_1226_);
lean_dec(v_fst_1223_);
lean_del_object(v___x_1219_);
v_a_1314_ = lean_ctor_get(v___x_1292_, 0);
v_isSharedCheck_1321_ = !lean_is_exclusive(v___x_1292_);
if (v_isSharedCheck_1321_ == 0)
{
v___x_1316_ = v___x_1292_;
v_isShared_1317_ = v_isSharedCheck_1321_;
goto v_resetjp_1315_;
}
else
{
lean_inc(v_a_1314_);
lean_dec(v___x_1292_);
v___x_1316_ = lean_box(0);
v_isShared_1317_ = v_isSharedCheck_1321_;
goto v_resetjp_1315_;
}
v_resetjp_1315_:
{
lean_object* v___x_1319_; 
if (v_isShared_1317_ == 0)
{
v___x_1319_ = v___x_1316_;
goto v_reusejp_1318_;
}
else
{
lean_object* v_reuseFailAlloc_1320_; 
v_reuseFailAlloc_1320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1320_, 0, v_a_1314_);
v___x_1319_ = v_reuseFailAlloc_1320_;
goto v_reusejp_1318_;
}
v_reusejp_1318_:
{
return v___x_1319_;
}
}
}
}
else
{
lean_object* v___x_1322_; lean_object* v___x_1323_; uint8_t v___x_1324_; 
lean_del_object(v___x_1226_);
lean_del_object(v___x_1219_);
v___x_1322_ = l_Int_Internal_Linear_Poly_div(v___x_1288_, v___x_1287_);
lean_inc_ref(v___x_1322_);
v___x_1323_ = l_Int_Internal_Linear_Poly_toExpr(v___x_1322_);
v___x_1324_ = l_Int_Internal_Linear_instBEqExpr_beq(v_fst_1223_, v___x_1323_);
lean_dec_ref(v___x_1323_);
if (v___x_1324_ == 0)
{
lean_object* v___x_1325_; 
lean_del_object(v___x_1282_);
lean_inc_ref(v___x_1322_);
v___x_1325_ = l_Int_Internal_Linear_Poly_denoteExpr___redArg(v___f_1278_, v___x_1322_);
if (lean_obj_tag(v___x_1325_) == 0)
{
lean_object* v_a_1326_; lean_object* v___x_1327_; uint8_t v___x_1328_; 
v_a_1326_ = lean_ctor_get(v___x_1325_, 0);
lean_inc(v_a_1326_);
lean_dec_ref_known(v___x_1325_, 1);
v___x_1327_ = lean_int_ediv(v_fst_1222_, v___x_1288_);
lean_dec(v_fst_1222_);
v___x_1328_ = lean_int_dec_le(v___x_1228_, v___x_1327_);
if (v___x_1328_ == 0)
{
lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; 
v___x_1329_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18);
v___x_1330_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20);
v___x_1331_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23);
v___x_1332_ = lean_int_neg(v___x_1327_);
lean_dec(v___x_1327_);
v___x_1333_ = l_Int_toNat(v___x_1332_);
lean_dec(v___x_1332_);
v___x_1334_ = l_Lean_instToExprInt_mkNat(v___x_1333_);
v___x_1335_ = l_Lean_mkApp3(v___x_1329_, v___x_1330_, v___x_1331_, v___x_1334_);
v___y_1230_ = v_a_1326_;
v___y_1231_ = v___x_1288_;
v___y_1232_ = v___x_1322_;
v___y_1233_ = v___y_1285_;
v___y_1234_ = v___x_1286_;
v___y_1235_ = v___x_1335_;
goto v___jp_1229_;
}
else
{
lean_object* v___x_1336_; lean_object* v___x_1337_; 
v___x_1336_ = l_Int_toNat(v___x_1327_);
lean_dec(v___x_1327_);
v___x_1337_ = l_Lean_instToExprInt_mkNat(v___x_1336_);
v___y_1230_ = v_a_1326_;
v___y_1231_ = v___x_1288_;
v___y_1232_ = v___x_1322_;
v___y_1233_ = v___y_1285_;
v___y_1234_ = v___x_1286_;
v___y_1235_ = v___x_1337_;
goto v___jp_1229_;
}
}
else
{
lean_object* v_a_1338_; lean_object* v___x_1340_; uint8_t v_isShared_1341_; uint8_t v_isSharedCheck_1345_; 
lean_dec_ref(v___x_1322_);
lean_dec(v___x_1288_);
lean_dec_ref(v___x_1286_);
lean_dec_ref(v___y_1285_);
lean_dec(v_snd_1224_);
lean_dec(v_fst_1223_);
lean_dec(v_fst_1222_);
v_a_1338_ = lean_ctor_get(v___x_1325_, 0);
v_isSharedCheck_1345_ = !lean_is_exclusive(v___x_1325_);
if (v_isSharedCheck_1345_ == 0)
{
v___x_1340_ = v___x_1325_;
v_isShared_1341_ = v_isSharedCheck_1345_;
goto v_resetjp_1339_;
}
else
{
lean_inc(v_a_1338_);
lean_dec(v___x_1325_);
v___x_1340_ = lean_box(0);
v_isShared_1341_ = v_isSharedCheck_1345_;
goto v_resetjp_1339_;
}
v_resetjp_1339_:
{
lean_object* v___x_1343_; 
if (v_isShared_1341_ == 0)
{
v___x_1343_ = v___x_1340_;
goto v_reusejp_1342_;
}
else
{
lean_object* v_reuseFailAlloc_1344_; 
v_reuseFailAlloc_1344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1344_, 0, v_a_1338_);
v___x_1343_ = v_reuseFailAlloc_1344_;
goto v_reusejp_1342_;
}
v_reusejp_1342_:
{
return v___x_1343_;
}
}
}
}
else
{
lean_object* v___x_1346_; lean_object* v___x_1348_; 
lean_dec_ref(v___x_1322_);
lean_dec(v___x_1288_);
lean_dec_ref(v___x_1286_);
lean_dec_ref(v___y_1285_);
lean_dec_ref(v___f_1278_);
lean_dec(v_snd_1224_);
lean_dec(v_fst_1223_);
lean_dec(v_fst_1222_);
v___x_1346_ = lean_box(0);
if (v_isShared_1283_ == 0)
{
lean_ctor_set(v___x_1282_, 0, v___x_1346_);
v___x_1348_ = v___x_1282_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v___x_1346_);
v___x_1348_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
return v___x_1348_;
}
}
}
}
}
}
else
{
lean_object* v_a_1361_; lean_object* v___x_1363_; uint8_t v_isShared_1364_; uint8_t v_isSharedCheck_1368_; 
lean_dec_ref(v___f_1278_);
lean_del_object(v___x_1226_);
lean_dec(v_snd_1224_);
lean_dec(v_fst_1223_);
lean_dec(v_fst_1222_);
lean_del_object(v___x_1219_);
v_a_1361_ = lean_ctor_get(v___x_1279_, 0);
v_isSharedCheck_1368_ = !lean_is_exclusive(v___x_1279_);
if (v_isSharedCheck_1368_ == 0)
{
v___x_1363_ = v___x_1279_;
v_isShared_1364_ = v_isSharedCheck_1368_;
goto v_resetjp_1362_;
}
else
{
lean_inc(v_a_1361_);
lean_dec(v___x_1279_);
v___x_1363_ = lean_box(0);
v_isShared_1364_ = v_isSharedCheck_1368_;
goto v_resetjp_1362_;
}
v_resetjp_1362_:
{
lean_object* v___x_1366_; 
if (v_isShared_1364_ == 0)
{
v___x_1366_ = v___x_1363_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v_a_1361_);
v___x_1366_ = v_reuseFailAlloc_1367_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
return v___x_1366_;
}
}
}
}
else
{
lean_object* v___x_1369_; lean_object* v___x_1371_; 
lean_del_object(v___x_1226_);
lean_dec(v_snd_1224_);
lean_dec(v_fst_1223_);
lean_dec(v_fst_1222_);
lean_del_object(v___x_1219_);
v___x_1369_ = lean_box(0);
if (v_isShared_1216_ == 0)
{
lean_ctor_set(v___x_1215_, 0, v___x_1369_);
v___x_1371_ = v___x_1215_;
goto v_reusejp_1370_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v___x_1369_);
v___x_1371_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1370_;
}
v_reusejp_1370_:
{
return v___x_1371_;
}
}
v___jp_1229_:
{
lean_object* v___x_1236_; lean_object* v___x_1237_; uint8_t v___x_1238_; 
lean_inc_ref(v___y_1235_);
v___x_1236_ = l_Lean_mkIntDvd(v___y_1235_, v___y_1230_);
v___x_1237_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__31, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__31_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__31);
v___x_1238_ = lean_int_dec_eq(v___y_1231_, v___x_1237_);
if (v___x_1238_ == 0)
{
lean_object* v___x_1239_; 
v___x_1239_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(v_snd_1224_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_);
if (lean_obj_tag(v___x_1239_) == 0)
{
lean_object* v_a_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; uint8_t v___x_1244_; 
v_a_1240_ = lean_ctor_get(v___x_1239_, 0);
lean_inc(v_a_1240_);
lean_dec_ref_known(v___x_1239_, 1);
v___x_1241_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__2, &l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__2_once, _init_l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__2);
v___x_1242_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_1223_);
v___x_1243_ = l_Lean_Meta_Simp_Arith_Int_ofPoly(v___y_1232_);
v___x_1244_ = lean_int_dec_le(v___x_1228_, v___y_1231_);
if (v___x_1244_ == 0)
{
lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; 
v___x_1245_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18);
v___x_1246_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20);
v___x_1247_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23);
v___x_1248_ = lean_int_neg(v___y_1231_);
lean_dec(v___y_1231_);
v___x_1249_ = l_Int_toNat(v___x_1248_);
lean_dec(v___x_1248_);
v___x_1250_ = l_Lean_instToExprInt_mkNat(v___x_1249_);
v___x_1251_ = l_Lean_mkApp3(v___x_1245_, v___x_1246_, v___x_1247_, v___x_1250_);
v___y_1201_ = v___y_1235_;
v___y_1202_ = v___x_1242_;
v___y_1203_ = v___y_1233_;
v___y_1204_ = v___x_1241_;
v___y_1205_ = v___x_1236_;
v___y_1206_ = v___y_1234_;
v___y_1207_ = v_a_1240_;
v___y_1208_ = v___x_1243_;
v___y_1209_ = v___x_1251_;
goto v___jp_1200_;
}
else
{
lean_object* v___x_1252_; lean_object* v___x_1253_; 
v___x_1252_ = l_Int_toNat(v___y_1231_);
lean_dec(v___y_1231_);
v___x_1253_ = l_Lean_instToExprInt_mkNat(v___x_1252_);
v___y_1201_ = v___y_1235_;
v___y_1202_ = v___x_1242_;
v___y_1203_ = v___y_1233_;
v___y_1204_ = v___x_1241_;
v___y_1205_ = v___x_1236_;
v___y_1206_ = v___y_1234_;
v___y_1207_ = v_a_1240_;
v___y_1208_ = v___x_1243_;
v___y_1209_ = v___x_1253_;
goto v___jp_1200_;
}
}
else
{
lean_object* v_a_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1261_; 
lean_dec_ref(v___x_1236_);
lean_dec_ref(v___y_1235_);
lean_dec_ref(v___y_1234_);
lean_dec_ref(v___y_1233_);
lean_dec_ref(v___y_1232_);
lean_dec(v___y_1231_);
lean_dec(v_fst_1223_);
v_a_1254_ = lean_ctor_get(v___x_1239_, 0);
v_isSharedCheck_1261_ = !lean_is_exclusive(v___x_1239_);
if (v_isSharedCheck_1261_ == 0)
{
v___x_1256_ = v___x_1239_;
v_isShared_1257_ = v_isSharedCheck_1261_;
goto v_resetjp_1255_;
}
else
{
lean_inc(v_a_1254_);
lean_dec(v___x_1239_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1261_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
lean_object* v___x_1259_; 
if (v_isShared_1257_ == 0)
{
v___x_1259_ = v___x_1256_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v_a_1254_);
v___x_1259_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
return v___x_1259_;
}
}
}
}
else
{
lean_object* v___x_1262_; 
lean_dec_ref(v___y_1235_);
lean_dec(v___y_1231_);
v___x_1262_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(v_snd_1224_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_);
if (lean_obj_tag(v___x_1262_) == 0)
{
lean_object* v_a_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; 
v_a_1263_ = lean_ctor_get(v___x_1262_, 0);
lean_inc(v_a_1263_);
lean_dec_ref_known(v___x_1262_, 1);
v___x_1264_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__5, &l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__5_once, _init_l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__5);
v___x_1265_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_1223_);
v___x_1266_ = l_Lean_Meta_Simp_Arith_Int_ofPoly(v___y_1232_);
v___x_1267_ = l_Lean_eagerReflBoolTrue;
v___x_1268_ = l_Lean_mkApp5(v___x_1264_, v_a_1263_, v___y_1233_, v___x_1265_, v___x_1266_, v___x_1267_);
v___y_1192_ = v___x_1236_;
v___y_1193_ = v___y_1234_;
v_h_1194_ = v___x_1268_;
goto v___jp_1191_;
}
else
{
lean_object* v_a_1269_; lean_object* v___x_1271_; uint8_t v_isShared_1272_; uint8_t v_isSharedCheck_1276_; 
lean_dec_ref(v___x_1236_);
lean_dec_ref(v___y_1234_);
lean_dec_ref(v___y_1233_);
lean_dec_ref(v___y_1232_);
lean_dec(v_fst_1223_);
v_a_1269_ = lean_ctor_get(v___x_1262_, 0);
v_isSharedCheck_1276_ = !lean_is_exclusive(v___x_1262_);
if (v_isSharedCheck_1276_ == 0)
{
v___x_1271_ = v___x_1262_;
v_isShared_1272_ = v_isSharedCheck_1276_;
goto v_resetjp_1270_;
}
else
{
lean_inc(v_a_1269_);
lean_dec(v___x_1262_);
v___x_1271_ = lean_box(0);
v_isShared_1272_ = v_isSharedCheck_1276_;
goto v_resetjp_1270_;
}
v_resetjp_1270_:
{
lean_object* v___x_1274_; 
if (v_isShared_1272_ == 0)
{
v___x_1274_ = v___x_1271_;
goto v_reusejp_1273_;
}
else
{
lean_object* v_reuseFailAlloc_1275_; 
v_reuseFailAlloc_1275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1275_, 0, v_a_1269_);
v___x_1274_ = v_reuseFailAlloc_1275_;
goto v_reusejp_1273_;
}
v_reusejp_1273_:
{
return v___x_1274_;
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
lean_object* v___x_1375_; lean_object* v___x_1377_; 
lean_dec(v_a_1213_);
v___x_1375_ = lean_box(0);
if (v_isShared_1216_ == 0)
{
lean_ctor_set(v___x_1215_, 0, v___x_1375_);
v___x_1377_ = v___x_1215_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v___x_1375_);
v___x_1377_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
return v___x_1377_;
}
}
}
}
else
{
lean_object* v_a_1380_; lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1387_; 
v_a_1380_ = lean_ctor_get(v___x_1212_, 0);
v_isSharedCheck_1387_ = !lean_is_exclusive(v___x_1212_);
if (v_isSharedCheck_1387_ == 0)
{
v___x_1382_ = v___x_1212_;
v_isShared_1383_ = v_isSharedCheck_1387_;
goto v_resetjp_1381_;
}
else
{
lean_inc(v_a_1380_);
lean_dec(v___x_1212_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1387_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
lean_object* v___x_1385_; 
if (v_isShared_1383_ == 0)
{
v___x_1385_ = v___x_1382_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1386_; 
v_reuseFailAlloc_1386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1386_, 0, v_a_1380_);
v___x_1385_ = v_reuseFailAlloc_1386_;
goto v_reusejp_1384_;
}
v_reusejp_1384_:
{
return v___x_1385_;
}
}
}
v___jp_1191_:
{
lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; 
lean_inc_ref(v___y_1192_);
v___x_1195_ = l_Lean_mkPropEq(v___y_1193_, v___y_1192_);
v___x_1196_ = l_Lean_Meta_mkExpectedPropHint(v_h_1194_, v___x_1195_);
v___x_1197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1197_, 0, v___y_1192_);
lean_ctor_set(v___x_1197_, 1, v___x_1196_);
v___x_1198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1198_, 0, v___x_1197_);
v___x_1199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1199_, 0, v___x_1198_);
return v___x_1199_;
}
v___jp_1200_:
{
lean_object* v___x_1210_; lean_object* v___x_1211_; 
v___x_1210_ = l_Lean_eagerReflBoolTrue;
lean_inc_ref(v___y_1204_);
v___x_1211_ = l_Lean_mkApp7(v___y_1204_, v___y_1207_, v___y_1203_, v___y_1202_, v___y_1201_, v___y_1208_, v___y_1209_, v___x_1210_);
v___y_1192_ = v___y_1205_;
v___y_1193_ = v___y_1206_;
v_h_1194_ = v___x_1211_;
goto v___jp_1191_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___boxed(lean_object* v_e_1388_, lean_object* v_a_1389_, lean_object* v_a_1390_, lean_object* v_a_1391_, lean_object* v_a_1392_, lean_object* v_a_1393_){
_start:
{
lean_object* v_res_1394_; 
v_res_1394_ = l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f(v_e_1388_, v_a_1389_, v_a_1390_, v_a_1391_, v_a_1392_);
lean_dec(v_a_1392_);
lean_dec_ref(v_a_1391_);
lean_dec(v_a_1390_);
lean_dec_ref(v_a_1389_);
return v_res_1394_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__3(void){
_start:
{
lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; 
v___x_1403_ = lean_box(0);
v___x_1404_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__2));
v___x_1405_ = l_Lean_mkConst(v___x_1404_, v___x_1403_);
return v___x_1405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f(lean_object* v_lhs_1406_, lean_object* v_a_1407_, lean_object* v_a_1408_, lean_object* v_a_1409_, lean_object* v_a_1410_){
_start:
{
lean_object* v___x_1412_; 
v___x_1412_ = l_Lean_Meta_Simp_Arith_Int_toLinearExpr(v_lhs_1406_, v_a_1407_, v_a_1408_, v_a_1409_, v_a_1410_);
if (lean_obj_tag(v___x_1412_) == 0)
{
lean_object* v_a_1413_; lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1480_; 
v_a_1413_ = lean_ctor_get(v___x_1412_, 0);
v_isSharedCheck_1480_ = !lean_is_exclusive(v___x_1412_);
if (v_isSharedCheck_1480_ == 0)
{
v___x_1415_ = v___x_1412_;
v_isShared_1416_ = v_isSharedCheck_1480_;
goto v_resetjp_1414_;
}
else
{
lean_inc(v_a_1413_);
lean_dec(v___x_1412_);
v___x_1415_ = lean_box(0);
v_isShared_1416_ = v_isSharedCheck_1480_;
goto v_resetjp_1414_;
}
v_resetjp_1414_:
{
lean_object* v_fst_1417_; lean_object* v_snd_1418_; lean_object* v___x_1420_; uint8_t v_isShared_1421_; uint8_t v_isSharedCheck_1479_; 
v_fst_1417_ = lean_ctor_get(v_a_1413_, 0);
v_snd_1418_ = lean_ctor_get(v_a_1413_, 1);
v_isSharedCheck_1479_ = !lean_is_exclusive(v_a_1413_);
if (v_isSharedCheck_1479_ == 0)
{
v___x_1420_ = v_a_1413_;
v_isShared_1421_ = v_isSharedCheck_1479_;
goto v_resetjp_1419_;
}
else
{
lean_inc(v_snd_1418_);
lean_inc(v_fst_1417_);
lean_dec(v_a_1413_);
v___x_1420_ = lean_box(0);
v_isShared_1421_ = v_isSharedCheck_1479_;
goto v_resetjp_1419_;
}
v_resetjp_1419_:
{
lean_object* v___x_1422_; lean_object* v___x_1423_; uint8_t v___x_1424_; uint8_t v___x_1425_; 
v___x_1422_ = l_Int_Internal_Linear_Expr_norm(v_fst_1417_);
lean_inc_ref(v___x_1422_);
v___x_1423_ = l_Int_Internal_Linear_Poly_toExpr(v___x_1422_);
v___x_1424_ = l_Int_Internal_Linear_instBEqExpr_beq(v_fst_1417_, v___x_1423_);
lean_dec_ref(v___x_1423_);
v___x_1425_ = lean_bool_not(v___x_1424_);
if (v___x_1425_ == 0)
{
lean_object* v___x_1426_; lean_object* v___x_1428_; 
lean_dec_ref(v___x_1422_);
lean_del_object(v___x_1420_);
lean_dec(v_snd_1418_);
lean_dec(v_fst_1417_);
v___x_1426_ = lean_box(0);
if (v_isShared_1416_ == 0)
{
lean_ctor_set(v___x_1415_, 0, v___x_1426_);
v___x_1428_ = v___x_1415_;
goto v_reusejp_1427_;
}
else
{
lean_object* v_reuseFailAlloc_1429_; 
v_reuseFailAlloc_1429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1429_, 0, v___x_1426_);
v___x_1428_ = v_reuseFailAlloc_1429_;
goto v_reusejp_1427_;
}
v_reusejp_1427_:
{
return v___x_1428_;
}
}
else
{
lean_object* v___x_1430_; 
lean_del_object(v___x_1415_);
lean_inc(v_snd_1418_);
v___x_1430_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(v_snd_1418_, v_a_1407_, v_a_1408_, v_a_1409_, v_a_1410_);
if (lean_obj_tag(v___x_1430_) == 0)
{
lean_object* v_a_1431_; lean_object* v___f_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; 
v_a_1431_ = lean_ctor_get(v___x_1430_, 0);
lean_inc(v_a_1431_);
lean_dec_ref_known(v___x_1430_, 1);
v___f_1432_ = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1432_, 0, v_snd_1418_);
lean_inc(v_fst_1417_);
v___x_1433_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_1417_);
lean_inc_ref(v___f_1432_);
v___x_1434_ = l_Int_Internal_Linear_Expr_denoteExpr___redArg(v___f_1432_, v_fst_1417_);
if (lean_obj_tag(v___x_1434_) == 0)
{
lean_object* v_a_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; 
v_a_1435_ = lean_ctor_get(v___x_1434_, 0);
lean_inc(v_a_1435_);
lean_dec_ref_known(v___x_1434_, 1);
lean_inc_ref(v___x_1422_);
v___x_1436_ = l_Lean_Meta_Simp_Arith_Int_ofPoly(v___x_1422_);
v___x_1437_ = l_Int_Internal_Linear_Poly_denoteExpr___redArg(v___f_1432_, v___x_1422_);
if (lean_obj_tag(v___x_1437_) == 0)
{
lean_object* v_a_1438_; lean_object* v___x_1440_; uint8_t v_isShared_1441_; uint8_t v_isSharedCheck_1454_; 
v_a_1438_ = lean_ctor_get(v___x_1437_, 0);
v_isSharedCheck_1454_ = !lean_is_exclusive(v___x_1437_);
if (v_isSharedCheck_1454_ == 0)
{
v___x_1440_ = v___x_1437_;
v_isShared_1441_ = v_isSharedCheck_1454_;
goto v_resetjp_1439_;
}
else
{
lean_inc(v_a_1438_);
lean_dec(v___x_1437_);
v___x_1440_ = lean_box(0);
v_isShared_1441_ = v_isSharedCheck_1454_;
goto v_resetjp_1439_;
}
v_resetjp_1439_:
{
lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1448_; 
v___x_1442_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__3, &l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__3_once, _init_l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__3);
v___x_1443_ = l_Lean_eagerReflBoolTrue;
v___x_1444_ = l_Lean_mkApp4(v___x_1442_, v_a_1431_, v___x_1433_, v___x_1436_, v___x_1443_);
lean_inc(v_a_1438_);
v___x_1445_ = l_Lean_mkIntEq(v_a_1435_, v_a_1438_);
v___x_1446_ = l_Lean_Meta_mkExpectedPropHint(v___x_1444_, v___x_1445_);
if (v_isShared_1421_ == 0)
{
lean_ctor_set(v___x_1420_, 1, v___x_1446_);
lean_ctor_set(v___x_1420_, 0, v_a_1438_);
v___x_1448_ = v___x_1420_;
goto v_reusejp_1447_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v_a_1438_);
lean_ctor_set(v_reuseFailAlloc_1453_, 1, v___x_1446_);
v___x_1448_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1447_;
}
v_reusejp_1447_:
{
lean_object* v___x_1449_; lean_object* v___x_1451_; 
v___x_1449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1449_, 0, v___x_1448_);
if (v_isShared_1441_ == 0)
{
lean_ctor_set(v___x_1440_, 0, v___x_1449_);
v___x_1451_ = v___x_1440_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1452_; 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v___x_1449_);
v___x_1451_ = v_reuseFailAlloc_1452_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
return v___x_1451_;
}
}
}
}
else
{
lean_object* v_a_1455_; lean_object* v___x_1457_; uint8_t v_isShared_1458_; uint8_t v_isSharedCheck_1462_; 
lean_dec_ref(v___x_1436_);
lean_dec(v_a_1435_);
lean_dec_ref(v___x_1433_);
lean_dec(v_a_1431_);
lean_del_object(v___x_1420_);
v_a_1455_ = lean_ctor_get(v___x_1437_, 0);
v_isSharedCheck_1462_ = !lean_is_exclusive(v___x_1437_);
if (v_isSharedCheck_1462_ == 0)
{
v___x_1457_ = v___x_1437_;
v_isShared_1458_ = v_isSharedCheck_1462_;
goto v_resetjp_1456_;
}
else
{
lean_inc(v_a_1455_);
lean_dec(v___x_1437_);
v___x_1457_ = lean_box(0);
v_isShared_1458_ = v_isSharedCheck_1462_;
goto v_resetjp_1456_;
}
v_resetjp_1456_:
{
lean_object* v___x_1460_; 
if (v_isShared_1458_ == 0)
{
v___x_1460_ = v___x_1457_;
goto v_reusejp_1459_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v_a_1455_);
v___x_1460_ = v_reuseFailAlloc_1461_;
goto v_reusejp_1459_;
}
v_reusejp_1459_:
{
return v___x_1460_;
}
}
}
}
else
{
lean_object* v_a_1463_; lean_object* v___x_1465_; uint8_t v_isShared_1466_; uint8_t v_isSharedCheck_1470_; 
lean_dec_ref(v___x_1433_);
lean_dec_ref(v___f_1432_);
lean_dec(v_a_1431_);
lean_dec_ref(v___x_1422_);
lean_del_object(v___x_1420_);
v_a_1463_ = lean_ctor_get(v___x_1434_, 0);
v_isSharedCheck_1470_ = !lean_is_exclusive(v___x_1434_);
if (v_isSharedCheck_1470_ == 0)
{
v___x_1465_ = v___x_1434_;
v_isShared_1466_ = v_isSharedCheck_1470_;
goto v_resetjp_1464_;
}
else
{
lean_inc(v_a_1463_);
lean_dec(v___x_1434_);
v___x_1465_ = lean_box(0);
v_isShared_1466_ = v_isSharedCheck_1470_;
goto v_resetjp_1464_;
}
v_resetjp_1464_:
{
lean_object* v___x_1468_; 
if (v_isShared_1466_ == 0)
{
v___x_1468_ = v___x_1465_;
goto v_reusejp_1467_;
}
else
{
lean_object* v_reuseFailAlloc_1469_; 
v_reuseFailAlloc_1469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1469_, 0, v_a_1463_);
v___x_1468_ = v_reuseFailAlloc_1469_;
goto v_reusejp_1467_;
}
v_reusejp_1467_:
{
return v___x_1468_;
}
}
}
}
else
{
lean_object* v_a_1471_; lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1478_; 
lean_dec_ref(v___x_1422_);
lean_del_object(v___x_1420_);
lean_dec(v_snd_1418_);
lean_dec(v_fst_1417_);
v_a_1471_ = lean_ctor_get(v___x_1430_, 0);
v_isSharedCheck_1478_ = !lean_is_exclusive(v___x_1430_);
if (v_isSharedCheck_1478_ == 0)
{
v___x_1473_ = v___x_1430_;
v_isShared_1474_ = v_isSharedCheck_1478_;
goto v_resetjp_1472_;
}
else
{
lean_inc(v_a_1471_);
lean_dec(v___x_1430_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1478_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
lean_object* v___x_1476_; 
if (v_isShared_1474_ == 0)
{
v___x_1476_ = v___x_1473_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1477_; 
v_reuseFailAlloc_1477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1477_, 0, v_a_1471_);
v___x_1476_ = v_reuseFailAlloc_1477_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
return v___x_1476_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1481_; lean_object* v___x_1483_; uint8_t v_isShared_1484_; uint8_t v_isSharedCheck_1488_; 
v_a_1481_ = lean_ctor_get(v___x_1412_, 0);
v_isSharedCheck_1488_ = !lean_is_exclusive(v___x_1412_);
if (v_isSharedCheck_1488_ == 0)
{
v___x_1483_ = v___x_1412_;
v_isShared_1484_ = v_isSharedCheck_1488_;
goto v_resetjp_1482_;
}
else
{
lean_inc(v_a_1481_);
lean_dec(v___x_1412_);
v___x_1483_ = lean_box(0);
v_isShared_1484_ = v_isSharedCheck_1488_;
goto v_resetjp_1482_;
}
v_resetjp_1482_:
{
lean_object* v___x_1486_; 
if (v_isShared_1484_ == 0)
{
v___x_1486_ = v___x_1483_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v_a_1481_);
v___x_1486_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
return v___x_1486_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___boxed(lean_object* v_lhs_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_){
_start:
{
lean_object* v_res_1495_; 
v_res_1495_ = l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f(v_lhs_1489_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_);
lean_dec(v_a_1493_);
lean_dec_ref(v_a_1492_);
lean_dec(v_a_1491_);
lean_dec_ref(v_a_1490_);
return v_res_1495_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Arith_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Arith_Int_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Arith_Int_Simp(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Simp_Arith_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Simp_Arith_Int_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Simp_Arith_Int_Simp(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Simp_Arith_Util(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Simp_Arith_Int_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Simp_Arith_Int_Simp(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Simp_Arith_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Arith_Int_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Simp_Arith_Int_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Simp_Arith_Int_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Simp_Arith_Int_Simp(builtin);
}
#ifdef __cplusplus
}
#endif

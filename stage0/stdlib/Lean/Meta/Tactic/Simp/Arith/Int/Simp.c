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
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_succ___override(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_Meta_Simp_Arith_Int_toLinearExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Internal_Linear_Expr_norm(lean_object*);
lean_object* l_Int_Internal_Linear_Poly_toExpr(lean_object*);
uint8_t l_Int_Internal_Linear_instBEqExpr_beq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Arith_Int_toContextExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(lean_object*);
lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly(lean_object*);
extern lean_object* l_Lean_eagerReflBoolTrue;
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Internal_Linear_Expr_denoteExpr___redArg(lean_object*, lean_object*);
lean_object* l_Int_Internal_Linear_Poly_denoteExpr___redArg(lean_object*, lean_object*);
lean_object* l_Lean_mkIntEq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkExpectedPropHint(lean_object*, lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* l_Lean_mkPropEq(lean_object*, lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Internal_Linear_Poly_div(lean_object*, lean_object*);
lean_object* l_Lean_mkIntLE(lean_object*, lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* l_Int_toNat(lean_object*);
lean_object* l_Lean_instToExprInt_mkNat(lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Internal_Linear_Poly_getConst(lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f(lean_object* v_e_168_, lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_){
_start:
{
lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_174_ = l_Lean_instInhabitedExpr;
v___x_175_ = l_Lean_Meta_Simp_Arith_Int_eqCnstr_x3f(v_e_168_, v_a_169_, v_a_170_, v_a_171_, v_a_172_);
if (lean_obj_tag(v___x_175_) == 0)
{
lean_object* v_a_176_; lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_555_; 
v_a_176_ = lean_ctor_get(v___x_175_, 0);
v_isSharedCheck_555_ = !lean_is_exclusive(v___x_175_);
if (v_isSharedCheck_555_ == 0)
{
v___x_178_ = v___x_175_;
v_isShared_179_ = v_isSharedCheck_555_;
goto v_resetjp_177_;
}
else
{
lean_inc(v_a_176_);
lean_dec(v___x_175_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_555_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
if (lean_obj_tag(v_a_176_) == 1)
{
lean_object* v_val_180_; lean_object* v___x_182_; uint8_t v_isShared_183_; uint8_t v_isSharedCheck_550_; 
v_val_180_ = lean_ctor_get(v_a_176_, 0);
v_isSharedCheck_550_ = !lean_is_exclusive(v_a_176_);
if (v_isSharedCheck_550_ == 0)
{
v___x_182_ = v_a_176_;
v_isShared_183_ = v_isSharedCheck_550_;
goto v_resetjp_181_;
}
else
{
lean_inc(v_val_180_);
lean_dec(v_a_176_);
v___x_182_ = lean_box(0);
v_isShared_183_ = v_isSharedCheck_550_;
goto v_resetjp_181_;
}
v_resetjp_181_:
{
lean_object* v_snd_184_; lean_object* v_fst_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_549_; 
v_snd_184_ = lean_ctor_get(v_val_180_, 1);
v_fst_185_ = lean_ctor_get(v_val_180_, 0);
v_isSharedCheck_549_ = !lean_is_exclusive(v_val_180_);
if (v_isSharedCheck_549_ == 0)
{
v___x_187_ = v_val_180_;
v_isShared_188_ = v_isSharedCheck_549_;
goto v_resetjp_186_;
}
else
{
lean_inc(v_snd_184_);
lean_inc(v_fst_185_);
lean_dec(v_val_180_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_549_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
lean_object* v_fst_189_; lean_object* v_snd_190_; lean_object* v___x_192_; uint8_t v_isShared_193_; uint8_t v_isSharedCheck_548_; 
v_fst_189_ = lean_ctor_get(v_snd_184_, 0);
v_snd_190_ = lean_ctor_get(v_snd_184_, 1);
v_isSharedCheck_548_ = !lean_is_exclusive(v_snd_184_);
if (v_isSharedCheck_548_ == 0)
{
v___x_192_ = v_snd_184_;
v_isShared_193_ = v_isSharedCheck_548_;
goto v_resetjp_191_;
}
else
{
lean_inc(v_snd_190_);
lean_inc(v_fst_189_);
lean_dec(v_snd_184_);
v___x_192_ = lean_box(0);
v_isShared_193_ = v_isSharedCheck_548_;
goto v_resetjp_191_;
}
v_resetjp_191_:
{
lean_object* v___f_194_; lean_object* v___x_195_; 
lean_inc(v_snd_190_);
v___f_194_ = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__0___boxed), 3, 2);
lean_closure_set(v___f_194_, 0, v___x_174_);
lean_closure_set(v___f_194_, 1, v_snd_190_);
lean_inc(v_fst_185_);
lean_inc_ref(v___f_194_);
v___x_195_ = l_Int_Internal_Linear_Expr_denoteExpr___redArg(v___f_194_, v_fst_185_);
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
lean_inc(v_fst_189_);
lean_inc_ref(v___f_194_);
v___x_200_ = l_Int_Internal_Linear_Expr_denoteExpr___redArg(v___f_194_, v_fst_189_);
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
lean_inc(v_fst_189_);
lean_inc(v_fst_185_);
v___x_282_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_282_, 0, v_fst_185_);
lean_ctor_set(v___x_282_, 1, v_fst_189_);
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
v___x_473_ = l_Int_Internal_Linear_instBEqExpr_beq(v___x_472_, v_fst_185_);
lean_dec_ref(v___x_472_);
if (v___x_473_ == 0)
{
v___y_398_ = v___x_471_;
goto v___jp_397_;
}
else
{
lean_object* v___x_474_; uint8_t v___x_475_; 
v___x_474_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__36, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__36_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__36);
v___x_475_ = l_Int_Internal_Linear_instBEqExpr_beq(v_fst_189_, v___x_474_);
v___y_398_ = v___x_475_;
goto v___jp_397_;
}
}
else
{
lean_object* v___x_476_; lean_object* v___x_477_; 
lean_dec_ref(v___x_283_);
lean_del_object(v___x_203_);
lean_del_object(v___x_198_);
lean_dec_ref(v___f_194_);
lean_del_object(v___x_192_);
lean_del_object(v___x_187_);
lean_del_object(v___x_182_);
lean_del_object(v___x_178_);
v___x_476_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__39, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__39_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__39);
v___x_477_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(v_snd_190_, v_a_169_, v_a_170_, v_a_171_, v_a_172_);
if (lean_obj_tag(v___x_477_) == 0)
{
lean_object* v_a_478_; lean_object* v___x_480_; uint8_t v_isShared_481_; uint8_t v_isSharedCheck_494_; 
v_a_478_ = lean_ctor_get(v___x_477_, 0);
v_isSharedCheck_494_ = !lean_is_exclusive(v___x_477_);
if (v_isSharedCheck_494_ == 0)
{
v___x_480_ = v___x_477_;
v_isShared_481_ = v_isSharedCheck_494_;
goto v_resetjp_479_;
}
else
{
lean_inc(v_a_478_);
lean_dec(v___x_477_);
v___x_480_ = lean_box(0);
v_isShared_481_ = v_isSharedCheck_494_;
goto v_resetjp_479_;
}
v_resetjp_479_:
{
lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_492_; 
v___x_482_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__42, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__42_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__42);
v___x_483_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_185_);
v___x_484_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_189_);
v___x_485_ = l_Lean_eagerReflBoolTrue;
v___x_486_ = l_Lean_mkApp4(v___x_482_, v_a_478_, v___x_483_, v___x_484_, v___x_485_);
v___x_487_ = l_Lean_mkPropEq(v___x_205_, v___x_476_);
v___x_488_ = l_Lean_Meta_mkExpectedPropHint(v___x_486_, v___x_487_);
v___x_489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_489_, 0, v___x_476_);
lean_ctor_set(v___x_489_, 1, v___x_488_);
v___x_490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_490_, 0, v___x_489_);
if (v_isShared_481_ == 0)
{
lean_ctor_set(v___x_480_, 0, v___x_490_);
v___x_492_ = v___x_480_;
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
lean_dec(v_fst_189_);
lean_dec(v_fst_185_);
v_a_495_ = lean_ctor_get(v___x_477_, 0);
v_isSharedCheck_502_ = !lean_is_exclusive(v___x_477_);
if (v_isSharedCheck_502_ == 0)
{
v___x_497_ = v___x_477_;
v_isShared_498_ = v_isSharedCheck_502_;
goto v_resetjp_496_;
}
else
{
lean_inc(v_a_495_);
lean_dec(v___x_477_);
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
lean_object* v___x_503_; lean_object* v___x_504_; 
lean_dec_ref(v___x_283_);
lean_del_object(v___x_203_);
lean_del_object(v___x_198_);
lean_dec_ref(v___f_194_);
lean_del_object(v___x_192_);
lean_del_object(v___x_187_);
lean_del_object(v___x_182_);
lean_del_object(v___x_178_);
v___x_503_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__9, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__9_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__9);
v___x_504_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(v_snd_190_, v_a_169_, v_a_170_, v_a_171_, v_a_172_);
if (lean_obj_tag(v___x_504_) == 0)
{
lean_object* v_a_505_; lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_521_; 
v_a_505_ = lean_ctor_get(v___x_504_, 0);
v_isSharedCheck_521_ = !lean_is_exclusive(v___x_504_);
if (v_isSharedCheck_521_ == 0)
{
v___x_507_ = v___x_504_;
v_isShared_508_ = v_isSharedCheck_521_;
goto v_resetjp_506_;
}
else
{
lean_inc(v_a_505_);
lean_dec(v___x_504_);
v___x_507_ = lean_box(0);
v_isShared_508_ = v_isSharedCheck_521_;
goto v_resetjp_506_;
}
v_resetjp_506_:
{
lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_519_; 
v___x_509_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__45, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__45_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__45);
v___x_510_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_185_);
v___x_511_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_189_);
v___x_512_ = l_Lean_eagerReflBoolTrue;
v___x_513_ = l_Lean_mkApp4(v___x_509_, v_a_505_, v___x_510_, v___x_511_, v___x_512_);
v___x_514_ = l_Lean_mkPropEq(v___x_205_, v___x_503_);
v___x_515_ = l_Lean_Meta_mkExpectedPropHint(v___x_513_, v___x_514_);
v___x_516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_516_, 0, v___x_503_);
lean_ctor_set(v___x_516_, 1, v___x_515_);
v___x_517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_517_, 0, v___x_516_);
if (v_isShared_508_ == 0)
{
lean_ctor_set(v___x_507_, 0, v___x_517_);
v___x_519_ = v___x_507_;
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
lean_dec(v_fst_189_);
lean_dec(v_fst_185_);
v_a_522_ = lean_ctor_get(v___x_504_, 0);
v_isSharedCheck_529_ = !lean_is_exclusive(v___x_504_);
if (v_isSharedCheck_529_ == 0)
{
v___x_524_ = v___x_504_;
v_isShared_525_ = v_isSharedCheck_529_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_a_522_);
lean_dec(v___x_504_);
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
lean_inc_ref(v___y_207_);
v___x_214_ = l_Lean_mkApp5(v___y_207_, v___y_211_, v___y_208_, v___y_209_, v___y_212_, v___x_213_);
lean_inc_ref_n(v___y_210_, 2);
v___x_215_ = l_Lean_mkPropEq(v___x_205_, v___y_210_);
v___x_216_ = l_Lean_Meta_mkExpectedPropHint(v___x_214_, v___x_215_);
if (v_isShared_193_ == 0)
{
lean_ctor_set(v___x_192_, 1, v___x_216_);
lean_ctor_set(v___x_192_, 0, v___y_210_);
v___x_218_ = v___x_192_;
goto v_reusejp_217_;
}
else
{
lean_object* v_reuseFailAlloc_225_; 
v_reuseFailAlloc_225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_225_, 0, v___y_210_);
lean_ctor_set(v_reuseFailAlloc_225_, 1, v___x_216_);
v___x_218_ = v_reuseFailAlloc_225_;
goto v_reusejp_217_;
}
v_reusejp_217_:
{
lean_object* v___x_220_; 
if (v_isShared_183_ == 0)
{
lean_ctor_set(v___x_182_, 0, v___x_218_);
v___x_220_ = v___x_182_;
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
lean_inc_ref(v___y_232_);
v___x_235_ = l_Lean_mkApp6(v___y_232_, v___y_229_, v___y_230_, v___y_227_, v___y_228_, v___y_233_, v___x_234_);
lean_inc_ref(v___y_231_);
v___x_236_ = l_Lean_mkPropEq(v___x_205_, v___y_231_);
v___x_237_ = l_Lean_Meta_mkExpectedPropHint(v___x_235_, v___x_236_);
if (v_isShared_188_ == 0)
{
lean_ctor_set(v___x_187_, 1, v___x_237_);
lean_ctor_set(v___x_187_, 0, v___y_231_);
v___x_239_ = v___x_187_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v___y_231_);
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
v___x_249_ = l_Lean_mkIntEq(v___y_247_, v___y_248_);
v___x_250_ = lean_expr_eqv(v___x_249_, v___x_205_);
if (v___x_250_ == 0)
{
lean_object* v___x_251_; 
lean_del_object(v___x_178_);
v___x_251_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(v_snd_190_, v_a_169_, v_a_170_, v_a_171_, v_a_172_);
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
v___x_257_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_185_);
v___x_258_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_189_);
v___x_259_ = l_Lean_mkNatLit(v___y_246_);
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
lean_dec(v___y_246_);
lean_dec_ref(v___x_205_);
lean_dec(v_fst_189_);
lean_dec(v_fst_185_);
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
lean_dec(v___y_246_);
lean_dec_ref(v___x_205_);
lean_dec(v_snd_190_);
lean_dec(v_fst_189_);
lean_dec(v_fst_185_);
v___x_278_ = lean_box(0);
if (v_isShared_179_ == 0)
{
lean_ctor_set(v___x_178_, 0, v___x_278_);
v___x_280_ = v___x_178_;
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
lean_object* v___x_297_; lean_object* v___x_298_; 
lean_dec_ref(v___x_283_);
lean_del_object(v___x_198_);
lean_dec_ref(v___f_194_);
lean_del_object(v___x_187_);
v___x_297_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__9, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__9_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__9);
v___x_298_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(v_snd_190_, v___y_285_, v___y_286_, v___y_287_, v___y_288_);
if (lean_obj_tag(v___x_298_) == 0)
{
lean_object* v_a_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; uint8_t v___x_303_; 
v_a_299_ = lean_ctor_get(v___x_298_, 0);
lean_inc(v_a_299_);
lean_dec_ref_known(v___x_298_, 1);
v___x_300_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__12, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__12_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__12);
v___x_301_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_185_);
v___x_302_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_189_);
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
v___y_207_ = v___x_300_;
v___y_208_ = v___x_301_;
v___y_209_ = v___x_302_;
v___y_210_ = v___x_297_;
v___y_211_ = v_a_299_;
v___y_212_ = v___x_310_;
goto v___jp_206_;
}
else
{
lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_311_ = l_Int_toNat(v___x_293_);
lean_dec(v___x_293_);
v___x_312_ = l_Lean_instToExprInt_mkNat(v___x_311_);
v___y_207_ = v___x_300_;
v___y_208_ = v___x_301_;
v___y_209_ = v___x_302_;
v___y_210_ = v___x_297_;
v___y_211_ = v_a_299_;
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
lean_del_object(v___x_192_);
lean_dec(v_fst_189_);
lean_dec(v_fst_185_);
lean_del_object(v___x_182_);
v_a_313_ = lean_ctor_get(v___x_298_, 0);
v_isSharedCheck_320_ = !lean_is_exclusive(v___x_298_);
if (v_isSharedCheck_320_ == 0)
{
v___x_315_ = v___x_298_;
v_isShared_316_ = v_isSharedCheck_320_;
goto v_resetjp_314_;
}
else
{
lean_inc(v_a_313_);
lean_dec(v___x_298_);
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
lean_del_object(v___x_192_);
lean_del_object(v___x_182_);
v___x_321_ = l_Int_Internal_Linear_Poly_div(v___x_293_, v___x_283_);
lean_inc_ref(v___x_321_);
v___x_322_ = l_Int_Internal_Linear_Poly_denoteExpr___redArg(v___f_194_, v___x_321_);
if (lean_obj_tag(v___x_322_) == 0)
{
lean_object* v_a_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; 
v_a_323_ = lean_ctor_get(v___x_322_, 0);
lean_inc(v_a_323_);
lean_dec_ref_known(v___x_322_, 1);
v___x_324_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__24, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__24_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__24);
v___x_325_ = l_Lean_mkIntEq(v_a_323_, v___x_324_);
v___x_326_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(v_snd_190_, v___y_285_, v___y_286_, v___y_287_, v___y_288_);
if (lean_obj_tag(v___x_326_) == 0)
{
lean_object* v_a_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; uint8_t v___x_332_; 
v_a_327_ = lean_ctor_get(v___x_326_, 0);
lean_inc(v_a_327_);
lean_dec_ref_known(v___x_326_, 1);
v___x_328_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__27, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__27_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__27);
v___x_329_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_185_);
v___x_330_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_189_);
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
v___y_227_ = v___x_330_;
v___y_228_ = v___x_331_;
v___y_229_ = v_a_327_;
v___y_230_ = v___x_329_;
v___y_231_ = v___x_325_;
v___y_232_ = v___x_328_;
v___y_233_ = v___x_339_;
goto v___jp_226_;
}
else
{
lean_object* v___x_340_; lean_object* v___x_341_; 
v___x_340_ = l_Int_toNat(v___x_293_);
lean_dec(v___x_293_);
v___x_341_ = l_Lean_instToExprInt_mkNat(v___x_340_);
v___y_227_ = v___x_330_;
v___y_228_ = v___x_331_;
v___y_229_ = v_a_327_;
v___y_230_ = v___x_329_;
v___y_231_ = v___x_325_;
v___y_232_ = v___x_328_;
v___y_233_ = v___x_341_;
goto v___jp_226_;
}
}
else
{
lean_object* v_a_342_; lean_object* v___x_344_; uint8_t v_isShared_345_; uint8_t v_isSharedCheck_349_; 
lean_dec_ref(v___x_325_);
lean_dec_ref(v___x_321_);
lean_dec(v___x_293_);
lean_dec_ref(v___x_205_);
lean_del_object(v___x_198_);
lean_dec(v_fst_189_);
lean_del_object(v___x_187_);
lean_dec(v_fst_185_);
v_a_342_ = lean_ctor_get(v___x_326_, 0);
v_isSharedCheck_349_ = !lean_is_exclusive(v___x_326_);
if (v_isSharedCheck_349_ == 0)
{
v___x_344_ = v___x_326_;
v_isShared_345_ = v_isSharedCheck_349_;
goto v_resetjp_343_;
}
else
{
lean_inc(v_a_342_);
lean_dec(v___x_326_);
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
lean_dec(v_snd_190_);
lean_dec(v_fst_189_);
lean_del_object(v___x_187_);
lean_dec(v_fst_185_);
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
lean_del_object(v___x_192_);
lean_del_object(v___x_187_);
lean_del_object(v___x_182_);
lean_inc_ref(v___x_283_);
v___x_358_ = l_Int_Internal_Linear_Poly_denoteExpr___redArg(v___f_194_, v___x_283_);
if (lean_obj_tag(v___x_358_) == 0)
{
lean_object* v_a_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; 
v_a_359_ = lean_ctor_get(v___x_358_, 0);
lean_inc(v_a_359_);
lean_dec_ref_known(v___x_358_, 1);
v___x_360_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__24, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__24_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__24);
v___x_361_ = l_Lean_mkIntEq(v_a_359_, v___x_360_);
v___x_362_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(v_snd_190_, v___y_285_, v___y_286_, v___y_287_, v___y_288_);
if (lean_obj_tag(v___x_362_) == 0)
{
lean_object* v_a_363_; lean_object* v___x_365_; uint8_t v_isShared_366_; uint8_t v_isSharedCheck_380_; 
v_a_363_ = lean_ctor_get(v___x_362_, 0);
v_isSharedCheck_380_ = !lean_is_exclusive(v___x_362_);
if (v_isSharedCheck_380_ == 0)
{
v___x_365_ = v___x_362_;
v_isShared_366_ = v_isSharedCheck_380_;
goto v_resetjp_364_;
}
else
{
lean_inc(v_a_363_);
lean_dec(v___x_362_);
v___x_365_ = lean_box(0);
v_isShared_366_ = v_isSharedCheck_380_;
goto v_resetjp_364_;
}
v_resetjp_364_:
{
lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_378_; 
v___x_367_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30);
v___x_368_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_185_);
v___x_369_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_189_);
v___x_370_ = l_Lean_Meta_Simp_Arith_Int_ofPoly(v___x_283_);
v___x_371_ = l_Lean_eagerReflBoolTrue;
v___x_372_ = l_Lean_mkApp5(v___x_367_, v_a_363_, v___x_368_, v___x_369_, v___x_370_, v___x_371_);
lean_inc_ref(v___x_361_);
v___x_373_ = l_Lean_mkPropEq(v___x_205_, v___x_361_);
v___x_374_ = l_Lean_Meta_mkExpectedPropHint(v___x_372_, v___x_373_);
v___x_375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_375_, 0, v___x_361_);
lean_ctor_set(v___x_375_, 1, v___x_374_);
v___x_376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_376_, 0, v___x_375_);
if (v_isShared_366_ == 0)
{
lean_ctor_set(v___x_365_, 0, v___x_376_);
v___x_378_ = v___x_365_;
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
lean_dec_ref(v___x_361_);
lean_dec_ref(v___x_283_);
lean_dec_ref(v___x_205_);
lean_dec(v_fst_189_);
lean_dec(v_fst_185_);
v_a_381_ = lean_ctor_get(v___x_362_, 0);
v_isSharedCheck_388_ = !lean_is_exclusive(v___x_362_);
if (v_isSharedCheck_388_ == 0)
{
v___x_383_ = v___x_362_;
v_isShared_384_ = v_isSharedCheck_388_;
goto v_resetjp_382_;
}
else
{
lean_inc(v_a_381_);
lean_dec(v___x_362_);
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
lean_dec(v_snd_190_);
lean_dec(v_fst_189_);
lean_dec(v_fst_185_);
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
v_v_400_ = lean_ctor_get(v___x_283_, 1);
v_p_401_ = lean_ctor_get(v___x_283_, 2);
v___x_402_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__31, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__31_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__31);
v___x_403_ = lean_int_dec_eq(v_k_399_, v___x_402_);
if (v___x_403_ == 0)
{
lean_del_object(v___x_178_);
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
lean_inc_ref(v_p_401_);
lean_inc(v_v_400_);
lean_dec_ref_known(v___x_283_, 3);
lean_del_object(v___x_203_);
lean_del_object(v___x_198_);
lean_dec_ref(v___f_194_);
lean_del_object(v___x_192_);
lean_del_object(v___x_187_);
lean_del_object(v___x_182_);
v_k_404_ = lean_ctor_get(v_p_401_, 0);
lean_inc(v_k_404_);
lean_dec_ref_known(v_p_401_, 1);
v___x_405_ = lean_array_get_borrowed(v___x_174_, v_snd_190_, v_v_400_);
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
v___y_246_ = v_v_400_;
v___y_247_ = v___x_405_;
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
v___y_246_ = v_v_400_;
v___y_247_ = v___x_405_;
v___y_248_ = v___x_417_;
goto v___jp_245_;
}
}
else
{
lean_object* v_k_418_; lean_object* v_v_419_; lean_object* v_p_420_; lean_object* v___x_421_; uint8_t v___x_422_; 
lean_del_object(v___x_178_);
v_k_418_ = lean_ctor_get(v_p_401_, 0);
v_v_419_ = lean_ctor_get(v_p_401_, 1);
v_p_420_ = lean_ctor_get(v_p_401_, 2);
lean_inc_ref(v_p_420_);
v___x_421_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__32, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__32_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__32);
v___x_422_ = lean_int_dec_eq(v_k_418_, v___x_421_);
if (v___x_422_ == 0)
{
lean_dec_ref(v_p_420_);
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
v___y_285_ = v_a_169_;
v___y_286_ = v_a_170_;
v___y_287_ = v_a_171_;
v___y_288_ = v_a_172_;
goto v___jp_284_;
}
else
{
lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; uint8_t v___x_432_; 
lean_inc(v_v_419_);
lean_inc(v_v_400_);
lean_dec_ref_known(v___x_283_, 3);
lean_del_object(v___x_203_);
lean_del_object(v___x_198_);
lean_dec_ref(v___f_194_);
lean_del_object(v___x_192_);
lean_del_object(v___x_187_);
lean_del_object(v___x_182_);
v___x_429_ = lean_array_get_borrowed(v___x_174_, v_snd_190_, v_v_400_);
v___x_430_ = lean_array_get_borrowed(v___x_174_, v_snd_190_, v_v_419_);
lean_inc(v___x_430_);
lean_inc(v___x_429_);
v___x_431_ = l_Lean_mkIntEq(v___x_429_, v___x_430_);
v___x_432_ = lean_expr_eqv(v___x_431_, v___x_205_);
if (v___x_432_ == 0)
{
lean_object* v___x_433_; 
v___x_433_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(v_snd_190_, v_a_169_, v_a_170_, v_a_171_, v_a_172_);
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
v___x_439_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_185_);
v___x_440_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_189_);
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
lean_dec(v_fst_189_);
lean_dec(v_fst_185_);
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
lean_dec(v_snd_190_);
lean_dec(v_fst_189_);
lean_dec(v_fst_185_);
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
lean_del_object(v___x_178_);
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
lean_del_object(v___x_192_);
lean_dec(v_snd_190_);
lean_dec(v_fst_189_);
lean_del_object(v___x_187_);
lean_dec(v_fst_185_);
lean_del_object(v___x_182_);
lean_del_object(v___x_178_);
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
lean_del_object(v___x_192_);
lean_dec(v_snd_190_);
lean_dec(v_fst_189_);
lean_del_object(v___x_187_);
lean_dec(v_fst_185_);
lean_del_object(v___x_182_);
lean_del_object(v___x_178_);
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
lean_del_object(v___x_192_);
lean_dec(v_snd_190_);
lean_dec(v_fst_189_);
lean_del_object(v___x_187_);
lean_dec(v_fst_185_);
lean_del_object(v___x_182_);
lean_del_object(v___x_178_);
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
lean_dec(v_a_176_);
v___x_551_ = lean_box(0);
if (v_isShared_179_ == 0)
{
lean_ctor_set(v___x_178_, 0, v___x_551_);
v___x_553_ = v___x_178_;
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
v_a_556_ = lean_ctor_get(v___x_175_, 0);
v_isSharedCheck_563_ = !lean_is_exclusive(v___x_175_);
if (v_isSharedCheck_563_ == 0)
{
v___x_558_ = v___x_175_;
v_isShared_559_ = v_isSharedCheck_563_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_a_556_);
lean_dec(v___x_175_);
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
LEAN_EXPORT void l_Lean_Meta_Simp_Arith_Int_simpEq_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_168_ = stack[0].m_obj;
lean_object* v_a_169_ = stack[1].m_obj;
lean_object* v_a_170_ = stack[2].m_obj;
lean_object* v_a_171_ = stack[3].m_obj;
lean_object* v_a_172_ = stack[4].m_obj;
lean_object* v_res_564_;
v_res_564_ = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f(v_e_168_, v_a_169_, v_a_170_, v_a_171_, v_a_172_);
stack->m_obj
 = v_res_564_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___boxed(lean_object* v_e_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_, lean_object* v_a_569_, lean_object* v_a_570_){
_start:
{
lean_object* v_res_571_; 
v_res_571_ = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f(v_e_565_, v_a_566_, v_a_567_, v_a_568_, v_a_569_);
lean_dec(v_a_569_);
lean_dec_ref(v_a_568_);
lean_dec(v_a_567_);
lean_dec_ref(v_a_566_);
return v_res_571_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__2(void){
_start:
{
lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_578_ = lean_box(0);
v___x_579_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__1));
v___x_580_ = l_Lean_mkConst(v___x_579_, v___x_578_);
return v___x_580_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__5(void){
_start:
{
lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; 
v___x_587_ = lean_box(0);
v___x_588_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__4));
v___x_589_ = l_Lean_mkConst(v___x_588_, v___x_587_);
return v___x_589_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__8(void){
_start:
{
lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; 
v___x_596_ = lean_box(0);
v___x_597_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__7));
v___x_598_ = l_Lean_mkConst(v___x_597_, v___x_596_);
return v___x_598_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__11(void){
_start:
{
lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_605_ = lean_box(0);
v___x_606_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__10));
v___x_607_ = l_Lean_mkConst(v___x_606_, v___x_605_);
return v___x_607_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__14(void){
_start:
{
lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; 
v___x_614_ = lean_box(0);
v___x_615_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__13));
v___x_616_ = l_Lean_mkConst(v___x_615_, v___x_614_);
return v___x_616_;
}
}
lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f(lean_object* v_e_622_, uint8_t v_checkIfModified_623_, lean_object* v_a_624_, lean_object* v_a_625_, lean_object* v_a_626_, lean_object* v_a_627_){
_start:
{
lean_object* v___y_630_; lean_object* v___y_631_; lean_object* v_h_632_; lean_object* v___y_639_; lean_object* v___y_640_; lean_object* v___y_641_; lean_object* v___y_642_; lean_object* v___y_643_; lean_object* v___y_644_; lean_object* v___y_645_; lean_object* v___y_646_; lean_object* v___y_650_; lean_object* v___y_651_; lean_object* v___y_652_; lean_object* v___y_653_; lean_object* v___y_654_; lean_object* v___y_655_; lean_object* v___y_656_; lean_object* v___y_657_; lean_object* v___y_661_; lean_object* v___y_662_; lean_object* v___y_663_; lean_object* v___y_664_; lean_object* v___y_665_; lean_object* v___y_666_; lean_object* v___y_667_; lean_object* v___y_668_; lean_object* v___y_669_; uint8_t v___y_670_; lean_object* v___y_741_; lean_object* v___y_742_; lean_object* v___y_743_; lean_object* v___y_744_; lean_object* v___y_745_; lean_object* v___y_746_; lean_object* v___x_796_; uint8_t v___y_798_; lean_object* v___x_936_; uint8_t v___x_937_; 
v___x_796_ = l_Lean_instInhabitedExpr;
v___x_936_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__17));
v___x_937_ = l_Lean_Expr_isAppOf(v_e_622_, v___x_936_);
if (v___x_937_ == 0)
{
v___y_798_ = v___x_937_;
goto v___jp_797_;
}
else
{
v___y_798_ = v_checkIfModified_623_;
goto v___jp_797_;
}
v___jp_629_:
{
lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; 
lean_inc_ref(v___y_631_);
v___x_633_ = l_Lean_mkPropEq(v___y_630_, v___y_631_);
v___x_634_ = l_Lean_Meta_mkExpectedPropHint(v_h_632_, v___x_633_);
v___x_635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_635_, 0, v___y_631_);
lean_ctor_set(v___x_635_, 1, v___x_634_);
v___x_636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_636_, 0, v___x_635_);
v___x_637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_637_, 0, v___x_636_);
return v___x_637_;
}
v___jp_638_:
{
lean_object* v___x_647_; lean_object* v___x_648_; 
v___x_647_ = l_Lean_eagerReflBoolTrue;
lean_inc_ref(v___y_640_);
v___x_648_ = l_Lean_mkApp6(v___y_640_, v___y_641_, v___y_643_, v___y_642_, v___y_644_, v___y_646_, v___x_647_);
v___y_630_ = v___y_639_;
v___y_631_ = v___y_645_;
v_h_632_ = v___x_648_;
goto v___jp_629_;
}
v___jp_649_:
{
lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_658_ = l_Lean_eagerReflBoolTrue;
lean_inc_ref(v___y_654_);
v___x_659_ = l_Lean_mkApp6(v___y_654_, v___y_651_, v___y_653_, v___y_655_, v___y_652_, v___y_657_, v___x_658_);
v___y_630_ = v___y_650_;
v___y_631_ = v___y_656_;
v_h_632_ = v___x_659_;
goto v___jp_629_;
}
v___jp_660_:
{
lean_object* v___x_671_; lean_object* v___x_672_; 
v___x_671_ = l_Int_Internal_Linear_Poly_div(v___y_665_, v___y_663_);
lean_inc_ref(v___x_671_);
v___x_672_ = l_Int_Internal_Linear_Poly_denoteExpr___redArg(v___y_667_, v___x_671_);
if (lean_obj_tag(v___x_672_) == 0)
{
lean_object* v_a_673_; lean_object* v___x_674_; lean_object* v___x_675_; 
v_a_673_ = lean_ctor_get(v___x_672_, 0);
lean_inc(v_a_673_);
lean_dec_ref_known(v___x_672_, 1);
v___x_674_ = l_Lean_mkIntLit(v___y_666_);
v___x_675_ = l_Lean_mkIntLE(v_a_673_, v___x_674_);
if (v___y_670_ == 0)
{
lean_object* v___x_676_; 
v___x_676_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(v___y_668_, v_a_624_, v_a_625_, v_a_626_, v_a_627_);
if (lean_obj_tag(v___x_676_) == 0)
{
lean_object* v_a_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; uint8_t v___x_683_; 
v_a_677_ = lean_ctor_get(v___x_676_, 0);
lean_inc(v_a_677_);
lean_dec_ref_known(v___x_676_, 1);
v___x_678_ = lean_box(0);
v___x_679_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__2, &l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__2_once, _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__2);
v___x_680_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v___y_669_);
v___x_681_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v___y_661_);
v___x_682_ = l_Lean_Meta_Simp_Arith_Int_ofPoly(v___x_671_);
v___x_683_ = lean_int_dec_le(v___y_666_, v___y_665_);
if (v___x_683_ == 0)
{
lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_684_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__15));
v___x_685_ = l_Lean_Level_ofNat(v___y_664_);
v___x_686_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_686_, 0, v___x_685_);
lean_ctor_set(v___x_686_, 1, v___x_678_);
v___x_687_ = l_Lean_Expr_const___override(v___x_684_, v___x_686_);
v___x_688_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20);
v___x_689_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23);
v___x_690_ = lean_int_neg(v___y_665_);
lean_dec(v___y_665_);
v___x_691_ = l_Int_toNat(v___x_690_);
lean_dec(v___x_690_);
v___x_692_ = l_Lean_instToExprInt_mkNat(v___x_691_);
v___x_693_ = l_Lean_mkApp3(v___x_687_, v___x_688_, v___x_689_, v___x_692_);
v___y_650_ = v___y_662_;
v___y_651_ = v_a_677_;
v___y_652_ = v___x_682_;
v___y_653_ = v___x_680_;
v___y_654_ = v___x_679_;
v___y_655_ = v___x_681_;
v___y_656_ = v___x_675_;
v___y_657_ = v___x_693_;
goto v___jp_649_;
}
else
{
lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_694_ = l_Int_toNat(v___y_665_);
lean_dec(v___y_665_);
v___x_695_ = l_Lean_instToExprInt_mkNat(v___x_694_);
v___y_650_ = v___y_662_;
v___y_651_ = v_a_677_;
v___y_652_ = v___x_682_;
v___y_653_ = v___x_680_;
v___y_654_ = v___x_679_;
v___y_655_ = v___x_681_;
v___y_656_ = v___x_675_;
v___y_657_ = v___x_695_;
goto v___jp_649_;
}
}
else
{
lean_object* v_a_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_703_; 
lean_dec_ref(v___x_675_);
lean_dec_ref(v___x_671_);
lean_dec_ref(v___y_669_);
lean_dec(v___y_665_);
lean_dec_ref(v___y_662_);
lean_dec_ref(v___y_661_);
v_a_696_ = lean_ctor_get(v___x_676_, 0);
v_isSharedCheck_703_ = !lean_is_exclusive(v___x_676_);
if (v_isSharedCheck_703_ == 0)
{
v___x_698_ = v___x_676_;
v_isShared_699_ = v_isSharedCheck_703_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_a_696_);
lean_dec(v___x_676_);
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
v___x_704_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(v___y_668_, v_a_624_, v_a_625_, v_a_626_, v_a_627_);
if (lean_obj_tag(v___x_704_) == 0)
{
lean_object* v_a_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; uint8_t v___x_711_; 
v_a_705_ = lean_ctor_get(v___x_704_, 0);
lean_inc(v_a_705_);
lean_dec_ref_known(v___x_704_, 1);
v___x_706_ = lean_box(0);
v___x_707_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__5, &l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__5_once, _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__5);
v___x_708_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v___y_669_);
v___x_709_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v___y_661_);
v___x_710_ = l_Lean_Meta_Simp_Arith_Int_ofPoly(v___x_671_);
v___x_711_ = lean_int_dec_le(v___y_666_, v___y_665_);
if (v___x_711_ == 0)
{
lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; 
v___x_712_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__15));
v___x_713_ = l_Lean_Level_ofNat(v___y_664_);
v___x_714_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_714_, 0, v___x_713_);
lean_ctor_set(v___x_714_, 1, v___x_706_);
v___x_715_ = l_Lean_Expr_const___override(v___x_712_, v___x_714_);
v___x_716_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20);
v___x_717_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23);
v___x_718_ = lean_int_neg(v___y_665_);
lean_dec(v___y_665_);
v___x_719_ = l_Int_toNat(v___x_718_);
lean_dec(v___x_718_);
v___x_720_ = l_Lean_instToExprInt_mkNat(v___x_719_);
v___x_721_ = l_Lean_mkApp3(v___x_715_, v___x_716_, v___x_717_, v___x_720_);
v___y_639_ = v___y_662_;
v___y_640_ = v___x_707_;
v___y_641_ = v_a_705_;
v___y_642_ = v___x_709_;
v___y_643_ = v___x_708_;
v___y_644_ = v___x_710_;
v___y_645_ = v___x_675_;
v___y_646_ = v___x_721_;
goto v___jp_638_;
}
else
{
lean_object* v___x_722_; lean_object* v___x_723_; 
v___x_722_ = l_Int_toNat(v___y_665_);
lean_dec(v___y_665_);
v___x_723_ = l_Lean_instToExprInt_mkNat(v___x_722_);
v___y_639_ = v___y_662_;
v___y_640_ = v___x_707_;
v___y_641_ = v_a_705_;
v___y_642_ = v___x_709_;
v___y_643_ = v___x_708_;
v___y_644_ = v___x_710_;
v___y_645_ = v___x_675_;
v___y_646_ = v___x_723_;
goto v___jp_638_;
}
}
else
{
lean_object* v_a_724_; lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_731_; 
lean_dec_ref(v___x_675_);
lean_dec_ref(v___x_671_);
lean_dec_ref(v___y_669_);
lean_dec(v___y_665_);
lean_dec_ref(v___y_662_);
lean_dec_ref(v___y_661_);
v_a_724_ = lean_ctor_get(v___x_704_, 0);
v_isSharedCheck_731_ = !lean_is_exclusive(v___x_704_);
if (v_isSharedCheck_731_ == 0)
{
v___x_726_ = v___x_704_;
v_isShared_727_ = v_isSharedCheck_731_;
goto v_resetjp_725_;
}
else
{
lean_inc(v_a_724_);
lean_dec(v___x_704_);
v___x_726_ = lean_box(0);
v_isShared_727_ = v_isSharedCheck_731_;
goto v_resetjp_725_;
}
v_resetjp_725_:
{
lean_object* v___x_729_; 
if (v_isShared_727_ == 0)
{
v___x_729_ = v___x_726_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v_a_724_);
v___x_729_ = v_reuseFailAlloc_730_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
return v___x_729_;
}
}
}
}
}
else
{
lean_object* v_a_732_; lean_object* v___x_734_; uint8_t v_isShared_735_; uint8_t v_isSharedCheck_739_; 
lean_dec_ref(v___x_671_);
lean_dec_ref(v___y_669_);
lean_dec_ref(v___y_668_);
lean_dec(v___y_665_);
lean_dec_ref(v___y_662_);
lean_dec_ref(v___y_661_);
v_a_732_ = lean_ctor_get(v___x_672_, 0);
v_isSharedCheck_739_ = !lean_is_exclusive(v___x_672_);
if (v_isSharedCheck_739_ == 0)
{
v___x_734_ = v___x_672_;
v_isShared_735_ = v_isSharedCheck_739_;
goto v_resetjp_733_;
}
else
{
lean_inc(v_a_732_);
lean_dec(v___x_672_);
v___x_734_ = lean_box(0);
v_isShared_735_ = v_isSharedCheck_739_;
goto v_resetjp_733_;
}
v_resetjp_733_:
{
lean_object* v___x_737_; 
if (v_isShared_735_ == 0)
{
v___x_737_ = v___x_734_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v_a_732_);
v___x_737_ = v_reuseFailAlloc_738_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
return v___x_737_;
}
}
}
}
v___jp_740_:
{
lean_object* v___x_747_; lean_object* v___x_748_; uint8_t v___x_749_; 
v___x_747_ = l_Int_Internal_Linear_Poly_gcdCoeffs_x27(v___y_743_);
v___x_748_ = lean_unsigned_to_nat(1u);
v___x_749_ = lean_nat_dec_eq(v___x_747_, v___x_748_);
if (v___x_749_ == 0)
{
lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; uint8_t v___x_755_; 
v___x_750_ = l_Int_Internal_Linear_Poly_getConst(v___y_743_);
v___x_751_ = lean_nat_to_int(v___x_747_);
v___x_752_ = lean_int_emod(v___x_750_, v___x_751_);
lean_dec(v___x_750_);
v___x_753_ = lean_unsigned_to_nat(0u);
v___x_754_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6);
v___x_755_ = lean_int_dec_eq(v___x_752_, v___x_754_);
lean_dec(v___x_752_);
if (v___x_755_ == 0)
{
uint8_t v___x_756_; 
v___x_756_ = 1;
v___y_661_ = v___y_741_;
v___y_662_ = v___y_742_;
v___y_663_ = v___y_743_;
v___y_664_ = v___x_753_;
v___y_665_ = v___x_751_;
v___y_666_ = v___x_754_;
v___y_667_ = v___y_744_;
v___y_668_ = v___y_745_;
v___y_669_ = v___y_746_;
v___y_670_ = v___x_756_;
goto v___jp_660_;
}
else
{
v___y_661_ = v___y_741_;
v___y_662_ = v___y_742_;
v___y_663_ = v___y_743_;
v___y_664_ = v___x_753_;
v___y_665_ = v___x_751_;
v___y_666_ = v___x_754_;
v___y_667_ = v___y_744_;
v___y_668_ = v___y_745_;
v___y_669_ = v___y_746_;
v___y_670_ = v___x_749_;
goto v___jp_660_;
}
}
else
{
lean_object* v___x_757_; 
lean_dec(v___x_747_);
lean_inc_ref(v___y_743_);
v___x_757_ = l_Int_Internal_Linear_Poly_denoteExpr___redArg(v___y_744_, v___y_743_);
if (lean_obj_tag(v___x_757_) == 0)
{
lean_object* v_a_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; 
v_a_758_ = lean_ctor_get(v___x_757_, 0);
lean_inc(v_a_758_);
lean_dec_ref_known(v___x_757_, 1);
v___x_759_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__24, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__24_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__24);
v___x_760_ = l_Lean_mkIntLE(v_a_758_, v___x_759_);
v___x_761_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(v___y_745_, v_a_624_, v_a_625_, v_a_626_, v_a_627_);
if (lean_obj_tag(v___x_761_) == 0)
{
lean_object* v_a_762_; lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_779_; 
v_a_762_ = lean_ctor_get(v___x_761_, 0);
v_isSharedCheck_779_ = !lean_is_exclusive(v___x_761_);
if (v_isSharedCheck_779_ == 0)
{
v___x_764_ = v___x_761_;
v_isShared_765_ = v_isSharedCheck_779_;
goto v_resetjp_763_;
}
else
{
lean_inc(v_a_762_);
lean_dec(v___x_761_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_779_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_777_; 
v___x_766_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__8, &l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__8_once, _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__8);
v___x_767_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v___y_746_);
v___x_768_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v___y_741_);
v___x_769_ = l_Lean_Meta_Simp_Arith_Int_ofPoly(v___y_743_);
v___x_770_ = l_Lean_eagerReflBoolTrue;
v___x_771_ = l_Lean_mkApp5(v___x_766_, v_a_762_, v___x_767_, v___x_768_, v___x_769_, v___x_770_);
lean_inc_ref(v___x_760_);
v___x_772_ = l_Lean_mkPropEq(v___y_742_, v___x_760_);
v___x_773_ = l_Lean_Meta_mkExpectedPropHint(v___x_771_, v___x_772_);
v___x_774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_774_, 0, v___x_760_);
lean_ctor_set(v___x_774_, 1, v___x_773_);
v___x_775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_775_, 0, v___x_774_);
if (v_isShared_765_ == 0)
{
lean_ctor_set(v___x_764_, 0, v___x_775_);
v___x_777_ = v___x_764_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v___x_775_);
v___x_777_ = v_reuseFailAlloc_778_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
return v___x_777_;
}
}
}
else
{
lean_object* v_a_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_787_; 
lean_dec_ref(v___x_760_);
lean_dec_ref(v___y_746_);
lean_dec_ref(v___y_743_);
lean_dec_ref(v___y_742_);
lean_dec_ref(v___y_741_);
v_a_780_ = lean_ctor_get(v___x_761_, 0);
v_isSharedCheck_787_ = !lean_is_exclusive(v___x_761_);
if (v_isSharedCheck_787_ == 0)
{
v___x_782_ = v___x_761_;
v_isShared_783_ = v_isSharedCheck_787_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_a_780_);
lean_dec(v___x_761_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_787_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
lean_object* v___x_785_; 
if (v_isShared_783_ == 0)
{
v___x_785_ = v___x_782_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v_a_780_);
v___x_785_ = v_reuseFailAlloc_786_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
return v___x_785_;
}
}
}
}
else
{
lean_object* v_a_788_; lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_795_; 
lean_dec_ref(v___y_746_);
lean_dec_ref(v___y_745_);
lean_dec_ref(v___y_743_);
lean_dec_ref(v___y_742_);
lean_dec_ref(v___y_741_);
v_a_788_ = lean_ctor_get(v___x_757_, 0);
v_isSharedCheck_795_ = !lean_is_exclusive(v___x_757_);
if (v_isSharedCheck_795_ == 0)
{
v___x_790_ = v___x_757_;
v_isShared_791_ = v_isSharedCheck_795_;
goto v_resetjp_789_;
}
else
{
lean_inc(v_a_788_);
lean_dec(v___x_757_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_795_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v___x_793_; 
if (v_isShared_791_ == 0)
{
v___x_793_ = v___x_790_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v_a_788_);
v___x_793_ = v_reuseFailAlloc_794_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
return v___x_793_;
}
}
}
}
}
v___jp_797_:
{
lean_object* v___x_799_; 
v___x_799_ = l_Lean_Meta_Simp_Arith_Int_leCnstr_x3f(v_e_622_, v_a_624_, v_a_625_, v_a_626_, v_a_627_);
if (lean_obj_tag(v___x_799_) == 0)
{
lean_object* v_a_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_927_; 
v_a_800_ = lean_ctor_get(v___x_799_, 0);
v_isSharedCheck_927_ = !lean_is_exclusive(v___x_799_);
if (v_isSharedCheck_927_ == 0)
{
v___x_802_ = v___x_799_;
v_isShared_803_ = v_isSharedCheck_927_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_a_800_);
lean_dec(v___x_799_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_927_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
if (lean_obj_tag(v_a_800_) == 1)
{
lean_object* v_val_804_; lean_object* v___x_806_; uint8_t v_isShared_807_; uint8_t v_isSharedCheck_922_; 
lean_del_object(v___x_802_);
v_val_804_ = lean_ctor_get(v_a_800_, 0);
v_isSharedCheck_922_ = !lean_is_exclusive(v_a_800_);
if (v_isSharedCheck_922_ == 0)
{
v___x_806_ = v_a_800_;
v_isShared_807_ = v_isSharedCheck_922_;
goto v_resetjp_805_;
}
else
{
lean_inc(v_val_804_);
lean_dec(v_a_800_);
v___x_806_ = lean_box(0);
v_isShared_807_ = v_isSharedCheck_922_;
goto v_resetjp_805_;
}
v_resetjp_805_:
{
lean_object* v_snd_808_; lean_object* v_fst_809_; lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_921_; 
v_snd_808_ = lean_ctor_get(v_val_804_, 1);
v_fst_809_ = lean_ctor_get(v_val_804_, 0);
v_isSharedCheck_921_ = !lean_is_exclusive(v_val_804_);
if (v_isSharedCheck_921_ == 0)
{
v___x_811_ = v_val_804_;
v_isShared_812_ = v_isSharedCheck_921_;
goto v_resetjp_810_;
}
else
{
lean_inc(v_snd_808_);
lean_inc(v_fst_809_);
lean_dec(v_val_804_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_921_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
lean_object* v_fst_813_; lean_object* v_snd_814_; lean_object* v___x_816_; uint8_t v_isShared_817_; uint8_t v_isSharedCheck_920_; 
v_fst_813_ = lean_ctor_get(v_snd_808_, 0);
v_snd_814_ = lean_ctor_get(v_snd_808_, 1);
v_isSharedCheck_920_ = !lean_is_exclusive(v_snd_808_);
if (v_isSharedCheck_920_ == 0)
{
v___x_816_ = v_snd_808_;
v_isShared_817_ = v_isSharedCheck_920_;
goto v_resetjp_815_;
}
else
{
lean_inc(v_snd_814_);
lean_inc(v_fst_813_);
lean_dec(v_snd_808_);
v___x_816_ = lean_box(0);
v_isShared_817_ = v_isSharedCheck_920_;
goto v_resetjp_815_;
}
v_resetjp_815_:
{
lean_object* v___f_818_; lean_object* v___x_819_; 
lean_inc(v_snd_814_);
v___f_818_ = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__0___boxed), 3, 2);
lean_closure_set(v___f_818_, 0, v___x_796_);
lean_closure_set(v___f_818_, 1, v_snd_814_);
lean_inc(v_fst_809_);
lean_inc_ref(v___f_818_);
v___x_819_ = l_Int_Internal_Linear_Expr_denoteExpr___redArg(v___f_818_, v_fst_809_);
if (lean_obj_tag(v___x_819_) == 0)
{
lean_object* v_a_820_; lean_object* v___x_821_; 
v_a_820_ = lean_ctor_get(v___x_819_, 0);
lean_inc(v_a_820_);
lean_dec_ref_known(v___x_819_, 1);
lean_inc(v_fst_813_);
lean_inc_ref(v___f_818_);
v___x_821_ = l_Int_Internal_Linear_Expr_denoteExpr___redArg(v___f_818_, v_fst_813_);
if (lean_obj_tag(v___x_821_) == 0)
{
lean_object* v_a_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_903_; 
v_a_822_ = lean_ctor_get(v___x_821_, 0);
v_isSharedCheck_903_ = !lean_is_exclusive(v___x_821_);
if (v_isSharedCheck_903_ == 0)
{
v___x_824_ = v___x_821_;
v_isShared_825_ = v_isSharedCheck_903_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_a_822_);
lean_dec(v___x_821_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_903_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
lean_object* v___x_826_; lean_object* v___x_828_; 
v___x_826_ = l_Lean_mkIntLE(v_a_820_, v_a_822_);
lean_inc(v_fst_813_);
lean_inc(v_fst_809_);
if (v_isShared_812_ == 0)
{
lean_ctor_set_tag(v___x_811_, 3);
lean_ctor_set(v___x_811_, 1, v_fst_813_);
v___x_828_ = v___x_811_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v_fst_809_);
lean_ctor_set(v_reuseFailAlloc_902_, 1, v_fst_813_);
v___x_828_ = v_reuseFailAlloc_902_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
lean_object* v___x_829_; uint8_t v___x_830_; 
v___x_829_ = l_Int_Internal_Linear_Expr_norm(v___x_828_);
lean_dec_ref(v___x_828_);
v___x_830_ = l_Int_Internal_Linear_Poly_isUnsatLe(v___x_829_);
if (v___x_830_ == 0)
{
uint8_t v___x_831_; 
v___x_831_ = l_Int_Internal_Linear_Poly_isValidLe(v___x_829_);
if (v___x_831_ == 0)
{
lean_del_object(v___x_816_);
lean_del_object(v___x_806_);
if (v___y_798_ == 0)
{
lean_del_object(v___x_824_);
v___y_741_ = v_fst_813_;
v___y_742_ = v___x_826_;
v___y_743_ = v___x_829_;
v___y_744_ = v___f_818_;
v___y_745_ = v_snd_814_;
v___y_746_ = v_fst_809_;
goto v___jp_740_;
}
else
{
lean_object* v___x_832_; uint8_t v___x_833_; 
lean_inc_ref(v___x_829_);
v___x_832_ = l_Int_Internal_Linear_Poly_toExpr(v___x_829_);
v___x_833_ = l_Int_Internal_Linear_instBEqExpr_beq(v___x_832_, v_fst_809_);
lean_dec_ref(v___x_832_);
if (v___x_833_ == 0)
{
lean_del_object(v___x_824_);
v___y_741_ = v_fst_813_;
v___y_742_ = v___x_826_;
v___y_743_ = v___x_829_;
v___y_744_ = v___f_818_;
v___y_745_ = v_snd_814_;
v___y_746_ = v_fst_809_;
goto v___jp_740_;
}
else
{
lean_object* v___x_834_; uint8_t v___x_835_; 
v___x_834_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__36, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__36_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__36);
v___x_835_ = l_Int_Internal_Linear_instBEqExpr_beq(v_fst_813_, v___x_834_);
if (v___x_835_ == 0)
{
lean_del_object(v___x_824_);
v___y_741_ = v_fst_813_;
v___y_742_ = v___x_826_;
v___y_743_ = v___x_829_;
v___y_744_ = v___f_818_;
v___y_745_ = v_snd_814_;
v___y_746_ = v_fst_809_;
goto v___jp_740_;
}
else
{
lean_object* v___x_836_; lean_object* v___x_838_; 
lean_dec_ref(v___x_829_);
lean_dec_ref(v___x_826_);
lean_dec_ref(v___f_818_);
lean_dec(v_snd_814_);
lean_dec(v_fst_813_);
lean_dec(v_fst_809_);
v___x_836_ = lean_box(0);
if (v_isShared_825_ == 0)
{
lean_ctor_set(v___x_824_, 0, v___x_836_);
v___x_838_ = v___x_824_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v___x_836_);
v___x_838_ = v_reuseFailAlloc_839_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
return v___x_838_;
}
}
}
}
}
else
{
lean_object* v___x_840_; lean_object* v___x_841_; 
lean_dec_ref(v___x_829_);
lean_del_object(v___x_824_);
lean_dec_ref(v___f_818_);
v___x_840_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__39, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__39_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__39);
v___x_841_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(v_snd_814_, v_a_624_, v_a_625_, v_a_626_, v_a_627_);
if (lean_obj_tag(v___x_841_) == 0)
{
lean_object* v_a_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_862_; 
v_a_842_ = lean_ctor_get(v___x_841_, 0);
v_isSharedCheck_862_ = !lean_is_exclusive(v___x_841_);
if (v_isSharedCheck_862_ == 0)
{
v___x_844_ = v___x_841_;
v_isShared_845_ = v_isSharedCheck_862_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_a_842_);
lean_dec(v___x_841_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_862_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_854_; 
v___x_846_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__11, &l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__11_once, _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__11);
v___x_847_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_809_);
v___x_848_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_813_);
v___x_849_ = l_Lean_eagerReflBoolTrue;
v___x_850_ = l_Lean_mkApp4(v___x_846_, v_a_842_, v___x_847_, v___x_848_, v___x_849_);
v___x_851_ = l_Lean_mkPropEq(v___x_826_, v___x_840_);
v___x_852_ = l_Lean_Meta_mkExpectedPropHint(v___x_850_, v___x_851_);
if (v_isShared_817_ == 0)
{
lean_ctor_set(v___x_816_, 1, v___x_852_);
lean_ctor_set(v___x_816_, 0, v___x_840_);
v___x_854_ = v___x_816_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v___x_840_);
lean_ctor_set(v_reuseFailAlloc_861_, 1, v___x_852_);
v___x_854_ = v_reuseFailAlloc_861_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
lean_object* v___x_856_; 
if (v_isShared_807_ == 0)
{
lean_ctor_set(v___x_806_, 0, v___x_854_);
v___x_856_ = v___x_806_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v___x_854_);
v___x_856_ = v_reuseFailAlloc_860_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
lean_object* v___x_858_; 
if (v_isShared_845_ == 0)
{
lean_ctor_set(v___x_844_, 0, v___x_856_);
v___x_858_ = v___x_844_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v___x_856_);
v___x_858_ = v_reuseFailAlloc_859_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
return v___x_858_;
}
}
}
}
}
else
{
lean_object* v_a_863_; lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_870_; 
lean_dec_ref(v___x_826_);
lean_del_object(v___x_816_);
lean_dec(v_fst_813_);
lean_dec(v_fst_809_);
lean_del_object(v___x_806_);
v_a_863_ = lean_ctor_get(v___x_841_, 0);
v_isSharedCheck_870_ = !lean_is_exclusive(v___x_841_);
if (v_isSharedCheck_870_ == 0)
{
v___x_865_ = v___x_841_;
v_isShared_866_ = v_isSharedCheck_870_;
goto v_resetjp_864_;
}
else
{
lean_inc(v_a_863_);
lean_dec(v___x_841_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_870_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
lean_object* v___x_868_; 
if (v_isShared_866_ == 0)
{
v___x_868_ = v___x_865_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v_a_863_);
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
lean_object* v___x_871_; lean_object* v___x_872_; 
lean_dec_ref(v___x_829_);
lean_del_object(v___x_824_);
lean_dec_ref(v___f_818_);
v___x_871_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__9, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__9_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__9);
v___x_872_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(v_snd_814_, v_a_624_, v_a_625_, v_a_626_, v_a_627_);
if (lean_obj_tag(v___x_872_) == 0)
{
lean_object* v_a_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_893_; 
v_a_873_ = lean_ctor_get(v___x_872_, 0);
v_isSharedCheck_893_ = !lean_is_exclusive(v___x_872_);
if (v_isSharedCheck_893_ == 0)
{
v___x_875_ = v___x_872_;
v_isShared_876_ = v_isSharedCheck_893_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_a_873_);
lean_dec(v___x_872_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_893_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_885_; 
v___x_877_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__14, &l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__14_once, _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__14);
v___x_878_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_809_);
v___x_879_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_813_);
v___x_880_ = l_Lean_eagerReflBoolTrue;
v___x_881_ = l_Lean_mkApp4(v___x_877_, v_a_873_, v___x_878_, v___x_879_, v___x_880_);
v___x_882_ = l_Lean_mkPropEq(v___x_826_, v___x_871_);
v___x_883_ = l_Lean_Meta_mkExpectedPropHint(v___x_881_, v___x_882_);
if (v_isShared_817_ == 0)
{
lean_ctor_set(v___x_816_, 1, v___x_883_);
lean_ctor_set(v___x_816_, 0, v___x_871_);
v___x_885_ = v___x_816_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v___x_871_);
lean_ctor_set(v_reuseFailAlloc_892_, 1, v___x_883_);
v___x_885_ = v_reuseFailAlloc_892_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
lean_object* v___x_887_; 
if (v_isShared_807_ == 0)
{
lean_ctor_set(v___x_806_, 0, v___x_885_);
v___x_887_ = v___x_806_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v___x_885_);
v___x_887_ = v_reuseFailAlloc_891_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
lean_object* v___x_889_; 
if (v_isShared_876_ == 0)
{
lean_ctor_set(v___x_875_, 0, v___x_887_);
v___x_889_ = v___x_875_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v___x_887_);
v___x_889_ = v_reuseFailAlloc_890_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
return v___x_889_;
}
}
}
}
}
else
{
lean_object* v_a_894_; lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_901_; 
lean_dec_ref(v___x_826_);
lean_del_object(v___x_816_);
lean_dec(v_fst_813_);
lean_dec(v_fst_809_);
lean_del_object(v___x_806_);
v_a_894_ = lean_ctor_get(v___x_872_, 0);
v_isSharedCheck_901_ = !lean_is_exclusive(v___x_872_);
if (v_isSharedCheck_901_ == 0)
{
v___x_896_ = v___x_872_;
v_isShared_897_ = v_isSharedCheck_901_;
goto v_resetjp_895_;
}
else
{
lean_inc(v_a_894_);
lean_dec(v___x_872_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_901_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
lean_object* v___x_899_; 
if (v_isShared_897_ == 0)
{
v___x_899_ = v___x_896_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v_a_894_);
v___x_899_ = v_reuseFailAlloc_900_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
return v___x_899_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_904_; lean_object* v___x_906_; uint8_t v_isShared_907_; uint8_t v_isSharedCheck_911_; 
lean_dec(v_a_820_);
lean_dec_ref(v___f_818_);
lean_del_object(v___x_816_);
lean_dec(v_snd_814_);
lean_dec(v_fst_813_);
lean_del_object(v___x_811_);
lean_dec(v_fst_809_);
lean_del_object(v___x_806_);
v_a_904_ = lean_ctor_get(v___x_821_, 0);
v_isSharedCheck_911_ = !lean_is_exclusive(v___x_821_);
if (v_isSharedCheck_911_ == 0)
{
v___x_906_ = v___x_821_;
v_isShared_907_ = v_isSharedCheck_911_;
goto v_resetjp_905_;
}
else
{
lean_inc(v_a_904_);
lean_dec(v___x_821_);
v___x_906_ = lean_box(0);
v_isShared_907_ = v_isSharedCheck_911_;
goto v_resetjp_905_;
}
v_resetjp_905_:
{
lean_object* v___x_909_; 
if (v_isShared_907_ == 0)
{
v___x_909_ = v___x_906_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v_a_904_);
v___x_909_ = v_reuseFailAlloc_910_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
return v___x_909_;
}
}
}
}
else
{
lean_object* v_a_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_919_; 
lean_dec_ref(v___f_818_);
lean_del_object(v___x_816_);
lean_dec(v_snd_814_);
lean_dec(v_fst_813_);
lean_del_object(v___x_811_);
lean_dec(v_fst_809_);
lean_del_object(v___x_806_);
v_a_912_ = lean_ctor_get(v___x_819_, 0);
v_isSharedCheck_919_ = !lean_is_exclusive(v___x_819_);
if (v_isSharedCheck_919_ == 0)
{
v___x_914_ = v___x_819_;
v_isShared_915_ = v_isSharedCheck_919_;
goto v_resetjp_913_;
}
else
{
lean_inc(v_a_912_);
lean_dec(v___x_819_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_919_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
lean_object* v___x_917_; 
if (v_isShared_915_ == 0)
{
v___x_917_ = v___x_914_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v_a_912_);
v___x_917_ = v_reuseFailAlloc_918_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
return v___x_917_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_923_; lean_object* v___x_925_; 
lean_dec(v_a_800_);
v___x_923_ = lean_box(0);
if (v_isShared_803_ == 0)
{
lean_ctor_set(v___x_802_, 0, v___x_923_);
v___x_925_ = v___x_802_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v___x_923_);
v___x_925_ = v_reuseFailAlloc_926_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
return v___x_925_;
}
}
}
}
else
{
lean_object* v_a_928_; lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_935_; 
v_a_928_ = lean_ctor_get(v___x_799_, 0);
v_isSharedCheck_935_ = !lean_is_exclusive(v___x_799_);
if (v_isSharedCheck_935_ == 0)
{
v___x_930_ = v___x_799_;
v_isShared_931_ = v_isSharedCheck_935_;
goto v_resetjp_929_;
}
else
{
lean_inc(v_a_928_);
lean_dec(v___x_799_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_935_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
lean_object* v___x_933_; 
if (v_isShared_931_ == 0)
{
v___x_933_ = v___x_930_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v_a_928_);
v___x_933_ = v_reuseFailAlloc_934_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
return v___x_933_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Simp_Arith_Int_simpLe_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_622_ = stack[0].m_obj;
uint8_t v_checkIfModified_623_ = stack[1].m_num;
lean_object* v_a_624_ = stack[2].m_obj;
lean_object* v_a_625_ = stack[3].m_obj;
lean_object* v_a_626_ = stack[4].m_obj;
lean_object* v_a_627_ = stack[5].m_obj;
lean_object* v_res_938_;
v_res_938_ = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f(v_e_622_, v_checkIfModified_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_);
stack->m_obj
 = v_res_938_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___boxed(lean_object* v_e_939_, lean_object* v_checkIfModified_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_){
_start:
{
uint8_t v_checkIfModified_boxed_946_; lean_object* v_res_947_; 
v_checkIfModified_boxed_946_ = lean_unbox(v_checkIfModified_940_);
v_res_947_ = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f(v_e_939_, v_checkIfModified_boxed_946_, v_a_941_, v_a_942_, v_a_943_, v_a_944_);
lean_dec(v_a_944_);
lean_dec_ref(v_a_943_);
lean_dec(v_a_942_);
lean_dec_ref(v_a_941_);
return v_res_947_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__3(void){
_start:
{
lean_object* v___x_953_; lean_object* v___x_954_; 
v___x_953_ = lean_box(0);
v___x_954_ = l_Lean_Level_succ___override(v___x_953_);
return v___x_954_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__4(void){
_start:
{
lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; 
v___x_955_ = lean_box(0);
v___x_956_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__3, &l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__3_once, _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__3);
v___x_957_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_957_, 0, v___x_956_);
lean_ctor_set(v___x_957_, 1, v___x_955_);
return v___x_957_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__5(void){
_start:
{
lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; 
v___x_958_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__4, &l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__4_once, _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__4);
v___x_959_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__2));
v___x_960_ = l_Lean_mkConst(v___x_959_, v___x_958_);
return v___x_960_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__6(void){
_start:
{
lean_object* v___x_961_; lean_object* v___x_962_; 
v___x_961_ = lean_box(0);
v___x_962_ = l_Lean_mkSort(v___x_961_);
return v___x_962_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__18(void){
_start:
{
lean_object* v___x_981_; lean_object* v___x_982_; 
v___x_981_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__31, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__31_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__31);
v___x_982_ = l_Lean_mkIntLit(v___x_981_);
return v___x_982_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__21(void){
_start:
{
lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; 
v___x_987_ = lean_box(0);
v___x_988_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__20));
v___x_989_ = l_Lean_mkConst(v___x_988_, v___x_987_);
return v___x_989_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__24(void){
_start:
{
lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; 
v___x_994_ = lean_box(0);
v___x_995_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__23));
v___x_996_ = l_Lean_mkConst(v___x_995_, v___x_994_);
return v___x_996_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__27(void){
_start:
{
lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; 
v___x_1001_ = lean_box(0);
v___x_1002_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__26));
v___x_1003_ = l_Lean_mkConst(v___x_1002_, v___x_1001_);
return v___x_1003_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__30(void){
_start:
{
lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; 
v___x_1008_ = lean_box(0);
v___x_1009_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__29));
v___x_1010_ = l_Lean_mkConst(v___x_1009_, v___x_1008_);
return v___x_1010_;
}
}
lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f(lean_object* v_e_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_){
_start:
{
lean_object* v_val_1018_; lean_object* v_h_u2081_1019_; lean_object* v___y_1020_; lean_object* v___y_1021_; lean_object* v___y_1022_; lean_object* v___y_1023_; lean_object* v___x_1062_; lean_object* v___x_1063_; uint8_t v___x_1064_; 
v___x_1062_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__8));
v___x_1063_ = lean_unsigned_to_nat(1u);
v___x_1064_ = l_Lean_Expr_isAppOfArity(v_e_1011_, v___x_1062_, v___x_1063_);
if (v___x_1064_ == 0)
{
uint8_t v___x_1065_; lean_object* v___x_1066_; 
v___x_1065_ = 1;
v___x_1066_ = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f(v_e_1011_, v___x_1065_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_);
return v___x_1066_;
}
else
{
lean_object* v___x_1067_; lean_object* v___x_1068_; 
v___x_1067_ = l_Lean_Expr_appArg_x21(v_e_1011_);
v___x_1068_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v___x_1067_, v_a_1013_);
if (lean_obj_tag(v___x_1068_) == 0)
{
lean_object* v_a_1069_; lean_object* v___x_1070_; uint8_t v___x_1071_; 
v_a_1069_ = lean_ctor_get(v___x_1068_, 0);
lean_inc(v_a_1069_);
lean_dec_ref_known(v___x_1068_, 1);
v___x_1070_ = l_Lean_Expr_cleanupAnnotations(v_a_1069_);
v___x_1071_ = l_Lean_Expr_isApp(v___x_1070_);
if (v___x_1071_ == 0)
{
lean_dec_ref(v___x_1070_);
lean_dec_ref(v_e_1011_);
goto v___jp_1059_;
}
else
{
lean_object* v_arg_1072_; lean_object* v___x_1073_; uint8_t v___x_1074_; 
v_arg_1072_ = lean_ctor_get(v___x_1070_, 1);
lean_inc_ref(v_arg_1072_);
v___x_1073_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1070_);
v___x_1074_ = l_Lean_Expr_isApp(v___x_1073_);
if (v___x_1074_ == 0)
{
lean_dec_ref(v___x_1073_);
lean_dec_ref(v_arg_1072_);
lean_dec_ref(v_e_1011_);
goto v___jp_1059_;
}
else
{
lean_object* v_arg_1075_; lean_object* v___x_1076_; uint8_t v___x_1077_; 
v_arg_1075_ = lean_ctor_get(v___x_1073_, 1);
lean_inc_ref(v_arg_1075_);
v___x_1076_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1073_);
v___x_1077_ = l_Lean_Expr_isApp(v___x_1076_);
if (v___x_1077_ == 0)
{
lean_dec_ref(v___x_1076_);
lean_dec_ref(v_arg_1075_);
lean_dec_ref(v_arg_1072_);
lean_dec_ref(v_e_1011_);
goto v___jp_1059_;
}
else
{
lean_object* v___x_1078_; uint8_t v___x_1079_; 
v___x_1078_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1076_);
v___x_1079_ = l_Lean_Expr_isApp(v___x_1078_);
if (v___x_1079_ == 0)
{
lean_dec_ref(v___x_1078_);
lean_dec_ref(v_arg_1075_);
lean_dec_ref(v_arg_1072_);
lean_dec_ref(v_e_1011_);
goto v___jp_1059_;
}
else
{
lean_object* v_arg_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; uint8_t v___x_1083_; 
v_arg_1080_ = lean_ctor_get(v___x_1078_, 1);
lean_inc_ref(v_arg_1080_);
v___x_1081_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1078_);
v___x_1082_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__11));
v___x_1083_ = l_Lean_Expr_isConstOf(v___x_1081_, v___x_1082_);
if (v___x_1083_ == 0)
{
lean_object* v___x_1084_; uint8_t v___x_1085_; 
v___x_1084_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__14));
v___x_1085_ = l_Lean_Expr_isConstOf(v___x_1081_, v___x_1084_);
if (v___x_1085_ == 0)
{
lean_object* v___x_1086_; uint8_t v___x_1087_; 
v___x_1086_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__17));
v___x_1087_ = l_Lean_Expr_isConstOf(v___x_1081_, v___x_1086_);
if (v___x_1087_ == 0)
{
lean_object* v___x_1088_; uint8_t v___x_1089_; 
v___x_1088_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__17));
v___x_1089_ = l_Lean_Expr_isConstOf(v___x_1081_, v___x_1088_);
lean_dec_ref(v___x_1081_);
if (v___x_1089_ == 0)
{
lean_dec_ref(v_arg_1080_);
lean_dec_ref(v_arg_1075_);
lean_dec_ref(v_arg_1072_);
lean_dec_ref(v_e_1011_);
goto v___jp_1059_;
}
else
{
lean_object* v___x_1090_; 
v___x_1090_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_1080_, v_a_1013_);
if (lean_obj_tag(v___x_1090_) == 0)
{
lean_object* v_a_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; uint8_t v___x_1094_; 
v_a_1091_ = lean_ctor_get(v___x_1090_, 0);
lean_inc(v_a_1091_);
lean_dec_ref_known(v___x_1090_, 1);
v___x_1092_ = l_Lean_Expr_cleanupAnnotations(v_a_1091_);
v___x_1093_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19));
v___x_1094_ = l_Lean_Expr_isConstOf(v___x_1092_, v___x_1093_);
lean_dec_ref(v___x_1092_);
if (v___x_1094_ == 0)
{
lean_dec_ref(v_arg_1075_);
lean_dec_ref(v_arg_1072_);
lean_dec_ref(v_e_1011_);
goto v___jp_1059_;
}
else
{
lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; 
v___x_1095_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__18, &l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__18_once, _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__18);
lean_inc_ref(v_arg_1072_);
v___x_1096_ = l_Lean_mkIntAdd(v_arg_1072_, v___x_1095_);
lean_inc_ref(v_arg_1075_);
v___x_1097_ = l_Lean_mkIntLE(v___x_1096_, v_arg_1075_);
v___x_1098_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__21, &l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__21_once, _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__21);
v___x_1099_ = l_Lean_mkAppB(v___x_1098_, v_arg_1075_, v_arg_1072_);
v_val_1018_ = v___x_1097_;
v_h_u2081_1019_ = v___x_1099_;
v___y_1020_ = v_a_1012_;
v___y_1021_ = v_a_1013_;
v___y_1022_ = v_a_1014_;
v___y_1023_ = v_a_1015_;
goto v___jp_1017_;
}
}
else
{
lean_object* v_a_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1107_; 
lean_dec_ref(v_arg_1075_);
lean_dec_ref(v_arg_1072_);
lean_dec_ref(v_e_1011_);
v_a_1100_ = lean_ctor_get(v___x_1090_, 0);
v_isSharedCheck_1107_ = !lean_is_exclusive(v___x_1090_);
if (v_isSharedCheck_1107_ == 0)
{
v___x_1102_ = v___x_1090_;
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_a_1100_);
lean_dec(v___x_1090_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v___x_1105_; 
if (v_isShared_1103_ == 0)
{
v___x_1105_ = v___x_1102_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v_a_1100_);
v___x_1105_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
return v___x_1105_;
}
}
}
}
}
else
{
lean_object* v___x_1108_; 
lean_dec_ref(v___x_1081_);
v___x_1108_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_1080_, v_a_1013_);
if (lean_obj_tag(v___x_1108_) == 0)
{
lean_object* v_a_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; uint8_t v___x_1112_; 
v_a_1109_ = lean_ctor_get(v___x_1108_, 0);
lean_inc(v_a_1109_);
lean_dec_ref_known(v___x_1108_, 1);
v___x_1110_ = l_Lean_Expr_cleanupAnnotations(v_a_1109_);
v___x_1111_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19));
v___x_1112_ = l_Lean_Expr_isConstOf(v___x_1110_, v___x_1111_);
lean_dec_ref(v___x_1110_);
if (v___x_1112_ == 0)
{
lean_dec_ref(v_arg_1075_);
lean_dec_ref(v_arg_1072_);
lean_dec_ref(v_e_1011_);
goto v___jp_1059_;
}
else
{
lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; 
v___x_1113_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__18, &l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__18_once, _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__18);
lean_inc_ref(v_arg_1075_);
v___x_1114_ = l_Lean_mkIntAdd(v_arg_1075_, v___x_1113_);
lean_inc_ref(v_arg_1072_);
v___x_1115_ = l_Lean_mkIntLE(v___x_1114_, v_arg_1072_);
v___x_1116_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__24, &l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__24_once, _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__24);
v___x_1117_ = l_Lean_mkAppB(v___x_1116_, v_arg_1075_, v_arg_1072_);
v_val_1018_ = v___x_1115_;
v_h_u2081_1019_ = v___x_1117_;
v___y_1020_ = v_a_1012_;
v___y_1021_ = v_a_1013_;
v___y_1022_ = v_a_1014_;
v___y_1023_ = v_a_1015_;
goto v___jp_1017_;
}
}
else
{
lean_object* v_a_1118_; lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1125_; 
lean_dec_ref(v_arg_1075_);
lean_dec_ref(v_arg_1072_);
lean_dec_ref(v_e_1011_);
v_a_1118_ = lean_ctor_get(v___x_1108_, 0);
v_isSharedCheck_1125_ = !lean_is_exclusive(v___x_1108_);
if (v_isSharedCheck_1125_ == 0)
{
v___x_1120_ = v___x_1108_;
v_isShared_1121_ = v_isSharedCheck_1125_;
goto v_resetjp_1119_;
}
else
{
lean_inc(v_a_1118_);
lean_dec(v___x_1108_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1125_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
lean_object* v___x_1123_; 
if (v_isShared_1121_ == 0)
{
v___x_1123_ = v___x_1120_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v_a_1118_);
v___x_1123_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
return v___x_1123_;
}
}
}
}
}
else
{
lean_object* v___x_1126_; 
lean_dec_ref(v___x_1081_);
v___x_1126_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_1080_, v_a_1013_);
if (lean_obj_tag(v___x_1126_) == 0)
{
lean_object* v_a_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; uint8_t v___x_1130_; 
v_a_1127_ = lean_ctor_get(v___x_1126_, 0);
lean_inc(v_a_1127_);
lean_dec_ref_known(v___x_1126_, 1);
v___x_1128_ = l_Lean_Expr_cleanupAnnotations(v_a_1127_);
v___x_1129_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19));
v___x_1130_ = l_Lean_Expr_isConstOf(v___x_1128_, v___x_1129_);
lean_dec_ref(v___x_1128_);
if (v___x_1130_ == 0)
{
lean_dec_ref(v_arg_1075_);
lean_dec_ref(v_arg_1072_);
lean_dec_ref(v_e_1011_);
goto v___jp_1059_;
}
else
{
lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; 
lean_inc_ref(v_arg_1075_);
lean_inc_ref(v_arg_1072_);
v___x_1131_ = l_Lean_mkIntLE(v_arg_1072_, v_arg_1075_);
v___x_1132_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__27, &l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__27_once, _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__27);
v___x_1133_ = l_Lean_mkAppB(v___x_1132_, v_arg_1075_, v_arg_1072_);
v_val_1018_ = v___x_1131_;
v_h_u2081_1019_ = v___x_1133_;
v___y_1020_ = v_a_1012_;
v___y_1021_ = v_a_1013_;
v___y_1022_ = v_a_1014_;
v___y_1023_ = v_a_1015_;
goto v___jp_1017_;
}
}
else
{
lean_object* v_a_1134_; lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1141_; 
lean_dec_ref(v_arg_1075_);
lean_dec_ref(v_arg_1072_);
lean_dec_ref(v_e_1011_);
v_a_1134_ = lean_ctor_get(v___x_1126_, 0);
v_isSharedCheck_1141_ = !lean_is_exclusive(v___x_1126_);
if (v_isSharedCheck_1141_ == 0)
{
v___x_1136_ = v___x_1126_;
v_isShared_1137_ = v_isSharedCheck_1141_;
goto v_resetjp_1135_;
}
else
{
lean_inc(v_a_1134_);
lean_dec(v___x_1126_);
v___x_1136_ = lean_box(0);
v_isShared_1137_ = v_isSharedCheck_1141_;
goto v_resetjp_1135_;
}
v_resetjp_1135_:
{
lean_object* v___x_1139_; 
if (v_isShared_1137_ == 0)
{
v___x_1139_ = v___x_1136_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v_a_1134_);
v___x_1139_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
return v___x_1139_;
}
}
}
}
}
else
{
lean_object* v___x_1142_; 
lean_dec_ref(v___x_1081_);
v___x_1142_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_1080_, v_a_1013_);
if (lean_obj_tag(v___x_1142_) == 0)
{
lean_object* v_a_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; uint8_t v___x_1146_; 
v_a_1143_ = lean_ctor_get(v___x_1142_, 0);
lean_inc(v_a_1143_);
lean_dec_ref_known(v___x_1142_, 1);
v___x_1144_ = l_Lean_Expr_cleanupAnnotations(v_a_1143_);
v___x_1145_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19));
v___x_1146_ = l_Lean_Expr_isConstOf(v___x_1144_, v___x_1145_);
lean_dec_ref(v___x_1144_);
if (v___x_1146_ == 0)
{
lean_dec_ref(v_arg_1075_);
lean_dec_ref(v_arg_1072_);
lean_dec_ref(v_e_1011_);
goto v___jp_1059_;
}
else
{
lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; 
lean_inc_ref(v_arg_1072_);
lean_inc_ref(v_arg_1075_);
v___x_1147_ = l_Lean_mkIntLE(v_arg_1075_, v_arg_1072_);
v___x_1148_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__30, &l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__30_once, _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__30);
v___x_1149_ = l_Lean_mkAppB(v___x_1148_, v_arg_1075_, v_arg_1072_);
v_val_1018_ = v___x_1147_;
v_h_u2081_1019_ = v___x_1149_;
v___y_1020_ = v_a_1012_;
v___y_1021_ = v_a_1013_;
v___y_1022_ = v_a_1014_;
v___y_1023_ = v_a_1015_;
goto v___jp_1017_;
}
}
else
{
lean_object* v_a_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1157_; 
lean_dec_ref(v_arg_1075_);
lean_dec_ref(v_arg_1072_);
lean_dec_ref(v_e_1011_);
v_a_1150_ = lean_ctor_get(v___x_1142_, 0);
v_isSharedCheck_1157_ = !lean_is_exclusive(v___x_1142_);
if (v_isSharedCheck_1157_ == 0)
{
v___x_1152_ = v___x_1142_;
v_isShared_1153_ = v_isSharedCheck_1157_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_a_1150_);
lean_dec(v___x_1142_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1157_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v___x_1155_; 
if (v_isShared_1153_ == 0)
{
v___x_1155_ = v___x_1152_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v_a_1150_);
v___x_1155_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
return v___x_1155_;
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
lean_object* v_a_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1165_; 
lean_dec_ref(v_e_1011_);
v_a_1158_ = lean_ctor_get(v___x_1068_, 0);
v_isSharedCheck_1165_ = !lean_is_exclusive(v___x_1068_);
if (v_isSharedCheck_1165_ == 0)
{
v___x_1160_ = v___x_1068_;
v_isShared_1161_ = v_isSharedCheck_1165_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_a_1158_);
lean_dec(v___x_1068_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1165_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
lean_object* v___x_1163_; 
if (v_isShared_1161_ == 0)
{
v___x_1163_ = v___x_1160_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v_a_1158_);
v___x_1163_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
return v___x_1163_;
}
}
}
}
v___jp_1017_:
{
uint8_t v___x_1024_; lean_object* v___x_1025_; 
v___x_1024_ = 0;
lean_inc_ref(v_val_1018_);
v___x_1025_ = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f(v_val_1018_, v___x_1024_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_);
if (lean_obj_tag(v___x_1025_) == 0)
{
lean_object* v_a_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1058_; 
v_a_1026_ = lean_ctor_get(v___x_1025_, 0);
v_isSharedCheck_1058_ = !lean_is_exclusive(v___x_1025_);
if (v_isSharedCheck_1058_ == 0)
{
v___x_1028_ = v___x_1025_;
v_isShared_1029_ = v_isSharedCheck_1058_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_a_1026_);
lean_dec(v___x_1025_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1058_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
if (lean_obj_tag(v_a_1026_) == 1)
{
lean_object* v_val_1030_; lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1052_; 
v_val_1030_ = lean_ctor_get(v_a_1026_, 0);
v_isSharedCheck_1052_ = !lean_is_exclusive(v_a_1026_);
if (v_isSharedCheck_1052_ == 0)
{
v___x_1032_ = v_a_1026_;
v_isShared_1033_ = v_isSharedCheck_1052_;
goto v_resetjp_1031_;
}
else
{
lean_inc(v_val_1030_);
lean_dec(v_a_1026_);
v___x_1032_ = lean_box(0);
v_isShared_1033_ = v_isSharedCheck_1052_;
goto v_resetjp_1031_;
}
v_resetjp_1031_:
{
lean_object* v_fst_1034_; lean_object* v_snd_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1051_; 
v_fst_1034_ = lean_ctor_get(v_val_1030_, 0);
v_snd_1035_ = lean_ctor_get(v_val_1030_, 1);
v_isSharedCheck_1051_ = !lean_is_exclusive(v_val_1030_);
if (v_isSharedCheck_1051_ == 0)
{
v___x_1037_ = v_val_1030_;
v_isShared_1038_ = v_isSharedCheck_1051_;
goto v_resetjp_1036_;
}
else
{
lean_inc(v_snd_1035_);
lean_inc(v_fst_1034_);
lean_dec(v_val_1030_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1051_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1043_; 
v___x_1039_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__5, &l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__5_once, _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__5);
v___x_1040_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__6, &l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__6_once, _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__6);
lean_inc(v_fst_1034_);
v___x_1041_ = l_Lean_mkApp6(v___x_1039_, v___x_1040_, v_e_1011_, v_val_1018_, v_fst_1034_, v_h_u2081_1019_, v_snd_1035_);
if (v_isShared_1038_ == 0)
{
lean_ctor_set(v___x_1037_, 1, v___x_1041_);
v___x_1043_ = v___x_1037_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v_fst_1034_);
lean_ctor_set(v_reuseFailAlloc_1050_, 1, v___x_1041_);
v___x_1043_ = v_reuseFailAlloc_1050_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
lean_object* v___x_1045_; 
if (v_isShared_1033_ == 0)
{
lean_ctor_set(v___x_1032_, 0, v___x_1043_);
v___x_1045_ = v___x_1032_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v___x_1043_);
v___x_1045_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
lean_object* v___x_1047_; 
if (v_isShared_1029_ == 0)
{
lean_ctor_set(v___x_1028_, 0, v___x_1045_);
v___x_1047_ = v___x_1028_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v___x_1045_);
v___x_1047_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
return v___x_1047_;
}
}
}
}
}
}
else
{
lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1056_; 
lean_dec(v_a_1026_);
lean_dec_ref(v_e_1011_);
v___x_1053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1053_, 0, v_val_1018_);
lean_ctor_set(v___x_1053_, 1, v_h_u2081_1019_);
v___x_1054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1053_);
if (v_isShared_1029_ == 0)
{
lean_ctor_set(v___x_1028_, 0, v___x_1054_);
v___x_1056_ = v___x_1028_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1057_; 
v_reuseFailAlloc_1057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1057_, 0, v___x_1054_);
v___x_1056_ = v_reuseFailAlloc_1057_;
goto v_reusejp_1055_;
}
v_reusejp_1055_:
{
return v___x_1056_;
}
}
}
}
else
{
lean_dec_ref(v_h_u2081_1019_);
lean_dec_ref(v_val_1018_);
lean_dec_ref(v_e_1011_);
return v___x_1025_;
}
}
v___jp_1059_:
{
lean_object* v___x_1060_; lean_object* v___x_1061_; 
v___x_1060_ = lean_box(0);
v___x_1061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1061_, 0, v___x_1060_);
return v___x_1061_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Simp_Arith_Int_simpRel_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1011_ = stack[0].m_obj;
lean_object* v_a_1012_ = stack[1].m_obj;
lean_object* v_a_1013_ = stack[2].m_obj;
lean_object* v_a_1014_ = stack[3].m_obj;
lean_object* v_a_1015_ = stack[4].m_obj;
lean_object* v_res_1166_;
v_res_1166_ = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f(v_e_1011_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_);
stack->m_obj
 = v_res_1166_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___boxed(lean_object* v_e_1167_, lean_object* v_a_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_){
_start:
{
lean_object* v_res_1173_; 
v_res_1173_ = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f(v_e_1167_, v_a_1168_, v_a_1169_, v_a_1170_, v_a_1171_);
lean_dec(v_a_1171_);
lean_dec_ref(v_a_1170_);
lean_dec(v_a_1169_);
lean_dec_ref(v_a_1168_);
return v_res_1173_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__2(void){
_start:
{
lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; 
v___x_1180_ = lean_box(0);
v___x_1181_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__1));
v___x_1182_ = l_Lean_mkConst(v___x_1181_, v___x_1180_);
return v___x_1182_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__5(void){
_start:
{
lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; 
v___x_1189_ = lean_box(0);
v___x_1190_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__4));
v___x_1191_ = l_Lean_mkConst(v___x_1190_, v___x_1189_);
return v___x_1191_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__8(void){
_start:
{
lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; 
v___x_1198_ = lean_box(0);
v___x_1199_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__7));
v___x_1200_ = l_Lean_mkConst(v___x_1199_, v___x_1198_);
return v___x_1200_;
}
}
lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f(lean_object* v_e_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_){
_start:
{
lean_object* v___y_1208_; lean_object* v___y_1209_; lean_object* v_h_1210_; lean_object* v___y_1217_; lean_object* v___y_1218_; lean_object* v___y_1219_; lean_object* v___y_1220_; lean_object* v___y_1221_; lean_object* v___y_1222_; lean_object* v___y_1223_; lean_object* v___y_1224_; lean_object* v___y_1225_; lean_object* v___x_1228_; lean_object* v___x_1229_; 
v___x_1228_ = l_Lean_instInhabitedExpr;
v___x_1229_ = l_Lean_Meta_Simp_Arith_Int_dvdCnstr_x3f(v_e_1201_, v_a_1202_, v_a_1203_, v_a_1204_, v_a_1205_);
if (lean_obj_tag(v___x_1229_) == 0)
{
lean_object* v_a_1230_; lean_object* v___x_1232_; uint8_t v_isShared_1233_; uint8_t v_isSharedCheck_1396_; 
v_a_1230_ = lean_ctor_get(v___x_1229_, 0);
v_isSharedCheck_1396_ = !lean_is_exclusive(v___x_1229_);
if (v_isSharedCheck_1396_ == 0)
{
v___x_1232_ = v___x_1229_;
v_isShared_1233_ = v_isSharedCheck_1396_;
goto v_resetjp_1231_;
}
else
{
lean_inc(v_a_1230_);
lean_dec(v___x_1229_);
v___x_1232_ = lean_box(0);
v_isShared_1233_ = v_isSharedCheck_1396_;
goto v_resetjp_1231_;
}
v_resetjp_1231_:
{
if (lean_obj_tag(v_a_1230_) == 1)
{
lean_object* v_val_1234_; lean_object* v___x_1236_; uint8_t v_isShared_1237_; uint8_t v_isSharedCheck_1391_; 
v_val_1234_ = lean_ctor_get(v_a_1230_, 0);
v_isSharedCheck_1391_ = !lean_is_exclusive(v_a_1230_);
if (v_isSharedCheck_1391_ == 0)
{
v___x_1236_ = v_a_1230_;
v_isShared_1237_ = v_isSharedCheck_1391_;
goto v_resetjp_1235_;
}
else
{
lean_inc(v_val_1234_);
lean_dec(v_a_1230_);
v___x_1236_ = lean_box(0);
v_isShared_1237_ = v_isSharedCheck_1391_;
goto v_resetjp_1235_;
}
v_resetjp_1235_:
{
lean_object* v_snd_1238_; lean_object* v_fst_1239_; lean_object* v_fst_1240_; lean_object* v_snd_1241_; lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1390_; 
v_snd_1238_ = lean_ctor_get(v_val_1234_, 1);
lean_inc(v_snd_1238_);
v_fst_1239_ = lean_ctor_get(v_val_1234_, 0);
lean_inc(v_fst_1239_);
lean_dec(v_val_1234_);
v_fst_1240_ = lean_ctor_get(v_snd_1238_, 0);
v_snd_1241_ = lean_ctor_get(v_snd_1238_, 1);
v_isSharedCheck_1390_ = !lean_is_exclusive(v_snd_1238_);
if (v_isSharedCheck_1390_ == 0)
{
v___x_1243_ = v_snd_1238_;
v_isShared_1244_ = v_isSharedCheck_1390_;
goto v_resetjp_1242_;
}
else
{
lean_inc(v_snd_1241_);
lean_inc(v_fst_1240_);
lean_dec(v_snd_1238_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1390_;
goto v_resetjp_1242_;
}
v_resetjp_1242_:
{
lean_object* v___x_1245_; lean_object* v___y_1247_; lean_object* v___y_1248_; lean_object* v___y_1249_; lean_object* v___y_1250_; lean_object* v___y_1251_; lean_object* v___y_1252_; uint8_t v___x_1294_; 
v___x_1245_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6);
v___x_1294_ = lean_int_dec_eq(v_fst_1239_, v___x_1245_);
if (v___x_1294_ == 0)
{
lean_object* v___f_1295_; lean_object* v___x_1296_; 
lean_del_object(v___x_1232_);
lean_inc(v_snd_1241_);
v___f_1295_ = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1295_, 0, v___x_1228_);
lean_closure_set(v___f_1295_, 1, v_snd_1241_);
lean_inc(v_fst_1240_);
lean_inc_ref(v___f_1295_);
v___x_1296_ = l_Int_Internal_Linear_Expr_denoteExpr___redArg(v___f_1295_, v_fst_1240_);
if (lean_obj_tag(v___x_1296_) == 0)
{
lean_object* v_a_1297_; lean_object* v___x_1299_; uint8_t v_isShared_1300_; uint8_t v_isSharedCheck_1377_; 
v_a_1297_ = lean_ctor_get(v___x_1296_, 0);
v_isSharedCheck_1377_ = !lean_is_exclusive(v___x_1296_);
if (v_isSharedCheck_1377_ == 0)
{
v___x_1299_ = v___x_1296_;
v_isShared_1300_ = v_isSharedCheck_1377_;
goto v_resetjp_1298_;
}
else
{
lean_inc(v_a_1297_);
lean_dec(v___x_1296_);
v___x_1299_ = lean_box(0);
v_isShared_1300_ = v_isSharedCheck_1377_;
goto v_resetjp_1298_;
}
v_resetjp_1298_:
{
lean_object* v___y_1302_; uint8_t v___x_1367_; 
v___x_1367_ = lean_int_dec_le(v___x_1245_, v_fst_1239_);
if (v___x_1367_ == 0)
{
lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; 
v___x_1368_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18);
v___x_1369_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20);
v___x_1370_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23);
v___x_1371_ = lean_int_neg(v_fst_1239_);
v___x_1372_ = l_Int_toNat(v___x_1371_);
lean_dec(v___x_1371_);
v___x_1373_ = l_Lean_instToExprInt_mkNat(v___x_1372_);
v___x_1374_ = l_Lean_mkApp3(v___x_1368_, v___x_1369_, v___x_1370_, v___x_1373_);
v___y_1302_ = v___x_1374_;
goto v___jp_1301_;
}
else
{
lean_object* v___x_1375_; lean_object* v___x_1376_; 
v___x_1375_ = l_Int_toNat(v_fst_1239_);
v___x_1376_ = l_Lean_instToExprInt_mkNat(v___x_1375_);
v___y_1302_ = v___x_1376_;
goto v___jp_1301_;
}
v___jp_1301_:
{
lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; uint8_t v___x_1308_; 
lean_inc_ref(v___y_1302_);
v___x_1303_ = l_Lean_mkIntDvd(v___y_1302_, v_a_1297_);
v___x_1304_ = l_Int_Internal_Linear_Expr_norm(v_fst_1240_);
lean_inc(v_fst_1239_);
v___x_1305_ = l_Int_Internal_Linear_Poly_gcdCoeffs(v___x_1304_, v_fst_1239_);
v___x_1306_ = l_Int_Internal_Linear_Poly_getConst(v___x_1304_);
v___x_1307_ = lean_int_emod(v___x_1306_, v___x_1305_);
lean_dec(v___x_1306_);
v___x_1308_ = lean_int_dec_eq(v___x_1307_, v___x_1245_);
lean_dec(v___x_1307_);
if (v___x_1308_ == 0)
{
lean_object* v___x_1309_; lean_object* v___x_1310_; 
lean_dec(v___x_1305_);
lean_dec_ref(v___x_1304_);
lean_del_object(v___x_1299_);
lean_dec_ref(v___f_1295_);
lean_dec(v_fst_1239_);
v___x_1309_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__9, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__9_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__9);
v___x_1310_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(v_snd_1241_, v_a_1202_, v_a_1203_, v_a_1204_, v_a_1205_);
if (lean_obj_tag(v___x_1310_) == 0)
{
lean_object* v_a_1311_; lean_object* v___x_1313_; uint8_t v_isShared_1314_; uint8_t v_isSharedCheck_1330_; 
v_a_1311_ = lean_ctor_get(v___x_1310_, 0);
v_isSharedCheck_1330_ = !lean_is_exclusive(v___x_1310_);
if (v_isSharedCheck_1330_ == 0)
{
v___x_1313_ = v___x_1310_;
v_isShared_1314_ = v_isSharedCheck_1330_;
goto v_resetjp_1312_;
}
else
{
lean_inc(v_a_1311_);
lean_dec(v___x_1310_);
v___x_1313_ = lean_box(0);
v_isShared_1314_ = v_isSharedCheck_1330_;
goto v_resetjp_1312_;
}
v_resetjp_1312_:
{
lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1322_; 
v___x_1315_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__8, &l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__8_once, _init_l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__8);
v___x_1316_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_1240_);
v___x_1317_ = l_Lean_eagerReflBoolTrue;
v___x_1318_ = l_Lean_mkApp4(v___x_1315_, v_a_1311_, v___y_1302_, v___x_1316_, v___x_1317_);
v___x_1319_ = l_Lean_mkPropEq(v___x_1303_, v___x_1309_);
v___x_1320_ = l_Lean_Meta_mkExpectedPropHint(v___x_1318_, v___x_1319_);
if (v_isShared_1244_ == 0)
{
lean_ctor_set(v___x_1243_, 1, v___x_1320_);
lean_ctor_set(v___x_1243_, 0, v___x_1309_);
v___x_1322_ = v___x_1243_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1329_; 
v_reuseFailAlloc_1329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1329_, 0, v___x_1309_);
lean_ctor_set(v_reuseFailAlloc_1329_, 1, v___x_1320_);
v___x_1322_ = v_reuseFailAlloc_1329_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
lean_object* v___x_1324_; 
if (v_isShared_1237_ == 0)
{
lean_ctor_set(v___x_1236_, 0, v___x_1322_);
v___x_1324_ = v___x_1236_;
goto v_reusejp_1323_;
}
else
{
lean_object* v_reuseFailAlloc_1328_; 
v_reuseFailAlloc_1328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1328_, 0, v___x_1322_);
v___x_1324_ = v_reuseFailAlloc_1328_;
goto v_reusejp_1323_;
}
v_reusejp_1323_:
{
lean_object* v___x_1326_; 
if (v_isShared_1314_ == 0)
{
lean_ctor_set(v___x_1313_, 0, v___x_1324_);
v___x_1326_ = v___x_1313_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1327_; 
v_reuseFailAlloc_1327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1327_, 0, v___x_1324_);
v___x_1326_ = v_reuseFailAlloc_1327_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
return v___x_1326_;
}
}
}
}
}
else
{
lean_object* v_a_1331_; lean_object* v___x_1333_; uint8_t v_isShared_1334_; uint8_t v_isSharedCheck_1338_; 
lean_dec_ref(v___x_1303_);
lean_dec_ref(v___y_1302_);
lean_del_object(v___x_1243_);
lean_dec(v_fst_1240_);
lean_del_object(v___x_1236_);
v_a_1331_ = lean_ctor_get(v___x_1310_, 0);
v_isSharedCheck_1338_ = !lean_is_exclusive(v___x_1310_);
if (v_isSharedCheck_1338_ == 0)
{
v___x_1333_ = v___x_1310_;
v_isShared_1334_ = v_isSharedCheck_1338_;
goto v_resetjp_1332_;
}
else
{
lean_inc(v_a_1331_);
lean_dec(v___x_1310_);
v___x_1333_ = lean_box(0);
v_isShared_1334_ = v_isSharedCheck_1338_;
goto v_resetjp_1332_;
}
v_resetjp_1332_:
{
lean_object* v___x_1336_; 
if (v_isShared_1334_ == 0)
{
v___x_1336_ = v___x_1333_;
goto v_reusejp_1335_;
}
else
{
lean_object* v_reuseFailAlloc_1337_; 
v_reuseFailAlloc_1337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1337_, 0, v_a_1331_);
v___x_1336_ = v_reuseFailAlloc_1337_;
goto v_reusejp_1335_;
}
v_reusejp_1335_:
{
return v___x_1336_;
}
}
}
}
else
{
lean_object* v___x_1339_; lean_object* v___x_1340_; uint8_t v___x_1341_; 
lean_del_object(v___x_1243_);
lean_del_object(v___x_1236_);
v___x_1339_ = l_Int_Internal_Linear_Poly_div(v___x_1305_, v___x_1304_);
lean_inc_ref(v___x_1339_);
v___x_1340_ = l_Int_Internal_Linear_Poly_toExpr(v___x_1339_);
v___x_1341_ = l_Int_Internal_Linear_instBEqExpr_beq(v_fst_1240_, v___x_1340_);
lean_dec_ref(v___x_1340_);
if (v___x_1341_ == 0)
{
lean_object* v___x_1342_; lean_object* v___x_1343_; 
lean_del_object(v___x_1299_);
v___x_1342_ = lean_int_ediv(v_fst_1239_, v___x_1305_);
lean_dec(v_fst_1239_);
lean_inc_ref(v___x_1339_);
v___x_1343_ = l_Int_Internal_Linear_Poly_denoteExpr___redArg(v___f_1295_, v___x_1339_);
if (lean_obj_tag(v___x_1343_) == 0)
{
lean_object* v_a_1344_; uint8_t v___x_1345_; 
v_a_1344_ = lean_ctor_get(v___x_1343_, 0);
lean_inc(v_a_1344_);
lean_dec_ref_known(v___x_1343_, 1);
v___x_1345_ = lean_int_dec_le(v___x_1245_, v___x_1342_);
if (v___x_1345_ == 0)
{
lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; 
v___x_1346_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18);
v___x_1347_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20);
v___x_1348_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23);
v___x_1349_ = lean_int_neg(v___x_1342_);
lean_dec(v___x_1342_);
v___x_1350_ = l_Int_toNat(v___x_1349_);
lean_dec(v___x_1349_);
v___x_1351_ = l_Lean_instToExprInt_mkNat(v___x_1350_);
v___x_1352_ = l_Lean_mkApp3(v___x_1346_, v___x_1347_, v___x_1348_, v___x_1351_);
v___y_1247_ = v___x_1305_;
v___y_1248_ = v_a_1344_;
v___y_1249_ = v___x_1339_;
v___y_1250_ = v___y_1302_;
v___y_1251_ = v___x_1303_;
v___y_1252_ = v___x_1352_;
goto v___jp_1246_;
}
else
{
lean_object* v___x_1353_; lean_object* v___x_1354_; 
v___x_1353_ = l_Int_toNat(v___x_1342_);
lean_dec(v___x_1342_);
v___x_1354_ = l_Lean_instToExprInt_mkNat(v___x_1353_);
v___y_1247_ = v___x_1305_;
v___y_1248_ = v_a_1344_;
v___y_1249_ = v___x_1339_;
v___y_1250_ = v___y_1302_;
v___y_1251_ = v___x_1303_;
v___y_1252_ = v___x_1354_;
goto v___jp_1246_;
}
}
else
{
lean_object* v_a_1355_; lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1362_; 
lean_dec(v___x_1342_);
lean_dec_ref(v___x_1339_);
lean_dec(v___x_1305_);
lean_dec_ref(v___x_1303_);
lean_dec_ref(v___y_1302_);
lean_dec(v_snd_1241_);
lean_dec(v_fst_1240_);
v_a_1355_ = lean_ctor_get(v___x_1343_, 0);
v_isSharedCheck_1362_ = !lean_is_exclusive(v___x_1343_);
if (v_isSharedCheck_1362_ == 0)
{
v___x_1357_ = v___x_1343_;
v_isShared_1358_ = v_isSharedCheck_1362_;
goto v_resetjp_1356_;
}
else
{
lean_inc(v_a_1355_);
lean_dec(v___x_1343_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1362_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
lean_object* v___x_1360_; 
if (v_isShared_1358_ == 0)
{
v___x_1360_ = v___x_1357_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v_a_1355_);
v___x_1360_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
return v___x_1360_;
}
}
}
}
else
{
lean_object* v___x_1363_; lean_object* v___x_1365_; 
lean_dec_ref(v___x_1339_);
lean_dec(v___x_1305_);
lean_dec_ref(v___x_1303_);
lean_dec_ref(v___y_1302_);
lean_dec_ref(v___f_1295_);
lean_dec(v_snd_1241_);
lean_dec(v_fst_1240_);
lean_dec(v_fst_1239_);
v___x_1363_ = lean_box(0);
if (v_isShared_1300_ == 0)
{
lean_ctor_set(v___x_1299_, 0, v___x_1363_);
v___x_1365_ = v___x_1299_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v___x_1363_);
v___x_1365_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
return v___x_1365_;
}
}
}
}
}
}
else
{
lean_object* v_a_1378_; lean_object* v___x_1380_; uint8_t v_isShared_1381_; uint8_t v_isSharedCheck_1385_; 
lean_dec_ref(v___f_1295_);
lean_del_object(v___x_1243_);
lean_dec(v_snd_1241_);
lean_dec(v_fst_1240_);
lean_dec(v_fst_1239_);
lean_del_object(v___x_1236_);
v_a_1378_ = lean_ctor_get(v___x_1296_, 0);
v_isSharedCheck_1385_ = !lean_is_exclusive(v___x_1296_);
if (v_isSharedCheck_1385_ == 0)
{
v___x_1380_ = v___x_1296_;
v_isShared_1381_ = v_isSharedCheck_1385_;
goto v_resetjp_1379_;
}
else
{
lean_inc(v_a_1378_);
lean_dec(v___x_1296_);
v___x_1380_ = lean_box(0);
v_isShared_1381_ = v_isSharedCheck_1385_;
goto v_resetjp_1379_;
}
v_resetjp_1379_:
{
lean_object* v___x_1383_; 
if (v_isShared_1381_ == 0)
{
v___x_1383_ = v___x_1380_;
goto v_reusejp_1382_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1384_, 0, v_a_1378_);
v___x_1383_ = v_reuseFailAlloc_1384_;
goto v_reusejp_1382_;
}
v_reusejp_1382_:
{
return v___x_1383_;
}
}
}
}
else
{
lean_object* v___x_1386_; lean_object* v___x_1388_; 
lean_del_object(v___x_1243_);
lean_dec(v_snd_1241_);
lean_dec(v_fst_1240_);
lean_dec(v_fst_1239_);
lean_del_object(v___x_1236_);
v___x_1386_ = lean_box(0);
if (v_isShared_1233_ == 0)
{
lean_ctor_set(v___x_1232_, 0, v___x_1386_);
v___x_1388_ = v___x_1232_;
goto v_reusejp_1387_;
}
else
{
lean_object* v_reuseFailAlloc_1389_; 
v_reuseFailAlloc_1389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1389_, 0, v___x_1386_);
v___x_1388_ = v_reuseFailAlloc_1389_;
goto v_reusejp_1387_;
}
v_reusejp_1387_:
{
return v___x_1388_;
}
}
v___jp_1246_:
{
lean_object* v___x_1253_; lean_object* v___x_1254_; uint8_t v___x_1255_; 
lean_inc_ref(v___y_1252_);
v___x_1253_ = l_Lean_mkIntDvd(v___y_1252_, v___y_1248_);
v___x_1254_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__31, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__31_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__31);
v___x_1255_ = lean_int_dec_eq(v___y_1247_, v___x_1254_);
if (v___x_1255_ == 0)
{
lean_object* v___x_1256_; 
v___x_1256_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(v_snd_1241_, v_a_1202_, v_a_1203_, v_a_1204_, v_a_1205_);
if (lean_obj_tag(v___x_1256_) == 0)
{
lean_object* v_a_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; uint8_t v___x_1261_; 
v_a_1257_ = lean_ctor_get(v___x_1256_, 0);
lean_inc(v_a_1257_);
lean_dec_ref_known(v___x_1256_, 1);
v___x_1258_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__2, &l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__2_once, _init_l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__2);
v___x_1259_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_1240_);
v___x_1260_ = l_Lean_Meta_Simp_Arith_Int_ofPoly(v___y_1249_);
v___x_1261_ = lean_int_dec_le(v___x_1245_, v___y_1247_);
if (v___x_1261_ == 0)
{
lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; 
v___x_1262_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18);
v___x_1263_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20);
v___x_1264_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23);
v___x_1265_ = lean_int_neg(v___y_1247_);
lean_dec(v___y_1247_);
v___x_1266_ = l_Int_toNat(v___x_1265_);
lean_dec(v___x_1265_);
v___x_1267_ = l_Lean_instToExprInt_mkNat(v___x_1266_);
v___x_1268_ = l_Lean_mkApp3(v___x_1262_, v___x_1263_, v___x_1264_, v___x_1267_);
v___y_1217_ = v___x_1258_;
v___y_1218_ = v_a_1257_;
v___y_1219_ = v___x_1260_;
v___y_1220_ = v___x_1259_;
v___y_1221_ = v___y_1251_;
v___y_1222_ = v___x_1253_;
v___y_1223_ = v___y_1250_;
v___y_1224_ = v___y_1252_;
v___y_1225_ = v___x_1268_;
goto v___jp_1216_;
}
else
{
lean_object* v___x_1269_; lean_object* v___x_1270_; 
v___x_1269_ = l_Int_toNat(v___y_1247_);
lean_dec(v___y_1247_);
v___x_1270_ = l_Lean_instToExprInt_mkNat(v___x_1269_);
v___y_1217_ = v___x_1258_;
v___y_1218_ = v_a_1257_;
v___y_1219_ = v___x_1260_;
v___y_1220_ = v___x_1259_;
v___y_1221_ = v___y_1251_;
v___y_1222_ = v___x_1253_;
v___y_1223_ = v___y_1250_;
v___y_1224_ = v___y_1252_;
v___y_1225_ = v___x_1270_;
goto v___jp_1216_;
}
}
else
{
lean_object* v_a_1271_; lean_object* v___x_1273_; uint8_t v_isShared_1274_; uint8_t v_isSharedCheck_1278_; 
lean_dec_ref(v___x_1253_);
lean_dec_ref(v___y_1252_);
lean_dec_ref(v___y_1251_);
lean_dec_ref(v___y_1250_);
lean_dec_ref(v___y_1249_);
lean_dec(v___y_1247_);
lean_dec(v_fst_1240_);
v_a_1271_ = lean_ctor_get(v___x_1256_, 0);
v_isSharedCheck_1278_ = !lean_is_exclusive(v___x_1256_);
if (v_isSharedCheck_1278_ == 0)
{
v___x_1273_ = v___x_1256_;
v_isShared_1274_ = v_isSharedCheck_1278_;
goto v_resetjp_1272_;
}
else
{
lean_inc(v_a_1271_);
lean_dec(v___x_1256_);
v___x_1273_ = lean_box(0);
v_isShared_1274_ = v_isSharedCheck_1278_;
goto v_resetjp_1272_;
}
v_resetjp_1272_:
{
lean_object* v___x_1276_; 
if (v_isShared_1274_ == 0)
{
v___x_1276_ = v___x_1273_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v_a_1271_);
v___x_1276_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
return v___x_1276_;
}
}
}
}
else
{
lean_object* v___x_1279_; 
lean_dec_ref(v___y_1252_);
lean_dec(v___y_1247_);
v___x_1279_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(v_snd_1241_, v_a_1202_, v_a_1203_, v_a_1204_, v_a_1205_);
if (lean_obj_tag(v___x_1279_) == 0)
{
lean_object* v_a_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; 
v_a_1280_ = lean_ctor_get(v___x_1279_, 0);
lean_inc(v_a_1280_);
lean_dec_ref_known(v___x_1279_, 1);
v___x_1281_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__5, &l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__5_once, _init_l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__5);
v___x_1282_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_1240_);
v___x_1283_ = l_Lean_Meta_Simp_Arith_Int_ofPoly(v___y_1249_);
v___x_1284_ = l_Lean_eagerReflBoolTrue;
v___x_1285_ = l_Lean_mkApp5(v___x_1281_, v_a_1280_, v___y_1250_, v___x_1282_, v___x_1283_, v___x_1284_);
v___y_1208_ = v___x_1253_;
v___y_1209_ = v___y_1251_;
v_h_1210_ = v___x_1285_;
goto v___jp_1207_;
}
else
{
lean_object* v_a_1286_; lean_object* v___x_1288_; uint8_t v_isShared_1289_; uint8_t v_isSharedCheck_1293_; 
lean_dec_ref(v___x_1253_);
lean_dec_ref(v___y_1251_);
lean_dec_ref(v___y_1250_);
lean_dec_ref(v___y_1249_);
lean_dec(v_fst_1240_);
v_a_1286_ = lean_ctor_get(v___x_1279_, 0);
v_isSharedCheck_1293_ = !lean_is_exclusive(v___x_1279_);
if (v_isSharedCheck_1293_ == 0)
{
v___x_1288_ = v___x_1279_;
v_isShared_1289_ = v_isSharedCheck_1293_;
goto v_resetjp_1287_;
}
else
{
lean_inc(v_a_1286_);
lean_dec(v___x_1279_);
v___x_1288_ = lean_box(0);
v_isShared_1289_ = v_isSharedCheck_1293_;
goto v_resetjp_1287_;
}
v_resetjp_1287_:
{
lean_object* v___x_1291_; 
if (v_isShared_1289_ == 0)
{
v___x_1291_ = v___x_1288_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v_a_1286_);
v___x_1291_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
return v___x_1291_;
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
lean_object* v___x_1392_; lean_object* v___x_1394_; 
lean_dec(v_a_1230_);
v___x_1392_ = lean_box(0);
if (v_isShared_1233_ == 0)
{
lean_ctor_set(v___x_1232_, 0, v___x_1392_);
v___x_1394_ = v___x_1232_;
goto v_reusejp_1393_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v___x_1392_);
v___x_1394_ = v_reuseFailAlloc_1395_;
goto v_reusejp_1393_;
}
v_reusejp_1393_:
{
return v___x_1394_;
}
}
}
}
else
{
lean_object* v_a_1397_; lean_object* v___x_1399_; uint8_t v_isShared_1400_; uint8_t v_isSharedCheck_1404_; 
v_a_1397_ = lean_ctor_get(v___x_1229_, 0);
v_isSharedCheck_1404_ = !lean_is_exclusive(v___x_1229_);
if (v_isSharedCheck_1404_ == 0)
{
v___x_1399_ = v___x_1229_;
v_isShared_1400_ = v_isSharedCheck_1404_;
goto v_resetjp_1398_;
}
else
{
lean_inc(v_a_1397_);
lean_dec(v___x_1229_);
v___x_1399_ = lean_box(0);
v_isShared_1400_ = v_isSharedCheck_1404_;
goto v_resetjp_1398_;
}
v_resetjp_1398_:
{
lean_object* v___x_1402_; 
if (v_isShared_1400_ == 0)
{
v___x_1402_ = v___x_1399_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v_a_1397_);
v___x_1402_ = v_reuseFailAlloc_1403_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
return v___x_1402_;
}
}
}
v___jp_1207_:
{
lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; 
lean_inc_ref(v___y_1208_);
v___x_1211_ = l_Lean_mkPropEq(v___y_1209_, v___y_1208_);
v___x_1212_ = l_Lean_Meta_mkExpectedPropHint(v_h_1210_, v___x_1211_);
v___x_1213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1213_, 0, v___y_1208_);
lean_ctor_set(v___x_1213_, 1, v___x_1212_);
v___x_1214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1214_, 0, v___x_1213_);
v___x_1215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1215_, 0, v___x_1214_);
return v___x_1215_;
}
v___jp_1216_:
{
lean_object* v___x_1226_; lean_object* v___x_1227_; 
v___x_1226_ = l_Lean_eagerReflBoolTrue;
lean_inc_ref(v___y_1217_);
v___x_1227_ = l_Lean_mkApp7(v___y_1217_, v___y_1218_, v___y_1223_, v___y_1220_, v___y_1224_, v___y_1219_, v___y_1225_, v___x_1226_);
v___y_1208_ = v___y_1222_;
v___y_1209_ = v___y_1221_;
v_h_1210_ = v___x_1227_;
goto v___jp_1207_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1201_ = stack[0].m_obj;
lean_object* v_a_1202_ = stack[1].m_obj;
lean_object* v_a_1203_ = stack[2].m_obj;
lean_object* v_a_1204_ = stack[3].m_obj;
lean_object* v_a_1205_ = stack[4].m_obj;
lean_object* v_res_1405_;
v_res_1405_ = l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f(v_e_1201_, v_a_1202_, v_a_1203_, v_a_1204_, v_a_1205_);
stack->m_obj
 = v_res_1405_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___boxed(lean_object* v_e_1406_, lean_object* v_a_1407_, lean_object* v_a_1408_, lean_object* v_a_1409_, lean_object* v_a_1410_, lean_object* v_a_1411_){
_start:
{
lean_object* v_res_1412_; 
v_res_1412_ = l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f(v_e_1406_, v_a_1407_, v_a_1408_, v_a_1409_, v_a_1410_);
lean_dec(v_a_1410_);
lean_dec_ref(v_a_1409_);
lean_dec(v_a_1408_);
lean_dec_ref(v_a_1407_);
return v_res_1412_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__3(void){
_start:
{
lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; 
v___x_1421_ = lean_box(0);
v___x_1422_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__2));
v___x_1423_ = l_Lean_mkConst(v___x_1422_, v___x_1421_);
return v___x_1423_;
}
}
lean_object* l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f(lean_object* v_lhs_1424_, lean_object* v_a_1425_, lean_object* v_a_1426_, lean_object* v_a_1427_, lean_object* v_a_1428_){
_start:
{
lean_object* v___x_1430_; lean_object* v___x_1431_; 
v___x_1430_ = l_Lean_instInhabitedExpr;
v___x_1431_ = l_Lean_Meta_Simp_Arith_Int_toLinearExpr(v_lhs_1424_, v_a_1425_, v_a_1426_, v_a_1427_, v_a_1428_);
if (lean_obj_tag(v___x_1431_) == 0)
{
lean_object* v_a_1432_; lean_object* v___x_1434_; uint8_t v_isShared_1435_; uint8_t v_isSharedCheck_1498_; 
v_a_1432_ = lean_ctor_get(v___x_1431_, 0);
v_isSharedCheck_1498_ = !lean_is_exclusive(v___x_1431_);
if (v_isSharedCheck_1498_ == 0)
{
v___x_1434_ = v___x_1431_;
v_isShared_1435_ = v_isSharedCheck_1498_;
goto v_resetjp_1433_;
}
else
{
lean_inc(v_a_1432_);
lean_dec(v___x_1431_);
v___x_1434_ = lean_box(0);
v_isShared_1435_ = v_isSharedCheck_1498_;
goto v_resetjp_1433_;
}
v_resetjp_1433_:
{
lean_object* v_fst_1436_; lean_object* v_snd_1437_; lean_object* v___x_1439_; uint8_t v_isShared_1440_; uint8_t v_isSharedCheck_1497_; 
v_fst_1436_ = lean_ctor_get(v_a_1432_, 0);
v_snd_1437_ = lean_ctor_get(v_a_1432_, 1);
v_isSharedCheck_1497_ = !lean_is_exclusive(v_a_1432_);
if (v_isSharedCheck_1497_ == 0)
{
v___x_1439_ = v_a_1432_;
v_isShared_1440_ = v_isSharedCheck_1497_;
goto v_resetjp_1438_;
}
else
{
lean_inc(v_snd_1437_);
lean_inc(v_fst_1436_);
lean_dec(v_a_1432_);
v___x_1439_ = lean_box(0);
v_isShared_1440_ = v_isSharedCheck_1497_;
goto v_resetjp_1438_;
}
v_resetjp_1438_:
{
lean_object* v___x_1441_; lean_object* v___x_1442_; uint8_t v___x_1443_; 
v___x_1441_ = l_Int_Internal_Linear_Expr_norm(v_fst_1436_);
lean_inc_ref(v___x_1441_);
v___x_1442_ = l_Int_Internal_Linear_Poly_toExpr(v___x_1441_);
v___x_1443_ = l_Int_Internal_Linear_instBEqExpr_beq(v_fst_1436_, v___x_1442_);
lean_dec_ref(v___x_1442_);
if (v___x_1443_ == 0)
{
lean_object* v___f_1444_; lean_object* v___x_1445_; 
lean_del_object(v___x_1434_);
lean_inc(v_snd_1437_);
v___f_1444_ = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1444_, 0, v___x_1430_);
lean_closure_set(v___f_1444_, 1, v_snd_1437_);
v___x_1445_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(v_snd_1437_, v_a_1425_, v_a_1426_, v_a_1427_, v_a_1428_);
if (lean_obj_tag(v___x_1445_) == 0)
{
lean_object* v_a_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; 
v_a_1446_ = lean_ctor_get(v___x_1445_, 0);
lean_inc(v_a_1446_);
lean_dec_ref_known(v___x_1445_, 1);
v___x_1447_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__3, &l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__3_once, _init_l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__3);
lean_inc(v_fst_1436_);
v___x_1448_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_1436_);
lean_inc_ref(v___x_1441_);
v___x_1449_ = l_Lean_Meta_Simp_Arith_Int_ofPoly(v___x_1441_);
v___x_1450_ = l_Lean_eagerReflBoolTrue;
v___x_1451_ = l_Lean_mkApp4(v___x_1447_, v_a_1446_, v___x_1448_, v___x_1449_, v___x_1450_);
lean_inc_ref(v___f_1444_);
v___x_1452_ = l_Int_Internal_Linear_Expr_denoteExpr___redArg(v___f_1444_, v_fst_1436_);
if (lean_obj_tag(v___x_1452_) == 0)
{
lean_object* v_a_1453_; lean_object* v___x_1454_; 
v_a_1453_ = lean_ctor_get(v___x_1452_, 0);
lean_inc(v_a_1453_);
lean_dec_ref_known(v___x_1452_, 1);
v___x_1454_ = l_Int_Internal_Linear_Poly_denoteExpr___redArg(v___f_1444_, v___x_1441_);
if (lean_obj_tag(v___x_1454_) == 0)
{
lean_object* v_a_1455_; lean_object* v___x_1457_; uint8_t v_isShared_1458_; uint8_t v_isSharedCheck_1468_; 
v_a_1455_ = lean_ctor_get(v___x_1454_, 0);
v_isSharedCheck_1468_ = !lean_is_exclusive(v___x_1454_);
if (v_isSharedCheck_1468_ == 0)
{
v___x_1457_ = v___x_1454_;
v_isShared_1458_ = v_isSharedCheck_1468_;
goto v_resetjp_1456_;
}
else
{
lean_inc(v_a_1455_);
lean_dec(v___x_1454_);
v___x_1457_ = lean_box(0);
v_isShared_1458_ = v_isSharedCheck_1468_;
goto v_resetjp_1456_;
}
v_resetjp_1456_:
{
lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1462_; 
lean_inc(v_a_1455_);
v___x_1459_ = l_Lean_mkIntEq(v_a_1453_, v_a_1455_);
v___x_1460_ = l_Lean_Meta_mkExpectedPropHint(v___x_1451_, v___x_1459_);
if (v_isShared_1440_ == 0)
{
lean_ctor_set(v___x_1439_, 1, v___x_1460_);
lean_ctor_set(v___x_1439_, 0, v_a_1455_);
v___x_1462_ = v___x_1439_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1467_; 
v_reuseFailAlloc_1467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1467_, 0, v_a_1455_);
lean_ctor_set(v_reuseFailAlloc_1467_, 1, v___x_1460_);
v___x_1462_ = v_reuseFailAlloc_1467_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
lean_object* v___x_1463_; lean_object* v___x_1465_; 
v___x_1463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1463_, 0, v___x_1462_);
if (v_isShared_1458_ == 0)
{
lean_ctor_set(v___x_1457_, 0, v___x_1463_);
v___x_1465_ = v___x_1457_;
goto v_reusejp_1464_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v___x_1463_);
v___x_1465_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1464_;
}
v_reusejp_1464_:
{
return v___x_1465_;
}
}
}
}
else
{
lean_object* v_a_1469_; lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1476_; 
lean_dec(v_a_1453_);
lean_dec_ref(v___x_1451_);
lean_del_object(v___x_1439_);
v_a_1469_ = lean_ctor_get(v___x_1454_, 0);
v_isSharedCheck_1476_ = !lean_is_exclusive(v___x_1454_);
if (v_isSharedCheck_1476_ == 0)
{
v___x_1471_ = v___x_1454_;
v_isShared_1472_ = v_isSharedCheck_1476_;
goto v_resetjp_1470_;
}
else
{
lean_inc(v_a_1469_);
lean_dec(v___x_1454_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1476_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
lean_object* v___x_1474_; 
if (v_isShared_1472_ == 0)
{
v___x_1474_ = v___x_1471_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v_a_1469_);
v___x_1474_ = v_reuseFailAlloc_1475_;
goto v_reusejp_1473_;
}
v_reusejp_1473_:
{
return v___x_1474_;
}
}
}
}
else
{
lean_object* v_a_1477_; lean_object* v___x_1479_; uint8_t v_isShared_1480_; uint8_t v_isSharedCheck_1484_; 
lean_dec_ref(v___x_1451_);
lean_dec_ref(v___f_1444_);
lean_dec_ref(v___x_1441_);
lean_del_object(v___x_1439_);
v_a_1477_ = lean_ctor_get(v___x_1452_, 0);
v_isSharedCheck_1484_ = !lean_is_exclusive(v___x_1452_);
if (v_isSharedCheck_1484_ == 0)
{
v___x_1479_ = v___x_1452_;
v_isShared_1480_ = v_isSharedCheck_1484_;
goto v_resetjp_1478_;
}
else
{
lean_inc(v_a_1477_);
lean_dec(v___x_1452_);
v___x_1479_ = lean_box(0);
v_isShared_1480_ = v_isSharedCheck_1484_;
goto v_resetjp_1478_;
}
v_resetjp_1478_:
{
lean_object* v___x_1482_; 
if (v_isShared_1480_ == 0)
{
v___x_1482_ = v___x_1479_;
goto v_reusejp_1481_;
}
else
{
lean_object* v_reuseFailAlloc_1483_; 
v_reuseFailAlloc_1483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1483_, 0, v_a_1477_);
v___x_1482_ = v_reuseFailAlloc_1483_;
goto v_reusejp_1481_;
}
v_reusejp_1481_:
{
return v___x_1482_;
}
}
}
}
else
{
lean_object* v_a_1485_; lean_object* v___x_1487_; uint8_t v_isShared_1488_; uint8_t v_isSharedCheck_1492_; 
lean_dec_ref(v___f_1444_);
lean_dec_ref(v___x_1441_);
lean_del_object(v___x_1439_);
lean_dec(v_fst_1436_);
v_a_1485_ = lean_ctor_get(v___x_1445_, 0);
v_isSharedCheck_1492_ = !lean_is_exclusive(v___x_1445_);
if (v_isSharedCheck_1492_ == 0)
{
v___x_1487_ = v___x_1445_;
v_isShared_1488_ = v_isSharedCheck_1492_;
goto v_resetjp_1486_;
}
else
{
lean_inc(v_a_1485_);
lean_dec(v___x_1445_);
v___x_1487_ = lean_box(0);
v_isShared_1488_ = v_isSharedCheck_1492_;
goto v_resetjp_1486_;
}
v_resetjp_1486_:
{
lean_object* v___x_1490_; 
if (v_isShared_1488_ == 0)
{
v___x_1490_ = v___x_1487_;
goto v_reusejp_1489_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v_a_1485_);
v___x_1490_ = v_reuseFailAlloc_1491_;
goto v_reusejp_1489_;
}
v_reusejp_1489_:
{
return v___x_1490_;
}
}
}
}
else
{
lean_object* v___x_1493_; lean_object* v___x_1495_; 
lean_dec_ref(v___x_1441_);
lean_del_object(v___x_1439_);
lean_dec(v_snd_1437_);
lean_dec(v_fst_1436_);
v___x_1493_ = lean_box(0);
if (v_isShared_1435_ == 0)
{
lean_ctor_set(v___x_1434_, 0, v___x_1493_);
v___x_1495_ = v___x_1434_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1496_; 
v_reuseFailAlloc_1496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1496_, 0, v___x_1493_);
v___x_1495_ = v_reuseFailAlloc_1496_;
goto v_reusejp_1494_;
}
v_reusejp_1494_:
{
return v___x_1495_;
}
}
}
}
}
else
{
lean_object* v_a_1499_; lean_object* v___x_1501_; uint8_t v_isShared_1502_; uint8_t v_isSharedCheck_1506_; 
v_a_1499_ = lean_ctor_get(v___x_1431_, 0);
v_isSharedCheck_1506_ = !lean_is_exclusive(v___x_1431_);
if (v_isSharedCheck_1506_ == 0)
{
v___x_1501_ = v___x_1431_;
v_isShared_1502_ = v_isSharedCheck_1506_;
goto v_resetjp_1500_;
}
else
{
lean_inc(v_a_1499_);
lean_dec(v___x_1431_);
v___x_1501_ = lean_box(0);
v_isShared_1502_ = v_isSharedCheck_1506_;
goto v_resetjp_1500_;
}
v_resetjp_1500_:
{
lean_object* v___x_1504_; 
if (v_isShared_1502_ == 0)
{
v___x_1504_ = v___x_1501_;
goto v_reusejp_1503_;
}
else
{
lean_object* v_reuseFailAlloc_1505_; 
v_reuseFailAlloc_1505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1505_, 0, v_a_1499_);
v___x_1504_ = v_reuseFailAlloc_1505_;
goto v_reusejp_1503_;
}
v_reusejp_1503_:
{
return v___x_1504_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_lhs_1424_ = stack[0].m_obj;
lean_object* v_a_1425_ = stack[1].m_obj;
lean_object* v_a_1426_ = stack[2].m_obj;
lean_object* v_a_1427_ = stack[3].m_obj;
lean_object* v_a_1428_ = stack[4].m_obj;
lean_object* v_res_1507_;
v_res_1507_ = l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f(v_lhs_1424_, v_a_1425_, v_a_1426_, v_a_1427_, v_a_1428_);
stack->m_obj
 = v_res_1507_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___boxed(lean_object* v_lhs_1508_, lean_object* v_a_1509_, lean_object* v_a_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_){
_start:
{
lean_object* v_res_1514_; 
v_res_1514_ = l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f(v_lhs_1508_, v_a_1509_, v_a_1510_, v_a_1511_, v_a_1512_);
lean_dec(v_a_1512_);
lean_dec_ref(v_a_1511_);
lean_dec(v_a_1510_);
lean_dec_ref(v_a_1509_);
return v_res_1514_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Arith_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Arith_Int_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Arith_Int_Simp(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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

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
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* lean_nat_gcd(lean_object*, lean_object*);
lean_object* l_Lean_mkIntLit(lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Arith_Int_toLinearExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Linear_Expr_norm(lean_object*);
lean_object* l_Int_Linear_Poly_toExpr(lean_object*);
uint8_t l_Int_Linear_instBEqExpr_beq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Arith_Int_toContextExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(lean_object*);
lean_object* l_Int_Linear_Expr_denoteExpr___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly(lean_object*);
lean_object* l_Int_Linear_Poly_denoteExpr___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_eagerReflBoolTrue;
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIntEq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkExpectedPropHint(lean_object*, lean_object*);
lean_object* l_Lean_Level_succ___override(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* l_Lean_mkPropEq(lean_object*, lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_div(lean_object*, lean_object*);
lean_object* l_Lean_mkIntLE(lean_object*, lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* l_Int_toNat(lean_object*);
lean_object* l_Lean_instToExprInt_mkNat(lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_getConst(lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Arith_Int_leCnstr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Int_Linear_Poly_isUnsatLe(lean_object*);
uint8_t l_Int_Linear_Poly_isValidLe(lean_object*);
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
lean_object* l_Int_Linear_Poly_gcdCoeffs(lean_object*, lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Arith_Int_eqCnstr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
uint8_t l_Int_Linear_Poly_isUnsatEq(lean_object*);
uint8_t l_Int_Linear_Poly_isValidEq(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Simp_0__Int_Linear_Poly_gcdAll_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Simp_0__Int_Linear_Poly_gcdAll_go___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_gcdAll(lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_gcdAll___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Simp_0__Int_Linear_Poly_gcdCoeffs_x27_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Simp_0__Int_Linear_Poly_gcdCoeffs_x27_go___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_gcdCoeffs_x27(lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_gcdCoeffs_x27___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_Simp_Arith_Int_simpEq_x3f_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Int"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Linear"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "norm_eq_var_const"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__2 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(216, 204, 107, 233, 98, 67, 69, 81)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__3_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(35, 112, 223, 250, 183, 82, 157, 139)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__3 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__4;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "False"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__6_value),LEAN_SCALAR_PTR_LITERAL(227, 122, 176, 177, 50, 175, 152, 12)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__7 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__7_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "eq_eq_false_of_divCoeff"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__9 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__9_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__10_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(216, 204, 107, 233, 98, 67, 69, 81)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__10_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__9_value),LEAN_SCALAR_PTR_LITERAL(155, 236, 46, 169, 167, 124, 63, 211)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__10 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__10_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__11;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Neg"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__12 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__12_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "neg"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__13 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__13_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__12_value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__14_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__13_value),LEAN_SCALAR_PTR_LITERAL(105, 26, 70, 221, 245, 238, 127, 238)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__14 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__14_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__15;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__16;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "instNegInt"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__21_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__20_value),LEAN_SCALAR_PTR_LITERAL(217, 109, 233, 1, 211, 122, 77, 88)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__21 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__21_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "norm_eq_coeff"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__24 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__24_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__25_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__25_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(216, 204, 107, 233, 98, 67, 69, 81)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__25_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__24_value),LEAN_SCALAR_PTR_LITERAL(85, 43, 120, 188, 118, 245, 143, 91)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__25 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__25_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__26;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "norm_eq"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__27 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__27_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__28_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__28_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__28_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(216, 204, 107, 233, 98, 67, 69, 81)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__28_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__27_value),LEAN_SCALAR_PTR_LITERAL(44, 156, 243, 152, 103, 234, 174, 123)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__28 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__28_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__29;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__31;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "norm_eq_var"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__32 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__32_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__33_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__33_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__33_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(216, 204, 107, 233, 98, 67, 69, 81)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__33_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__32_value),LEAN_SCALAR_PTR_LITERAL(135, 64, 142, 174, 60, 214, 97, 115)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__33 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__33_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__34;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__35;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "True"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__36 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__36_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__36_value),LEAN_SCALAR_PTR_LITERAL(78, 21, 103, 131, 118, 13, 187, 164)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__37 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__37_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__38_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__38;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "eq_eq_true"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__39 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__39_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__40_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__40_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__40_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(216, 204, 107, 233, 98, 67, 69, 81)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__40_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__39_value),LEAN_SCALAR_PTR_LITERAL(22, 67, 32, 138, 58, 105, 16, 18)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__40 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__40_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__41_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__41;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "eq_eq_false"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__42 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__42_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__43_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__43_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__43_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(216, 204, 107, 233, 98, 67, 69, 81)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__43_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__42_value),LEAN_SCALAR_PTR_LITERAL(235, 105, 48, 217, 98, 238, 131, 5)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__43 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__43_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__44_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__44;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "norm_le_coeff"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(216, 204, 107, 233, 98, 67, 69, 81)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(152, 68, 185, 68, 63, 172, 180, 150)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__2;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "norm_le_coeff_tight"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__3 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(216, 204, 107, 233, 98, 67, 69, 81)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__3_value),LEAN_SCALAR_PTR_LITERAL(244, 199, 217, 219, 136, 132, 30, 204)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__4 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__5;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "norm_le"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__6 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__7_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(216, 204, 107, 233, 98, 67, 69, 81)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__7_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__6_value),LEAN_SCALAR_PTR_LITERAL(232, 121, 64, 164, 96, 91, 136, 25)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__7 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__7_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__8;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "le_eq_true"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__9 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__9_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__10_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(216, 204, 107, 233, 98, 67, 69, 81)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__10_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__9_value),LEAN_SCALAR_PTR_LITERAL(168, 245, 170, 32, 204, 84, 255, 159)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__10 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__10_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__11;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "le_eq_false"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__12 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__12_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__13_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(216, 204, 107, 233, 98, 67, 69, 81)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__13_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__12_value),LEAN_SCALAR_PTR_LITERAL(76, 250, 170, 64, 206, 9, 106, 135)}};
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
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(216, 204, 107, 233, 98, 67, 69, 81)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(209, 243, 25, 22, 225, 48, 108, 155)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__2;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "norm_dvd"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__3 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(216, 204, 107, 233, 98, 67, 69, 81)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__3_value),LEAN_SCALAR_PTR_LITERAL(14, 102, 31, 143, 124, 229, 161, 52)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__4 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__5;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "dvd_eq_false"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__6 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__7_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(216, 204, 107, 233, 98, 67, 69, 81)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__7_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__6_value),LEAN_SCALAR_PTR_LITERAL(76, 255, 101, 122, 145, 117, 61, 183)}};
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
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(216, 204, 107, 233, 98, 67, 69, 81)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__2_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(162, 62, 222, 142, 91, 249, 126, 146)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__2_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(53, 220, 199, 2, 108, 141, 83, 34)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__2 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Simp_0__Int_Linear_Poly_gcdAll_go(lean_object* v_k_1_, lean_object* v_p_2_){
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Simp_0__Int_Linear_Poly_gcdAll_go___boxed(lean_object* v_k_13_, lean_object* v_p_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Simp_0__Int_Linear_Poly_gcdAll_go(v_k_13_, v_p_14_);
lean_dec_ref(v_p_14_);
return v_res_15_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_gcdAll(lean_object* v_x_16_){
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
v___x_22_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Simp_0__Int_Linear_Poly_gcdAll_go(v___x_21_, v_p_20_);
return v___x_22_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_gcdAll___boxed(lean_object* v_x_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Int_Linear_Poly_gcdAll(v_x_23_);
lean_dec_ref(v_x_23_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Simp_0__Int_Linear_Poly_gcdCoeffs_x27_go(lean_object* v_k_25_, lean_object* v_p_26_){
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Simp_0__Int_Linear_Poly_gcdCoeffs_x27_go___boxed(lean_object* v_k_34_, lean_object* v_p_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Simp_0__Int_Linear_Poly_gcdCoeffs_x27_go(v_k_34_, v_p_35_);
lean_dec_ref(v_p_35_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_gcdCoeffs_x27(lean_object* v_x_37_){
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
v___x_42_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Simp_0__Int_Linear_Poly_gcdCoeffs_x27_go(v___x_41_, v_p_40_);
return v___x_42_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_gcdCoeffs_x27___boxed(lean_object* v_x_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l_Int_Linear_Poly_gcdCoeffs_x27(v_x_43_);
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
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__4(void){
_start:
{
lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_62_ = lean_box(0);
v___x_63_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__3));
v___x_64_ = l_Lean_mkConst(v___x_63_, v___x_62_);
return v___x_64_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5(void){
_start:
{
lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_65_ = lean_unsigned_to_nat(0u);
v___x_66_ = lean_nat_to_int(v___x_65_);
return v___x_66_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8(void){
_start:
{
lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_70_ = lean_box(0);
v___x_71_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__7));
v___x_72_ = l_Lean_mkConst(v___x_71_, v___x_70_);
return v___x_72_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__11(void){
_start:
{
lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; 
v___x_78_ = lean_box(0);
v___x_79_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__10));
v___x_80_ = l_Lean_mkConst(v___x_79_, v___x_78_);
return v___x_80_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__15(void){
_start:
{
lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_86_ = lean_unsigned_to_nat(0u);
v___x_87_ = l_Lean_Level_ofNat(v___x_86_);
return v___x_87_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__16(void){
_start:
{
lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_88_ = lean_box(0);
v___x_89_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__15, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__15_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__15);
v___x_90_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_90_, 0, v___x_89_);
lean_ctor_set(v___x_90_, 1, v___x_88_);
return v___x_90_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17(void){
_start:
{
lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_91_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__16, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__16_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__16);
v___x_92_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__14));
v___x_93_ = l_Lean_Expr_const___override(v___x_92_, v___x_91_);
return v___x_93_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19(void){
_start:
{
lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_96_ = lean_box(0);
v___x_97_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18));
v___x_98_ = l_Lean_Expr_const___override(v___x_97_, v___x_96_);
return v___x_98_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22(void){
_start:
{
lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_103_ = lean_box(0);
v___x_104_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__21));
v___x_105_ = l_Lean_Expr_const___override(v___x_104_, v___x_103_);
return v___x_105_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23(void){
_start:
{
lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_106_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5);
v___x_107_ = l_Lean_mkIntLit(v___x_106_);
return v___x_107_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__26(void){
_start:
{
lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_113_ = lean_box(0);
v___x_114_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__25));
v___x_115_ = l_Lean_mkConst(v___x_114_, v___x_113_);
return v___x_115_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__29(void){
_start:
{
lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_121_ = lean_box(0);
v___x_122_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__28));
v___x_123_ = l_Lean_mkConst(v___x_122_, v___x_121_);
return v___x_123_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30(void){
_start:
{
lean_object* v___x_124_; lean_object* v___x_125_; 
v___x_124_ = lean_unsigned_to_nat(1u);
v___x_125_ = lean_nat_to_int(v___x_124_);
return v___x_125_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__31(void){
_start:
{
lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_126_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30);
v___x_127_ = lean_int_neg(v___x_126_);
return v___x_127_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__34(void){
_start:
{
lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_133_ = lean_box(0);
v___x_134_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__33));
v___x_135_ = l_Lean_mkConst(v___x_134_, v___x_133_);
return v___x_135_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__35(void){
_start:
{
lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_136_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5);
v___x_137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_137_, 0, v___x_136_);
return v___x_137_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__38(void){
_start:
{
lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_141_ = lean_box(0);
v___x_142_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__37));
v___x_143_ = l_Lean_mkConst(v___x_142_, v___x_141_);
return v___x_143_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__41(void){
_start:
{
lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_149_ = lean_box(0);
v___x_150_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__40));
v___x_151_ = l_Lean_mkConst(v___x_150_, v___x_149_);
return v___x_151_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__44(void){
_start:
{
lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_157_ = lean_box(0);
v___x_158_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__43));
v___x_159_ = l_Lean_mkConst(v___x_158_, v___x_157_);
return v___x_159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f(lean_object* v_e_160_, lean_object* v_a_161_, lean_object* v_a_162_, lean_object* v_a_163_, lean_object* v_a_164_){
_start:
{
lean_object* v___x_166_; 
v___x_166_ = l_Lean_Meta_Simp_Arith_Int_eqCnstr_x3f(v_e_160_, v_a_161_, v_a_162_, v_a_163_, v_a_164_);
if (lean_obj_tag(v___x_166_) == 0)
{
lean_object* v_a_167_; lean_object* v___x_169_; uint8_t v_isShared_170_; uint8_t v_isSharedCheck_547_; 
v_a_167_ = lean_ctor_get(v___x_166_, 0);
v_isSharedCheck_547_ = !lean_is_exclusive(v___x_166_);
if (v_isSharedCheck_547_ == 0)
{
v___x_169_ = v___x_166_;
v_isShared_170_ = v_isSharedCheck_547_;
goto v_resetjp_168_;
}
else
{
lean_inc(v_a_167_);
lean_dec(v___x_166_);
v___x_169_ = lean_box(0);
v_isShared_170_ = v_isSharedCheck_547_;
goto v_resetjp_168_;
}
v_resetjp_168_:
{
if (lean_obj_tag(v_a_167_) == 1)
{
lean_object* v_val_171_; lean_object* v___x_173_; uint8_t v_isShared_174_; uint8_t v_isSharedCheck_542_; 
v_val_171_ = lean_ctor_get(v_a_167_, 0);
v_isSharedCheck_542_ = !lean_is_exclusive(v_a_167_);
if (v_isSharedCheck_542_ == 0)
{
v___x_173_ = v_a_167_;
v_isShared_174_ = v_isSharedCheck_542_;
goto v_resetjp_172_;
}
else
{
lean_inc(v_val_171_);
lean_dec(v_a_167_);
v___x_173_ = lean_box(0);
v_isShared_174_ = v_isSharedCheck_542_;
goto v_resetjp_172_;
}
v_resetjp_172_:
{
lean_object* v_snd_175_; lean_object* v_fst_176_; lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_541_; 
v_snd_175_ = lean_ctor_get(v_val_171_, 1);
v_fst_176_ = lean_ctor_get(v_val_171_, 0);
v_isSharedCheck_541_ = !lean_is_exclusive(v_val_171_);
if (v_isSharedCheck_541_ == 0)
{
v___x_178_ = v_val_171_;
v_isShared_179_ = v_isSharedCheck_541_;
goto v_resetjp_177_;
}
else
{
lean_inc(v_snd_175_);
lean_inc(v_fst_176_);
lean_dec(v_val_171_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_541_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
lean_object* v_fst_180_; lean_object* v_snd_181_; lean_object* v___x_183_; uint8_t v_isShared_184_; uint8_t v_isSharedCheck_540_; 
v_fst_180_ = lean_ctor_get(v_snd_175_, 0);
v_snd_181_ = lean_ctor_get(v_snd_175_, 1);
v_isSharedCheck_540_ = !lean_is_exclusive(v_snd_175_);
if (v_isSharedCheck_540_ == 0)
{
v___x_183_ = v_snd_175_;
v_isShared_184_ = v_isSharedCheck_540_;
goto v_resetjp_182_;
}
else
{
lean_inc(v_snd_181_);
lean_inc(v_fst_180_);
lean_dec(v_snd_175_);
v___x_183_ = lean_box(0);
v_isShared_184_ = v_isSharedCheck_540_;
goto v_resetjp_182_;
}
v_resetjp_182_:
{
lean_object* v___x_185_; lean_object* v___f_186_; lean_object* v___x_187_; 
v___x_185_ = l_Lean_instInhabitedExpr;
lean_inc(v_snd_181_);
v___f_186_ = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__0___boxed), 3, 2);
lean_closure_set(v___f_186_, 0, v___x_185_);
lean_closure_set(v___f_186_, 1, v_snd_181_);
lean_inc(v_fst_176_);
lean_inc_ref(v___f_186_);
v___x_187_ = l_Int_Linear_Expr_denoteExpr___redArg(v___f_186_, v_fst_176_);
if (lean_obj_tag(v___x_187_) == 0)
{
lean_object* v_a_188_; lean_object* v___x_190_; uint8_t v_isShared_191_; uint8_t v_isSharedCheck_531_; 
v_a_188_ = lean_ctor_get(v___x_187_, 0);
v_isSharedCheck_531_ = !lean_is_exclusive(v___x_187_);
if (v_isSharedCheck_531_ == 0)
{
v___x_190_ = v___x_187_;
v_isShared_191_ = v_isSharedCheck_531_;
goto v_resetjp_189_;
}
else
{
lean_inc(v_a_188_);
lean_dec(v___x_187_);
v___x_190_ = lean_box(0);
v_isShared_191_ = v_isSharedCheck_531_;
goto v_resetjp_189_;
}
v_resetjp_189_:
{
lean_object* v___x_192_; 
lean_inc(v_fst_180_);
lean_inc_ref(v___f_186_);
v___x_192_ = l_Int_Linear_Expr_denoteExpr___redArg(v___f_186_, v_fst_180_);
if (lean_obj_tag(v___x_192_) == 0)
{
lean_object* v_a_193_; lean_object* v___x_195_; uint8_t v_isShared_196_; uint8_t v_isSharedCheck_522_; 
v_a_193_ = lean_ctor_get(v___x_192_, 0);
v_isSharedCheck_522_ = !lean_is_exclusive(v___x_192_);
if (v_isSharedCheck_522_ == 0)
{
v___x_195_ = v___x_192_;
v_isShared_196_ = v_isSharedCheck_522_;
goto v_resetjp_194_;
}
else
{
lean_inc(v_a_193_);
lean_dec(v___x_192_);
v___x_195_ = lean_box(0);
v_isShared_196_ = v_isSharedCheck_522_;
goto v_resetjp_194_;
}
v_resetjp_194_:
{
lean_object* v___x_197_; lean_object* v___y_199_; lean_object* v___y_200_; lean_object* v___y_201_; lean_object* v___y_202_; lean_object* v___y_203_; lean_object* v___y_204_; lean_object* v___y_219_; lean_object* v___y_220_; lean_object* v___y_221_; lean_object* v___y_222_; lean_object* v___y_223_; lean_object* v___y_224_; lean_object* v___y_225_; lean_object* v___y_238_; lean_object* v___y_239_; lean_object* v___y_240_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___y_277_; lean_object* v___y_278_; lean_object* v___y_279_; lean_object* v___y_280_; uint8_t v___y_390_; uint8_t v___x_462_; 
v___x_197_ = l_Lean_mkIntEq(v_a_188_, v_a_193_);
lean_inc(v_fst_180_);
lean_inc(v_fst_176_);
v___x_274_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_274_, 0, v_fst_176_);
lean_ctor_set(v___x_274_, 1, v_fst_180_);
v___x_275_ = l_Int_Linear_Expr_norm(v___x_274_);
lean_dec_ref(v___x_274_);
v___x_462_ = l_Int_Linear_Poly_isUnsatEq(v___x_275_);
if (v___x_462_ == 0)
{
uint8_t v___x_463_; 
v___x_463_ = l_Int_Linear_Poly_isValidEq(v___x_275_);
if (v___x_463_ == 0)
{
lean_object* v___x_464_; uint8_t v___x_465_; 
lean_inc_ref(v___x_275_);
v___x_464_ = l_Int_Linear_Poly_toExpr(v___x_275_);
v___x_465_ = l_Int_Linear_instBEqExpr_beq(v___x_464_, v_fst_176_);
lean_dec_ref(v___x_464_);
if (v___x_465_ == 0)
{
v___y_390_ = v___x_465_;
goto v___jp_389_;
}
else
{
lean_object* v___x_466_; uint8_t v___x_467_; 
v___x_466_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__35, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__35_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__35);
v___x_467_ = l_Int_Linear_instBEqExpr_beq(v_fst_180_, v___x_466_);
v___y_390_ = v___x_467_;
goto v___jp_389_;
}
}
else
{
lean_object* v___x_468_; 
lean_dec_ref(v___x_275_);
lean_del_object(v___x_195_);
lean_del_object(v___x_190_);
lean_dec_ref(v___f_186_);
lean_del_object(v___x_183_);
lean_del_object(v___x_178_);
lean_del_object(v___x_173_);
lean_del_object(v___x_169_);
v___x_468_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(v_snd_181_, v_a_161_, v_a_162_, v_a_163_, v_a_164_);
if (lean_obj_tag(v___x_468_) == 0)
{
lean_object* v_a_469_; lean_object* v___x_471_; uint8_t v_isShared_472_; uint8_t v_isSharedCheck_486_; 
v_a_469_ = lean_ctor_get(v___x_468_, 0);
v_isSharedCheck_486_ = !lean_is_exclusive(v___x_468_);
if (v_isSharedCheck_486_ == 0)
{
v___x_471_ = v___x_468_;
v_isShared_472_ = v_isSharedCheck_486_;
goto v_resetjp_470_;
}
else
{
lean_inc(v_a_469_);
lean_dec(v___x_468_);
v___x_471_ = lean_box(0);
v_isShared_472_ = v_isSharedCheck_486_;
goto v_resetjp_470_;
}
v_resetjp_470_:
{
lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_484_; 
v___x_473_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__38, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__38_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__38);
v___x_474_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__41, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__41_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__41);
v___x_475_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_176_);
v___x_476_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_180_);
v___x_477_ = l_Lean_eagerReflBoolTrue;
v___x_478_ = l_Lean_mkApp4(v___x_474_, v_a_469_, v___x_475_, v___x_476_, v___x_477_);
v___x_479_ = l_Lean_mkPropEq(v___x_197_, v___x_473_);
v___x_480_ = l_Lean_Meta_mkExpectedPropHint(v___x_478_, v___x_479_);
v___x_481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_481_, 0, v___x_473_);
lean_ctor_set(v___x_481_, 1, v___x_480_);
v___x_482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_482_, 0, v___x_481_);
if (v_isShared_472_ == 0)
{
lean_ctor_set(v___x_471_, 0, v___x_482_);
v___x_484_ = v___x_471_;
goto v_reusejp_483_;
}
else
{
lean_object* v_reuseFailAlloc_485_; 
v_reuseFailAlloc_485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_485_, 0, v___x_482_);
v___x_484_ = v_reuseFailAlloc_485_;
goto v_reusejp_483_;
}
v_reusejp_483_:
{
return v___x_484_;
}
}
}
else
{
lean_object* v_a_487_; lean_object* v___x_489_; uint8_t v_isShared_490_; uint8_t v_isSharedCheck_494_; 
lean_dec_ref(v___x_197_);
lean_dec(v_fst_180_);
lean_dec(v_fst_176_);
v_a_487_ = lean_ctor_get(v___x_468_, 0);
v_isSharedCheck_494_ = !lean_is_exclusive(v___x_468_);
if (v_isSharedCheck_494_ == 0)
{
v___x_489_ = v___x_468_;
v_isShared_490_ = v_isSharedCheck_494_;
goto v_resetjp_488_;
}
else
{
lean_inc(v_a_487_);
lean_dec(v___x_468_);
v___x_489_ = lean_box(0);
v_isShared_490_ = v_isSharedCheck_494_;
goto v_resetjp_488_;
}
v_resetjp_488_:
{
lean_object* v___x_492_; 
if (v_isShared_490_ == 0)
{
v___x_492_ = v___x_489_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v_a_487_);
v___x_492_ = v_reuseFailAlloc_493_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
return v___x_492_;
}
}
}
}
}
else
{
lean_object* v___x_495_; 
lean_dec_ref(v___x_275_);
lean_del_object(v___x_195_);
lean_del_object(v___x_190_);
lean_dec_ref(v___f_186_);
lean_del_object(v___x_183_);
lean_del_object(v___x_178_);
lean_del_object(v___x_173_);
lean_del_object(v___x_169_);
v___x_495_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(v_snd_181_, v_a_161_, v_a_162_, v_a_163_, v_a_164_);
if (lean_obj_tag(v___x_495_) == 0)
{
lean_object* v_a_496_; lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_513_; 
v_a_496_ = lean_ctor_get(v___x_495_, 0);
v_isSharedCheck_513_ = !lean_is_exclusive(v___x_495_);
if (v_isSharedCheck_513_ == 0)
{
v___x_498_ = v___x_495_;
v_isShared_499_ = v_isSharedCheck_513_;
goto v_resetjp_497_;
}
else
{
lean_inc(v_a_496_);
lean_dec(v___x_495_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_513_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_511_; 
v___x_500_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8);
v___x_501_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__44, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__44_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__44);
v___x_502_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_176_);
v___x_503_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_180_);
v___x_504_ = l_Lean_eagerReflBoolTrue;
v___x_505_ = l_Lean_mkApp4(v___x_501_, v_a_496_, v___x_502_, v___x_503_, v___x_504_);
v___x_506_ = l_Lean_mkPropEq(v___x_197_, v___x_500_);
v___x_507_ = l_Lean_Meta_mkExpectedPropHint(v___x_505_, v___x_506_);
v___x_508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_508_, 0, v___x_500_);
lean_ctor_set(v___x_508_, 1, v___x_507_);
v___x_509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_509_, 0, v___x_508_);
if (v_isShared_499_ == 0)
{
lean_ctor_set(v___x_498_, 0, v___x_509_);
v___x_511_ = v___x_498_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v___x_509_);
v___x_511_ = v_reuseFailAlloc_512_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
return v___x_511_;
}
}
}
else
{
lean_object* v_a_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_521_; 
lean_dec_ref(v___x_197_);
lean_dec(v_fst_180_);
lean_dec(v_fst_176_);
v_a_514_ = lean_ctor_get(v___x_495_, 0);
v_isSharedCheck_521_ = !lean_is_exclusive(v___x_495_);
if (v_isSharedCheck_521_ == 0)
{
v___x_516_ = v___x_495_;
v_isShared_517_ = v_isSharedCheck_521_;
goto v_resetjp_515_;
}
else
{
lean_inc(v_a_514_);
lean_dec(v___x_495_);
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
v___jp_198_:
{
lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_210_; 
v___x_205_ = l_Lean_eagerReflBoolTrue;
lean_inc_ref(v___y_200_);
v___x_206_ = l_Lean_mkApp5(v___y_200_, v___y_202_, v___y_201_, v___y_203_, v___y_204_, v___x_205_);
lean_inc_ref_n(v___y_199_, 2);
v___x_207_ = l_Lean_mkPropEq(v___x_197_, v___y_199_);
v___x_208_ = l_Lean_Meta_mkExpectedPropHint(v___x_206_, v___x_207_);
if (v_isShared_184_ == 0)
{
lean_ctor_set(v___x_183_, 1, v___x_208_);
lean_ctor_set(v___x_183_, 0, v___y_199_);
v___x_210_ = v___x_183_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_217_; 
v_reuseFailAlloc_217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_217_, 0, v___y_199_);
lean_ctor_set(v_reuseFailAlloc_217_, 1, v___x_208_);
v___x_210_ = v_reuseFailAlloc_217_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
lean_object* v___x_212_; 
if (v_isShared_174_ == 0)
{
lean_ctor_set(v___x_173_, 0, v___x_210_);
v___x_212_ = v___x_173_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_216_; 
v_reuseFailAlloc_216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_216_, 0, v___x_210_);
v___x_212_ = v_reuseFailAlloc_216_;
goto v_reusejp_211_;
}
v_reusejp_211_:
{
lean_object* v___x_214_; 
if (v_isShared_196_ == 0)
{
lean_ctor_set(v___x_195_, 0, v___x_212_);
v___x_214_ = v___x_195_;
goto v_reusejp_213_;
}
else
{
lean_object* v_reuseFailAlloc_215_; 
v_reuseFailAlloc_215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v___x_212_);
v___x_214_ = v_reuseFailAlloc_215_;
goto v_reusejp_213_;
}
v_reusejp_213_:
{
return v___x_214_;
}
}
}
}
v___jp_218_:
{
lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_231_; 
v___x_226_ = l_Lean_eagerReflBoolTrue;
lean_inc_ref(v___y_223_);
v___x_227_ = l_Lean_mkApp6(v___y_223_, v___y_222_, v___y_219_, v___y_221_, v___y_224_, v___y_225_, v___x_226_);
lean_inc_ref(v___y_220_);
v___x_228_ = l_Lean_mkPropEq(v___x_197_, v___y_220_);
v___x_229_ = l_Lean_Meta_mkExpectedPropHint(v___x_227_, v___x_228_);
if (v_isShared_179_ == 0)
{
lean_ctor_set(v___x_178_, 1, v___x_229_);
lean_ctor_set(v___x_178_, 0, v___y_220_);
v___x_231_ = v___x_178_;
goto v_reusejp_230_;
}
else
{
lean_object* v_reuseFailAlloc_236_; 
v_reuseFailAlloc_236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v___y_220_);
lean_ctor_set(v_reuseFailAlloc_236_, 1, v___x_229_);
v___x_231_ = v_reuseFailAlloc_236_;
goto v_reusejp_230_;
}
v_reusejp_230_:
{
lean_object* v___x_232_; lean_object* v___x_234_; 
v___x_232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_232_, 0, v___x_231_);
if (v_isShared_191_ == 0)
{
lean_ctor_set(v___x_190_, 0, v___x_232_);
v___x_234_ = v___x_190_;
goto v_reusejp_233_;
}
else
{
lean_object* v_reuseFailAlloc_235_; 
v_reuseFailAlloc_235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_235_, 0, v___x_232_);
v___x_234_ = v_reuseFailAlloc_235_;
goto v_reusejp_233_;
}
v_reusejp_233_:
{
return v___x_234_;
}
}
}
v___jp_237_:
{
lean_object* v___x_241_; uint8_t v___x_242_; 
lean_inc_ref(v___y_240_);
v___x_241_ = l_Lean_mkIntEq(v___y_238_, v___y_240_);
v___x_242_ = lean_expr_eqv(v___x_241_, v___x_197_);
if (v___x_242_ == 0)
{
lean_object* v___x_243_; 
lean_del_object(v___x_169_);
v___x_243_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(v_snd_181_, v_a_161_, v_a_162_, v_a_163_, v_a_164_);
if (lean_obj_tag(v___x_243_) == 0)
{
lean_object* v_a_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_261_; 
v_a_244_ = lean_ctor_get(v___x_243_, 0);
v_isSharedCheck_261_ = !lean_is_exclusive(v___x_243_);
if (v_isSharedCheck_261_ == 0)
{
v___x_246_ = v___x_243_;
v_isShared_247_ = v_isSharedCheck_261_;
goto v_resetjp_245_;
}
else
{
lean_inc(v_a_244_);
lean_dec(v___x_243_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_261_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_259_; 
v___x_248_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__4, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__4_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__4);
v___x_249_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_176_);
v___x_250_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_180_);
v___x_251_ = l_Lean_mkNatLit(v___y_239_);
v___x_252_ = l_Lean_eagerReflBoolTrue;
v___x_253_ = l_Lean_mkApp6(v___x_248_, v_a_244_, v___x_249_, v___x_250_, v___x_251_, v___y_240_, v___x_252_);
lean_inc_ref(v___x_241_);
v___x_254_ = l_Lean_mkPropEq(v___x_197_, v___x_241_);
v___x_255_ = l_Lean_Meta_mkExpectedPropHint(v___x_253_, v___x_254_);
v___x_256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_256_, 0, v___x_241_);
lean_ctor_set(v___x_256_, 1, v___x_255_);
v___x_257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_257_, 0, v___x_256_);
if (v_isShared_247_ == 0)
{
lean_ctor_set(v___x_246_, 0, v___x_257_);
v___x_259_ = v___x_246_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v___x_257_);
v___x_259_ = v_reuseFailAlloc_260_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
return v___x_259_;
}
}
}
else
{
lean_object* v_a_262_; lean_object* v___x_264_; uint8_t v_isShared_265_; uint8_t v_isSharedCheck_269_; 
lean_dec_ref(v___x_241_);
lean_dec_ref(v___y_240_);
lean_dec(v___y_239_);
lean_dec_ref(v___x_197_);
lean_dec(v_fst_180_);
lean_dec(v_fst_176_);
v_a_262_ = lean_ctor_get(v___x_243_, 0);
v_isSharedCheck_269_ = !lean_is_exclusive(v___x_243_);
if (v_isSharedCheck_269_ == 0)
{
v___x_264_ = v___x_243_;
v_isShared_265_ = v_isSharedCheck_269_;
goto v_resetjp_263_;
}
else
{
lean_inc(v_a_262_);
lean_dec(v___x_243_);
v___x_264_ = lean_box(0);
v_isShared_265_ = v_isSharedCheck_269_;
goto v_resetjp_263_;
}
v_resetjp_263_:
{
lean_object* v___x_267_; 
if (v_isShared_265_ == 0)
{
v___x_267_ = v___x_264_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v_a_262_);
v___x_267_ = v_reuseFailAlloc_268_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
return v___x_267_;
}
}
}
}
else
{
lean_object* v___x_270_; lean_object* v___x_272_; 
lean_dec_ref(v___x_241_);
lean_dec_ref(v___y_240_);
lean_dec(v___y_239_);
lean_dec_ref(v___x_197_);
lean_dec(v_snd_181_);
lean_dec(v_fst_180_);
lean_dec(v_fst_176_);
v___x_270_ = lean_box(0);
if (v_isShared_170_ == 0)
{
lean_ctor_set(v___x_169_, 0, v___x_270_);
v___x_272_ = v___x_169_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_273_; 
v_reuseFailAlloc_273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_273_, 0, v___x_270_);
v___x_272_ = v_reuseFailAlloc_273_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
return v___x_272_;
}
}
}
v___jp_276_:
{
lean_object* v___x_281_; lean_object* v___x_282_; uint8_t v___x_283_; 
v___x_281_ = l_Int_Linear_Poly_gcdCoeffs_x27(v___x_275_);
v___x_282_ = lean_unsigned_to_nat(1u);
v___x_283_ = lean_nat_dec_eq(v___x_281_, v___x_282_);
if (v___x_283_ == 0)
{
lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; uint8_t v___x_288_; 
v___x_284_ = l_Int_Linear_Poly_getConst(v___x_275_);
v___x_285_ = lean_nat_to_int(v___x_281_);
v___x_286_ = lean_int_emod(v___x_284_, v___x_285_);
lean_dec(v___x_284_);
v___x_287_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5);
v___x_288_ = lean_int_dec_eq(v___x_286_, v___x_287_);
lean_dec(v___x_286_);
if (v___x_288_ == 0)
{
lean_object* v___x_289_; 
lean_dec_ref(v___x_275_);
lean_del_object(v___x_190_);
lean_dec_ref(v___f_186_);
lean_del_object(v___x_178_);
v___x_289_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(v_snd_181_, v___y_277_, v___y_278_, v___y_279_, v___y_280_);
if (lean_obj_tag(v___x_289_) == 0)
{
lean_object* v_a_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; uint8_t v___x_295_; 
v_a_290_ = lean_ctor_get(v___x_289_, 0);
lean_inc(v_a_290_);
lean_dec_ref(v___x_289_);
v___x_291_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8);
v___x_292_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__11, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__11_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__11);
v___x_293_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_176_);
v___x_294_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_180_);
v___x_295_ = lean_int_dec_le(v___x_287_, v___x_285_);
if (v___x_295_ == 0)
{
lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_296_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17);
v___x_297_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19);
v___x_298_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22);
v___x_299_ = lean_int_neg(v___x_285_);
lean_dec(v___x_285_);
v___x_300_ = l_Int_toNat(v___x_299_);
lean_dec(v___x_299_);
v___x_301_ = l_Lean_instToExprInt_mkNat(v___x_300_);
v___x_302_ = l_Lean_mkApp3(v___x_296_, v___x_297_, v___x_298_, v___x_301_);
v___y_199_ = v___x_291_;
v___y_200_ = v___x_292_;
v___y_201_ = v___x_293_;
v___y_202_ = v_a_290_;
v___y_203_ = v___x_294_;
v___y_204_ = v___x_302_;
goto v___jp_198_;
}
else
{
lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_303_ = l_Int_toNat(v___x_285_);
lean_dec(v___x_285_);
v___x_304_ = l_Lean_instToExprInt_mkNat(v___x_303_);
v___y_199_ = v___x_291_;
v___y_200_ = v___x_292_;
v___y_201_ = v___x_293_;
v___y_202_ = v_a_290_;
v___y_203_ = v___x_294_;
v___y_204_ = v___x_304_;
goto v___jp_198_;
}
}
else
{
lean_object* v_a_305_; lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_312_; 
lean_dec(v___x_285_);
lean_dec_ref(v___x_197_);
lean_del_object(v___x_195_);
lean_del_object(v___x_183_);
lean_dec(v_fst_180_);
lean_dec(v_fst_176_);
lean_del_object(v___x_173_);
v_a_305_ = lean_ctor_get(v___x_289_, 0);
v_isSharedCheck_312_ = !lean_is_exclusive(v___x_289_);
if (v_isSharedCheck_312_ == 0)
{
v___x_307_ = v___x_289_;
v_isShared_308_ = v_isSharedCheck_312_;
goto v_resetjp_306_;
}
else
{
lean_inc(v_a_305_);
lean_dec(v___x_289_);
v___x_307_ = lean_box(0);
v_isShared_308_ = v_isSharedCheck_312_;
goto v_resetjp_306_;
}
v_resetjp_306_:
{
lean_object* v___x_310_; 
if (v_isShared_308_ == 0)
{
v___x_310_ = v___x_307_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_311_; 
v_reuseFailAlloc_311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_311_, 0, v_a_305_);
v___x_310_ = v_reuseFailAlloc_311_;
goto v_reusejp_309_;
}
v_reusejp_309_:
{
return v___x_310_;
}
}
}
}
else
{
lean_object* v___x_313_; lean_object* v___x_314_; 
lean_del_object(v___x_195_);
lean_del_object(v___x_183_);
lean_del_object(v___x_173_);
v___x_313_ = l_Int_Linear_Poly_div(v___x_285_, v___x_275_);
lean_inc_ref(v___x_313_);
v___x_314_ = l_Int_Linear_Poly_denoteExpr___redArg(v___f_186_, v___x_313_);
if (lean_obj_tag(v___x_314_) == 0)
{
lean_object* v_a_315_; lean_object* v___x_316_; 
v_a_315_ = lean_ctor_get(v___x_314_, 0);
lean_inc(v_a_315_);
lean_dec_ref(v___x_314_);
v___x_316_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(v_snd_181_, v___y_277_, v___y_278_, v___y_279_, v___y_280_);
if (lean_obj_tag(v___x_316_) == 0)
{
lean_object* v_a_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; uint8_t v___x_324_; 
v_a_317_ = lean_ctor_get(v___x_316_, 0);
lean_inc(v_a_317_);
lean_dec_ref(v___x_316_);
v___x_318_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23);
v___x_319_ = l_Lean_mkIntEq(v_a_315_, v___x_318_);
v___x_320_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__26, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__26_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__26);
v___x_321_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_176_);
v___x_322_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_180_);
v___x_323_ = l_Lean_Meta_Simp_Arith_Int_ofPoly(v___x_313_);
v___x_324_ = lean_int_dec_le(v___x_287_, v___x_285_);
if (v___x_324_ == 0)
{
lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_325_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17);
v___x_326_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19);
v___x_327_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22);
v___x_328_ = lean_int_neg(v___x_285_);
lean_dec(v___x_285_);
v___x_329_ = l_Int_toNat(v___x_328_);
lean_dec(v___x_328_);
v___x_330_ = l_Lean_instToExprInt_mkNat(v___x_329_);
v___x_331_ = l_Lean_mkApp3(v___x_325_, v___x_326_, v___x_327_, v___x_330_);
v___y_219_ = v___x_321_;
v___y_220_ = v___x_319_;
v___y_221_ = v___x_322_;
v___y_222_ = v_a_317_;
v___y_223_ = v___x_320_;
v___y_224_ = v___x_323_;
v___y_225_ = v___x_331_;
goto v___jp_218_;
}
else
{
lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_332_ = l_Int_toNat(v___x_285_);
lean_dec(v___x_285_);
v___x_333_ = l_Lean_instToExprInt_mkNat(v___x_332_);
v___y_219_ = v___x_321_;
v___y_220_ = v___x_319_;
v___y_221_ = v___x_322_;
v___y_222_ = v_a_317_;
v___y_223_ = v___x_320_;
v___y_224_ = v___x_323_;
v___y_225_ = v___x_333_;
goto v___jp_218_;
}
}
else
{
lean_object* v_a_334_; lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_341_; 
lean_dec(v_a_315_);
lean_dec_ref(v___x_313_);
lean_dec(v___x_285_);
lean_dec_ref(v___x_197_);
lean_del_object(v___x_190_);
lean_dec(v_fst_180_);
lean_del_object(v___x_178_);
lean_dec(v_fst_176_);
v_a_334_ = lean_ctor_get(v___x_316_, 0);
v_isSharedCheck_341_ = !lean_is_exclusive(v___x_316_);
if (v_isSharedCheck_341_ == 0)
{
v___x_336_ = v___x_316_;
v_isShared_337_ = v_isSharedCheck_341_;
goto v_resetjp_335_;
}
else
{
lean_inc(v_a_334_);
lean_dec(v___x_316_);
v___x_336_ = lean_box(0);
v_isShared_337_ = v_isSharedCheck_341_;
goto v_resetjp_335_;
}
v_resetjp_335_:
{
lean_object* v___x_339_; 
if (v_isShared_337_ == 0)
{
v___x_339_ = v___x_336_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v_a_334_);
v___x_339_ = v_reuseFailAlloc_340_;
goto v_reusejp_338_;
}
v_reusejp_338_:
{
return v___x_339_;
}
}
}
}
else
{
lean_object* v_a_342_; lean_object* v___x_344_; uint8_t v_isShared_345_; uint8_t v_isSharedCheck_349_; 
lean_dec_ref(v___x_313_);
lean_dec(v___x_285_);
lean_dec_ref(v___x_197_);
lean_del_object(v___x_190_);
lean_dec(v_snd_181_);
lean_dec(v_fst_180_);
lean_del_object(v___x_178_);
lean_dec(v_fst_176_);
v_a_342_ = lean_ctor_get(v___x_314_, 0);
v_isSharedCheck_349_ = !lean_is_exclusive(v___x_314_);
if (v_isSharedCheck_349_ == 0)
{
v___x_344_ = v___x_314_;
v_isShared_345_ = v_isSharedCheck_349_;
goto v_resetjp_343_;
}
else
{
lean_inc(v_a_342_);
lean_dec(v___x_314_);
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
}
else
{
lean_object* v___x_350_; 
lean_dec(v___x_281_);
lean_del_object(v___x_195_);
lean_del_object(v___x_190_);
lean_del_object(v___x_183_);
lean_del_object(v___x_178_);
lean_del_object(v___x_173_);
lean_inc_ref(v___x_275_);
v___x_350_ = l_Int_Linear_Poly_denoteExpr___redArg(v___f_186_, v___x_275_);
if (lean_obj_tag(v___x_350_) == 0)
{
lean_object* v_a_351_; lean_object* v___x_352_; 
v_a_351_ = lean_ctor_get(v___x_350_, 0);
lean_inc(v_a_351_);
lean_dec_ref(v___x_350_);
v___x_352_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(v_snd_181_, v___y_277_, v___y_278_, v___y_279_, v___y_280_);
if (lean_obj_tag(v___x_352_) == 0)
{
lean_object* v_a_353_; lean_object* v___x_355_; uint8_t v_isShared_356_; uint8_t v_isSharedCheck_372_; 
v_a_353_ = lean_ctor_get(v___x_352_, 0);
v_isSharedCheck_372_ = !lean_is_exclusive(v___x_352_);
if (v_isSharedCheck_372_ == 0)
{
v___x_355_ = v___x_352_;
v_isShared_356_ = v_isSharedCheck_372_;
goto v_resetjp_354_;
}
else
{
lean_inc(v_a_353_);
lean_dec(v___x_352_);
v___x_355_ = lean_box(0);
v_isShared_356_ = v_isSharedCheck_372_;
goto v_resetjp_354_;
}
v_resetjp_354_:
{
lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_370_; 
v___x_357_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23);
v___x_358_ = l_Lean_mkIntEq(v_a_351_, v___x_357_);
v___x_359_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__29, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__29_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__29);
v___x_360_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_176_);
v___x_361_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_180_);
v___x_362_ = l_Lean_Meta_Simp_Arith_Int_ofPoly(v___x_275_);
v___x_363_ = l_Lean_eagerReflBoolTrue;
v___x_364_ = l_Lean_mkApp5(v___x_359_, v_a_353_, v___x_360_, v___x_361_, v___x_362_, v___x_363_);
lean_inc_ref(v___x_358_);
v___x_365_ = l_Lean_mkPropEq(v___x_197_, v___x_358_);
v___x_366_ = l_Lean_Meta_mkExpectedPropHint(v___x_364_, v___x_365_);
v___x_367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_367_, 0, v___x_358_);
lean_ctor_set(v___x_367_, 1, v___x_366_);
v___x_368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_368_, 0, v___x_367_);
if (v_isShared_356_ == 0)
{
lean_ctor_set(v___x_355_, 0, v___x_368_);
v___x_370_ = v___x_355_;
goto v_reusejp_369_;
}
else
{
lean_object* v_reuseFailAlloc_371_; 
v_reuseFailAlloc_371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_371_, 0, v___x_368_);
v___x_370_ = v_reuseFailAlloc_371_;
goto v_reusejp_369_;
}
v_reusejp_369_:
{
return v___x_370_;
}
}
}
else
{
lean_object* v_a_373_; lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_380_; 
lean_dec(v_a_351_);
lean_dec_ref(v___x_275_);
lean_dec_ref(v___x_197_);
lean_dec(v_fst_180_);
lean_dec(v_fst_176_);
v_a_373_ = lean_ctor_get(v___x_352_, 0);
v_isSharedCheck_380_ = !lean_is_exclusive(v___x_352_);
if (v_isSharedCheck_380_ == 0)
{
v___x_375_ = v___x_352_;
v_isShared_376_ = v_isSharedCheck_380_;
goto v_resetjp_374_;
}
else
{
lean_inc(v_a_373_);
lean_dec(v___x_352_);
v___x_375_ = lean_box(0);
v_isShared_376_ = v_isSharedCheck_380_;
goto v_resetjp_374_;
}
v_resetjp_374_:
{
lean_object* v___x_378_; 
if (v_isShared_376_ == 0)
{
v___x_378_ = v___x_375_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v_a_373_);
v___x_378_ = v_reuseFailAlloc_379_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
return v___x_378_;
}
}
}
}
else
{
lean_object* v_a_381_; lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_388_; 
lean_dec_ref(v___x_275_);
lean_dec_ref(v___x_197_);
lean_dec(v_snd_181_);
lean_dec(v_fst_180_);
lean_dec(v_fst_176_);
v_a_381_ = lean_ctor_get(v___x_350_, 0);
v_isSharedCheck_388_ = !lean_is_exclusive(v___x_350_);
if (v_isSharedCheck_388_ == 0)
{
v___x_383_ = v___x_350_;
v_isShared_384_ = v_isSharedCheck_388_;
goto v_resetjp_382_;
}
else
{
lean_inc(v_a_381_);
lean_dec(v___x_350_);
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
}
v___jp_389_:
{
if (v___y_390_ == 0)
{
if (lean_obj_tag(v___x_275_) == 1)
{
lean_object* v_k_391_; lean_object* v_v_392_; lean_object* v_p_393_; lean_object* v___x_394_; uint8_t v___x_395_; 
v_k_391_ = lean_ctor_get(v___x_275_, 0);
lean_inc(v_k_391_);
v_v_392_ = lean_ctor_get(v___x_275_, 1);
lean_inc(v_v_392_);
v_p_393_ = lean_ctor_get(v___x_275_, 2);
lean_inc_ref(v_p_393_);
v___x_394_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30);
v___x_395_ = lean_int_dec_eq(v_k_391_, v___x_394_);
lean_dec(v_k_391_);
if (v___x_395_ == 0)
{
lean_dec_ref(v_p_393_);
lean_dec(v_v_392_);
lean_del_object(v___x_169_);
v___y_277_ = v_a_161_;
v___y_278_ = v_a_162_;
v___y_279_ = v_a_163_;
v___y_280_ = v_a_164_;
goto v___jp_276_;
}
else
{
if (lean_obj_tag(v_p_393_) == 0)
{
lean_object* v_k_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; uint8_t v___x_400_; 
lean_dec_ref(v___x_275_);
lean_del_object(v___x_195_);
lean_del_object(v___x_190_);
lean_dec_ref(v___f_186_);
lean_del_object(v___x_183_);
lean_del_object(v___x_178_);
lean_del_object(v___x_173_);
v_k_396_ = lean_ctor_get(v_p_393_, 0);
lean_inc(v_k_396_);
lean_dec_ref(v_p_393_);
v___x_397_ = lean_array_get_borrowed(v___x_185_, v_snd_181_, v_v_392_);
v___x_398_ = lean_int_neg(v_k_396_);
lean_dec(v_k_396_);
v___x_399_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5);
v___x_400_ = lean_int_dec_le(v___x_399_, v___x_398_);
if (v___x_400_ == 0)
{
lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_401_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17);
v___x_402_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19);
v___x_403_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22);
v___x_404_ = lean_int_neg(v___x_398_);
lean_dec(v___x_398_);
v___x_405_ = l_Int_toNat(v___x_404_);
lean_dec(v___x_404_);
v___x_406_ = l_Lean_instToExprInt_mkNat(v___x_405_);
v___x_407_ = l_Lean_mkApp3(v___x_401_, v___x_402_, v___x_403_, v___x_406_);
lean_inc(v___x_397_);
v___y_238_ = v___x_397_;
v___y_239_ = v_v_392_;
v___y_240_ = v___x_407_;
goto v___jp_237_;
}
else
{
lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_408_ = l_Int_toNat(v___x_398_);
lean_dec(v___x_398_);
v___x_409_ = l_Lean_instToExprInt_mkNat(v___x_408_);
lean_inc(v___x_397_);
v___y_238_ = v___x_397_;
v___y_239_ = v_v_392_;
v___y_240_ = v___x_409_;
goto v___jp_237_;
}
}
else
{
lean_object* v_k_410_; lean_object* v_v_411_; lean_object* v_p_412_; lean_object* v___x_413_; uint8_t v___x_414_; 
lean_del_object(v___x_169_);
v_k_410_ = lean_ctor_get(v_p_393_, 0);
lean_inc(v_k_410_);
v_v_411_ = lean_ctor_get(v_p_393_, 1);
lean_inc(v_v_411_);
v_p_412_ = lean_ctor_get(v_p_393_, 2);
lean_inc_ref(v_p_412_);
lean_dec_ref(v_p_393_);
v___x_413_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__31, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__31_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__31);
v___x_414_ = lean_int_dec_eq(v_k_410_, v___x_413_);
lean_dec(v_k_410_);
if (v___x_414_ == 0)
{
lean_dec_ref(v_p_412_);
lean_dec(v_v_411_);
lean_dec(v_v_392_);
v___y_277_ = v_a_161_;
v___y_278_ = v_a_162_;
v___y_279_ = v_a_163_;
v___y_280_ = v_a_164_;
goto v___jp_276_;
}
else
{
if (lean_obj_tag(v_p_412_) == 0)
{
lean_object* v_k_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_459_; 
v_k_415_ = lean_ctor_get(v_p_412_, 0);
v_isSharedCheck_459_ = !lean_is_exclusive(v_p_412_);
if (v_isSharedCheck_459_ == 0)
{
v___x_417_ = v_p_412_;
v_isShared_418_ = v_isSharedCheck_459_;
goto v_resetjp_416_;
}
else
{
lean_inc(v_k_415_);
lean_dec(v_p_412_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_459_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
lean_object* v___x_419_; uint8_t v___x_420_; 
v___x_419_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5);
v___x_420_ = lean_int_dec_eq(v_k_415_, v___x_419_);
lean_dec(v_k_415_);
if (v___x_420_ == 0)
{
lean_del_object(v___x_417_);
lean_dec(v_v_411_);
lean_dec(v_v_392_);
v___y_277_ = v_a_161_;
v___y_278_ = v_a_162_;
v___y_279_ = v_a_163_;
v___y_280_ = v_a_164_;
goto v___jp_276_;
}
else
{
lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; uint8_t v___x_424_; 
lean_dec_ref(v___x_275_);
lean_del_object(v___x_195_);
lean_del_object(v___x_190_);
lean_dec_ref(v___f_186_);
lean_del_object(v___x_183_);
lean_del_object(v___x_178_);
lean_del_object(v___x_173_);
v___x_421_ = lean_array_get_borrowed(v___x_185_, v_snd_181_, v_v_392_);
v___x_422_ = lean_array_get_borrowed(v___x_185_, v_snd_181_, v_v_411_);
lean_inc(v___x_422_);
lean_inc(v___x_421_);
v___x_423_ = l_Lean_mkIntEq(v___x_421_, v___x_422_);
v___x_424_ = lean_expr_eqv(v___x_423_, v___x_197_);
if (v___x_424_ == 0)
{
lean_object* v___x_425_; 
v___x_425_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(v_snd_181_, v_a_161_, v_a_162_, v_a_163_, v_a_164_);
if (lean_obj_tag(v___x_425_) == 0)
{
lean_object* v_a_426_; lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_446_; 
v_a_426_ = lean_ctor_get(v___x_425_, 0);
v_isSharedCheck_446_ = !lean_is_exclusive(v___x_425_);
if (v_isSharedCheck_446_ == 0)
{
v___x_428_ = v___x_425_;
v_isShared_429_ = v_isSharedCheck_446_;
goto v_resetjp_427_;
}
else
{
lean_inc(v_a_426_);
lean_dec(v___x_425_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_446_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_441_; 
v___x_430_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__34, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__34_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__34);
v___x_431_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_176_);
v___x_432_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_180_);
v___x_433_ = l_Lean_mkNatLit(v_v_392_);
v___x_434_ = l_Lean_mkNatLit(v_v_411_);
v___x_435_ = l_Lean_eagerReflBoolTrue;
v___x_436_ = l_Lean_mkApp6(v___x_430_, v_a_426_, v___x_431_, v___x_432_, v___x_433_, v___x_434_, v___x_435_);
lean_inc_ref(v___x_423_);
v___x_437_ = l_Lean_mkPropEq(v___x_197_, v___x_423_);
v___x_438_ = l_Lean_Meta_mkExpectedPropHint(v___x_436_, v___x_437_);
v___x_439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_439_, 0, v___x_423_);
lean_ctor_set(v___x_439_, 1, v___x_438_);
if (v_isShared_418_ == 0)
{
lean_ctor_set_tag(v___x_417_, 1);
lean_ctor_set(v___x_417_, 0, v___x_439_);
v___x_441_ = v___x_417_;
goto v_reusejp_440_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v___x_439_);
v___x_441_ = v_reuseFailAlloc_445_;
goto v_reusejp_440_;
}
v_reusejp_440_:
{
lean_object* v___x_443_; 
if (v_isShared_429_ == 0)
{
lean_ctor_set(v___x_428_, 0, v___x_441_);
v___x_443_ = v___x_428_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v___x_441_);
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
else
{
lean_object* v_a_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_454_; 
lean_dec_ref(v___x_423_);
lean_del_object(v___x_417_);
lean_dec(v_v_411_);
lean_dec(v_v_392_);
lean_dec_ref(v___x_197_);
lean_dec(v_fst_180_);
lean_dec(v_fst_176_);
v_a_447_ = lean_ctor_get(v___x_425_, 0);
v_isSharedCheck_454_ = !lean_is_exclusive(v___x_425_);
if (v_isSharedCheck_454_ == 0)
{
v___x_449_ = v___x_425_;
v_isShared_450_ = v_isSharedCheck_454_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_a_447_);
lean_dec(v___x_425_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_454_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v___x_452_; 
if (v_isShared_450_ == 0)
{
v___x_452_ = v___x_449_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v_a_447_);
v___x_452_ = v_reuseFailAlloc_453_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
return v___x_452_;
}
}
}
}
else
{
lean_object* v___x_455_; lean_object* v___x_457_; 
lean_dec_ref(v___x_423_);
lean_dec(v_v_411_);
lean_dec(v_v_392_);
lean_dec_ref(v___x_197_);
lean_dec(v_snd_181_);
lean_dec(v_fst_180_);
lean_dec(v_fst_176_);
v___x_455_ = lean_box(0);
if (v_isShared_418_ == 0)
{
lean_ctor_set(v___x_417_, 0, v___x_455_);
v___x_457_ = v___x_417_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v___x_455_);
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
}
else
{
lean_dec_ref(v_p_412_);
lean_dec(v_v_411_);
lean_dec(v_v_392_);
v___y_277_ = v_a_161_;
v___y_278_ = v_a_162_;
v___y_279_ = v_a_163_;
v___y_280_ = v_a_164_;
goto v___jp_276_;
}
}
}
}
}
else
{
lean_del_object(v___x_169_);
v___y_277_ = v_a_161_;
v___y_278_ = v_a_162_;
v___y_279_ = v_a_163_;
v___y_280_ = v_a_164_;
goto v___jp_276_;
}
}
else
{
lean_object* v___x_460_; lean_object* v___x_461_; 
lean_dec_ref(v___x_275_);
lean_dec_ref(v___x_197_);
lean_del_object(v___x_195_);
lean_del_object(v___x_190_);
lean_dec_ref(v___f_186_);
lean_del_object(v___x_183_);
lean_dec(v_snd_181_);
lean_dec(v_fst_180_);
lean_del_object(v___x_178_);
lean_dec(v_fst_176_);
lean_del_object(v___x_173_);
lean_del_object(v___x_169_);
v___x_460_ = lean_box(0);
v___x_461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_461_, 0, v___x_460_);
return v___x_461_;
}
}
}
}
else
{
lean_object* v_a_523_; lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_530_; 
lean_del_object(v___x_190_);
lean_dec(v_a_188_);
lean_dec_ref(v___f_186_);
lean_del_object(v___x_183_);
lean_dec(v_snd_181_);
lean_dec(v_fst_180_);
lean_del_object(v___x_178_);
lean_dec(v_fst_176_);
lean_del_object(v___x_173_);
lean_del_object(v___x_169_);
v_a_523_ = lean_ctor_get(v___x_192_, 0);
v_isSharedCheck_530_ = !lean_is_exclusive(v___x_192_);
if (v_isSharedCheck_530_ == 0)
{
v___x_525_ = v___x_192_;
v_isShared_526_ = v_isSharedCheck_530_;
goto v_resetjp_524_;
}
else
{
lean_inc(v_a_523_);
lean_dec(v___x_192_);
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
else
{
lean_object* v_a_532_; lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_539_; 
lean_dec_ref(v___f_186_);
lean_del_object(v___x_183_);
lean_dec(v_snd_181_);
lean_dec(v_fst_180_);
lean_del_object(v___x_178_);
lean_dec(v_fst_176_);
lean_del_object(v___x_173_);
lean_del_object(v___x_169_);
v_a_532_ = lean_ctor_get(v___x_187_, 0);
v_isSharedCheck_539_ = !lean_is_exclusive(v___x_187_);
if (v_isSharedCheck_539_ == 0)
{
v___x_534_ = v___x_187_;
v_isShared_535_ = v_isSharedCheck_539_;
goto v_resetjp_533_;
}
else
{
lean_inc(v_a_532_);
lean_dec(v___x_187_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_539_;
goto v_resetjp_533_;
}
v_resetjp_533_:
{
lean_object* v___x_537_; 
if (v_isShared_535_ == 0)
{
v___x_537_ = v___x_534_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v_a_532_);
v___x_537_ = v_reuseFailAlloc_538_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
return v___x_537_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_543_; lean_object* v___x_545_; 
lean_dec(v_a_167_);
v___x_543_ = lean_box(0);
if (v_isShared_170_ == 0)
{
lean_ctor_set(v___x_169_, 0, v___x_543_);
v___x_545_ = v___x_169_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v___x_543_);
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
else
{
lean_object* v_a_548_; lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_555_; 
v_a_548_ = lean_ctor_get(v___x_166_, 0);
v_isSharedCheck_555_ = !lean_is_exclusive(v___x_166_);
if (v_isSharedCheck_555_ == 0)
{
v___x_550_ = v___x_166_;
v_isShared_551_ = v_isSharedCheck_555_;
goto v_resetjp_549_;
}
else
{
lean_inc(v_a_548_);
lean_dec(v___x_166_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_555_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
lean_object* v___x_553_; 
if (v_isShared_551_ == 0)
{
v___x_553_ = v___x_550_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v_a_548_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___boxed(lean_object* v_e_556_, lean_object* v_a_557_, lean_object* v_a_558_, lean_object* v_a_559_, lean_object* v_a_560_, lean_object* v_a_561_){
_start:
{
lean_object* v_res_562_; 
v_res_562_ = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f(v_e_556_, v_a_557_, v_a_558_, v_a_559_, v_a_560_);
lean_dec(v_a_560_);
lean_dec_ref(v_a_559_);
lean_dec(v_a_558_);
lean_dec_ref(v_a_557_);
return v_res_562_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__2(void){
_start:
{
lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; 
v___x_568_ = lean_box(0);
v___x_569_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__1));
v___x_570_ = l_Lean_mkConst(v___x_569_, v___x_568_);
return v___x_570_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__5(void){
_start:
{
lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_576_ = lean_box(0);
v___x_577_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__4));
v___x_578_ = l_Lean_mkConst(v___x_577_, v___x_576_);
return v___x_578_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__8(void){
_start:
{
lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; 
v___x_584_ = lean_box(0);
v___x_585_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__7));
v___x_586_ = l_Lean_mkConst(v___x_585_, v___x_584_);
return v___x_586_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__11(void){
_start:
{
lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; 
v___x_592_ = lean_box(0);
v___x_593_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__10));
v___x_594_ = l_Lean_mkConst(v___x_593_, v___x_592_);
return v___x_594_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__14(void){
_start:
{
lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; 
v___x_600_ = lean_box(0);
v___x_601_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__13));
v___x_602_ = l_Lean_mkConst(v___x_601_, v___x_600_);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f(lean_object* v_e_608_, uint8_t v_checkIfModified_609_, lean_object* v_a_610_, lean_object* v_a_611_, lean_object* v_a_612_, lean_object* v_a_613_){
_start:
{
lean_object* v___y_616_; lean_object* v___y_617_; lean_object* v_h_618_; lean_object* v___y_625_; lean_object* v___y_626_; lean_object* v___y_627_; lean_object* v___y_628_; lean_object* v___y_629_; lean_object* v___y_630_; lean_object* v___y_631_; lean_object* v___y_632_; lean_object* v___y_636_; lean_object* v___y_637_; lean_object* v___y_638_; lean_object* v___y_639_; lean_object* v___y_640_; lean_object* v___y_641_; lean_object* v___y_642_; lean_object* v___y_643_; lean_object* v___y_647_; lean_object* v___y_648_; lean_object* v___y_649_; lean_object* v___y_650_; lean_object* v___y_651_; lean_object* v___y_652_; lean_object* v___y_653_; lean_object* v___y_654_; lean_object* v___y_655_; uint8_t v___y_656_; lean_object* v___y_727_; lean_object* v___y_728_; lean_object* v___y_729_; lean_object* v___y_730_; lean_object* v___y_731_; lean_object* v___y_732_; lean_object* v___x_782_; uint8_t v___y_784_; lean_object* v___x_922_; uint8_t v___x_923_; 
v___x_782_ = l_Lean_instInhabitedExpr;
v___x_922_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__17));
v___x_923_ = l_Lean_Expr_isAppOf(v_e_608_, v___x_922_);
if (v___x_923_ == 0)
{
v___y_784_ = v___x_923_;
goto v___jp_783_;
}
else
{
v___y_784_ = v_checkIfModified_609_;
goto v___jp_783_;
}
v___jp_615_:
{
lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; 
lean_inc_ref(v___y_617_);
v___x_619_ = l_Lean_mkPropEq(v___y_616_, v___y_617_);
v___x_620_ = l_Lean_Meta_mkExpectedPropHint(v_h_618_, v___x_619_);
v___x_621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_621_, 0, v___y_617_);
lean_ctor_set(v___x_621_, 1, v___x_620_);
v___x_622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_622_, 0, v___x_621_);
v___x_623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_623_, 0, v___x_622_);
return v___x_623_;
}
v___jp_624_:
{
lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_633_ = l_Lean_eagerReflBoolTrue;
lean_inc_ref(v___y_629_);
v___x_634_ = l_Lean_mkApp6(v___y_629_, v___y_628_, v___y_630_, v___y_631_, v___y_627_, v___y_632_, v___x_633_);
v___y_616_ = v___y_625_;
v___y_617_ = v___y_626_;
v_h_618_ = v___x_634_;
goto v___jp_615_;
}
v___jp_635_:
{
lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_644_ = l_Lean_eagerReflBoolTrue;
lean_inc_ref(v___y_640_);
v___x_645_ = l_Lean_mkApp6(v___y_640_, v___y_642_, v___y_641_, v___y_638_, v___y_639_, v___y_643_, v___x_644_);
v___y_616_ = v___y_636_;
v___y_617_ = v___y_637_;
v_h_618_ = v___x_645_;
goto v___jp_615_;
}
v___jp_646_:
{
lean_object* v___x_657_; lean_object* v___x_658_; 
v___x_657_ = l_Int_Linear_Poly_div(v___y_652_, v___y_651_);
lean_inc_ref(v___x_657_);
v___x_658_ = l_Int_Linear_Poly_denoteExpr___redArg(v___y_649_, v___x_657_);
if (lean_obj_tag(v___x_658_) == 0)
{
lean_object* v_a_659_; lean_object* v___x_660_; lean_object* v___x_661_; 
v_a_659_ = lean_ctor_get(v___x_658_, 0);
lean_inc(v_a_659_);
lean_dec_ref(v___x_658_);
v___x_660_ = l_Lean_mkIntLit(v___y_653_);
v___x_661_ = l_Lean_mkIntLE(v_a_659_, v___x_660_);
if (v___y_656_ == 0)
{
lean_object* v___x_662_; 
v___x_662_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(v___y_650_, v_a_610_, v_a_611_, v_a_612_, v_a_613_);
if (lean_obj_tag(v___x_662_) == 0)
{
lean_object* v_a_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; uint8_t v___x_669_; 
v_a_663_ = lean_ctor_get(v___x_662_, 0);
lean_inc(v_a_663_);
lean_dec_ref(v___x_662_);
v___x_664_ = lean_box(0);
v___x_665_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__2, &l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__2_once, _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__2);
v___x_666_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v___y_655_);
v___x_667_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v___y_648_);
v___x_668_ = l_Lean_Meta_Simp_Arith_Int_ofPoly(v___x_657_);
v___x_669_ = lean_int_dec_le(v___y_653_, v___y_652_);
if (v___x_669_ == 0)
{
lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; 
v___x_670_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__14));
v___x_671_ = l_Lean_Level_ofNat(v___y_654_);
v___x_672_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_672_, 0, v___x_671_);
lean_ctor_set(v___x_672_, 1, v___x_664_);
v___x_673_ = l_Lean_Expr_const___override(v___x_670_, v___x_672_);
v___x_674_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19);
v___x_675_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22);
v___x_676_ = lean_int_neg(v___y_652_);
lean_dec(v___y_652_);
v___x_677_ = l_Int_toNat(v___x_676_);
lean_dec(v___x_676_);
v___x_678_ = l_Lean_instToExprInt_mkNat(v___x_677_);
v___x_679_ = l_Lean_mkApp3(v___x_673_, v___x_674_, v___x_675_, v___x_678_);
v___y_636_ = v___y_647_;
v___y_637_ = v___x_661_;
v___y_638_ = v___x_667_;
v___y_639_ = v___x_668_;
v___y_640_ = v___x_665_;
v___y_641_ = v___x_666_;
v___y_642_ = v_a_663_;
v___y_643_ = v___x_679_;
goto v___jp_635_;
}
else
{
lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_680_ = l_Int_toNat(v___y_652_);
lean_dec(v___y_652_);
v___x_681_ = l_Lean_instToExprInt_mkNat(v___x_680_);
v___y_636_ = v___y_647_;
v___y_637_ = v___x_661_;
v___y_638_ = v___x_667_;
v___y_639_ = v___x_668_;
v___y_640_ = v___x_665_;
v___y_641_ = v___x_666_;
v___y_642_ = v_a_663_;
v___y_643_ = v___x_681_;
goto v___jp_635_;
}
}
else
{
lean_object* v_a_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_689_; 
lean_dec_ref(v___x_661_);
lean_dec_ref(v___x_657_);
lean_dec_ref(v___y_655_);
lean_dec(v___y_652_);
lean_dec_ref(v___y_648_);
lean_dec_ref(v___y_647_);
v_a_682_ = lean_ctor_get(v___x_662_, 0);
v_isSharedCheck_689_ = !lean_is_exclusive(v___x_662_);
if (v_isSharedCheck_689_ == 0)
{
v___x_684_ = v___x_662_;
v_isShared_685_ = v_isSharedCheck_689_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_a_682_);
lean_dec(v___x_662_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_689_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
lean_object* v___x_687_; 
if (v_isShared_685_ == 0)
{
v___x_687_ = v___x_684_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v_a_682_);
v___x_687_ = v_reuseFailAlloc_688_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
return v___x_687_;
}
}
}
}
else
{
lean_object* v___x_690_; 
v___x_690_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(v___y_650_, v_a_610_, v_a_611_, v_a_612_, v_a_613_);
if (lean_obj_tag(v___x_690_) == 0)
{
lean_object* v_a_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; uint8_t v___x_697_; 
v_a_691_ = lean_ctor_get(v___x_690_, 0);
lean_inc(v_a_691_);
lean_dec_ref(v___x_690_);
v___x_692_ = lean_box(0);
v___x_693_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__5, &l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__5_once, _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__5);
v___x_694_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v___y_655_);
v___x_695_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v___y_648_);
v___x_696_ = l_Lean_Meta_Simp_Arith_Int_ofPoly(v___x_657_);
v___x_697_ = lean_int_dec_le(v___y_653_, v___y_652_);
if (v___x_697_ == 0)
{
lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; 
v___x_698_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__14));
v___x_699_ = l_Lean_Level_ofNat(v___y_654_);
v___x_700_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_700_, 0, v___x_699_);
lean_ctor_set(v___x_700_, 1, v___x_692_);
v___x_701_ = l_Lean_Expr_const___override(v___x_698_, v___x_700_);
v___x_702_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19);
v___x_703_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22);
v___x_704_ = lean_int_neg(v___y_652_);
lean_dec(v___y_652_);
v___x_705_ = l_Int_toNat(v___x_704_);
lean_dec(v___x_704_);
v___x_706_ = l_Lean_instToExprInt_mkNat(v___x_705_);
v___x_707_ = l_Lean_mkApp3(v___x_701_, v___x_702_, v___x_703_, v___x_706_);
v___y_625_ = v___y_647_;
v___y_626_ = v___x_661_;
v___y_627_ = v___x_696_;
v___y_628_ = v_a_691_;
v___y_629_ = v___x_693_;
v___y_630_ = v___x_694_;
v___y_631_ = v___x_695_;
v___y_632_ = v___x_707_;
goto v___jp_624_;
}
else
{
lean_object* v___x_708_; lean_object* v___x_709_; 
v___x_708_ = l_Int_toNat(v___y_652_);
lean_dec(v___y_652_);
v___x_709_ = l_Lean_instToExprInt_mkNat(v___x_708_);
v___y_625_ = v___y_647_;
v___y_626_ = v___x_661_;
v___y_627_ = v___x_696_;
v___y_628_ = v_a_691_;
v___y_629_ = v___x_693_;
v___y_630_ = v___x_694_;
v___y_631_ = v___x_695_;
v___y_632_ = v___x_709_;
goto v___jp_624_;
}
}
else
{
lean_object* v_a_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_717_; 
lean_dec_ref(v___x_661_);
lean_dec_ref(v___x_657_);
lean_dec_ref(v___y_655_);
lean_dec(v___y_652_);
lean_dec_ref(v___y_648_);
lean_dec_ref(v___y_647_);
v_a_710_ = lean_ctor_get(v___x_690_, 0);
v_isSharedCheck_717_ = !lean_is_exclusive(v___x_690_);
if (v_isSharedCheck_717_ == 0)
{
v___x_712_ = v___x_690_;
v_isShared_713_ = v_isSharedCheck_717_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_a_710_);
lean_dec(v___x_690_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_717_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
lean_object* v___x_715_; 
if (v_isShared_713_ == 0)
{
v___x_715_ = v___x_712_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v_a_710_);
v___x_715_ = v_reuseFailAlloc_716_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
return v___x_715_;
}
}
}
}
}
else
{
lean_object* v_a_718_; lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_725_; 
lean_dec_ref(v___x_657_);
lean_dec_ref(v___y_655_);
lean_dec(v___y_652_);
lean_dec_ref(v___y_650_);
lean_dec_ref(v___y_648_);
lean_dec_ref(v___y_647_);
v_a_718_ = lean_ctor_get(v___x_658_, 0);
v_isSharedCheck_725_ = !lean_is_exclusive(v___x_658_);
if (v_isSharedCheck_725_ == 0)
{
v___x_720_ = v___x_658_;
v_isShared_721_ = v_isSharedCheck_725_;
goto v_resetjp_719_;
}
else
{
lean_inc(v_a_718_);
lean_dec(v___x_658_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_725_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
lean_object* v___x_723_; 
if (v_isShared_721_ == 0)
{
v___x_723_ = v___x_720_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v_a_718_);
v___x_723_ = v_reuseFailAlloc_724_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
return v___x_723_;
}
}
}
}
v___jp_726_:
{
lean_object* v___x_733_; lean_object* v___x_734_; uint8_t v___x_735_; 
v___x_733_ = l_Int_Linear_Poly_gcdCoeffs_x27(v___y_731_);
v___x_734_ = lean_unsigned_to_nat(1u);
v___x_735_ = lean_nat_dec_eq(v___x_733_, v___x_734_);
if (v___x_735_ == 0)
{
lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; uint8_t v___x_741_; 
v___x_736_ = l_Int_Linear_Poly_getConst(v___y_731_);
v___x_737_ = lean_nat_to_int(v___x_733_);
v___x_738_ = lean_int_emod(v___x_736_, v___x_737_);
lean_dec(v___x_736_);
v___x_739_ = lean_unsigned_to_nat(0u);
v___x_740_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5);
v___x_741_ = lean_int_dec_eq(v___x_738_, v___x_740_);
lean_dec(v___x_738_);
if (v___x_741_ == 0)
{
uint8_t v___x_742_; 
v___x_742_ = 1;
v___y_647_ = v___y_727_;
v___y_648_ = v___y_728_;
v___y_649_ = v___y_729_;
v___y_650_ = v___y_730_;
v___y_651_ = v___y_731_;
v___y_652_ = v___x_737_;
v___y_653_ = v___x_740_;
v___y_654_ = v___x_739_;
v___y_655_ = v___y_732_;
v___y_656_ = v___x_742_;
goto v___jp_646_;
}
else
{
v___y_647_ = v___y_727_;
v___y_648_ = v___y_728_;
v___y_649_ = v___y_729_;
v___y_650_ = v___y_730_;
v___y_651_ = v___y_731_;
v___y_652_ = v___x_737_;
v___y_653_ = v___x_740_;
v___y_654_ = v___x_739_;
v___y_655_ = v___y_732_;
v___y_656_ = v___x_735_;
goto v___jp_646_;
}
}
else
{
lean_object* v___x_743_; 
lean_dec(v___x_733_);
lean_inc_ref(v___y_731_);
v___x_743_ = l_Int_Linear_Poly_denoteExpr___redArg(v___y_729_, v___y_731_);
if (lean_obj_tag(v___x_743_) == 0)
{
lean_object* v_a_744_; lean_object* v___x_745_; 
v_a_744_ = lean_ctor_get(v___x_743_, 0);
lean_inc(v_a_744_);
lean_dec_ref(v___x_743_);
v___x_745_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(v___y_730_, v_a_610_, v_a_611_, v_a_612_, v_a_613_);
if (lean_obj_tag(v___x_745_) == 0)
{
lean_object* v_a_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_765_; 
v_a_746_ = lean_ctor_get(v___x_745_, 0);
v_isSharedCheck_765_ = !lean_is_exclusive(v___x_745_);
if (v_isSharedCheck_765_ == 0)
{
v___x_748_ = v___x_745_;
v_isShared_749_ = v_isSharedCheck_765_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_a_746_);
lean_dec(v___x_745_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_765_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_763_; 
v___x_750_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__23);
v___x_751_ = l_Lean_mkIntLE(v_a_744_, v___x_750_);
v___x_752_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__8, &l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__8_once, _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__8);
v___x_753_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v___y_732_);
v___x_754_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v___y_728_);
v___x_755_ = l_Lean_Meta_Simp_Arith_Int_ofPoly(v___y_731_);
v___x_756_ = l_Lean_eagerReflBoolTrue;
v___x_757_ = l_Lean_mkApp5(v___x_752_, v_a_746_, v___x_753_, v___x_754_, v___x_755_, v___x_756_);
lean_inc_ref(v___x_751_);
v___x_758_ = l_Lean_mkPropEq(v___y_727_, v___x_751_);
v___x_759_ = l_Lean_Meta_mkExpectedPropHint(v___x_757_, v___x_758_);
v___x_760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_760_, 0, v___x_751_);
lean_ctor_set(v___x_760_, 1, v___x_759_);
v___x_761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_761_, 0, v___x_760_);
if (v_isShared_749_ == 0)
{
lean_ctor_set(v___x_748_, 0, v___x_761_);
v___x_763_ = v___x_748_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v___x_761_);
v___x_763_ = v_reuseFailAlloc_764_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
return v___x_763_;
}
}
}
else
{
lean_object* v_a_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_773_; 
lean_dec(v_a_744_);
lean_dec_ref(v___y_732_);
lean_dec_ref(v___y_731_);
lean_dec_ref(v___y_728_);
lean_dec_ref(v___y_727_);
v_a_766_ = lean_ctor_get(v___x_745_, 0);
v_isSharedCheck_773_ = !lean_is_exclusive(v___x_745_);
if (v_isSharedCheck_773_ == 0)
{
v___x_768_ = v___x_745_;
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_a_766_);
lean_dec(v___x_745_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
lean_object* v___x_771_; 
if (v_isShared_769_ == 0)
{
v___x_771_ = v___x_768_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v_a_766_);
v___x_771_ = v_reuseFailAlloc_772_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
return v___x_771_;
}
}
}
}
else
{
lean_object* v_a_774_; lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_781_; 
lean_dec_ref(v___y_732_);
lean_dec_ref(v___y_731_);
lean_dec_ref(v___y_730_);
lean_dec_ref(v___y_728_);
lean_dec_ref(v___y_727_);
v_a_774_ = lean_ctor_get(v___x_743_, 0);
v_isSharedCheck_781_ = !lean_is_exclusive(v___x_743_);
if (v_isSharedCheck_781_ == 0)
{
v___x_776_ = v___x_743_;
v_isShared_777_ = v_isSharedCheck_781_;
goto v_resetjp_775_;
}
else
{
lean_inc(v_a_774_);
lean_dec(v___x_743_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_781_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
lean_object* v___x_779_; 
if (v_isShared_777_ == 0)
{
v___x_779_ = v___x_776_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v_a_774_);
v___x_779_ = v_reuseFailAlloc_780_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
return v___x_779_;
}
}
}
}
}
v___jp_783_:
{
lean_object* v___x_785_; 
v___x_785_ = l_Lean_Meta_Simp_Arith_Int_leCnstr_x3f(v_e_608_, v_a_610_, v_a_611_, v_a_612_, v_a_613_);
if (lean_obj_tag(v___x_785_) == 0)
{
lean_object* v_a_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_913_; 
v_a_786_ = lean_ctor_get(v___x_785_, 0);
v_isSharedCheck_913_ = !lean_is_exclusive(v___x_785_);
if (v_isSharedCheck_913_ == 0)
{
v___x_788_ = v___x_785_;
v_isShared_789_ = v_isSharedCheck_913_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_a_786_);
lean_dec(v___x_785_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_913_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
if (lean_obj_tag(v_a_786_) == 1)
{
lean_object* v_val_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_908_; 
lean_del_object(v___x_788_);
v_val_790_ = lean_ctor_get(v_a_786_, 0);
v_isSharedCheck_908_ = !lean_is_exclusive(v_a_786_);
if (v_isSharedCheck_908_ == 0)
{
v___x_792_ = v_a_786_;
v_isShared_793_ = v_isSharedCheck_908_;
goto v_resetjp_791_;
}
else
{
lean_inc(v_val_790_);
lean_dec(v_a_786_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_908_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
lean_object* v_snd_794_; lean_object* v_fst_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_907_; 
v_snd_794_ = lean_ctor_get(v_val_790_, 1);
v_fst_795_ = lean_ctor_get(v_val_790_, 0);
v_isSharedCheck_907_ = !lean_is_exclusive(v_val_790_);
if (v_isSharedCheck_907_ == 0)
{
v___x_797_ = v_val_790_;
v_isShared_798_ = v_isSharedCheck_907_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_snd_794_);
lean_inc(v_fst_795_);
lean_dec(v_val_790_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_907_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
lean_object* v_fst_799_; lean_object* v_snd_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_906_; 
v_fst_799_ = lean_ctor_get(v_snd_794_, 0);
v_snd_800_ = lean_ctor_get(v_snd_794_, 1);
v_isSharedCheck_906_ = !lean_is_exclusive(v_snd_794_);
if (v_isSharedCheck_906_ == 0)
{
v___x_802_ = v_snd_794_;
v_isShared_803_ = v_isSharedCheck_906_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_snd_800_);
lean_inc(v_fst_799_);
lean_dec(v_snd_794_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_906_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
lean_object* v___f_804_; lean_object* v___x_805_; 
lean_inc(v_snd_800_);
v___f_804_ = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__0___boxed), 3, 2);
lean_closure_set(v___f_804_, 0, v___x_782_);
lean_closure_set(v___f_804_, 1, v_snd_800_);
lean_inc(v_fst_795_);
lean_inc_ref(v___f_804_);
v___x_805_ = l_Int_Linear_Expr_denoteExpr___redArg(v___f_804_, v_fst_795_);
if (lean_obj_tag(v___x_805_) == 0)
{
lean_object* v_a_806_; lean_object* v___x_807_; 
v_a_806_ = lean_ctor_get(v___x_805_, 0);
lean_inc(v_a_806_);
lean_dec_ref(v___x_805_);
lean_inc(v_fst_799_);
lean_inc_ref(v___f_804_);
v___x_807_ = l_Int_Linear_Expr_denoteExpr___redArg(v___f_804_, v_fst_799_);
if (lean_obj_tag(v___x_807_) == 0)
{
lean_object* v_a_808_; lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_889_; 
v_a_808_ = lean_ctor_get(v___x_807_, 0);
v_isSharedCheck_889_ = !lean_is_exclusive(v___x_807_);
if (v_isSharedCheck_889_ == 0)
{
v___x_810_ = v___x_807_;
v_isShared_811_ = v_isSharedCheck_889_;
goto v_resetjp_809_;
}
else
{
lean_inc(v_a_808_);
lean_dec(v___x_807_);
v___x_810_ = lean_box(0);
v_isShared_811_ = v_isSharedCheck_889_;
goto v_resetjp_809_;
}
v_resetjp_809_:
{
lean_object* v___x_812_; lean_object* v___x_814_; 
v___x_812_ = l_Lean_mkIntLE(v_a_806_, v_a_808_);
lean_inc(v_fst_799_);
lean_inc(v_fst_795_);
if (v_isShared_798_ == 0)
{
lean_ctor_set_tag(v___x_797_, 3);
lean_ctor_set(v___x_797_, 1, v_fst_799_);
v___x_814_ = v___x_797_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v_fst_795_);
lean_ctor_set(v_reuseFailAlloc_888_, 1, v_fst_799_);
v___x_814_ = v_reuseFailAlloc_888_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
lean_object* v___x_815_; uint8_t v___x_816_; 
v___x_815_ = l_Int_Linear_Expr_norm(v___x_814_);
lean_dec_ref(v___x_814_);
v___x_816_ = l_Int_Linear_Poly_isUnsatLe(v___x_815_);
if (v___x_816_ == 0)
{
uint8_t v___x_817_; 
v___x_817_ = l_Int_Linear_Poly_isValidLe(v___x_815_);
if (v___x_817_ == 0)
{
lean_del_object(v___x_802_);
lean_del_object(v___x_792_);
if (v___y_784_ == 0)
{
lean_del_object(v___x_810_);
v___y_727_ = v___x_812_;
v___y_728_ = v_fst_799_;
v___y_729_ = v___f_804_;
v___y_730_ = v_snd_800_;
v___y_731_ = v___x_815_;
v___y_732_ = v_fst_795_;
goto v___jp_726_;
}
else
{
lean_object* v___x_818_; uint8_t v___x_819_; 
lean_inc_ref(v___x_815_);
v___x_818_ = l_Int_Linear_Poly_toExpr(v___x_815_);
v___x_819_ = l_Int_Linear_instBEqExpr_beq(v___x_818_, v_fst_795_);
lean_dec_ref(v___x_818_);
if (v___x_819_ == 0)
{
lean_del_object(v___x_810_);
v___y_727_ = v___x_812_;
v___y_728_ = v_fst_799_;
v___y_729_ = v___f_804_;
v___y_730_ = v_snd_800_;
v___y_731_ = v___x_815_;
v___y_732_ = v_fst_795_;
goto v___jp_726_;
}
else
{
lean_object* v___x_820_; uint8_t v___x_821_; 
v___x_820_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__35, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__35_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__35);
v___x_821_ = l_Int_Linear_instBEqExpr_beq(v_fst_799_, v___x_820_);
if (v___x_821_ == 0)
{
lean_del_object(v___x_810_);
v___y_727_ = v___x_812_;
v___y_728_ = v_fst_799_;
v___y_729_ = v___f_804_;
v___y_730_ = v_snd_800_;
v___y_731_ = v___x_815_;
v___y_732_ = v_fst_795_;
goto v___jp_726_;
}
else
{
lean_object* v___x_822_; lean_object* v___x_824_; 
lean_dec_ref(v___x_815_);
lean_dec_ref(v___x_812_);
lean_dec_ref(v___f_804_);
lean_dec(v_snd_800_);
lean_dec(v_fst_799_);
lean_dec(v_fst_795_);
v___x_822_ = lean_box(0);
if (v_isShared_811_ == 0)
{
lean_ctor_set(v___x_810_, 0, v___x_822_);
v___x_824_ = v___x_810_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v___x_822_);
v___x_824_ = v_reuseFailAlloc_825_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
return v___x_824_;
}
}
}
}
}
else
{
lean_object* v___x_826_; 
lean_dec_ref(v___x_815_);
lean_del_object(v___x_810_);
lean_dec_ref(v___f_804_);
v___x_826_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(v_snd_800_, v_a_610_, v_a_611_, v_a_612_, v_a_613_);
if (lean_obj_tag(v___x_826_) == 0)
{
lean_object* v_a_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_848_; 
v_a_827_ = lean_ctor_get(v___x_826_, 0);
v_isSharedCheck_848_ = !lean_is_exclusive(v___x_826_);
if (v_isSharedCheck_848_ == 0)
{
v___x_829_ = v___x_826_;
v_isShared_830_ = v_isSharedCheck_848_;
goto v_resetjp_828_;
}
else
{
lean_inc(v_a_827_);
lean_dec(v___x_826_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_848_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_840_; 
v___x_831_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__38, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__38_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__38);
v___x_832_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__11, &l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__11_once, _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__11);
v___x_833_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_795_);
v___x_834_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_799_);
v___x_835_ = l_Lean_eagerReflBoolTrue;
v___x_836_ = l_Lean_mkApp4(v___x_832_, v_a_827_, v___x_833_, v___x_834_, v___x_835_);
v___x_837_ = l_Lean_mkPropEq(v___x_812_, v___x_831_);
v___x_838_ = l_Lean_Meta_mkExpectedPropHint(v___x_836_, v___x_837_);
if (v_isShared_803_ == 0)
{
lean_ctor_set(v___x_802_, 1, v___x_838_);
lean_ctor_set(v___x_802_, 0, v___x_831_);
v___x_840_ = v___x_802_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v___x_831_);
lean_ctor_set(v_reuseFailAlloc_847_, 1, v___x_838_);
v___x_840_ = v_reuseFailAlloc_847_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
lean_object* v___x_842_; 
if (v_isShared_793_ == 0)
{
lean_ctor_set(v___x_792_, 0, v___x_840_);
v___x_842_ = v___x_792_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v___x_840_);
v___x_842_ = v_reuseFailAlloc_846_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
lean_object* v___x_844_; 
if (v_isShared_830_ == 0)
{
lean_ctor_set(v___x_829_, 0, v___x_842_);
v___x_844_ = v___x_829_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v___x_842_);
v___x_844_ = v_reuseFailAlloc_845_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
return v___x_844_;
}
}
}
}
}
else
{
lean_object* v_a_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_856_; 
lean_dec_ref(v___x_812_);
lean_del_object(v___x_802_);
lean_dec(v_fst_799_);
lean_dec(v_fst_795_);
lean_del_object(v___x_792_);
v_a_849_ = lean_ctor_get(v___x_826_, 0);
v_isSharedCheck_856_ = !lean_is_exclusive(v___x_826_);
if (v_isSharedCheck_856_ == 0)
{
v___x_851_ = v___x_826_;
v_isShared_852_ = v_isSharedCheck_856_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_a_849_);
lean_dec(v___x_826_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_856_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
lean_object* v___x_854_; 
if (v_isShared_852_ == 0)
{
v___x_854_ = v___x_851_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v_a_849_);
v___x_854_ = v_reuseFailAlloc_855_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
return v___x_854_;
}
}
}
}
}
else
{
lean_object* v___x_857_; 
lean_dec_ref(v___x_815_);
lean_del_object(v___x_810_);
lean_dec_ref(v___f_804_);
v___x_857_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(v_snd_800_, v_a_610_, v_a_611_, v_a_612_, v_a_613_);
if (lean_obj_tag(v___x_857_) == 0)
{
lean_object* v_a_858_; lean_object* v___x_860_; uint8_t v_isShared_861_; uint8_t v_isSharedCheck_879_; 
v_a_858_ = lean_ctor_get(v___x_857_, 0);
v_isSharedCheck_879_ = !lean_is_exclusive(v___x_857_);
if (v_isSharedCheck_879_ == 0)
{
v___x_860_ = v___x_857_;
v_isShared_861_ = v_isSharedCheck_879_;
goto v_resetjp_859_;
}
else
{
lean_inc(v_a_858_);
lean_dec(v___x_857_);
v___x_860_ = lean_box(0);
v_isShared_861_ = v_isSharedCheck_879_;
goto v_resetjp_859_;
}
v_resetjp_859_:
{
lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_871_; 
v___x_862_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8);
v___x_863_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__14, &l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__14_once, _init_l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__14);
v___x_864_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_795_);
v___x_865_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_799_);
v___x_866_ = l_Lean_eagerReflBoolTrue;
v___x_867_ = l_Lean_mkApp4(v___x_863_, v_a_858_, v___x_864_, v___x_865_, v___x_866_);
v___x_868_ = l_Lean_mkPropEq(v___x_812_, v___x_862_);
v___x_869_ = l_Lean_Meta_mkExpectedPropHint(v___x_867_, v___x_868_);
if (v_isShared_803_ == 0)
{
lean_ctor_set(v___x_802_, 1, v___x_869_);
lean_ctor_set(v___x_802_, 0, v___x_862_);
v___x_871_ = v___x_802_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v___x_862_);
lean_ctor_set(v_reuseFailAlloc_878_, 1, v___x_869_);
v___x_871_ = v_reuseFailAlloc_878_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
lean_object* v___x_873_; 
if (v_isShared_793_ == 0)
{
lean_ctor_set(v___x_792_, 0, v___x_871_);
v___x_873_ = v___x_792_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v___x_871_);
v___x_873_ = v_reuseFailAlloc_877_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
lean_object* v___x_875_; 
if (v_isShared_861_ == 0)
{
lean_ctor_set(v___x_860_, 0, v___x_873_);
v___x_875_ = v___x_860_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v___x_873_);
v___x_875_ = v_reuseFailAlloc_876_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
return v___x_875_;
}
}
}
}
}
else
{
lean_object* v_a_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_887_; 
lean_dec_ref(v___x_812_);
lean_del_object(v___x_802_);
lean_dec(v_fst_799_);
lean_dec(v_fst_795_);
lean_del_object(v___x_792_);
v_a_880_ = lean_ctor_get(v___x_857_, 0);
v_isSharedCheck_887_ = !lean_is_exclusive(v___x_857_);
if (v_isSharedCheck_887_ == 0)
{
v___x_882_ = v___x_857_;
v_isShared_883_ = v_isSharedCheck_887_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_a_880_);
lean_dec(v___x_857_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_887_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
lean_object* v___x_885_; 
if (v_isShared_883_ == 0)
{
v___x_885_ = v___x_882_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v_a_880_);
v___x_885_ = v_reuseFailAlloc_886_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
return v___x_885_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_890_; lean_object* v___x_892_; uint8_t v_isShared_893_; uint8_t v_isSharedCheck_897_; 
lean_dec(v_a_806_);
lean_dec_ref(v___f_804_);
lean_del_object(v___x_802_);
lean_dec(v_snd_800_);
lean_dec(v_fst_799_);
lean_del_object(v___x_797_);
lean_dec(v_fst_795_);
lean_del_object(v___x_792_);
v_a_890_ = lean_ctor_get(v___x_807_, 0);
v_isSharedCheck_897_ = !lean_is_exclusive(v___x_807_);
if (v_isSharedCheck_897_ == 0)
{
v___x_892_ = v___x_807_;
v_isShared_893_ = v_isSharedCheck_897_;
goto v_resetjp_891_;
}
else
{
lean_inc(v_a_890_);
lean_dec(v___x_807_);
v___x_892_ = lean_box(0);
v_isShared_893_ = v_isSharedCheck_897_;
goto v_resetjp_891_;
}
v_resetjp_891_:
{
lean_object* v___x_895_; 
if (v_isShared_893_ == 0)
{
v___x_895_ = v___x_892_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v_a_890_);
v___x_895_ = v_reuseFailAlloc_896_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
return v___x_895_;
}
}
}
}
else
{
lean_object* v_a_898_; lean_object* v___x_900_; uint8_t v_isShared_901_; uint8_t v_isSharedCheck_905_; 
lean_dec_ref(v___f_804_);
lean_del_object(v___x_802_);
lean_dec(v_snd_800_);
lean_dec(v_fst_799_);
lean_del_object(v___x_797_);
lean_dec(v_fst_795_);
lean_del_object(v___x_792_);
v_a_898_ = lean_ctor_get(v___x_805_, 0);
v_isSharedCheck_905_ = !lean_is_exclusive(v___x_805_);
if (v_isSharedCheck_905_ == 0)
{
v___x_900_ = v___x_805_;
v_isShared_901_ = v_isSharedCheck_905_;
goto v_resetjp_899_;
}
else
{
lean_inc(v_a_898_);
lean_dec(v___x_805_);
v___x_900_ = lean_box(0);
v_isShared_901_ = v_isSharedCheck_905_;
goto v_resetjp_899_;
}
v_resetjp_899_:
{
lean_object* v___x_903_; 
if (v_isShared_901_ == 0)
{
v___x_903_ = v___x_900_;
goto v_reusejp_902_;
}
else
{
lean_object* v_reuseFailAlloc_904_; 
v_reuseFailAlloc_904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_904_, 0, v_a_898_);
v___x_903_ = v_reuseFailAlloc_904_;
goto v_reusejp_902_;
}
v_reusejp_902_:
{
return v___x_903_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_909_; lean_object* v___x_911_; 
lean_dec(v_a_786_);
v___x_909_ = lean_box(0);
if (v_isShared_789_ == 0)
{
lean_ctor_set(v___x_788_, 0, v___x_909_);
v___x_911_ = v___x_788_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v___x_909_);
v___x_911_ = v_reuseFailAlloc_912_;
goto v_reusejp_910_;
}
v_reusejp_910_:
{
return v___x_911_;
}
}
}
}
else
{
lean_object* v_a_914_; lean_object* v___x_916_; uint8_t v_isShared_917_; uint8_t v_isSharedCheck_921_; 
v_a_914_ = lean_ctor_get(v___x_785_, 0);
v_isSharedCheck_921_ = !lean_is_exclusive(v___x_785_);
if (v_isSharedCheck_921_ == 0)
{
v___x_916_ = v___x_785_;
v_isShared_917_ = v_isSharedCheck_921_;
goto v_resetjp_915_;
}
else
{
lean_inc(v_a_914_);
lean_dec(v___x_785_);
v___x_916_ = lean_box(0);
v_isShared_917_ = v_isSharedCheck_921_;
goto v_resetjp_915_;
}
v_resetjp_915_:
{
lean_object* v___x_919_; 
if (v_isShared_917_ == 0)
{
v___x_919_ = v___x_916_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v_a_914_);
v___x_919_ = v_reuseFailAlloc_920_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
return v___x_919_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___boxed(lean_object* v_e_924_, lean_object* v_checkIfModified_925_, lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_){
_start:
{
uint8_t v_checkIfModified_boxed_931_; lean_object* v_res_932_; 
v_checkIfModified_boxed_931_ = lean_unbox(v_checkIfModified_925_);
v_res_932_ = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f(v_e_924_, v_checkIfModified_boxed_931_, v_a_926_, v_a_927_, v_a_928_, v_a_929_);
lean_dec(v_a_929_);
lean_dec_ref(v_a_928_);
lean_dec(v_a_927_);
lean_dec_ref(v_a_926_);
return v_res_932_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__3(void){
_start:
{
lean_object* v___x_938_; lean_object* v___x_939_; 
v___x_938_ = lean_box(0);
v___x_939_ = l_Lean_Level_succ___override(v___x_938_);
return v___x_939_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__4(void){
_start:
{
lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; 
v___x_940_ = lean_box(0);
v___x_941_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__3, &l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__3_once, _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__3);
v___x_942_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_942_, 0, v___x_941_);
lean_ctor_set(v___x_942_, 1, v___x_940_);
return v___x_942_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__5(void){
_start:
{
lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; 
v___x_943_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__4, &l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__4_once, _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__4);
v___x_944_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__2));
v___x_945_ = l_Lean_mkConst(v___x_944_, v___x_943_);
return v___x_945_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__6(void){
_start:
{
lean_object* v___x_946_; lean_object* v___x_947_; 
v___x_946_ = lean_box(0);
v___x_947_ = l_Lean_mkSort(v___x_946_);
return v___x_947_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__18(void){
_start:
{
lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_966_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30);
v___x_967_ = l_Lean_mkIntLit(v___x_966_);
return v___x_967_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__21(void){
_start:
{
lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; 
v___x_972_ = lean_box(0);
v___x_973_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__20));
v___x_974_ = l_Lean_mkConst(v___x_973_, v___x_972_);
return v___x_974_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__24(void){
_start:
{
lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; 
v___x_979_ = lean_box(0);
v___x_980_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__23));
v___x_981_ = l_Lean_mkConst(v___x_980_, v___x_979_);
return v___x_981_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__27(void){
_start:
{
lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; 
v___x_986_ = lean_box(0);
v___x_987_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__26));
v___x_988_ = l_Lean_mkConst(v___x_987_, v___x_986_);
return v___x_988_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__30(void){
_start:
{
lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; 
v___x_993_ = lean_box(0);
v___x_994_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__29));
v___x_995_ = l_Lean_mkConst(v___x_994_, v___x_993_);
return v___x_995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f(lean_object* v_e_996_, lean_object* v_a_997_, lean_object* v_a_998_, lean_object* v_a_999_, lean_object* v_a_1000_){
_start:
{
lean_object* v_val_1006_; lean_object* v_h_u2081_1007_; lean_object* v___y_1008_; lean_object* v___y_1009_; lean_object* v___y_1010_; lean_object* v___y_1011_; lean_object* v___x_1047_; lean_object* v___x_1048_; uint8_t v___x_1049_; 
v___x_1047_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__8));
v___x_1048_ = lean_unsigned_to_nat(1u);
v___x_1049_ = l_Lean_Expr_isAppOfArity(v_e_996_, v___x_1047_, v___x_1048_);
if (v___x_1049_ == 0)
{
uint8_t v___x_1050_; lean_object* v___x_1051_; 
v___x_1050_ = 1;
v___x_1051_ = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f(v_e_996_, v___x_1050_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_);
return v___x_1051_;
}
else
{
lean_object* v___x_1052_; lean_object* v___x_1053_; 
v___x_1052_ = l_Lean_Expr_appArg_x21(v_e_996_);
v___x_1053_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v___x_1052_, v_a_998_);
if (lean_obj_tag(v___x_1053_) == 0)
{
lean_object* v_a_1054_; lean_object* v___x_1055_; uint8_t v___x_1056_; 
v_a_1054_ = lean_ctor_get(v___x_1053_, 0);
lean_inc(v_a_1054_);
lean_dec_ref(v___x_1053_);
v___x_1055_ = l_Lean_Expr_cleanupAnnotations(v_a_1054_);
v___x_1056_ = l_Lean_Expr_isApp(v___x_1055_);
if (v___x_1056_ == 0)
{
lean_dec_ref(v___x_1055_);
lean_dec_ref(v_e_996_);
goto v___jp_1002_;
}
else
{
lean_object* v_arg_1057_; lean_object* v___x_1058_; uint8_t v___x_1059_; 
v_arg_1057_ = lean_ctor_get(v___x_1055_, 1);
lean_inc_ref(v_arg_1057_);
v___x_1058_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1055_);
v___x_1059_ = l_Lean_Expr_isApp(v___x_1058_);
if (v___x_1059_ == 0)
{
lean_dec_ref(v___x_1058_);
lean_dec_ref(v_arg_1057_);
lean_dec_ref(v_e_996_);
goto v___jp_1002_;
}
else
{
lean_object* v_arg_1060_; lean_object* v___x_1061_; uint8_t v___x_1062_; 
v_arg_1060_ = lean_ctor_get(v___x_1058_, 1);
lean_inc_ref(v_arg_1060_);
v___x_1061_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1058_);
v___x_1062_ = l_Lean_Expr_isApp(v___x_1061_);
if (v___x_1062_ == 0)
{
lean_dec_ref(v___x_1061_);
lean_dec_ref(v_arg_1060_);
lean_dec_ref(v_arg_1057_);
lean_dec_ref(v_e_996_);
goto v___jp_1002_;
}
else
{
lean_object* v___x_1063_; uint8_t v___x_1064_; 
v___x_1063_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1061_);
v___x_1064_ = l_Lean_Expr_isApp(v___x_1063_);
if (v___x_1064_ == 0)
{
lean_dec_ref(v___x_1063_);
lean_dec_ref(v_arg_1060_);
lean_dec_ref(v_arg_1057_);
lean_dec_ref(v_e_996_);
goto v___jp_1002_;
}
else
{
lean_object* v_arg_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; uint8_t v___x_1068_; 
v_arg_1065_ = lean_ctor_get(v___x_1063_, 1);
lean_inc_ref(v_arg_1065_);
v___x_1066_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1063_);
v___x_1067_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__11));
v___x_1068_ = l_Lean_Expr_isConstOf(v___x_1066_, v___x_1067_);
if (v___x_1068_ == 0)
{
lean_object* v___x_1069_; uint8_t v___x_1070_; 
v___x_1069_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__14));
v___x_1070_ = l_Lean_Expr_isConstOf(v___x_1066_, v___x_1069_);
if (v___x_1070_ == 0)
{
lean_object* v___x_1071_; uint8_t v___x_1072_; 
v___x_1071_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__17));
v___x_1072_ = l_Lean_Expr_isConstOf(v___x_1066_, v___x_1071_);
if (v___x_1072_ == 0)
{
lean_object* v___x_1073_; uint8_t v___x_1074_; 
v___x_1073_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___closed__17));
v___x_1074_ = l_Lean_Expr_isConstOf(v___x_1066_, v___x_1073_);
lean_dec_ref(v___x_1066_);
if (v___x_1074_ == 0)
{
lean_dec_ref(v_arg_1065_);
lean_dec_ref(v_arg_1060_);
lean_dec_ref(v_arg_1057_);
lean_dec_ref(v_e_996_);
goto v___jp_1002_;
}
else
{
lean_object* v___x_1075_; 
v___x_1075_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_1065_, v_a_998_);
if (lean_obj_tag(v___x_1075_) == 0)
{
lean_object* v_a_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; uint8_t v___x_1079_; 
v_a_1076_ = lean_ctor_get(v___x_1075_, 0);
lean_inc(v_a_1076_);
lean_dec_ref(v___x_1075_);
v___x_1077_ = l_Lean_Expr_cleanupAnnotations(v_a_1076_);
v___x_1078_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18));
v___x_1079_ = l_Lean_Expr_isConstOf(v___x_1077_, v___x_1078_);
lean_dec_ref(v___x_1077_);
if (v___x_1079_ == 0)
{
lean_dec_ref(v_arg_1060_);
lean_dec_ref(v_arg_1057_);
lean_dec_ref(v_e_996_);
goto v___jp_1002_;
}
else
{
lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; 
v___x_1080_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__18, &l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__18_once, _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__18);
lean_inc_ref(v_arg_1057_);
v___x_1081_ = l_Lean_mkIntAdd(v_arg_1057_, v___x_1080_);
lean_inc_ref(v_arg_1060_);
v___x_1082_ = l_Lean_mkIntLE(v___x_1081_, v_arg_1060_);
v___x_1083_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__21, &l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__21_once, _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__21);
v___x_1084_ = l_Lean_mkAppB(v___x_1083_, v_arg_1060_, v_arg_1057_);
v_val_1006_ = v___x_1082_;
v_h_u2081_1007_ = v___x_1084_;
v___y_1008_ = v_a_997_;
v___y_1009_ = v_a_998_;
v___y_1010_ = v_a_999_;
v___y_1011_ = v_a_1000_;
goto v___jp_1005_;
}
}
else
{
lean_object* v_a_1085_; lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1092_; 
lean_dec_ref(v_arg_1060_);
lean_dec_ref(v_arg_1057_);
lean_dec_ref(v_e_996_);
v_a_1085_ = lean_ctor_get(v___x_1075_, 0);
v_isSharedCheck_1092_ = !lean_is_exclusive(v___x_1075_);
if (v_isSharedCheck_1092_ == 0)
{
v___x_1087_ = v___x_1075_;
v_isShared_1088_ = v_isSharedCheck_1092_;
goto v_resetjp_1086_;
}
else
{
lean_inc(v_a_1085_);
lean_dec(v___x_1075_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1092_;
goto v_resetjp_1086_;
}
v_resetjp_1086_:
{
lean_object* v___x_1090_; 
if (v_isShared_1088_ == 0)
{
v___x_1090_ = v___x_1087_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v_a_1085_);
v___x_1090_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
return v___x_1090_;
}
}
}
}
}
else
{
lean_object* v___x_1093_; 
lean_dec_ref(v___x_1066_);
v___x_1093_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_1065_, v_a_998_);
if (lean_obj_tag(v___x_1093_) == 0)
{
lean_object* v_a_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; uint8_t v___x_1097_; 
v_a_1094_ = lean_ctor_get(v___x_1093_, 0);
lean_inc(v_a_1094_);
lean_dec_ref(v___x_1093_);
v___x_1095_ = l_Lean_Expr_cleanupAnnotations(v_a_1094_);
v___x_1096_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18));
v___x_1097_ = l_Lean_Expr_isConstOf(v___x_1095_, v___x_1096_);
lean_dec_ref(v___x_1095_);
if (v___x_1097_ == 0)
{
lean_dec_ref(v_arg_1060_);
lean_dec_ref(v_arg_1057_);
lean_dec_ref(v_e_996_);
goto v___jp_1002_;
}
else
{
lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; 
v___x_1098_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__18, &l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__18_once, _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__18);
lean_inc_ref(v_arg_1060_);
v___x_1099_ = l_Lean_mkIntAdd(v_arg_1060_, v___x_1098_);
lean_inc_ref(v_arg_1057_);
v___x_1100_ = l_Lean_mkIntLE(v___x_1099_, v_arg_1057_);
v___x_1101_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__24, &l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__24_once, _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__24);
v___x_1102_ = l_Lean_mkAppB(v___x_1101_, v_arg_1060_, v_arg_1057_);
v_val_1006_ = v___x_1100_;
v_h_u2081_1007_ = v___x_1102_;
v___y_1008_ = v_a_997_;
v___y_1009_ = v_a_998_;
v___y_1010_ = v_a_999_;
v___y_1011_ = v_a_1000_;
goto v___jp_1005_;
}
}
else
{
lean_object* v_a_1103_; lean_object* v___x_1105_; uint8_t v_isShared_1106_; uint8_t v_isSharedCheck_1110_; 
lean_dec_ref(v_arg_1060_);
lean_dec_ref(v_arg_1057_);
lean_dec_ref(v_e_996_);
v_a_1103_ = lean_ctor_get(v___x_1093_, 0);
v_isSharedCheck_1110_ = !lean_is_exclusive(v___x_1093_);
if (v_isSharedCheck_1110_ == 0)
{
v___x_1105_ = v___x_1093_;
v_isShared_1106_ = v_isSharedCheck_1110_;
goto v_resetjp_1104_;
}
else
{
lean_inc(v_a_1103_);
lean_dec(v___x_1093_);
v___x_1105_ = lean_box(0);
v_isShared_1106_ = v_isSharedCheck_1110_;
goto v_resetjp_1104_;
}
v_resetjp_1104_:
{
lean_object* v___x_1108_; 
if (v_isShared_1106_ == 0)
{
v___x_1108_ = v___x_1105_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v_a_1103_);
v___x_1108_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
return v___x_1108_;
}
}
}
}
}
else
{
lean_object* v___x_1111_; 
lean_dec_ref(v___x_1066_);
v___x_1111_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_1065_, v_a_998_);
if (lean_obj_tag(v___x_1111_) == 0)
{
lean_object* v_a_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; uint8_t v___x_1115_; 
v_a_1112_ = lean_ctor_get(v___x_1111_, 0);
lean_inc(v_a_1112_);
lean_dec_ref(v___x_1111_);
v___x_1113_ = l_Lean_Expr_cleanupAnnotations(v_a_1112_);
v___x_1114_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18));
v___x_1115_ = l_Lean_Expr_isConstOf(v___x_1113_, v___x_1114_);
lean_dec_ref(v___x_1113_);
if (v___x_1115_ == 0)
{
lean_dec_ref(v_arg_1060_);
lean_dec_ref(v_arg_1057_);
lean_dec_ref(v_e_996_);
goto v___jp_1002_;
}
else
{
lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; 
lean_inc_ref(v_arg_1060_);
lean_inc_ref(v_arg_1057_);
v___x_1116_ = l_Lean_mkIntLE(v_arg_1057_, v_arg_1060_);
v___x_1117_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__27, &l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__27_once, _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__27);
v___x_1118_ = l_Lean_mkAppB(v___x_1117_, v_arg_1060_, v_arg_1057_);
v_val_1006_ = v___x_1116_;
v_h_u2081_1007_ = v___x_1118_;
v___y_1008_ = v_a_997_;
v___y_1009_ = v_a_998_;
v___y_1010_ = v_a_999_;
v___y_1011_ = v_a_1000_;
goto v___jp_1005_;
}
}
else
{
lean_object* v_a_1119_; lean_object* v___x_1121_; uint8_t v_isShared_1122_; uint8_t v_isSharedCheck_1126_; 
lean_dec_ref(v_arg_1060_);
lean_dec_ref(v_arg_1057_);
lean_dec_ref(v_e_996_);
v_a_1119_ = lean_ctor_get(v___x_1111_, 0);
v_isSharedCheck_1126_ = !lean_is_exclusive(v___x_1111_);
if (v_isSharedCheck_1126_ == 0)
{
v___x_1121_ = v___x_1111_;
v_isShared_1122_ = v_isSharedCheck_1126_;
goto v_resetjp_1120_;
}
else
{
lean_inc(v_a_1119_);
lean_dec(v___x_1111_);
v___x_1121_ = lean_box(0);
v_isShared_1122_ = v_isSharedCheck_1126_;
goto v_resetjp_1120_;
}
v_resetjp_1120_:
{
lean_object* v___x_1124_; 
if (v_isShared_1122_ == 0)
{
v___x_1124_ = v___x_1121_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v_a_1119_);
v___x_1124_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
return v___x_1124_;
}
}
}
}
}
else
{
lean_object* v___x_1127_; 
lean_dec_ref(v___x_1066_);
v___x_1127_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_1065_, v_a_998_);
if (lean_obj_tag(v___x_1127_) == 0)
{
lean_object* v_a_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; uint8_t v___x_1131_; 
v_a_1128_ = lean_ctor_get(v___x_1127_, 0);
lean_inc(v_a_1128_);
lean_dec_ref(v___x_1127_);
v___x_1129_ = l_Lean_Expr_cleanupAnnotations(v_a_1128_);
v___x_1130_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__18));
v___x_1131_ = l_Lean_Expr_isConstOf(v___x_1129_, v___x_1130_);
lean_dec_ref(v___x_1129_);
if (v___x_1131_ == 0)
{
lean_dec_ref(v_arg_1060_);
lean_dec_ref(v_arg_1057_);
lean_dec_ref(v_e_996_);
goto v___jp_1002_;
}
else
{
lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; 
lean_inc_ref(v_arg_1057_);
lean_inc_ref(v_arg_1060_);
v___x_1132_ = l_Lean_mkIntLE(v_arg_1060_, v_arg_1057_);
v___x_1133_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__30, &l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__30_once, _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__30);
v___x_1134_ = l_Lean_mkAppB(v___x_1133_, v_arg_1060_, v_arg_1057_);
v_val_1006_ = v___x_1132_;
v_h_u2081_1007_ = v___x_1134_;
v___y_1008_ = v_a_997_;
v___y_1009_ = v_a_998_;
v___y_1010_ = v_a_999_;
v___y_1011_ = v_a_1000_;
goto v___jp_1005_;
}
}
else
{
lean_object* v_a_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1142_; 
lean_dec_ref(v_arg_1060_);
lean_dec_ref(v_arg_1057_);
lean_dec_ref(v_e_996_);
v_a_1135_ = lean_ctor_get(v___x_1127_, 0);
v_isSharedCheck_1142_ = !lean_is_exclusive(v___x_1127_);
if (v_isSharedCheck_1142_ == 0)
{
v___x_1137_ = v___x_1127_;
v_isShared_1138_ = v_isSharedCheck_1142_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_a_1135_);
lean_dec(v___x_1127_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1142_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
lean_object* v___x_1140_; 
if (v_isShared_1138_ == 0)
{
v___x_1140_ = v___x_1137_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v_a_1135_);
v___x_1140_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
return v___x_1140_;
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
lean_object* v_a_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1150_; 
lean_dec_ref(v_e_996_);
v_a_1143_ = lean_ctor_get(v___x_1053_, 0);
v_isSharedCheck_1150_ = !lean_is_exclusive(v___x_1053_);
if (v_isSharedCheck_1150_ == 0)
{
v___x_1145_ = v___x_1053_;
v_isShared_1146_ = v_isSharedCheck_1150_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_a_1143_);
lean_dec(v___x_1053_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1150_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
lean_object* v___x_1148_; 
if (v_isShared_1146_ == 0)
{
v___x_1148_ = v___x_1145_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v_a_1143_);
v___x_1148_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
return v___x_1148_;
}
}
}
}
v___jp_1002_:
{
lean_object* v___x_1003_; lean_object* v___x_1004_; 
v___x_1003_ = lean_box(0);
v___x_1004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1004_, 0, v___x_1003_);
return v___x_1004_;
}
v___jp_1005_:
{
uint8_t v___x_1012_; lean_object* v___x_1013_; 
v___x_1012_ = 0;
lean_inc_ref(v_val_1006_);
v___x_1013_ = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f(v_val_1006_, v___x_1012_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_);
if (lean_obj_tag(v___x_1013_) == 0)
{
lean_object* v_a_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1046_; 
v_a_1014_ = lean_ctor_get(v___x_1013_, 0);
v_isSharedCheck_1046_ = !lean_is_exclusive(v___x_1013_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_1016_ = v___x_1013_;
v_isShared_1017_ = v_isSharedCheck_1046_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_a_1014_);
lean_dec(v___x_1013_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1046_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
if (lean_obj_tag(v_a_1014_) == 1)
{
lean_object* v_val_1018_; lean_object* v___x_1020_; uint8_t v_isShared_1021_; uint8_t v_isSharedCheck_1040_; 
v_val_1018_ = lean_ctor_get(v_a_1014_, 0);
v_isSharedCheck_1040_ = !lean_is_exclusive(v_a_1014_);
if (v_isSharedCheck_1040_ == 0)
{
v___x_1020_ = v_a_1014_;
v_isShared_1021_ = v_isSharedCheck_1040_;
goto v_resetjp_1019_;
}
else
{
lean_inc(v_val_1018_);
lean_dec(v_a_1014_);
v___x_1020_ = lean_box(0);
v_isShared_1021_ = v_isSharedCheck_1040_;
goto v_resetjp_1019_;
}
v_resetjp_1019_:
{
lean_object* v_fst_1022_; lean_object* v_snd_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1039_; 
v_fst_1022_ = lean_ctor_get(v_val_1018_, 0);
v_snd_1023_ = lean_ctor_get(v_val_1018_, 1);
v_isSharedCheck_1039_ = !lean_is_exclusive(v_val_1018_);
if (v_isSharedCheck_1039_ == 0)
{
v___x_1025_ = v_val_1018_;
v_isShared_1026_ = v_isSharedCheck_1039_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_snd_1023_);
lean_inc(v_fst_1022_);
lean_dec(v_val_1018_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1039_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1031_; 
v___x_1027_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__5, &l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__5_once, _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__5);
v___x_1028_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__6, &l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__6_once, _init_l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___closed__6);
lean_inc(v_fst_1022_);
v___x_1029_ = l_Lean_mkApp6(v___x_1027_, v___x_1028_, v_e_996_, v_val_1006_, v_fst_1022_, v_h_u2081_1007_, v_snd_1023_);
if (v_isShared_1026_ == 0)
{
lean_ctor_set(v___x_1025_, 1, v___x_1029_);
v___x_1031_ = v___x_1025_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v_fst_1022_);
lean_ctor_set(v_reuseFailAlloc_1038_, 1, v___x_1029_);
v___x_1031_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
lean_object* v___x_1033_; 
if (v_isShared_1021_ == 0)
{
lean_ctor_set(v___x_1020_, 0, v___x_1031_);
v___x_1033_ = v___x_1020_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v___x_1031_);
v___x_1033_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
lean_object* v___x_1035_; 
if (v_isShared_1017_ == 0)
{
lean_ctor_set(v___x_1016_, 0, v___x_1033_);
v___x_1035_ = v___x_1016_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v___x_1033_);
v___x_1035_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
return v___x_1035_;
}
}
}
}
}
}
else
{
lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1044_; 
lean_dec(v_a_1014_);
lean_dec_ref(v_e_996_);
v___x_1041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1041_, 0, v_val_1006_);
lean_ctor_set(v___x_1041_, 1, v_h_u2081_1007_);
v___x_1042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1042_, 0, v___x_1041_);
if (v_isShared_1017_ == 0)
{
lean_ctor_set(v___x_1016_, 0, v___x_1042_);
v___x_1044_ = v___x_1016_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v___x_1042_);
v___x_1044_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
return v___x_1044_;
}
}
}
}
else
{
lean_dec_ref(v_h_u2081_1007_);
lean_dec_ref(v_val_1006_);
lean_dec_ref(v_e_996_);
return v___x_1013_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___boxed(lean_object* v_e_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_){
_start:
{
lean_object* v_res_1157_; 
v_res_1157_ = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f(v_e_1151_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_);
lean_dec(v_a_1155_);
lean_dec_ref(v_a_1154_);
lean_dec(v_a_1153_);
lean_dec_ref(v_a_1152_);
return v_res_1157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lam__0(lean_object* v_snd_1158_, lean_object* v_x_1159_){
_start:
{
lean_object* v___x_1160_; lean_object* v___x_1161_; 
v___x_1160_ = l_Lean_instInhabitedExpr;
v___x_1161_ = lean_array_get_borrowed(v___x_1160_, v_snd_1158_, v_x_1159_);
lean_inc(v___x_1161_);
return v___x_1161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lam__0___boxed(lean_object* v_snd_1162_, lean_object* v_x_1163_){
_start:
{
lean_object* v_res_1164_; 
v_res_1164_ = l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lam__0(v_snd_1162_, v_x_1163_);
lean_dec(v_x_1163_);
lean_dec_ref(v_snd_1162_);
return v_res_1164_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__2(void){
_start:
{
lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; 
v___x_1170_ = lean_box(0);
v___x_1171_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__1));
v___x_1172_ = l_Lean_mkConst(v___x_1171_, v___x_1170_);
return v___x_1172_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__5(void){
_start:
{
lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; 
v___x_1178_ = lean_box(0);
v___x_1179_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__4));
v___x_1180_ = l_Lean_mkConst(v___x_1179_, v___x_1178_);
return v___x_1180_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__8(void){
_start:
{
lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; 
v___x_1186_ = lean_box(0);
v___x_1187_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__7));
v___x_1188_ = l_Lean_mkConst(v___x_1187_, v___x_1186_);
return v___x_1188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f(lean_object* v_e_1189_, lean_object* v_a_1190_, lean_object* v_a_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_){
_start:
{
lean_object* v___y_1196_; lean_object* v___y_1197_; lean_object* v_h_1198_; lean_object* v___y_1205_; lean_object* v___y_1206_; lean_object* v___y_1207_; lean_object* v___y_1208_; lean_object* v___y_1209_; lean_object* v___y_1210_; lean_object* v___y_1211_; lean_object* v___y_1212_; lean_object* v___y_1213_; lean_object* v___x_1216_; 
v___x_1216_ = l_Lean_Meta_Simp_Arith_Int_dvdCnstr_x3f(v_e_1189_, v_a_1190_, v_a_1191_, v_a_1192_, v_a_1193_);
if (lean_obj_tag(v___x_1216_) == 0)
{
lean_object* v_a_1217_; lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1383_; 
v_a_1217_ = lean_ctor_get(v___x_1216_, 0);
v_isSharedCheck_1383_ = !lean_is_exclusive(v___x_1216_);
if (v_isSharedCheck_1383_ == 0)
{
v___x_1219_ = v___x_1216_;
v_isShared_1220_ = v_isSharedCheck_1383_;
goto v_resetjp_1218_;
}
else
{
lean_inc(v_a_1217_);
lean_dec(v___x_1216_);
v___x_1219_ = lean_box(0);
v_isShared_1220_ = v_isSharedCheck_1383_;
goto v_resetjp_1218_;
}
v_resetjp_1218_:
{
if (lean_obj_tag(v_a_1217_) == 1)
{
lean_object* v_val_1221_; lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1378_; 
v_val_1221_ = lean_ctor_get(v_a_1217_, 0);
v_isSharedCheck_1378_ = !lean_is_exclusive(v_a_1217_);
if (v_isSharedCheck_1378_ == 0)
{
v___x_1223_ = v_a_1217_;
v_isShared_1224_ = v_isSharedCheck_1378_;
goto v_resetjp_1222_;
}
else
{
lean_inc(v_val_1221_);
lean_dec(v_a_1217_);
v___x_1223_ = lean_box(0);
v_isShared_1224_ = v_isSharedCheck_1378_;
goto v_resetjp_1222_;
}
v_resetjp_1222_:
{
lean_object* v_snd_1225_; lean_object* v_fst_1226_; lean_object* v_fst_1227_; lean_object* v_snd_1228_; lean_object* v___x_1230_; uint8_t v_isShared_1231_; uint8_t v_isSharedCheck_1377_; 
v_snd_1225_ = lean_ctor_get(v_val_1221_, 1);
lean_inc(v_snd_1225_);
v_fst_1226_ = lean_ctor_get(v_val_1221_, 0);
lean_inc(v_fst_1226_);
lean_dec(v_val_1221_);
v_fst_1227_ = lean_ctor_get(v_snd_1225_, 0);
v_snd_1228_ = lean_ctor_get(v_snd_1225_, 1);
v_isSharedCheck_1377_ = !lean_is_exclusive(v_snd_1225_);
if (v_isSharedCheck_1377_ == 0)
{
v___x_1230_ = v_snd_1225_;
v_isShared_1231_ = v_isSharedCheck_1377_;
goto v_resetjp_1229_;
}
else
{
lean_inc(v_snd_1228_);
lean_inc(v_fst_1227_);
lean_dec(v_snd_1225_);
v___x_1230_ = lean_box(0);
v_isShared_1231_ = v_isSharedCheck_1377_;
goto v_resetjp_1229_;
}
v_resetjp_1229_:
{
lean_object* v___x_1232_; lean_object* v___y_1234_; lean_object* v___y_1235_; lean_object* v___y_1236_; lean_object* v___y_1237_; lean_object* v___y_1238_; lean_object* v___y_1239_; uint8_t v___x_1281_; 
v___x_1232_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__5);
v___x_1281_ = lean_int_dec_eq(v_fst_1226_, v___x_1232_);
if (v___x_1281_ == 0)
{
lean_object* v___f_1282_; lean_object* v___x_1283_; 
lean_del_object(v___x_1219_);
lean_inc(v_snd_1228_);
v___f_1282_ = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1282_, 0, v_snd_1228_);
lean_inc(v_fst_1227_);
lean_inc_ref(v___f_1282_);
v___x_1283_ = l_Int_Linear_Expr_denoteExpr___redArg(v___f_1282_, v_fst_1227_);
if (lean_obj_tag(v___x_1283_) == 0)
{
lean_object* v_a_1284_; lean_object* v___x_1286_; uint8_t v_isShared_1287_; uint8_t v_isSharedCheck_1364_; 
v_a_1284_ = lean_ctor_get(v___x_1283_, 0);
v_isSharedCheck_1364_ = !lean_is_exclusive(v___x_1283_);
if (v_isSharedCheck_1364_ == 0)
{
v___x_1286_ = v___x_1283_;
v_isShared_1287_ = v_isSharedCheck_1364_;
goto v_resetjp_1285_;
}
else
{
lean_inc(v_a_1284_);
lean_dec(v___x_1283_);
v___x_1286_ = lean_box(0);
v_isShared_1287_ = v_isSharedCheck_1364_;
goto v_resetjp_1285_;
}
v_resetjp_1285_:
{
lean_object* v___y_1289_; uint8_t v___x_1354_; 
v___x_1354_ = lean_int_dec_le(v___x_1232_, v_fst_1226_);
if (v___x_1354_ == 0)
{
lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; 
v___x_1355_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17);
v___x_1356_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19);
v___x_1357_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22);
v___x_1358_ = lean_int_neg(v_fst_1226_);
v___x_1359_ = l_Int_toNat(v___x_1358_);
lean_dec(v___x_1358_);
v___x_1360_ = l_Lean_instToExprInt_mkNat(v___x_1359_);
v___x_1361_ = l_Lean_mkApp3(v___x_1355_, v___x_1356_, v___x_1357_, v___x_1360_);
v___y_1289_ = v___x_1361_;
goto v___jp_1288_;
}
else
{
lean_object* v___x_1362_; lean_object* v___x_1363_; 
v___x_1362_ = l_Int_toNat(v_fst_1226_);
v___x_1363_ = l_Lean_instToExprInt_mkNat(v___x_1362_);
v___y_1289_ = v___x_1363_;
goto v___jp_1288_;
}
v___jp_1288_:
{
lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; uint8_t v___x_1295_; 
lean_inc_ref(v___y_1289_);
v___x_1290_ = l_Lean_mkIntDvd(v___y_1289_, v_a_1284_);
v___x_1291_ = l_Int_Linear_Expr_norm(v_fst_1227_);
lean_inc(v_fst_1226_);
v___x_1292_ = l_Int_Linear_Poly_gcdCoeffs(v___x_1291_, v_fst_1226_);
v___x_1293_ = l_Int_Linear_Poly_getConst(v___x_1291_);
v___x_1294_ = lean_int_emod(v___x_1293_, v___x_1292_);
lean_dec(v___x_1293_);
v___x_1295_ = lean_int_dec_eq(v___x_1294_, v___x_1232_);
lean_dec(v___x_1294_);
if (v___x_1295_ == 0)
{
lean_object* v___x_1296_; 
lean_dec(v___x_1292_);
lean_dec_ref(v___x_1291_);
lean_del_object(v___x_1286_);
lean_dec_ref(v___f_1282_);
lean_dec(v_fst_1226_);
v___x_1296_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(v_snd_1228_, v_a_1190_, v_a_1191_, v_a_1192_, v_a_1193_);
if (lean_obj_tag(v___x_1296_) == 0)
{
lean_object* v_a_1297_; lean_object* v___x_1299_; uint8_t v_isShared_1300_; uint8_t v_isSharedCheck_1317_; 
v_a_1297_ = lean_ctor_get(v___x_1296_, 0);
v_isSharedCheck_1317_ = !lean_is_exclusive(v___x_1296_);
if (v_isSharedCheck_1317_ == 0)
{
v___x_1299_ = v___x_1296_;
v_isShared_1300_ = v_isSharedCheck_1317_;
goto v_resetjp_1298_;
}
else
{
lean_inc(v_a_1297_);
lean_dec(v___x_1296_);
v___x_1299_ = lean_box(0);
v_isShared_1300_ = v_isSharedCheck_1317_;
goto v_resetjp_1298_;
}
v_resetjp_1298_:
{
lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1309_; 
v___x_1301_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__8);
v___x_1302_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__8, &l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__8_once, _init_l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__8);
v___x_1303_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_1227_);
v___x_1304_ = l_Lean_eagerReflBoolTrue;
v___x_1305_ = l_Lean_mkApp4(v___x_1302_, v_a_1297_, v___y_1289_, v___x_1303_, v___x_1304_);
v___x_1306_ = l_Lean_mkPropEq(v___x_1290_, v___x_1301_);
v___x_1307_ = l_Lean_Meta_mkExpectedPropHint(v___x_1305_, v___x_1306_);
if (v_isShared_1231_ == 0)
{
lean_ctor_set(v___x_1230_, 1, v___x_1307_);
lean_ctor_set(v___x_1230_, 0, v___x_1301_);
v___x_1309_ = v___x_1230_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1316_; 
v_reuseFailAlloc_1316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1316_, 0, v___x_1301_);
lean_ctor_set(v_reuseFailAlloc_1316_, 1, v___x_1307_);
v___x_1309_ = v_reuseFailAlloc_1316_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
lean_object* v___x_1311_; 
if (v_isShared_1224_ == 0)
{
lean_ctor_set(v___x_1223_, 0, v___x_1309_);
v___x_1311_ = v___x_1223_;
goto v_reusejp_1310_;
}
else
{
lean_object* v_reuseFailAlloc_1315_; 
v_reuseFailAlloc_1315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1315_, 0, v___x_1309_);
v___x_1311_ = v_reuseFailAlloc_1315_;
goto v_reusejp_1310_;
}
v_reusejp_1310_:
{
lean_object* v___x_1313_; 
if (v_isShared_1300_ == 0)
{
lean_ctor_set(v___x_1299_, 0, v___x_1311_);
v___x_1313_ = v___x_1299_;
goto v_reusejp_1312_;
}
else
{
lean_object* v_reuseFailAlloc_1314_; 
v_reuseFailAlloc_1314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1314_, 0, v___x_1311_);
v___x_1313_ = v_reuseFailAlloc_1314_;
goto v_reusejp_1312_;
}
v_reusejp_1312_:
{
return v___x_1313_;
}
}
}
}
}
else
{
lean_object* v_a_1318_; lean_object* v___x_1320_; uint8_t v_isShared_1321_; uint8_t v_isSharedCheck_1325_; 
lean_dec_ref(v___x_1290_);
lean_dec_ref(v___y_1289_);
lean_del_object(v___x_1230_);
lean_dec(v_fst_1227_);
lean_del_object(v___x_1223_);
v_a_1318_ = lean_ctor_get(v___x_1296_, 0);
v_isSharedCheck_1325_ = !lean_is_exclusive(v___x_1296_);
if (v_isSharedCheck_1325_ == 0)
{
v___x_1320_ = v___x_1296_;
v_isShared_1321_ = v_isSharedCheck_1325_;
goto v_resetjp_1319_;
}
else
{
lean_inc(v_a_1318_);
lean_dec(v___x_1296_);
v___x_1320_ = lean_box(0);
v_isShared_1321_ = v_isSharedCheck_1325_;
goto v_resetjp_1319_;
}
v_resetjp_1319_:
{
lean_object* v___x_1323_; 
if (v_isShared_1321_ == 0)
{
v___x_1323_ = v___x_1320_;
goto v_reusejp_1322_;
}
else
{
lean_object* v_reuseFailAlloc_1324_; 
v_reuseFailAlloc_1324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1324_, 0, v_a_1318_);
v___x_1323_ = v_reuseFailAlloc_1324_;
goto v_reusejp_1322_;
}
v_reusejp_1322_:
{
return v___x_1323_;
}
}
}
}
else
{
lean_object* v___x_1326_; lean_object* v___x_1327_; uint8_t v___x_1328_; 
lean_del_object(v___x_1230_);
lean_del_object(v___x_1223_);
v___x_1326_ = l_Int_Linear_Poly_div(v___x_1292_, v___x_1291_);
lean_inc_ref(v___x_1326_);
v___x_1327_ = l_Int_Linear_Poly_toExpr(v___x_1326_);
v___x_1328_ = l_Int_Linear_instBEqExpr_beq(v_fst_1227_, v___x_1327_);
lean_dec_ref(v___x_1327_);
if (v___x_1328_ == 0)
{
lean_object* v___x_1329_; 
lean_del_object(v___x_1286_);
lean_inc_ref(v___x_1326_);
v___x_1329_ = l_Int_Linear_Poly_denoteExpr___redArg(v___f_1282_, v___x_1326_);
if (lean_obj_tag(v___x_1329_) == 0)
{
lean_object* v_a_1330_; lean_object* v___x_1331_; uint8_t v___x_1332_; 
v_a_1330_ = lean_ctor_get(v___x_1329_, 0);
lean_inc(v_a_1330_);
lean_dec_ref(v___x_1329_);
v___x_1331_ = lean_int_ediv(v_fst_1226_, v___x_1292_);
lean_dec(v_fst_1226_);
v___x_1332_ = lean_int_dec_le(v___x_1232_, v___x_1331_);
if (v___x_1332_ == 0)
{
lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; 
v___x_1333_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17);
v___x_1334_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19);
v___x_1335_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22);
v___x_1336_ = lean_int_neg(v___x_1331_);
lean_dec(v___x_1331_);
v___x_1337_ = l_Int_toNat(v___x_1336_);
lean_dec(v___x_1336_);
v___x_1338_ = l_Lean_instToExprInt_mkNat(v___x_1337_);
v___x_1339_ = l_Lean_mkApp3(v___x_1333_, v___x_1334_, v___x_1335_, v___x_1338_);
v___y_1234_ = v___y_1289_;
v___y_1235_ = v___x_1292_;
v___y_1236_ = v_a_1330_;
v___y_1237_ = v___x_1326_;
v___y_1238_ = v___x_1290_;
v___y_1239_ = v___x_1339_;
goto v___jp_1233_;
}
else
{
lean_object* v___x_1340_; lean_object* v___x_1341_; 
v___x_1340_ = l_Int_toNat(v___x_1331_);
lean_dec(v___x_1331_);
v___x_1341_ = l_Lean_instToExprInt_mkNat(v___x_1340_);
v___y_1234_ = v___y_1289_;
v___y_1235_ = v___x_1292_;
v___y_1236_ = v_a_1330_;
v___y_1237_ = v___x_1326_;
v___y_1238_ = v___x_1290_;
v___y_1239_ = v___x_1341_;
goto v___jp_1233_;
}
}
else
{
lean_object* v_a_1342_; lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1349_; 
lean_dec_ref(v___x_1326_);
lean_dec(v___x_1292_);
lean_dec_ref(v___x_1290_);
lean_dec_ref(v___y_1289_);
lean_dec(v_snd_1228_);
lean_dec(v_fst_1227_);
lean_dec(v_fst_1226_);
v_a_1342_ = lean_ctor_get(v___x_1329_, 0);
v_isSharedCheck_1349_ = !lean_is_exclusive(v___x_1329_);
if (v_isSharedCheck_1349_ == 0)
{
v___x_1344_ = v___x_1329_;
v_isShared_1345_ = v_isSharedCheck_1349_;
goto v_resetjp_1343_;
}
else
{
lean_inc(v_a_1342_);
lean_dec(v___x_1329_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1349_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
lean_object* v___x_1347_; 
if (v_isShared_1345_ == 0)
{
v___x_1347_ = v___x_1344_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1348_; 
v_reuseFailAlloc_1348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1348_, 0, v_a_1342_);
v___x_1347_ = v_reuseFailAlloc_1348_;
goto v_reusejp_1346_;
}
v_reusejp_1346_:
{
return v___x_1347_;
}
}
}
}
else
{
lean_object* v___x_1350_; lean_object* v___x_1352_; 
lean_dec_ref(v___x_1326_);
lean_dec(v___x_1292_);
lean_dec_ref(v___x_1290_);
lean_dec_ref(v___y_1289_);
lean_dec_ref(v___f_1282_);
lean_dec(v_snd_1228_);
lean_dec(v_fst_1227_);
lean_dec(v_fst_1226_);
v___x_1350_ = lean_box(0);
if (v_isShared_1287_ == 0)
{
lean_ctor_set(v___x_1286_, 0, v___x_1350_);
v___x_1352_ = v___x_1286_;
goto v_reusejp_1351_;
}
else
{
lean_object* v_reuseFailAlloc_1353_; 
v_reuseFailAlloc_1353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1353_, 0, v___x_1350_);
v___x_1352_ = v_reuseFailAlloc_1353_;
goto v_reusejp_1351_;
}
v_reusejp_1351_:
{
return v___x_1352_;
}
}
}
}
}
}
else
{
lean_object* v_a_1365_; lean_object* v___x_1367_; uint8_t v_isShared_1368_; uint8_t v_isSharedCheck_1372_; 
lean_dec_ref(v___f_1282_);
lean_del_object(v___x_1230_);
lean_dec(v_snd_1228_);
lean_dec(v_fst_1227_);
lean_dec(v_fst_1226_);
lean_del_object(v___x_1223_);
v_a_1365_ = lean_ctor_get(v___x_1283_, 0);
v_isSharedCheck_1372_ = !lean_is_exclusive(v___x_1283_);
if (v_isSharedCheck_1372_ == 0)
{
v___x_1367_ = v___x_1283_;
v_isShared_1368_ = v_isSharedCheck_1372_;
goto v_resetjp_1366_;
}
else
{
lean_inc(v_a_1365_);
lean_dec(v___x_1283_);
v___x_1367_ = lean_box(0);
v_isShared_1368_ = v_isSharedCheck_1372_;
goto v_resetjp_1366_;
}
v_resetjp_1366_:
{
lean_object* v___x_1370_; 
if (v_isShared_1368_ == 0)
{
v___x_1370_ = v___x_1367_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v_a_1365_);
v___x_1370_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
return v___x_1370_;
}
}
}
}
else
{
lean_object* v___x_1373_; lean_object* v___x_1375_; 
lean_del_object(v___x_1230_);
lean_dec(v_snd_1228_);
lean_dec(v_fst_1227_);
lean_dec(v_fst_1226_);
lean_del_object(v___x_1223_);
v___x_1373_ = lean_box(0);
if (v_isShared_1220_ == 0)
{
lean_ctor_set(v___x_1219_, 0, v___x_1373_);
v___x_1375_ = v___x_1219_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v___x_1373_);
v___x_1375_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
return v___x_1375_;
}
}
v___jp_1233_:
{
lean_object* v___x_1240_; lean_object* v___x_1241_; uint8_t v___x_1242_; 
lean_inc_ref(v___y_1239_);
v___x_1240_ = l_Lean_mkIntDvd(v___y_1239_, v___y_1236_);
v___x_1241_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__30);
v___x_1242_ = lean_int_dec_eq(v___y_1235_, v___x_1241_);
if (v___x_1242_ == 0)
{
lean_object* v___x_1243_; 
v___x_1243_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(v_snd_1228_, v_a_1190_, v_a_1191_, v_a_1192_, v_a_1193_);
if (lean_obj_tag(v___x_1243_) == 0)
{
lean_object* v_a_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; uint8_t v___x_1248_; 
v_a_1244_ = lean_ctor_get(v___x_1243_, 0);
lean_inc(v_a_1244_);
lean_dec_ref(v___x_1243_);
v___x_1245_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__2, &l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__2_once, _init_l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__2);
v___x_1246_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_1227_);
v___x_1247_ = l_Lean_Meta_Simp_Arith_Int_ofPoly(v___y_1237_);
v___x_1248_ = lean_int_dec_le(v___x_1232_, v___y_1235_);
if (v___x_1248_ == 0)
{
lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; 
v___x_1249_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__17);
v___x_1250_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__19);
v___x_1251_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22, &l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22_once, _init_l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___closed__22);
v___x_1252_ = lean_int_neg(v___y_1235_);
lean_dec(v___y_1235_);
v___x_1253_ = l_Int_toNat(v___x_1252_);
lean_dec(v___x_1252_);
v___x_1254_ = l_Lean_instToExprInt_mkNat(v___x_1253_);
v___x_1255_ = l_Lean_mkApp3(v___x_1249_, v___x_1250_, v___x_1251_, v___x_1254_);
v___y_1205_ = v___y_1234_;
v___y_1206_ = v___x_1247_;
v___y_1207_ = v___x_1245_;
v___y_1208_ = v___x_1246_;
v___y_1209_ = v___y_1238_;
v___y_1210_ = v___x_1240_;
v___y_1211_ = v___y_1239_;
v___y_1212_ = v_a_1244_;
v___y_1213_ = v___x_1255_;
goto v___jp_1204_;
}
else
{
lean_object* v___x_1256_; lean_object* v___x_1257_; 
v___x_1256_ = l_Int_toNat(v___y_1235_);
lean_dec(v___y_1235_);
v___x_1257_ = l_Lean_instToExprInt_mkNat(v___x_1256_);
v___y_1205_ = v___y_1234_;
v___y_1206_ = v___x_1247_;
v___y_1207_ = v___x_1245_;
v___y_1208_ = v___x_1246_;
v___y_1209_ = v___y_1238_;
v___y_1210_ = v___x_1240_;
v___y_1211_ = v___y_1239_;
v___y_1212_ = v_a_1244_;
v___y_1213_ = v___x_1257_;
goto v___jp_1204_;
}
}
else
{
lean_object* v_a_1258_; lean_object* v___x_1260_; uint8_t v_isShared_1261_; uint8_t v_isSharedCheck_1265_; 
lean_dec_ref(v___x_1240_);
lean_dec_ref(v___y_1239_);
lean_dec_ref(v___y_1238_);
lean_dec_ref(v___y_1237_);
lean_dec(v___y_1235_);
lean_dec_ref(v___y_1234_);
lean_dec(v_fst_1227_);
v_a_1258_ = lean_ctor_get(v___x_1243_, 0);
v_isSharedCheck_1265_ = !lean_is_exclusive(v___x_1243_);
if (v_isSharedCheck_1265_ == 0)
{
v___x_1260_ = v___x_1243_;
v_isShared_1261_ = v_isSharedCheck_1265_;
goto v_resetjp_1259_;
}
else
{
lean_inc(v_a_1258_);
lean_dec(v___x_1243_);
v___x_1260_ = lean_box(0);
v_isShared_1261_ = v_isSharedCheck_1265_;
goto v_resetjp_1259_;
}
v_resetjp_1259_:
{
lean_object* v___x_1263_; 
if (v_isShared_1261_ == 0)
{
v___x_1263_ = v___x_1260_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v_a_1258_);
v___x_1263_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
return v___x_1263_;
}
}
}
}
else
{
lean_object* v___x_1266_; 
lean_dec_ref(v___y_1239_);
lean_dec(v___y_1235_);
v___x_1266_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(v_snd_1228_, v_a_1190_, v_a_1191_, v_a_1192_, v_a_1193_);
if (lean_obj_tag(v___x_1266_) == 0)
{
lean_object* v_a_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; 
v_a_1267_ = lean_ctor_get(v___x_1266_, 0);
lean_inc(v_a_1267_);
lean_dec_ref(v___x_1266_);
v___x_1268_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__5, &l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__5_once, _init_l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___closed__5);
v___x_1269_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_1227_);
v___x_1270_ = l_Lean_Meta_Simp_Arith_Int_ofPoly(v___y_1237_);
v___x_1271_ = l_Lean_eagerReflBoolTrue;
v___x_1272_ = l_Lean_mkApp5(v___x_1268_, v_a_1267_, v___y_1234_, v___x_1269_, v___x_1270_, v___x_1271_);
v___y_1196_ = v___y_1238_;
v___y_1197_ = v___x_1240_;
v_h_1198_ = v___x_1272_;
goto v___jp_1195_;
}
else
{
lean_object* v_a_1273_; lean_object* v___x_1275_; uint8_t v_isShared_1276_; uint8_t v_isSharedCheck_1280_; 
lean_dec_ref(v___x_1240_);
lean_dec_ref(v___y_1238_);
lean_dec_ref(v___y_1237_);
lean_dec_ref(v___y_1234_);
lean_dec(v_fst_1227_);
v_a_1273_ = lean_ctor_get(v___x_1266_, 0);
v_isSharedCheck_1280_ = !lean_is_exclusive(v___x_1266_);
if (v_isSharedCheck_1280_ == 0)
{
v___x_1275_ = v___x_1266_;
v_isShared_1276_ = v_isSharedCheck_1280_;
goto v_resetjp_1274_;
}
else
{
lean_inc(v_a_1273_);
lean_dec(v___x_1266_);
v___x_1275_ = lean_box(0);
v_isShared_1276_ = v_isSharedCheck_1280_;
goto v_resetjp_1274_;
}
v_resetjp_1274_:
{
lean_object* v___x_1278_; 
if (v_isShared_1276_ == 0)
{
v___x_1278_ = v___x_1275_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v_a_1273_);
v___x_1278_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
return v___x_1278_;
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
lean_object* v___x_1379_; lean_object* v___x_1381_; 
lean_dec(v_a_1217_);
v___x_1379_ = lean_box(0);
if (v_isShared_1220_ == 0)
{
lean_ctor_set(v___x_1219_, 0, v___x_1379_);
v___x_1381_ = v___x_1219_;
goto v_reusejp_1380_;
}
else
{
lean_object* v_reuseFailAlloc_1382_; 
v_reuseFailAlloc_1382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1382_, 0, v___x_1379_);
v___x_1381_ = v_reuseFailAlloc_1382_;
goto v_reusejp_1380_;
}
v_reusejp_1380_:
{
return v___x_1381_;
}
}
}
}
else
{
lean_object* v_a_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1391_; 
v_a_1384_ = lean_ctor_get(v___x_1216_, 0);
v_isSharedCheck_1391_ = !lean_is_exclusive(v___x_1216_);
if (v_isSharedCheck_1391_ == 0)
{
v___x_1386_ = v___x_1216_;
v_isShared_1387_ = v_isSharedCheck_1391_;
goto v_resetjp_1385_;
}
else
{
lean_inc(v_a_1384_);
lean_dec(v___x_1216_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1391_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
lean_object* v___x_1389_; 
if (v_isShared_1387_ == 0)
{
v___x_1389_ = v___x_1386_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v_a_1384_);
v___x_1389_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
return v___x_1389_;
}
}
}
v___jp_1195_:
{
lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; 
lean_inc_ref(v___y_1197_);
v___x_1199_ = l_Lean_mkPropEq(v___y_1196_, v___y_1197_);
v___x_1200_ = l_Lean_Meta_mkExpectedPropHint(v_h_1198_, v___x_1199_);
v___x_1201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1201_, 0, v___y_1197_);
lean_ctor_set(v___x_1201_, 1, v___x_1200_);
v___x_1202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1202_, 0, v___x_1201_);
v___x_1203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1203_, 0, v___x_1202_);
return v___x_1203_;
}
v___jp_1204_:
{
lean_object* v___x_1214_; lean_object* v___x_1215_; 
v___x_1214_ = l_Lean_eagerReflBoolTrue;
lean_inc_ref(v___y_1207_);
v___x_1215_ = l_Lean_mkApp7(v___y_1207_, v___y_1212_, v___y_1205_, v___y_1208_, v___y_1211_, v___y_1206_, v___y_1213_, v___x_1214_);
v___y_1196_ = v___y_1209_;
v___y_1197_ = v___y_1210_;
v_h_1198_ = v___x_1215_;
goto v___jp_1195_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___boxed(lean_object* v_e_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_, lean_object* v_a_1396_, lean_object* v_a_1397_){
_start:
{
lean_object* v_res_1398_; 
v_res_1398_ = l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f(v_e_1392_, v_a_1393_, v_a_1394_, v_a_1395_, v_a_1396_);
lean_dec(v_a_1396_);
lean_dec_ref(v_a_1395_);
lean_dec(v_a_1394_);
lean_dec_ref(v_a_1393_);
return v_res_1398_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__3(void){
_start:
{
lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; 
v___x_1406_ = lean_box(0);
v___x_1407_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__2));
v___x_1408_ = l_Lean_mkConst(v___x_1407_, v___x_1406_);
return v___x_1408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f(lean_object* v_lhs_1409_, lean_object* v_a_1410_, lean_object* v_a_1411_, lean_object* v_a_1412_, lean_object* v_a_1413_){
_start:
{
lean_object* v___x_1415_; 
v___x_1415_ = l_Lean_Meta_Simp_Arith_Int_toLinearExpr(v_lhs_1409_, v_a_1410_, v_a_1411_, v_a_1412_, v_a_1413_);
if (lean_obj_tag(v___x_1415_) == 0)
{
lean_object* v_a_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1482_; 
v_a_1416_ = lean_ctor_get(v___x_1415_, 0);
v_isSharedCheck_1482_ = !lean_is_exclusive(v___x_1415_);
if (v_isSharedCheck_1482_ == 0)
{
v___x_1418_ = v___x_1415_;
v_isShared_1419_ = v_isSharedCheck_1482_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_a_1416_);
lean_dec(v___x_1415_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1482_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v_fst_1420_; lean_object* v_snd_1421_; lean_object* v___x_1423_; uint8_t v_isShared_1424_; uint8_t v_isSharedCheck_1481_; 
v_fst_1420_ = lean_ctor_get(v_a_1416_, 0);
v_snd_1421_ = lean_ctor_get(v_a_1416_, 1);
v_isSharedCheck_1481_ = !lean_is_exclusive(v_a_1416_);
if (v_isSharedCheck_1481_ == 0)
{
v___x_1423_ = v_a_1416_;
v_isShared_1424_ = v_isSharedCheck_1481_;
goto v_resetjp_1422_;
}
else
{
lean_inc(v_snd_1421_);
lean_inc(v_fst_1420_);
lean_dec(v_a_1416_);
v___x_1423_ = lean_box(0);
v_isShared_1424_ = v_isSharedCheck_1481_;
goto v_resetjp_1422_;
}
v_resetjp_1422_:
{
lean_object* v___x_1425_; lean_object* v___x_1426_; uint8_t v___x_1427_; 
v___x_1425_ = l_Int_Linear_Expr_norm(v_fst_1420_);
lean_inc_ref(v___x_1425_);
v___x_1426_ = l_Int_Linear_Poly_toExpr(v___x_1425_);
v___x_1427_ = l_Int_Linear_instBEqExpr_beq(v_fst_1420_, v___x_1426_);
lean_dec_ref(v___x_1426_);
if (v___x_1427_ == 0)
{
lean_object* v___x_1428_; 
lean_del_object(v___x_1418_);
lean_inc(v_snd_1421_);
v___x_1428_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(v_snd_1421_, v_a_1410_, v_a_1411_, v_a_1412_, v_a_1413_);
if (lean_obj_tag(v___x_1428_) == 0)
{
lean_object* v_a_1429_; lean_object* v___f_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; 
v_a_1429_ = lean_ctor_get(v___x_1428_, 0);
lean_inc(v_a_1429_);
lean_dec_ref(v___x_1428_);
v___f_1430_ = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1430_, 0, v_snd_1421_);
lean_inc(v_fst_1420_);
v___x_1431_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_fst_1420_);
lean_inc_ref(v___f_1430_);
v___x_1432_ = l_Int_Linear_Expr_denoteExpr___redArg(v___f_1430_, v_fst_1420_);
if (lean_obj_tag(v___x_1432_) == 0)
{
lean_object* v_a_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; 
v_a_1433_ = lean_ctor_get(v___x_1432_, 0);
lean_inc(v_a_1433_);
lean_dec_ref(v___x_1432_);
lean_inc_ref(v___x_1425_);
v___x_1434_ = l_Lean_Meta_Simp_Arith_Int_ofPoly(v___x_1425_);
v___x_1435_ = l_Int_Linear_Poly_denoteExpr___redArg(v___f_1430_, v___x_1425_);
if (lean_obj_tag(v___x_1435_) == 0)
{
lean_object* v_a_1436_; lean_object* v___x_1438_; uint8_t v_isShared_1439_; uint8_t v_isSharedCheck_1452_; 
v_a_1436_ = lean_ctor_get(v___x_1435_, 0);
v_isSharedCheck_1452_ = !lean_is_exclusive(v___x_1435_);
if (v_isSharedCheck_1452_ == 0)
{
v___x_1438_ = v___x_1435_;
v_isShared_1439_ = v_isSharedCheck_1452_;
goto v_resetjp_1437_;
}
else
{
lean_inc(v_a_1436_);
lean_dec(v___x_1435_);
v___x_1438_ = lean_box(0);
v_isShared_1439_ = v_isSharedCheck_1452_;
goto v_resetjp_1437_;
}
v_resetjp_1437_:
{
lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1446_; 
v___x_1440_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__3, &l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__3_once, _init_l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___closed__3);
v___x_1441_ = l_Lean_eagerReflBoolTrue;
v___x_1442_ = l_Lean_mkApp4(v___x_1440_, v_a_1429_, v___x_1431_, v___x_1434_, v___x_1441_);
lean_inc(v_a_1436_);
v___x_1443_ = l_Lean_mkIntEq(v_a_1433_, v_a_1436_);
v___x_1444_ = l_Lean_Meta_mkExpectedPropHint(v___x_1442_, v___x_1443_);
if (v_isShared_1424_ == 0)
{
lean_ctor_set(v___x_1423_, 1, v___x_1444_);
lean_ctor_set(v___x_1423_, 0, v_a_1436_);
v___x_1446_ = v___x_1423_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1451_; 
v_reuseFailAlloc_1451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1451_, 0, v_a_1436_);
lean_ctor_set(v_reuseFailAlloc_1451_, 1, v___x_1444_);
v___x_1446_ = v_reuseFailAlloc_1451_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
lean_object* v___x_1447_; lean_object* v___x_1449_; 
v___x_1447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1447_, 0, v___x_1446_);
if (v_isShared_1439_ == 0)
{
lean_ctor_set(v___x_1438_, 0, v___x_1447_);
v___x_1449_ = v___x_1438_;
goto v_reusejp_1448_;
}
else
{
lean_object* v_reuseFailAlloc_1450_; 
v_reuseFailAlloc_1450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1450_, 0, v___x_1447_);
v___x_1449_ = v_reuseFailAlloc_1450_;
goto v_reusejp_1448_;
}
v_reusejp_1448_:
{
return v___x_1449_;
}
}
}
}
else
{
lean_object* v_a_1453_; lean_object* v___x_1455_; uint8_t v_isShared_1456_; uint8_t v_isSharedCheck_1460_; 
lean_dec_ref(v___x_1434_);
lean_dec(v_a_1433_);
lean_dec_ref(v___x_1431_);
lean_dec(v_a_1429_);
lean_del_object(v___x_1423_);
v_a_1453_ = lean_ctor_get(v___x_1435_, 0);
v_isSharedCheck_1460_ = !lean_is_exclusive(v___x_1435_);
if (v_isSharedCheck_1460_ == 0)
{
v___x_1455_ = v___x_1435_;
v_isShared_1456_ = v_isSharedCheck_1460_;
goto v_resetjp_1454_;
}
else
{
lean_inc(v_a_1453_);
lean_dec(v___x_1435_);
v___x_1455_ = lean_box(0);
v_isShared_1456_ = v_isSharedCheck_1460_;
goto v_resetjp_1454_;
}
v_resetjp_1454_:
{
lean_object* v___x_1458_; 
if (v_isShared_1456_ == 0)
{
v___x_1458_ = v___x_1455_;
goto v_reusejp_1457_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v_a_1453_);
v___x_1458_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1457_;
}
v_reusejp_1457_:
{
return v___x_1458_;
}
}
}
}
else
{
lean_object* v_a_1461_; lean_object* v___x_1463_; uint8_t v_isShared_1464_; uint8_t v_isSharedCheck_1468_; 
lean_dec_ref(v___x_1431_);
lean_dec_ref(v___f_1430_);
lean_dec(v_a_1429_);
lean_dec_ref(v___x_1425_);
lean_del_object(v___x_1423_);
v_a_1461_ = lean_ctor_get(v___x_1432_, 0);
v_isSharedCheck_1468_ = !lean_is_exclusive(v___x_1432_);
if (v_isSharedCheck_1468_ == 0)
{
v___x_1463_ = v___x_1432_;
v_isShared_1464_ = v_isSharedCheck_1468_;
goto v_resetjp_1462_;
}
else
{
lean_inc(v_a_1461_);
lean_dec(v___x_1432_);
v___x_1463_ = lean_box(0);
v_isShared_1464_ = v_isSharedCheck_1468_;
goto v_resetjp_1462_;
}
v_resetjp_1462_:
{
lean_object* v___x_1466_; 
if (v_isShared_1464_ == 0)
{
v___x_1466_ = v___x_1463_;
goto v_reusejp_1465_;
}
else
{
lean_object* v_reuseFailAlloc_1467_; 
v_reuseFailAlloc_1467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1467_, 0, v_a_1461_);
v___x_1466_ = v_reuseFailAlloc_1467_;
goto v_reusejp_1465_;
}
v_reusejp_1465_:
{
return v___x_1466_;
}
}
}
}
else
{
lean_object* v_a_1469_; lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1476_; 
lean_dec_ref(v___x_1425_);
lean_del_object(v___x_1423_);
lean_dec(v_snd_1421_);
lean_dec(v_fst_1420_);
v_a_1469_ = lean_ctor_get(v___x_1428_, 0);
v_isSharedCheck_1476_ = !lean_is_exclusive(v___x_1428_);
if (v_isSharedCheck_1476_ == 0)
{
v___x_1471_ = v___x_1428_;
v_isShared_1472_ = v_isSharedCheck_1476_;
goto v_resetjp_1470_;
}
else
{
lean_inc(v_a_1469_);
lean_dec(v___x_1428_);
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
lean_object* v___x_1477_; lean_object* v___x_1479_; 
lean_dec_ref(v___x_1425_);
lean_del_object(v___x_1423_);
lean_dec(v_snd_1421_);
lean_dec(v_fst_1420_);
v___x_1477_ = lean_box(0);
if (v_isShared_1419_ == 0)
{
lean_ctor_set(v___x_1418_, 0, v___x_1477_);
v___x_1479_ = v___x_1418_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v___x_1477_);
v___x_1479_ = v_reuseFailAlloc_1480_;
goto v_reusejp_1478_;
}
v_reusejp_1478_:
{
return v___x_1479_;
}
}
}
}
}
else
{
lean_object* v_a_1483_; lean_object* v___x_1485_; uint8_t v_isShared_1486_; uint8_t v_isSharedCheck_1490_; 
v_a_1483_ = lean_ctor_get(v___x_1415_, 0);
v_isSharedCheck_1490_ = !lean_is_exclusive(v___x_1415_);
if (v_isSharedCheck_1490_ == 0)
{
v___x_1485_ = v___x_1415_;
v_isShared_1486_ = v_isSharedCheck_1490_;
goto v_resetjp_1484_;
}
else
{
lean_inc(v_a_1483_);
lean_dec(v___x_1415_);
v___x_1485_ = lean_box(0);
v_isShared_1486_ = v_isSharedCheck_1490_;
goto v_resetjp_1484_;
}
v_resetjp_1484_:
{
lean_object* v___x_1488_; 
if (v_isShared_1486_ == 0)
{
v___x_1488_ = v___x_1485_;
goto v_reusejp_1487_;
}
else
{
lean_object* v_reuseFailAlloc_1489_; 
v_reuseFailAlloc_1489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1489_, 0, v_a_1483_);
v___x_1488_ = v_reuseFailAlloc_1489_;
goto v_reusejp_1487_;
}
v_reusejp_1487_:
{
return v___x_1488_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___boxed(lean_object* v_lhs_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_, lean_object* v_a_1496_){
_start:
{
lean_object* v_res_1497_; 
v_res_1497_ = l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f(v_lhs_1491_, v_a_1492_, v_a_1493_, v_a_1494_, v_a_1495_);
lean_dec(v_a_1495_);
lean_dec_ref(v_a_1494_);
lean_dec(v_a_1493_);
lean_dec_ref(v_a_1492_);
return v_res_1497_;
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
